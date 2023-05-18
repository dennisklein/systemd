/* SPDX-License-Identifier: LGPL-2.1-or-later */

#include <dirent.h>
#include <errno.h>
#include <limits.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "alloc-util.h"
#include "bus-error.h"
#include "bus-util.h"
#include "cgroup-show.h"
#include "cgroup-util.h"
#include "env-file.h"
#include "escape.h"
#include "fd-util.h"
#include "format-util.h"
#include "glyph-util.h"
#include "hostname-util.h"
#include "list.h"
#include "locale-util.h"
#include "macro.h"
#include "nulstr-util.h"
#include "output-mode.h"
#include "parse-util.h"
#include "path-util.h"
#include "process-util.h"
#include "sort-util.h"
#include "string-util.h"
#include "terminal-util.h"
#include "unit-name.h"
#include "xattr-util.h"

#define PID_MIN_COLUMNS 20

/* remove duplicates from sorted pid array in-place */
static inline unsigned uniq_pid_array(pid_t sorted_pids[], unsigned length) {
        assert(sorted_pids);
        if (length < 2)
                return length;

        pid_t * const last = sorted_pids + (length - 1);
        /* create a new unique pid array in-place */
        pid_t *uniq = sorted_pids;

        FOREACH_ARRAY(pid, sorted_pids, length - 1) {
                if (*pid != *(pid + 1)) {
                        /* append the last pid of non-unique streak */
                        *uniq = *pid;
                        uniq++;
                }
        }
        /* last pid at end of non-unique streak by definition */
        *uniq = *last;
        uniq++;

        return uniq - sorted_pids; /* new length */
}

/* returns maximum of given integers */
static inline unsigned long max(unsigned long a, long b) {
        assert(a < LONG_MAX);

        if ((long) a > b)
                return a;
        return b;
}

static inline int show_pid(
                const char *prefix,
                unsigned pid_width,
                unsigned ppid_tree_depth,
                const char *glyph,
                pid_t pid,
                size_t n_columns,
                OutputFlags flags) {

        int r;
        _cleanup_free_ char *cmdline = NULL;

        if (pid_width == 0)
                pid_width = DECIMAL_STR_WIDTH(pid);

        const unsigned row_prefix_width = ppid_tree_depth + pid_width + 3; /* something like "...├─1114784 " */
        n_columns = (flags & OUTPUT_FULL_WIDTH) ? SIZE_MAX : max(PID_MIN_COLUMNS, n_columns - row_prefix_width);

        r = get_process_cmdline(pid,
                                n_columns,
                                PROCESS_CMDLINE_COMM_FALLBACK | PROCESS_CMDLINE_USE_LOCALE,
                                &cmdline);
        if (r < 0)
                return r;

        printf("%s%s%s%s%*"PID_PRI" %s%s\n",
               prefix,
               (ppid_tree_depth > 0) ? ansi_grey() : "",
               glyph,
               (ppid_tree_depth > 0) ? "": ansi_grey(),
               (int) pid_width,
               pid,
               strna(cmdline),
               ansi_normal());

        return 0;
}

struct PpidTreeNode {
        pid_t pid;

        LIST_FIELDS(struct PpidTreeNode, siblings);
        LIST_HEAD(struct PpidTreeNode, children);
        unsigned n_children;
};

/**
 * recursively construct the ppid tree from equal-length pid/ppid arrays where
 * a process' pid and ppid correspond to the same index in both arrays.
 *
 * - the parent arg is the last used node element from a sufficiently large
 *   pre-allocated node array (it is known a priori that we need n_ppids tree nodes)
 * - returns the last used node element
 */
static struct PpidTreeNode* construct_ppid_tree(
                const pid_t pids[],
                const pid_t ppids[],
                size_t n_ppids,
                struct PpidTreeNode *parent,
                struct PpidTreeNode *last_preallocated) {

        assert(pids);
        assert(ppids); /* must contain as many elements as the pids array */
        assert(parent);

        struct PpidTreeNode *last = parent;
        const pid_t *pid = pids;
        FOREACH_ARRAY(ppid, ppids, n_ppids) {
                if (*ppid == parent->pid) {
                        /* take the next pre-allocated unused node */
                        struct PpidTreeNode *child = last + 1;
                        child->pid = *pid;

                        /* have the parent learn about its new child :) */
                        LIST_APPEND(siblings, parent->children, child);
                        parent->n_children++;

                        /* search subtree of current child */
                        last = construct_ppid_tree(pids, ppids, n_ppids, child, last_preallocated);
                }
                pid++; /* loop over pid and ppid arrays in lock-step */

                /* check if tree construction is complete */
                if (last == last_preallocated)
                        break;
        }

        return last; /* last used node */
}

static int show_ppid_tree(
                struct PpidTreeNode *parent,
                const char *prefix,
                unsigned depth,
                size_t n_columns,
                OutputFlags flags,
                bool more) {

        assert(parent);

        int r;
        unsigned pid_width = 0;

        /* right-align pids if this is a flat branch (no subtrees) */
        if (parent->n_children > 1) {
                bool is_flat_branch = true;
                LIST_FOREACH(siblings, child, parent->children) {
                        is_flat_branch = (child->n_children == 0);
                        if (!is_flat_branch)
                                break;
                }
                if (is_flat_branch)
                        pid_width = DECIMAL_STR_WIDTH(LIST_FIND_TAIL(siblings, parent->children)->pid);
        }

        LIST_FOREACH_WITH_NEXT(siblings, child, next, parent->children) {
                const char *glyph = special_glyph((next || more) ? SPECIAL_GLYPH_TREE_BRANCH
                                                                 : SPECIAL_GLYPH_TREE_RIGHT);
                r = show_pid(prefix, pid_width, depth, glyph, child->pid, n_columns, flags);
                if (r < 0)
                        return r;

                if (child->children) {
                        _cleanup_free_ char *subprefix = NULL;
                        subprefix = strjoin(prefix,
                                            (depth > 0) ? ansi_grey() : "",
                                            special_glyph((next || more) ? SPECIAL_GLYPH_TREE_VERTICAL
                                                                         : SPECIAL_GLYPH_TREE_SPACE),
                                            (depth > 0) ? ansi_normal() : "");
                        if (!subprefix)
                                return -ENOMEM;

                        r = show_ppid_tree(child, subprefix, depth + 2, n_columns, flags, false);
                        if (r < 0)
                                return r;
                }
        }

        return 0;
}

static int show_pids(
                pid_t pids[],
                unsigned n_pids,
                const char *prefix,
                size_t n_columns,
                bool extra,
                bool more,
                OutputFlags flags) {

        if (n_pids == 0)
                return 0;

        int r;

        /* sort and deduplicate pid array */
        typesafe_qsort(pids, n_pids, pid_compare_func);
        n_pids = uniq_pid_array(pids, n_pids);

        if ((n_pids > 1) && (flags & OUTPUT_PPID_TREE) && !extra) {
                /* print the ppid tree */

                size_t n_ppids = n_pids;
                _cleanup_free_ pid_t *ppids = NULL;
                ppids = new(pid_t, n_ppids);
                if (!ppids)
                        return -ENOMEM;

                /* query parent pids, virtual tree root is pid 0 */
                pid_t *ppid = ppids;
                FOREACH_ARRAY(pid, pids, n_pids) {
                        r = get_process_ppid(*pid, ppid);
                        if (r < 0)
                                *ppid = 0;

                        /* check if parent process is member of the given pids array */
                        void* found = typesafe_bsearch(ppid, pids, n_pids, pid_compare_func);
                        if (!found)
                                *ppid = 0;

                        ppid++;
                }

                /* pre-allocate all tree nodes at once */
                size_t n_tree_nodes = n_pids + 1;
                _cleanup_free_ struct PpidTreeNode *root = NULL;
                root = new0(struct PpidTreeNode, n_tree_nodes);
                if (!root)
                        return -ENOMEM;

                /* construct tree from pid/ppid arrays */
                struct PpidTreeNode* last = construct_ppid_tree(pids, ppids, n_ppids, root, (root + n_tree_nodes - 1));
                assert(last == (root + n_tree_nodes - 1));

                /* print by traversing depth-first */
                r = show_ppid_tree(root, prefix, 0, n_columns, flags, more);
                if (r < 0)
                        return r;
        } else {
                /* print flat list */

                pid_t * const last_pid = pids + (n_pids - 1);
                const unsigned pid_width = DECIMAL_STR_WIDTH(*last_pid);

                FOREACH_ARRAY(pid, pids, n_pids) {
                        const char *glyph = extra ? special_glyph(SPECIAL_GLYPH_TRIANGULAR_BULLET)
                                                  : special_glyph((more || pid != last_pid) ? SPECIAL_GLYPH_TREE_BRANCH
                                                                                            : SPECIAL_GLYPH_TREE_RIGHT);
                        r = show_pid(prefix, pid_width, 0, glyph, *pid, n_columns, flags);
                        if (r < 0)
                                return r;
                }
        }

        return 0;
}

static int show_cgroup_one_by_path(
                const char *path,
                const char *prefix,
                size_t n_columns,
                bool more,
                OutputFlags flags) {

        _cleanup_free_ pid_t *pids = NULL;
        _cleanup_fclose_ FILE *f = NULL;
        _cleanup_free_ char *p = NULL;
        size_t n = 0;
        char *fn;
        int r;

        r = cg_mangle_path(path, &p);
        if (r < 0)
                return r;

        fn = strjoina(p, "/cgroup.procs");
        f = fopen(fn, "re");
        if (!f)
                return -errno;

        for (;;) {
                pid_t pid;

                /* libvirt / qemu uses threaded mode and cgroup.procs cannot be read at the lower levels.
                 * From https://docs.kernel.org/admin-guide/cgroup-v2.html#threads,
                 * “cgroup.procs” in a threaded domain cgroup contains the PIDs of all processes in
                 * the subtree and is not readable in the subtree proper. */
                r = cg_read_pid(f, &pid);
                if (IN_SET(r, 0, -EOPNOTSUPP))
                        break;
                if (r < 0)
                        return r;

                if (!(flags & OUTPUT_KERNEL_THREADS) && is_kernel_thread(pid) > 0)
                        continue;

                if (!GREEDY_REALLOC(pids, n + 1))
                        return -ENOMEM;

                pids[n++] = pid;
        }

        return show_pids(pids, n, prefix, n_columns, false, more, flags);
}

static int is_delegated(int cgfd, const char *path) {
        _cleanup_free_ char *b = NULL;
        int r;

        assert(cgfd >= 0 || path);

        r = getxattr_malloc(cgfd < 0 ? path : FORMAT_PROC_FD_PATH(cgfd), "trusted.delegate", &b);
        if (r < 0 && ERRNO_IS_XATTR_ABSENT(r)) {
                /* If the trusted xattr isn't set (preferred), then check the untrusted one. Under the
                 * assumption that whoever is trusted enough to own the cgroup, is also trusted enough to
                 * decide if it is delegated or not this should be safe. */
                r = getxattr_malloc(cgfd < 0 ? path : FORMAT_PROC_FD_PATH(cgfd), "user.delegate", &b);
                if (r < 0 && ERRNO_IS_XATTR_ABSENT(r))
                        return false;
        }
        if (r < 0)
                return log_debug_errno(r, "Failed to read delegate xattr, ignoring: %m");

        r = parse_boolean(b);
        if (r < 0)
                return log_debug_errno(r, "Failed to parse delegate xattr boolean value, ignoring: %m");

        return r;
}

static int show_cgroup_name(
                const char *path,
                const char *prefix,
                SpecialGlyph glyph,
                OutputFlags flags) {

        uint64_t cgroupid = UINT64_MAX;
        _cleanup_free_ char *b = NULL;
        _cleanup_close_ int fd = -EBADF;
        bool delegate;
        int r;

        if (FLAGS_SET(flags, OUTPUT_CGROUP_XATTRS) || FLAGS_SET(flags, OUTPUT_CGROUP_ID)) {
                fd = open(path, O_PATH|O_CLOEXEC|O_NOFOLLOW|O_DIRECTORY, 0);
                if (fd < 0)
                        log_debug_errno(errno, "Failed to open cgroup '%s', ignoring: %m", path);
        }

        delegate = is_delegated(fd, path) > 0;

        if (FLAGS_SET(flags, OUTPUT_CGROUP_ID)) {
                cg_file_handle fh = CG_FILE_HANDLE_INIT;
                int mnt_id = -1;

                if (name_to_handle_at(
                                    fd < 0 ? AT_FDCWD : fd,
                                    fd < 0 ? path : "",
                                    &fh.file_handle,
                                    &mnt_id,
                                    fd < 0 ? 0 : AT_EMPTY_PATH) < 0)
                        log_debug_errno(errno, "Failed to determine cgroup ID of %s, ignoring: %m", path);
                else
                        cgroupid = CG_FILE_HANDLE_CGROUPID(fh);
        }

        r = path_extract_filename(path, &b);
        if (r < 0)
                return log_error_errno(r, "Failed to extract filename from cgroup path: %m");

        printf("%s%s%s%s%s",
               prefix, special_glyph(glyph),
               delegate ? ansi_underline() : "",
               cg_unescape(b),
               delegate ? ansi_normal() : "");

        if (delegate)
                printf(" %s%s%s",
                       ansi_highlight(),
                       special_glyph(SPECIAL_GLYPH_ELLIPSIS),
                       ansi_normal());

        if (cgroupid != UINT64_MAX)
                printf(" %s(#%" PRIu64 ")%s", ansi_grey(), cgroupid, ansi_normal());

        printf("\n");

        if (FLAGS_SET(flags, OUTPUT_CGROUP_XATTRS) && fd >= 0) {
                _cleanup_free_ char *nl = NULL;

                r = flistxattr_malloc(fd, &nl);
                if (r < 0)
                        log_debug_errno(r, "Failed to enumerate xattrs on '%s', ignoring: %m", path);

                NULSTR_FOREACH(xa, nl) {
                        _cleanup_free_ char *x = NULL, *y = NULL, *buf = NULL;
                        int n;

                        if (!STARTSWITH_SET(xa, "user.", "trusted."))
                                continue;

                        n = fgetxattr_malloc(fd, xa, &buf);
                        if (n < 0) {
                                log_debug_errno(r, "Failed to read xattr '%s' off '%s', ignoring: %m", xa, path);
                                continue;
                        }

                        x = cescape(xa);
                        if (!x)
                                return -ENOMEM;

                        y = cescape_length(buf, n);
                        if (!y)
                                return -ENOMEM;

                        printf("%s%s%s %s%s%s: %s\n",
                               prefix,
                               glyph == SPECIAL_GLYPH_TREE_BRANCH ? special_glyph(SPECIAL_GLYPH_TREE_VERTICAL) : "  ",
                               special_glyph(SPECIAL_GLYPH_ARROW_RIGHT),
                               ansi_blue(), x, ansi_normal(),
                               y);
                }
        }

        return 0;
}

int show_cgroup_by_path(
                const char *path,
                const char *prefix,
                size_t n_columns,
                OutputFlags flags) {

        _cleanup_free_ char *fn = NULL, *p1 = NULL, *last = NULL, *p2 = NULL;
        _cleanup_closedir_ DIR *d = NULL;
        bool shown_pids = false;
        char *gn = NULL;
        int r;

        assert(path);

        if (n_columns <= 0)
                n_columns = columns();

        prefix = strempty(prefix);

        r = cg_mangle_path(path, &fn);
        if (r < 0)
                return r;

        d = opendir(fn);
        if (!d)
                return -errno;

        while ((r = cg_read_subgroup(d, &gn)) > 0) {
                _cleanup_free_ char *k = NULL;

                k = path_join(fn, gn);
                free(gn);
                if (!k)
                        return -ENOMEM;

                if (!(flags & OUTPUT_SHOW_ALL) && cg_is_empty_recursive(NULL, k) > 0)
                        continue;

                if (!shown_pids) {
                        show_cgroup_one_by_path(path, prefix, n_columns, true, flags);
                        shown_pids = true;
                }

                if (last) {
                        r = show_cgroup_name(last, prefix, SPECIAL_GLYPH_TREE_BRANCH, flags);
                        if (r < 0)
                                return r;

                        if (!p1) {
                                p1 = strjoin(prefix, special_glyph(SPECIAL_GLYPH_TREE_VERTICAL));
                                if (!p1)
                                        return -ENOMEM;
                        }

                        show_cgroup_by_path(last, p1, n_columns-2, flags);
                        free(last);
                }

                last = TAKE_PTR(k);
        }

        if (r < 0)
                return r;

        if (!shown_pids)
                show_cgroup_one_by_path(path, prefix, n_columns, !!last, flags);

        if (last) {
                r = show_cgroup_name(last, prefix, SPECIAL_GLYPH_TREE_RIGHT, flags);
                if (r < 0)
                        return r;

                if (!p2) {
                        p2 = strjoin(prefix, "  ");
                        if (!p2)
                                return -ENOMEM;
                }

                show_cgroup_by_path(last, p2, n_columns-2, flags);
        }

        return 0;
}

int show_cgroup(const char *controller,
                const char *path,
                const char *prefix,
                size_t n_columns,
                OutputFlags flags) {
        _cleanup_free_ char *p = NULL;
        int r;

        assert(path);

        r = cg_get_path(controller, path, NULL, &p);
        if (r < 0)
                return r;

        return show_cgroup_by_path(p, prefix, n_columns, flags);
}

static int show_extra_pids(
                const char *controller,
                const char *path,
                const char *prefix,
                size_t n_columns,
                const pid_t pids[],
                unsigned n_pids,
                OutputFlags flags) {

        _cleanup_free_ pid_t *copy = NULL;
        unsigned i, j;
        int r;

        assert(path);

        if (n_pids <= 0)
                return 0;

        if (n_columns <= 0)
                n_columns = columns();

        prefix = strempty(prefix);

        copy = new(pid_t, n_pids);
        if (!copy)
                return -ENOMEM;

        for (i = 0, j = 0; i < n_pids; i++) {
                _cleanup_free_ char *k = NULL;

                r = cg_pid_get_path(controller, pids[i], &k);
                if (r < 0)
                        return r;

                if (path_startswith(k, path))
                        continue;

                copy[j++] = pids[i];
        }

        return show_pids(copy, j, prefix, n_columns, true, false, flags);
}

int show_cgroup_and_extra(
                const char *controller,
                const char *path,
                const char *prefix,
                size_t n_columns,
                const pid_t extra_pids[],
                unsigned n_extra_pids,
                OutputFlags flags) {

        int r;

        assert(path);

        r = show_cgroup(controller, path, prefix, n_columns, flags);
        if (r < 0)
                return r;

        return show_extra_pids(controller, path, prefix, n_columns, extra_pids, n_extra_pids, flags);
}

int show_cgroup_get_unit_path_and_warn(
                sd_bus *bus,
                const char *unit,
                char **ret) {

        _cleanup_(sd_bus_error_free) sd_bus_error error = SD_BUS_ERROR_NULL;
        _cleanup_free_ char *path = NULL;
        int r;

        path = unit_dbus_path_from_name(unit);
        if (!path)
                return log_oom();

        r = sd_bus_get_property_string(
                        bus,
                        "org.freedesktop.systemd1",
                        path,
                        unit_dbus_interface_from_name(unit),
                        "ControlGroup",
                        &error,
                        ret);
        if (r < 0)
                return log_error_errno(r, "Failed to query unit control group path: %s",
                                       bus_error_message(&error, r));

        return 0;
}

int show_cgroup_get_path_and_warn(
                const char *machine,
                const char *prefix,
                char **ret) {

        _cleanup_free_ char *root = NULL;
        int r;

        if (machine) {
                _cleanup_(sd_bus_flush_close_unrefp) sd_bus *bus = NULL;
                _cleanup_free_ char *unit = NULL;
                const char *m;

                if (!hostname_is_valid(machine, 0))
                        return log_error_errno(SYNTHETIC_ERRNO(EINVAL), "Machine name is not valid: %s", machine);

                m = strjoina("/run/systemd/machines/", machine);
                r = parse_env_file(NULL, m, "SCOPE", &unit);
                if (r < 0)
                        return log_error_errno(r, "Failed to load machine data: %m");

                r = bus_connect_transport_systemd(BUS_TRANSPORT_LOCAL, NULL, RUNTIME_SCOPE_SYSTEM, &bus);
                if (r < 0)
                        return bus_log_connect_error(r, BUS_TRANSPORT_LOCAL);

                r = show_cgroup_get_unit_path_and_warn(bus, unit, &root);
                if (r < 0)
                        return r;
        } else {
                r = cg_get_root_path(&root);
                if (r == -ENOMEDIUM)
                        return log_error_errno(r, "Failed to get root control group path.\n"
                                                  "No cgroup filesystem mounted on /sys/fs/cgroup");
                if (r < 0)
                        return log_error_errno(r, "Failed to get root control group path: %m");
        }

        if (prefix) {
                char *t;

                t = path_join(root, prefix);
                if (!t)
                        return log_oom();

                *ret = t;
        } else
                *ret = TAKE_PTR(root);

        return 0;
}

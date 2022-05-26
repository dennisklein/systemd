/* SPDX-License-Identifier: LGPL-2.1-or-later */

#include <efi.h>
#include <efilib.h>

#include "disk.h"
#include "util.h"

EFI_STATUS disk_get_part_uuid(EFI_HANDLE *handle, CHAR16 uuid[static 37]) {
        EFI_STATUS err;
        EFI_DEVICE_PATH *device_path;
        _cleanup_freepool_ EFI_DEVICE_PATH *paths = NULL;

        /* export the device path this image is started from */

        if (!handle)
                return EFI_NOT_FOUND;

        err = BS->HandleProtocol(handle, &DevicePathProtocol, (void **) &device_path);
        if (err != EFI_SUCCESS)
                return err;

        paths = UnpackDevicePath(device_path);
        for (EFI_DEVICE_PATH *path = paths; !IsDevicePathEnd(path); path = NextDevicePathNode(path)) {
                HARDDRIVE_DEVICE_PATH *drive;

                if (DevicePathType(path) != MEDIA_DEVICE_PATH)
                        continue;
                if (DevicePathSubType(path) != MEDIA_HARDDRIVE_DP)
                        continue;
                drive = (HARDDRIVE_DEVICE_PATH *)path;
                if (drive->SignatureType != SIGNATURE_TYPE_GUID)
                        continue;

                GuidToString(uuid, (EFI_GUID *)&drive->Signature);
                return EFI_SUCCESS;
        }

        return EFI_NOT_FOUND;
}

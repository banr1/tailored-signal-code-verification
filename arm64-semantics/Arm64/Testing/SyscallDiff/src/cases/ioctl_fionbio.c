// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// ioctl(2) FIONBIO / FIOASYNC on a regular file succeed (do_vfs_ioctl handles them before
// vfs_ioctl, so they never reach -ENOTTY).
#include "sd_rt.h"

#define FIONBIO 0x5421
#define FIOASYNC 0x5452

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fd = sd_openat(AT_FDCWD, "io_nbio.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  i32 one = 1;
  i32 zero = 0;
  SD_EXPECT("ioctl_fionbio_on", sd_sys3(SYS_ioctl, fd, FIONBIO, &one), 0);
  SD_EXPECT("ioctl_fionbio_off", sd_sys3(SYS_ioctl, fd, FIONBIO, &zero), 0);
  SD_EXPECT("ioctl_fioasync_off", sd_sys3(SYS_ioctl, fd, FIOASYNC, &zero), 0);
  SD_EXPECT("close", sd_close((int)fd), 0);
  return 0;
}

// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// ioctl(2) FIOCLEX / FIONCLEX on a regular file succeed and toggle FD_CLOEXEC (do_vfs_ioctl).
#include "sd_rt.h"

#define FIONCLEX 0x5450
#define FIOCLEX 0x5451

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fd = sd_openat(AT_FDCWD, "io_clex.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("ioctl_fioclex", sd_sys3(SYS_ioctl, fd, FIOCLEX, 0), 0);
  SD_EXPECT("getfd_set", sd_sys3(SYS_fcntl, fd, F_GETFD, 0), FD_CLOEXEC);
  SD_EXPECT("ioctl_fionclex", sd_sys3(SYS_ioctl, fd, FIONCLEX, 0), 0);
  SD_EXPECT("getfd_clear", sd_sys3(SYS_fcntl, fd, F_GETFD, 0), 0);
  SD_EXPECT("close", sd_close((int)fd), 0);
  return 0;
}

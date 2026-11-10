// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// ioctl(2) FIONREAD on a regular file returns 0 and stores i_size - f_pos (do_vfs_ioctl).
#include "sd_rt.h"

#define FIONREAD 0x541B

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fd = sd_openat(AT_FDCWD, "io_nread.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("write_10", sd_write((int)fd, "0123456789", 10), 10);
  SD_EXPECT("lseek_3", sd_lseek((int)fd, 3, SEEK_SET), 3);
  i32 n = -1;
  SD_EXPECT("ioctl_fionread", sd_sys3(SYS_ioctl, fd, FIONREAD, &n), 0);
  SD_EXPECT("nread", n, 7);
  SD_EXPECT("close", sd_close((int)fd), 0);
  return 0;
}

// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// pread64(2) EBADF (pos >= 0): never-opened fd, negative fd, and an fd opened O_WRONLY.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  char buf[4];
  SD_EXPECT("pread_fd_99", sd_sys4(SYS_pread64, 99, buf, 4, 0), -EBADF);
  SD_EXPECT("pread_fd_neg1", sd_sys4(SYS_pread64, -1L, buf, 4, 0), -EBADF);
  i64 fd = sd_openat(AT_FDCWD, "w.txt", O_CREAT | O_WRONLY, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("pread_wronly", sd_sys4(SYS_pread64, fd, buf, 4, 0), -EBADF);
  sd_close((int)fd);
  return 0;
}

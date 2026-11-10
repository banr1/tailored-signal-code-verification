// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// close(2) twice -> EBADF; read/write/lseek/pread64 on the closed fd -> EBADF.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  char buf[4];
  i64 fd = sd_openat(AT_FDCWD, "c.txt", O_CREAT | O_RDWR, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("close_1", sd_close((int)fd), 0);
  SD_EXPECT("close_2", sd_close((int)fd), -EBADF);
  SD_EXPECT("read_closed", sd_read((int)fd, buf, 4), -EBADF);
  SD_EXPECT("write_closed", sd_write((int)fd, "x", 1), -EBADF);
  SD_EXPECT("lseek_closed", sd_lseek((int)fd, 0, SEEK_SET), -EBADF);
  SD_EXPECT("pread_closed", sd_sys4(SYS_pread64, fd, buf, 4, 0), -EBADF);
  return 0;
}

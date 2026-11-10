// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat/write/close/read sequence: create a file, write it, reopen O_RDONLY, read it back, hit EOF.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  char buf[16];
  i64 fd = sd_openat(AT_FDCWD, "rt.txt", O_CREAT | O_WRONLY, 0644);
  SD_CHECK("open_creat_ok", fd >= 3);
  SD_EXPECT("write_hello", sd_write((int)fd, "hello world", 11), 11);
  SD_EXPECT("close_w", sd_close((int)fd), 0);
  i64 fd2 = sd_openat(AT_FDCWD, "rt.txt", O_RDONLY, 0);
  SD_CHECK("open_rdonly_reuses_fd", fd2 == fd);
  sd_memset(buf, 0, sizeof buf);
  SD_EXPECT("read_all", sd_read((int)fd2, buf, sizeof buf), 11);
  SD_CHECK("read_bytes_eq", sd_memeq(buf, "hello world", 11));
  SD_EXPECT("read_eof", sd_read((int)fd2, buf, sizeof buf), 0);
  SD_EXPECT("close_r", sd_close((int)fd2), 0);
  return 0;
}

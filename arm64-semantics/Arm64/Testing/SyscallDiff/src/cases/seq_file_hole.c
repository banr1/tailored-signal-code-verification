// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// lseek(2) past EOF then write(2) creates a hole that reads back as zero bytes.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  char buf[16];
  i64 fd = sd_openat(AT_FDCWD, "h.txt", O_CREAT | O_RDWR, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("write_ab", sd_write((int)fd, "ab", 2), 2);
  SD_EXPECT("seek_8", sd_lseek((int)fd, 8, SEEK_SET), 8);
  SD_EXPECT("write_cd", sd_write((int)fd, "cd", 2), 2);
  SD_EXPECT("size_10", sd_lseek((int)fd, 0, SEEK_END), 10);
  SD_EXPECT("rewind", sd_lseek((int)fd, 0, SEEK_SET), 0);
  sd_memset(buf, 0x55, sizeof buf);
  SD_EXPECT("read_all", sd_read((int)fd, buf, sizeof buf), 10);
  SD_CHECK("head_ab", sd_memeq(buf, "ab", 2));
  SD_CHECK("hole_zero", sd_memeq(buf + 2, "\0\0\0\0\0\0", 6));
  SD_CHECK("tail_cd", sd_memeq(buf + 8, "cd", 2));
  SD_CHECK("untouched", (u8)buf[10] == 0x55);
  sd_close((int)fd);
  return 0;
}

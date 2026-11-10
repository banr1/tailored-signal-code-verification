// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// read(2) EFAULT on a non-empty file (NULL / unmapped buffer); the offset does not advance.
#include "sd_rt.h"
static i64 mkfile(const char *path, const char *data, u64 n) {
  i64 fd = sd_openat(AT_FDCWD, path, O_CREAT | O_WRONLY | O_TRUNC, 0644);
  if (fd < 0) return fd;
  i64 r = sd_write((int)fd, data, n);
  sd_close((int)fd);
  return r;
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  char buf[8];
  SD_EXPECT("mk", mkfile("e.txt", "abcd", 4), 4);
  i64 fd = sd_openat(AT_FDCWD, "e.txt", O_RDONLY, 0);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("read_null", sd_read((int)fd, (void *)0, 4), -EFAULT);
  SD_EXPECT("read_unmapped", sd_read((int)fd, (void *)0x10000, 4), -EFAULT);
  SD_EXPECT("pos_unchanged", sd_lseek((int)fd, 0, SEEK_CUR), 0);
  sd_memset(buf, 0, sizeof buf);
  SD_EXPECT("read_ok", sd_read((int)fd, buf, 4), 4);
  SD_CHECK("bytes", sd_memeq(buf, "abcd", 4));
  sd_close((int)fd);
  return 0;
}

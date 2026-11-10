// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) O_APPEND: every write lands at end of file even after lseek to 0; offset ends at the new size.
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
  char buf[16];
  SD_EXPECT("mk", mkfile("a.txt", "abc", 3), 3);
  i64 fd = sd_openat(AT_FDCWD, "a.txt", O_WRONLY | O_APPEND, 0);
  SD_CHECK("open_append_ok", fd >= 3);
  SD_EXPECT("write_de", sd_write((int)fd, "de", 2), 2);
  SD_EXPECT("lseek_set_0", sd_lseek((int)fd, 0, SEEK_SET), 0);
  SD_EXPECT("write_f", sd_write((int)fd, "f", 1), 1);
  SD_EXPECT("pos_after_append", sd_lseek((int)fd, 0, SEEK_CUR), 6);
  sd_close((int)fd);
  fd = sd_openat(AT_FDCWD, "a.txt", O_RDONLY, 0);
  sd_memset(buf, 0, sizeof buf);
  SD_EXPECT("read_all", sd_read((int)fd, buf, sizeof buf), 6);
  SD_CHECK("bytes_abcdef", sd_memeq(buf, "abcdef", 6));
  sd_close((int)fd);
  return 0;
}

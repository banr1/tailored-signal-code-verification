// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// read(2) copies only file bytes: at EOF a NULL buffer returns 0; a buffer whose tail is unmapped gets a full 8-byte read.
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
  SD_EXPECT("mk", mkfile("s.txt", "ABCDEFGH", 8), 8);
  i64 fd = sd_openat(AT_FDCWD, "s.txt", O_RDONLY, 0);
  SD_CHECK("open_ok", fd >= 3);
  i64 m = sd_mmap(0, 2 * PAGE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  SD_CHECK("mmap_ok", m > 0);
  SD_EXPECT("munmap_2nd", sd_munmap((u64)m + PAGE, PAGE), 0);
  char *p = (char *)((u64)m + PAGE - 8);
  /* 16-byte request, only 8 mapped bytes, but the file only has 8 bytes to copy. */
  SD_EXPECT("read_8_of_16", sd_read((int)fd, p, 16), 8);
  SD_CHECK("bytes", sd_memeq(p, "ABCDEFGH", 8));
  /* At EOF nothing is copied, so the buffer is never touched. */
  SD_EXPECT("read_eof_null", sd_read((int)fd, (void *)0, 16), 0);
  sd_close((int)fd);
  return 0;
}

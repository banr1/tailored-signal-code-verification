// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) O_RDONLY|O_TRUNC on a writable regular file: Linux opens it and truncates it to 0 bytes.
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
  SD_EXPECT("mk", mkfile("t.txt", "abcdef", 6), 6);
  i64 fd = sd_openat(AT_FDCWD, "t.txt", O_RDONLY | O_TRUNC, 0);
  SD_CHECK("open_rdonly_trunc_ok", fd >= 3);
  if (fd >= 0) {
    SD_EXPECT("read_after", sd_read((int)fd, buf, sizeof buf), 0);
    sd_close((int)fd);
  }
  return 0;
}

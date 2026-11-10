// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) path normalization: "./f", ".//f" and "f" name the same file (shared contents).
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  char buf[8];
  i64 fd = sd_openat(AT_FDCWD, "./f", O_CREAT | O_WRONLY, 0644);
  SD_CHECK("creat_dot_slash_ok", fd >= 3);
  SD_EXPECT("write", sd_write((int)fd, "dot", 3), 3);
  sd_close((int)fd);
  SD_EXPECT("excl_plain", sd_openat(AT_FDCWD, "f", O_CREAT | O_EXCL | O_WRONLY, 0644), -EEXIST);
  fd = sd_openat(AT_FDCWD, ".//f", O_RDONLY, 0);
  SD_CHECK("open_dot_slash_slash_ok", fd >= 3);
  sd_memset(buf, 0, sizeof buf);
  SD_EXPECT("read", sd_read((int)fd, buf, sizeof buf), 3);
  SD_CHECK("bytes", sd_memeq(buf, "dot", 3));
  sd_close((int)fd);
  return 0;
}

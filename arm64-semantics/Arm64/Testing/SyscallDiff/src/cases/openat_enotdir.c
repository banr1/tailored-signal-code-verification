// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) on a regular file used as a directory: O_DIRECTORY, trailing '/', and "reg/x" -> ENOTDIR.
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
  SD_EXPECT("mk_reg", mkfile("reg", "r", 1), 1);
  SD_EXPECT("o_directory", sd_openat(AT_FDCWD, "reg", O_RDONLY | O_DIRECTORY, 0), -ENOTDIR);
  SD_EXPECT("trailing_slash", sd_openat(AT_FDCWD, "reg/", O_RDONLY, 0), -ENOTDIR);
  SD_EXPECT("trailing_slash_dot", sd_openat(AT_FDCWD, "reg/.", O_RDONLY, 0), -ENOTDIR);
  SD_EXPECT("reg_as_parent", sd_openat(AT_FDCWD, "reg/x", O_RDONLY, 0), -ENOTDIR);
  SD_EXPECT("reg_as_parent_creat", sd_openat(AT_FDCWD, "reg/x", O_CREAT | O_WRONLY, 0644), -ENOTDIR);
  return 0;
}

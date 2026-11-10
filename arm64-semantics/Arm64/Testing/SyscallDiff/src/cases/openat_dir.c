// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) on directory "." O_RDONLY succeeds; read -> EISDIR, write -> EBADF, close -> 0.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  char buf[8];
  i64 fd = sd_openat(AT_FDCWD, ".", O_RDONLY, 0);
  SD_CHECK("open_dot_ok", fd >= 3);
  SD_EXPECT("read_dir", sd_read((int)fd, buf, sizeof buf), -EISDIR);
  SD_EXPECT("write_dir", sd_write((int)fd, "x", 1), -EBADF);
  SD_EXPECT("close_dir", sd_close((int)fd), 0);
  fd = sd_openat(AT_FDCWD, ".", O_RDONLY | O_DIRECTORY, 0);
  SD_CHECK("open_dot_odirectory_ok", fd >= 3);
  SD_EXPECT("close_dir2", sd_close((int)fd), 0);
  return 0;
}

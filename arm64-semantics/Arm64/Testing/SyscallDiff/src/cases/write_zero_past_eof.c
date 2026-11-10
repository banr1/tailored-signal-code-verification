// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// write(2) count 0 on a file at an offset past EOF returns 0 and does not extend the file.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fd = sd_openat(AT_FDCWD, "z.txt", O_CREAT | O_RDWR, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("write_2", sd_write((int)fd, "ab", 2), 2);
  SD_EXPECT("seek_100", sd_lseek((int)fd, 100, SEEK_SET), 100);
  SD_EXPECT("write_zero", sd_write((int)fd, "x", 0), 0);
  SD_EXPECT("write_zero_null", sd_write((int)fd, (void *)0, 0), 0);
  SD_EXPECT("size_still_2", sd_lseek((int)fd, 0, SEEK_END), 2);
  sd_close((int)fd);
  return 0;
}

// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// lseek(2) in-bounds SEEK_DATA (3) / SEEK_HOLE (4) on a sparse file (64 KiB hole then 1 data byte).
#include "sd_rt.h"

#define SEEK_DATA 3
#define SEEK_HOLE 4

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fd = sd_openat(AT_FDCWD, "sparse.bin", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("seek_64k", sd_lseek((int)fd, 65536, SEEK_SET), 65536);
  SD_EXPECT("write_1", sd_write((int)fd, "A", 1), 1);
  SD_EXPECT("seek_hole_0", sd_lseek((int)fd, 0, SEEK_HOLE), 0);
  SD_EXPECT("seek_data_0", sd_lseek((int)fd, 0, SEEK_DATA), 65536);
  SD_EXPECT("seek_hole_64k", sd_lseek((int)fd, 65536, SEEK_HOLE), 65537);
  sd_close((int)fd);
  return 0;
}

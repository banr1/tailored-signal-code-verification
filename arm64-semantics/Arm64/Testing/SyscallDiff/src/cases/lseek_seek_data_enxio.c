// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// lseek(2) SEEK_DATA (3) / SEEK_HOLE (4) at or beyond EOF (== i_size, > i_size) -> ENXIO.
#include "sd_rt.h"

#define SEEK_DATA 3
#define SEEK_HOLE 4
#define ENXIO 6

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
  SD_EXPECT("mk", mkfile("d.txt", "0123456789", 10), 10);
  i64 fd = sd_openat(AT_FDCWD, "d.txt", O_RDONLY, 0);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("seek_data_eof", sd_lseek((int)fd, 10, SEEK_DATA), -ENXIO);
  SD_EXPECT("seek_hole_eof", sd_lseek((int)fd, 10, SEEK_HOLE), -ENXIO);
  SD_EXPECT("seek_data_past_eof", sd_lseek((int)fd, 20, SEEK_DATA), -ENXIO);
  SD_EXPECT("seek_hole_past_eof", sd_lseek((int)fd, 20, SEEK_HOLE), -ENXIO);
  SD_EXPECT("pos_unchanged", sd_lseek((int)fd, 0, SEEK_CUR), 0);
  sd_close((int)fd);
  return 0;
}

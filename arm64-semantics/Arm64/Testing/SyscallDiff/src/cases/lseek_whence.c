// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// lseek(2) SEEK_SET / SEEK_CUR / SEEK_END (positive, negative, past EOF) and reads at the new offsets.
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
  char buf[4];
  SD_EXPECT("mk", mkfile("l.txt", "0123456789", 10), 10);
  i64 fd = sd_openat(AT_FDCWD, "l.txt", O_RDONLY, 0);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("set_3", sd_lseek((int)fd, 3, SEEK_SET), 3);
  SD_EXPECT("read_2", sd_read((int)fd, buf, 2), 2);
  SD_CHECK("bytes_34", sd_memeq(buf, "34", 2));
  SD_EXPECT("cur_plus2", sd_lseek((int)fd, 2, SEEK_CUR), 7);
  SD_EXPECT("cur_minus4", sd_lseek((int)fd, -4, SEEK_CUR), 3);
  SD_EXPECT("cur_0", sd_lseek((int)fd, 0, SEEK_CUR), 3);
  SD_EXPECT("end_minus1", sd_lseek((int)fd, -1, SEEK_END), 9);
  SD_EXPECT("read_last", sd_read((int)fd, buf, 4), 1);
  SD_CHECK("byte_9", buf[0] == '9');
  SD_EXPECT("end_0", sd_lseek((int)fd, 0, SEEK_END), 10);
  SD_EXPECT("end_plus5", sd_lseek((int)fd, 5, SEEK_END), 15);
  SD_EXPECT("read_past_eof", sd_read((int)fd, buf, 4), 0);
  SD_EXPECT("cur_minus15", sd_lseek((int)fd, -15, SEEK_CUR), 0);
  sd_close((int)fd);
  return 0;
}

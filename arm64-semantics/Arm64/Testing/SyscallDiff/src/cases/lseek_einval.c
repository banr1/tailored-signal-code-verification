// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// lseek(2) EINVAL: negative resulting offset (SET/CUR/END), SEEK_END overflow, bad whence; offset kept.
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
  SD_EXPECT("mk", mkfile("l.txt", "0123456789", 10), 10);
  i64 fd = sd_openat(AT_FDCWD, "l.txt", O_RDONLY, 0);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("set_4", sd_lseek((int)fd, 4, SEEK_SET), 4);
  SD_EXPECT("set_neg1", sd_lseek((int)fd, -1, SEEK_SET), -EINVAL);
  SD_EXPECT("cur_neg5", sd_lseek((int)fd, -5, SEEK_CUR), -EINVAL);
  SD_EXPECT("end_neg11", sd_lseek((int)fd, -11, SEEK_END), -EINVAL);
  /* 10 + LLONG_MAX overflows to a negative loff_t. */
  SD_EXPECT("end_llong_max", sd_lseek((int)fd, 0x7fffffffffffffffL, SEEK_END), -EINVAL);
  SD_EXPECT("whence_5", sd_lseek((int)fd, 0, 5), -EINVAL);
  SD_EXPECT("whence_big", sd_lseek((int)fd, 0, 0x7fffffff), -EINVAL);
  SD_EXPECT("pos_kept", sd_lseek((int)fd, 0, SEEK_CUR), 4);
  sd_close((int)fd);
  return 0;
}

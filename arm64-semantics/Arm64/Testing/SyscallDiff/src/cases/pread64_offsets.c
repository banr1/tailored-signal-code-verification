// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// pread64(2) reads at explicit offsets (middle, tail, EOF, far past EOF) without moving the file offset.
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
  SD_EXPECT("mk", mkfile("p.txt", "0123456789", 10), 10);
  i64 fd = sd_openat(AT_FDCWD, "p.txt", O_RDONLY, 0);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("seek_1", sd_lseek((int)fd, 1, SEEK_SET), 1);
  SD_EXPECT("pread_4_at_5", sd_sys4(SYS_pread64, fd, buf, 4, 5), 4);
  SD_CHECK("bytes_5678", sd_memeq(buf, "5678", 4));
  SD_EXPECT("pread_8_at_7", sd_sys4(SYS_pread64, fd, buf, 8, 7), 3);
  SD_CHECK("bytes_789", sd_memeq(buf, "789", 3));
  SD_EXPECT("pread_at_eof", sd_sys4(SYS_pread64, fd, buf, 8, 10), 0);
  SD_EXPECT("pread_far", sd_sys4(SYS_pread64, fd, buf, 8, 1UL << 40), 0);
  SD_EXPECT("pread_zero_len", sd_sys4(SYS_pread64, fd, buf, 0, 3), 0);
  SD_EXPECT("pos_still_1", sd_lseek((int)fd, 0, SEEK_CUR), 1);
  SD_EXPECT("read_1", sd_read((int)fd, buf, 1), 1);
  SD_CHECK("byte_1", buf[0] == '1');
  sd_close((int)fd);
  return 0;
}

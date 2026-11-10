// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// Two openat(2) fds on one file have independent offsets but share contents (write via one, read via other).
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  char buf[16];
  i64 w = sd_openat(AT_FDCWD, "s.txt", O_CREAT | O_RDWR, 0644);
  i64 r = sd_openat(AT_FDCWD, "s.txt", O_RDWR, 0);
  SD_CHECK("w_ok", w >= 3);
  SD_CHECK("r_ok", r > w);
  SD_EXPECT("w_write", sd_write((int)w, "hello", 5), 5);
  SD_EXPECT("r_pos_0", sd_lseek((int)r, 0, SEEK_CUR), 0);
  sd_memset(buf, 0, sizeof buf);
  SD_EXPECT("r_read_3", sd_read((int)r, buf, 3), 3);
  SD_CHECK("r_bytes_hel", sd_memeq(buf, "hel", 3));
  SD_EXPECT("r_write_XY", sd_write((int)r, "XY", 2), 2);
  SD_EXPECT("w_pos_5", sd_lseek((int)w, 0, SEEK_CUR), 5);
  SD_EXPECT("w_write_bang", sd_write((int)w, "!", 1), 1);
  SD_EXPECT("pread_all", sd_sys4(SYS_pread64, r, buf, sizeof buf, 0), 6);
  SD_CHECK("bytes_helXY_bang", sd_memeq(buf, "helXY!", 6));
  sd_close((int)w);
  sd_close((int)r);
  return 0;
}

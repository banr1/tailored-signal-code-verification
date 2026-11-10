// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// write(2) from a buffer whose tail is unmapped: Linux writes the readable 8 bytes (short write).
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  char buf[16];
  i64 fd = sd_openat(AT_FDCWD, "s.txt", O_CREAT | O_RDWR, 0644);
  SD_CHECK("open_ok", fd >= 3);
  i64 m = sd_mmap(0, 2 * PAGE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  SD_CHECK("mmap_ok", m > 0);
  char *p = (char *)((u64)m + PAGE - 8);
  for (int i = 0; i < 8; i++) p[i] = (char)('a' + i);
  SD_EXPECT("munmap_2nd", sd_munmap((u64)m + PAGE, PAGE), 0);
  SD_EXPECT("write_16_tail_unmapped", sd_write((int)fd, p, 16), 8);
  SD_EXPECT("size", sd_lseek((int)fd, 0, SEEK_END), 8);
  sd_memset(buf, 0, sizeof buf);
  SD_EXPECT("pread_back", sd_sys4(SYS_pread64, fd, buf, 16, 0), 8);
  SD_CHECK("bytes", sd_memeq(buf, "abcdefgh", 8));
  sd_close((int)fd);
  return 0;
}

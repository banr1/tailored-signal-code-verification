// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// read(2) with count > MAX_RW_COUNT (0x7ffff000): Linux and the Lean model clamp count to
// MAX_RW_COUNT and read the 4-byte file, whereas qemu-aarch64 lock_user returns -EFAULT on the
// 2 GiB range (QEMU-DEV-13).
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  char buf[16];
  i64 fd = sd_openat(AT_FDCWD, "m.txt", O_CREAT | O_RDWR | O_TRUNC, 0600);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("write_4", sd_write((int)fd, "abcd", 4), 4);
  SD_EXPECT("rewind", sd_lseek((int)fd, 0, SEEK_SET), 0);
  SD_EXPECT("read_over_max_rw", sd_read((int)fd, buf, 0x80000000UL), 4);
  SD_CHECK("data_ok", sd_memeq(buf, "abcd", 4));
  sd_close((int)fd);
  return 0;
}

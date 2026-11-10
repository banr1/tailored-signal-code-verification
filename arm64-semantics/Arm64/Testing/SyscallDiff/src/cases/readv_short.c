// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// readv(2) short read: file ends inside segment 1, later segments untouched; mid-file offset start.
#include "sd_rt.h"

static i64 sd_readv(int fd, const struct sd_iovec *iov, u64 cnt) {
  return sd_sys3(SYS_readv, (i64)fd, iov, cnt);
}

static void show_buf(const char *label, const char *p, u64 n) {
  sd_puts(label);
  sd_puts("=[");
  sd_write(1, p, n);
  sd_puts("]\n");
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fd = sd_openat(AT_FDCWD, "rvs.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("write_7", sd_write((int)fd, "0123456", 7), 7);
  /* Start at offset 2: 5 bytes remain for 4 + 4 + 4 bytes of segments. */
  SD_EXPECT("lseek_2", sd_lseek((int)fd, 2, SEEK_SET), 2);

  char a[4], b[4], c[4];
  sd_memset(a, '.', 4);
  sd_memset(b, '.', 4);
  sd_memset(c, '.', 4);
  struct sd_iovec v[3];
  v[0].base = a;
  v[0].len = 4;
  v[1].base = b;
  v[1].len = 4;
  v[2].base = c;
  v[2].len = 4;
  SD_EXPECT("readv_short", sd_readv((int)fd, v, 3), 5);
  show_buf("seg0", a, 4);
  show_buf("seg1", b, 4);
  show_buf("seg2", c, 4);
  SD_EXPECT("lseek_cur", sd_lseek((int)fd, 0, SEEK_CUR), 7);
  SD_EXPECT("readv_eof", sd_readv((int)fd, v, 3), 0);
  SD_EXPECT("close", sd_close((int)fd), 0);
  return 0;
}

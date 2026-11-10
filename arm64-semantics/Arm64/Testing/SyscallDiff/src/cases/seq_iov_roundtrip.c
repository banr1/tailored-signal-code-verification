// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// writev/readv/fstat sequence: gather 4 segments into a file, fstat size, scatter back with a new split.
#include "sd_rt.h"

static i64 sd_readv(int fd, const struct sd_iovec *iov, u64 cnt) {
  return sd_sys3(SYS_readv, (i64)fd, iov, cnt);
}
static i64 sd_writev(int fd, const struct sd_iovec *iov, u64 cnt) {
  return sd_sys3(SYS_writev, (i64)fd, iov, cnt);
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
  i64 fd = sd_openat(AT_FDCWD, "seq.bin", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  struct sd_iovec w[4];
  w[0].base = "one-";
  w[0].len = 4;
  w[1].base = "";
  w[1].len = 0;
  w[2].base = "two-";
  w[2].len = 4;
  w[3].base = "three";
  w[3].len = 5;
  SD_EXPECT("writev_13", sd_writev((int)fd, w, 4), 13);
  /* Append a second gather at the current offset. */
  w[0].base = "|four";
  w[0].len = 5;
  SD_EXPECT("writev_5", sd_writev((int)fd, w, 1), 5);

  u64 st[16];
  sd_memset(st, 0, sizeof st);
  SD_EXPECT("fstat", sd_sys2(SYS_fstat, fd, st), 0);
  SD_EXPECT("st_size", (i64)st[6], 18);

  SD_EXPECT("lseek_0", sd_lseek((int)fd, 0, SEEK_SET), 0);
  char a[7], b[7], c[7];
  sd_memset(a, '.', 7);
  sd_memset(b, '.', 7);
  sd_memset(c, '.', 7);
  struct sd_iovec r[3];
  r[0].base = a;
  r[0].len = 7;
  r[1].base = b;
  r[1].len = 7;
  r[2].base = c;
  r[2].len = 7;
  SD_EXPECT("readv_18", sd_readv((int)fd, r, 3), 18);
  show_buf("r0", a, 7);
  show_buf("r1", b, 7);
  show_buf("r2", c, 7);
  SD_EXPECT("close", sd_close((int)fd), 0);
  return 0;
}

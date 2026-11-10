// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// readv(2) scatter from stdin (stdin = "hello world"): one short readv, then 0 at EOF.
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
  char a[5], b[1], c[16];
  sd_memset(a, '.', 5);
  sd_memset(b, '.', 1);
  sd_memset(c, '.', 16);
  struct sd_iovec v[3];
  v[0].base = a;
  v[0].len = 5;
  v[1].base = b;
  v[1].len = 1;
  v[2].base = c;
  v[2].len = 16;
  SD_EXPECT("readv_stdin", sd_readv(0, v, 3), 11);
  show_buf("seg0", a, 5);
  show_buf("seg1", b, 1);
  show_buf("seg2", c, 16);
  SD_EXPECT("readv_stdin_eof", sd_readv(0, v, 3), 0);
  return 0;
}

// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// writev(2) gather to stdout/stderr: multi-segment, interior/leading/trailing zero-length segments.
#include "sd_rt.h"

static i64 sd_writev(int fd, const struct sd_iovec *iov, u64 cnt) {
  return sd_sys3(SYS_writev, (i64)fd, iov, cnt);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  struct sd_iovec v3[3];
  v3[0].base = "abc";
  v3[0].len = 3;
  v3[1].base = "defgh";
  v3[1].len = 5;
  v3[2].base = "\n";
  v3[2].len = 1;
  SD_EXPECT("writev_3seg", sd_writev(1, v3, 3), 9);

  /* Zero-length segments (including a NULL base) anywhere in the vector are skipped. */
  struct sd_iovec v5[5];
  v5[0].base = (void *)0;
  v5[0].len = 0;
  v5[1].base = "xy";
  v5[1].len = 2;
  v5[2].base = "IGNORED";
  v5[2].len = 0;
  v5[3].base = "z\n";
  v5[3].len = 2;
  v5[4].base = (void *)0;
  v5[4].len = 0;
  SD_EXPECT("writev_zero_segs", sd_writev(1, v5, 5), 4);

  /* A single segment behaves like write(2). */
  struct sd_iovec v1[1];
  v1[0].base = "single\n";
  v1[0].len = 7;
  SD_EXPECT("writev_1seg", sd_writev(1, v1, 1), 7);

  /* stderr gather. */
  struct sd_iovec ve[2];
  ve[0].base = "to-";
  ve[0].len = 3;
  ve[1].base = "stderr\n";
  ve[1].len = 7;
  SD_EXPECT("writev_stderr", sd_writev(2, ve, 2), 10);
  return 0;
}

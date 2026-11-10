// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// writev(2) EFAULT on stdout: NULL / unmapped iovec array, and a first segment with an unmapped base.
#include "sd_rt.h"

static i64 sd_writev(int fd, const struct sd_iovec *iov, u64 cnt) {
  return sd_sys3(SYS_writev, (i64)fd, iov, cnt);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("writev_vec_null", sd_writev(1, (void *)0, 1), -EFAULT);
  SD_EXPECT("writev_vec_unmapped", sd_writev(1, (void *)0x10000, 2), -EFAULT);
  struct sd_iovec v[2];
  v[0].base = (void *)0x10000;
  v[0].len = 4;
  v[1].base = "tail";
  v[1].len = 4;
  /* Fault in the first segment: nothing transferred, so the error is returned. */
  SD_EXPECT("writev_seg0_unmapped", sd_writev(1, v, 2), -EFAULT);
  v[0].base = (void *)0;
  v[0].len = 1;
  SD_EXPECT("writev_seg0_null", sd_writev(1, v, 1), -EFAULT);
  return 0;
}

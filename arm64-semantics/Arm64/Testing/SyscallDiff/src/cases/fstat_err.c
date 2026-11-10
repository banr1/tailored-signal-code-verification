// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// fstat(2) errors: EBADF (unopened / negative / closed fd, checked before statbuf) and EFAULT.
#include "sd_rt.h"

static const u8 ro_stat[128] = {1};

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  u64 st[16];
  SD_EXPECT("fstat_fd_99", sd_sys2(SYS_fstat, 99, st), -EBADF);
  SD_EXPECT("fstat_fd_neg1", sd_sys2(SYS_fstat, -1, st), -EBADF);
  /* A bad fd wins over a bad statbuf. */
  SD_EXPECT("fstat_fd_99_null", sd_sys2(SYS_fstat, 99, 0), -EBADF);

  i64 fd = sd_openat(AT_FDCWD, "st_err.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("fstat_null", sd_sys2(SYS_fstat, fd, 0), -EFAULT);
  SD_EXPECT("fstat_unmapped", sd_sys2(SYS_fstat, fd, 0x10000), -EFAULT);
  SD_EXPECT("fstat_rodata", sd_sys2(SYS_fstat, fd, ro_stat), -EFAULT);
  SD_EXPECT("close", sd_close((int)fd), 0);
  SD_EXPECT("fstat_closed", sd_sys2(SYS_fstat, fd, st), -EBADF);
  return 0;
}

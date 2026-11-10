// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// write(2) error paths: EBADF (unopened / negative fd) and EFAULT (unmapped buffer).
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("write_fd_99", sd_write(99, "x", 1), -EBADF);
  SD_EXPECT("write_fd_neg1", sd_write(-1, "x", 1), -EBADF);
  SD_EXPECT("write_null_buf", sd_write(1, (void *)0, 1), -EFAULT);
  SD_EXPECT("write_unmapped_buf", sd_write(1, (void *)0x10000, 8), -EFAULT);
  SD_EXPECT("write_zero_kaddr", sd_write(1, (void *)(1ULL << 63), 0), -EFAULT);
  return 0;
}

// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// clock_gettime(2) EFAULT for NULL / unmapped / read-only tp on valid clocks.
#include "sd_rt.h"

static const struct sd_timespec ro_ts = {1, 1};

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("realtime_null", sd_sys2(SYS_clock_gettime, CLOCK_REALTIME, 0), -EFAULT);
  SD_EXPECT("monotonic_unmapped", sd_sys2(SYS_clock_gettime, CLOCK_MONOTONIC, 0x10000), -EFAULT);
  SD_EXPECT("monotonic_rodata", sd_sys2(SYS_clock_gettime, CLOCK_MONOTONIC, &ro_ts), -EFAULT);
  return 0;
}

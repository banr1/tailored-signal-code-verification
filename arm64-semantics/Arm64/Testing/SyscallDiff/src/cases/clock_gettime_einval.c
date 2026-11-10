// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// clock_gettime(2) EINVAL for unregistered clock ids (10 = removed CLOCK_SGI_CYCLE, 12, 64).
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  /* posix_clocks[] has NULL slots at 10 and 12..15 and ends at 12 (or 24 with
     CONFIG_POSIX_AUX_CLOCKS, whose ids 16..23 are therefore avoided). */
  struct sd_timespec t;
  SD_EXPECT("clock_10", sd_sys2(SYS_clock_gettime, 10, &t), -EINVAL);
  SD_EXPECT("clock_12", sd_sys2(SYS_clock_gettime, 12, &t), -EINVAL);
  SD_EXPECT("clock_64", sd_sys2(SYS_clock_gettime, 64, &t), -EINVAL);
  return 0;
}

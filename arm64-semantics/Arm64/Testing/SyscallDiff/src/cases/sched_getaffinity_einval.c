// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// sched_getaffinity(2): len 0, 4, 7, and 9 (too small or not a multiple of 8) return -EINVAL.
#include "sd_rt.h"

static i64 aff(i64 pid, u64 len, void *mask) {
  return sd_sys3(SYS_sched_getaffinity, pid, len, mask);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  static u64 mask[16];
  SD_EXPECT("len_0", aff(0, 0, mask), -EINVAL);
  SD_EXPECT("len_4", aff(0, 4, mask), -EINVAL);
  SD_EXPECT("len_7", aff(0, 7, mask), -EINVAL);
  SD_EXPECT("len_9", aff(0, 9, mask), -EINVAL);
  return 0;
}

// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// sched_getaffinity(2): an unmapped or NULL user_mask_ptr with a valid len returns -EFAULT.
#include "sd_rt.h"

static i64 aff(i64 pid, u64 len, void *mask) {
  return sd_sys3(SYS_sched_getaffinity, pid, len, mask);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("mask_unmapped", aff(0, 1024, (void *)0x10000), -EFAULT);
  SD_EXPECT("mask_null", aff(0, 1024, 0), -EFAULT);
  return 0;
}

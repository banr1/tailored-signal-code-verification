// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// rt_sigprocmask(2): unmapped set, and unmapped oldset on a query, return -EFAULT.
#include "sd_rt.h"

static i64 spm(i64 how, const void *set, void *oset, u64 sz) {
  return sd_sys4(SYS_rt_sigprocmask, how, set, oset, sz);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("set_unmapped", spm(SIG_BLOCK, (void *)0x10000, 0, 8), -EFAULT);
  SD_EXPECT("set_wrap64", spm(SIG_BLOCK, (void *)(~0UL - 3), 0, 8), -EFAULT);
  SD_EXPECT("oldset_unmapped_query", spm(SIG_BLOCK, 0, (void *)0x10000, 8), -EFAULT);
  SD_EXPECT("oldset_wrap64_query", spm(SIG_BLOCK, 0, (void *)(~0UL - 3), 8), -EFAULT);
  return 0;
}

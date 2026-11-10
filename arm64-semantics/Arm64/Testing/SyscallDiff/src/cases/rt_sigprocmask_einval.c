// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// rt_sigprocmask(2): sigsetsize != 8 and an invalid how (with set != NULL) return -EINVAL.
#include "sd_rt.h"

static i64 spm(i64 how, const void *set, void *oset, u64 sz) {
  return sd_sys4(SYS_rt_sigprocmask, how, set, oset, sz);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  u64 usr1 = 1UL << (SIGUSR1 - 1);
  u64 old = 0xa5a5a5a5a5a5a5a5UL;
  SD_EXPECT("sigsetsize_4", spm(SIG_BLOCK, &usr1, 0, 4), -EINVAL);
  SD_EXPECT("sigsetsize_16", spm(SIG_BLOCK, &usr1, 0, 16), -EINVAL);
  SD_EXPECT("sigsetsize_0_query", spm(SIG_BLOCK, 0, &old, 0), -EINVAL);
  SD_EXPECT("how_3", spm(3, &usr1, 0, 8), -EINVAL);
  SD_EXPECT("how_neg1", spm(-1, &usr1, 0, 8), -EINVAL);
  old = 0xa5a5a5a5a5a5a5a5UL;
  SD_EXPECT("query", spm(SIG_BLOCK, 0, &old, 8), 0);
  SD_EXPECT("mask_unchanged", old, 0);
  return 0;
}

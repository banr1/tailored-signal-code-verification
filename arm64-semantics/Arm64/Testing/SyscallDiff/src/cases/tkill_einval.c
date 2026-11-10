// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// tkill(2) argument errors: tid <= 0 and sig outside [0, 64] return -EINVAL.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 tid = sd_sys0(SYS_gettid);
  SD_EXPECT("tkill_tid0", sd_sys2(SYS_tkill, 0, SIGABRT), -EINVAL);
  SD_EXPECT("tkill_tid_neg1", sd_sys2(SYS_tkill, -1, SIGABRT), -EINVAL);
  SD_EXPECT("tkill_sig65", sd_sys2(SYS_tkill, tid, 65), -EINVAL);
  SD_EXPECT("tkill_sig_neg1", sd_sys2(SYS_tkill, tid, -1), -EINVAL);
  return 0;
}

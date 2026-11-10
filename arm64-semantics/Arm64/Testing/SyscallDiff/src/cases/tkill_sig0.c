// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// tkill/tgkill(self, 0): signal 0 is an existence/permission probe and returns 0.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 pid = sd_sys0(SYS_getpid);
  i64 tid = sd_sys0(SYS_gettid);
  SD_EXPECT("tkill_sig0", sd_sys2(SYS_tkill, tid, 0), 0);
  SD_EXPECT("tgkill_sig0", sd_sys3(SYS_tgkill, pid, tid, 0), 0);
  return 0;
}

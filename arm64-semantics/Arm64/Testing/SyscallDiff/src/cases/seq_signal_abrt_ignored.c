// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// rt_sigaction(SIGABRT, SIG_IGN), then tkill/tgkill(self, SIGABRT) are dropped and return 0.
#include "sd_rt.h"

struct sd_ksigaction {
  u64 handler;
  u64 flags;
  u64 restorer;
  u64 mask;
};
static i64 sa(i64 sig, const void *act, void *oact, u64 sz) {
  return sd_sys4(SYS_rt_sigaction, sig, act, oact, sz);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  struct sd_ksigaction ign = {1, 0, 0, 0};
  i64 pid = sd_sys0(SYS_getpid);
  i64 tid = sd_sys0(SYS_gettid);
  SD_EXPECT("sigaction_abrt_ign", sa(SIGABRT, &ign, 0, 8), 0);
  SD_EXPECT("tkill_abrt", sd_sys2(SYS_tkill, tid, SIGABRT), 0);
  SD_EXPECT("tgkill_abrt", sd_sys3(SYS_tgkill, pid, tid, SIGABRT), 0);
  sd_puts("survived\n");
  return 0;
}

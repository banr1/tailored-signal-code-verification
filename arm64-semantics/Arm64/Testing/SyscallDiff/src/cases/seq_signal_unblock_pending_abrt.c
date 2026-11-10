// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// Blocked SIGABRT queued by tkill is delivered immediately upon SIG_UNBLOCK (signal 6, exit 134).
#include "sd_rt.h"

static i64 spm(i64 how, const void *set, void *oset, u64 sz) {
  return sd_sys4(SYS_rt_sigprocmask, how, set, oset, sz);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  u64 abrt = 1UL << (SIGABRT - 1);
  i64 tid = sd_sys0(SYS_gettid);
  SD_EXPECT("block_abrt", spm(SIG_BLOCK, &abrt, 0, 8), 0);
  SD_EXPECT("tkill_blocked", sd_sys2(SYS_tkill, tid, SIGABRT), 0);
  sd_puts("pre\n");
  spm(SIG_UNBLOCK, &abrt, 0, 8);
  sd_puts("post\n");
  return 0;
}

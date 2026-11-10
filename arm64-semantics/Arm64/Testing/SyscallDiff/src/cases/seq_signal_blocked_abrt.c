// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// Blocked SIGABRT: tkill/tgkill queue SIGABRT without terminating while blocked;
// setting SIG_IGN flushes pending SIGABRT, and exiting while blocked exits 0.
#include "sd_rt.h"

struct sd_ksigaction {
  u64 handler;
  u64 flags;
  u64 restorer;
  u64 mask;
};

static i64 spm(i64 how, const void *set, void *oset, u64 sz) {
  return sd_sys4(SYS_rt_sigprocmask, how, set, oset, sz);
}

static i64 sa(i64 sig, const void *act, void *oact, u64 sz) {
  return sd_sys4(SYS_rt_sigaction, sig, act, oact, sz);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  u64 abrt = 1UL << (SIGABRT - 1);
  struct sd_ksigaction ign = {1, 0, 0, 0};
  struct sd_ksigaction dfl = {0, 0, 0, 0};
  i64 pid = sd_sys0(SYS_getpid);
  i64 tid = sd_sys0(SYS_gettid);

  // 1. Block SIGABRT, queue via tkill, flush via SIG_IGN, restore SIG_DFL, unblock -> survives.
  SD_EXPECT("block1", spm(SIG_BLOCK, &abrt, 0, 8), 0);
  SD_EXPECT("tkill_pending1", sd_sys2(SYS_tkill, tid, SIGABRT), 0);
  SD_EXPECT("flush_ign", sa(SIGABRT, &ign, 0, 8), 0);
  SD_EXPECT("restore_dfl", sa(SIGABRT, &dfl, 0, 8), 0);
  SD_EXPECT("unblock_after_flush", spm(SIG_UNBLOCK, &abrt, 0, 8), 0);

  // 2. Block SIGABRT under SIG_DFL, queue via tkill + tgkill, print "ok\n", and exit 0.
  SD_EXPECT("block2", spm(SIG_BLOCK, &abrt, 0, 8), 0);
  SD_EXPECT("tkill_blocked", sd_sys2(SYS_tkill, tid, SIGABRT), 0);
  SD_EXPECT("tgkill_blocked", sd_sys3(SYS_tgkill, pid, tid, SIGABRT), 0);
  sd_puts("ok\n");
  return 0;
}

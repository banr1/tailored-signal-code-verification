// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// rt_sigaction(2): sa_flags is masked to UAPI_SA_FLAGS and SIGKILL/SIGSTOP are dropped from sa_mask.
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
  struct sd_ksigaction act = {1, ~0UL, 0, ~0UL}, old;
  SD_EXPECT("set_ign_all_bits", sa(SIGUSR1, &act, 0, 8), 0);
  sd_memset(&old, 0xa5, sizeof old);
  SD_EXPECT("query", sa(SIGUSR1, 0, &old, 8), 0);
  SD_EXPECT("handler", old.handler, 1);
  sd_show_hex("flags", old.flags);
  SD_EXPECT("flags_eq_uapi", old.flags, 0xdc000807UL);
  sd_show_hex("mask", old.mask);
  SD_EXPECT("mask_no_kill_stop", old.mask, ~0x40100UL);
  return 0;
}

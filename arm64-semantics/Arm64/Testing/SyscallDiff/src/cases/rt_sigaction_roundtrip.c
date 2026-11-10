// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// rt_sigaction(2): SIG_DFL -> SIG_IGN -> SIG_DFL on SIGUSR1, reading each old action back via oldact.
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
  struct sd_ksigaction ign = {1, 0, 0, 0}, dfl = {0, 0, 0, 0}, old;
  sd_memset(&old, 0xa5, sizeof old);
  SD_EXPECT("set_ign", sa(SIGUSR1, &ign, &old, 8), 0);
  SD_EXPECT("old0_handler", old.handler, 0);
  SD_EXPECT("old0_flags", old.flags, 0);
  SD_EXPECT("old0_restorer", old.restorer, 0);
  SD_EXPECT("old0_mask", old.mask, 0);
  sd_memset(&old, 0xa5, sizeof old);
  SD_EXPECT("query_ign", sa(SIGUSR1, 0, &old, 8), 0);
  SD_EXPECT("old1_handler", old.handler, 1);
  sd_memset(&old, 0xa5, sizeof old);
  SD_EXPECT("set_dfl", sa(SIGUSR1, &dfl, &old, 8), 0);
  SD_EXPECT("old2_handler", old.handler, 1);
  sd_memset(&old, 0xa5, sizeof old);
  SD_EXPECT("query_dfl", sa(SIGUSR1, 0, &old, 8), 0);
  SD_EXPECT("old3_handler", old.handler, 0);
  return 0;
}

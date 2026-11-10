// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// rt_sigaction(2): unmapped act, and unmapped oldact on a query, return -EFAULT.
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
  struct sd_ksigaction old;
  SD_EXPECT("act_unmapped", sa(SIGUSR1, (void *)0x10000, 0, 8), -EFAULT);
  SD_EXPECT("oldact_unmapped_query", sa(SIGUSR1, 0, (void *)0x10000, 8), -EFAULT);
  sd_memset(&old, 0xa5, sizeof old);
  SD_EXPECT("usr1_query", sa(SIGUSR1, 0, &old, 8), 0);
  SD_EXPECT("usr1_handler_unchanged", old.handler, 0);
  return 0;
}

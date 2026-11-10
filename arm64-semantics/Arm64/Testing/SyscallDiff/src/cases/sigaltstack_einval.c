// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// sigaltstack(2): ss_flags outside {0, SS_ONSTACK, SS_DISABLE} returns -EINVAL and changes nothing.
#include "sd_rt.h"

struct sd_stack {
  u64 sp;
  i32 flags;
  i32 pad;
  u64 size;
};
static u8 altstack[16384] __attribute__((aligned(16), unused));
static i64 sas(const void *ss, void *oss) { return sd_sys2(SYS_sigaltstack, ss, oss); }

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  struct sd_stack ss = {(u64)altstack, 4, 0, 8192}, old;
  SD_EXPECT("flags_4", sas(&ss, 0), -EINVAL);
  ss.flags = 3;
  SD_EXPECT("flags_3", sas(&ss, 0), -EINVAL);
  ss.flags = 0x40000000;
  SD_EXPECT("flags_bit30", sas(&ss, 0), -EINVAL);
  sd_memset(&old, 0xa5, sizeof old);
  SD_EXPECT("query", sas(0, &old), 0);
  SD_EXPECT("ss_flags_still_disabled", old.flags, SS_DISABLE);
  SD_EXPECT("ss_size_still_0", old.size, 0);
  return 0;
}

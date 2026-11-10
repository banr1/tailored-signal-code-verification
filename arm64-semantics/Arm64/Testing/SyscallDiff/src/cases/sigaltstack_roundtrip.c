// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// sigaltstack(2): install an 8192-byte stack, read it back, then replace it and read the old one.
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
  struct sd_stack ss = {(u64)altstack, 0, 0, 8192}, ss2 = {(u64)altstack, 0, 0, 16384}, old;
  SD_EXPECT("install_8192", sas(&ss, 0), 0);
  sd_memset(&old, 0xa5, sizeof old);
  SD_EXPECT("query1", sas(0, &old), 0);
  SD_CHECK("ss_sp1_is_altstack", old.sp == (u64)altstack);
  SD_EXPECT("ss_flags1", old.flags, 0);
  SD_EXPECT("ss_size1", old.size, 8192);
  sd_memset(&old, 0xa5, sizeof old);
  SD_EXPECT("install_16384", sas(&ss2, &old), 0);
  SD_CHECK("ss_sp2_is_altstack", old.sp == (u64)altstack);
  SD_EXPECT("ss_size2_is_previous", old.size, 8192);
  sd_memset(&old, 0xa5, sizeof old);
  SD_EXPECT("query3", sas(0, &old), 0);
  SD_EXPECT("ss_size3", old.size, 16384);
  return 0;
}

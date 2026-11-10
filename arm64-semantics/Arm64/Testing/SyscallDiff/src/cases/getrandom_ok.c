// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// getrandom(2) success: full count for each valid flag set; buffer changed, tail canary untouched.
#include "sd_rt.h"

static int all_eq(const u8 *p, u64 n, u8 v) {
  for (u64 i = 0; i < n; i++)
    if (p[i] != v) return 0;
  return 1;
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  /* Random bytes are never printed; only the return count and "not all sentinel" are. The
     chance that 32 random bytes are all 0xAA is 2^-256. */
  static const u64 flags[5] = {0, GRND_NONBLOCK, GRND_INSECURE, GRND_RANDOM | GRND_NONBLOCK,
                               GRND_INSECURE | GRND_NONBLOCK};
  static const char *names[5] = {"flags_0", "flags_nonblock", "flags_insecure",
                                 "flags_random_nonblock", "flags_insecure_nonblock"};
  u8 buf[40];
  for (int i = 0; i < 5; i++) {
    sd_memset(buf, 0xAA, sizeof buf);
    SD_EXPECT(names[i], sd_sys3(SYS_getrandom, buf, 32, flags[i]), 32);
    SD_CHECK("changed", !all_eq(buf, 32, 0xAA));
    SD_CHECK("canary", all_eq(buf + 32, 8, 0xAA));
  }
  /* flags is `unsigned int`: upper 32 bits of x2 are ignored. */
  sd_memset(buf, 0xAA, sizeof buf);
  SD_EXPECT("flags_hi_bits", sd_sys3(SYS_getrandom, buf, 32, 0x100000000UL), 32);
  /* Odd, unaligned length and buffer. */
  sd_memset(buf, 0xAA, sizeof buf);
  SD_EXPECT("unaligned_7", sd_sys3(SYS_getrandom, buf + 1, 7, 0), 7);
  SD_CHECK("canary_head", buf[0] == 0xAA);
  SD_CHECK("canary_tail", all_eq(buf + 8, 32, 0xAA));
  return 0;
}

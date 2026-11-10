// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// getrandom(2) EINVAL on a valid buffer: unknown flag bits and GRND_INSECURE | GRND_RANDOM.
#include "sd_rt.h"

static int all_eq(const u8 *p, u64 n, u8 v) {
  for (u64 i = 0; i < n; i++)
    if (p[i] != v) return 0;
  return 1;
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  u8 buf[16];
  sd_memset(buf, 0xAA, sizeof buf);
  SD_EXPECT("flags_8", sd_sys3(SYS_getrandom, buf, 16, 0x8), -EINVAL);
  SD_EXPECT("flags_80000000", sd_sys3(SYS_getrandom, buf, 16, 0x80000000UL), -EINVAL);
  SD_EXPECT("flags_insecure_random", sd_sys3(SYS_getrandom, buf, 16, GRND_INSECURE | GRND_RANDOM),
            -EINVAL);
  SD_EXPECT("flags_all3", sd_sys3(SYS_getrandom, buf, 16, 0x7), -EINVAL);
  /* Flags are checked before the length: zero length still fails. */
  SD_EXPECT("flags_8_len0", sd_sys3(SYS_getrandom, buf, 0, 0x8), -EINVAL);
  SD_CHECK("untouched", all_eq(buf, 16, 0xAA));
  return 0;
}

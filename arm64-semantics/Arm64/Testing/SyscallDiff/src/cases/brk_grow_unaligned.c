// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// brk(2) to an unaligned address returns it exactly; the whole final page is mapped and zeroed.
#include "sd_rt.h"

/* Store `v` at the first and last byte of every 64-byte chunk of `[base, base + len)`. */
static inline void mm_fill(u64 base, u64 len, u8 v) {
  volatile u8 *p = (volatile u8 *)base;
  for (u64 i = 0; i < len; i += 64) {
    p[i] = v;
    p[i + 63 < len ? i + 63 : len - 1] = v;
  }
}

/* 1 iff the first and last byte of every 64-byte chunk of `[base, base + len)` equal `v`. */
static inline int mm_all_eq(u64 base, u64 len, u8 v) {
  volatile u8 *p = (volatile u8 *)base;
  for (u64 i = 0; i < len; i += 64)
    if (p[i] != v || p[i + 63 < len ? i + 63 : len - 1] != v) return 0;
  return 1;
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  u64 start = ((u64)sd_brk(0) + PAGE - 1) & ~(PAGE - 1);
  u64 want = start + PAGE + 123;
  SD_CHECK("brk_ret_exact", sd_brk(want) == (i64)want);
  SD_CHECK("brk_query_exact", sd_brk(0) == (i64)want);
  SD_CHECK("pages_zero", mm_all_eq(start, 2 * PAGE, 0));
  mm_fill(start + PAGE, PAGE, 0x33);
  SD_CHECK("last_page_written", mm_all_eq(start + PAGE, PAGE, 0x33));
  SD_CHECK("brk_same_page_ret", sd_brk(want + 100) == (i64)(want + 100));
  SD_CHECK("brk_same_page_query", sd_brk(0) == (i64)(want + 100));
  return 0;
}

// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// brk(2) grow by 4 pages: returns the new break; the new heap pages read zero and are writable.
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
  u64 end = start + 4 * PAGE;
  SD_CHECK("brk_grow_ret", sd_brk(end) == (i64)end);
  SD_CHECK("brk_query_new", sd_brk(0) == (i64)end);
  SD_CHECK("heap_zero", mm_all_eq(start, 4 * PAGE, 0));
  mm_fill(start, 4 * PAGE, 0x5a);
  SD_CHECK("heap_written", mm_all_eq(start, 4 * PAGE, 0x5a));
  return 0;
}

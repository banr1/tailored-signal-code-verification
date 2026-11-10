// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// munmap(2) EINVAL on unaligned addr, len == 0, and len past TASK_SIZE; the mapping stays intact.
#include "sd_rt.h"

#define MM_RW (PROT_READ | PROT_WRITE)

#define MM_PA (MAP_PRIVATE | MAP_ANONYMOUS)

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

static inline int mm_page_aligned(i64 a) { return a > 0 && ((u64)a & (PAGE - 1)) == 0; }

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 p = sd_mmap(0, 2 * PAGE, MM_RW, MM_PA, -1, 0);
  SD_CHECK("mmap_aligned", mm_page_aligned(p));
  if (!mm_page_aligned(p)) return 0;
  mm_fill(p, 2 * PAGE, 0x42);
  SD_EXPECT("munmap_unaligned", sd_munmap(p + 1, PAGE), -EINVAL);
  SD_EXPECT("munmap_len0", sd_munmap(p, 0), -EINVAL);
  SD_EXPECT("munmap_len_huge", sd_munmap(p, 1UL << 62), -EINVAL);
  SD_CHECK("still_mapped", mm_all_eq(p, 2 * PAGE, 0x42));
  return 0;
}

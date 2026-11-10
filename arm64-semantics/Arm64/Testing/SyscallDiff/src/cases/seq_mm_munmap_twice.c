// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// munmap(2) of an already-unmapped range succeeds again (returns 0).
#include "sd_rt.h"

#define MM_RW (PROT_READ | PROT_WRITE)

#define MM_PA (MAP_PRIVATE | MAP_ANONYMOUS)

static inline int mm_page_aligned(i64 a) { return a > 0 && ((u64)a & (PAGE - 1)) == 0; }

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 p = sd_mmap(0, 2 * PAGE, MM_RW, MM_PA, -1, 0);
  SD_CHECK("mmap_aligned", mm_page_aligned(p));
  if (!mm_page_aligned(p)) return 0;
  SD_EXPECT("munmap_first", sd_munmap(p, 2 * PAGE), 0);
  SD_EXPECT("munmap_second", sd_munmap(p, 2 * PAGE), 0);
  return 0;
}

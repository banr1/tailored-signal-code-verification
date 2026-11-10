// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// mmap(2) PROT_NONE mapping succeeds; a load from it raises SIGSEGV.
#include "sd_rt.h"

#define MM_PA (MAP_PRIVATE | MAP_ANONYMOUS)

static inline int mm_page_aligned(i64 a) { return a > 0 && ((u64)a & (PAGE - 1)) == 0; }

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 p = sd_mmap(0, PAGE, PROT_NONE, MM_PA, -1, 0);
  SD_CHECK("mmap_none_aligned", mm_page_aligned(p));
  if (!mm_page_aligned(p)) return 0;
  sd_puts("about_to_fault\n");
  u8 v = *(volatile u8 *)p;
  SD_SHOW("unreachable", v);
  return 0;
}

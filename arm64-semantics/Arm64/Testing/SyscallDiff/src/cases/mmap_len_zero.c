// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// mmap(2) with len == 0 fails with EINVAL for both PROT_READ|PROT_WRITE and PROT_NONE.
#include "sd_rt.h"

#define MM_RW (PROT_READ | PROT_WRITE)

#define MM_PA (MAP_PRIVATE | MAP_ANONYMOUS)

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("mmap_len0_rw", sd_mmap(0, 0, MM_RW, MM_PA, -1, 0), -EINVAL);
  SD_EXPECT("mmap_len0_none", sd_mmap(0, 0, PROT_NONE, MM_PA, -1, 0), -EINVAL);
  return 0;
}

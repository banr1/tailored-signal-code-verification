// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// brk(2) query paths: brk(0) and brk(addr below start_brk) return the current break unchanged.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 b0 = sd_brk(0);
  SD_CHECK("brk0_positive", b0 > 0);
  SD_CHECK("brk0_stable", sd_brk(0) == b0);
  SD_CHECK("brk_below_start_is_query", sd_brk(PAGE) == b0);
  SD_CHECK("brk_same_value", sd_brk((u64)b0) == b0);
  SD_CHECK("brk0_unchanged", sd_brk(0) == b0);
  return 0;
}

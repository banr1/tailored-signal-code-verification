// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// set_tid_address(2): returns the caller's tid for valid, NULL, and unmapped tidptr without writing it.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  static volatile int slot = 0x5a5a;
  i64 tid = sd_sys0(SYS_gettid);
  SD_CHECK("valid_ptr_ret_tid", sd_sys1(SYS_set_tid_address, &slot) == tid);
  SD_EXPECT("slot_untouched", slot, 0x5a5a);
  SD_CHECK("unmapped_ptr_ret_tid", sd_sys1(SYS_set_tid_address, (void *)0x10000) == tid);
  SD_CHECK("null_ptr_ret_tid", sd_sys1(SYS_set_tid_address, 0) == tid);
  return 0;
}

// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// sched_getaffinity(2): pid 0 and pid getpid() return a non-empty mask of ret % 8 == 0 bytes, rest untouched.
#include "sd_rt.h"

static i64 aff(i64 pid, u64 len, void *mask) {
  return sd_sys3(SYS_sched_getaffinity, pid, len, mask);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  static u8 mask[1024];
  sd_memset(mask, 0xa5, sizeof mask);
  i64 ret = aff(0, sizeof mask, mask);
  SD_CHECK("ret_pos", ret > 0);
  SD_CHECK("ret_mult_8", ret % 8 == 0);
  int any = 0;
  for (i64 i = 0; i < ret && i < (i64)sizeof mask; i++) any |= mask[i];
  SD_CHECK("mask_nonempty", any != 0);
  int tail_ok = 1;
  for (i64 i = ret; i >= 0 && i < (i64)sizeof mask; i++) tail_ok &= mask[i] == 0xa5;
  SD_CHECK("tail_untouched", tail_ok);
  SD_CHECK("self_pid_same_len", aff(sd_sys0(SYS_getpid), sizeof mask, mask) == ret);
  return 0;
}

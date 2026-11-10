// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// getrandom(2) zero length on a valid buffer: returns 0 and writes nothing (all flag sets).
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  u8 buf[4];
  sd_memset(buf, 0xAA, sizeof buf);
  SD_EXPECT("len0_buf", sd_sys3(SYS_getrandom, buf, 0, 0), 0);
  SD_EXPECT("len0_nonblock", sd_sys3(SYS_getrandom, buf, 0, GRND_NONBLOCK), 0);
  SD_EXPECT("len0_insecure", sd_sys3(SYS_getrandom, buf, 0, GRND_INSECURE), 0);
  SD_CHECK("untouched", buf[0] == 0xAA && buf[3] == 0xAA);
  return 0;
}

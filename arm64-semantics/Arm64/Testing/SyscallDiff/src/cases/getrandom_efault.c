// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// getrandom(2) EFAULT for NULL, unmapped, and read-only (.rodata) buffers with valid flags.
#include "sd_rt.h"

static const u8 ro_buf[16] = {1};

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("buf_null", sd_sys3(SYS_getrandom, 0, 16, 0), -EFAULT);
  SD_EXPECT("buf_unmapped", sd_sys3(SYS_getrandom, 0x10000, 16, GRND_NONBLOCK), -EFAULT);
  SD_EXPECT("buf_rodata", sd_sys3(SYS_getrandom, ro_buf, 16, 0), -EFAULT);
  return 0;
}

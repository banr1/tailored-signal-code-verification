// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) EFAULT: NULL and unmapped pathname pointers (with and without O_CREAT).
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("null_path", sd_openat(AT_FDCWD, (const char *)0, O_RDONLY, 0), -EFAULT);
  SD_EXPECT("null_path_creat", sd_openat(AT_FDCWD, (const char *)0, O_CREAT | O_WRONLY, 0644), -EFAULT);
  SD_EXPECT("unmapped_path", sd_openat(AT_FDCWD, (const char *)0x10000, O_RDONLY, 0), -EFAULT);
  return 0;
}

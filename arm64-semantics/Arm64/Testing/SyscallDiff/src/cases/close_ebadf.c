// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// close(2) EBADF: never-opened fd, negative fd, fd at the RLIMIT_NOFILE edge, INT_MAX.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("close_99", sd_close(99), -EBADF);
  SD_EXPECT("close_neg1", sd_close(-1), -EBADF);
  SD_EXPECT("close_1023", sd_close(1023), -EBADF);
  SD_EXPECT("close_intmax", sd_close(0x7fffffff), -EBADF);
  return 0;
}

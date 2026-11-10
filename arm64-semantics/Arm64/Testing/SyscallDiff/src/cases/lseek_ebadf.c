// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// lseek(2) EBADF: never-opened fd and negative fd.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("lseek_fd_99", sd_lseek(99, 0, SEEK_SET), -EBADF);
  SD_EXPECT("lseek_fd_neg1", sd_lseek(-1, 0, SEEK_SET), -EBADF);
  SD_EXPECT("lseek_fd_99_badwhence", sd_lseek(99, 0, 9), -EBADF);
  return 0;
}

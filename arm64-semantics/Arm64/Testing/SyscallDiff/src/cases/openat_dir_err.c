// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) on directory ".": write access / O_TRUNC / O_CREAT -> EISDIR, O_CREAT|O_EXCL -> EEXIST.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("dot_wronly", sd_openat(AT_FDCWD, ".", O_WRONLY, 0), -EISDIR);
  SD_EXPECT("dot_rdwr", sd_openat(AT_FDCWD, ".", O_RDWR, 0), -EISDIR);
  SD_EXPECT("dot_rdonly_trunc", sd_openat(AT_FDCWD, ".", O_RDONLY | O_TRUNC, 0), -EISDIR);
  SD_EXPECT("dot_creat", sd_openat(AT_FDCWD, ".", O_CREAT | O_RDONLY, 0644), -EISDIR);
  SD_EXPECT("dot_creat_excl", sd_openat(AT_FDCWD, ".", O_CREAT | O_EXCL | O_WRONLY, 0644), -EEXIST);
  return 0;
}

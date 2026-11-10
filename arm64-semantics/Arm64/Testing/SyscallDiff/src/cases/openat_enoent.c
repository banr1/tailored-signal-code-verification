// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) ENOENT: missing file without O_CREAT, missing parent dir (with/without O_CREAT), empty path.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("missing_rdonly", sd_openat(AT_FDCWD, "nope.txt", O_RDONLY, 0), -ENOENT);
  SD_EXPECT("missing_rdwr", sd_openat(AT_FDCWD, "nope.txt", O_RDWR, 0), -ENOENT);
  SD_EXPECT("missing_parent", sd_openat(AT_FDCWD, "nodir/f", O_RDONLY, 0), -ENOENT);
  SD_EXPECT("missing_parent_creat", sd_openat(AT_FDCWD, "nodir/f", O_CREAT | O_WRONLY, 0644), -ENOENT);
  SD_EXPECT("empty_path", sd_openat(AT_FDCWD, "", O_RDONLY, 0), -ENOENT);
  SD_EXPECT("empty_path_creat", sd_openat(AT_FDCWD, "", O_CREAT | O_WRONLY, 0644), -ENOENT);
  return 0;
}

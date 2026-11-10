// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) O_CREAT on a missing file without 0600 (owner read+write, e.g. mode 0444):
// Linux creates a read-only file; Lean fails closed because FsState does not track per-inode modes.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fd = sd_openat(AT_FDCWD, "ro.txt", O_CREAT | O_WRONLY, 0444);
  SD_CHECK("creat_0444_ok", fd >= 3);
  if (fd >= 0) sd_close((int)fd);
  return 0;
}

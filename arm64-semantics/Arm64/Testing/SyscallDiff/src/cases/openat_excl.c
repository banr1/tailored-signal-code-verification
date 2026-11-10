// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) O_CREAT|O_EXCL: creates a new file once, then EEXIST; O_EXCL without O_CREAT is ignored.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fd = sd_openat(AT_FDCWD, "x.txt", O_CREAT | O_EXCL | O_WRONLY, 0644);
  SD_CHECK("excl_create_ok", fd >= 3);
  SD_EXPECT("close", sd_close((int)fd), 0);
  SD_EXPECT("excl_existing", sd_openat(AT_FDCWD, "x.txt", O_CREAT | O_EXCL | O_RDWR, 0644), -EEXIST);
  SD_EXPECT("excl_existing_rdonly", sd_openat(AT_FDCWD, "x.txt", O_CREAT | O_EXCL | O_RDONLY, 0644),
            -EEXIST);
  fd = sd_openat(AT_FDCWD, "x.txt", O_EXCL | O_RDONLY, 0);
  SD_CHECK("excl_without_creat_ok", fd >= 3);
  SD_EXPECT("close2", sd_close((int)fd), 0);
  return 0;
}

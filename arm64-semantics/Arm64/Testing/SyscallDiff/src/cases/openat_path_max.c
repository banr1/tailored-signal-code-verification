// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) pathname length: no NUL within PATH_MAX (4096) -> ENAMETOOLONG; a 4095-byte path is walked.
#include "sd_rt.h"

static char big[4200];

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  for (int i = 0; i < 4200; i++) big[i] = 'a';
  /* 4200 non-NUL bytes: getname hits PATH_MAX before any NUL. */
  SD_EXPECT("no_nul_4200", sd_openat(AT_FDCWD, big, O_RDONLY, 0), -ENAMETOOLONG);
  /* Exactly 4096 bytes before the NUL is still too long (PATH_MAX includes the NUL). */
  big[4096] = 0;
  SD_EXPECT("len_4096", sd_openat(AT_FDCWD, big, O_RDONLY, 0), -ENAMETOOLONG);
  /* 4095 bytes fits: "./" x 2045 + "nope." (5) = 4095 bytes, resolving to missing "nope.". */
  for (int i = 0; i < 4090; i += 2) {
    big[i] = '.';
    big[i + 1] = '/';
  }
  big[4090] = 'n';
  big[4091] = 'o';
  big[4092] = 'p';
  big[4093] = 'e';
  big[4094] = '.';
  big[4095] = 0;
  SD_EXPECT("len_4095_enoent", sd_openat(AT_FDCWD, big, O_RDONLY, 0), -ENOENT);
  return 0;
}

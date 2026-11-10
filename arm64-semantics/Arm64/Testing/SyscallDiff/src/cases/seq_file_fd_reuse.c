// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) allocates the lowest free fd: after closing two of three fds, reopens reuse the lowest first.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 a = sd_openat(AT_FDCWD, "a", O_CREAT | O_WRONLY, 0644);
  i64 b = sd_openat(AT_FDCWD, "b", O_CREAT | O_WRONLY, 0644);
  i64 c = sd_openat(AT_FDCWD, "c", O_CREAT | O_WRONLY, 0644);
  SD_CHECK("a_ok", a >= 3);
  SD_CHECK("increasing", a < b && b < c);
  SD_EXPECT("close_b", sd_close((int)b), 0);
  i64 d = sd_openat(AT_FDCWD, "a", O_RDONLY, 0);
  SD_CHECK("d_reuses_b", d == b);
  /* Free c then a: the next open takes a (lowest), the one after takes c. */
  SD_EXPECT("close_c", sd_close((int)c), 0);
  SD_EXPECT("close_a", sd_close((int)a), 0);
  i64 e = sd_openat(AT_FDCWD, ".", O_RDONLY, 0);
  SD_CHECK("e_reuses_a", e == a);
  i64 f = sd_openat(AT_FDCWD, "c", O_RDONLY, 0);
  SD_CHECK("f_reuses_c", f == c);
  SD_EXPECT("close_d", sd_close((int)d), 0);
  SD_EXPECT("close_e", sd_close((int)e), 0);
  SD_EXPECT("close_f", sd_close((int)f), 0);
  return 0;
}

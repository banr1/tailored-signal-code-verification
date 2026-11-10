// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) 64 times on one file yields 64 distinct increasing fds; closing two mid fds lets reopens reuse them in order.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fds[64];
  int increasing = 1, closed = 1;
  for (int i = 0; i < 64; i++) {
    fds[i] = sd_openat(AT_FDCWD, "m.txt", O_CREAT | O_RDWR, 0644);
    if (fds[i] < 3 || (i > 0 && fds[i] <= fds[i - 1])) increasing = 0;
  }
  SD_CHECK("increasing", increasing);
  SD_EXPECT("close_40", sd_close((int)fds[40]), 0);
  SD_EXPECT("close_20", sd_close((int)fds[20]), 0);
  i64 x = sd_openat(AT_FDCWD, "m.txt", O_RDONLY, 0);
  i64 y = sd_openat(AT_FDCWD, "m.txt", O_RDONLY, 0);
  SD_CHECK("x_reuses_20", x == fds[20]);
  SD_CHECK("y_reuses_40", y == fds[40]);
  fds[20] = x;
  fds[40] = y;
  for (int i = 0; i < 64; i++)
    if (sd_close((int)fds[i]) != 0) closed = 0;
  SD_CHECK("all_closed", closed);
  i64 fd = sd_openat(AT_FDCWD, "m.txt", O_RDONLY, 0);
  SD_CHECK("reuses_first", fd == fds[0]);
  sd_close((int)fd);
  return 0;
}

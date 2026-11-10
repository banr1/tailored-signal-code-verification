// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// clock_gettime(2) REALTIME/MONOTONIC/MONOTONIC_RAW/BOOTTIME: ret 0, nsec in range, monotonic order.
#include "sd_rt.h"

#define CLOCK_MONOTONIC_RAW 4
#define CLOCK_REALTIME_COARSE 5
#define CLOCK_MONOTONIC_COARSE 6
#define CLOCK_BOOTTIME 7

static int ts_valid(const struct sd_timespec *t) {
  return t->sec >= 0 && t->nsec >= 0 && t->nsec < 1000000000L;
}
static int ts_le(const struct sd_timespec *a, const struct sd_timespec *b) {
  return a->sec < b->sec || (a->sec == b->sec && a->nsec <= b->nsec);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  /* Values are never printed (host clock vs. model oracle); only properties are. */
  static const int clocks[6] = {CLOCK_REALTIME, CLOCK_MONOTONIC, CLOCK_MONOTONIC_RAW,
                                CLOCK_REALTIME_COARSE, CLOCK_MONOTONIC_COARSE, CLOCK_BOOTTIME};
  static const char *names[6] = {"realtime", "monotonic", "monotonic_raw",
                                 "realtime_coarse", "monotonic_coarse", "boottime"};
  for (int i = 0; i < 6; i++) {
    struct sd_timespec t;
    t.sec = -7;
    t.nsec = -7;
    SD_EXPECT(names[i], sd_sys2(SYS_clock_gettime, clocks[i], &t), 0);
    SD_CHECK("valid", ts_valid(&t));
  }
  struct sd_timespec a, b;
  SD_EXPECT("mono_a", sd_sys2(SYS_clock_gettime, CLOCK_MONOTONIC, &a), 0);
  SD_EXPECT("mono_b", sd_sys2(SYS_clock_gettime, CLOCK_MONOTONIC, &b), 0);
  SD_CHECK("mono_nondecreasing", ts_le(&a, &b));
  return 0;
}

// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// ppoll(2) EFAULT: unmapped timeout, NULL / unmapped ufds, and read-only ufds (revents write-back).
#include "sd_rt.h"

/* Valid-looking entry (fd 1, events 0) in .rodata: readable, not writable. */
static const struct sd_pollfd ro_fds[1] = {{1, 0, 0}};

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  struct sd_pollfd p[1];
  p[0].fd = 1;
  p[0].events = 0;
  p[0].revents = 0;
  struct sd_timespec ts;
  ts.sec = 0;
  ts.nsec = 0;
  SD_EXPECT("ppoll_tsp_unmapped", sd_sys5(SYS_ppoll, p, 1, 0x10000, 0, 8), -EFAULT);
  SD_EXPECT("ppoll_ufds_null", sd_sys5(SYS_ppoll, 0, 1, &ts, 0, 8), -EFAULT);
  SD_EXPECT("ppoll_ufds_unmapped", sd_sys5(SYS_ppoll, 0x10000, 2, &ts, 0, 8), -EFAULT);
  SD_EXPECT("ppoll_ufds_rodata", sd_sys5(SYS_ppoll, ro_fds, 1, &ts, 0, 8), -EFAULT);
  return 0;
}

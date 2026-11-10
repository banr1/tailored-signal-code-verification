// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// ppoll(2) zero-timeout probes: fds 0/1/2 with events = 0 (revents cleared, ret 0) and nfds = 0.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  struct sd_timespec ts;
  ts.sec = 0;
  ts.nsec = 0;
  struct sd_pollfd p[3];
  for (int i = 0; i < 3; i++) {
    p[i].fd = i;
    p[i].events = 0;
    p[i].revents = 0x7fff; /* overwritten by the kernel */
  }
  SD_EXPECT("ppoll_stdio3", sd_sys5(SYS_ppoll, p, 3, &ts, 0, 8), 0);
  SD_EXPECT("revents0", p[0].revents, 0);
  SD_EXPECT("revents1", p[1].revents, 0);
  SD_EXPECT("revents2", p[2].revents, 0);
  /* Same fd listed twice. */
  p[0].fd = 1;
  p[1].fd = 1;
  p[0].revents = 0x55;
  SD_EXPECT("ppoll_dup", sd_sys5(SYS_ppoll, p, 2, &ts, 0, 8), 0);
  SD_EXPECT("revents_dup", p[0].revents, 0);
  /* nfds = 0: ufds is never read; sigmask NULL ignores sigsetsize. */
  SD_EXPECT("ppoll_nfds0_null", sd_sys5(SYS_ppoll, 0, 0, &ts, 0, 0), 0);
  SD_EXPECT("ppoll_nfds0_size99", sd_sys5(SYS_ppoll, p, 0, &ts, 0, 99), 0);
  return 0;
}

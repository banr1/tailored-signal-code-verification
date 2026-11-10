// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// ppoll(2) EINVAL: invalid timeout (nsec >= 1e9, negative sec/nsec) and sigsetsize != 8 with a mask.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  struct sd_pollfd p[1];
  p[0].fd = 1;
  p[0].events = 0;
  p[0].revents = 0;
  struct sd_timespec ts;
  ts.sec = 0;
  ts.nsec = 1000000000;
  SD_EXPECT("ppoll_nsec_1e9", sd_sys5(SYS_ppoll, p, 1, &ts, 0, 8), -EINVAL);
  ts.nsec = -1;
  SD_EXPECT("ppoll_nsec_neg", sd_sys5(SYS_ppoll, p, 1, &ts, 0, 8), -EINVAL);
  ts.sec = -1;
  ts.nsec = 0;
  SD_EXPECT("ppoll_sec_neg", sd_sys5(SYS_ppoll, p, 1, &ts, 0, 8), -EINVAL);
  /* Valid zero timeout, non-NULL sigmask with sigsetsize != sizeof(sigset_t) = 8. */
  ts.sec = 0;
  u64 mask = 0;
  SD_EXPECT("ppoll_sigsetsize_4", sd_sys5(SYS_ppoll, p, 1, &ts, &mask, 4), -EINVAL);
  SD_EXPECT("ppoll_sigsetsize_16", sd_sys5(SYS_ppoll, p, 1, &ts, &mask, 16), -EINVAL);
  return 0;
}

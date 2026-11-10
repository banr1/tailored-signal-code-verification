// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// getpid/gettid: positive, stable across calls, and equal in a single-threaded process.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 pid = sd_sys0(SYS_getpid);
  i64 tid = sd_sys0(SYS_gettid);
  SD_CHECK("getpid_pos", pid > 0);
  SD_CHECK("gettid_pos", tid > 0);
  SD_CHECK("pid_eq_tid", pid == tid);
  SD_CHECK("getpid_stable", sd_sys0(SYS_getpid) == pid);
  SD_CHECK("gettid_stable", sd_sys0(SYS_gettid) == tid);
  return 0;
}

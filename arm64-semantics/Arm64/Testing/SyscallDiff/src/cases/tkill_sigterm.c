// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// tkill(self, SIGTERM) with the default disposition terminates the process by signal 15.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  sd_puts("before_sigterm\n");
  sd_sys2(SYS_tkill, sd_sys0(SYS_gettid), SIGTERM);
  sd_puts("not_reached\n");
  return 0;
}

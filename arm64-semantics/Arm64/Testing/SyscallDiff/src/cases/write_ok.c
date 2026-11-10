// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// write(2) success paths on stdout/stderr: full, zero-length, and multi-call byte counts.
#include "sd_rt.h"

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("write_stdout_5", sd_write(1, "hello", 5), 5);
  SD_EXPECT("write_stdout_nl", sd_write(1, "\n", 1), 1);
  SD_EXPECT("write_stdout_zero", sd_write(1, "x", 0), 0);
  SD_EXPECT("write_stderr_6", sd_write(2, "err!!\n", 6), 6);
  /* Zero-length write with a NULL buffer is still 0 (no access_ok fault for count 0). */
  SD_EXPECT("write_stdout_zero_null", sd_write(1, (void *)0, 0), 0);
  return 0;
}

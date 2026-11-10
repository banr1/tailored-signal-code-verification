// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// fcntl(2) unknown command (0x7fff) on an open regular file returns EINVAL (do_fcntl default case).
#include "sd_rt.h"

static i64 sd_fcntl(i64 fd, u64 cmd, u64 arg) { return sd_sys3(SYS_fcntl, fd, cmd, arg); }

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fd = sd_openat(AT_FDCWD, "fc_cmd.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("fcntl_cmd_7fff", sd_fcntl(fd, 0x7fff, 0), -EINVAL);
  SD_EXPECT("close", sd_close((int)fd), 0);
  return 0;
}

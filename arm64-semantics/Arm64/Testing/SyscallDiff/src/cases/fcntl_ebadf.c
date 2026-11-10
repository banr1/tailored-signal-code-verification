// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// fcntl(2) EBADF for F_GETFD/F_SETFD on unopened, negative, and closed fds.
#include "sd_rt.h"

static i64 sd_fcntl(i64 fd, u64 cmd, u64 arg) { return sd_sys3(SYS_fcntl, fd, cmd, arg); }

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  SD_EXPECT("getfd_fd_99", sd_fcntl(99, F_GETFD, 0), -EBADF);
  SD_EXPECT("setfd_fd_99", sd_fcntl(99, F_SETFD, FD_CLOEXEC), -EBADF);
  SD_EXPECT("getfd_fd_neg1", sd_fcntl(-1, F_GETFD, 0), -EBADF);
  /* fd is `unsigned int`: the upper 32 bits of x0 are ignored (0x1_0000_0063 is fd 99). */
  SD_EXPECT("getfd_fd_hi99", sd_fcntl(0x100000063L, F_GETFD, 0), -EBADF);
  i64 fd = sd_openat(AT_FDCWD, "fc_err.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("close", sd_close((int)fd), 0);
  SD_EXPECT("getfd_closed", sd_fcntl(fd, F_GETFD, 0), -EBADF);
  SD_EXPECT("setfd_closed", sd_fcntl(fd, F_SETFD, 0), -EBADF);
  return 0;
}

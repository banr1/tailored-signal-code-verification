// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// fcntl(2) F_GETFD/F_SETFD FD_CLOEXEC round trip, O_CLOEXEC at open, non-FD_CLOEXEC bits ignored.
#include "sd_rt.h"

static i64 sd_fcntl(i64 fd, u64 cmd, u64 arg) { return sd_sys3(SYS_fcntl, fd, cmd, arg); }

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fd = sd_openat(AT_FDCWD, "fc.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("getfd_initial", sd_fcntl(fd, F_GETFD, 0), 0);
  SD_EXPECT("setfd_cloexec", sd_fcntl(fd, F_SETFD, FD_CLOEXEC), 0);
  SD_EXPECT("getfd_set", sd_fcntl(fd, F_GETFD, 0), FD_CLOEXEC);
  SD_EXPECT("setfd_0", sd_fcntl(fd, F_SETFD, 0), 0);
  SD_EXPECT("getfd_cleared", sd_fcntl(fd, F_GETFD, 0), 0);
  /* Only bit 0 of the argument matters. */
  SD_EXPECT("setfd_3", sd_fcntl(fd, F_SETFD, 3), 0);
  SD_EXPECT("getfd_3", sd_fcntl(fd, F_GETFD, 0), FD_CLOEXEC);
  SD_EXPECT("setfd_2", sd_fcntl(fd, F_SETFD, 2), 0);
  SD_EXPECT("getfd_2", sd_fcntl(fd, F_GETFD, 0), 0);
  SD_EXPECT("close", sd_close((int)fd), 0);

  i64 fd2 = sd_openat(AT_FDCWD, "fc.txt", O_RDONLY | O_CLOEXEC, 0);
  SD_CHECK("open_cloexec_ok", fd2 >= 3);
  SD_EXPECT("getfd_o_cloexec", sd_fcntl(fd2, F_GETFD, 0), FD_CLOEXEC);
  SD_EXPECT("close2", sd_close((int)fd2), 0);

  i64 dfd = sd_openat(AT_FDCWD, ".", O_RDONLY | O_DIRECTORY, 0);
  SD_CHECK("open_dir_ok", dfd >= 3);
  SD_EXPECT("setfd_dir", sd_fcntl(dfd, F_SETFD, FD_CLOEXEC), 0);
  SD_EXPECT("getfd_dir", sd_fcntl(dfd, F_GETFD, 0), FD_CLOEXEC);
  SD_EXPECT("close_dir", sd_close((int)dfd), 0);
  return 0;
}

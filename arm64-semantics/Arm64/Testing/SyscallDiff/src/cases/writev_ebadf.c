// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// writev(2) EBADF: unopened / negative / closed fds and a regular file opened O_RDONLY.
#include "sd_rt.h"

static i64 sd_writev(int fd, const struct sd_iovec *iov, u64 cnt) {
  return sd_sys3(SYS_writev, (i64)fd, iov, cnt);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  struct sd_iovec v[1];
  v[0].base = "data";
  v[0].len = 4;
  SD_EXPECT("writev_fd_99", sd_writev(99, v, 1), -EBADF);
  SD_EXPECT("writev_fd_neg1", sd_writev(-1, v, 1), -EBADF);

  i64 fd = sd_openat(AT_FDCWD, "wv_ro.txt", O_CREAT | O_WRONLY | O_TRUNC, 0644);
  SD_CHECK("create_ok", fd >= 3);
  SD_EXPECT("close_w", sd_close((int)fd), 0);
  fd = sd_openat(AT_FDCWD, "wv_ro.txt", O_RDONLY, 0);
  SD_CHECK("open_ro_ok", fd >= 3);
  /* FMODE_WRITE is checked before the vector is imported. */
  SD_EXPECT("writev_rdonly", sd_writev((int)fd, v, 1), -EBADF);
  SD_EXPECT("close_ro", sd_close((int)fd), 0);
  SD_EXPECT("writev_closed", sd_writev((int)fd, v, 1), -EBADF);
  return 0;
}

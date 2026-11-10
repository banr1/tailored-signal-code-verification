// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// readv(2) EBADF (unopened / O_WRONLY fd) and EISDIR (directory fd from O_DIRECTORY open of ".").
#include "sd_rt.h"

static i64 sd_readv(int fd, const struct sd_iovec *iov, u64 cnt) {
  return sd_sys3(SYS_readv, (i64)fd, iov, cnt);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  char buf[8];
  struct sd_iovec v[1];
  v[0].base = buf;
  v[0].len = 8;
  SD_EXPECT("readv_fd_99", sd_readv(99, v, 1), -EBADF);
  SD_EXPECT("readv_fd_neg1", sd_readv(-1, v, 1), -EBADF);

  i64 fd = sd_openat(AT_FDCWD, "rv_wo.txt", O_CREAT | O_WRONLY | O_TRUNC, 0644);
  SD_CHECK("open_wo_ok", fd >= 3);
  SD_EXPECT("write_4", sd_write((int)fd, "abcd", 4), 4);
  SD_EXPECT("readv_wronly", sd_readv((int)fd, v, 1), -EBADF);
  SD_EXPECT("close_wo", sd_close((int)fd), 0);

  i64 dfd = sd_openat(AT_FDCWD, ".", O_RDONLY | O_DIRECTORY, 0);
  SD_CHECK("open_dir_ok", dfd >= 3);
  SD_EXPECT("readv_dir", sd_readv((int)dfd, v, 1), -EISDIR);
  SD_EXPECT("close_dir", sd_close((int)dfd), 0);
  return 0;
}

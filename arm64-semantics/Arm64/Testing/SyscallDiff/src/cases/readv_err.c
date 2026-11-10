// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// readv(2) on a readable file: EINVAL (iovcnt > 1024, negative len) and EFAULT (vector, segment, rodata).
#include "sd_rt.h"

static i64 sd_readv(int fd, const struct sd_iovec *iov, u64 cnt) {
  return sd_sys3(SYS_readv, (i64)fd, iov, cnt);
}

static const char ro_buf[16] = "read-only-buffer";

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  i64 fd = sd_openat(AT_FDCWD, "rv_err.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("write_8", sd_write((int)fd, "12345678", 8), 8);
  SD_EXPECT("lseek_0", sd_lseek((int)fd, 0, SEEK_SET), 0);

  char buf[8];
  struct sd_iovec v[2];
  v[0].base = buf;
  v[0].len = 4;
  v[1].base = buf + 4;
  v[1].len = (u64)-2;
  SD_EXPECT("readv_cnt_1025", sd_readv((int)fd, v, 1025), -EINVAL);
  SD_EXPECT("readv_len_neg", sd_readv((int)fd, v, 2), -EINVAL);
  SD_EXPECT("readv_vec_null", sd_readv((int)fd, (void *)0, 1), -EFAULT);
  v[0].base = (void *)0x10000;
  v[0].len = 4;
  SD_EXPECT("readv_seg_unmapped", sd_readv((int)fd, v, 1), -EFAULT);
  v[0].base = (void *)ro_buf;
  v[0].len = 4;
  SD_EXPECT("readv_seg_rodata", sd_readv((int)fd, v, 1), -EFAULT);
  /* None of the failed calls consumed file data. */
  SD_EXPECT("lseek_cur", sd_lseek((int)fd, 0, SEEK_CUR), 0);
  SD_EXPECT("close", sd_close((int)fd), 0);
  return 0;
}

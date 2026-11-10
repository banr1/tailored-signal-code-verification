// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// writev(2) EINVAL on stdout: iovcnt > UIO_MAXIOV (1024) and a negative (ssize_t) iov_len.
#include "sd_rt.h"

static i64 sd_writev(int fd, const struct sd_iovec *iov, u64 cnt) {
  return sd_sys3(SYS_writev, (i64)fd, iov, cnt);
}

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  struct sd_iovec v[2];
  v[0].base = "ok";
  v[0].len = 2;
  v[1].base = "no";
  v[1].len = 2;
  /* nr_segs > UIO_MAXIOV is rejected before the vector is read. */
  SD_EXPECT("writev_cnt_1025", sd_writev(1, v, 1025), -EINVAL);
  /* A negative iov_len anywhere in the vector rejects the whole call; nothing is written. */
  v[1].len = (u64)-1;
  SD_EXPECT("writev_len_neg1", sd_writev(1, v, 2), -EINVAL);
  v[1].len = 0x8000000000000000UL;
  SD_EXPECT("writev_len_min", sd_writev(1, v, 2), -EINVAL);
  return 0;
}

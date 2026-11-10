// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// ioctl(2) terminal requests on a regular file return ENOTTY (TCGETS, TIOCGWINSZ, TCSETS).
#include "sd_rt.h"

#define TCGETS 0x5401
#define TCSETS 0x5402
#define TIOCGWINSZ 0x5413

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  u8 buf[64];
  sd_memset(buf, 0, sizeof buf);
  i64 fd = sd_openat(AT_FDCWD, "io.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  SD_EXPECT("ioctl_tcgets", sd_sys3(SYS_ioctl, fd, TCGETS, buf), -ENOTTY);
  SD_EXPECT("ioctl_tiocgwinsz", sd_sys3(SYS_ioctl, fd, TIOCGWINSZ, buf), -ENOTTY);
  SD_EXPECT("ioctl_tcsets", sd_sys3(SYS_ioctl, fd, TCSETS, buf), -ENOTTY);
  SD_EXPECT("close", sd_close((int)fd), 0);
  return 0;
}

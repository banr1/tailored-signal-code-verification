// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.


// openat(2) path component length: a 255-byte name is created; a 256-byte name -> ENAMETOOLONG (NAME_MAX).
#include "sd_rt.h"

static char name[300];

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  for (int i = 0; i < 300; i++) name[i] = 'n';
  name[255] = 0;
  i64 fd = sd_openat(AT_FDCWD, name, O_CREAT | O_WRONLY, 0644);
  SD_CHECK("name_255_creat_ok", fd >= 3);
  if (fd >= 0) sd_close((int)fd);
  name[255] = 'n';
  name[256] = 0;
  SD_EXPECT("name_256_creat", sd_openat(AT_FDCWD, name, O_CREAT | O_WRONLY, 0644), -ENAMETOOLONG);
  SD_EXPECT("name_256_rdonly", sd_openat(AT_FDCWD, name, O_RDONLY, 0), -ENAMETOOLONG);
  // Trailing '/' with O_CREAT returns -EISDIR before final-segment NAME_MAX (fs/namei.c:4707),
  // whereas O_RDONLY without O_CREAT and strict ancestor "n"*256 + "/." return -ENAMETOOLONG.
  name[256] = '/';
  name[257] = 0;
  SD_EXPECT("name_256_slash_creat", sd_openat(AT_FDCWD, name, O_CREAT | O_WRONLY, 0644), -EISDIR);
  SD_EXPECT("name_256_slash_rdonly", sd_openat(AT_FDCWD, name, O_RDONLY, 0), -ENAMETOOLONG);
  name[257] = '.';
  name[258] = 0;
  SD_EXPECT("name_256_slash_dot_creat", sd_openat(AT_FDCWD, name, O_CREAT | O_WRONLY, 0644), -ENAMETOOLONG);
  return 0;
}

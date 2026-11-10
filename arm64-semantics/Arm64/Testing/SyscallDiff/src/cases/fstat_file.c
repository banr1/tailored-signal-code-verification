// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

// fstat(2) on a created regular file: S_IFREG, st_nlink, st_size tracking writes; directory S_IFDIR.
#include "sd_rt.h"

/* AArch64 `struct stat` (include/uapi/asm-generic/stat.h), 128 bytes. Only deterministic fields
   (type bits, nlink of a regular file, size) are printed: dev/ino/uid/gid/times/blksize/blocks
   and permission bits (umask) are host-dependent. */
struct sd_stat {
  u64 st_dev;
  u64 st_ino;
  u32 st_mode;
  u32 st_nlink;
  u32 st_uid;
  u32 st_gid;
  u64 st_rdev;
  u64 pad1;
  i64 st_size;
  i32 st_blksize;
  i32 pad2;
  i64 st_blocks;
  u64 rest[7];
};
#define S_IFMT 0170000
#define S_IFREG 0100000
#define S_IFDIR 0040000

int sd_main(int argc, char **argv) {
  (void)argc;
  (void)argv;
  struct sd_stat st;
  i64 fd = sd_openat(AT_FDCWD, "st.txt", O_CREAT | O_RDWR | O_TRUNC, 0644);
  SD_CHECK("open_ok", fd >= 3);
  sd_memset(&st, 0xff, sizeof st);
  SD_EXPECT("fstat_empty", sd_sys2(SYS_fstat, fd, &st), 0);
  SD_EXPECT("ifmt_reg", st.st_mode & S_IFMT, S_IFREG);
  SD_EXPECT("nlink", st.st_nlink, 1);
  SD_EXPECT("size_empty", st.st_size, 0);

  SD_EXPECT("write_100a", sd_write((int)fd, &st, 100), 100);
  SD_EXPECT("write_100b", sd_write((int)fd, &st, 100), 100);
  sd_memset(&st, 0xff, sizeof st);
  SD_EXPECT("fstat_200", sd_sys2(SYS_fstat, fd, &st), 0);
  SD_EXPECT("size_200", st.st_size, 200);
  SD_CHECK("blksize_pos", st.st_blksize > 0);

  /* Sparse extension via lseek past EOF + 1-byte write. */
  SD_EXPECT("lseek_4999", sd_lseek((int)fd, 4999, SEEK_SET), 4999);
  SD_EXPECT("write_1", sd_write((int)fd, "z", 1), 1);
  SD_EXPECT("fstat_5000", sd_sys2(SYS_fstat, fd, &st), 0);
  SD_EXPECT("size_5000", st.st_size, 5000);
  SD_EXPECT("close", sd_close((int)fd), 0);

  i64 dfd = sd_openat(AT_FDCWD, ".", O_RDONLY | O_DIRECTORY, 0);
  SD_CHECK("open_dir_ok", dfd >= 3);
  sd_memset(&st, 0xff, sizeof st);
  SD_EXPECT("fstat_dir", sd_sys2(SYS_fstat, dfd, &st), 0);
  SD_EXPECT("ifmt_dir", st.st_mode & S_IFMT, S_IFDIR);
  SD_EXPECT("close_dir", sd_close((int)dfd), 0);
  return 0;
}

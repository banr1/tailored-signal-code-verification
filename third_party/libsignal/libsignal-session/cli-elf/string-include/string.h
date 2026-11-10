/*
 * Copyright © 2005-2020 Rich Felker, et al.
 * SPDX-License-Identifier: MIT
 *
 * From musl 1.2.5 (https://musl.libc.org/, full license text in musl's `COPYRIGHT`):
 * the `src/include/string.h` wrapper (its `__memrchr` declaration) with
 * `#include "../../include/string.h"` replaced by `#include_next <string.h>`, plus the
 * `mem*` prototypes of `include/string.h` and `bcmp` of `include/strings.h`.
 * See `third_party/libsignal/README.md`.
 */

#ifndef MUSL_STRING_STRING_H
#define MUSL_STRING_STRING_H

#include <features.h>
#include_next <string.h>

void *memcpy(void *__restrict, const void *__restrict, size_t);
void *memmove(void *, const void *, size_t);
void *memset(void *, int, size_t);
int memcmp(const void *, const void *, size_t);
int bcmp(const void *, const void *, size_t);
void *memchr(const void *, int, size_t);
void *memrchr(const void *, int, size_t);
hidden void *__memrchr(const void *, int, size_t);
void *memccpy(void *__restrict, const void *__restrict, int, size_t);
void *mempcpy(void *, const void *, size_t);
void *memmem(const void *, size_t, const void *, size_t);

#endif

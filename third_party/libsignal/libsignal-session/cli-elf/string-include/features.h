/*
 * Copyright © 2005-2020 Rich Felker, et al.
 * SPDX-License-Identifier: MIT
 *
 * From musl 1.2.5 `src/include/features.h` (https://musl.libc.org/, full license text in musl's
 * `COPYRIGHT`), with the include guard renamed and `#include "../../include/features.h"`
 * replaced by `#include_next <features.h>`. See `third_party/libsignal/README.md`.
 */

#ifndef MUSL_STRING_FEATURES_H
#define MUSL_STRING_FEATURES_H

#include_next <features.h>

#define weak __attribute__((__weak__))
#define hidden __attribute__((__visibility__("hidden")))
#define weak_alias(old, new) \
	extern __typeof(old) new __attribute__((__weak__, __alias__(#old)))

#endif

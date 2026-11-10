// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

/*
 * C FFI wrapper around Berkeley SoftFloat 3e (`ARM-VFPv2` specialization) (`[TEST ONLY]`).
 *
 * Exposes `softfloat_eval_batch` to `src/fp.rs` so IEEE-754 floating-point operations
 * (`f32`/`f64` add, sub, mul, div, sqrt, fma, rint, fcvt, fcvtzs/u, scvtf/ucvtf,
 * fmin/fmax/fminnm/fmaxnm, fcmp) can be audited and compared against `Arm64/Trusted/ISA/Float.lean`
 * independently of the Sail and Unicorn full-machine emulators.
 */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "softfloat.h"

static inline bool sf_is_nan32(uint32_t x) { return (x & 0x7fffffffU) > 0x7f800000U; }
static inline bool sf_is_snan32(uint32_t x) { return sf_is_nan32(x) && ((x & 0x00400000U) == 0); }
static inline bool sf_is_inf32(uint32_t x) { return (x & 0x7fffffffU) == 0x7f800000U; }
static inline bool sf_is_zero32(uint32_t x) { return (x & 0x7fffffffU) == 0; }

static inline bool sf_is_nan64(uint64_t x) {
  return (x & 0x7fffffffffffffffULL) > 0x7ff0000000000000ULL;
}
static inline bool sf_is_snan64(uint64_t x) {
  return sf_is_nan64(x) && ((x & 0x0008000000000000ULL) == 0);
}
static inline bool sf_is_inf64(uint64_t x) {
  return (x & 0x7fffffffffffffffULL) == 0x7ff0000000000000ULL;
}
static inline bool sf_is_zero64(uint64_t x) { return (x & 0x7fffffffffffffffULL) == 0; }

static uint32_t arm_fma32(uint32_t addend, uint32_t x, uint32_t y) {
  bool inf_zero = (sf_is_inf32(x) && sf_is_zero32(y)) || (sf_is_zero32(x) && sf_is_inf32(y));
  if (sf_is_snan32(addend) || sf_is_snan32(x) || sf_is_snan32(y) || inf_zero) {
    softfloat_raiseFlags(softfloat_flag_invalid);
  }
  if (sf_is_snan32(addend)) return addend | 0x00400000U;
  if (sf_is_snan32(x)) return x | 0x00400000U;
  if (sf_is_snan32(y)) return y | 0x00400000U;
  if (sf_is_nan32(addend)) return inf_zero ? 0x7fc00000U : addend;
  if (sf_is_nan32(x)) return x;
  if (sf_is_nan32(y)) return y;
  float32_t fa = {x}, fb = {y}, fc = {addend};
  return f32_mulAdd(fa, fb, fc).v;
}

static uint64_t arm_fma64(uint64_t addend, uint64_t x, uint64_t y) {
  bool inf_zero = (sf_is_inf64(x) && sf_is_zero64(y)) || (sf_is_zero64(x) && sf_is_inf64(y));
  if (sf_is_snan64(addend) || sf_is_snan64(x) || sf_is_snan64(y) || inf_zero) {
    softfloat_raiseFlags(softfloat_flag_invalid);
  }
  if (sf_is_snan64(addend)) return addend | 0x0008000000000000ULL;
  if (sf_is_snan64(x)) return x | 0x0008000000000000ULL;
  if (sf_is_snan64(y)) return y | 0x0008000000000000ULL;
  if (sf_is_nan64(addend)) return inf_zero ? 0x7ff8000000000000ULL : addend;
  if (sf_is_nan64(x)) return x;
  if (sf_is_nan64(y)) return y;
  float64_t fa = {x}, fb = {y}, fc = {addend};
  return f64_mulAdd(fa, fb, fc).v;
}

static uint32_t arm_minmax32(bool is_max, bool is_num, uint32_t a, uint32_t b) {
  if (sf_is_snan32(a) || sf_is_snan32(b)) {
    softfloat_raiseFlags(softfloat_flag_invalid);
  }
  if (is_num && !sf_is_snan32(a) && !sf_is_snan32(b)) {
    if (sf_is_nan32(a) && !sf_is_nan32(b)) a = b;
    else if (sf_is_nan32(b) && !sf_is_nan32(a)) b = a;
  }
  if (sf_is_snan32(a)) return a | 0x00400000U;
  if (sf_is_snan32(b)) return b | 0x00400000U;
  if (sf_is_nan32(a)) return a;
  if (sf_is_nan32(b)) return b;
  if (sf_is_zero32(a) && sf_is_zero32(b)) {
    bool sa = (a >> 31) != 0, sb = (b >> 31) != 0;
    bool sout = is_max ? (sa && sb) : (sa || sb);
    return sout ? 0x80000000U : 0U;
  }
  float32_t fa = {a}, fb = {b};
  if (is_max) return f32_lt_quiet(fb, fa) ? a : b;
  return f32_lt_quiet(fa, fb) ? a : b;
}

static uint64_t arm_minmax64(bool is_max, bool is_num, uint64_t a, uint64_t b) {
  if (sf_is_snan64(a) || sf_is_snan64(b)) {
    softfloat_raiseFlags(softfloat_flag_invalid);
  }
  if (is_num && !sf_is_snan64(a) && !sf_is_snan64(b)) {
    if (sf_is_nan64(a) && !sf_is_nan64(b)) a = b;
    else if (sf_is_nan64(b) && !sf_is_nan64(a)) b = a;
  }
  if (sf_is_snan64(a)) return a | 0x0008000000000000ULL;
  if (sf_is_snan64(b)) return b | 0x0008000000000000ULL;
  if (sf_is_nan64(a)) return a;
  if (sf_is_nan64(b)) return b;
  if (sf_is_zero64(a) && sf_is_zero64(b)) {
    bool sa = (a >> 63) != 0, sb = (b >> 63) != 0;
    bool sout = is_max ? (sa && sb) : (sa || sb);
    return sout ? 0x8000000000000000ULL : 0ULL;
  }
  float64_t fa = {a}, fb = {b};
  if (is_max) return f64_lt_quiet(fb, fa) ? a : b;
  return f64_lt_quiet(fa, fb) ? a : b;
}

static uint64_t sf_flags_to_arm_fpsr(uint_fast8_t sf_flags) {
  uint64_t fpsr = 0;
  if (sf_flags & softfloat_flag_invalid)   fpsr |= 0x01; // IOC
  if (sf_flags & softfloat_flag_infinite)  fpsr |= 0x02; // DZC
  if (sf_flags & softfloat_flag_overflow)  fpsr |= 0x04; // OFC
  if (sf_flags & softfloat_flag_underflow) fpsr |= 0x08; // UFC
  if (sf_flags & softfloat_flag_inexact)   fpsr |= 0x10; // IXC
  return fpsr;
}

void softfloat_eval_batch(const uint64_t *in_words, size_t count, uint64_t *out_words) {
  softfloat_detectTininess = softfloat_tininess_beforeRounding;
  for (size_t i = 0; i < count; i++) {
    uint64_t meta = in_words[i * 4];
    uint64_t a = in_words[i * 4 + 1];
    uint64_t b = in_words[i * 4 + 2];
    uint64_t c = in_words[i * 4 + 3];
    uint8_t op = (uint8_t)(meta & 0xff);
    uint8_t rm_code = (uint8_t)((meta >> 8) & 0xff);
    uint8_t sf_rm = softfloat_round_near_even;
    switch (rm_code) {
      case 0: sf_rm = softfloat_round_near_even; break;
      case 1: sf_rm = softfloat_round_max; break;
      case 2: sf_rm = softfloat_round_min; break;
      case 3: sf_rm = softfloat_round_minMag; break;
      default: sf_rm = softfloat_round_near_maxMag; break;
    }
    softfloat_roundingMode = sf_rm;
    softfloat_exceptionFlags = 0;

    float32_t a32 = {(uint32_t)a}, b32 = {(uint32_t)b};
    float64_t a64 = {a}, b64 = {b};
    uint64_t res = 0;
    switch (op) {
      case 0: res = f32_add(a32, b32).v; break;
      case 1: res = f32_sub(a32, b32).v; break;
      case 2: res = f32_mul(a32, b32).v; break;
      case 3: res = f32_div(a32, b32).v; break;
      case 4: res = f32_sqrt(a32).v; break;
      case 5: res = arm_fma32((uint32_t)c, (uint32_t)a, (uint32_t)b); break;
      case 6: res = f32_roundToInt(a32, sf_rm, false).v; break;
      case 7: res = f32_to_f64(a32).v; break;
      case 8:
        res = (uint32_t)f32_to_i32(a32, sf_rm, true);
        if (softfloat_exceptionFlags & softfloat_flag_invalid) softfloat_exceptionFlags &= ~softfloat_flag_inexact;
        break;
      case 9:
        res = (uint32_t)f32_to_ui32(a32, sf_rm, true);
        if (softfloat_exceptionFlags & softfloat_flag_invalid) softfloat_exceptionFlags &= ~softfloat_flag_inexact;
        break;
      case 10:
        res = (uint64_t)f32_to_i64(a32, sf_rm, true);
        if (softfloat_exceptionFlags & softfloat_flag_invalid) softfloat_exceptionFlags &= ~softfloat_flag_inexact;
        break;
      case 11:
        res = (uint64_t)f32_to_ui64(a32, sf_rm, true);
        if (softfloat_exceptionFlags & softfloat_flag_invalid) softfloat_exceptionFlags &= ~softfloat_flag_inexact;
        break;
      case 12: res = i32_to_f32((int32_t)(uint32_t)a).v; break;
      case 13: res = ui32_to_f32((uint32_t)a).v; break;
      case 14: res = i64_to_f32((int64_t)a).v; break;
      case 15: res = ui64_to_f32(a).v; break;
      case 16: res = arm_minmax32(false, false, (uint32_t)a, (uint32_t)b); break;
      case 17: res = arm_minmax32(true, false, (uint32_t)a, (uint32_t)b); break;
      case 18: res = arm_minmax32(false, true, (uint32_t)a, (uint32_t)b); break;
      case 19: res = arm_minmax32(true, true, (uint32_t)a, (uint32_t)b); break;
      case 20:
        if (sf_is_nan32((uint32_t)a) || sf_is_nan32((uint32_t)b)) {
          if (sf_is_snan32((uint32_t)a) || sf_is_snan32((uint32_t)b)) {
            softfloat_raiseFlags(softfloat_flag_invalid);
          }
          res = 3;
        } else if (f32_eq(a32, b32)) res = 6;
        else if (f32_lt_quiet(a32, b32)) res = 8;
        else res = 2;
        break;
      case 21: res = f32_roundToInt(a32, sf_rm, true).v; break;
      case 22:
        if (sf_is_nan32((uint32_t)a) || sf_is_nan32((uint32_t)b)) {
          softfloat_raiseFlags(softfloat_flag_invalid);
          res = 3;
        } else if (f32_eq(a32, b32)) res = 6;
        else if (f32_lt_quiet(a32, b32)) res = 8;
        else res = 2;
        break;
      case 32: res = f64_add(a64, b64).v; break;
      case 33: res = f64_sub(a64, b64).v; break;
      case 34: res = f64_mul(a64, b64).v; break;
      case 35: res = f64_div(a64, b64).v; break;
      case 36: res = f64_sqrt(a64).v; break;
      case 37: res = arm_fma64(c, a, b); break;
      case 38: res = f64_roundToInt(a64, sf_rm, false).v; break;
      case 39: res = f64_to_f32(a64).v; break;
      case 40:
        res = (uint32_t)f64_to_i32(a64, sf_rm, true);
        if (softfloat_exceptionFlags & softfloat_flag_invalid) softfloat_exceptionFlags &= ~softfloat_flag_inexact;
        break;
      case 41:
        res = (uint32_t)f64_to_ui32(a64, sf_rm, true);
        if (softfloat_exceptionFlags & softfloat_flag_invalid) softfloat_exceptionFlags &= ~softfloat_flag_inexact;
        break;
      case 42:
        res = (uint64_t)f64_to_i64(a64, sf_rm, true);
        if (softfloat_exceptionFlags & softfloat_flag_invalid) softfloat_exceptionFlags &= ~softfloat_flag_inexact;
        break;
      case 43:
        res = (uint64_t)f64_to_ui64(a64, sf_rm, true);
        if (softfloat_exceptionFlags & softfloat_flag_invalid) softfloat_exceptionFlags &= ~softfloat_flag_inexact;
        break;
      case 44: res = i32_to_f64((int32_t)(uint32_t)a).v; break;
      case 45: res = ui32_to_f64((uint32_t)a).v; break;
      case 46: res = i64_to_f64((int64_t)a).v; break;
      case 47: res = ui64_to_f64(a).v; break;
      case 48: res = arm_minmax64(false, false, a, b); break;
      case 49: res = arm_minmax64(true, false, a, b); break;
      case 50: res = arm_minmax64(false, true, a, b); break;
      case 51: res = arm_minmax64(true, true, a, b); break;
      case 52:
        if (sf_is_nan64(a) || sf_is_nan64(b)) {
          if (sf_is_snan64(a) || sf_is_snan64(b)) {
            softfloat_raiseFlags(softfloat_flag_invalid);
          }
          res = 3;
        } else if (f64_eq(a64, b64)) res = 6;
        else if (f64_lt_quiet(a64, b64)) res = 8;
        else res = 2;
        break;
      case 53: res = f64_roundToInt(a64, sf_rm, true).v; break;
      case 54:
        if (sf_is_nan64(a) || sf_is_nan64(b)) {
          softfloat_raiseFlags(softfloat_flag_invalid);
          res = 3;
        } else if (f64_eq(a64, b64)) res = 6;
        else if (f64_lt_quiet(a64, b64)) res = 8;
        else res = 2;
        break;
      default: res = 0; break;
    }
    out_words[i * 2] = res;
    out_words[i * 2 + 1] = sf_flags_to_arm_fpsr(softfloat_exceptionFlags);
  }
}

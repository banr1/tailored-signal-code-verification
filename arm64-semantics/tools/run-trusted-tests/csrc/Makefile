# Build the Berkeley SoftFloat 3e IEEE-754 oracle (`libsoftfloat_armvfpv2.a` +
# `libsoftfloat_ffi.a`) and the TestFloat 3e vector generator (`testfloat_gen`).
#
# Note: The Sail Armv9.4-A ISA simulator C model is built and linked by the standalone
# `tools/sail-aarch64` crate (`tools/sail-aarch64/csrc/Makefile`).

CC ?= cc
AR ?= ar

FP_TOOLS_DIR ?=
OUT_DIR      ?= .

SF_INC_DIR   := $(FP_TOOLS_DIR)/softfloat3/source/include
SF_BUILD_DIR := $(FP_TOOLS_DIR)/softfloat3/build/Linux-x86_64-GCC
TF_BUILD_DIR := $(FP_TOOLS_DIR)/testfloat3/build/Linux-x86_64-GCC
SF_ARCHIVE   := $(FP_TOOLS_DIR)/libsoftfloat_armvfpv2.a
TF_STAMP     := $(FP_TOOLS_DIR)/.testfloat_gen_armvfpv2

.PHONY: all fp-tools softfloat-ffi

all: fp-tools softfloat-ffi

# 1. Berkeley SoftFloat 3e (`ARM-VFPv2` NaN specialization) & TestFloat 3e generator.
fp-tools: $(SF_ARCHIVE) $(TF_STAMP)

$(SF_ARCHIVE):
	@cp -n "$(FP_TOOLS_DIR)/softfloat3/source/8086-SSE/s_bf16UIToCommonNaN.c" \
		"$(FP_TOOLS_DIR)/softfloat3/source/ARM-VFPv2/" 2>/dev/null || true
	@cp -n "$(FP_TOOLS_DIR)/softfloat3/source/8086-SSE/s_commonNaNToBF16UI.c" \
		"$(FP_TOOLS_DIR)/softfloat3/source/ARM-VFPv2/" 2>/dev/null || true
	@grep -q softfloat_isSigNaNBF16UI "$(FP_TOOLS_DIR)/softfloat3/source/ARM-VFPv2/specialize.h" || \
		sed -i 's/#define defaultNaNF32UI/#define softfloat_isSigNaNBF16UI( uiA ) ((((uiA) \& 0x7FC0) == 0x7F80) \&\& ((uiA) \& 0x003F))\nvoid softfloat_bf16UIToCommonNaN( uint_fast16_t uiA, struct commonNaN *zPtr );\nuint_fast16_t softfloat_commonNaNToBF16UI( const struct commonNaN *aPtr );\n#define defaultNaNF32UI/' \
		"$(FP_TOOLS_DIR)/softfloat3/source/ARM-VFPv2/specialize.h"
	$(MAKE) -C "$(SF_BUILD_DIR)" clean
	$(MAKE) -C "$(SF_BUILD_DIR)" -j8 SPECIALIZE_TYPE=ARM-VFPv2
	cp -f "$(SF_BUILD_DIR)/softfloat.a" "$(SF_ARCHIVE)"

$(TF_STAMP): $(SF_ARCHIVE)
	$(MAKE) -C "$(TF_BUILD_DIR)" clean
	$(MAKE) -C "$(TF_BUILD_DIR)" -j8 SOFTFLOAT_DIR="$(FP_TOOLS_DIR)/softfloat3" \
		TESTFLOAT_OPTS="-DFLOAT16 -DFLOAT64 -DEXTFLOAT80 -DFLOAT128 -DFLOAT_ROUND_ODD -DLONG_DOUBLE_IS_EXTFLOAT80" \
		testfloat_gen
	touch "$(TF_STAMP)"

# 2. SoftFloat 3e FFI wrapper (`softfloat_ffi.c` -> `libsoftfloat_ffi.a`).
softfloat-ffi: $(OUT_DIR)/libsoftfloat_ffi.a

$(OUT_DIR)/libsoftfloat_ffi.a: softfloat_ffi.c $(SF_ARCHIVE)
	$(CC) -O2 -pipe -Wall -Wextra -I"$(SF_INC_DIR)" -c softfloat_ffi.c -o "$(OUT_DIR)/softfloat_ffi.o"
	rm -f "$@"
	$(AR) rcs "$@" "$(OUT_DIR)/softfloat_ffi.o"

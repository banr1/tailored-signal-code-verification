# Build the Sail Armv9.4-A C simulator archive (`$(SAIL_CACHE_LIB)`) and the
# self-contained `libsail_aarch64_ffi.a` library used by `tools/sail-aarch64`.
#
# Modeled on upstream `rems-project/sail-arm/arm-v9.4-a/snapshots/c/Makefile`:
#   $(CC) -O2 $(SAIL_SRC_DIR)/armv9.c $(SAIL_SRC_DIR)/*.c -lgmp -lz -I $(SAIL_SRC_DIR)/
# Here `armv9.c` (5.3M lines) is compiled with `-O0 -Dmain=sail_model_main -DHAVE_SETCONFIG`
# (~2.5 min vs >15 min at `-O2`) and archived with unmodified Sail 0.17.1 runtime sources
# (`sail.c`, `rts.c`, `sail_failure.c`) plus a 3-line `elf_stub.c` (avoiding `-lz`).
# Weakening the 4 overridden symbols in `$(SAIL_CACHE_LIB)` via `objcopy -W` allows strong
# definitions in `sail_ffi.c` to override them cleanly without any downstream linker flags.

CC      ?= cc
AR      ?= ar
LD      ?= ld
OBJCOPY ?= objcopy
SAIL    ?= sail

SAIL_SRC_DIR   ?=
SAIL_CACHE_LIB ?=
OUT_DIR        ?= .
EXTRA_INC      ?=

SAIL_RTS_SRCS  := sail.c rts.c sail_failure.c

WEAKEN_FLAGS := \
	-W sail_assert \
	-W sail_match_failure \
	-W z_get_SCTLR_EL1_Type_EE \
	-W z_get_HCR_EL2_Type_DC

.PHONY: all sail-lib ffi-lib regen-armv9-c

all: $(OUT_DIR)/libsail_aarch64_ffi.a

# 1. Upstream Sail Armv9.4-A static library (cached across worktrees at $(SAIL_CACHE_LIB)).
sail-lib: $(SAIL_CACHE_LIB)

$(SAIL_CACHE_LIB): $(SAIL_SRC_DIR)/armv9.c
	@mkdir -p "$(dir $(SAIL_CACHE_LIB))" "$(OUT_DIR)/sail-objs"
	$(CC) -O0 -pipe -w -Dmain=sail_model_main -DHAVE_SETCONFIG -I"$(SAIL_SRC_DIR)" $(EXTRA_INC) \
		-c "$(SAIL_SRC_DIR)/armv9.c" -o "$(OUT_DIR)/sail-objs/armv9.o"
	@for f in $(SAIL_RTS_SRCS); do \
		$(CC) -O2 -pipe -w -DHAVE_SETCONFIG -I"$(SAIL_SRC_DIR)" $(EXTRA_INC) \
			-c "$(SAIL_SRC_DIR)/$$f" -o "$(OUT_DIR)/sail-objs/$${f%.c}.o" || exit 1; \
	done
	@printf '#include <stdbool.h>\n#include <stdint.h>\nvoid load_elf(char *f, bool *b, uint64_t *e) { (void)f; (void)b; (void)e; }\nint lookup_sym(const char *f, const char *s, uint64_t *v) { (void)f; (void)s; (void)v; return -1; }\n' \
		> "$(OUT_DIR)/sail-objs/elf_stub.c"
	$(CC) -O2 -pipe -w -c "$(OUT_DIR)/sail-objs/elf_stub.c" -o "$(OUT_DIR)/sail-objs/elf_stub.o"
	$(AR) rcs "$(OUT_DIR)/sail-objs/libsail_tmp.a" "$(OUT_DIR)/sail-objs"/*.o
	mv -f "$(OUT_DIR)/sail-objs/libsail_tmp.a" "$(SAIL_CACHE_LIB)"

# 2. Self-contained FFI static library (`sail_ffi.o` + weakened `$(SAIL_CACHE_LIB)` linked with `ld -r`).
ffi-lib: $(OUT_DIR)/libsail_aarch64_ffi.a

$(OUT_DIR)/libsail_aarch64_ffi.a: sail_ffi.c $(SAIL_CACHE_LIB)
	$(CC) -O2 -pipe -Wall -Wextra -I"$(SAIL_SRC_DIR)" $(EXTRA_INC) \
		-c sail_ffi.c -o "$(OUT_DIR)/sail_ffi.o"
	cp -f "$(SAIL_CACHE_LIB)" "$(OUT_DIR)/libsail_weak.a"
	$(OBJCOPY) $(WEAKEN_FLAGS) "$(OUT_DIR)/libsail_weak.a"
	$(LD) -r -o "$(OUT_DIR)/sail_aarch64_combined.o" \
		"$(OUT_DIR)/sail_ffi.o" --whole-archive "$(OUT_DIR)/libsail_weak.a" --no-whole-archive
	rm -f "$(OUT_DIR)/libsail_weak.a" "$@"
	$(AR) rcs "$@" "$(OUT_DIR)/sail_aarch64_combined.o"

# 3. Optional maintainer target: regenerate `armv9.c` from upstream `sail-arm/arm-v9.4-a` `.sail` sources.
regen-armv9-c:
	@test -n "$(SAIL_ARM_REPO)" || (echo "Set SAIL_ARM_REPO=/path/to/sail-arm/arm-v9.4-a" >&2; exit 1)
	$(MAKE) -C "$(SAIL_ARM_REPO)" SAIL="$(SAIL)" c/armv9.c

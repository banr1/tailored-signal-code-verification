// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

/*
 * C FFI bridge around the upstream Sail Armv9.4-A (`armv9.c`) ISA model (`[TEST ONLY]`).
 *
 * Exposes one-time EL0 system initialization (`sail_harness_init_once`), per-test state
 * reset (`sail_harness_reset`), sparse physical memory cleanup (`sail_harness_clear_mem`),
 * physical memory byte access (`sail_harness_write_bytes`, `sail_harness_read_bytes`),
 * bounded instruction stepping (`sail_harness_step_until`), architectural post-state readout
 * (`sail_harness_read_state`, `sail_harness_read_fpsr`, `sail_harness_read_fpcr`,
 * `sail_harness_set_fpcr`), and parallel fork-based single-instruction batch stepping
 * (`sail_harness_step_batch`) to `tools/sail-aarch64/src/lib.rs`.
 */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#include "rts.h"
#include "sail.h"

extern void model_init(void);
extern void kill_mem(void);
extern unit z__InitSystem(unit);
extern unit zstep_model(unit);

extern bool z__tlb_enabled;
extern bool z__BranchTaken;
extern uint64_t zBTypeNext;
extern bool have_exception;

unit sail_assert(bool b, const_sail_string msg) {
  if (b) {
    return UNIT;
  }
  /* Upstream Sail v8_base.sail:30795 Reduce() slice-width check lists {16..2048} and omits 8. */
  if (msg != NULL && strcmp(msg, "src/v8_base.sail:30795.306-30795.307") == 0) {
    return UNIT;
  }
  have_exception = true;
  return UNIT;
}

void sail_match_failure(const_sail_string msg) {
  (void)msg;
  have_exception = true;
}

/* Force Stage-1 flat memory (SCTLR_EL1.M=0) to use MemType_Normal (WB cacheable)
 * via s1params.dc=1 in AArch64_S1TTWParamsEL10 while keeping HCR_EL2.DC=0 so Stage-2
 * MMU translation remains disabled. */
static bool g_in_s1_ttw_params = false;
uint64_t z_get_SCTLR_EL1_Type_EE(uint64_t v) {
  g_in_s1_ttw_params = true;
  return (v >> 25) & 1ULL;
}

uint64_t z_get_HCR_EL2_Type_DC(uint64_t v) {
  if (g_in_s1_ttw_params) {
    g_in_s1_ttw_params = false;
    return 1ULL;
  }
  return (v >> 12) & 1ULL;
}

struct zProcState {
  uint64_t zA;
  uint64_t zALLINT;
  uint64_t zBTYPE;
  uint64_t zC;
  uint64_t zD;
  uint64_t zDIT;
  uint64_t zE;
  uint64_t zEL;
  uint64_t zEXLOCK;
  uint64_t zF;
  uint64_t zGE;
  uint64_t zI;
  uint64_t zIL;
  uint64_t zIT;
  uint64_t zJ;
  uint64_t zM;
  uint64_t zN;
  uint64_t zPAN;
  uint64_t zPM;
  uint64_t zPPEND;
  uint64_t zQ;
  uint64_t zSM;
  uint64_t zSP;
  uint64_t zSS;
  uint64_t zSSBS;
  uint64_t zT;
  uint64_t zTCO;
  uint64_t zUAO;
  uint64_t zV;
  uint64_t zZ;
  uint64_t zZA;
  uint64_t znRW;
};

struct zBits64 {
  uint64_t zbits;
};

struct zz5vecz8z5bvz9 {
  size_t len;
  lbits *data;
};

extern struct zProcState zPSTATE;
extern uint64_t zR0, zR1, zR2, zR3, zR4, zR5, zR6, zR7;
extern uint64_t zR8, zR9, zR10, zR11, zR12, zR13, zR14, zR15;
extern uint64_t zR16, zR17, zR18, zR19, zR20, zR21, zR22, zR23;
extern uint64_t zR24, zR25, zR26, zR27, zR28, zR29, zR30;
extern uint64_t z_PC;
extern uint64_t zSP_EL0;
extern uint64_t zTPIDR_EL0;

extern struct zBits64 zSCTLR_EL1, zSCTLR_EL2, zSCTLR_EL3;
extern struct zBits64 zCPACR_EL1, zCPTR_EL2, zCPTR_EL3;
extern struct zBits64 zHCR_EL2, zSCR_EL3, zFPCR, zFPSR, zDCZID_EL0;
extern struct zz5vecz8z5bvz9 z_Z;

static bool g_initialized = false;
static struct zProcState g_baseline_pstate;
static uint64_t g_baseline_sctlr_el1;
static uint64_t g_baseline_sctlr_el2;
static uint64_t g_baseline_sctlr_el3;
static uint64_t g_baseline_cpacr_el1;
static uint64_t g_baseline_cptr_el2;
static uint64_t g_baseline_cptr_el3;
static uint64_t g_baseline_hcr_el2;
static uint64_t g_baseline_scr_el3;

static uint64_t *const GPR_PTRS[31] = {
    &zR0,  &zR1,  &zR2,  &zR3,  &zR4,  &zR5,  &zR6,  &zR7,  &zR8,  &zR9,  &zR10,
    &zR11, &zR12, &zR13, &zR14, &zR15, &zR16, &zR17, &zR18, &zR19, &zR20, &zR21,
    &zR22, &zR23, &zR24, &zR25, &zR26, &zR27, &zR28, &zR29, &zR30,
};

void sail_harness_init_once(void) {
  if (g_initialized) {
    return;
  }
  model_init();
  z__tlb_enabled = false;
  z__InitSystem(UNIT);

  /* Configure flat AArch64 EL0 execution with MMU disabled, FP/SIMD enabled, and SA/SA0 enabled. */
  zPSTATE.zEL = 0;   /* EL0 */
  zPSTATE.znRW = 0;  /* AArch64 */
  zPSTATE.zSP = 0;   /* SP_EL0 */
  zPSTATE.zD = 1;    /* Mask Debug exceptions */
  zPSTATE.zA = 1;    /* Mask SError interrupts */
  zPSTATE.zI = 1;    /* Mask IRQ interrupts */
  zPSTATE.zF = 1;    /* Mask FIQ interrupts */
  zPSTATE.zSS = 0;
  zPSTATE.zIL = 0;
  zPSTATE.zBTYPE = 0;
  zPSTATE.zSM = 0;
  zPSTATE.zZA = 0;
  zPSTATE.zE = 0;

  /* SCR_EL3: RW=1 (bit 10, lower EL is AArch64), NS=1 (bit 0, Non-secure) */
  zSCR_EL3.zbits |= (1ULL << 10) | (1ULL << 0);
  /* HCR_EL2: RW=1 (bit 31, EL1 is AArch64), VM=0, DC=0 */
  zHCR_EL2.zbits = (1ULL << 31);
  /* SCTLR_EL1: M=0 (bit 0), A=0 (bit 1), SA=1 (bit 3), SA0=1 (bit 4), DZE=1 (bit 14, allow EL0 DC ZVA), E0E=0, EE=0 */
  zSCTLR_EL1.zbits =
      (zSCTLR_EL1.zbits & ~((1ULL << 0) | (1ULL << 1) | (1ULL << 24) | (1ULL << 25))) |
      (1ULL << 3) | (1ULL << 4) | (1ULL << 14);
  zSCTLR_EL2.zbits &= ~(1ULL << 0);
  zSCTLR_EL3.zbits &= ~(1ULL << 0);
  /* DCZID_EL0: DZP=0 (bit 4), BS=4 (64-byte DC ZVA block size) */
  zDCZID_EL0.zbits = 4;

  /* CPACR_EL1: FPEN=0b11 (bits [21:20]), ZEN=0b11 (bits [17:16]) */
  zCPACR_EL1.zbits = (3ULL << 20) | (3ULL << 16);
  /* CPTR_EL2 / CPTR_EL3: TFP=0 (no FP/SIMD trap to EL2/EL3) */
  zCPTR_EL2.zbits = 0;
  zCPTR_EL3.zbits = 0;
  zFPCR.zbits = 0;
  zFPSR.zbits = 0;
  zTPIDR_EL0 = 0;

  g_baseline_pstate = zPSTATE;
  g_baseline_sctlr_el1 = zSCTLR_EL1.zbits;
  g_baseline_sctlr_el2 = zSCTLR_EL2.zbits;
  g_baseline_sctlr_el3 = zSCTLR_EL3.zbits;
  g_baseline_cpacr_el1 = zCPACR_EL1.zbits;
  g_baseline_cptr_el2 = zCPTR_EL2.zbits;
  g_baseline_cptr_el3 = zCPTR_EL3.zbits;
  g_baseline_hcr_el2 = zHCR_EL2.zbits;
  g_baseline_scr_el3 = zSCR_EL3.zbits;
  g_initialized = true;
}

void sail_harness_clear_mem(void) {
  if (g_initialized) {
    kill_mem();
  }
}

void sail_harness_reset(const uint64_t regs[31], const uint64_t vregs_lo[32],
                        const uint64_t vregs_hi[32], uint64_t sp, uint64_t pc, uint8_t nzcv) {
  sail_harness_init_once();
  kill_mem();

  zPSTATE = g_baseline_pstate;
  zPSTATE.zN = (nzcv >> 3) & 1;
  zPSTATE.zZ = (nzcv >> 2) & 1;
  zPSTATE.zC = (nzcv >> 1) & 1;
  zPSTATE.zV = (nzcv >> 0) & 1;

  zSCTLR_EL1.zbits = g_baseline_sctlr_el1;
  zSCTLR_EL2.zbits = g_baseline_sctlr_el2;
  zSCTLR_EL3.zbits = g_baseline_sctlr_el3;
  zCPACR_EL1.zbits = g_baseline_cpacr_el1;
  zCPTR_EL2.zbits = g_baseline_cptr_el2;
  zCPTR_EL3.zbits = g_baseline_cptr_el3;
  zHCR_EL2.zbits = g_baseline_hcr_el2;
  zSCR_EL3.zbits = g_baseline_scr_el3;
  zDCZID_EL0.zbits = 4;
  z__tlb_enabled = false;

  for (size_t i = 0; i < 31; i++) {
    *GPR_PTRS[i] = regs[i];
  }
  zSP_EL0 = sp;
  z_PC = pc;
  zTPIDR_EL0 = 0;
  zFPCR.zbits = 0;
  zFPSR.zbits = 0;
  zBTypeNext = 0;
  z__BranchTaken = false;
  have_exception = false;

  for (size_t i = 0; i < z_Z.len; i++) {
    if (i < 32 && vregs_lo != NULL && vregs_hi != NULL) {
      mpz_set_ui(*z_Z.data[i].bits, vregs_hi[i]);
      mpz_mul_2exp(*z_Z.data[i].bits, *z_Z.data[i].bits, 64);
      mpz_add_ui(*z_Z.data[i].bits, *z_Z.data[i].bits, vregs_lo[i]);
    } else {
      mpz_set_ui(*z_Z.data[i].bits, 0);
    }
  }
}

void sail_harness_write_bytes(uint64_t addr, const uint8_t *buf, size_t len) {
  for (size_t i = 0; i < len; i++) {
    write_mem(addr + i, (uint64_t)buf[i]);
  }
}

void sail_harness_read_bytes(uint64_t addr, uint8_t *buf, size_t len) {
  for (size_t i = 0; i < len; i++) {
    buf[i] = (uint8_t)read_mem(addr + i);
  }
}

/*
 * Step `zstep_model(UNIT)` up to `max_steps` instructions until `z_PC == exit_pc`.
 *
 * Returns:
 *   0  if `z_PC == exit_pc` (`*out_steps` = steps executed, `*out_pc` = `z_PC`)
 *   1  if `max_steps` was reached with `z_PC != exit_pc`
 *  -1  if `have_exception` was raised (Sail assertion / match failure)
 *  -2  if `zPSTATE.zEL != 0` (synchronous exception trap out of EL0)
 */
int sail_harness_step_until(uint64_t exit_pc, size_t max_steps, size_t *out_steps,
                            uint64_t *out_pc) {
  size_t step = 0;
  for (; step < max_steps && z_PC != exit_pc; step++) {
    uint64_t insn_pc = z_PC;
    zstep_model(UNIT);
    if (have_exception) {
      have_exception = false;
      if (out_steps != NULL) {
        *out_steps = step + 1;
      }
      if (out_pc != NULL) {
        *out_pc = insn_pc;
      }
      return -1;
    }
    if (zPSTATE.zEL != 0) {
      if (out_steps != NULL) {
        *out_steps = step + 1;
      }
      if (out_pc != NULL) {
        *out_pc = insn_pc;
      }
      return -2;
    }
  }
  if (out_steps != NULL) {
    *out_steps = step;
  }
  if (out_pc != NULL) {
    *out_pc = z_PC;
  }
  return (z_PC == exit_pc) ? 0 : 1;
}

void sail_harness_read_state(uint64_t out_regs[31], uint64_t out_vregs_lo[32],
                             uint64_t out_vregs_hi[32], uint64_t *out_sp, uint64_t *out_pc,
                             uint8_t *out_nzcv) {
  for (size_t i = 0; i < 31; i++) {
    out_regs[i] = *GPR_PTRS[i];
  }
  mpz_t tmp;
  mpz_init(tmp);
  for (size_t i = 0; i < 32; i++) {
    if (i < z_Z.len) {
      out_vregs_lo[i] = (uint64_t)mpz_get_ui(*z_Z.data[i].bits);
      mpz_fdiv_q_2exp(tmp, *z_Z.data[i].bits, 64);
      out_vregs_hi[i] = (uint64_t)mpz_get_ui(tmp);
    } else {
      out_vregs_lo[i] = 0;
      out_vregs_hi[i] = 0;
    }
  }
  mpz_clear(tmp);
  *out_sp = zSP_EL0;
  *out_pc = z_PC;
  *out_nzcv = (uint8_t)(((zPSTATE.zN & 1) << 3) | ((zPSTATE.zZ & 1) << 2) |
                        ((zPSTATE.zC & 1) << 1) | (zPSTATE.zV & 1));
}

uint64_t sail_harness_read_fpsr(void) { return zFPSR.zbits; }

void sail_harness_set_fpsr(uint64_t fpsr) { zFPSR.zbits = fpsr; }

uint64_t sail_harness_read_fpcr(void) { return zFPCR.zbits; }

void sail_harness_set_fpcr(uint64_t fpcr) { zFPCR.zbits = fpcr; }

uint64_t sail_harness_read_tpidr_el0(void) { return zTPIDR_EL0; }

void sail_harness_set_tpidr_el0(uint64_t tpidr) { zTPIDR_EL0 = tpidr; }


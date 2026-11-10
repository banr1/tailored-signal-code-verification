/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpand
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import ProofLib.SepLogic.WPp

/-!
# `spqr::kdf::hkdf_to_slice`: Expand Loop and Top-Level Proof

Proves the HKDF-Expand loop (`0x636f0 → 0x639e4`) for `okmLen ∈ {32, 64, 96}` and assembles the
fixed-base and `[LibsignalPlacement]` `RunsTo` theorems for `spqr::kdf::hkdf_to_slice`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.FinalizeFixed3Proof
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof

attribute [scoped simp, arm64_norm]
  State.readReg64_setMem State.pc_setMem State.sp_setMem State.status_setMem
  Expand.mem_setMem
attribute [local simp, local arm64_norm] bv_sub_add_lit hkdfCodeFakeB bv_sub_add_lit_ge
@[local simp, local arm64_norm] private theorem lsmpl_base_475 [LibsignalPlacement] : lsmpl.base 425 = (blkPl_425).base := rfl

@[scoped simp, arm64_norm] theorem extractLsb'_0_64_zero128 : (0#128).extractLsb' 0 64 = 0#64 := rfl
@[scoped simp, arm64_norm] theorem extractLsb'_64_64_zero128 : (0#128).extractLsb' 64 64 = 0#64 := rfl

@[simp, arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [0x5e098 → 0x5e59c]

variable {b b_iv : BitVec 64} {C : Crypto} {ext : String → Option (State → State)}

theorem hkdfExpand_64_eq (F : ShaState → List (BitVec 8) → ShaState) (prk info : List (BitVec 8)) :
    hkdfExpand F prk info 64 = Expand.t1 F prk info ++ Expand.t2 F prk info := by
  dsimp only [hkdfExpand]; have h2 : (64 + 31) / 32 = 2 := rfl
  have hblocks : (hkdfBlocks F prk info 2).flatten = Expand.t1 F prk info ++ Expand.t2 F prk info := by
    simp [hkdfBlocks, Expand.t1, Expand.t2]
  rw [h2, hblocks, List.take_of_length_le]; simp [Expand.t1, Expand.t2, length_hmacWith]

/-- Postcondition of `spqr::kdf::hkdf_to_slice` (`b + 0x63284` → `s₀.readReg64 .lr`). -/
def HPost (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s' : State) : Prop :=
  s'.pc = s₀.readReg64 .lr ∧
  s'.status = .Running ∧
  CalleeSaved s₀ s' ∧
  s'.mem.readBytes okmA okmLen = hkdfExpand F (hkdfExtractBytes F salt ikm) info okmLen ∧
  HFrame okmLen s₀ s'.mem

structure StateDone (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (okmA : BitVec 64) (okmLen : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + 0x5e0b0#64
  common  : HCommon okmLen s₀ s
  okm_all : s.mem.readBytes okmA okmLen = hkdfExpand F (hkdfExtractBytes F salt ikm) info okmLen

@[scoped simp, arm64_norm]
theorem hsp_592_add_96_eq_sp (s₀ : State) :
    hsp s₀ + 592#64 + 96#64 = s₀.sp := by
  unfold hsp; bv_lin

set_option hygiene false in
local macro "hkdf_epilogue_body" : tactic => `(tactic| (
  have hpc := hx.pc_eq; have hrun := hx.common.status; have hsp_eq := hx.common.sp_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.common.frame
  rcases hx.common.saved with
    ⟨m592, m600, m608, m616, m624, m632, m640, m648, m656, m664, m672, m680⟩
  iterate 21 kdf_step
  refine RunsTo.refl ?_
  have hA : AgreesOutside s.mem
      ((((((((s.mem.write64 (hsp s₀ + 32#64) 0#64).write64 (hsp s₀ + 40#64) 0#64).write64
        (hsp s₀ + 48#64) 0#64).write64 (hsp s₀ + 56#64) 0#64).write64
        (hsp s₀ + 64#64) 0#64).write64 (hsp s₀ + 72#64) 0#64).write64
        (hsp s₀ + 80#64) 0#64).write64 (hsp s₀ + 88#64) 0#64
      |>.write64 (hsp s₀ + 256#64) 0#64 |>.write64 (hsp s₀ + 264#64) 0#64
      |>.write64 (hsp s₀ + 240#64) 0#64 |>.write64 (hsp s₀ + 248#64) 0#64
      |>.write64 (hsp s₀ + 224#64) 0#64 |>.write64 (hsp s₀ + 232#64) 0#64
      |>.write64 (hsp s₀ + 208#64) 0#64 |>.write64 (hsp s₀ + 216#64) 0#64)
      (hsp s₀ + 32#64) 240 := by prove_agrees_hsp
  have hd_okm : DisjointRegions (hsp s₀ + 32#64) 240 okmA okmLen :=
    hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩
  refine ⟨by kdf_reg, by kdf_reg, ⟨by kdf_reg, ?_⟩, ?_,
    HFrame.of_agreesOutside_hsp hx.common.frame hA (by decide)⟩
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> kdf_reg
  · exact (hA.readBytes_eq hd_okm (by have := hpre.okm_len; omega)).trans hx.okm_all))

/-- Epilogue (`b + 0x5dfcc` → `s₀.readReg64 .lr`, 21 steps): zeroes stack scratch slots, restores
`sp = s₀.sp` and `x19..x30`, and returns. -/
theorem epilogue_runsTo [HkdfHooks C.F ext] {aligned : Prop}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hx : StateDone b C.F salt ikm info okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (HPost C.F salt ikm info okmA okmLen s₀) := by
  hkdf_epilogue_body

theorem epilogue_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks} {aligned : Prop}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hx : StateDone hkdfCodeFakeB C.F salt ikm info okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s (HPost C.F salt ikm info okmA okmLen s₀) := by
  hkdf_epilogue_body

set_option hygiene false in
local macro "hkdf_b1_done_32_body" : tactic => `(tactic| (
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq
  have hx29 := hx.exp.common.x29_eq; have hsaved := hx.exp.common.saved
  have hframe := hx.exp.common.frame; have hokm := hx.okm_32
  have hx26 : s.readReg64 .x26 = 0#64 := hx.x26_eq
  kdf_step
  refine RunsTo.refl ⟨by kdf_reg,
    ⟨by kdf_reg, by kdf_reg, by kdf_reg,
     by rw [State.mem_setPC]; exact hsaved, by rw [State.mem_setPC]; exact hframe⟩,
    by rw [State.mem_setPC, hkdfExpand_32_eq]; exact hokm⟩))

/-- Case `okmLen = 32` (`b + 0x636f0` → `b + 0x5dfcc`, 1 step): `x26 = 0#64`, so `cbz x26` jumps
directly to `StateDone` at `0x5dfcc`. -/
theorem b1_done_32_runsTo [HkdfHooks C.F ext] {aligned : Prop}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA 32 s₀ b_iv aligned)
    (hx : StateB1Done b C.F salt ikm info infoA okmA 32 s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateDone b C.F salt ikm info okmA 32 s₀) := by
  hkdf_b1_done_32_body

theorem b1_done_32_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks} {aligned : Prop}
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA 32 s₀ b_iv aligned)
    (hx : StateB1Done hkdfCodeFakeB C.F salt ikm info infoA okmA 32 s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s (StateDone hkdfCodeFakeB C.F salt ikm info okmA 32 s₀) := by
  hkdf_b1_done_32_body

/-! ## Expand Loop (`0x637b8 → 0x637b4`) for `okmLen ∈ {64, 96}` -/

structure StateLoop (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + 0x5e3c0#64
  exp     : HExpCommon F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  x12_eq  : s.readReg64 .x12 = 64#64
  x21_eq  : s.readReg64 .x21 = hsp s₀ + 352#64
  x22_eq  : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x27_eq  : s.readReg64 .x27 = BitVec.ofNat 64 i
  x28_eq  : s.readReg64 .x28 = hsp s₀ + 352#64
  t_508   : s.mem.readBytes (hsp s₀ + 508#64) 32 = tPrev
  okm_pre : s.mem.readBytes okmA dstOff = okmSoFar

set_option hygiene false in
local macro "hkdf_b1_to_loop_body" : tactic => `(tactic| (
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq
  have hx29 := hx.exp.common.x29_eq; have hx22 := hx.x22_eq; have hx24 := hx.x24_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx28 := hx.x28_eq
  have hne0 : (BitVec.ofNat 64 (okmLen - 32) == 0#64) = false := by rcases hokm with rfl | rfl <;> rfl
  iterate 6 kdf_step
  refine RunsTo.refl ⟨by kdf_reg,
    { common := ⟨by kdf_reg, by kdf_reg, by kdf_reg, hx.exp.common.saved, hx.exp.common.frame⟩
      m0_eq := hx.exp.m0_eq, m8_eq := hx.exp.m8_eq, m16_eq := hx.exp.m16_eq,
      m24_eq := hx.exp.m24_eq, hmac_208 := hx.exp.hmac_208 },
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, hx.t1_508, hx.okm_32⟩))

/-- Loop entry (`b + 0x636f0` → `b + 0x637b8`, 6 steps when `okmLen = 64 ∨ okmLen = 96`):
steps from `StateB1Done` into `StateLoop` with `i = 1`, `rem = okmLen - 32`, `dstOff = 32`. -/
theorem b1_to_loop_runsTo [HkdfHooks C.F ext]
    {salt ikm info : List (BitVec 8)} {infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s : State} (hokm : okmLen = 64 ∨ okmLen = 96)
    (hx : StateB1Done b C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoop b C.F salt ikm info infoA okmA
        (Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info)
        (Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info)
        okmLen 1 (okmLen - 32) 32 s₀) := by
  hkdf_b1_to_loop_body

theorem b1_to_loop_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    {salt ikm info : List (BitVec 8)} {infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s : State} (hokm : okmLen = 64 ∨ okmLen = 96)
    (hx : StateB1Done hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA
        (Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info)
        (Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info)
        okmLen 1 (okmLen - 32) 32 s₀) := by
  hkdf_b1_to_loop_body

theorem HmacSt.of_copy_208_write32_352 {m₀ m : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key t : List (BitVec 8)}
    (htmpl : HmacSt m₀ (hsp s₀ + 208#64) F key [])
    (ht : m₀.readBytes (hsp s₀ + 508#64) 32 = t) (ht_len : t.length = 32)
    (h0  : m.read64 (hsp s₀ + 352#64) = m₀.read64 (hsp s₀ + 508#64)) (h8   : m.read64 (hsp s₀ + 360#64) = m₀.read64 (hsp s₀ + 516#64))
    (h16 : m.read64 (hsp s₀ + 368#64) = m₀.read64 (hsp s₀ + 524#64)) (h24  : m.read64 (hsp s₀ + 376#64) = m₀.read64 (hsp s₀ + 532#64))
    (hpos : m.read8 (hsp s₀ + 415#64) = 32#8)
    (h64 : m.read64 (hsp s₀ + 416#64) = m₀.read64 (hsp s₀ + 272#64)) (h72  : m.read64 (hsp s₀ + 424#64) = m₀.read64 (hsp s₀ + 280#64))
    (h80 : m.read64 (hsp s₀ + 432#64) = m₀.read64 (hsp s₀ + 288#64)) (h88  : m.read64 (hsp s₀ + 440#64) = m₀.read64 (hsp s₀ + 296#64))
    (h96 : m.read64 (hsp s₀ + 448#64) = m₀.read64 (hsp s₀ + 304#64)) (h104 : m.read64 (hsp s₀ + 456#64) = m₀.read64 (hsp s₀ + 312#64))
    (h112 : m.read64 (hsp s₀ + 464#64) = m₀.read64 (hsp s₀ + 320#64)) (h120 : m.read64 (hsp s₀ + 472#64) = m₀.read64 (hsp s₀ + 328#64))
    (h128 : m.read64 (hsp s₀ + 480#64) = m₀.read64 (hsp s₀ + 336#64)) (h136 : m.read64 (hsp s₀ + 488#64) = m₀.read64 (hsp s₀ + 344#64)) :
    HmacSt m (hsp s₀ + 352#64) F key t := by
  rcases htmpl with ⟨_, _, _, hin, hcnt1, hout, hcnt2⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ht_len, readBytes_32_eq_of_read64_eq h0 (Expand.read64_add_off h8) (Expand.read64_add_off h16) (Expand.read64_add_off h24), ht]
  · rw [ht_len, show hsp s₀ + 352#64 + 0x3f#64 = hsp s₀ + 415#64 by bv_lin, hpos]
  · rw [show hsp s₀ + 352#64 + 0x40#64 = hsp s₀ + 416#64 by bv_lin,
        readBytes_32_eq_of_read64_eq h64 (Expand.read64_add_off h72) (Expand.read64_add_off h80) (Expand.read64_add_off h88),
        show hsp s₀ + 272#64 = hsp s₀ + 208#64 + 0x40#64 by bv_lin, hin]
  · rw [show hsp s₀ + 352#64 + 0x60#64 = hsp s₀ + 448#64 by bv_lin, h96, show hsp s₀ + 304#64 = hsp s₀ + 208#64 + 0x60#64 by bv_lin, hcnt1]
  · rw [show hsp s₀ + 352#64 + 0x68#64 = hsp s₀ + 456#64 by bv_lin,
        readBytes_32_eq_of_read64_eq h104 (Expand.read64_add_off h112) (Expand.read64_add_off h120) (Expand.read64_add_off h128),
        show hsp s₀ + 312#64 = hsp s₀ + 208#64 + 0x68#64 by bv_lin, hout]
  · rw [show hsp s₀ + 352#64 + 0x88#64 = hsp s₀ + 488#64 by bv_lin, h136, show hsp s₀ + 344#64 = hsp s₀ + 208#64 + 0x88#64 by bv_lin, hcnt2]

theorem info_ge32_lemmas {n : ℕ} (hge : 32 ≤ n) (hlt : n < 64) :
    (AddWithCarry64 (BitVec.ofNat 64 n) 18446744073709551583#64 true).2.c = true ∧
    BitVec.ule 32#64 (BitVec.ofNat 64 n) = true ∧ BitVec.ult (BitVec.ofNat 64 n) 32#64 = false ∧
    BitVec.ofNat 64 n - 32#64 = BitVec.ofNat 64 (n - 32) ∧
    BitVec.ofNat 64 n + 18446744073709551584#64 = BitVec.ofNat 64 (n - 32) := by
  have hm : n ∈ List.range' 32 32 := List.mem_range'.mpr ⟨n - 32, by omega, by omega⟩
  clear hge hlt; revert hm; generalize n = k; decide +revert

/-- Loop cut `StateLoopA1` at `pc_target` (after 46 steps from `0x5e2dc`):
`Hmac(PRK, tPrev)` initialized at `hsp s₀ + 352#64`, and `memcpy(hsp s₀ + 384#64, infoA, 32)` called. -/
structure StateLoopA1 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) (pc_target : BitVec 64 := b + bv% (ls_off% "memcpy")) : Prop where
  pc_eq    : s.pc = pc_target
  exp      : HExpCommon F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq    : s.readReg64 .lr = b + 0x5e478#64
  x0_eq    : s.readReg64 .x0 = hsp s₀ + 384#64
  x1_eq    : s.readReg64 .x1 = infoA
  x2_eq    : s.readReg64 .x2 = 32#64
  x19_eq   : s.readReg64 .x19 = hsp s₀ + 352#64
  x20_eq   : s.readReg64 .x20 = BitVec.ofNat 64 info.length
  x21_eq   : s.readReg64 .x21 = BitVec.ofNat 64 (info.length - 32)
  x22_eq   : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = hsp s₀ + 352#64
  x24_eq   : s.readReg64 .x24 = 32#64
  x25_eq   : s.readReg64 .x25 = infoA + 32#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x27_eq   : s.readReg64 .x27 = BitVec.ofNat 64 i
  x28_eq   : s.readReg64 .x28 = 32#64
  hmac_352 : HmacSt s.mem (hsp s₀ + 352#64) F (hkdfExtractBytes F salt ikm) tPrev
  okm_pre  : s.mem.readBytes okmA dstOff = okmSoFar

set_option hygiene false in
local macro "hkdf_iter_a1_body" : tactic => `(tactic| (
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq
  have hx29 := hx.exp.common.x29_eq; have hx12 := hx.x12_eq; have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq; have hx25 := hx.x25_eq; have hx26 := hx.x26_eq
  have hx27 := hx.x27_eq; have hx28 := hx.x28_eq; have hm8 := hx.exp.m8_eq; have hm24 := hx.exp.m24_eq
  have hpos_208 : s.mem.read8 (hsp s₀ + 271#64) = 0#8 := by simpa [BitVec.add_assoc] using hx.exp.hmac_208.2.2.1
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.exp.common.frame
  rcases info_ge32_lemmas hpre.info_ge (by have := hpre.info_lt; omega) with ⟨hinfo_c, hinfo_ule, hinfo_ult, hinfo_sub1, hinfo_sub2⟩
  iterate 46 kdf_step
  refine RunsTo.refl ?_
  have hA : AgreesOutside s.mem
      (((((((((((((((((s.mem.write64 (hsp s₀ + 72#64) (s.mem.read64 (hsp s₀ + 312#64))).write64 (hsp s₀ + 80#64) (s.mem.read64 (hsp s₀ + 320#64))).write64
        (hsp s₀ + 88#64) (s.mem.read64 (hsp s₀ + 328#64))).write64 (hsp s₀ + 96#64) (s.mem.read64 (hsp s₀ + 336#64))).write64
        (hsp s₀ + 64#64) (s.mem.read64 (hsp s₀ + 304#64))).write64 (hsp s₀ + 104#64) (s.mem.read64 (hsp s₀ + 344#64))).write64
        (hsp s₀ + 32#64) (s.mem.read64 (hsp s₀ + 272#64))).write64 (hsp s₀ + 40#64) (s.mem.read64 (hsp s₀ + 280#64))).write64
        (hsp s₀ + 48#64) (s.mem.read64 (hsp s₀ + 288#64))).write64 (hsp s₀ + 56#64) (s.mem.read64 (hsp s₀ + 296#64))).write64
        (hsp s₀ + 416#64) (s.mem.read64 (hsp s₀ + 272#64))).write64 (hsp s₀ + 424#64) (s.mem.read64 (hsp s₀ + 280#64))).write64
        (hsp s₀ + 432#64) (s.mem.read64 (hsp s₀ + 288#64))).write64 (hsp s₀ + 440#64) (s.mem.read64 (hsp s₀ + 296#64))).write64
        (hsp s₀ + 448#64) (s.mem.read64 (hsp s₀ + 304#64))).write64 (hsp s₀ + 456#64) (s.mem.read64 (hsp s₀ + 312#64))).write64
        (hsp s₀ + 464#64) (s.mem.read64 (hsp s₀ + 320#64)) |>.write64 (hsp s₀ + 472#64) (s.mem.read64 (hsp s₀ + 328#64))
        |>.write64 (hsp s₀ + 384#64) (s.mem.read64 (hsp s₀ + 240#64)) |>.write64 (hsp s₀ + 392#64) (s.mem.read64 (hsp s₀ + 248#64))
        |>.write64 (hsp s₀ + 400#64) (s.mem.read64 (hsp s₀ + 256#64)) |>.write64 (hsp s₀ + 408#64) (s.mem.read64 (hsp s₀ + 264#64))
        |>.write64 (hsp s₀ + 480#64) (s.mem.read64 (hsp s₀ + 336#64)) |>.write64 (hsp s₀ + 488#64) (s.mem.read64 (hsp s₀ + 344#64))
        |>.write64 (hsp s₀ + 352#64) (s.mem.read64 (hsp s₀ + 208#64)) |>.write64 (hsp s₀ + 360#64) (s.mem.read64 (hsp s₀ + 216#64))
        |>.write64 (hsp s₀ + 368#64) (s.mem.read64 (hsp s₀ + 224#64)) |>.write64 (hsp s₀ + 376#64) (s.mem.read64 (hsp s₀ + 232#64))
        |>.write64 (hsp s₀ + 352#64) (s.mem.read64 (hsp s₀ + 508#64)) |>.write64 (hsp s₀ + 360#64) (s.mem.read64 (hsp s₀ + 516#64))
        |>.write64 (hsp s₀ + 368#64) (s.mem.read64 (hsp s₀ + 524#64)) |>.write64 (hsp s₀ + 376#64) (s.mem.read64 (hsp s₀ + 532#64))
        |>.write8 (hsp s₀ + 415#64) 32#8)
      (hsp s₀ + 32#64) 464 := by prove_agrees_hsp
  refine ⟨by kdf_reg,
    HExpCommon.of_agreesOutside_32_560 (off := 32#64) (sz := 464) hx.exp
      (by kdf_reg) (by kdf_reg) (by kdf_reg)
      hA (by decide) (by prove_hmac_208 hx.exp.hmac_208),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hinfo_sub1, hinfo_sub2],
    by kdf_reg, by kdf_reg,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm]; rcases hrem with rfl | rfl <;> rfl,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    refine HmacSt.of_copy_208_write32_352 hx.exp.hmac_208 hx.t_508 ht_len
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [arm64_norm]
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (hsp s₀ + 32#64) 464 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right okmA
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      exact (hA.readBytes_eq hd (by have := hpre.okm_len; omega)).trans hx.okm_pre))

/-- Loop segment `A1` (`b + 0x5e2dc` → `b + 0x97228`, 46 steps): copies `Hmac(PRK, [])` to
`hsp s₀ + 352#64`, writes `tPrev` (32 B) from `hsp s₀ + 508#64` to `hsp s₀ + 352#64..384#64`,
and calls `memcpy(hsp s₀ + 384#64, infoA, 32)`. -/
theorem iter_a1_runsTo [HkdfHooks C.F ext] {aligned : Prop}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (ht_len : tPrev.length = 32) (hrem : rem = 32 ∨ rem = 64) (hdst : dstOff ≤ okmLen)
    (hx : StateLoop b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopA1 b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  hkdf_iter_a1_body

theorem iter_a1_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks} {aligned : Prop}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (ht_len : tPrev.length = 32) (hrem : rem = 32 ∨ rem = 64) (hdst : dstOff ≤ okmLen)
    (hx : StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoopA1 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ · (lsρ lsMemcpySym)) := by
  hkdf_iter_a1_body

/-- Loop cut `StateLoopA2` at `b + 0x6388c#64` (return from `compress256` on `tPrev ++ info.take 32`). -/
structure StateLoopA2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + 0x5e494#64
  exp     : HExpCommon F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  x19_eq  : s.readReg64 .x19 = hsp s₀ + 352#64
  x21_eq  : s.readReg64 .x21 = BitVec.ofNat 64 (info.length - 32)
  x22_eq  : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = hsp s₀ + 352#64
  x24_eq  : s.readReg64 .x24 = 32#64
  x25_eq  : s.readReg64 .x25 = infoA + 32#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x27_eq  : s.readReg64 .x27 = BitVec.ofNat 64 i
  in_416  : s.mem.readBytes (hsp s₀ + 416#64) 32 =
              shaStateBytes (F (hmacInnerInit F (hkdfExtractBytes F salt ikm)) (tPrev ++ info.take 32))
  cnt_448 : s.mem.read64 (hsp s₀ + 448#64) = 2#64
  out_456 : s.mem.readBytes (hsp s₀ + 456#64) 32 =
              shaStateBytes (hmacOuterInit F (hkdfExtractBytes F salt ikm))
  cnt_488 : s.mem.read64 (hsp s₀ + 488#64) = 1#64
  okm_pre : s.mem.readBytes okmA dstOff = okmSoFar

set_option hygiene false in
local macro "hkdf_iter_a2_mid" : tactic => `(tactic| (
  let prk := hkdfExtractBytes C.F salt ikm
  let m₁ := s.mem.writeBytes (hsp s₀ + 384#64) (info.take 32)
  have hA1 : AgreesOutside s.mem m₁ (hsp s₀ + 384#64) 32 :=
    Expand.agreesOutside_writeBytes_le s.mem (hsp s₀ + 384#64) (info.take 32) 32 (by omega)
  have hc1 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_352_592 (off := 384#64) (sz := 32) hx.exp hrun hsp_eq hx29 hA1 (by decide)
  have hcnt1_m1 : m₁.read64 (hsp s₀ + 448#64) = 1#64 := by
    rw [hA1.read64_eq (by unfold DisjointRegions; bv_omega),
        show hsp s₀ + 448#64 = (hsp s₀ + 352#64) + 0x60#64 by bv_lin]
    exact hx.hmac_352.2.2.2.2.1
  have hrw1 : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  dsimp only [m₁] at hcnt1_m1 hrw1
  iterate 7 kdf_step
  let m₂ := m₁.write64 (hsp s₀ + 448#64) 2#64
  have hA2 : AgreesOutside m₁ m₂ (hsp s₀ + 448#64) 8 :=
    agreesOutside_hsp_write64 (AgreesOutside.rfl' m₁ (hsp s₀ + 448#64) 8) (by decide)
  have hc2 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₂) :=
    HExpCommon.of_agreesOutside_352_592 (off := 448#64) (sz := 8) hc1 hrun hsp_eq hx29 hA2 (by decide)
  have hin_416 : m₂.readBytes (hsp s₀ + 416#64) 32 = shaStateBytes (hmacInnerInit C.F prk) := by
    rw [hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        show hsp s₀ + 416#64 = (hsp s₀ + 352#64) + 0x40#64 by bv_lin]
    exact hx.hmac_352.2.2.2.1
  have hblk_352 : m₂.readBytes (hsp s₀ + 352#64) 64 = tPrev ++ info.take 32 := by
    change m₂.readBytes (hsp s₀ + 352#64) (32 + 32) = tPrev ++ info.take 32
    rw [Bytes.readBytes_add m₂ (hsp s₀ + 352#64) 32 32,
        show (hsp s₀ + 352#64) + BitVec.ofNat 64 32 = hsp s₀ + 384#64 by bv_lin]
    have ht_m2 : m₂.readBytes (hsp s₀ + 352#64) 32 = tPrev := by
      rw [hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
          hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide), ← ht_len]
      exact hx.hmac_352.2.1
    have hi_m2 : m₂.readBytes (hsp s₀ + 384#64) 32 = info.take 32 := by
      rw [hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)]
      have h := Bytes.readBytes_writeBytes_same s.mem (hsp s₀ + 384#64) (info.take 32)
        (by rw [htake_len]; decide)
      rwa [htake_len] at h
    rw [ht_m2, hi_m2]
  have hblk_len : (tPrev ++ info.take 32).length = 64 := by rw [List.length_append, ht_len, htake_len]
  have hrw_416 : m₂.RW (hsp s₀ + 416#64) 32 :=
    (HFrame.rw_hsp hpre hc2.common.frame).sub (by bv_omega)))

set_option hygiene false in
local macro "hkdf_iter_a2_post" : tactic => `(tactic| (
  let stBytes := shaStateBytes (C.F (hmacInnerInit C.F prk) (tPrev ++ info.take 32))
  let m₃ := m₂.writeBytes (hsp s₀ + 416#64) stBytes
  have hA3 : AgreesOutside m₂ m₃ (hsp s₀ + 416#64) 32 :=
    Expand.agreesOutside_writeBytes_le m₂ (hsp s₀ + 416#64) stBytes 32 (by simp [stBytes])
  have hc3 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₃) :=
    HExpCommon.of_agreesOutside_352_592 (off := 416#64) (sz := 32) hc2 hrun hsp_eq hx29 hA3 (by decide)
  refine RunsTo.refl ⟨by kdf_reg,
    ⟨⟨by kdf_reg, by kdf_reg, by kdf_reg,
      by rw [Expand.mem_setMem]; exact hc3.common.saved,
      by rw [Expand.mem_setMem]; exact hc3.common.frame⟩,
     by rw [Expand.mem_setMem]; exact hc3.m0_eq, by rw [Expand.mem_setMem]; exact hc3.m8_eq,
     by rw [Expand.mem_setMem]; exact hc3.m16_eq, by rw [Expand.mem_setMem]; exact hc3.m24_eq,
     by rw [Expand.mem_setMem]; exact hc3.hmac_208⟩,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    ?_, ?_, ?_, ?_, ?_⟩
  · show m₃.readBytes (hsp s₀ + 416#64) 32 = stBytes
    have hlen : stBytes.length = 32 := shaStateBytes_length _
    have h := Bytes.readBytes_writeBytes_same m₂ (hsp s₀ + 416#64) stBytes (by rw [hlen]; decide)
    rwa [hlen] at h
  · show m₃.read64 (hsp s₀ + 448#64) = 2#64
    rw [hA3.read64_eq (by unfold DisjointRegions; bv_omega)]
    simp (config := { decide := true }) only [m₂, arm64_norm]
  · show m₃.readBytes (hsp s₀ + 456#64) 32 = shaStateBytes (hmacOuterInit C.F prk)
    rw [hA3.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        show hsp s₀ + 456#64 = (hsp s₀ + 352#64) + 0x68#64 by bv_lin]
    exact hx.hmac_352.2.2.2.2.2.1
  · show m₃.read64 (hsp s₀ + 488#64) = 1#64
    rw [hA3.read64_eq (by unfold DisjointRegions; bv_omega),
        hA2.read64_eq (by unfold DisjointRegions; bv_omega),
        hA1.read64_eq (by unfold DisjointRegions; bv_omega),
        show hsp s₀ + 488#64 = (hsp s₀ + 352#64) + 0x88#64 by bv_lin]
    exact hx.hmac_352.2.2.2.2.2.2
  · show m₃.readBytes okmA dstOff = okmSoFar
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd3 : DisjointRegions (hsp s₀ + 416#64) 32 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 416#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd2 : DisjointRegions (hsp s₀ + 448#64) 8 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 448#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd1 : DisjointRegions (hsp s₀ + 384#64) 32 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 384#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hlen : dstOff ≤ 2 ^ 64 := by have := hpre.okm_len; omega
      rw [hA3.readBytes_eq hd3 hlen, hA2.readBytes_eq hd2 hlen, hA1.readBytes_eq hd1 hlen]
      exact hx.okm_pre))

set_option maxHeartbeats 1600000 in
theorem iter_a2_runsTo [HkdfHooks C.F ext] {aligned : Prop}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ}
    {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (ht_len : tPrev.length = 32) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA1 b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopA2 b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hlr := hx.lr_eq; have hx0 := hx.x0_eq; have hx1 := hx.x1_eq; have hx2 := hx.x2_eq
  have hx19 := hx.x19_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq; have hx24 := hx.x24_eq; have hx25 := hx.x25_eq
  have hx26 := hx.x26_eq; have hx27 := hx.x27_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_384 : s.mem.RW (hsp s₀ + 384#64) 32 := hrw_hsp.sub (by bv_omega)
  have hinfo_all : s.mem.readBytes infoA info.length = info := HFrame.info_bytes hpre hx.exp.common.frame
  have hinfo_take : s.mem.readBytes infoA 32 = info.take 32 := by
    simpa using Bytes.readBytes_slice_of_readBytes_eq s.mem infoA info hinfo_all 0 32 (by have := hpre.info_ge; omega)
  have htake_len : (info.take 32).length = 32 := List.length_take_of_le hpre.info_ge
  have hx2_nat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  refine s2_memcpy_step_ext b C ext hrun hpc hx0 hx1 hx2_nat hlr hinfo_take hrw_384 ?_
  hkdf_iter_a2_mid
  refine s2_compress256_step_ext b C ext
    (stPtr := hsp s₀ + 416#64) (blkPtr := hsp s₀ + 352#64) (lr := b + 0x5e494#64)
    (st := hmacInnerInit C.F prk) (blk := tPrev ++ info.take 32)
    (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg)
    (by rw [Expand.mem_setMem]; exact hin_416) (by rw [Expand.mem_setMem]; exact hblk_352) hblk_len
    (by rw [Expand.mem_setMem]; exact hrw_416) ?_
  hkdf_iter_a2_post

set_option maxHeartbeats 1600000 in
theorem iter_a2_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks} {aligned : Prop}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (ht_len : tPrev.length = 32) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA1 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s (lsρ lsMemcpySym)) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoopA2 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hlr := hx.lr_eq
  have hx0 := hx.x0_eq; have hx1 := hx.x1_eq; have hx2 := hx.x2_eq
  have hx19 := hx.x19_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq; have hx24 := hx.x24_eq; have hx25 := hx.x25_eq
  have hx26 := hx.x26_eq; have hx27 := hx.x27_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_384 : s.mem.RW (hsp s₀ + 384#64) 32 := hrw_hsp.sub (by bv_omega)
  have hinfo_all : s.mem.readBytes infoA info.length = info := HFrame.info_bytes hpre hx.exp.common.frame
  have hinfo_take : s.mem.readBytes infoA 32 = info.take 32 := by
    simpa using Bytes.readBytes_slice_of_readBytes_eq s.mem infoA info hinfo_all 0 32 (by have := hpre.info_ge; omega)
  have htake_len : (info.take 32).length = 32 := List.length_take_of_le hpre.info_ge
  have hx2_nat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  refine s2_memcpy_step_placed_429 h_memcpy hrun hpc hx0 hx1 hx2_nat hlr hinfo_take hrw_384 ?_
  hkdf_iter_a2_mid
  refine s2_compress256_step_placed_429 h_compress
    (stPtr := hsp s₀ + 416#64) (blkPtr := hsp s₀ + 352#64) (lr := (blkPl_379).base + 1544#64)
    (st := hmacInnerInit C.F prk) (blk := tPrev ++ info.take 32)
    (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg)
    (by rw [Expand.mem_setMem]; exact hin_416) (by rw [Expand.mem_setMem]; exact hblk_352) hblk_len
    (by rw [Expand.mem_setMem]; exact hrw_416) ?_
  hkdf_iter_a2_post

theorem info_sub32_lemmas {k : ℕ} (hk : k < 64) :
    (BitVec.ofNat 64 k >>> 6) = 0#64 ∧
    (BitVec.ofNat 64 k >>> 6#64) = 0#64 ∧
    (BitVec.ofNat 64 k &&& 0x7fffffffffffffc0#64) = 0#64 ∧
    (BitVec.ofNat 64 k &&& 63#64) = BitVec.ofNat 64 k ∧
    ((BitVec.ofNat 64 k >>> 6) == 0#64) = true ∧
    ((BitVec.ofNat 64 k >>> 6#64) == 0#64) = true := by
  have hm : k ∈ List.range 64 := List.mem_range.mpr hk
  clear hk; revert hm; generalize k = n; decide +revert

theorem iter_counter_lemmas {i : ℕ} (hi : i = 1 ∨ i = 2) :
    (BitVec.ofNat 64 i == 255#64) = false ∧ (BitVec.ofNat 64 i != 255#64) = true ∧
    (AddWithCarry64 (BitVec.ofNat 64 i) 18446744073709551360#64 true).2.z = false ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 i) + 1#32) = BitVec.ofNat 64 (i + 1) ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 (i + 1))) = BitVec.ofNat 64 (i + 1) := by
  rcases hi with rfl | rfl <;> decide

theorem HmacStN.of_copy_352_32 {m₀ m : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key pfx tail : List (BitVec 8)}
    (hsrc : HmacStN m₀ (hsp s₀ + 352#64) F key pfx tail)
    (h0  : m.read64 (hsp s₀ + 32#64)  = m₀.read64 (hsp s₀ + 352#64)) (h8   : m.read64 (hsp s₀ + 40#64)  = m₀.read64 (hsp s₀ + 360#64))
    (h16 : m.read64 (hsp s₀ + 48#64)  = m₀.read64 (hsp s₀ + 368#64)) (h24  : m.read64 (hsp s₀ + 56#64)  = m₀.read64 (hsp s₀ + 376#64))
    (h32 : m.read64 (hsp s₀ + 64#64)  = m₀.read64 (hsp s₀ + 384#64)) (h40  : m.read64 (hsp s₀ + 72#64)  = m₀.read64 (hsp s₀ + 392#64))
    (h48 : m.read64 (hsp s₀ + 80#64)  = m₀.read64 (hsp s₀ + 400#64)) (h56  : m.read64 (hsp s₀ + 88#64)  = m₀.read64 (hsp s₀ + 408#64))
    (h64 : m.read64 (hsp s₀ + 96#64)  = m₀.read64 (hsp s₀ + 416#64)) (h72  : m.read64 (hsp s₀ + 104#64) = m₀.read64 (hsp s₀ + 424#64))
    (h80 : m.read64 (hsp s₀ + 112#64) = m₀.read64 (hsp s₀ + 432#64)) (h88  : m.read64 (hsp s₀ + 120#64) = m₀.read64 (hsp s₀ + 440#64))
    (h96 : m.read64 (hsp s₀ + 128#64) = m₀.read64 (hsp s₀ + 448#64)) (h104 : m.read64 (hsp s₀ + 136#64) = m₀.read64 (hsp s₀ + 456#64))
    (h112 : m.read64 (hsp s₀ + 144#64) = m₀.read64 (hsp s₀ + 464#64)) (h120 : m.read64 (hsp s₀ + 152#64) = m₀.read64 (hsp s₀ + 472#64))
    (h128 : m.read64 (hsp s₀ + 160#64) = m₀.read64 (hsp s₀ + 480#64)) (h136 : m.read64 (hsp s₀ + 168#64) = m₀.read64 (hsp s₀ + 488#64)) :
    HmacStN m (hsp s₀ + 32#64) F key pfx tail :=
  HmacStN.of_copy_19 hsrc h0 (Expand.read64_add_off h8) (Expand.read64_add_off h16)
    (Expand.read64_add_off h24) (Expand.read64_add_off h32) (Expand.read64_add_off h40)
    (Expand.read64_add_off h48) (Expand.read64_add_off h56) (Expand.read64_add_off h64)
    (Expand.read64_add_off h72) (Expand.read64_add_off h80) (Expand.read64_add_off h88)
    (Expand.read64_add_off h96) (Expand.read64_add_off h104) (Expand.read64_add_off h112)
    (Expand.read64_add_off h120) (Expand.read64_add_off h128) (Expand.read64_add_off h136)

theorem HmacStN.of_tail_counter_352 {m₀ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key blk tail0 : List (BitVec 8)}
    {b0 b1 c : BitVec 8} (hblk : blk.length = 64) (htail0 : tail0.length < 55)
    (hin : m₀.readBytes (hsp s₀ + 416#64) 32 = shaStateBytes (F (hmacInnerInit F key) blk))
    (hcnt1 : m₀.read64 (hsp s₀ + 448#64) = 2#64)
    (hout : m₀.readBytes (hsp s₀ + 456#64) 32 = shaStateBytes (hmacOuterInit F key))
    (hcnt2 : m₀.read64 (hsp s₀ + 488#64) = 1#64) :
    let m₁ := ((m₀.write8 (hsp s₀ + 415#64) b0).write8 (hsp s₀ + 415#64) b1).writeBytes (hsp s₀ + 352#64) tail0
    let m₂ := (((m₁.write8 (hsp s₀ + 32#64) c).write8 (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) c).write8
      (hsp s₀ + 415#64) (BitVec.ofNat 8 (tail0.length + 1)))
    HmacStN m₂ (hsp s₀ + 352#64) F key blk (tail0 ++ [c]) := by
  intro m₁ m₂; have hlen : (tail0 ++ [c]).length = tail0.length + 1 := by simp
  refine HmacStN.mk_block64 hblk (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hlen, Bytes.readBytes_add m₂ (hsp s₀ + 352#64) tail0.length 1]
    have h_t0 : m₂.readBytes (hsp s₀ + 352#64) tail0.length = tail0 := by
      by_cases ht0 : tail0.length = 0
      · rw [ht0, List.eq_nil_of_length_eq_zero ht0]; rfl
      · dsimp only [m₂, m₁]
        rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by omega),
            (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by omega),
            (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by omega)]
        exact Bytes.readBytes_writeBytes_same _ _ tail0 (by omega)
    have h_c : m₂.readBytes (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 = [c] := by
      dsimp only [Memory.readBytes, m₂]; rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
    rw [h_t0, h_c]
  · rw [hlen, show hsp s₀ + 352#64 + 0x3f#64 = hsp s₀ + 415#64 by bv_omega]; exact Memory.read8_write8_same _ _ _
  · rw [show hsp s₀ + 352#64 + 0x40#64 = hsp s₀ + 416#64 by bv_omega]; dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        Expand.writeBytes_readBytes_disj _ _ tail0 (hsp s₀ + 416#64) 32 (fun _ _ => by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide), hin]
  · rw [show hsp s₀ + 352#64 + 0x60#64 = hsp s₀ + 448#64 by bv_omega]; dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        Expand.writeBytes_read64_disj _ _ tail0 (hsp s₀ + 448#64) (fun _ => by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega), hcnt1]
  · rw [show hsp s₀ + 352#64 + 0x68#64 = hsp s₀ + 456#64 by bv_omega]; dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        Expand.writeBytes_readBytes_disj _ _ tail0 (hsp s₀ + 456#64) 32 (fun _ _ => by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide), hout]
  · rw [show hsp s₀ + 352#64 + 0x88#64 = hsp s₀ + 488#64 by bv_omega]; dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 352#64 + BitVec.ofNat 64 tail0.length) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 32#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        Expand.writeBytes_read64_disj _ _ tail0 (hsp s₀ + 488#64) (fun _ => by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (hsp s₀ + 415#64) 1 |>.write8 (by simp [InRegion])).read64_eq (by unfold DisjointRegions; bv_omega), hcnt2]

structure StateLoopC (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) (pc_target : BitVec 64 := b + 0x67a58#64) : Prop where
  pc_eq    : s.pc = pc_target
  exp      : HExpCommon F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  lr_eq    : s.readReg64 .lr = b + 0x5e38c#64
  x0_eq    : s.readReg64 .x0 = hsp s₀ + 540#64
  x1_eq    : s.readReg64 .x1 = hsp s₀ + 32#64
  x20_eq   : s.readReg64 .x20 = okmA + BitVec.ofNat 64 (dstOff + 32)
  x21_eq   : s.readReg64 .x21 = hsp s₀ + 352#64
  x22_eq   : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x24_eq   : s.readReg64 .x24 = 32#64
  x25_eq   : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (rem - 32)
  x27_eq   : s.readReg64 .x27 = BitVec.ofNat 64 i
  x28_eq   : s.readReg64 .x28 = hsp s₀ + 352#64
  hmac_32  : HmacStN s.mem (hsp s₀ + 32#64) F (hkdfExtractBytes F salt ikm)
               (tPrev ++ info.take 32) (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre  : s.mem.readBytes okmA dstOff = okmSoFar

set_option hygiene false in
local macro "hkdf_iter_b_pre" : tactic => `(tactic| (
  have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq
  have hx29 := hx.exp.common.x29_eq; have hx19 := hx.x19_eq; have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq; have hx23 := hx.x23_eq; have hx24 := hx.x24_eq
  have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.exp.common.frame
  have hk_lt : info.length - 32 < 23 := by have := hpre.info_lt; omega
  rcases info_sub32_lemmas (by omega : info.length - 32 < 64) with
    ⟨hlsr6_nat, hlsr6, hand_hi, hand_lo, hlsr6_nat_eq, hlsr6_eq⟩
  rcases Expand.cmp_lt64_lemmas (by omega : info.length - 32 < 64) with ⟨h_k_ule, h_k_ult, h_k_cmp⟩
  iterate 11 kdf_step
  let prk := hkdfExtractBytes C.F salt ikm
  let k := info.length - 32
  let m₀ := (s.mem.write8 (hsp s₀ + 415#64) 0#8).write8 (hsp s₀ + 415#64) (BitVec.ofNat 8 k)
  have hA0 : AgreesOutside s.mem m₀ (hsp s₀ + 415#64) 1 := by dsimp only [m₀]; prove_agrees_hsp
  have hc0 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₀) :=
    HExpCommon.of_agreesOutside_352_592 (off := 415#64) (sz := 1) hx.exp hrun hsp_eq hx29 hA0 (by decide)
  have hinfo_all : m₀.readBytes infoA info.length = info := HFrame.info_bytes hpre hc0.common.frame
  have hinfo_drop : m₀.readBytes (infoA + 32#64) k = info.drop 32 := by
    have h := Bytes.readBytes_slice_of_readBytes_eq m₀ infoA info hinfo_all 32 k (by have := hpre.info_ge; omega)
    simpa [k, List.take_of_length_le (by simp : (info.drop 32).length ≤ info.length - 32)] using h
  have hdrop_len : (info.drop 32).length = k := by simp [k]
  have hrw_352 : m₀.RW (hsp s₀ + 352#64) k := (HFrame.rw_hsp hpre hc0.common.frame).sub (by bv_omega)
  have hx2_nat : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]))

set_option hygiene false in
local macro "hkdf_iter_b_post" pc8d0:term : tactic => `(tactic| (
  let m₁ := m₀.writeBytes (hsp s₀ + 352#64) (info.drop 32)
  have hA1 : AgreesOutside m₀ m₁ (hsp s₀ + 352#64) 23 :=
    Expand.agreesOutside_writeBytes_le m₀ (hsp s₀ + 352#64) (info.drop 32) 23 (by omega)
  refine RunsTo.trans (RunsTo.refl (P := fun s₁ : State =>
      s₁.pc = $pc8d0 ∧ s₁.status = .Running ∧ s₁.sp = hsp s₀ ∧
      s₁.readReg64 .x29 = hsp s₀ + 592#64 ∧ s₁.readReg64 .x19 = hsp s₀ + 352#64 ∧
      s₁.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff ∧ s₁.readReg64 .x23 = hsp s₀ + 352#64 ∧
      s₁.readReg64 .x24 = 32#64 ∧ s₁.readReg64 .x26 = BitVec.ofNat 64 rem ∧
      s₁.readReg64 .x27 = BitVec.ofNat 64 i ∧ s₁.readReg64 .x28 = hsp s₀ + 352#64 ∧
      (∃ _ : Unit, s₁.mem = m₁))
    ⟨by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
     by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
     ⟨(), by rw [State.mem_setPC, Expand.mem_setMem, Expand.mem_setMem]⟩⟩) ?_
  rintro s₁ ⟨hpc₁, hrun₁, hsp₁, hx29_1, hx19_1, hx22_1, hx23_1, hx24_1, hx26_1, hx27_1, hx28_1, hm₁_box⟩
  clear hpc hrun hsp_eq hx29 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hrw_hsp
    hlsr6_nat hlsr6 hand_hi hand_lo hlsr6_nat_eq hlsr6_eq h_k_ule h_k_ult h_k_cmp
    hinfo_all hinfo_drop hrw_352 hx2_nat
  have hc1 : HExpCommon C.F prk info infoA okmLen s₀ s₁ :=
    HExpCommon.of_agreesOutside_352_592 (off := 352#64) (sz := 23) hc0
      hrun₁ hsp₁ hx29_1 (by rcases hm₁_box with ⟨_, h⟩; rw [h]; exact hA1) (by decide)
  have hm16_1 : s₁.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := hc1.m16_eq
  have hpos_415 : s₁.mem.read8 (hsp s₀ + 415#64) = BitVec.ofNat 8 k := by
    rcases hm₁_box with ⟨_, hm₁_save⟩; rw [hm₁_save]
    have hd : ∀ (_ : 0 < (info.drop 32).length),
        DisjointRegions (hsp s₀ + 352#64) (info.drop 32).length (hsp s₀ + 415#64) 1 := by
      intro _; unfold DisjointRegions; bv_omega
    have h1 := Expand.writeBytes_readBytes_disj m₀ (hsp s₀ + 352#64) (info.drop 32)
      (hsp s₀ + 415#64) 1 (fun h0 _ => hd h0) (by decide)
    dsimp only [Memory.readBytes, BitVec.add_zero] at h1
    rw [List.cons.inj h1 |>.1]; exact Memory.read8_write8_same _ _ _
  have hrw1 : s₁.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  rcases canWrite_hsp_352_add hrw1 (by omega : k < 64) with ⟨hcw_pos1, hcw_pos2⟩
  have hze32 := Expand.zeroExtend32_ofNat8_eq_truncate32 (by omega : k < 64)
  have hze64 := Expand.zeroExtend64_ofNat8 (by omega : k < 64)
  have hze64_32 := zeroExtend64_truncate32_ofNat64 (by omega : k < 64)
  have hand255 := Expand.zeroExtend64_and255_truncate32_ofNat64 (by omega : k < 64)
  have hand64_255 := Expand.and64_255_ofNat64 (by omega : k < 64)
  have hand40 := Expand.and_0xffffffffff_ofNat64 (by omega : k < 64)
  rcases Expand.cmp32_lt63_lemmas (by omega : k < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1_k := Expand.zeroExtend64_add1_truncate32_ofNat64 (by omega : k < 63)
  rcases iter_counter_lemmas hi with ⟨hi_eq, hi_ne, hi_z, hi_add1, hi1_ze⟩
  have hdst_add : (okmA + BitVec.ofNat 64 dstOff) + 32#64 = okmA + BitVec.ofNat 64 (dstOff + 32) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hrem_sub : BitVec.ofNat 64 rem - 32#64 = BitVec.ofNat 64 (rem - 32) := by
    rcases hrem with rfl | rfl <;> rfl
  dsimp only [k] at hpos_415 hcw_pos1 hcw_pos2 hze32 hze64 hze64_32 hand255 hand64_255
  dsimp only [k] at hand40 hcmp63_eq hcmp63_ne hcmp63_z hadd1_k
  iterate 31 kdf_step
  refine RunsTo.refl ?_
  rcases hm₁_box with ⟨_, hm₁_save⟩
  have hhm_352 : HmacStN
      ((((s₁.mem.write8 (hsp s₀ + 32#64) (BitVec.ofNat 8 (i + 1))).write8
        (hsp s₀ + 352#64 + BitVec.ofNat 64 k) (BitVec.ofNat 8 (i + 1))).write8
        (hsp s₀ + 415#64) (BitVec.ofNat 8 (k + 1))))
      (hsp s₀ + 352#64) C.F prk (tPrev ++ info.take 32)
      (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) := by
    rw [hm₁_save]
    have htake_len : (info.take 32).length = 32 := List.length_take_of_le hpre.info_ge
    have hblk_len : (tPrev ++ info.take 32).length = 64 := by rw [List.length_append, ht_len, htake_len]
    simpa only [hdrop_len] using HmacStN.of_tail_counter_352 (b0 := 0#8) (b1 := BitVec.ofNat 8 k)
      (c := BitVec.ofNat 8 (i + 1)) hblk_len (by rw [hdrop_len]; omega : (info.drop 32).length < 55)
      hx.in_416 hx.cnt_448 hx.out_456 hx.cnt_488
  refine ⟨by kdf_reg,
    HExpCommon.of_agreesOutside_32_560 (off := 32#64) (sz := 464) hc1
      (by kdf_reg) (by kdf_reg) (by kdf_reg)
      (by prove_agrees_hsp) (by decide) (by prove_hmac_208 hc1.hmac_208),
    by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hdst_add],
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hrem_sub],
    by kdf_reg, by kdf_reg, ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    refine HmacStN.of_copy_352_32 hhm_352 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [k, arm64_norm]
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hlen : dstOff ≤ 2 ^ 64 := by have := hpre.okm_len; omega
      have hd2 : DisjointRegions (hsp s₀ + 32#64) 464 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd1 : DisjointRegions (hsp s₀ + 352#64) 23 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 352#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd0 : DisjointRegions (hsp s₀ + 415#64) 1 okmA dstOff :=
        (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 415#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      refine Eq.trans (AgreesOutside.readBytes_eq (m₁ := s₁.mem) ?_ hd2 hlen) ?_
      · prove_agrees_hsp
      · rw [hm₁_save, hA1.readBytes_eq hd1 hlen, hA0.readBytes_eq hd0 hlen]
        exact hx.okm_pre))

set_option maxHeartbeats 4000000 in
theorem iter_b_runsTo [HkdfHooks C.F ext] {aligned : Prop}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (ht_len : tPrev.length = 32) (hi : i = 1 ∨ i = 2) (hrem : rem = 32 ∨ rem = 64)
    (hdst : dstOff + 32 ≤ okmLen)
    (hx : StateLoopA2 b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopC b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hpc := hx.pc_eq; hkdf_iter_b_pre
  refine s2_memcpy_step_ext b C ext
    (dst := hsp s₀ + 352#64) (src := infoA + 32#64) (lr := b + 0x5e4d8#64)
    (len := k) (bs := info.drop 32)
    (by kdf_reg) (by kdf_reg) (by kdf_reg)
    (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, BitVec.add_zero])
    hx2_nat (by kdf_reg) (by rw [Expand.mem_setMem]; exact hinfo_drop)
    (by rw [Expand.mem_setMem]; exact hrw_352) ?_
  hkdf_iter_b_post (b + 0x5e4d8#64)

set_option maxHeartbeats 4000000 in
theorem iter_b_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks} {aligned : Prop}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (ht_len : tPrev.length = 32) (hi : i = 1 ∨ i = 2) (hrem : rem = 32 ∨ rem = 64)
    (hdst : dstOff + 32 ≤ okmLen)
    (hx : StateLoopA2 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoopC hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ · (blkPl_425).base) := by
  have hpc := hx.pc_eq; hkdf_iter_b_pre
  refine s2_memcpy_step_placed_429 h_memcpy
    (dst := hsp s₀ + 352#64) (src := infoA + 32#64) (lr := (blkPl_379).base + 1612#64)
    (len := k) (bs := info.drop 32)
    (by kdf_reg) (by kdf_reg) (by kdf_reg)
    (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, BitVec.add_zero])
    hx2_nat (by kdf_reg) (by rw [Expand.mem_setMem]; exact hinfo_drop)
    (by rw [Expand.mem_setMem]; exact hrw_352) ?_
  hkdf_iter_b_post ((blkPl_379).base + 1612#64)

structure StateLoopFin (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : List (BitVec 8)) (infoA okmA : BitVec 64)
    (tPrev okmSoFar : List (BitVec 8)) (okmLen i rem dstOff : ℕ)
    (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + 0x5e38c#64
  exp     : HExpCommon F (hkdfExtractBytes F salt ikm) info infoA okmLen s₀ s
  x20_eq  : s.readReg64 .x20 = okmA + BitVec.ofNat 64 (dstOff + 32)
  x21_eq  : s.readReg64 .x21 = hsp s₀ + 352#64
  x22_eq  : s.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff
  x24_eq  : s.readReg64 .x24 = 32#64
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 info.length
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 (rem - 32)
  x27_eq  : s.readReg64 .x27 = BitVec.ofNat 64 i
  x28_eq  : s.readReg64 .x28 = hsp s₀ + 352#64
  t_540   : s.mem.readBytes (hsp s₀ + 540#64) 32 =
              hmacWith F (hkdfExtractBytes F salt ikm) (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre : s.mem.readBytes okmA dstOff = okmSoFar

/-- `finalize_fixed` inside loop (`b + 0x6ce50` → `b + 0x63784`): computes
`T(i + 1) = hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])` at `hsp s₀ + 540#64`. -/
theorem iter_fin_runsTo [HkdfHooks C.F ext]
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopC b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopFin b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hrw_hsp := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.exp.common.frame
  have hfin_pre : FinPre3Pfx b C.F (hkdfExtractBytes C.F salt ikm)
      (tPrev ++ info.take 32) (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := hx.pc_eq, status := hx.exp.common.status, key_le := by simp [hkdfExtractBytes, hmacWith],
      tail_lt := by have := hpre.info_lt; simp; omega, hmac_st := by rw [hx.x1_eq]; exact hx.hmac_32,
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.exp.common.sp_eq]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  refine (FinalizeFixed3Proof.finalize_fixed3_pfx_runsTo_ext (ext := ext) hfin_pre).mono
    fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at hout; rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq] at hfr
  have hmsg_eq : (tPrev ++ info.take 32) ++ (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) =
      tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)] := by
    rw [List.append_assoc tPrev (info.take 32), ← List.append_assoc (info.take 32), List.take_append_drop, ← List.append_assoc]
  rw [hmsg_eq] at hout
  have hokm' : s'.mem.readBytes okmA dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hokm_len := hpre.okm_len
      refine (Expand.Frame.readBytes_eq hfr (fun r hr => ?_) (by omega)).trans hx.okm_pre
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> dsimp only
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ - 144#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
  exact ⟨hpc', HExpCommon.of_fin_frame hx.exp hrun' hcs hfr,
    (CalleeSaved.x20 hcs).trans hx.x20_eq, (CalleeSaved.x21 hcs).trans hx.x21_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq, (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, hout, hokm'⟩

theorem iter_fin_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv (LibsignalCodeLoaded lsmpl s₀.mem))
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopC hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have : HkdfPlacedHooks C.F H := { memset := h_memset, memcpy := h_memcpy, compress256 := h_compress }
  have hrw_hsp := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.exp.common.frame
  have hfin_pre : FinPre3Pfx fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm)
      (tPrev ++ info.take 32) (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq, status := hx.exp.common.status, key_le := by simp [hkdfExtractBytes, hmacWith],
      tail_lt := by have := hpre.info_lt; simp; omega, hmac_st := by rw [hx.x1_eq]; exact hx.hmac_32,
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.exp.common.sp_eq]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  have hcl_s : LibsignalCodeLoaded lsmpl s.mem :=
    CryptoVerification.LibsignalCodeLoaded.of_keepsFrozenNoAnon hpre.base_al (HFrame.keepsFrozen hpre hx.exp.common.frame)
  refine (FinalizeFixed3Proof.finalize_fixed3_pfx_placed_runsTo_of_other_block
    hcl_s hfin_pre).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at hout; rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq] at hfr
  have hmsg_eq : (tPrev ++ info.take 32) ++ (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) =
      tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)] := by
    rw [List.append_assoc tPrev (info.take 32), ← List.append_assoc (info.take 32), List.take_append_drop, ← List.append_assoc]
  rw [hmsg_eq] at hout
  have hokm' : s'.mem.readBytes okmA dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hokm_len := hpre.okm_len
      refine (Expand.Frame.readBytes_eq hfr (fun r hr => ?_) (by omega)).trans hx.okm_pre
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> dsimp only
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ - 144#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
  exact ⟨hpc', HExpCommon.of_fin_frame hx.exp hrun' hcs hfr,
    (CalleeSaved.x20 hcs).trans hx.x20_eq, (CalleeSaved.x21 hcs).trans hx.x21_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq, (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, hout, hokm'⟩

set_option hygiene false in local macro "hkdf_iter_d_continue_post" : tactic => `(tactic| (
  let prk := hkdfExtractBytes C.F salt ikm
  let m₁ := s.mem.writeBytes (okmA + 32#64) tN
  have hA1 : AgreesOutside s.mem m₁ (okmA + 32#64) 32 :=
    Expand.agreesOutside_writeBytes_le s.mem (okmA + 32#64) tN 32 (by omega)
  have hc1 : HExpCommon C.F prk info infoA 96 s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_okm hpre hx.exp hrun hsp_eq hx29 hA1 ⟨by decide, by decide⟩
  have hm24_1 : m₁.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64 := hc1.m24_eq
  have hrw1_hsp : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  dsimp only [m₁] at hm24_1 hrw1_hsp
  iterate 9 kdf_step
  refine RunsTo.refl ?_
  have hA2 : AgreesOutside m₁
      ((((m₁.write64 (hsp s₀ + 508#64) (m₁.read64 (hsp s₀ + 540#64))).write64
        (hsp s₀ + 516#64) (m₁.read64 (hsp s₀ + 548#64))).write64
        (hsp s₀ + 524#64) (m₁.read64 (hsp s₀ + 556#64))).write64
        (hsp s₀ + 532#64) (m₁.read64 (hsp s₀ + 564#64)))
      (hsp s₀ + 508#64) 32 := by prove_agrees_hsp
  refine ⟨by kdf_reg,
    HExpCommon.of_agreesOutside_352_592 (off := 508#64) (sz := 32) hc1
      (by kdf_reg) (by kdf_reg) (by kdf_reg) hA2 (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
    by kdf_reg, by kdf_reg, by kdf_reg, ?_, ?_⟩
  · simp only [Expand.mem_setMem]
    have ht_m1 : m₁.readBytes (hsp s₀ + 540#64) 32 = tN := by
      have hd : DisjointRegions (okmA + 32#64) 32 (hsp s₀ + 540#64) 32 :=
        (hpre.disj_okm_stk.sub_left (okmA + 32#64) ⟨by decide, by bv_omega⟩).sub_right
          (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans ht_540
    exact readBytes_32_hsp_508_of_540 ht_m1
      (by simp (config := { decide := true }) only [m₁, arm64_norm])
      (by simp (config := { decide := true }) only [m₁, arm64_norm])
      (by simp (config := { decide := true }) only [m₁, arm64_norm])
      (by simp (config := { decide := true }) only [m₁, arm64_norm])
  · have hd2 : DisjointRegions (hsp s₀ + 508#64) 32 okmA 64 :=
      (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 508#64) ⟨by decide, by bv_omega⟩).sub_right
        okmA ⟨by decide, by bv_omega⟩
    dsimp only [Expand.mem_setMem]
    rw [hA2.readBytes_eq hd2 (by decide), show (64 : ℕ) = 32 + 32 from rfl,
        Bytes.readBytes_add m₁ okmA 32 32]
    have hpre_m1 : m₁.readBytes okmA 32 = okmSoFar := by
      have hd1 : DisjointRegions (okmA + 32#64) 32 okmA 32 := by unfold DisjointRegions; bv_omega
      exact (hA1.readBytes_eq hd1 (by decide)).trans hx.okm_pre
    have hnext_m1 : m₁.readBytes (okmA + BitVec.ofNat 64 32) 32 = tN := by
      have h := Bytes.readBytes_writeBytes_same s.mem (okmA + 32#64) tN (by rw [htNext_len]; decide)
      rwa [htNext_len] at h
    rw [hpre_m1, hnext_m1]))

set_option maxHeartbeats 1600000 in
/-- Loop continuation (`b + 0x5e2a8` → `b + 0x5e2dc`, 4 steps + `memcpy` + 9 steps when `rem = 64`):
copies `T(2)` to `okmA + 32#64`, caches `T(2)` at `hsp s₀ + 508#64`, and loops back to `0x5e2dc`
with `i = 2`, `rem = 32`, `dstOff = 64`. -/
theorem iter_d_continue_runsTo [HkdfHooks C.F ext] {aligned : Prop}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hokm96 : okmLen = 96)
    (hx : StateLoopFin b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen 1 64 32 s₀ s) :
    let tNext := hmacWith C.F (hkdfExtractBytes C.F salt ikm) (tPrev ++ info ++ [2#8])
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoop b C.F salt ikm info infoA okmA tNext (okmSoFar ++ tNext) okmLen 2 32 64 s₀) := by
  intro tNext; subst hokm96
  have ht_540 : s.mem.readBytes (hsp s₀ + 540#64) 32 = tNext := hx.t_540
  have htNext_len : tNext.length = 32 := length_hmacWith _ _ _
  generalize tNext = tN at ht_540 htNext_len ⊢
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx20 : s.readReg64 .x20 = okmA + 64#64 := hx.x20_eq
  have hx21 := hx.x21_eq; have hx22 : s.readReg64 .x22 = okmA + 32#64 := hx.x22_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq
  have hx26 : s.readReg64 .x26 = 32#64 := hx.x26_eq
  have hx27 : s.readReg64 .x27 = 1#64 := hx.x27_eq
  have hx28 := hx.x28_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_okm : s.mem.RW okmA 96 := HFrame.rw_okm hpre hx.exp.common.frame
  have hrw_dst : s.mem.RW (okmA + 32#64) 32 := hrw_okm.sub (by bv_omega)
  iterate 4 kdf_step
  refine s2_memcpy_step_ext b C ext hrun rfl rfl rfl rfl rfl ht_540 hrw_dst ?_
  hkdf_iter_d_continue_post

set_option maxHeartbeats 1600000 in
theorem iter_d_continue_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks} {aligned : Prop}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hokm96 : okmLen = 96)
    (hx : StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen 1 64 32 s₀ s) :
    let tNext := hmacWith C.F (hkdfExtractBytes C.F salt ikm) (tPrev ++ info ++ [2#8])
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tNext (okmSoFar ++ tNext) okmLen 2 32 64 s₀) := by
  intro tNext; subst hokm96
  have ht_540 : s.mem.readBytes (hsp s₀ + 540#64) 32 = tNext := hx.t_540
  have htNext_len : tNext.length = 32 := length_hmacWith _ _ _
  generalize tNext = tN at ht_540 htNext_len ⊢
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status
  have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx20 : s.readReg64 .x20 = okmA + 64#64 := hx.x20_eq
  have hx21 := hx.x21_eq; have hx22 : s.readReg64 .x22 = okmA + 32#64 := hx.x22_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq
  have hx26 : s.readReg64 .x26 = 32#64 := hx.x26_eq
  have hx27 : s.readReg64 .x27 = 1#64 := hx.x27_eq
  have hx28 := hx.x28_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_okm : s.mem.RW okmA 96 := HFrame.rw_okm hpre hx.exp.common.frame
  have hrw_dst : s.mem.RW (okmA + 32#64) 32 := hrw_okm.sub (by bv_omega)
  iterate 4 kdf_step
  refine s2_memcpy_step_placed_429 h_memcpy hrun rfl rfl rfl rfl rfl ht_540 hrw_dst ?_
  hkdf_iter_d_continue_post

theorem okmLen_lt_8161_lemmas {okmLen : ℕ}
    (hokm : okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96) :
    (AddWithCarry64 (BitVec.ofNat 64 okmLen) 18446744073709543454#64 true).2.c = false ∧
    BitVec.ule 8161#64 (BitVec.ofNat 64 okmLen) = false ∧
    BitVec.ult (BitVec.ofNat 64 okmLen) 8161#64 = true := by
  rcases hokm with rfl | rfl | rfl <;> decide

set_option hygiene false in local macro "hkdf_iter_d_done_post" : tactic => `(tactic| (
  let m₁ := s.mem.writeBytes (okmA + BitVec.ofNat 64 dstOff) tN
  have hA1 : AgreesOutside s.mem m₁ (okmA + BitVec.ofNat 64 dstOff) 32 :=
    Expand.agreesOutside_writeBytes_le s.mem (okmA + BitVec.ofNat 64 dstOff) tN 32 (by omega)
  have hc1 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_okm hpre hx.exp hrun hsp_eq hx29 hA1
      ⟨by decide, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hpre.okm_len; omega)]; omega⟩
  have hm0_1 : m₁.read64 (hsp s₀) = BitVec.ofNat 64 okmLen := by
    simpa [Expand.mem_setMem, BitVec.add_zero] using hc1.m0_eq
  have hm0_1' : m₁.read64 (hsp s₀ + 0#64) = BitVec.ofNat 64 okmLen := hc1.m0_eq
  have hm24_1 : m₁.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64 := hc1.m24_eq
  have hrw1_hsp : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  rcases okmLen_lt_8161_lemmas hpre.okm_len with ⟨hokm_c, hokm_ule, hokm_ult⟩
  dsimp only [m₁] at hm0_1 hm0_1' hm24_1 hrw1_hsp
  iterate 13 kdf_step
  refine RunsTo.refl ?_
  have hA2 : AgreesOutside m₁
      ((((m₁.write64 (hsp s₀ + 508#64) (m₁.read64 (hsp s₀ + 540#64))).write64
        (hsp s₀ + 516#64) (m₁.read64 (hsp s₀ + 548#64))).write64
        (hsp s₀ + 524#64) (m₁.read64 (hsp s₀ + 556#64))).write64
        (hsp s₀ + 532#64) (m₁.read64 (hsp s₀ + 564#64)))
      (hsp s₀ + 508#64) 32 := by prove_agrees_hsp
  refine ⟨by kdf_reg,
    HCommon.of_agreesOutside_hsp (off := 508#64) (sz := 32) hc1.common
      (by kdf_reg) (by kdf_reg) (by kdf_reg) hA2 (by decide), ?_⟩
  have hd2 : DisjointRegions (hsp s₀ + 508#64) 32 okmA okmLen :=
    hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 508#64) ⟨by decide, by bv_omega⟩
  dsimp only [Expand.mem_setMem]
  rw [hA2.readBytes_eq hd2 (by have := hpre.okm_len; omega), ← hdst_eq,
      Bytes.readBytes_add m₁ okmA dstOff 32]
  have hpre_m1 : m₁.readBytes okmA dstOff = okmSoFar := by
    have hd1 : DisjointRegions (okmA + BitVec.ofNat 64 dstOff) 32 okmA dstOff := by
      have := hpre.okm_len; unfold DisjointRegions; bv_omega
    exact (hA1.readBytes_eq hd1 (by have := hpre.okm_len; omega)).trans hx.okm_pre
  have hnext_m1 : m₁.readBytes (okmA + BitVec.ofNat 64 dstOff) 32 = tN := by
    have h := Bytes.readBytes_writeBytes_same s.mem (okmA + BitVec.ofNat 64 dstOff) tN
      (by rw [htNext_len]; decide)
    rwa [htNext_len] at h
  rw [hpre_m1, hnext_m1, hokm_eq, hdst_eq]))

set_option maxHeartbeats 1600000 in
/-- Loop exit (`b + 0x5e2a8` → `b + 0x5dfcc`, 4 steps + `memcpy` + 13 steps when `rem = 32`). -/
theorem iter_d_done_runsTo [HkdfHooks C.F ext] {aligned : Prop}
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i dstOff : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hdst_pos : 0 < dstOff) (hdst_eq : dstOff + 32 = okmLen)
    (hokm_eq : okmSoFar ++ hmacWith C.F (hkdfExtractBytes C.F salt ikm)
        (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) =
      hkdfExpand C.F (hkdfExtractBytes C.F salt ikm) info okmLen)
    (hx : StateLoopFin b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i 32 dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s (StateDone b C.F salt ikm info okmA okmLen s₀) := by
  let prk := hkdfExtractBytes C.F salt ikm
  have ht_540 : s.mem.readBytes (hsp s₀ + 540#64) 32 =
      hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) := hx.t_540
  have htNext_len : (hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])).length = 32 := length_hmacWith _ _ _
  generalize hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) = tN at ht_540 htNext_len hokm_eq
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx20 := hx.x20_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq; have hx24 := hx.x24_eq; have hx25 := hx.x25_eq
  have hx26 : s.readReg64 .x26 = 0#64 := hx.x26_eq; have hx27 := hx.x27_eq; have hx28 := hx.x28_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_okm : s.mem.RW okmA okmLen := HFrame.rw_okm hpre hx.exp.common.frame
  have hrw_dst : s.mem.RW (okmA + BitVec.ofNat 64 dstOff) 32 := hrw_okm.sub (by have := hpre.okm_len; bv_omega)
  iterate 4 kdf_step
  refine s2_memcpy_step_ext b C ext hrun rfl rfl rfl rfl rfl ht_540 hrw_dst ?_
  hkdf_iter_d_done_post

set_option maxHeartbeats 1600000 in
theorem iter_d_done_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks} {aligned : Prop}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hdst_pos : 0 < dstOff) (hdst_eq : dstOff + 32 = okmLen)
    (hokm_eq : okmSoFar ++ hmacWith C.F (hkdfExtractBytes C.F salt ikm)
        (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) =
      hkdfExpand C.F (hkdfExtractBytes C.F salt ikm) info okmLen)
    (hx : StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i 32 dstOff s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s (StateDone hkdfCodeFakeB C.F salt ikm info okmA okmLen s₀) := by
  let prk := hkdfExtractBytes C.F salt ikm
  have ht_540 : s.mem.readBytes (hsp s₀ + 540#64) 32 =
      hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) := hx.t_540
  have htNext_len : (hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])).length = 32 := length_hmacWith _ _ _
  generalize hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) = tN at ht_540 htNext_len hokm_eq
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx20 := hx.x20_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq; have hx24 := hx.x24_eq; have hx25 := hx.x25_eq
  have hx26 : s.readReg64 .x26 = 0#64 := hx.x26_eq; have hx27 := hx.x27_eq; have hx28 := hx.x28_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_okm : s.mem.RW okmA okmLen := HFrame.rw_okm hpre hx.exp.common.frame
  have hrw_dst : s.mem.RW (okmA + BitVec.ofNat 64 dstOff) 32 := hrw_okm.sub (by have := hpre.okm_len; bv_omega)
  iterate 4 kdf_step
  refine s2_memcpy_step_placed_429 h_memcpy hrun rfl rfl rfl rfl rfl ht_540 hrw_dst ?_
  hkdf_iter_d_done_post

/-- One full loop iteration (`b + 0x5e2dc` → `b + 0x5e2a8`, `A1 + A2 + B + Fin`). -/
theorem iter_step_runsTo [HkdfHooks C.F ext]
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (ht_len : tPrev.length = 32) (hi : i = 1 ∨ i = 2) (hrem : rem = 32 ∨ rem = 64)
    (hdst : dstOff + 32 ≤ okmLen)
    (hx : StateLoop b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt b ext) s
      (StateLoopFin b C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) :=
  (iter_a1_runsTo hpre ht_len hrem (by omega) hx).trans fun _ hs1 =>
  (iter_a2_runsTo hpre ht_len (by omega) hs1).trans fun _ hs2 =>
  (iter_b_runsTo hpre ht_len hi hrem hdst hs2).trans fun _ hs3 =>
  iter_fin_runsTo hpre (by omega) hs3

theorem iter_step_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv
      (LibsignalCodeLoaded lsmpl s₀.mem))
    (ht_len : tPrev.length = 32) (hi : i = 1 ∨ i = 2) (hrem : rem = 32 ∨ rem = 64)
    (hdst : dstOff + 32 ≤ okmLen)
    (hx : StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) :=
  (iter_a1_placed_runsTo hpre ht_len hrem (by omega) hx).trans fun _ hs1 =>
  (iter_a2_placed_runsTo h_memcpy h_compress hpre ht_len (by omega) hs1).trans fun _ hs2 =>
  (iter_b_placed_runsTo h_memcpy hpre ht_len hi hrem hdst hs2).trans fun _ hs3 =>
  iter_fin_placed_runsTo h_memcpy h_memset h_compress hpre (by omega) hs3

/-- Full `RunsTo` theorem for `spqr::kdf::hkdf_to_slice` (`b + 0x63284` → `s₀.readReg64 .lr`). -/
theorem hkdf_to_slice_runsTo_ext [HkdfHooks C.F ext]
    (hNfs : Nfs3GenRunsToExt b C.F ext)
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : HPre b salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀ (HPost C.F salt ikm info okmA okmLen s₀) := by
  refine (block1_phase_runsTo hNfs hpre).trans fun s₁ hs₁ => ?_
  rcases hpre.okm_len with rfl | rfl | rfl
  · exact (b1_done_32_runsTo hpre hs₁).trans fun _ hdone => epilogue_runsTo hpre hdone
  · refine (b1_to_loop_runsTo (Or.inl rfl) hs₁).trans fun _ hloop1 => ?_
    refine (iter_step_runsTo hpre (Expand.t1_length _ _ _) (Or.inl rfl) (Or.inl rfl) (by decide) hloop1).trans fun _ hfin1 => ?_
    refine (iter_d_done_runsTo hpre (by decide) rfl ?_ hfin1).trans fun _ hdone => epilogue_runsTo hpre hdone
    exact (hkdfExpand_64_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm
  · refine (b1_to_loop_runsTo (Or.inr rfl) hs₁).trans fun _ hloop1 => ?_
    refine (iter_step_runsTo hpre (Expand.t1_length _ _ _) (Or.inl rfl) (Or.inr rfl) (by decide) hloop1).trans fun _ hfin1 => ?_
    refine (iter_d_continue_runsTo hpre rfl hfin1).trans fun _ hloop2 => ?_
    refine (iter_step_runsTo hpre (length_hmacWith _ _ _) (Or.inr rfl) (Or.inl rfl) (by decide) hloop2).trans fun _ hfin2 => ?_
    refine (iter_d_done_runsTo hpre (by decide) rfl ?_ hfin2).trans fun _ hdone => epilogue_runsTo hpre hdone
    exact (hkdfExpand_96_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm

/-- Full placed `RunsTo` theorem for `spqr::kdf::hkdf_to_slice` (Block `379`). -/
theorem hkdf_to_slice_placed_runsTo [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    (hNfs : Nfs3GenRunsToProg ((blkPC_379).rebase (blkPl_379).base H)
      nfs3PlacedFakeB (blkPl_402).base (LibsignalCodeLoaded lsmpl) C.F)
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀
      nfs3PlacedFakeB (LibsignalCodeLoaded lsmpl s₀.mem)) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s₀ (HPost C.F salt ikm info okmA okmLen s₀) := by
  refine (block1_phase_placed_runsTo h_memcpy h_memset h_compress hNfs hpre).trans fun s₁ hs₁ => ?_
  rcases hpre.okm_len with rfl | rfl | rfl
  · exact (b1_done_32_placed_runsTo hpre hs₁).trans fun _ hdone => epilogue_placed_runsTo hpre hdone
  · refine (b1_to_loop_placed_runsTo (Or.inl rfl) hs₁).trans fun _ hloop1 => ?_
    refine (iter_step_placed_runsTo h_memcpy h_memset h_compress hpre (Expand.t1_length _ _ _)
      (Or.inl rfl) (Or.inl rfl) (by decide) hloop1).trans fun _ hfin1 => ?_
    refine (iter_d_done_placed_runsTo h_memcpy hpre (by decide) rfl ?_ hfin1).trans fun _ hdone => epilogue_placed_runsTo hpre hdone
    exact (hkdfExpand_64_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm
  · refine (b1_to_loop_placed_runsTo (Or.inr rfl) hs₁).trans fun _ hloop1 => ?_
    refine (iter_step_placed_runsTo h_memcpy h_memset h_compress hpre (Expand.t1_length _ _ _)
      (Or.inl rfl) (Or.inr rfl) (by decide) hloop1).trans fun _ hfin1 => ?_
    refine (iter_d_continue_placed_runsTo h_memcpy hpre rfl hfin1).trans fun _ hloop2 => ?_
    refine (iter_step_placed_runsTo h_memcpy h_memset h_compress hpre (length_hmacWith _ _ _)
      (Or.inr rfl) (Or.inl rfl) (by decide) hloop2).trans fun _ hfin2 => ?_
    refine (iter_d_done_placed_runsTo h_memcpy hpre (by decide) rfl ?_ hfin2).trans fun _ hdone => epilogue_placed_runsTo hpre hdone
    exact (hkdfExpand_96_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm

end CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCallees
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage2
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1CommonExt -- shake: keep

/-!
# `initialize_alice_session` SPQR Cut, Session Assembly, and Top-Level Proofs

Proves the `spqr::initial_state` cut (`initAlice_spqr_init`), `SessionState` construction
(`initAlice_session_build`), and top-level `initializeAliceSession_ok` /
`initializeAliceSession_err` contracts (`0x6fcd0`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace CryptoVerification.E2E.Pqxdh.Initiator
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.E2E CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Pqxdh
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
ls_attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  CryptoVerification.libsignalSessionCode_fnOff_0x21c6c
  CryptoVerification.libsignalSessionCode_fnOff_0x125a4
  CryptoVerification.libsignalSessionCode_fnOff_0x11c98
  CryptoVerification.libsignalSessionCode_fnOff_0x117e8
  CryptoVerification.libsignalSessionCode_fnOff_0x12064
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
/-! ## 3. Segment 5: `initAlice_spqr_init` (`+2588..+2848`, `0x497ac..0x498b0`) -/
@[local simp, local arm64_norm, local wp_norm]
private theorem bv_add_5296_sub_48 (fsp : BitVec 64) :
    fsp + 5296#64 - 48#64 = fsp + 5248#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem cond_ne_subs_0_1 :
    ConditionHolds CondCode.NE (subsPState64 0#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide
theorem memRegion36_336_split (fsp : BitVec 64) :
    memRegion (fsp + 336#64) 36 =
      cells (fsp + 336#64) 4 ∗ (∃∗ v : BitVec 32, (fsp + 368#64) ↦₃₂ v) := by
  rw [ProofLib.memRegion_split' (b := fsp + 336#64) (n := 32) (k := 4)
      (b' := fsp + 368#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (fsp + 336#64) 4 (by decide) :
      memRegion (fsp + 336#64) 32 = cells (fsp + 336#64) 4),
    ProofLib.memRegion_four (fsp + 368#64)]
theorem memRegion68_2080_split (fsp : BitVec 64) :
    memRegion (fsp + 2080#64) 68 =
      cells (fsp + 2080#64) 8 ∗ (∃∗ v : BitVec 32, (fsp + 2144#64) ↦₃₂ v) := by
  rw [ProofLib.memRegion_split' (b := fsp + 2080#64) (n := 64) (k := 4)
      (b' := fsp + 2144#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (fsp + 2080#64) 8 (by decide) :
      memRegion (fsp + 2080#64) 64 = cells (fsp + 2080#64) 8),
    ProofLib.memRegion_four (fsp + 2144#64)]
theorem cells4_2080_to_memRegion32 (fsp w0 w1 w2 w3 : BitVec 64) :
    ((fsp + 2080#64) ↦₆₄ w0) ∗ ((fsp + 2088#64) ↦₆₄ w1) ∗ ((fsp + 2096#64) ↦₆₄ w2) ∗ ((fsp +
      2104#64) ↦₆₄ w3) ⊢
      memRegion (fsp + 2080#64) 32 := by
  rw [(memRegion_cells (fsp + 2080#64) 4 (by decide) :
    memRegion (fsp + 2080#64) 32 = cells (fsp + 2080#64) 4)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))
theorem ccOk72_3648_to_spqrParams (fsp : BitVec 64)
    (rk0 rk1 rk2 rk3 ck0 ck1 ck2 ck3 : BitVec 64) :
    ((fsp + 3648#64) ↦₃₂ 0#32) ∗ ((fsp + 3652#64) ↦₆₄ rk0) ∗ ((fsp + 3660#64) ↦₆₄ rk1) ∗
    ((fsp + 3668#64) ↦₆₄ rk2) ∗ ((fsp + 3676#64) ↦₆₄ rk3) ∗ ((fsp + 3684#64) ↦₆₄ ck0) ∗ ((fsp +
      3692#64) ↦₆₄ ck1) ∗
    ((fsp + 3700#64) ↦₆₄ ck2) ∗ ((fsp + 3708#64) ↦₆₄ ck3) ∗ ((fsp + 3716#64) ↦₃₂ 0#32) ⊢
      ∃∗ w3680 : BitVec 32, ∃∗ w3672 : BitVec 64, ∃∗ w3668 : BitVec 32,
      ∃∗ w3664 : BitVec 32, ∃∗ w3656 : BitVec 64, ∃∗ w3648 : BitVec 64,
        ((fsp + 3648#64) ↦₆₄ w3648) ∗ ((fsp + 3656#64) ↦₆₄ w3656) ∗ ((fsp + 3664#64) ↦₃₂ w3664) ∗
        ((fsp + 3668#64) ↦₃₂ w3668) ∗ ((fsp + 3672#64) ↦₆₄ w3672) ∗ ((fsp + 3680#64) ↦₃₂ w3680) ∗
        memRegion (fsp + 3684#64) 36 := by
  have hm72 :
      ((fsp + 3648#64) ↦₃₂ 0#32) ∗ ((fsp + 3652#64) ↦₆₄ rk0) ∗ ((fsp + 3660#64) ↦₆₄ rk1) ∗
      ((fsp + 3668#64) ↦₆₄ rk2) ∗ ((fsp + 3676#64) ↦₆₄ rk3) ∗
      ((fsp + 3684#64) ↦₆₄ ck0) ∗ ((fsp + 3692#64) ↦₆₄ ck1) ∗
      ((fsp + 3700#64) ↦₆₄ ck2) ∗ ((fsp + 3708#64) ↦₆₄ ck3) ∗ ((fsp + 3716#64) ↦₃₂ 0#32) ⊢
        memRegion (fsp + 3648#64) 72 := by
    rw [ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 4) (k := 68) (b' :=
      fsp + 3652#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3652#64) (n := 8) (k := 60) (b' :=
        fsp + 3660#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3660#64) (n := 8) (k := 52) (b' :=
        fsp + 3668#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3668#64) (n := 8) (k := 44) (b' :=
        fsp + 3676#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3676#64) (n := 8) (k := 36) (b' :=
        fsp + 3684#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3684#64) (n := 8) (k := 28) (b' :=
        fsp + 3692#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3692#64) (n := 8) (k := 20) (b' :=
        fsp + 3700#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3700#64) (n := 8) (k := 12) (b' :=
        fsp + 3708#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3708#64) (n := 8) (k := 4) (b' :=
        fsp + 3716#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo32_entails_memRegion _ _)))))))))
  refine Entails.trans hm72 ?_
  rw [ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 8) (k := 64) (b' :=
    fsp + 3656#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 3656#64) (n := 8) (k := 56) (b' :=
      fsp + 3664#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 3664#64) (n := 4) (k := 52) (b' :=
      fsp + 3668#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 3668#64) (n := 4) (k := 48) (b' :=
      fsp + 3672#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 3672#64) (n := 8) (k := 40) (b' :=
      fsp + 3680#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 3680#64) (n := 4) (k := 36) (b' :=
      fsp + 3684#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (fsp + 3648#64),
    ProofLib.memRegion_eight (fsp + 3656#64),
    ProofLib.memRegion_four (fsp + 3664#64),
    ProofLib.memRegion_four (fsp + 3668#64),
    ProofLib.memRegion_eight (fsp + 3672#64),
    ProofLib.memRegion_four (fsp + 3680#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _
theorem spqrParams_3648_merge_72 (fsp : BitVec 64)
    (w3648 w3656 w3672 : BitVec 64) (w3664 w3668 w3680 : BitVec 32) :
    ((fsp + 3648#64) ↦₆₄ w3648) ∗ ((fsp + 3656#64) ↦₆₄ w3656) ∗ ((fsp + 3664#64) ↦₃₂ w3664) ∗
    ((fsp + 3668#64) ↦₃₂ w3668) ∗ ((fsp + 3672#64) ↦₆₄ w3672) ∗ ((fsp + 3680#64) ↦₃₂ w3680) ∗
    memRegion (fsp + 3684#64) 36 ⊢
      memRegion (fsp + 3648#64) 72 := by
  rw [
    ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 8) (k := 64) (b' :=
      fsp + 3656#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 3656#64) (n := 8) (k := 56) (b' :=
      fsp + 3664#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 3664#64) (n := 4) (k := 52) (b' :=
      fsp + 3668#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 3668#64) (n := 4) (k := 48) (b' :=
      fsp + 3672#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 3672#64) (n := 8) (k := 40) (b' :=
      fsp + 3680#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 3680#64) (n := 4) (k := 36) (b' :=
      fsp + 3684#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (Entails.refl _))))))
/-- The cells `initAlice_to_spqr` leaves at the `bl spqr::initial_state` (`+2700`): the `Params`
block at `fsp + 3648` (`auth_key` = `fsp + 272`, the chain parameters, `A2B`, `V1`, `V1`), the
`pqr_key` at `fsp + 272`, the new chain key at `fsp + 336` and the root key at `fsp + 5248`. -/
def aliceSpqrCutCells (fsp paramsPtr : BitVec 64) (b_111 : BitVec 8) (rk1 ck1_0 pqrKey : Bytes) :
    SepProp :=
  ((paramsPtr + 273#64) ↦₈ b_111) ∗ ((fsp + 272#64) ↦ₛ bytesToBv8 pqrKey) ∗
  ((fsp + 336#64) ↦ₛ bytesToBv8 ck1_0) ∗ ((fsp + 5248#64) ↦ₛ bytesToBv8 rk1) ∗
  ((fsp + 3648#64) ↦₆₄ (fsp + 272#64)) ∗ ((fsp + 3656#64) ↦₆₄ 32#64) ∗
  ((fsp + 3664#64) ↦₃₂ 25000#32) ∗ ((fsp + 3668#64) ↦₃₂ 2000#32) ∗
  ((fsp + 3672#64) ↦₆₄ 0x100000000#64) ∗ ((fsp + 3680#64) ↦₃₂ 1#32)

theorem aliceCut_entails {P T K F : SepProp} (h : P ⊢ (T ∗ K) ∗ F) : P ⊢ T ∗ K ∗ anyHeap :=
  Entails.trans h (by
    rw [sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))

/-- What every Alice cut proof leaves at `spqr::initial_state`'s entry: the cut cells, a kept
part `K` and an arbitrary rest; `x0` = the `Params`, `x20` = `paramsPtr`, `x30` = `entry + 2704`. -/
def AliceCutPost (entry : BitVec 64) (s0 : State) (fsp paramsPtr : BitVec 64)
    (rk1 ck1_0 pqrKey : Bytes) (K : SepProp) (sf : State) (P_f : SepProp) : Prop :=
  (P_f ⊢ aliceSpqrCutCells fsp paramsPtr 0#8 rk1 ck1_0 pqrKey ∗ K ∗ anyHeap) ∧
  sf.status = ExecStatus.Running ∧ sf.sp = fsp ∧
  sf.readReg64 (.gpr 0#5) = fsp + 3648#64 ∧
  sf.readReg64 (.gpr 20#5) = paramsPtr ∧
  sf.readReg64 (.gpr 30#5) = entry + 2704#64 ∧
  sf.trace = s0.trace

theorem AliceCutPost.weaken {entry : BitVec 64} {s0 : State} {fsp paramsPtr : BitVec 64}
    {rk1 ck1_0 pqrKey : Bytes} {K K' : SepProp} {sf : State} {P_f : SepProp}
    (hK : K ⊢ K' ∗ anyHeap)
    (h : AliceCutPost entry s0 fsp paramsPtr rk1 ck1_0 pqrKey K sf P_f) :
    AliceCutPost entry s0 fsp paramsPtr rk1 ck1_0 pqrKey K' sf P_f := by
  obtain ⟨hP, h2⟩ := h
  refine ⟨Entails.trans hP (sepConj_mono_right ?_), h2⟩
  refine Entails.trans (sepConj_mono_left hK) ?_
  rw [sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem cutKeep {K R Full : SepProp} (h : Full = K ∗ R) : Full ⊢ K ∗ anyHeap :=
  h ▸ sepConj_mono_right (entails_anyHeap _)

/-! ## 4. Segment 6: `initAlice_session_build` (`+2848..+2952`, `0x498b0..0x49918`) -/
private theorem sepWPp_pure_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (hP : P = ⌜φ⌝ ∗ F)
    (h : φ → SepWPp prog ret s F Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ SepWPp.pure_left h
abbrev sessionBuildStack : Nat := 480 + allocHookStack
def alicePre72Bv8 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr : BitVec 64) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 localIkBoxPtr ++ unpack64 33#64 ++
  unpack64 33#64 ++ unpack64 remoteIkBoxPtr ++ unpack64 33#64 ++
  unpack64 32#64 ++ unpack64 rootKeyBoxPtr ++ unpack64 32#64
@[simp]
theorem alicePre72Bv8_length (p1 p2 p3 : BitVec 64) :
    (alicePre72Bv8 p1 p2 p3).length = 72 := by
  simp [alicePre72Bv8]
theorem alicePre72_eq_pointsToBytes (ptr p1 p2 p3 : BitVec 64) :
    (ptr ↦₆₄ 33#64) ∗ ((ptr + 0x08#64) ↦₆₄ p1) ∗ ((ptr + 0x10#64) ↦₆₄ 33#64) ∗ ((ptr +
      0x18#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x20#64) ↦₆₄ p2) ∗ ((ptr + 0x28#64) ↦₆₄ 33#64) ∗ ((ptr + 0x30#64) ↦₆₄ 32#64) ∗
    ((ptr + 0x38#64) ↦₆₄ p3) ∗ ((ptr + 0x40#64) ↦₆₄ 32#64) =
      (ptr ↦ₛ alicePre72Bv8 p1 p2 p3) := by
  unfold alicePre72Bv8
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes]
def aliceMid48Bv8 (baseKeyBoxPtr spqrCap spqrBufPtr spqrLen : BitVec 64) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 baseKeyBoxPtr ++ unpack64 33#64 ++
  unpack64 spqrCap ++ unpack64 spqrBufPtr ++ unpack64 spqrLen
@[simp]
theorem aliceMid48Bv8_length (p4 c5 p5 l5 : BitVec 64) :
    (aliceMid48Bv8 p4 c5 p5 l5).length = 48 := by
  simp [aliceMid48Bv8]
theorem aliceMid48_eq_pointsToBytes (ptr p4 c5 p5 l5 : BitVec 64) :
    ((ptr + 0x60#64) ↦₆₄ 33#64) ∗ ((ptr + 0x68#64) ↦₆₄ p4) ∗ ((ptr + 0x70#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x78#64) ↦₆₄ c5) ∗ ((ptr + 0x80#64) ↦₆₄ p5) ∗ ((ptr + 0x88#64) ↦₆₄ l5) =
      ((ptr + 0x60#64) ↦ₛ aliceMid48Bv8 p4 c5 p5 l5) := by
  unfold aliceMid48Bv8
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes]
def aliceHead144Bv8 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr
    baseKeyBoxPtr spqrCap spqrBufPtr spqrLen : BitVec 64) : List (BitVec 8) :=
  alicePre72Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr ++
  receiverChainVecBytes24 chainBufPtr ++
  aliceMid48Bv8 baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
@[simp]
theorem aliceHead144Bv8_length (p1 p2 p3 cb p4 c5 p5 l5 : BitVec 64) :
    (aliceHead144Bv8 p1 p2 p3 cb p4 c5 p5 l5).length = 144 := by
  simp [aliceHead144Bv8, receiverChainVecBytes24_length]
theorem aliceHead144_eq_pointsToBytes (ptr p1 p2 p3 cb p4 c5 p5 l5 : BitVec 64) :
    (ptr ↦ₛ alicePre72Bv8 p1 p2 p3) ∗ receiverChainVecFieldsAt ptr cb ∗
    ((ptr + 0x60#64) ↦ₛ aliceMid48Bv8 p4 c5 p5 l5) =
      (ptr ↦ₛ aliceHead144Bv8 p1 p2 p3 cb p4 c5 p5 l5) := by
  unfold aliceHead144Bv8
  rw [receiverChainVecFieldsAt_eq_pointsToBytes]
  simp only [List.append_assoc, pointsToBytes_append, alicePre72Bv8_length,
    receiverChainVecBytes24_length, BitVec.add_assoc, BitVec.reduceAdd]
def aliceTail100Bv8 (pad_f4 : BitVec 32) (pad40 : List (BitVec 8))
    (kyberCap kyberPtr kyberLen : BitVec 64) (kyberId pad_144 : BitVec 32) : List (BitVec 8) :=
  unpack32 pad_f4 ++
  unpack64 0xffffffffffffffff#64 ++
  pad40 ++
  unpack64 kyberCap ++
  unpack64 kyberPtr ++
  unpack64 kyberLen ++
  unpack32 kyberId ++
  unpack32 pad_144 ++
  unpack32 4#32 ++
  unpack64 0#64 ++
  unpack32 0#32
theorem aliceTail100Bv8_length (pad_f4 : BitVec 32) (pad40 : List (BitVec 8))
    (hpad40 : pad40.length = 40)
    (kyberCap kyberPtr kyberLen : BitVec 64) (kyberId pad_144 : BitVec 32) :
    (aliceTail100Bv8 pad_f4 pad40 kyberCap kyberPtr kyberLen kyberId pad_144).length = 100 := by
  simp [aliceTail100Bv8, unpack32, hpad40]
theorem aliceTail100_eq_pointsToBytes (ptr : BitVec 64)
    (pad_f4 : BitVec 32) (pad40 : List (BitVec 8)) (hpad40 : pad40.length = 40)
    (kyberCap kyberPtr kyberLen : BitVec 64) (kyberId pad_144 : BitVec 32) :
    ((ptr + 0xf4#64) ↦₃₂ pad_f4) ∗ ((ptr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((ptr +
      0x100#64) ↦ₛ pad40) ∗
    ((ptr + 0x128#64) ↦₆₄ kyberCap) ∗ ((ptr + 0x130#64) ↦₆₄ kyberPtr) ∗ ((ptr +
      0x138#64) ↦₆₄ kyberLen) ∗
    ((ptr + 0x140#64) ↦₃₂ kyberId) ∗ ((ptr + 0x144#64) ↦₃₂ pad_144) ∗ ((ptr + 0x148#64) ↦₃₂ 4#32) ∗
    ((ptr + 0x14c#64) ↦₆₄ 0#64) ∗ ((ptr + 0x154#64) ↦₃₂ 0#32) =
      ((ptr +
        0xf4#64) ↦ₛ aliceTail100Bv8 pad_f4 pad40 kyberCap kyberPtr kyberLen kyberId pad_144) := by
  unfold aliceTail100Bv8
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, unpack32_length, hpad40,
    BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes, ←
      pointsTo32_eq_pointsToBytes]
def alicePost248Bv8 (baseKeyBoxPtr spqrCap spqrBufPtr spqrLen : BitVec 64)
    (pad92 tail100 : List (BitVec 8)) : List (BitVec 8) :=
  aliceMid48Bv8 baseKeyBoxPtr spqrCap spqrBufPtr spqrLen ++
  unpack64 0xffffffffffffffff#64 ++
  pad92 ++
  tail100
theorem alicePost248Bv8_length (p4 c5 p5 l5 : BitVec 64)
    (pad92 tail100 : List (BitVec 8)) (h92 : pad92.length = 92) (h100 : tail100.length = 100) :
    (alicePost248Bv8 p4 c5 p5 l5 pad92 tail100).length = 248 := by
  simp [alicePost248Bv8, h92, h100]
theorem alicePost248_eq_pointsToBytes (ptr p4 c5 p5 l5 : BitVec 64)
    (pad92 tail100 : List (BitVec 8)) (hpad92 : pad92.length = 92) :
    ((ptr + 0x60#64) ↦ₛ aliceMid48Bv8 p4 c5 p5 l5) ∗ ((ptr + 0x90#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    ((ptr + 0x98#64) ↦ₛ pad92) ∗ ((ptr + 0xf4#64) ↦ₛ tail100) =
      ((ptr + 0x60#64) ↦ₛ alicePost248Bv8 p4 c5 p5 l5 pad92 tail100) := by
  unfold alicePost248Bv8
  simp only [List.append_assoc, pointsToBytes_append, aliceMid48Bv8_length, unpack64_length, hpad92,
    BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes]
def aliceSession344Bv8 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr
    baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
    senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (pad40 : List (BitVec 8))
    (kyberCap kyberPtr kyberLen : BitVec 64) (kyberId pad_144 : BitVec 32) : List (BitVec 8) :=
  aliceHead144Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr
    baseKeyBoxPtr spqrCap spqrBufPtr spqrLen ++
  senderChainBytes100 senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr 0#32 ++
  aliceTail100Bv8 pad_f4 pad40 kyberCap kyberPtr kyberLen kyberId pad_144
theorem aliceSession344Bv8_length (p1 p2 p3 cb p4 c5 p5 l5 spub spriv sck : BitVec 64)
    (pad_f4 : BitVec 32) (pad40 : List (BitVec 8)) (hpad40 : pad40.length = 40)
    (kyberCap kyberPtr kyberLen : BitVec 64) (kyberId pad_144 : BitVec 32) :
    (aliceSession344Bv8 p1 p2 p3 cb p4 c5 p5 l5 spub spriv sck
      pad_f4 pad40 kyberCap kyberPtr kyberLen kyberId pad_144).length = 344 := by
  simp [aliceSession344Bv8, senderChainBytes100_length,
    aliceTail100Bv8_length pad_f4 pad40 hpad40 kyberCap kyberPtr kyberLen kyberId pad_144]
theorem aliceSession344_pack (ptr p1 p2 p3 cb p4 c5 p5 l5 spub spriv sck : BitVec 64)
    (pad_f4 : BitVec 32) (pad40 : List (BitVec 8))
    (kyberCap kyberPtr kyberLen : BitVec 64) (kyberId pad_144 : BitVec 32) :
    (ptr ↦ₛ aliceHead144Bv8 p1 p2 p3 cb p4 c5 p5 l5) ∗ senderChainFieldsAt ptr spub spriv sck 0#32 ∗
    ((ptr + 0xf4#64) ↦ₛ aliceTail100Bv8 pad_f4 pad40 kyberCap kyberPtr kyberLen kyberId pad_144) =
      (ptr ↦ₛ aliceSession344Bv8 p1 p2 p3 cb p4 c5 p5 l5 spub spriv sck
        pad_f4 pad40 kyberCap kyberPtr kyberLen kyberId pad_144) := by
  unfold aliceSession344Bv8
  rw [senderChainFieldsAt_eq_pointsToBytes]
  simp only [List.append_assoc, pointsToBytes_append, aliceHead144Bv8_length,
    senderChainBytes100_length, BitVec.add_assoc, BitVec.reduceAdd]
theorem stackAt_sessionBuild_split_sessionNew (fsp : BitVec 64) :
    stackAt fsp sessionBuildStack =
      memRegion (fsp - 4576#64) 352 ∗ (memRegion (fsp - 4224#64) 128 ∗
        stackAt fsp allocHookStack) := by
  simp only [stackAt, sessionBuildStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := fsp - 4576#64) (n := 352) (k := 4224)
      (b' := fsp - 4224#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp - 4224#64) (n := 128) (k := 4096)
      (b' := fsp - 4096#64) rfl (by bv_omega) (by decide)]
theorem stackAt_sessionBuild_split_withReceiver (fsp : BitVec 64) :
    stackAt fsp sessionBuildStack =
      memRegion (fsp - 4576#64) 480 ∗ stackAt fsp allocHookStack := by
  simp only [stackAt, sessionBuildStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := fsp - 4576#64) (n := 480) (k := 4096)
      (b' := fsp - 4096#64) rfl (by bv_omega) (by decide)]
theorem stackAt_sessionBuild_split_withSender (fsp : BitVec 64) :
    stackAt fsp sessionBuildStack =
      memRegion (fsp - 4576#64) 320 ∗ (memRegion (fsp - 4256#64) 160 ∗
        stackAt fsp allocHookStack) := by
  simp only [stackAt, sessionBuildStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := fsp - 4576#64) (n := 320) (k := 4256)
      (b' := fsp - 4256#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp - 4256#64) (n := 160) (k := 4096)
      (b' := fsp - 4096#64) rfl (by bv_omega) (by decide)]
theorem stackAt_sessionBuild_split_setKyberCt (fsp : BitVec 64) :
    stackAt fsp sessionBuildStack =
      memRegion (fsp - 4576#64) 4528 ∗ cells (fsp - 48#64) 6 := by
  simp only [stackAt, sessionBuildStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := fsp - 4576#64) (n := 4528) (k := 48)
      (b' := fsp - 48#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (fsp - 48#64) 6 (by decide) :
      memRegion (fsp - 48#64) 48 = cells (fsp - 48#64) 6)]
theorem memRegion96_split_92_4 (ptr : BitVec 64) :
    memRegion ptr 96 =
      (∃∗ pad92 : List (BitVec 8), ⌜pad92.length = 92⌝ ∗ (ptr ↦ₛ pad92)) ∗
      (∃∗ pad_f4 : BitVec 32, (ptr + 92#64) ↦₃₂ pad_f4) := by
  rw [ProofLib.memRegion_split' (b := ptr) (n := 92) (k := 4)
        (b' := ptr + 92#64) rfl (by bv_omega) (by decide),
      memRegion_eq_exists_bytes ptr 92 (by decide),
      ProofLib.memRegion_four (ptr + 92#64)]
theorem memRegion24_split_8_8_4_4 (ptr : BitVec 64) :
    memRegion ptr 24 =
      (∃∗ w0 : BitVec 64, ptr ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (ptr + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 32, (ptr + 16#64) ↦₃₂ w2) ∗ (∃∗ w3 : BitVec 32, (ptr + 20#64) ↦₃₂ w3) := by
  rw [ProofLib.memRegion_split' (b := ptr) (n := 8) (k := 16)
        (b' := ptr + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ptr + 8#64) (n := 8) (k := 8)
        (b' := ptr + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ptr + 16#64) (n := 4) (k := 4)
        (b' := ptr + 20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ptr,
      ProofLib.memRegion_eight (ptr + 8#64),
      ProofLib.memRegion_four (ptr + 16#64),
      ProofLib.memRegion_four (ptr + 20#64)]
theorem spqrOut_2080_to_memRegion344 (fsp : BitVec 64) :
    ((fsp + 2080#64) ↦₆₄ 0#64) ∗ ((fsp + 2088#64) ↦₆₄ 0#64) ∗ ((fsp + 2096#64) ↦₆₄ 1#64) ∗
    ((fsp + 2104#64) ↦₆₄ 0#64) ∗ memRegion (fsp + 2112#64) 312 ⊢
      memRegion (fsp + 2080#64) 344 := by
  rw [ProofLib.memRegion_split' (b := fsp + 2080#64) (n := 32) (k := 312)
      (b' := fsp + 2112#64) rfl (by bv_omega) (by decide),
    ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
  refine sepConj_mono_left ?_
  simpa only [sepConj_assoc] using cells4_2080_to_memRegion32 fsp 0#64 0#64 1#64 0#64
theorem cells3_480_to_memRegion24 (fsp w0 w1 w2 : BitVec 64) :
    ((fsp + 480#64) ↦₆₄ w0) ∗ ((fsp + 488#64) ↦₆₄ w1) ∗ ((fsp + 496#64) ↦₆₄ w2) ⊢
      memRegion (fsp + 480#64) 24 := by
  rw [(memRegion_cells (fsp + 480#64) 3 (by decide) :
    memRegion (fsp + 480#64) 24 = cells (fsp + 480#64) 3)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.refl _)))
theorem withReceiver_inPtr_to_memRegion344 (ptr chainBufPtr : BitVec 64)
    (pre72 post248 : List (BitVec 8))
    (hpre : pre72.length = 72) (hpost : post248.length = 248) :
    (ptr ↦ₛ pre72) ∗ receiverChainVecFieldsAt ptr chainBufPtr ∗ ((ptr + 0x60#64) ↦ₛ post248) ⊢
      memRegion ptr 344 := by
  rw [withReceiverChain_pack344 ptr chainBufPtr pre72 post248 hpre]
  have hlen : (pre72 ++ (receiverChainVecBytes24 chainBufPtr ++ post248)).length = 344 := by
    simp [hpre, hpost, receiverChainVecBytes24_length]
  rw [← hlen]
  exact pointsToBytes_entails_memRegion ptr _
theorem withSender_inPtr_to_memRegion344 (ptr pubPtr privPtr ckPtr : BitVec 64)
    (idx : BitVec 32) (pre144 post100 : List (BitVec 8))
    (hpre : pre144.length = 144) (hpost : post100.length = 100) :
    (ptr ↦ₛ pre144) ∗ senderChainFieldsAt ptr pubPtr privPtr ckPtr idx ∗ ((ptr +
      0xf4#64) ↦ₛ post100) ⊢
      memRegion ptr 344 := by
  rw [withSenderChain_pack344 ptr pubPtr privPtr ckPtr idx pre144 post100 hpre]
  have hlen : (pre144 ++ (senderChainBytes100 pubPtr privPtr ckPtr idx ++ post100)).length = 344 :=
    by
    simp [hpre, hpost, senderChainBytes100_length]
  rw [← hlen]
  exact pointsToBytes_entails_memRegion ptr _
theorem setKyberCt_pre_entails (ptr w130 w138 : BitVec 64) (w140 : BitVec 32) :
    ((ptr + 0x130#64) ↦₆₄ w130) ∗ ((ptr + 0x138#64) ↦₆₄ w138) ∗ ((ptr + 0x140#64) ↦₃₂ w140) ⊢
      (∃∗ w1 : BitVec 64, (ptr + 0x130#64) ↦₆₄ w1) ∗ (∃∗ w2 : BitVec 64, (ptr + 0x138#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 32, (ptr + 0x140#64) ↦₃₂ w3) :=
  sepConj_mono (Entails.sepExists_right w130 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w138 (Entails.refl _))
      (Entails.sepExists_right w140 (Entails.refl _)))
/-! ## 6. Combined Stage 2b (`+2588..RET`) and Stage 2 (`+1956..RET`) -/
theorem SepWPp.seq {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {Qm post Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Qm Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm →
      SepWPp prog target sm Pm post Qp) :
    SepWPp prog target s P post Qp := by
  unfold SepWPp at h1 ⊢
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | hpan⟩
  · exact match h2 sm Pm hpcm hrunm hQ R hmm (hsteps.codeLoaded hL) with
    | ⟨sf, hsteps', hout⟩ => ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩
theorem memRegion344_2080_split68 (fsp : BitVec 64) :
    memRegion (fsp + 2080#64) 344 =
      memRegion (fsp + 2080#64) 68 ∗ memRegion (fsp + 2148#64) 276 :=
  ProofLib.memRegion_split' (b := fsp + 2080#64) (n := 68) (k := 276)
    (b' := fsp + 2148#64) rfl (by bv_omega) (by decide)

theorem stackAt_sessionBuild_split_pqxdhHook (fsp : BitVec 64) :
    stackAt fsp sessionBuildStack =
      memRegion (fsp - 4576#64) 480 ∗ stackAt fsp pqxdhHookStack := by
  simp only [stackAt, sessionBuildStack, pqxdhHookStack, allocHookStack]
  exact ProofLib.memRegion_split' (b := fsp - 4576#64) (n := 480) (k := 4096)
    (b' := fsp - 4096#64) rfl (by bv_omega) (by decide)

theorem ck1_2112_entails_memRegion312 (fsp : BitVec 64) {ck1_0 : Bytes}
    (hck1_len : ck1_0.length = 32) :
    ((fsp + 2112#64) ↦ₛ bytesToBv8 ck1_0) ∗ ((fsp + 2144#64) ↦₃₂ 0#32) ∗ memRegion (fsp +
      2148#64) 276 ⊢
    memRegion (fsp + 2112#64) 312 := by
  have hlen : (bytesToBv8 ck1_0).length = 32 := by simp [bytesToBv8, hck1_len]
  rw [ProofLib.memRegion_split' (b := fsp + 2112#64) (n := 32) (k := 280)
      (b' := fsp + 2144#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 2144#64) (n := 4) (k := 276)
      (b' := fsp + 2148#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (hlen ▸ pointsToBytes_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ 0#32) (Entails.refl _))

theorem memRegion72_272_3648_eq_344 (fsp : BitVec 64) :
    memRegion (fsp + 3648#64) 72 ∗ memRegion (fsp + 3720#64) 272 =
      memRegion (fsp + 3648#64) 344 :=
  (ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 72) (k := 272)
    (b' := fsp + 3720#64) rfl (by bv_omega) (by decide)).symm

theorem chainKey_index_of_rootCreateChain_ok
    {C : Crypto} {rk : RootKey} {their : PublicKey} {our : PrivateKey}
    {rk1 : RootKey} {ck1 : ChainKey}
    (h : rootCreateChain C rk their our = .ok (rk1, ck1)) :
    ck1.index = 0#32 := by
  rcases hdh : calculateAgreement C.X their our with _ | ss
  · rw [Keys.rootCreateChain_of_calculateAgreement_none C rk their our hdh] at h
    cases h
  · rw [Keys.rootCreateChain_of_calculateAgreement_some C rk their our ss hdh] at h
    injection h with hp
    injection hp with _ hck
    subst hck
    rfl

theorem pointsToBytes_chainKeyBytes_of_index_zero (a : BitVec 64) {ck : ChainKey}
    (h : ck.index = 0#32) :
    (a ↦ₛ chainKeyBytes ck) =
      (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ 0#32) := by
  rcases ck with ⟨k, idx⟩
  dsimp only at h
  subst h
  dsimp only [chainKeyBytes]
  have hlen : (keyToBytes32 k).length = 32 := by simp [keyToBytes32]
  have h0 : leBytes 4 0 = unpack32 0#32 := rfl
  rw [pointsToBytes_append, hlen, BitVec.toNat_ofNat, Nat.zero_mod, h0, ←
    pointsTo32_eq_pointsToBytes]

theorem memRegion100_352_split20 (fsp : BitVec 64) :
    memRegion (fsp + 352#64) 100 =
      memRegion (fsp + 352#64) 20 ∗ memRegion (fsp + 372#64) 80 :=
  ProofLib.memRegion_split' (b := fsp + 352#64) (n := 20) (k := 80)
    (b' := fsp + 372#64) rfl (by bv_omega) (by decide)

theorem memRegion16_20_336_eq_36 (fsp : BitVec 64) :
    memRegion (fsp + 336#64) 16 ∗ memRegion (fsp + 352#64) 20 =
      memRegion (fsp + 336#64) 36 :=
  (ProofLib.memRegion_split' (b := fsp + 336#64) (n := 16) (k := 20)
    (b' := fsp + 352#64) rfl (by bv_omega) (by decide)).symm

theorem memRegion1568_2080_split344 (fsp : BitVec 64) :
    memRegion (fsp + 2080#64) 1568 =
      memRegion (fsp + 2080#64) 344 ∗ memRegion (fsp + 2424#64) 1224 :=
  ProofLib.memRegion_split' (b := fsp + 2080#64) (n := 344) (k := 1224)
    (b' := fsp + 2424#64) rfl (by bv_omega) (by decide)

theorem memRegion1528_3720_split272 (fsp : BitVec 64) :
    memRegion (fsp + 3720#64) 1528 =
      memRegion (fsp + 3720#64) 272 ∗ memRegion (fsp + 3992#64) 1256 :=
  ProofLib.memRegion_split' (b := fsp + 3720#64) (n := 272) (k := 1256)
    (b' := fsp + 3992#64) rfl (by bv_omega) (by decide)

theorem memRegion344_1256_3648_eq_1600 (fsp : BitVec 64) :
    memRegion (fsp + 3648#64) 344 ∗ memRegion (fsp + 3992#64) 1256 =
      memRegion (fsp + 3648#64) 1600 :=
  (ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 344) (k := 1256)
    (b' := fsp + 3992#64) rfl (by bv_omega) (by decide)).symm

theorem stackAt_pqxdhEntry_split_sessionBuild (fsp : BitVec 64) :
    stackAt fsp pqxdhEntryStack =
      memRegion (fsp - 16384#64) 11808 ∗ stackAt fsp sessionBuildStack := by
  simp only [stackAt, pqxdhEntryStack, sessionBuildStack, allocHookStack]
  exact ProofLib.memRegion_split' (b := fsp - 16384#64) (n := 11808) (k := 4576)
    (b' := fsp - 4576#64) rfl (by bv_omega) (by decide)

theorem bytesToBv8_encodeEC_vecU8 (v : List.Vector (BitVec 8) 32) :
    bytesToBv8 (encodeEC (CryptoVerification.E2E.vecU8 v)) = 0x05#8 :: v.toList := by
  change BitVec.ofNat 8 TAG_EC_DJB.toNat :: bytesToBv8 (CryptoVerification.E2E.vecU8 v) =
    0x05#8 :: v.toList
  rw [ResponderCore.bytesToBv8_vecU8]
  rfl

/-! ## 7. Top-Level `initializeAliceSession_ok` and `initializeAliceSession_err` (`0x6fcd0`) -/

theorem stackAt_pqxdhEntry_split_calculateAgreement (fsp : BitVec 64) :
    stackAt fsp pqxdhEntryStack =
      memRegion (fsp - 16384#64) 12128 ∗ stackAt fsp calculateAgreementStack := by
  simp only [stackAt, pqxdhEntryStack, calculateAgreementStack, allocHookStack]
  exact ProofLib.memRegion_split' (b := fsp - 16384#64) (n := 12128) (k := 4256)
    (b' := fsp - 4256#64) rfl (by bv_omega) (by decide)

theorem ekASk_480_entails_memRegion24_8 (fsp : BitVec 64) {ekASk : Bytes}
    (hlen : ekASk.length = 32) :
    ((fsp + 480#64) ↦ₛ bytesToBv8 ekASk) ⊢
      memRegion (fsp + 480#64) 24 ∗ memRegion (fsp + 504#64) 8 := by
  have h1 : ((fsp + 480#64) ↦ₛ bytesToBv8 ekASk) ⊢ memRegion (fsp + 480#64) 32 := by
    have hbv : (bytesToBv8 ekASk).length = 32 := by simp [bytesToBv8, hlen]
    exact hbv ▸ pointsToBytes_entails_memRegion _ _
  rw [ProofLib.memRegion_split' (b := fsp + 480#64) (n := 24) (k := 8)
    (b' := fsp + 504#64) rfl (by bv_omega) (by decide)] at h1
  exact h1

theorem pqspkB_512_entails_memRegion32_32_1504 (fsp : BitVec 64) {pqspkB : Bytes}
    (hlen : pqspkB.length = 1568) :
    ((fsp + 512#64) ↦ₛ bytesToBv8 pqspkB) ⊢
      memRegion (fsp + 512#64) 32 ∗ memRegion (fsp + 544#64) 32 ∗ memRegion (fsp + 576#64) 1504 :=
        by
  have h1 : ((fsp + 512#64) ↦ₛ bytesToBv8 pqspkB) ⊢ memRegion (fsp + 512#64) 1568 := by
    have hbv : (bytesToBv8 pqspkB).length = 1568 := by simp [bytesToBv8, hlen]
    exact hbv ▸ pointsToBytes_entails_memRegion _ _
  rw [ProofLib.memRegion_split' (b := fsp + 512#64) (n := 32) (k := 1536)
        (b' := fsp + 544#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 544#64) (n := 32) (k := 1504)
        (b' := fsp + 576#64) rfl (by bv_omega) (by decide)] at h1
  exact h1

theorem kemCoins_2080_entails_memRegion1568 (fsp : BitVec 64) {kemCoins : Bytes}
    (hlen : kemCoins.length = 32) :
    ((fsp + 2080#64) ↦ₛ bytesToBv8 kemCoins) ∗ memRegion (fsp + 2112#64) 1536 ⊢
      memRegion (fsp + 2080#64) 1568 := by
  have hbv : (bytesToBv8 kemCoins).length = 32 := by simp [bytesToBv8, hlen]
  rw [memRegion1568_2080_split32 fsp]
  exact sepConj_mono_left (hbv ▸ pointsToBytes_entails_memRegion _ _)

end CryptoVerification.E2E.Pqxdh.Initiator

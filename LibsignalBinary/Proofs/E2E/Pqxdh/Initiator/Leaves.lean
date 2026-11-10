/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitiatorCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesDecode
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Seed.Defs -- shake: keep

/-!
# PQXDH Initiator Leaf Callee Specifications and Proofs

Proves `subroutine_ok` on `tripleRatchetProgAt` and `[LibsignalPlacement]` for `spqr_chain_params`,
`RawVecInner::finish_grow [local#6]`, `RawVecInner::do_reserve_and_handle [local#6]`,
`<kem::Ciphertext>::serialize`, and `<kem::Key<Public>>::serialize`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 1600000

namespace CryptoVerification.E2E.Pqxdh

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.E2E.Seed
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `spqr_chain_params` (`0x21c6c`, 5 instructions) -/

abbrev spqrChainParamsName : String := "libsignal_protocol::ratchet::spqr_chain_params"

theorem spqrChainParams_fnOff : libsignalSessionCode.fnOff spqrChainParamsName = 0x21c6c :=
  libsignalSessionCode_fnOff_0x21c6c

def spqrChainParamsSpec : Spec (BitVec 32) where
  pre := fun v s => ⌜s.readReg32 .x0 = v⌝
  post := fun v s0 sf =>
    ⌜sf.trace = s0.trace ∧
      sf.readReg64 .x0 = (if (v == 0#32) = true then 25000#64 else 4294967295#64) ∧
      sf.readReg64 .x1 = 2000#64⌝

theorem spqrChainParams_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr spqrChainParamsName)
      spqrChainParamsSpec := by
  unfold spqrChainParamsSpec
  have hfn : libsignalSessionCode.fnOff spqrChainParamsName = 0x21c6c :=
    spqrChainParams_fnOff
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.spqrChainParams b
    (Rust.withPanics (trTrapExterns C abs)) hfn 0x21c6c 20
  wp_init v s0
  examples_generalize_entry
  examples_hide_fetches
  subst h
  wp_steps
  wp_done

theorem spqrChainParams_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr spqrChainParamsName)
      spqrChainParamsSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr spqrChainParamsName]
  exact subroutine_ok_kit_of_trTrap spqrChainParams_ok_trap

/-! ## 2. `finish_grow [local#6]` (`0x763f8`) & `do_reserve_and_handle [local#6]` (`0x71f94`) -/

abbrev finishGrow6Name : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [local#9]"

abbrev doReserve6Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::" ++
  "do_reserve_and_handle::<alloc::alloc::Global> [local#8]"

def doReserve6Spec (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ newCap + 1 ≤ 2 ^ 63⌝ ∗
    vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp doReserveStack
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, vecU8At A x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
    A.pool ∗ stackAt s0.sp doReserveStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

namespace DoReserve6Aux

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre_doReserve6 (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre_doReserve6 (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre_doReserve6 (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre_doReserve6 (s : State) (pc : BitVec 64) (m : Memory)
    (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre_doReserve6 (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre_doReserve6 (s : State) (pc : BitVec 64) (m : Memory)
    (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre_doReserve6 (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre_doReserve6 (s : State) (pc : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

private theorem doReserve6_pre_repack (P1 P2 P3 P4 P5 P6 R : SepProp) :
    P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (P6 ∗ R) =
      P1 ∗ P2 ∗ P6 ∗ P3 ∗ P4 ∗ P5 ∗ R := by ac_rfl

private theorem doReserve6_post_repack (P1 P2 P6 P3 P4 P5 P7 R : SepProp) :
    (P1 ∗ P2 ∗ P6 ∗ P3 ∗ P4 ∗ P5) ∗ P7 ∗ R =
      (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5) ∗ P7 ∗ (P6 ∗ R) := by ac_rfl

private theorem adds_cs_eq_false_doReserve6 {x2 x1 : BitVec 64}
    (h : x2.toNat + x1.toNat < 2 ^ 64) :
    (x2 + x1).ult x2 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

private theorem reserve_new_cap_eq_doReserve6 {cap x1 x2 : BitVec 64} {len additional : Nat}
    (hx1 : x1.toNat = len) (hx2 : x2.toNat = additional)
    (h : reserveCap cap.toNat len additional + 1 ≤ 2 ^ 63) :
    (if (8#64).ult (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = true then
      if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1
     else 8#64) =
      BitVec.ofNat 64 (reserveCap cap.toNat len additional) := by
  have hmax : max (max (len + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := h
  have hadd : (x2 + x1).toNat = len + additional := by
    rw [BitVec.toNat_add, hx2, hx1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm1 : (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1).toNat =
      max (len + additional) (2 * cap.toNat) := by
    by_cases hc : (cap <<< 1).ult (x2 + x1) = true
    · simp only [hc, ite_true, hadd]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
    · simp only [hc, Bool.false_eq_true, ite_false, hsh]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
  apply BitVec.eq_of_toNat_eq
  dsimp only [reserveCap]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = m1 at hm1 ⊢
  by_cases hc2 : (8#64).ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change 8 < max (len + additional) (2 * cap.toNat) at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change ¬ 8 < max (len + additional) (2 * cap.toNat) at hc2
    change 8 = max (max (len + additional) (2 * cap.toNat)) 8
    omega

private theorem stackAt_doReserve6 (sp : BitVec 64) :
    stackAt sp doReserveStack =
      stackAt (sp - 64#64) finishGrowStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := LibsignalTripleRatchet.stackAt_split_cells sp 4144 8 (by decide)
  change stackAt sp doReserveStack =
    stackAt (sp - 64#64) finishGrowStack ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

private def finishGrow6ExtraStack (sp : BitVec 64) : SepProp :=
  memRegion (sp - 32#64 - 4112#64) 16

private theorem stackAt_finishGrow6 (sp : BitVec 64) :
    stackAt sp finishGrowStack =
      finishGrow6ExtraStack sp ∗ stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 := by
  have h1 := LibsignalTripleRatchet.stackAt_split_cells sp 4112 4 (by decide)
  change stackAt sp finishGrowStack = stackAt (sp - 32#64) 4112 ∗ cells (sp - 32#64) 4 at h1
  have h2 : stackAt (sp - 32#64) 4112 =
      finishGrow6ExtraStack sp ∗ stackAt (sp - 32#64) allocHookStack := by
    unfold stackAt finishGrow6ExtraStack allocHookStack
    rw [show (4112 : Nat) = 16 + 4096 by rfl,
      memRegion_split (sp - 32#64 - 4112#64) 16 4096 (by decide)]
    have haddr : sp - 32#64 - 4112#64 + 16#64 = sp - 32#64 - 4096#64 := by bv_omega
    rw [haddr]
  rw [h1, h2, sepConj_assoc]

private theorem getLsbD_63_eq_false_doReserve6 {new : BitVec 64} (h : new.toNat + 1 ≤ 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
  omega

private theorem beq_getLsbD_63_true_eq_false_doReserve6 {new : BitVec 64}
    (h : new.toNat + 1 ≤ 2 ^ 63) :
    (new.getLsbD 63 == true) = false := by
  rw [getLsbD_63_eq_false_doReserve6 h]
  rfl

private theorem ne_zero_of_pos_doReserve6 {new : BitVec 64} (h0 : 0 < new.toNat) :
    new ≠ 0#64 := by
  intro heq
  subst heq
  change 0 < 0 at h0
  omega

private theorem beq_zero_eq_false_doReserve6 {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false :=
  beq_eq_false_iff_ne.mpr (ne_zero_of_pos_doReserve6 h0)

private abbrev FG6Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def finishGrow6ZeroSpec (A : RustAlloc) : Spec FG6Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp finishGrowStack
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' new.toNat 1 ∗ memRegion p' new.toNat) ∗
      A.pool ∗ stackAt fsp finishGrowStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private def finishGrow6NeSpec (A : RustAlloc) : Spec FG6Ghost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
    A.pool ∗ stackAt fsp finishGrowStack
  post := fun (out, cap, ptr, new, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' new.toNat 1 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat - bs.length)) ∗
      A.pool ∗ stackAt fsp finishGrowStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private def doReserve6RawSpec (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp doReserveStack
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp doReserveStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

attribute [local irreducible] Program.fnOff

private theorem vecU8At_eq_doReserve6 (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

end DoReserve6Aux

open DoReserve6Aux

/-! ## 3. `<kem::Ciphertext>::serialize` (`0x1fa74`) &
  `<kem::Key<Public>>::serialize` (`0x765d4`) -/

abbrev kemCiphertextSerializeName : String :=
  "<libsignal_protocol::kem::Ciphertext>::serialize"

abbrev kemPubKeySerializeName : String :=
  "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"

theorem kemCiphertextSerialize_fnOff :
    libsignalSessionCode.fnOff kemCiphertextSerializeName = 0x1fa74 :=
  libsignalSessionCode_fnOff_0x1fa74

private theorem stackAt_kemSerialize48 (sp : BitVec 64) :
    stackAt sp tryCloneFromRefStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  LibsignalTripleRatchet.stackAt_split_cells sp 4096 6 (by decide)

private theorem memRegion_1569_split (a : BitVec 64) :
    memRegion a 1569 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
    memRegion_split a 1 1568 (by decide), memRegion_one]

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post postP : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) post postP) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) post postP := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

def kemCiphertextSerializeSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (hdrPtr, boxPtr, ctBytes) s =>
    ⌜s.readReg64 .x0 = hdrPtr ∧ ctBytes.length = 1568⌝ ∗
    (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗
    (boxPtr ↦ₛ ctBytes) ∗ A.pool ∗ stackAt s.sp tryCloneFromRefStack
  post := fun (hdrPtr, boxPtr, ctBytes) s0 sf =>
    ∃∗ tempPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧
        sf.readReg64 .x0 = tempPtr ∧
        sf.readReg64 .x1 = 1569#64 ∧
        tempPtr ≠ 0#64⌝ ∗
      (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗
      (boxPtr ↦ₛ ctBytes) ∗
      (tempPtr ↦ₛ (8#8 :: ctBytes)) ∗ A.live tempPtr 1569 1 ∗
      A.pool ∗ stackAt s0.sp tryCloneFromRefStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem kemCiphertextSerialize_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr kemCiphertextSerializeName)
      (kemCiphertextSerializeSpec A) := by
  unfold kemCiphertextSerializeSpec
  simp only [stackAt_kemSerialize48]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff kemCiphertextSerializeName = 0x1fa74 :=
    kemCiphertextSerialize_fnOff
  have hshim := noAllocShim_ok_at_trap (b := b) (C := C) (abs := abs)
    (name := kemCiphertextSerializeName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x1fa74))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_norm_trap (b := b) (C := C) hA
    (name := kemCiphertextSerializeName) (k := num% (ls_off% "__rustc::__rust_alloc" - 0x1fa74))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hmemcpy := framelessMemcpy_ok_at_trap (b := b) (C := C) (abs := abs)
    (name := kemCiphertextSerializeName) (k := num% (ls_off% "memcpy" - 0x1fa74))
    (by rw [hfn, (ls_stub% "memcpy")])
  have hpanic := panic_at_handle_error_norm_trap (b := b) (C := C) (abs := abs)
    (name := kemCiphertextSerializeName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x1fa74))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  dsimp only [noAllocShimSpec] at hshim
  dsimp only [framelessMemcpySpec] at hmemcpy
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.kemCiphertextSerialize b
    (Rust.withPanics (trTrapExterns C abs)) hfn 0x1fa74 144
  dsimp only [trTrapProgAt] at hshim halloc hmemcpy hpanic ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr kemCiphertextSerializeName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init g s0
  obtain ⟨hdrPtr, boxPtr, ctBytes⟩ := g
  dsimp only at *
  subst h_1
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 1569 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 72#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (1569, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x1fa74))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_1569_split, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    rw [← h]
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, ctBytes)
    wp_steps
    simp only [pointsToBytes_cons]
    wp_done

theorem kemCiphertextSerialize_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr kemCiphertextSerializeName)
      (kemCiphertextSerializeSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr kemCiphertextSerializeName]
  exact subroutine_ok_kit_of_trTrap (kemCiphertextSerialize_ok_trap hA)

def kemPubKeySerializeSpec (A : RustAlloc) :
    Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (boxPtr, pkBytes) s =>
    ⌜s.readReg64 .x0 = boxPtr ∧ s.readReg64 .x1 = 1568#64 ∧ pkBytes.length = 1568⌝ ∗
    (boxPtr ↦ₛ pkBytes) ∗ A.pool ∗ stackAt s.sp tryCloneFromRefStack
  post := fun (boxPtr, pkBytes) s0 sf =>
    ∃∗ tempPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧
        sf.readReg64 .x0 = tempPtr ∧
        sf.readReg64 .x1 = 1569#64 ∧
        tempPtr ≠ 0#64⌝ ∗
      (boxPtr ↦ₛ pkBytes) ∗
      (tempPtr ↦ₛ (8#8 :: pkBytes)) ∗ A.live tempPtr 1569 1 ∗
      A.pool ∗ stackAt s0.sp tryCloneFromRefStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 4. Relocatable `[LibsignalPlacement]` Contracts -/

theorem spqrChainParams_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_74).rebase (blkPl_74).base H) (blkPl_74).base spqrChainParamsSpec := by
  unfold spqrChainParamsSpec; wp_init v s0; subst h; wp_steps; wp_done

theorem kemCiphertextSerialize_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_71).rebase (blkPl_71).base H) (blkPl_71).base
      (kemCiphertextSerializeSpec A) := by
  unfold kemCiphertextSerializeSpec; simp only [stackAt_kemSerialize48]; cells_unfold
  have hshim' : subroutine_ok ((blkPC_71).rebase (blkPl_71).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec := ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok ((blkPC_71).rebase (blkPl_71).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_of_mem halloc
  have hmemcpy' : subroutine_ok ((blkPC_71).rebase (blkPl_71).base H)
      (lsρ lsMemcpySym) framelessMemcpySpec := ls_hook_ok_of_mem hmemcpy
  have hpanic' : ((blkPC_71).rebase (blkPl_71).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  dsimp only [noAllocShimSpec] at hshim'; dsimp only [framelessMemcpySpec] at hmemcpy'
  wpp_init g s0; obtain ⟨hdrPtr, boxPtr, ctBytes⟩ := g; dsimp only at *; subst h_1
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; have hlay : LayoutOk 1569 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_71).base + 72#64)
  wp_steps; wp_call hshim' (); wp_steps; wp_call halloc' (1569, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]; refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym); wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using allowPanic_panicked
      (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_1569_split, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret; wp_steps; rw [← h]
    wp_call hmemcpy' (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, ctBytes)
    wp_steps; simp only [pointsToBytes_cons]; wp_done

end CryptoVerification.E2E.Pqxdh

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.FetchPlaced
import ProofLib.SepLogic.WPp

/-!
# Relocatable `Epoch::encoded_len` Verification (Blocks `478` and `399`)

Proves `[LibsignalPlacement]` `subroutine_ok` contracts for CLI Blocks `478` (`[local#3]`) and `399`
(`[local#2]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.Cli.SpqrV1.ProtoRepr.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.ProtoRepr.zeroExtend64_beq_zero32
  CryptoVerification.SpqrV1.ProtoRepr.ofNat_countLeadingZeros_64
  CryptoVerification.SpqrV1.ProtoRepr.ofNat_countLeadingZeros_32
  CryptoVerification.SpqrV1.ProtoRepr.truncate32_ofNat64
  CryptoVerification.SpqrV1.ProtoRepr.hwVarintLen_eq_ofNat_varintLen_norm
  CryptoVerification.SpqrV1.ProtoRepr.hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  CryptoVerification.SpqrV1.ProtoRepr.noneCap_add_one_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.noneCap_add_one_bne_zero
  CryptoVerification.SpqrV1.ProtoRepr.zext64_truncate32
  CryptoVerification.SpqrV1.ProtoRepr.ule_zero_64
  CryptoVerification.SpqrV1.ProtoRepr.ult_zero_64

def EpochEncodedLenLocal1PinnedPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 H) (blkPl_478).base (epochEncodedLenPinnedSpec A)

def EpochEncodedLenLocal1PlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 H) (blkPl_478).base (epochEncodedLenSpec A)

def EpochEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 (Rust.withPanics ext)) (blkPl_478).base (epochEncodedLenPinnedSpec A)

def EpochEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 (Rust.withPanics ext)) (blkPl_478).base (epochEncodedLenSpec A)

def EpochEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_478).base
    (epochEncodedLenPinnedSpec A)

def EpochEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_478 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_478).base
    (epochEncodedLenSpec A)

/-- Entry address predicate for placed Block `478` (`Epoch::encoded_len [local#3]`). -/
def IsEpochEncLenPlacedEntry (prog : Program) (entry : BitVec 64) : Prop :=
  ∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    prog = @lsProg_478 inst H ∧ entry = (@blkPl_478 inst).base

theorem epochEncLenPlaced_fetch_entry {prog : Program} {entry : BitVec 64}
    (hfn : IsEpochEncLenPlacedEntry prog entry) {ins : Instr}
    (h1 : ∀ [LibsignalPlacement] H,
      ((blkPC_478).rebase (blkPl_478).base H).fetch ((blkPl_478).base + 0#64) = some ins) :
    prog.fetch entry = some ins := by
  rcases hfn with ⟨inst, H, rfl, rfl⟩
  simpa using @h1 inst H

theorem epochEncLenPlaced_fetch_add {prog : Program} {entry : BitVec 64}
    (hfn : IsEpochEncLenPlacedEntry prog entry) {k : Nat} {ins : Instr}
    (h1 : ∀ [LibsignalPlacement] H,
      ((blkPC_478).rebase (blkPl_478).base H).fetch ((blkPl_478).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨inst, H, rfl, rfl⟩
  exact @h1 inst H

open Lean Elab Tactic in
/-- Fetch instructions in `[kStart, kEnd)` (byte offsets from function entry `entry`) when
    `hfn : IsEpochEncLenPlacedEntry prog entry`. -/
elab "epoch_fetches_range_478 " hfn:ident kStart:num kEnd:num : tactic => do
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let hexK := String.ofList (Nat.toDigits 16 k)
    let blk1 := mkIdent (`CryptoVerification.Cli.SpqrV1.ProtoRepr.Placed |>.str
      s!"blkPC_478_rebase_fetch_0x{hexK}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := epochEncLenPlaced_fetch_entry $hfn
          (fun [LibsignalPlacement] H => $blk1 _ H)))
    else
      evalTactic (← `(tactic|
        have := epochEncLenPlaced_fetch_add $hfn (k := $kq)
          (fun [LibsignalPlacement] H => $blk1 _ H)))

/-! ## Step Lemmas for `send` (`a + 0x00`) -/

private theorem step_epoch_send_none_placed (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsEpochEncLenPlacedEntry prog entry)
    (g : ChainEpochPBGhost) (a sp v16 v8 : BitVec 64) (ep : ChainEpochPB)
    (hsend : ep.send = none)
    (hrecv_b : OptEpochDirBounds g.recv ep.recv)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (epochUnpacked A g a ep ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ep.recv.isSome then entry + 192#64 else entry + 384#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send) →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm
        ((epochUnpacked A g a ep ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range_478 hfn 0 20
  epoch_fetches_range_478 hfn 368 384
  have hrecv_beq := hrecv_b.1
  have hrecv_bne := hrecv_b.2.1
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ noneCap) ∗ optEpochDirPayload A g.send a none ∗
      ((a + 56#64) ↦₆₄ optEpochDirCap g.recv ep.recv) ∗
      optEpochDirPayload A g.recv (a + 56#64) ep.recv := by
    simp only [epochUnpacked, hsend, optEpochDirCap]
  rw [hP1]
  apply SepWPp.of_sepWP (mid := if ep.recv.isSome then entry + 192#64 else entry + 384#64)
  wp_steps
  apply SepWP.done (by cases ep.recv <;> simp_all) (by simp_all)
  rw [← hP1]
  exact hnext _ (by cases ep.recv <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all [optEpochDirectionPBFieldEncodedLen])
    (by simp_all [EpochEncLenCalleeSaved])

private theorem step_epoch_send_some_a_placed (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsEpochEncLenPlacedEntry prog entry)
    (g : ChainEpochPBGhost) (a sp v16 v8 : BitVec 64) (ep : ChainEpochPB) (ds : EpochDirectionPB)
    (hsend : ep.send = some ds)
    (hsend_b : OptEpochDirBounds g.send ep.send)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (epochUnpacked A g a ep ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ds.next.isEmpty then entry + 416#64 else entry + 64#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u32VarintFieldEncodedLen ds.ctr) →
      sm.readReg64 .x9 = BitVec.ofNat 64 ds.next.length →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm
        ((epochUnpacked A g a ep ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range_478 hfn 0 64
  epoch_fetches_range_478 hfn 404 416
  have hcap_beq : (g.send.next.cap + 1#64 == 0#64) = false := by
    have h := hsend_b.1
    rwa [hsend, Option.isSome_some, Bool.not_true, optEpochDirCap] at h
  obtain ⟨_, _, hnext_beq, hnext_bne, _, _⟩ := hsend_b.2.2 ds hsend
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ g.send.next.cap) ∗ ((a + 8#64) ↦₆₄ g.send.next.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ds.next.length) ∗
      vecU8Buf A g.send.next.cap g.send.next.ptr ds.next ∗
      ((a + 24#64) ↦₆₄ g.send.prev.cap) ∗ ((a + 32#64) ↦₆₄ g.send.prev.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 ds.prev.length) ∗
      vecU8Buf A g.send.prev.cap g.send.prev.ptr ds.prev ∗
      ((a + 48#64) ↦₃₂ ds.ctr) ∗ memRegion (a + 52#64) 4 ∗
      ((a + 56#64) ↦₆₄ optEpochDirCap g.recv ep.recv) ∗
      optEpochDirPayload A g.recv (a + 56#64) ep.recv := by
    simp only [epochUnpacked, hsend, optEpochDirCap, optEpochDirPayload, sepConj_assoc]
  rw [hP1]
  by_cases hctr : ds.ctr = 0#32
  · apply SepWPp.of_sepWP (mid := if ds.next.isEmpty then entry + 416#64 else entry + 64#64)
    wp_steps
    apply SepWP.done (by cases ds.next.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases ds.next.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u32VarintFieldEncodedLen])
      (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  · have hctr_beq : (ds.ctr == 0#32) = false := beq_eq_false_iff_ne.mpr hctr
    have henc := bv_u32VarintField_nonzero hctr
    apply SepWPp.of_sepWP (mid := if ds.next.isEmpty then entry + 416#64 else entry + 64#64)
    wp_steps
    apply SepWP.done (by cases ds.next.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases ds.next.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

private theorem step_epoch_send_some_b_placed (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsEpochEncLenPlacedEntry prog entry)
    (g : ChainEpochPBGhost) (a : BitVec 64) (ep : ChainEpochPB) (ds : EpochDirectionPB) (s1 : Nat)
    (hsend : ep.send = some ds)
    (hsend_b : OptEpochDirBounds g.send ep.send)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if ds.next.isEmpty then entry + 416#64 else entry + 64#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 ds.next.length)
    (hP : P = epochUnpacked A g a ep ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ds.prev.isEmpty then entry + 132#64 else entry + 104#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + bytesFieldEncodedLen ds.next) →
      sm.readReg64 .x9 = BitVec.ofNat 64 ds.prev.length →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range_478 hfn 64 104
  epoch_fetches_range_478 hfn 416 432
  obtain ⟨_, _, _, _, hprev_beq, hprev_bne⟩ := hsend_b.2.2 ds hsend
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ g.send.next.cap) ∗ ((a + 8#64) ↦₆₄ g.send.next.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ds.next.length) ∗
      vecU8Buf A g.send.next.cap g.send.next.ptr ds.next ∗
      ((a + 24#64) ↦₆₄ g.send.prev.cap) ∗ ((a + 32#64) ↦₆₄ g.send.prev.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 ds.prev.length) ∗
      vecU8Buf A g.send.prev.cap g.send.prev.ptr ds.prev ∗
      ((a + 48#64) ↦₃₂ ds.ctr) ∗ memRegion (a + 52#64) 4 ∗
      ((a + 56#64) ↦₆₄ optEpochDirCap g.recv ep.recv) ∗
      optEpochDirPayload A g.recv (a + 56#64) ep.recv := by
    simp only [epochUnpacked, hsend, optEpochDirCap, optEpochDirPayload, sepConj_assoc]
  rw [hP1]
  cases hne : ds.next.isEmpty with
  | true =>
    simp only [hne, ↓reduceIte] at hpc
    cases hpe : ds.prev.isEmpty with
    | true =>
      apply SepWPp.of_sepWP (mid := if ds.prev.isEmpty then entry + 132#64 else entry + 104#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [bytesFieldEncodedLen])
        (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      apply SepWPp.of_sepWP (mid := if ds.prev.isEmpty then entry + 132#64 else entry + 104#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [bytesFieldEncodedLen])
        (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpc
    have henc := bv_bytesField_nonempty hne
    have hadd := bv_add_ofNat_comm s1 (bytesFieldEncodedLen ds.next)
    apply SepWPp.of_sepWP (mid := if ds.prev.isEmpty then entry + 132#64 else entry + 104#64)
    wp_steps
    apply SepWP.done (by cases ds.prev.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases ds.prev.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

private theorem step_epoch_send_some_c_placed (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsEpochEncLenPlacedEntry prog entry)
    (g : ChainEpochPBGhost) (a : BitVec 64) (ep : ChainEpochPB) (ds : EpochDirectionPB)
    (hsend : ep.send = some ds)
    (hrecv_b : OptEpochDirBounds g.recv ep.recv)
    (hfit : optEpochDirectionPBFieldEncodedLen (some ds) < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if ds.prev.isEmpty then entry + 132#64 else entry + 104#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 =
      BitVec.ofNat 64 (u32VarintFieldEncodedLen ds.ctr + bytesFieldEncodedLen ds.next))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 ds.prev.length)
    (hP : P = epochUnpacked A g a ep ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ep.recv.isSome then entry + 192#64 else entry + 384#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send) →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range_478 hfn 104 192
  have hrecv_beq := hrecv_b.1
  have hbody_lt : epochDirectionPBEncodedLen ds < 2 ^ 64 := by
    dsimp [optEpochDirectionPBFieldEncodedLen] at hfit
    omega
  have htot := bv_optEpochDirField_some ds
  have hcmp := cmp_ls_false_of_lt
    (vlen := varintLen (BitVec.ofNat 64 (epochDirectionPBEncodedLen ds)))
    (tot := optEpochDirectionPBFieldEncodedLen (some ds))
    (by dsimp [optEpochDirectionPBFieldEncodedLen]; omega) hfit
  rcases hcmp with ⟨hcmp1, hcmp2, hcmp3, hcmp4, hcmp5⟩
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ optEpochDirCap g.send ep.send) ∗ optEpochDirPayload A g.send a ep.send ∗
      ((a + 56#64) ↦₆₄ optEpochDirCap g.recv ep.recv) ∗
      optEpochDirPayload A g.recv (a + 56#64) ep.recv := rfl
  rw [hP1]
  cases hpe : ds.prev.isEmpty with
  | true =>
    simp only [hpe, ↓reduceIte] at hpc
    have hprev_len : ds.prev.length = 0 := List.isEmpty_iff.mp hpe |> congrArg List.length
    have hbody_true : u32VarintFieldEncodedLen ds.ctr + bytesFieldEncodedLen ds.next =
        epochDirectionPBEncodedLen ds := by
      dsimp [epochDirectionPBEncodedLen, bytesFieldEncodedLen]
      simp [hpe]
    rw [hprev_len] at hx9
    rw [hbody_true] at hx8
    apply SepWPp.of_sepWP (mid := if ep.recv.isSome then entry + 192#64 else entry + 384#64)
    wp_steps
    apply SepWP.done (by cases ep.recv <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases ep.recv <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    simp only [hpe, Bool.false_eq_true, ↓reduceIte] at hpc
    have henc := bv_bytesField_nonempty hpe
    obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen ds.prev)
        (b := u32VarintFieldEncodedLen ds.ctr + bytesFieldEncodedLen ds.next)
        (c := epochDirectionPBEncodedLen ds) rfl hbody_lt
    apply SepWPp.of_sepWP (mid := if ep.recv.isSome then entry + 192#64 else entry + 384#64)
    wp_steps
    apply SepWP.done (by cases ep.recv <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases ep.recv <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

/-! ## Step Lemmas for `recv` (`a + 0x38`) -/

private theorem step_epoch_recv_none_placed (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsEpochEncLenPlacedEntry prog entry)
    (g : ChainEpochPBGhost) (a sp : BitVec 64) (ep : ChainEpochPB)
    (hrecv : ep.recv = none)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (_hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (epochUnpacked A g a ep ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  epoch_fetches_range_478 hfn 360 368
  epoch_fetches_range_478 hfn 384 392
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all [chainEpochPBEncodedLen, optEpochDirectionPBFieldEncodedLen])
    (by epochEncLen_cc_close)

private theorem step_epoch_recv_some_a_placed (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsEpochEncLenPlacedEntry prog entry)
    (g : ChainEpochPBGhost) (a : BitVec 64) (ep : ChainEpochPB) (dr : EpochDirectionPB)
    (hrecv : ep.recv = some dr)
    (hrecv_b : OptEpochDirBounds g.recv ep.recv)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 192#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send))
    (hP : P = epochUnpacked A g a ep ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if dr.next.isEmpty then entry + 444#64 else entry + 236#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send) →
      sm.readReg64 .x9 = BitVec.ofNat 64 (u32VarintFieldEncodedLen dr.ctr) →
      sm.readReg64 .x10 = BitVec.ofNat 64 dr.next.length →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range_478 hfn 192 236
  epoch_fetches_range_478 hfn 432 444
  obtain ⟨_, _, hnext_beq, hnext_bne, _, _⟩ := hrecv_b.2.2 dr hrecv
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ optEpochDirCap g.send ep.send) ∗ optEpochDirPayload A g.send a ep.send ∗
      ((a + 56#64) ↦₆₄ g.recv.next.cap) ∗ ((a + 64#64) ↦₆₄ g.recv.next.ptr) ∗
      ((a + 72#64) ↦₆₄ BitVec.ofNat 64 dr.next.length) ∗
      vecU8Buf A g.recv.next.cap g.recv.next.ptr dr.next ∗
      ((a + 80#64) ↦₆₄ g.recv.prev.cap) ∗ ((a + 88#64) ↦₆₄ g.recv.prev.ptr) ∗
      ((a + 96#64) ↦₆₄ BitVec.ofNat 64 dr.prev.length) ∗
      vecU8Buf A g.recv.prev.cap g.recv.prev.ptr dr.prev ∗
      ((a + 104#64) ↦₃₂ dr.ctr) ∗ memRegion (a + 108#64) 4 := by
    simp only [epochUnpacked, hrecv, optEpochDirCap, optEpochDirPayload, arm64_norm]
  rw [hP1]
  by_cases hctr : dr.ctr = 0#32
  · apply SepWPp.of_sepWP (mid := if dr.next.isEmpty then entry + 444#64 else entry + 236#64)
    wp_steps
    apply SepWP.done (by cases dr.next.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases dr.next.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [u32VarintFieldEncodedLen]) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])
  · have hctr_beq : (dr.ctr == 0#32) = false := beq_eq_false_iff_ne.mpr hctr
    have henc := bv_u32VarintField_nonzero hctr
    apply SepWPp.of_sepWP (mid := if dr.next.isEmpty then entry + 444#64 else entry + 236#64)
    wp_steps
    apply SepWP.done (by cases dr.next.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases dr.next.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

private theorem step_epoch_recv_some_b_placed (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsEpochEncLenPlacedEntry prog entry)
    (g : ChainEpochPBGhost) (a : BitVec 64) (ep : ChainEpochPB) (dr : EpochDirectionPB) (r1 : Nat)
    (hrecv : ep.recv = some dr)
    (hrecv_b : OptEpochDirBounds g.recv ep.recv)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if dr.next.isEmpty then entry + 444#64 else entry + 236#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 r1)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 dr.next.length)
    (hP : P = epochUnpacked A g a ep ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if dr.prev.isEmpty then entry + 304#64 else entry + 276#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send) →
      sm.readReg64 .x9 = BitVec.ofNat 64 (r1 + bytesFieldEncodedLen dr.next) →
      sm.readReg64 .x10 = BitVec.ofNat 64 dr.prev.length →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  epoch_fetches_range_478 hfn 236 276
  epoch_fetches_range_478 hfn 444 460
  obtain ⟨_, _, _, _, hprev_beq, hprev_bne⟩ := hrecv_b.2.2 dr hrecv
  subst hP
  have hP1 : epochUnpacked A g a ep =
      (a ↦₆₄ optEpochDirCap g.send ep.send) ∗ optEpochDirPayload A g.send a ep.send ∗
      ((a + 56#64) ↦₆₄ g.recv.next.cap) ∗ ((a + 64#64) ↦₆₄ g.recv.next.ptr) ∗
      ((a + 72#64) ↦₆₄ BitVec.ofNat 64 dr.next.length) ∗
      vecU8Buf A g.recv.next.cap g.recv.next.ptr dr.next ∗
      ((a + 80#64) ↦₆₄ g.recv.prev.cap) ∗ ((a + 88#64) ↦₆₄ g.recv.prev.ptr) ∗
      ((a + 96#64) ↦₆₄ BitVec.ofNat 64 dr.prev.length) ∗
      vecU8Buf A g.recv.prev.cap g.recv.prev.ptr dr.prev ∗
      ((a + 104#64) ↦₃₂ dr.ctr) ∗ memRegion (a + 108#64) 4 := by
    simp only [epochUnpacked, hrecv, optEpochDirCap, optEpochDirPayload, arm64_norm]
  rw [hP1]
  cases hne : dr.next.isEmpty with
  | true =>
    simp only [hne, ↓reduceIte] at hpc
    cases hpe : dr.prev.isEmpty with
    | true =>
      apply SepWPp.of_sepWP (mid := if dr.prev.isEmpty then entry + 304#64 else entry + 276#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [bytesFieldEncodedLen]) (by simp_all)
        (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      apply SepWPp.of_sepWP (mid := if dr.prev.isEmpty then entry + 304#64 else entry + 276#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [bytesFieldEncodedLen]) (by simp_all)
        (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpc
    have henc := bv_bytesField_nonempty hne
    have hadd := bv_add_ofNat_comm r1 (bytesFieldEncodedLen dr.next)
    apply SepWPp.of_sepWP (mid := if dr.prev.isEmpty then entry + 304#64 else entry + 276#64)
    wp_steps
    apply SepWP.done (by cases dr.prev.isEmpty <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases dr.prev.isEmpty <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

private theorem step_epoch_recv_some_c_placed (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsEpochEncLenPlacedEntry prog entry)
    (g : ChainEpochPBGhost) (a sp : BitVec 64) (ep : ChainEpochPB) (dr : EpochDirectionPB)
    (hrecv : ep.recv = some dr)
    (hfit : chainEpochPBEncodedLen ep < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if dr.prev.isEmpty then entry + 304#64 else entry + 276#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (_hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send))
    (hx9 : s.readReg64 .x9 =
      BitVec.ofNat 64 (u32VarintFieldEncodedLen dr.ctr + bytesFieldEncodedLen dr.next))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 dr.prev.length)
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (epochUnpacked A g a ep ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  epoch_fetches_range_478 hfn 276 368
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  have hrecv_fit : optEpochDirectionPBFieldEncodedLen (some dr) < 2 ^ 64 := by
    unfold chainEpochPBEncodedLen at hfit
    rw [hrecv] at hfit
    omega
  have hbody_lt : epochDirectionPBEncodedLen dr < 2 ^ 64 := by
    dsimp [optEpochDirectionPBFieldEncodedLen] at hrecv_fit
    omega
  have htot := bv_optEpochDirField_some dr
  have hcmp := cmp_ls_false_of_lt
    (vlen := varintLen (BitVec.ofNat 64 (epochDirectionPBEncodedLen dr)))
    (tot := optEpochDirectionPBFieldEncodedLen (some dr))
    (by dsimp [optEpochDirectionPBFieldEncodedLen]; omega) hrecv_fit
  rcases hcmp with ⟨hcmp1, hcmp2, hcmp3, hcmp4, hcmp5⟩
  have hfinal_eq :
      optEpochDirectionPBFieldEncodedLen ep.send +
        optEpochDirectionPBFieldEncodedLen (some dr) =
      chainEpochPBEncodedLen ep := by
    unfold chainEpochPBEncodedLen
    rw [hrecv]
  obtain ⟨hadd_final, hccf1, hccf2, hccf3, hccf4⟩ :=
    adds_no_overflow_of_eq (a := optEpochDirectionPBFieldEncodedLen (some dr))
      (b := optEpochDirectionPBFieldEncodedLen ep.send)
      (c := chainEpochPBEncodedLen ep) hfinal_eq hfit
  subst hP
  cases hpe : dr.prev.isEmpty with
  | true =>
    simp only [hpe, ↓reduceIte] at hpc
    have hprev_len : dr.prev.length = 0 := List.isEmpty_iff.mp hpe |> congrArg List.length
    have hbody_true : u32VarintFieldEncodedLen dr.ctr + bytesFieldEncodedLen dr.next =
        epochDirectionPBEncodedLen dr := by
      dsimp [epochDirectionPBEncodedLen, bytesFieldEncodedLen]
      simp [hpe]
    rw [hprev_len] at hx10
    rw [hbody_true] at hx9
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)
  | false =>
    simp only [hpe, Bool.false_eq_true, ↓reduceIte] at hpc
    have henc := bv_bytesField_nonempty hpe
    obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen dr.prev)
        (b := u32VarintFieldEncodedLen dr.ctr + bytesFieldEncodedLen dr.next)
        (c := epochDirectionPBEncodedLen dr) rfl hbody_lt
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)

/-! ## Combined `send` and `recv` Phases and Top-Level Theorems -/

private theorem step_epoch_send_placed (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsEpochEncLenPlacedEntry prog entry)
    (g : ChainEpochPBGhost) (a sp v16 v8 : BitVec 64) (ep : ChainEpochPB)
    (hsend_b : OptEpochDirBounds g.send ep.send)
    (hrecv_b : OptEpochDirBounds g.recv ep.recv)
    (hfit : chainEpochPBEncodedLen ep < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (epochUnpacked A g a ep ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if ep.recv.isSome then entry + 192#64 else entry + 384#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optEpochDirectionPBFieldEncodedLen ep.send) →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm
        ((epochUnpacked A g a ep ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  cases hsend : ep.send with
  | none =>
    exact step_epoch_send_none_placed prog A entry hfn g a sp v16 v8 ep hsend hrecv_b
      hpc hrun hsp halign hx0 hP hnext
  | some ds =>
    have hsend_fit : optEpochDirectionPBFieldEncodedLen (some ds) < 2 ^ 64 := by
      unfold chainEpochPBEncodedLen at hfit
      rw [hsend] at hfit
      omega
    refine step_epoch_send_some_a_placed prog A entry hfn g a sp v16 v8 ep ds hsend hsend_b
      hpc hrun hsp halign hx0 hP ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1
    let FSave : SepProp :=
      ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr) ∗ F
    have hP_save :
        (epochUnpacked A g a ep ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F =
        epochUnpacked A g a ep ∗ FSave := by
      dsimp [FSave]; ac_rfl
    refine step_epoch_send_some_b_placed (F := FSave) prog A entry hfn g a ep ds
      (u32VarintFieldEncodedLen ds.ctr) hsend hsend_b
      hpc1 hrun1 hx0_1 hx8_1 hx9_1 hP_save ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hx9_2 hcs2
    refine step_epoch_send_some_c_placed (F := FSave) prog A entry hfn g a ep ds
      hsend hrecv_b hsend_fit
      hpc2 hrun2 hx0_2 hx8_2 hx9_2 hP_save ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    exact hnext s3 hpc3 hrun3 (by rw [hsp3, hsp2, hsp1]) (by rw [htr3, htr2, htr1])
      hx0_3 hx8_3 (hcs1.trans (hcs2.trans hcs3))

theorem epochEncodedLen_entry_pinned_placed_ok (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsEpochEncLenPlacedEntry prog entry) :
    subroutine_ok prog entry (epochEncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, ep⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [epochEncodedLenPinnedSpec, chainEpochPBPinnedAt_eq_unpacked,
    stackAt_epochEncodedLen_eq, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  unfold EpochEncodedLenFits at hfit
  have hmem0 : s0.mem ⊨
      (epochUnpacked A g a ep ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre using 1; ac_rfl
  obtain ⟨hsend_b, hrecv_b⟩ := epochUnpacked_bounds hpre
  refine ⟨(epochUnpacked A g a ep ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rwa [sepConj_emp], ?_⟩
  refine step_epoch_send_placed (F := R) prog A entry hfn g a s0.sp v16 v8 ep
    hsend_b hrecv_b hfit hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  cases hrecv : ep.recv with
  | none =>
    simp only [hrecv, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine step_epoch_recv_none_placed (F := R) prog A entry hfn g a s0.sp ep hrecv
      hpc1 hrun1 hsp1 halign hx0_1 hx8_1 hcs1 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [epochEncodedLenPinnedSpec, chainEpochPBPinnedAt_eq_unpacked,
      stackAt_epochEncodedLen_eq, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  | some dr =>
    simp only [hrecv, Option.isSome_some, ↓reduceIte] at hpc1
    let FSave : SepProp :=
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
    have hP_save :
        (epochUnpacked A g a ep ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ R =
        epochUnpacked A g a ep ∗ FSave := by
      dsimp [FSave]; ac_rfl
    refine step_epoch_recv_some_a_placed (F := FSave) prog A entry hfn g a ep dr hrecv hrecv_b
      hpc1 hrun1 hx0_1 hx8_1 hP_save ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hx9_2 hx10_2 hcs2
    refine step_epoch_recv_some_b_placed (F := FSave) prog A entry hfn g a ep dr
      (u32VarintFieldEncodedLen dr.ctr) hrecv hrecv_b
      hpc2 hrun2 hx0_2 hx8_2 hx9_2 hx10_2 hP_save ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hx9_3 hx10_3 hcs3
    have hsp3' : s3.sp = s0.sp - 16#64 := by rw [hsp3, hsp2, hsp1]
    have hcs3' : EpochEncLenCalleeSaved s0 s3 := hcs1.trans (hcs2.trans hcs3)
    refine step_epoch_recv_some_c_placed (F := R) prog A entry hfn g a s0.sp ep dr
      hrecv hfit hpc3 hrun3 hsp3' halign hx0_3 hx8_3 hx9_3 hx10_3 hcs3' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [epochEncodedLenPinnedSpec, chainEpochPBPinnedAt_eq_unpacked,
      stackAt_epochEncodedLen_eq, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr3, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

/-! ### Block `478` (`[local#3]`) and Block `399` (`[local#2]`) Placed Corollaries -/

theorem epochEncodedLen_local1_pinned_placed_ok_x [inst : LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : EpochEncodedLenLocal1PinnedPlacedOkX A H :=
  epochEncodedLen_entry_pinned_placed_ok _ A _ ⟨inst, H, rfl, rfl⟩

theorem epochEncodedLen_local1_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : EpochEncodedLenLocal1PlacedOkX A H :=
  epochEncodedLen_ok_of_pinned (epochEncodedLen_local1_pinned_placed_ok_x A H)

theorem epochEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal1PinnedPlacedOkExt A ext :=
  epochEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem epochEncodedLen_local1_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal1PlacedOkExt A ext :=
  epochEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem epochEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  epochEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem epochEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal1PlacedOk C A ctl abs :=
  epochEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem epochEncodedLen_local2_pinned_placed_ok_x [inst : LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_399).rebase (blkPl_399).base H) (blkPl_399).base
      (epochEncodedLenPinnedSpec A) :=
  epochEncodedLen_entry_pinned_ok _ A _ (Or.inr ⟨inst, H, Or.inr ⟨rfl, rfl⟩⟩)

theorem epochEncodedLen_local2_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_399).rebase (blkPl_399).base H) (blkPl_399).base
      (epochEncodedLenSpec A) :=
  epochEncodedLen_ok_of_pinned (epochEncodedLen_local2_pinned_placed_ok_x A H)

theorem epochEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal2PinnedPlacedOkExt A ext :=
  CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLen_local2_pinned_placed_ok_ext A ext

theorem epochEncodedLen_local2_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : EpochEncodedLenLocal2PlacedOkExt A ext :=
  CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLen_local2_placed_ok_ext A ext

theorem epochEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLen_local2_pinned_placed_ok C A ctl abs

theorem epochEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    EpochEncodedLenLocal2PlacedOk C A ctl abs :=
  CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLen_local2_placed_ok C A ctl abs

end CryptoVerification.Cli.SpqrV1.ProtoRepr

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchPlaced
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import ProofLib.SepLogic.WPp

/-!
# Relocatable 82- and 93-Instruction Unchunked `encoded_len` Leaf Proofs

Proves `[LibsignalPlacement]` `subroutine_ok` contracts for the 82-instruction group (CLI Blocks
`492`, `499`) and 93-instruction group (CLI Blocks `487`, `469`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open EncodedLen
open CryptoVerification.Cli.SpqrV1.ProtoRepr
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

private theorem subroutine_ok_repack {G1 G2 : Type} {prog : Program} {fnBase : BitVec 64}
    {S1 : Spec G1} {S2 : Spec G2} (f : G2 → G1)
    (hpre : ∀ x s, S2.pre x s = S1.pre (f x) s)
    (hpost : ∀ x s0 sf, S2.post x s0 sf = S1.post (f x) s0 sf)
    (hok : subroutine_ok prog fnBase S1)
    (honPanic : ∀ x s0 sf, S2.onPanic x s0 sf = S1.onPanic (f x) s0 sf := by intros; rfl)
    (honExit : ∀ x c s0 sf, S2.onExit x c s0 sf = S1.onExit (f x) c s0 sf := by intros; rfl)
    (honOom : ∀ x s0 sf, S2.onOom x s0 sf = S1.onOom (f x) s0 sf := by intros; rfl) :
    subroutine_ok prog fnBase S2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hsp => ?_
  rw [hpre] at hpre0
  refine hok.mono_outcome (f x) R s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨hpan, hmpan⟩ | ⟨code, hex, hmex⟩ | ⟨hoom, hmoom⟩
  · rw [← hpost] at hpost0
    exact Or.inl ⟨hret, hcc, hpost0⟩
  · rw [← honPanic] at hmpan
    exact Or.inr (Or.inl ⟨hpan, hmpan⟩)
  · rw [← honExit] at hmex
    exact Or.inr (Or.inr (Or.inl ⟨code, hex, hmex⟩))
  · rw [← honOom] at hmoom
    exact Or.inr (Or.inr (Or.inr ⟨hoom, hmoom⟩))

/-! ## Part 1: 82-Instruction Group (`492` `HeaderSent`, `499` `EkSentCt1Received`) -/

private def IsUnchunked82PlacedEntry [LibsignalPlacement] (H : String → Option (State → State))
    (prog : Program) (fnBase : BitVec 64) : Prop :=
  (prog = lsProg_492 H ∧ fnBase = (blkPl_492).base) ∨
  (prog = lsProg_499 H ∧ fnBase = (blkPl_499).base)

private theorem unchunked82_placed_fetch_entry [LibsignalPlacement]
    {H : String → Option (State → State)} {prog : Program} {fnBase : BitVec 64} {ins : Instr}
    (hfn : IsUnchunked82PlacedEntry H prog fnBase)
    (h0 : ((blkPC_492).rebase (blkPl_492).base H).fetch ((blkPl_492).base + 0#64) = some ins)
    (h1 : ((blkPC_499).rebase (blkPl_499).base H).fetch ((blkPl_499).base + 0#64) = some ins) :
    prog.fetch fnBase = some ins := by
  rcases hfn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa only [BitVec.add_zero] using h0
  · simpa only [BitVec.add_zero] using h1

private theorem unchunked82_placed_fetch_add [LibsignalPlacement]
    {H : String → Option (State → State)} {prog : Program} {fnBase : BitVec 64}
    (k : Nat) {ins : Instr}
    (hfn : IsUnchunked82PlacedEntry H prog fnBase)
    (h0 : ((blkPC_492).rebase (blkPl_492).base H).fetch ((blkPl_492).base + BitVec.ofNat 64 k) = some ins)
    (h1 : ((blkPC_499).rebase (blkPl_499).base H).fetch ((blkPl_499).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (fnBase + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h0
  · exact h1

open Lean Elab Tactic in
local elab "unchunked82_placed_fetches_range " H:term:max hfn:ident kStart:num kEnd:num : tactic => do
  let kS := kStart.getNat
  let kE := kEnd.getNat
  let ns := `CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.Placed
  let b0 := mkIdent (ns |>.str "blkPl_492")
  let b1 := mkIdent (ns |>.str "blkPl_499")
  let fe := mkIdent ``unchunked82_placed_fetch_entry
  let fa := mkIdent ``unchunked82_placed_fetch_add
  for i in [kS / 4 : kE / 4] do
    let k := 4 * i
    let hexK := String.ofList (Nat.toDigits 16 k)
    let l0 := mkIdent (ns |>.str s!"blkPC_492_rebase_fetch_0x{hexK}")
    let l1 := mkIdent (ns |>.str s!"blkPC_499_rebase_fetch_0x{hexK}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fe $hfn
          ($l0 ($b0).base $H) ($l1 ($b1).base $H)))
    else
      evalTactic (← `(tactic|
        have := $fa $kq $hfn
          ($l0 ($b0).base $H) ($l1 ($b1).base $H)))

private theorem step_unchunked82_epoch_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked82PlacedEntry H prog fnBase)
    (g : Unchunked4PBGhost) (a sp v16 v8 : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hauth_b : OptAuthBounds g.auth auth)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = fnBase) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (unchunked4Unpacked A g a epoch auth f3 f4 ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if auth.isSome then fnBase + 56#64 else fnBase + 188#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch) →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm
        ((unchunked4Unpacked A g a epoch auth f3 f4 ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked82_placed_fetches_range H hfn 0 56
  obtain ⟨hcap_beq, hcap_bne, _⟩ := hauth_b
  subst hP
  have hP1 : unchunked4Unpacked A g a epoch auth f3 f4 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗
      vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 48#64) auth ∗
      ((a + 96#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  by_cases hep : epoch = 0#64
  · apply SepWPp.of_sepWP (mid := if auth.isSome then fnBase + 56#64 else fnBase + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen]) (by simp_all [EpochEncLenCalleeSaved])
  · have hep_beq : (epoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep
    have hep_bne : (epoch != 0#64) = true := bne_iff_ne.mpr hep
    have henc := bv_u64VarintField_nonzero hep
    apply SepWPp.of_sepWP (mid := if auth.isSome then fnBase + 56#64 else fnBase + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

private theorem step_unchunked82_auth_none_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked82PlacedEntry H prog fnBase)
    (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8)) (hauth : auth = none)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 188#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked4Unpacked A g a epoch auth f3 f4 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = fnBase + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hauth
  unchunked82_placed_fetches_range H hfn 188 196
  have hlen_eq : unchunked2EncodedLen epoch none = u64VarintFieldEncodedLen epoch := by
    simp [unchunked2EncodedLen, optAuthenticatorPBFieldEncodedLen]
  subst hP
  apply SepWPp.of_sepWP (mid := fnBase + 196#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

private theorem step_unchunked82_auth_some_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked82PlacedEntry H prog fnBase)
    (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (au : AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hauth : auth = some au) (hauth_b : OptAuthBounds g.auth auth)
    (hfit : unchunked2EncodedLen epoch auth < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 56#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked4Unpacked A g a epoch auth f3 f4 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = fnBase + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hauth
  unchunked82_placed_fetches_range H hfn 56 184
  obtain ⟨_, _, hroot_beq, hroot_bne, hmac_beq, hmac_bne⟩ := hauth_b.2.2 au rfl
  have hauth_fit : optAuthenticatorPBFieldEncodedLen (some au) < 2 ^ 64 := by
    unfold unchunked2EncodedLen at hfit; omega
  have hbody_lt : authenticatorPBEncodedLen au < 2 ^ 64 := by
    dsimp [optAuthenticatorPBFieldEncodedLen] at hauth_fit; omega
  have htot := bv_optAuthField_some au
  have hcmp := cmp_ls_false_of_lt
    (vlen := varintLen (BitVec.ofNat 64 (authenticatorPBEncodedLen au)))
    (tot := optAuthenticatorPBFieldEncodedLen (some au))
    (by dsimp [optAuthenticatorPBFieldEncodedLen]; omega) hauth_fit
  rcases hcmp with ⟨hcmp1, hcmp2, hcmp3, hcmp4, hcmp5⟩
  obtain ⟨hadd_final, hccf1, hccf2, hccf3, hccf4⟩ :=
    adds_no_overflow_of_eq (a := optAuthenticatorPBFieldEncodedLen (some au))
      (b := u64VarintFieldEncodedLen epoch) (c := unchunked2EncodedLen epoch (some au)) rfl hfit
  subst hP
  have hP1 : unchunked4Unpacked A g a epoch (some au) f3 f4 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗
      vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.auth.rootKey.cap) ∗ ((a + 56#64) ↦₆₄ g.auth.rootKey.ptr) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 au.rootKey.length) ∗
      vecU8Buf A g.auth.rootKey.cap g.auth.rootKey.ptr au.rootKey ∗
      ((a + 72#64) ↦₆₄ g.auth.macKey.cap) ∗ ((a + 80#64) ↦₆₄ g.auth.macKey.ptr) ∗
      ((a + 88#64) ↦₆₄ BitVec.ofNat 64 au.macKey.length) ∗
      vecU8Buf A g.auth.macKey.cap g.auth.macKey.ptr au.macKey ∗
      ((a + 96#64) ↦₆₄ epoch) := by
    simp only [unchunked4Unpacked, optAuthCap, optAuthPayload, arm64_norm]
  rw [hP1]
  cases hre : au.rootKey.isEmpty with
  | true =>
    have hr_len : au.rootKey.length = 0 := List.isEmpty_iff.mp hre |> congrArg List.length
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_00 : authenticatorPBEncodedLen au = 0 := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre, hme]
      have hopt_00 : optAuthenticatorPBFieldEncodedLen (some au) = 2 := by
        simp [optAuthenticatorPBFieldEncodedLen, hbody_00, varintLen]
      rw [hopt_00] at hadd_final hccf1 hccf2
      apply SepWPp.of_sepWP (mid := fnBase + 196#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      have hbody_01 : bytesFieldEncodedLen au.macKey = authenticatorPBEncodedLen au := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre]
      apply SepWPp.of_sepWP (mid := fnBase + 196#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc_r := bv_bytesField_nonempty hre
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_10 : bytesFieldEncodedLen au.rootKey = authenticatorPBEncodedLen au := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hme]
      apply SepWPp.of_sepWP (mid := fnBase + 196#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
        adds_no_overflow_of_eq (a := bytesFieldEncodedLen au.macKey)
          (b := bytesFieldEncodedLen au.rootKey) (c := authenticatorPBEncodedLen au) rfl hbody_lt
      apply SepWPp.of_sepWP (mid := fnBase + 196#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

private theorem step_unchunked82_f3_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked82PlacedEntry H prog fnBase)
    (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hf3_b : VecU8FieldBounds f3) (hfit : unchunked3EncodedLen epoch auth f3 < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 196#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth))
    (hP : P = unchunked4Unpacked A g a epoch auth f3 f4 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = fnBase + 240#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked82_placed_fetches_range H hfn 196 240
  obtain ⟨_, hf3_beq, hf3_bne⟩ := hf3_b
  subst hP
  have hP1 : unchunked4Unpacked A g a epoch auth f3 f4 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗
      vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 48#64) auth ∗
      ((a + 96#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f3.isEmpty with
  | true =>
    have hf3_len : f3.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq : unchunked2EncodedLen epoch auth = unchunked3EncodedLen epoch auth f3 := by
      simp [unchunked2EncodedLen, unchunked3EncodedLen, bytesFieldEncodedLen, hfe]
    apply SepWPp.of_sepWP (mid := fnBase + 240#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc := bv_bytesField_nonempty hfe
    obtain ⟨hadd, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f3) (b := unchunked2EncodedLen epoch auth)
        (c := unchunked3EncodedLen epoch auth f3) rfl hfit
    apply SepWPp.of_sepWP (mid := fnBase + 240#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

private theorem step_unchunked82_f4_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked82PlacedEntry H prog fnBase)
    (g : Unchunked4PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hf4_b : VecU8FieldBounds f4) (hfit : unchunked4EncodedLen epoch auth f3 f4 < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 240#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64) (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (unchunked4Unpacked A g a epoch auth f3 f4 ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked4EncodedLen epoch auth f3 f4) →
      CalleeSavedPreserved s0 sf → Q sf P) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  unchunked82_placed_fetches_range H hfn 240 292
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  obtain ⟨_, hf4_beq, hf4_bne⟩ := hf4_b
  subst hP
  have hP1 : unchunked4Unpacked A g a epoch auth f3 f4 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗
      vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 48#64) auth ∗
      ((a + 96#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f4.isEmpty with
  | true =>
    have hf4_len : f4.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq : unchunked3EncodedLen epoch auth f3 = unchunked4EncodedLen epoch auth f3 f4 := by
      simp [unchunked3EncodedLen, unchunked4EncodedLen, bytesFieldEncodedLen, hfe]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)
  | false =>
    have henc := bv_bytesField_nonempty hfe
    obtain ⟨hadd, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f4) (b := unchunked3EncodedLen epoch auth f3)
        (c := unchunked4EncodedLen epoch auth f3 f4) rfl hfit
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)

private theorem unchunked82_placed_pinned_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked82PlacedEntry H prog fnBase) :
    subroutine_ok prog fnBase (unchunked4EncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, epoch, auth, f3, f4⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [unchunked4EncodedLenPinnedSpec, unchunked4PinnedAt_eq_unpacked,
    unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have hfit3 : unchunked3EncodedLen epoch auth f3 < 2 ^ 64 := by
    unfold unchunked4EncodedLen unchunked3EncodedLen at *; omega
  have hfit2 : unchunked2EncodedLen epoch auth < 2 ^ 64 := by
    unfold unchunked3EncodedLen unchunked2EncodedLen at *; omega
  obtain ⟨hauth_b, hf3_b, hf4_b⟩ := unchunked4Unpacked_bounds hpre
  refine ⟨(unchunked4Unpacked A g a epoch auth f3 f4 ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rw [sepConj_emp]; convert hpre using 1; ac_rfl, ?_⟩
  refine step_unchunked82_epoch_placed (F := R) A H prog fnBase hfn g a s0.sp v16 v8 epoch auth f3 f4
    hauth_b hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
  rcases auth with _ | au
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine step_unchunked82_auth_none_placed (F := FSave) A H prog fnBase hfn g a epoch none f3 f4 rfl
      hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine step_unchunked82_f3_placed (F := FSave) A H prog fnBase hfn g a epoch none f3 f4
      hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    have hsp3' : s3.sp = s0.sp - 16#64 := by rw [hsp3, hsp2, hsp1]
    have hcs3' : EpochEncLenCalleeSaved s0 s3 := hcs1.trans (hcs2.trans hcs3)
    refine step_unchunked82_f4_placed (F := R) A H prog fnBase hfn g a s0.sp epoch none f3 f4
      hf4_b hfit hpc3 hrun3 hsp3' halign hx0_3 hx8_3 hcs3' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked4EncodedLenPinnedSpec, unchunked4PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr3, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  · simp only [Option.isSome_some, ↓reduceIte] at hpc1
    refine step_unchunked82_auth_some_placed (F := FSave) A H prog fnBase hfn g a epoch (some au) au f3 f4
      rfl hauth_b hfit2 hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine step_unchunked82_f3_placed (F := FSave) A H prog fnBase hfn g a epoch (some au) f3 f4
      hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    have hsp3' : s3.sp = s0.sp - 16#64 := by rw [hsp3, hsp2, hsp1]
    have hcs3' : EpochEncLenCalleeSaved s0 s3 := hcs1.trans (hcs2.trans hcs3)
    refine step_unchunked82_f4_placed (F := R) A H prog fnBase hfn g a s0.sp epoch (some au) f3 f4
      hf4_b hfit hpc3 hrun3 hsp3' halign hx0_3 hx8_3 hcs3' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked4EncodedLenPinnedSpec, unchunked4PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr3, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

/-! ### Exported Contracts for `HeaderSent` (`492`) and `EkSentCt1Received` (`499`) -/

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderSentEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_492 (Rust.withPanics ext)) (blkPl_492).base (headerSentEncodedLenPinnedSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderSentEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_492 (Rust.withPanics ext)) (blkPl_492).base (headerSentEncodedLenSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderSentEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_492 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_492).base (headerSentEncodedLenPinnedSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderSentEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_492 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_492).base (headerSentEncodedLenSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_492 H) (blkPl_492).base (headerSentEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked82_placed_pinned_ok A H _ _ (Or.inl ⟨rfl, rfl⟩))
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_492 H) (blkPl_492).base (headerSentEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked4EncodedLen_ok_of_pinned (unchunked82_placed_pinned_ok A H _ _ (Or.inl ⟨rfl, rfl⟩)))
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderSentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderSentEncodedLenLocal1PlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderSentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderSentEncodedLenLocal1PlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_499 (Rust.withPanics ext)) (blkPl_499).base (ekSentCt1ReceivedEncodedLenPinnedSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentCt1ReceivedEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_499 (Rust.withPanics ext)) (blkPl_499).base (ekSentCt1ReceivedEncodedLenSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_499 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_499).base (ekSentCt1ReceivedEncodedLenPinnedSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentCt1ReceivedEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_499 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_499).base (ekSentCt1ReceivedEncodedLenSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_499 H) (blkPl_499).base (ekSentCt1ReceivedEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked82_placed_pinned_ok A H _ _ (Or.inr ⟨rfl, rfl⟩))
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_499 H) (blkPl_499).base (ekSentCt1ReceivedEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked4EncodedLen_ok_of_pinned (unchunked82_placed_pinned_ok A H _ _ (Or.inr ⟨rfl, rfl⟩)))
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentCt1ReceivedEncodedLenLocal1PlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentCt1ReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## Part 2: 93-Instruction Group (`487` `Ct1Sent`, `469` `Ct1SentEkReceived`) -/

private def IsUnchunked93PlacedEntry [LibsignalPlacement] (H : String → Option (State → State))
    (prog : Program) (fnBase : BitVec 64) : Prop :=
  (prog = lsProg_487 H ∧ fnBase = (blkPl_487).base) ∨
  (prog = lsProg_469 H ∧ fnBase = (blkPl_469).base)

private theorem unchunked93_placed_fetch_entry [LibsignalPlacement]
    {H : String → Option (State → State)} {prog : Program} {fnBase : BitVec 64} {ins : Instr}
    (hfn : IsUnchunked93PlacedEntry H prog fnBase)
    (h0 : ((blkPC_487).rebase (blkPl_487).base H).fetch ((blkPl_487).base + 0#64) = some ins)
    (h1 : ((blkPC_469).rebase (blkPl_469).base H).fetch ((blkPl_469).base + 0#64) = some ins) :
    prog.fetch fnBase = some ins := by
  rcases hfn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa only [BitVec.add_zero] using h0
  · simpa only [BitVec.add_zero] using h1

private theorem unchunked93_placed_fetch_add [LibsignalPlacement]
    {H : String → Option (State → State)} {prog : Program} {fnBase : BitVec 64}
    (k : Nat) {ins : Instr}
    (hfn : IsUnchunked93PlacedEntry H prog fnBase)
    (h0 : ((blkPC_487).rebase (blkPl_487).base H).fetch ((blkPl_487).base + BitVec.ofNat 64 k) = some ins)
    (h1 : ((blkPC_469).rebase (blkPl_469).base H).fetch ((blkPl_469).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (fnBase + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h0
  · exact h1

open Lean Elab Tactic in
local elab "unchunked93_placed_fetches_range " H:term:max hfn:ident kStart:num kEnd:num : tactic => do
  let kS := kStart.getNat
  let kE := kEnd.getNat
  let ns := `CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.Placed
  let b0 := mkIdent (ns |>.str "blkPl_487")
  let b1 := mkIdent (ns |>.str "blkPl_469")
  let fe := mkIdent ``unchunked93_placed_fetch_entry
  let fa := mkIdent ``unchunked93_placed_fetch_add
  for i in [kS / 4 : kE / 4] do
    let k := 4 * i
    let hexK := String.ofList (Nat.toDigits 16 k)
    let l0 := mkIdent (ns |>.str s!"blkPC_487_rebase_fetch_0x{hexK}")
    let l1 := mkIdent (ns |>.str s!"blkPC_469_rebase_fetch_0x{hexK}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fe $hfn
          ($l0 ($b0).base $H) ($l1 ($b1).base $H)))
    else
      evalTactic (← `(tactic|
        have := $fa $kq $hfn
          ($l0 ($b0).base $H) ($l1 ($b1).base $H)))

private theorem step_unchunked93_epoch_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked93PlacedEntry H prog fnBase)
    (g : Unchunked5PBGhost) (a sp v16 v8 : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hauth_b : OptAuthBounds g.auth auth)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = fnBase) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if auth.isSome then fnBase + 56#64 else fnBase + 188#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch) →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm
        ((unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked93_placed_fetches_range H hfn 0 56
  obtain ⟨hcap_beq, hcap_bne, _⟩ := hauth_b
  subst hP
  have hP1 : unchunked5Unpacked A g a epoch auth f3 f4 f5 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗ ((a + 120#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  by_cases hep : epoch = 0#64
  · apply SepWPp.of_sepWP (mid := if auth.isSome then fnBase + 56#64 else fnBase + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen]) (by simp_all [EpochEncLenCalleeSaved])
  · have hep_beq : (epoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep
    have hep_bne : (epoch != 0#64) = true := bne_iff_ne.mpr hep
    have henc := bv_u64VarintField_nonzero hep
    apply SepWPp.of_sepWP (mid := if auth.isSome then fnBase + 56#64 else fnBase + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

private theorem step_unchunked93_auth_none_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked93PlacedEntry H prog fnBase)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8)) (hauth : auth = none)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 188#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = fnBase + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hauth
  unchunked93_placed_fetches_range H hfn 188 196
  have hlen_eq : unchunked2EncodedLen epoch none = u64VarintFieldEncodedLen epoch := by
    simp [unchunked2EncodedLen, optAuthenticatorPBFieldEncodedLen]
  subst hP
  apply SepWPp.of_sepWP (mid := fnBase + 196#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

private theorem step_unchunked93_auth_some_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked93PlacedEntry H prog fnBase)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (au : AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hauth : auth = some au) (hauth_b : OptAuthBounds g.auth auth)
    (hfit : unchunked2EncodedLen epoch auth < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 56#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = fnBase + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hauth
  unchunked93_placed_fetches_range H hfn 56 184
  obtain ⟨_, _, hroot_beq, hroot_bne, hmac_beq, hmac_bne⟩ := hauth_b.2.2 au rfl
  have hauth_fit : optAuthenticatorPBFieldEncodedLen (some au) < 2 ^ 64 := by
    unfold unchunked2EncodedLen at hfit; omega
  have hbody_lt : authenticatorPBEncodedLen au < 2 ^ 64 := by dsimp [optAuthenticatorPBFieldEncodedLen] at hauth_fit; omega
  have htot := bv_optAuthField_some au
  have hcmp := cmp_ls_false_of_lt (vlen := varintLen (BitVec.ofNat 64 (authenticatorPBEncodedLen au)))
    (tot := optAuthenticatorPBFieldEncodedLen (some au)) (by dsimp [optAuthenticatorPBFieldEncodedLen]; omega) hauth_fit
  rcases hcmp with ⟨hcmp1, hcmp2, hcmp3, hcmp4, hcmp5⟩
  obtain ⟨hadd_final, hccf1, hccf2, hccf3, hccf4⟩ :=
    adds_no_overflow_of_eq (a := optAuthenticatorPBFieldEncodedLen (some au)) (b := u64VarintFieldEncodedLen epoch)
      (c := unchunked2EncodedLen epoch (some au)) rfl hfit
  subst hP
  have hP1 : unchunked5Unpacked A g a epoch (some au) f3 f4 f5 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a + 72#64) ↦₆₄ g.auth.rootKey.cap) ∗ ((a + 80#64) ↦₆₄ g.auth.rootKey.ptr) ∗ ((a + 88#64) ↦₆₄ BitVec.ofNat 64 au.rootKey.length) ∗
      vecU8Buf A g.auth.rootKey.cap g.auth.rootKey.ptr au.rootKey ∗
      ((a + 96#64) ↦₆₄ g.auth.macKey.cap) ∗ ((a + 104#64) ↦₆₄ g.auth.macKey.ptr) ∗ ((a + 112#64) ↦₆₄ BitVec.ofNat 64 au.macKey.length) ∗
      vecU8Buf A g.auth.macKey.cap g.auth.macKey.ptr au.macKey ∗ ((a + 120#64) ↦₆₄ epoch) := by
    simp only [unchunked5Unpacked, optAuthCap, optAuthPayload, arm64_norm]
  rw [hP1]
  cases hre : au.rootKey.isEmpty with
  | true =>
    have hr_len : au.rootKey.length = 0 := List.isEmpty_iff.mp hre |> congrArg List.length
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_00 : authenticatorPBEncodedLen au = 0 := by simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre, hme]
      have hopt_00 : optAuthenticatorPBFieldEncodedLen (some au) = 2 := by
        simp [optAuthenticatorPBFieldEncodedLen, hbody_00, varintLen]
      rw [hopt_00] at hadd_final hccf1 hccf2
      apply SepWPp.of_sepWP (mid := fnBase + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      have hbody_01 : bytesFieldEncodedLen au.macKey = authenticatorPBEncodedLen au := by simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre]
      apply SepWPp.of_sepWP (mid := fnBase + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc_r := bv_bytesField_nonempty hre
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_10 : bytesFieldEncodedLen au.rootKey = authenticatorPBEncodedLen au := by simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hme]
      apply SepWPp.of_sepWP (mid := fnBase + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
        adds_no_overflow_of_eq (a := bytesFieldEncodedLen au.macKey) (b := bytesFieldEncodedLen au.rootKey) (c := authenticatorPBEncodedLen au) rfl hbody_lt
      apply SepWPp.of_sepWP (mid := fnBase + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

private theorem step_unchunked93_f3_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked93PlacedEntry H prog fnBase)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hf3_b : VecU8FieldBounds f3)
    (hfit : unchunked3EncodedLen epoch auth f3 < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 196#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = fnBase + 240#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3) →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked93_placed_fetches_range H hfn 196 240
  obtain ⟨_, hf3_beq, hf3_bne⟩ := hf3_b
  subst hP
  have hP1 : unchunked5Unpacked A g a epoch auth f3 f4 f5 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗
      ((a + 120#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f3.isEmpty with
  | true =>
    have hf3_len : f3.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq : unchunked2EncodedLen epoch auth = unchunked3EncodedLen epoch auth f3 := by
      simp [unchunked2EncodedLen, unchunked3EncodedLen, bytesFieldEncodedLen, hfe]
    apply SepWPp.of_sepWP (mid := fnBase + 240#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc := bv_bytesField_nonempty hfe
    obtain ⟨hadd, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f3)
        (b := unchunked2EncodedLen epoch auth)
        (c := unchunked3EncodedLen epoch auth f3) rfl hfit
    apply SepWPp.of_sepWP (mid := fnBase + 240#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

private theorem step_unchunked93_f4_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked93PlacedEntry H prog fnBase)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hf4_b : VecU8FieldBounds f4)
    (hfit : unchunked4EncodedLen epoch auth f3 f4 < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 240#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = fnBase + 284#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked4EncodedLen epoch auth f3 f4) →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked93_placed_fetches_range H hfn 240 284
  obtain ⟨_, hf4_beq, hf4_bne⟩ := hf4_b
  subst hP
  have hP1 : unchunked5Unpacked A g a epoch auth f3 f4 f5 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗
      ((a + 120#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f4.isEmpty with
  | true =>
    have hf4_len : f4.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq : unchunked3EncodedLen epoch auth f3 = unchunked4EncodedLen epoch auth f3 f4 := by
      simp [unchunked3EncodedLen, unchunked4EncodedLen, bytesFieldEncodedLen, hfe]
    apply SepWPp.of_sepWP (mid := fnBase + 284#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc := bv_bytesField_nonempty hfe
    obtain ⟨hadd, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f4)
        (b := unchunked3EncodedLen epoch auth f3)
        (c := unchunked4EncodedLen epoch auth f3 f4) rfl hfit
    apply SepWPp.of_sepWP (mid := fnBase + 284#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

private theorem step_unchunked93_f5_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked93PlacedEntry H prog fnBase)
    (g : Unchunked5PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hf5_b : VecU8FieldBounds f5)
    (hfit : unchunked5EncodedLen epoch auth f3 f4 f5 < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 284#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked4EncodedLen epoch auth f3 f4))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked5EncodedLen epoch auth f3 f4 f5) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  unchunked93_placed_fetches_range H hfn 284 336
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  obtain ⟨_, hf5_beq, hf5_bne⟩ := hf5_b
  subst hP
  have hP1 : unchunked5Unpacked A g a epoch auth f3 f4 f5 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗
      ((a + 120#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f5.isEmpty with
  | true =>
    have hf5_len : f5.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq :
        unchunked4EncodedLen epoch auth f3 f4 = unchunked5EncodedLen epoch auth f3 f4 f5 := by
      simp [unchunked4EncodedLen, unchunked5EncodedLen, bytesFieldEncodedLen, hfe]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)
  | false =>
    have henc := bv_bytesField_nonempty hfe
    obtain ⟨hadd, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f5)
        (b := unchunked4EncodedLen epoch auth f3 f4)
        (c := unchunked5EncodedLen epoch auth f3 f4 f5) rfl hfit
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)

private theorem unchunked93_placed_pinned_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (prog : Program) (fnBase : BitVec 64)
    (hfn : IsUnchunked93PlacedEntry H prog fnBase) :
    subroutine_ok prog fnBase (unchunked5EncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, epoch, auth, f3, f4, f5⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [unchunked5EncodedLenPinnedSpec, unchunked5PinnedAt_eq_unpacked,
    unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have hfit4 : unchunked4EncodedLen epoch auth f3 f4 < 2 ^ 64 := by
    unfold unchunked5EncodedLen unchunked4EncodedLen at *; omega
  have hfit3 : unchunked3EncodedLen epoch auth f3 < 2 ^ 64 := by
    unfold unchunked4EncodedLen unchunked3EncodedLen at *; omega
  have hfit2 : unchunked2EncodedLen epoch auth < 2 ^ 64 := by
    unfold unchunked3EncodedLen unchunked2EncodedLen at *; omega
  obtain ⟨hauth_b, hf3_b, hf4_b, hf5_b⟩ := unchunked5Unpacked_bounds hpre
  refine ⟨(unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rw [sepConj_emp]; convert hpre using 1; ac_rfl, ?_⟩
  refine step_unchunked93_epoch_placed (F := R) A H prog fnBase hfn g a s0.sp v16 v8 epoch auth f3 f4 f5
    hauth_b hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
  rcases auth with _ | au
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine step_unchunked93_auth_none_placed (F := FSave) A H prog fnBase hfn g a epoch none f3 f4 f5 rfl
      hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine step_unchunked93_f3_placed (F := FSave) A H prog fnBase hfn g a epoch none f3 f4 f5
      hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    refine step_unchunked93_f4_placed (F := FSave) A H prog fnBase hfn g a epoch none f3 f4 f5
      hf4_b hfit4 hpc3 hrun3 hx0_3 hx8_3 (by dsimp [FSave]; ac_rfl) ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
    have hsp4' : s4.sp = s0.sp - 16#64 := by rw [hsp4, hsp3, hsp2, hsp1]
    have hcs4' : EpochEncLenCalleeSaved s0 s4 := hcs1.trans (hcs2.trans (hcs3.trans hcs4))
    refine step_unchunked93_f5_placed (F := R) A H prog fnBase hfn g a s0.sp epoch none f3 f4 f5
      hf5_b hfit hpc4 hrun4 hsp4' halign hx0_4 hx8_4 hcs4' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked5EncodedLenPinnedSpec, unchunked5PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr4, htr3, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  · simp only [Option.isSome_some, ↓reduceIte] at hpc1
    refine step_unchunked93_auth_some_placed (F := FSave) A H prog fnBase hfn g a epoch (some au) au f3 f4 f5
      rfl hauth_b hfit2 hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine step_unchunked93_f3_placed (F := FSave) A H prog fnBase hfn g a epoch (some au) f3 f4 f5
      hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    refine step_unchunked93_f4_placed (F := FSave) A H prog fnBase hfn g a epoch (some au) f3 f4 f5
      hf4_b hfit4 hpc3 hrun3 hx0_3 hx8_3 (by dsimp [FSave]; ac_rfl) ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
    have hsp4' : s4.sp = s0.sp - 16#64 := by rw [hsp4, hsp3, hsp2, hsp1]
    have hcs4' : EpochEncLenCalleeSaved s0 s4 := hcs1.trans (hcs2.trans (hcs3.trans hcs4))
    refine step_unchunked93_f5_placed (F := R) A H prog fnBase hfn g a s0.sp epoch (some au) f3 f4 f5
      hf5_b hfit hpc4 hrun4 hsp4' halign hx0_4 hx8_4 hcs4' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked5EncodedLenPinnedSpec, unchunked5PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr4, htr3, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

/-! ### Exported Contracts for `Ct1Sent` (`487`) and `Ct1SentEkReceived` (`469`) -/

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_487 (Rust.withPanics ext)) (blkPl_487).base (ct1SentEncodedLenPinnedSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_487 (Rust.withPanics ext)) (blkPl_487).base (ct1SentEncodedLenSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_487 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_487).base (ct1SentEncodedLenPinnedSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_487 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_487).base (ct1SentEncodedLenSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_487 H) (blkPl_487).base (ct1SentEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked93_placed_pinned_ok A H _ _ (Or.inl ⟨rfl, rfl⟩))
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_487 H) (blkPl_487).base (ct1SentEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked5EncodedLen_ok_of_pinned (unchunked93_placed_pinned_ok A H _ _ (Or.inl ⟨rfl, rfl⟩)))
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEncodedLenLocal1PlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEncodedLenLocal1PlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_469 (Rust.withPanics ext)) (blkPl_469).base (ct1SentEkReceivedEncodedLenPinnedSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEkReceivedEncodedLenLocal1PlacedOkExt
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_469 (Rust.withPanics ext)) (blkPl_469).base (ct1SentEkReceivedEncodedLenSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_469 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_469).base (ct1SentEkReceivedEncodedLenPinnedSpec A)
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEkReceivedEncodedLenLocal1PlacedOk
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_469 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_469).base (ct1SentEkReceivedEncodedLenSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_469 H) (blkPl_469).base (ct1SentEkReceivedEncodedLenPinnedSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked93_placed_pinned_ok A H _ _ (Or.inr ⟨rfl, rfl⟩))
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_placed_ok_x
    [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok (lsProg_469 H) (blkPl_469).base (ct1SentEkReceivedEncodedLenSpec A) :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (unchunked5EncodedLen_ok_of_pinned (unchunked93_placed_pinned_ok A H _ _ (Or.inr ⟨rfl, rfl⟩)))
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_placed_ok_ext
    [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEkReceivedEncodedLenLocal1PlacedOkExt A ext :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_placed_ok
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEkReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end CryptoVerification.SpqrV1.ProtoRepr

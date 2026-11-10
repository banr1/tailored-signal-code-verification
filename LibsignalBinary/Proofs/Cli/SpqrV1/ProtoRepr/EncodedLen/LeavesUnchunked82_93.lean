/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.Defs
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prog
public import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.SepLogic.CodeLookup
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.Fetch
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Fetch
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- shake: keep
public meta import Lean -- shake: keep

/-!
# CLI 82- and 93-Instruction Unchunked `encoded_len` Leaf Proofs

Proves `subroutine_ok` contracts for the 82-instruction (`HeaderSent`, `EkSentCt1Received`) and
93-instruction (`Ct1Sent`, `Ct1SentEkReceived`) unchunked `V1State` leaf `encoded_len` routines on
the CLI image.
-/

@[expose] public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n


namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSpqrV1

open EncodedLen

local notation "tripleRatchetProgAtExt" => CryptoVerification.LibsignalTripleRatchet.contractProg

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

private theorem subroutine_ok_repack {G1 G2 : Type} {prog : Program} {entry : BitVec 64}
    {S1 : Spec G1} {S2 : Spec G2} (f : G2 → G1)
    (hpre : ∀ x s, S2.pre x s = S1.pre (f x) s)
    (hpost : ∀ x s0 sf, S2.post x s0 sf = S1.post (f x) s0 sf)
    (hok : subroutine_ok prog entry S1)
    (honPanic : ∀ x s0 sf, S2.onPanic x s0 sf = S1.onPanic (f x) s0 sf := by intros; rfl)
    (honExit : ∀ x c s0 sf, S2.onExit x c s0 sf = S1.onExit (f x) c s0 sf := by intros; rfl)
    (honOom : ∀ x s0 sf, S2.onOom x s0 sf = S1.onOom (f x) s0 sf := by intros; rfl) :
    subroutine_ok prog entry S2 := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre0 hsp
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

/-! ## Part 1: 82-Instruction Group (`HeaderSent`, `EkSentCt1Received`) -/

/-- Entry address predicate for all 4 functions in the 82-insn group. -/
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked82Entry (b : BitVec 64) (abs : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr headerSentEncodedLenLocal2Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr ekSentCt1ReceivedEncodedLenLocal2Name = entry

open Lean Elab Tactic in
elab "unchunked82_fetches_range_cli " b:term:max H:term:max _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let offs := #[(num% (ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderSent as prost::message::Message>::encoded_len [local#3]")), 0x63eac, (num% (ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received as prost::message::Message>::encoded_len [local#3]")), 0x67474]
  let fnOffs := #[
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderSent as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x63eac,
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x67474
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let decs := offs.map fun off =>
      mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.ProtoRepr |>.str
        s!"spqrUnchunked82BinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
    let d0 := decs[0]!; let d1 := decs[1]!; let d2 := decs[2]!; let d3 := decs[3]!
    let f0 := fnOffs[0]!; let f1 := fnOffs[1]!; let f2 := fnOffs[2]!; let f3 := fnOffs[3]!
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := unchunked82_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $f0 (by decide) $d0)
          ($fetchEntry (b := $b) (H := $H) $f1 (by decide) $d1)
          ($fetchEntry (b := $b) (H := $H) $f2 (by decide) $d2)
          ($fetchEntry (b := $b) (H := $H) $f3 (by decide) $d3)))
    else
      evalTactic (← `(tactic|
        have := unchunked82_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f0 (by decide) $d0)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f1 (by decide) $d1)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f2 (by decide) $d2)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f3 (by decide) $d3)))

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_epoch (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked82Entry b abs entry)
    (g : Unchunked4PBGhost) (a sp v16 v8 : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hauth_b : OptAuthBounds g.auth auth)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (unchunked4Unpacked A g a epoch auth f3 f4 ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if auth.isSome then entry + 56#64 else entry + 188#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        ((unchunked4Unpacked A g a epoch auth f3 f4 ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  unchunked82_fetches_range_cli b (Rust.withPanics abs) entry hfn 0 56
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
  · apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen]) (by simp_all [EpochEncLenCalleeSaved])
  · have hep_beq : (epoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep
    have hep_bne : (epoch != 0#64) = true := bne_iff_ne.mpr hep
    have henc := bv_u64VarintField_nonzero hep
    apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_auth_none (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked82Entry b abs entry)
    (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8)) (hauth : auth = none)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 188#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked4Unpacked A g a epoch auth f3 f4 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  subst hauth
  unchunked82_fetches_range_cli b (Rust.withPanics abs) entry hfn 188 196
  have hlen_eq : unchunked2EncodedLen epoch none = u64VarintFieldEncodedLen epoch := by
    simp [unchunked2EncodedLen, optAuthenticatorPBFieldEncodedLen]
  subst hP
  apply SepWPp.of_sepWP (mid := entry + 196#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_auth_some (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked82Entry b abs entry)
    (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (au : AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hauth : auth = some au) (hauth_b : OptAuthBounds g.auth auth)
    (hfit : unchunked2EncodedLen epoch auth < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked4Unpacked A g a epoch auth f3 f4 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  subst hauth
  unchunked82_fetches_range_cli b (Rust.withPanics abs) entry hfn 56 184
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
      apply SepWPp.of_sepWP (mid := entry + 196#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      have hbody_01 : bytesFieldEncodedLen au.macKey = authenticatorPBEncodedLen au := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre]
      apply SepWPp.of_sepWP (mid := entry + 196#64)
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
      apply SepWPp.of_sepWP (mid := entry + 196#64)
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
      apply SepWPp.of_sepWP (mid := entry + 196#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- Tag-3 `f3: Vec<u8>` field length (`+0x0c4..+0x0ec` -> `+0x0f0` = `entry + 240#64`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_f3 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked82Entry b abs entry)
    (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hf3_b : VecU8FieldBounds f3) (hfit : unchunked3EncodedLen epoch auth f3 < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 196#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth))
    (hP : P = unchunked4Unpacked A g a epoch auth f3 f4 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 240#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3) →
      EpochEncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  unchunked82_fetches_range_cli b (Rust.withPanics abs) entry hfn 196 240
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
    apply SepWPp.of_sepWP (mid := entry + 240#64)
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
    apply SepWPp.of_sepWP (mid := entry + 240#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- Tag-4 `f4: Vec<u8>` field length + epilogue (`+0x0f0..+0x120: ldp, ret`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_f4 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked82Entry b abs entry)
    (g : Unchunked4PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hf4_b : VecU8FieldBounds f4) (hfit : unchunked4EncodedLen epoch auth f3 f4 < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 240#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64) (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (unchunked4Unpacked A g a epoch auth f3 f4 ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked4EncodedLen epoch auth f3 f4) →
      CalleeSavedPreserved s0 sf → Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  unchunked82_fetches_range_cli b (Rust.withPanics abs) entry hfn 240 292
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

/-- Shared `subroutine_ok` proof for all 4 functions in the 82-insn group. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked82_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked82Entry b ext entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (unchunked4EncodedLenPinnedSpec A) := by
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
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_epoch (F := R) b A ext entry hfn g a s0.sp v16 v8 epoch auth f3 f4
    hauth_b hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
  rcases auth with _ | au
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_auth_none (F := FSave) b A ext entry hfn g a epoch none f3 f4 rfl
      hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_f3 (F := FSave) b A ext entry hfn g a epoch none f3 f4
      hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    have hsp3' : s3.sp = s0.sp - 16#64 := by rw [hsp3, hsp2, hsp1]
    have hcs3' : EpochEncLenCalleeSaved s0 s3 := hcs1.trans (hcs2.trans hcs3)
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_f4 (F := R) b A ext entry hfn g a s0.sp epoch none f3 f4
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
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_auth_some (F := FSave) b A ext entry hfn g a epoch (some au) au f3 f4
      rfl hauth_b hfit2 hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_f3 (F := FSave) b A ext entry hfn g a epoch (some au) f3 f4
      hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    have hsp3' : s3.sp = s0.sp - 16#64 := by rw [hsp3, hsp2, hsp1]
    have hcs3' : EpochEncLenCalleeSaved s0 s3 := hcs1.trans (hcs2.trans hcs3)
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked82_f4 (F := R) b A ext entry hfn g a s0.sp epoch (some au) f3 f4
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

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderSentEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLenLocal1Name) (headerSentEncodedLenPinnedSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderSentEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked82_entry_pinned_ok_ext b A ext _ (Or.inl rfl))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentCt1ReceivedEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLenLocal1Name) (ekSentCt1ReceivedEncodedLenPinnedSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentCt1ReceivedEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked82_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl))))

/-- Entry address predicate for all 4 functions in the 93-insn group. -/
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked93Entry (b : BitVec 64) (abs : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr ct1SentEncodedLenLocal2Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr ct1SentEkReceivedEncodedLenLocal2Name = entry

open Lean Elab Tactic in
elab "unchunked93_fetches_range_cli " b:term:max H:term:max _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let offs := #[(num% (ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent as prost::message::Message>::encoded_len [local#3]")), 0x63948, (num% (ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived as prost::message::Message>::encoded_len [local#3]")), 0x5ed84]
  let fnOffs := #[
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x63948,
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x5ed84
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let decs := offs.map fun off =>
      mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.ProtoRepr |>.str
        s!"spqrUnchunked93BinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
    let d0 := decs[0]!; let d1 := decs[1]!; let d2 := decs[2]!; let d3 := decs[3]!
    let f0 := fnOffs[0]!; let f1 := fnOffs[1]!; let f2 := fnOffs[2]!; let f3 := fnOffs[3]!
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := unchunked93_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $f0 (by decide) $d0)
          ($fetchEntry (b := $b) (H := $H) $f1 (by decide) $d1)
          ($fetchEntry (b := $b) (H := $H) $f2 (by decide) $d2)
          ($fetchEntry (b := $b) (H := $H) $f3 (by decide) $d3)))
    else
      evalTactic (← `(tactic|
        have := unchunked93_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f0 (by decide) $d0)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f1 (by decide) $d1)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f2 (by decide) $d2)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f3 (by decide) $d3)))

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_epoch (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked93Entry b abs entry)
    (g : Unchunked5PBGhost) (a sp v16 v8 : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hauth_b : OptAuthBounds g.auth auth)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if auth.isSome then entry + 56#64 else entry + 188#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        ((unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  unchunked93_fetches_range_cli b (Rust.withPanics abs) entry hfn 0 56
  obtain ⟨hcap_beq, hcap_bne, _⟩ := hauth_b
  subst hP
  have hP1 : unchunked5Unpacked A g a epoch auth f3 f4 f5 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗ ((a + 120#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  by_cases hep : epoch = 0#64
  · apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen]) (by simp_all [EpochEncLenCalleeSaved])
  · have hep_beq : (epoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep
    have hep_bne : (epoch != 0#64) = true := bne_iff_ne.mpr hep
    have henc := bv_u64VarintField_nonzero hep
    apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_auth_none (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked93Entry b abs entry)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8)) (hauth : auth = none)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 188#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  subst hauth
  unchunked93_fetches_range_cli b (Rust.withPanics abs) entry hfn 188 196
  have hlen_eq : unchunked2EncodedLen epoch none = u64VarintFieldEncodedLen epoch := by
    simp [unchunked2EncodedLen, optAuthenticatorPBFieldEncodedLen]
  subst hP
  apply SepWPp.of_sepWP (mid := entry + 196#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_auth_some (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64) (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked93Entry b abs entry)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (au : AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hauth : auth = some au) (hauth_b : OptAuthBounds g.auth auth)
    (hfit : unchunked2EncodedLen epoch auth < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  subst hauth
  unchunked93_fetches_range_cli b (Rust.withPanics abs) entry hfn 56 184
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
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      have hbody_01 : bytesFieldEncodedLen au.macKey = authenticatorPBEncodedLen au := by simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre]
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc_r := bv_bytesField_nonempty hre
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_10 : bytesFieldEncodedLen au.rootKey = authenticatorPBEncodedLen au := by simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hme]
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
        adds_no_overflow_of_eq (a := bytesFieldEncodedLen au.macKey) (b := bytesFieldEncodedLen au.rootKey) (c := authenticatorPBEncodedLen au) rfl hbody_lt
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- Tag-3 `f3: Vec<u8>` field length (`+0x0c4..+0x0ec` -> `+0x0f0` = `entry + 240#64`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_f3 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked93Entry b abs entry)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hf3_b : VecU8FieldBounds f3)
    (hfit : unchunked3EncodedLen epoch auth f3 < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 196#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 240#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  unchunked93_fetches_range_cli b (Rust.withPanics abs) entry hfn 196 240
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
    apply SepWPp.of_sepWP (mid := entry + 240#64)
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
    apply SepWPp.of_sepWP (mid := entry + 240#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- Tag-4 `f4: Vec<u8>` field length (`+0x0f0..+0x118` -> `+0x11c` = `entry + 284#64`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_f4 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked93Entry b abs entry)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hf4_b : VecU8FieldBounds f4)
    (hfit : unchunked4EncodedLen epoch auth f3 f4 < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 240#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 284#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked4EncodedLen epoch auth f3 f4) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  unchunked93_fetches_range_cli b (Rust.withPanics abs) entry hfn 240 284
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
    apply SepWPp.of_sepWP (mid := entry + 284#64)
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
    apply SepWPp.of_sepWP (mid := entry + 284#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- Tag-5 `f5: Vec<u8>` field length + epilogue (`+0x11c..+0x14c: ldp, ret`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_f5 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked93Entry b abs entry)
    (g : Unchunked5PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hf5_b : VecU8FieldBounds f5)
    (hfit : unchunked5EncodedLen epoch auth f3 f4 f5 < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 284#64) (hrun : s.status = .Running)
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
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  unchunked93_fetches_range_cli b (Rust.withPanics abs) entry hfn 284 336
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

/-- Shared `subroutine_ok` proof for all 4 functions in the 93-insn group. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked93_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked93Entry b ext entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (unchunked5EncodedLenPinnedSpec A) := by
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
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_epoch (F := R) b A ext entry hfn g a s0.sp v16 v8 epoch auth f3 f4 f5
    hauth_b hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
  rcases auth with _ | au
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_auth_none (F := FSave) b A ext entry hfn g a epoch none f3 f4 f5 rfl
      hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_f3 (F := FSave) b A ext entry hfn g a epoch none f3 f4 f5
      hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_f4 (F := FSave) b A ext entry hfn g a epoch none f3 f4 f5
      hf4_b hfit4 hpc3 hrun3 hx0_3 hx8_3 (by dsimp [FSave]; ac_rfl) ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
    have hsp4' : s4.sp = s0.sp - 16#64 := by rw [hsp4, hsp3, hsp2, hsp1]
    have hcs4' : EpochEncLenCalleeSaved s0 s4 := hcs1.trans (hcs2.trans (hcs3.trans hcs4))
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_f5 (F := R) b A ext entry hfn g a s0.sp epoch none f3 f4 f5
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
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_auth_some (F := FSave) b A ext entry hfn g a epoch (some au) au f3 f4 f5
      rfl hauth_b hfit2 hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_f3 (F := FSave) b A ext entry hfn g a epoch (some au) f3 f4 f5
      hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_f4 (F := FSave) b A ext entry hfn g a epoch (some au) f3 f4 f5
      hf4_b hfit4 hpc3 hrun3 hx0_3 hx8_3 (by dsimp [FSave]; ac_rfl) ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
    have hsp4' : s4.sp = s0.sp - 16#64 := by rw [hsp4, hsp3, hsp2, hsp1]
    have hcs4' : EpochEncLenCalleeSaved s0 s4 := hcs1.trans (hcs2.trans (hcs3.trans hcs4))
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked93_f5 (F := R) b A ext entry hfn g a s0.sp epoch (some au) f3 f4 f5
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

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLenLocal1Name) (ct1SentEncodedLenPinnedSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked93_entry_pinned_ok_ext b A ext _ (Or.inl rfl))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEkReceivedEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLenLocal1Name) (ct1SentEkReceivedEncodedLenPinnedSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct1SentEkReceivedEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked93_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl))))

end CryptoVerification.SpqrV1.ProtoRepr

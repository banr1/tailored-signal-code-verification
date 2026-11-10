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
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- shake: keep
public meta import Lean -- shake: keep

/-!
# CLI 59- and 71-Instruction Unchunked `encoded_len` Leaf Proofs

Proves `subroutine_ok` contracts for the 59-instruction (`KeysUnsampled`, `NoHeaderReceived`,
`Ct2Sent`) and 71-instruction (`EkSent`, `HeaderReceived`) unchunked `V1State` leaf `encoded_len`
routines on the CLI image.
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

/-! ## Part 1: 59-Instruction Group (`KeysUnsampled`, `NoHeaderReceived`, `Ct2Sent`) -/

/-- Entry address predicate for all 6 functions in the 59-insn group. -/
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked59Entry (b : BitVec 64) (abs : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.keysUnsampledEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr keysUnsampledEncodedLenLocal2Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.noHeaderReceivedEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr noHeaderReceivedEncodedLenLocal2Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.ct2SentEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr ct2SentEncodedLenLocal2Name = entry

open Lean Elab Tactic in
elab "unchunked59_fetches_range_cli " b:term:max H:term:max _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let offs := #[(num% (ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::KeysUnsampled as prost::message::Message>::encoded_len [local#3]")), 0x613cc, (num% (ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::NoHeaderReceived as prost::message::Message>::encoded_len [local#3]")), 0x6796c, (num% (ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#3]")), 0x5f2f0]
  let fnOffs := #[
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::KeysUnsampled as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x613cc,
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::NoHeaderReceived as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x6796c,
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x5f2f0
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let decs := offs.map fun off =>
      mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.ProtoRepr |>.str
        s!"spqrUnchunked59BinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
    let d0 := decs[0]!; let d1 := decs[1]!; let d2 := decs[2]!
    let d3 := decs[3]!; let d4 := decs[4]!; let d5 := decs[5]!
    let f0 := fnOffs[0]!; let f1 := fnOffs[1]!; let f2 := fnOffs[2]!
    let f3 := fnOffs[3]!; let f4 := fnOffs[4]!; let f5 := fnOffs[5]!
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := unchunked59_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $f0 (by decide) $d0)
          ($fetchEntry (b := $b) (H := $H) $f1 (by decide) $d1)
          ($fetchEntry (b := $b) (H := $H) $f2 (by decide) $d2)
          ($fetchEntry (b := $b) (H := $H) $f3 (by decide) $d3)
          ($fetchEntry (b := $b) (H := $H) $f4 (by decide) $d4)
          ($fetchEntry (b := $b) (H := $H) $f5 (by decide) $d5)))
    else
      evalTactic (← `(tactic|
        have := unchunked59_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f0 (by decide) $d0)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f1 (by decide) $d1)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f2 (by decide) $d2)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f3 (by decide) $d3)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f4 (by decide) $d4)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f5 (by decide) $d5)))

/-- Prologue + `epoch` field length (`+0x000..+0x034`), branching to `+0x038` (`entry + 56#64`)
    when `auth.isSome` or `+0x0c0` (`entry + 192#64`) when `auth = none`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked59_epoch (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked59Entry b abs entry)
    (g : Unchunked2PBGhost) (a sp v16 v8 : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB)
    (hauth_b : OptAuthBounds g auth)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (unchunked2Unpacked A g a epoch auth ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if auth.isSome then entry + 56#64 else entry + 192#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        ((unchunked2Unpacked A g a epoch auth ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  unchunked59_fetches_range_cli b (Rust.withPanics abs) entry hfn 0 56
  obtain ⟨hcap_beq, hcap_bne, _⟩ := hauth_b
  subst hP
  have hP1 : unchunked2Unpacked A g a epoch auth =
      (a ↦₆₄ optAuthCap g auth) ∗ optAuthPayload A g a auth ∗ ((a + 48#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  by_cases hep : epoch = 0#64
  · apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 192#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen])
      (by simp_all [EpochEncLenCalleeSaved])
  · have hep_beq : (epoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep
    have hep_bne : (epoch != 0#64) = true := bne_iff_ne.mpr hep
    have henc := bv_u64VarintField_nonzero hep
    apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 192#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

/-- `auth = none` path (`+0x0c0..+0x0c4` -> `+0x0b8..+0x0bc: ldp, ret`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked59_auth_none (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked59Entry b abs entry)
    (g : Unchunked2PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB)
    (hauth : auth = none)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 192#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (unchunked2Unpacked A g a epoch auth ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  subst hauth
  unchunked59_fetches_range_cli b (Rust.withPanics abs) entry hfn 184 200
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  have hlen_eq : unchunked2EncodedLen epoch none = u64VarintFieldEncodedLen epoch := by
    simp [unchunked2EncodedLen, optAuthenticatorPBFieldEncodedLen]
  subst hP
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-- `auth = some au` path (`+0x038..+0x0bc: ldp, ret`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked59_auth_some (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked59Entry b abs entry)
    (g : Unchunked2PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (au : AuthenticatorPB)
    (hauth : auth = some au)
    (hauth_b : OptAuthBounds g auth)
    (hfit : unchunked2EncodedLen epoch auth < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (unchunked2Unpacked A g a epoch auth ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  subst hauth
  unchunked59_fetches_range_cli b (Rust.withPanics abs) entry hfn 56 192
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  obtain ⟨_, _, hroot_beq, hroot_bne, hmac_beq, hmac_bne⟩ := hauth_b.2.2 au rfl
  have hauth_fit : optAuthenticatorPBFieldEncodedLen (some au) < 2 ^ 64 := by
    unfold unchunked2EncodedLen at hfit
    omega
  have hbody_lt : authenticatorPBEncodedLen au < 2 ^ 64 := by
    dsimp [optAuthenticatorPBFieldEncodedLen] at hauth_fit
    omega
  have htot := bv_optAuthField_some au
  have hcmp := cmp_ls_false_of_lt
    (vlen := varintLen (BitVec.ofNat 64 (authenticatorPBEncodedLen au)))
    (tot := optAuthenticatorPBFieldEncodedLen (some au))
    (by dsimp [optAuthenticatorPBFieldEncodedLen]; omega) hauth_fit
  rcases hcmp with ⟨hcmp1, hcmp2, hcmp3, hcmp4, hcmp5⟩
  obtain ⟨hadd_final, hccf1, hccf2, hccf3, hccf4⟩ :=
    adds_no_overflow_of_eq (a := optAuthenticatorPBFieldEncodedLen (some au))
      (b := u64VarintFieldEncodedLen epoch)
      (c := unchunked2EncodedLen epoch (some au)) rfl hfit
  subst hP
  have hP1 : unchunked2Unpacked A g a epoch (some au) =
      (a ↦₆₄ g.rootKey.cap) ∗ ((a + 8#64) ↦₆₄ g.rootKey.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 au.rootKey.length) ∗
      vecU8Buf A g.rootKey.cap g.rootKey.ptr au.rootKey ∗
      ((a + 24#64) ↦₆₄ g.macKey.cap) ∗ ((a + 32#64) ↦₆₄ g.macKey.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 au.macKey.length) ∗
      vecU8Buf A g.macKey.cap g.macKey.ptr au.macKey ∗
      ((a + 48#64) ↦₆₄ epoch) := by
    simp only [unchunked2Unpacked, optAuthCap, optAuthPayload, arm64_norm]
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
      apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      apply SepWPp.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by epochEncLen_cc_close)
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      have hbody_01 : bytesFieldEncodedLen au.macKey = authenticatorPBEncodedLen au := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre]
      apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      apply SepWPp.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by epochEncLen_cc_close)
  | false =>
    have henc_r := bv_bytesField_nonempty hre
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_10 : bytesFieldEncodedLen au.rootKey = authenticatorPBEncodedLen au := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hme]
      apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      apply SepWPp.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by epochEncLen_cc_close)
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
        adds_no_overflow_of_eq (a := bytesFieldEncodedLen au.macKey)
          (b := bytesFieldEncodedLen au.rootKey)
          (c := authenticatorPBEncodedLen au) rfl hbody_lt
      apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      apply SepWPp.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by epochEncLen_cc_close)

/-- Shared `subroutine_ok` proof for all 6 functions in the 59-insn group. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked59_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked59Entry b ext entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (unchunked2EncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, epoch, auth⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [unchunked2EncodedLenPinnedSpec, unchunked2PinnedAt_eq_unpacked,
    unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have hmem0 : s0.mem ⊨
      (unchunked2Unpacked A g a epoch auth ∗
        ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre using 1; ac_rfl
  have hauth_b := unchunked2Unpacked_bounds hpre
  refine ⟨(unchunked2Unpacked A g a epoch auth ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rwa [sepConj_emp], ?_⟩
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked59_epoch (F := R) b A ext entry hfn g a s0.sp v16 v8 epoch auth
    hauth_b hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  rcases auth with _ | au
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked59_auth_none (F := R) b A ext entry hfn g a s0.sp epoch none rfl
      hpc1 hrun1 hsp1 halign hx8_1 hcs1 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked2EncodedLenPinnedSpec, unchunked2PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  · simp only [Option.isSome_some, ↓reduceIte] at hpc1
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked59_auth_some (F := R) b A ext entry hfn g a s0.sp epoch (some au) au
      rfl hauth_b hfit hpc1 hrun1 hsp1 halign hx0_1 hx8_1 hcs1 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked2EncodedLenPinnedSpec, unchunked2PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

private theorem subroutine_ok_repack {G1 G2 : Type} {prog : Program} {entry : BitVec 64}
    {S1 : Spec G1} {S2 : Spec G2} (f : G2 → G1)
    (hpre : ∀ x s, S2.pre x s = S1.pre (f x) s)
    (hpost : ∀ x s0 sf, S2.post x s0 sf = S1.post (f x) s0 sf)
    (hok : subroutine_ok prog entry S1)
    (honPanic : ∀ x s0 sf, S2.onPanic x s0 sf = S1.onPanic (f x) s0 sf := by intros; rfl)
    (honExit : ∀ x c s0 sf, S2.onExit x c s0 sf = S1.onExit (f x) c s0 sf := by intros; rfl)
    (honOom : ∀ x s0 sf, S2.onOom x s0 sf = S1.onOom (f x) s0 sf := by intros; rfl) :
    subroutine_ok prog entry S2 := by
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

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.KeysUnsampledEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.keysUnsampledEncodedLenLocal1Name) (keysUnsampledEncodedLenPinnedSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.keysUnsampledEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : CryptoVerification.Cli.SpqrV1.ProtoRepr.KeysUnsampledEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked59_entry_pinned_ok_ext b A ext _ (Or.inl rfl))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.NoHeaderReceivedEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.noHeaderReceivedEncodedLenLocal1Name) (noHeaderReceivedEncodedLenPinnedSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.noHeaderReceivedEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : CryptoVerification.Cli.SpqrV1.ProtoRepr.NoHeaderReceivedEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl))))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct2SentEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.ct2SentEncodedLenLocal1Name) (ct2SentEncodedLenPinnedSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ct2SentEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : CryptoVerification.Cli.SpqrV1.ProtoRepr.Ct2SentEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

/-- Entry address predicate for all 4 functions in the 71-insn group. -/
def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked71Entry (b : BitVec 64) (abs : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr ekSentEncodedLenLocal2Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.headerReceivedEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr headerReceivedEncodedLenLocal2Name = entry

open Lean Elab Tactic in
elab "unchunked71_fetches_range_cli " b:term:max H:term:max _entry:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let portEnv ← Lean.getEnv
  let portOpts ← Lean.getOptions
  let portNs ← Lean.getCurrNamespace
  let portOd ← Lean.getOpenDecls
  let offs := #[(num% (ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSent as prost::message::Message>::encoded_len [local#3]")), 0x64d94, (num% (ls_off% "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]")), 0x626c4]
  let fnOffs := #[
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSent as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x64d94,
    mkIdent (← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#3]").decl,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x626c4
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let decs := offs.map fun off =>
      mkIdent (portCliPickCli portEnv portOpts portNs portOd (`CryptoVerification.SpqrV1.ProtoRepr |>.str
        s!"spqrUnchunked71BinCli_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"))
    let d0 := decs[0]!; let d1 := decs[1]!; let d2 := decs[2]!; let d3 := decs[3]!
    let f0 := fnOffs[0]!; let f1 := fnOffs[1]!; let f2 := fnOffs[2]!; let f3 := fnOffs[3]!
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := unchunked71_fetch_entry $hfn
          ($fetchEntry (b := $b) (H := $H) $f0 (by decide) $d0)
          ($fetchEntry (b := $b) (H := $H) $f1 (by decide) $d1)
          ($fetchEntry (b := $b) (H := $H) $f2 (by decide) $d2)
          ($fetchEntry (b := $b) (H := $H) $f3 (by decide) $d3)))
    else
      evalTactic (← `(tactic|
        have := unchunked71_fetch_add $hfn (k := $kq)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f0 (by decide) $d0)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f1 (by decide) $d1)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f2 (by decide) $d2)
          ($fetchAdd (b := $b) (H := $H) (k := $kq) $f3 (by decide) $d3)))

/-- Prologue + `epoch` field length (`+0x000..+0x034`), branching to `+0x038` (`entry + 56#64`)
    when `auth.isSome` or `+0x0bc` (`entry + 188#64`) when `auth = none`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked71_epoch (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked71Entry b abs entry)
    (g : Unchunked3PBGhost) (a sp v16 v8 : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 : List (BitVec 8))
    (hauth_b : OptAuthBounds g.auth auth)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (unchunked3Unpacked A g a epoch auth f3 ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if auth.isSome then entry + 56#64 else entry + 188#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm
        ((unchunked3Unpacked A g a epoch auth f3 ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  unchunked71_fetches_range_cli b (Rust.withPanics abs) entry hfn 0 56
  obtain ⟨hcap_beq, hcap_bne, _⟩ := hauth_b
  subst hP
  have hP1 : unchunked3Unpacked A g a epoch auth f3 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ optAuthCap g.auth auth) ∗
      optAuthPayload A g.auth (a + 24#64) auth ∗
      ((a + 72#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  by_cases hep : epoch = 0#64
  · apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen])
      (by simp_all [EpochEncLenCalleeSaved])
  · have hep_beq : (epoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep
    have hep_bne : (epoch != 0#64) = true := bne_iff_ne.mpr hep
    have henc := bv_u64VarintField_nonzero hep
    apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

/-- `auth = none` path (`+0x0bc..+0x0c0` -> `+0x0c4` = `entry + 196#64`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked71_auth_none (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked71Entry b abs entry)
    (g : Unchunked3PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 : List (BitVec 8))
    (hauth : auth = none)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 188#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked3Unpacked A g a epoch auth f3 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 196#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  subst hauth
  unchunked71_fetches_range_cli b (Rust.withPanics abs) entry hfn 188 196
  have hlen_eq : unchunked2EncodedLen epoch none = u64VarintFieldEncodedLen epoch := by
    simp [unchunked2EncodedLen, optAuthenticatorPBFieldEncodedLen]
  subst hP
  apply SepWPp.of_sepWP (mid := entry + 196#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- `auth = some au` path (`+0x038..+0x0b4` -> `+0x0c4` = `entry + 196#64`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked71_auth_some (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked71Entry b abs entry)
    (g : Unchunked3PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (au : AuthenticatorPB)
    (f3 : List (BitVec 8))
    (hauth : auth = some au)
    (hauth_b : OptAuthBounds g.auth auth)
    (hfit : unchunked2EncodedLen epoch auth < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked3Unpacked A g a epoch auth f3 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 196#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b abs) ret s P Q Qp := by
  subst hauth
  unchunked71_fetches_range_cli b (Rust.withPanics abs) entry hfn 56 184
  obtain ⟨_, _, hroot_beq, hroot_bne, hmac_beq, hmac_bne⟩ := hauth_b.2.2 au rfl
  have hauth_fit : optAuthenticatorPBFieldEncodedLen (some au) < 2 ^ 64 := by
    unfold unchunked2EncodedLen at hfit
    omega
  have hbody_lt : authenticatorPBEncodedLen au < 2 ^ 64 := by
    dsimp [optAuthenticatorPBFieldEncodedLen] at hauth_fit
    omega
  have htot := bv_optAuthField_some au
  have hcmp := cmp_ls_false_of_lt
    (vlen := varintLen (BitVec.ofNat 64 (authenticatorPBEncodedLen au)))
    (tot := optAuthenticatorPBFieldEncodedLen (some au))
    (by dsimp [optAuthenticatorPBFieldEncodedLen]; omega) hauth_fit
  rcases hcmp with ⟨hcmp1, hcmp2, hcmp3, hcmp4, hcmp5⟩
  obtain ⟨hadd_final, hccf1, hccf2, hccf3, hccf4⟩ :=
    adds_no_overflow_of_eq (a := optAuthenticatorPBFieldEncodedLen (some au))
      (b := u64VarintFieldEncodedLen epoch)
      (c := unchunked2EncodedLen epoch (some au)) rfl hfit
  subst hP
  have hP1 : unchunked3Unpacked A g a epoch (some au) f3 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.auth.rootKey.cap) ∗ ((a + 32#64) ↦₆₄ g.auth.rootKey.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 au.rootKey.length) ∗
      vecU8Buf A g.auth.rootKey.cap g.auth.rootKey.ptr au.rootKey ∗
      ((a + 48#64) ↦₆₄ g.auth.macKey.cap) ∗ ((a + 56#64) ↦₆₄ g.auth.macKey.ptr) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 au.macKey.length) ∗
      vecU8Buf A g.auth.macKey.cap g.auth.macKey.ptr au.macKey ∗
      ((a + 72#64) ↦₆₄ epoch) := by
    simp only [unchunked3Unpacked, optAuthCap, optAuthPayload, arm64_norm]
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
          (b := bytesFieldEncodedLen au.rootKey)
          (c := authenticatorPBEncodedLen au) rfl hbody_lt
      apply SepWPp.of_sepWP (mid := entry + 196#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- Tag-3 `f3: Vec<u8>` field length + epilogue (`+0x0c4..+0x0f4: ldp, ret`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked71_f3 (b : BitVec 64) (A : RustAlloc)
    (abs : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked71Entry b abs entry)
    (g : Unchunked3PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 : List (BitVec 8))
    (hf3_b : VecU8FieldBounds f3)
    (hfit : unchunked3EncodedLen epoch auth f3 < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 196#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (unchunked3Unpacked A g a epoch auth f3 ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b abs) (s0.readReg64 .lr) s P Q Qp := by
  unchunked71_fetches_range_cli b (Rust.withPanics abs) entry hfn 196 248
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  obtain ⟨_, hf3_beq, hf3_bne⟩ := hf3_b
  subst hP
  have hP1 : unchunked3Unpacked A g a epoch auth f3 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ optAuthCap g.auth auth) ∗
      optAuthPayload A g.auth (a + 24#64) auth ∗
      ((a + 72#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f3.isEmpty with
  | true =>
    have hf_len : f3.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq : unchunked2EncodedLen epoch auth = unchunked3EncodedLen epoch auth f3 := by
      simp [unchunked2EncodedLen, unchunked3EncodedLen, bytesFieldEncodedLen, hfe]
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
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f3)
        (b := unchunked2EncodedLen epoch auth)
        (c := unchunked3EncodedLen epoch auth f3) rfl hfit
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)

/-- Shared `subroutine_ok` proof for all 4 functions in the 71-insn group. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked71_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn : CryptoVerification.Cli.SpqrV1.ProtoRepr.IsUnchunked71Entry b ext entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (unchunked3EncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, epoch, auth, f3⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [unchunked3EncodedLenPinnedSpec, unchunked3PinnedAt_eq_unpacked,
    unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have hfit2 : unchunked2EncodedLen epoch auth < 2 ^ 64 := by
    unfold unchunked3EncodedLen unchunked2EncodedLen at *; omega
  have hmem0 : s0.mem ⊨
      (unchunked3Unpacked A g a epoch auth f3 ∗
        ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre using 1; ac_rfl
  obtain ⟨hauth_b, hf3_b⟩ := unchunked3Unpacked_bounds hpre
  refine ⟨(unchunked3Unpacked A g a epoch auth f3 ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rwa [sepConj_emp], ?_⟩
  refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked71_epoch (F := R) b A ext entry hfn g a s0.sp v16 v8 epoch auth f3
    hauth_b hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
  rcases auth with _ | au
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked71_auth_none (F := FSave) b A ext entry hfn g a epoch none f3 rfl
      hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    have hsp2' : s2.sp = s0.sp - 16#64 := by rw [hsp2, hsp1]
    have hcs2' : EpochEncLenCalleeSaved s0 s2 := hcs1.trans hcs2
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked71_f3 (F := R) b A ext entry hfn g a s0.sp epoch none f3
      hf3_b hfit hpc2 hrun2 hsp2' halign hx0_2 hx8_2 hcs2' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked3EncodedLenPinnedSpec, unchunked3PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  · simp only [Option.isSome_some, ↓reduceIte] at hpc1
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked71_auth_some (F := FSave) b A ext entry hfn g a epoch (some au) au f3
      rfl hauth_b hfit2 hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    have hsp2' : s2.sp = s0.sp - 16#64 := by rw [hsp2, hsp1]
    have hcs2' : EpochEncLenCalleeSaved s0 s2 := hcs1.trans hcs2
    refine CryptoVerification.Cli.SpqrV1.ProtoRepr.step_unchunked71_f3 (F := R) b A ext entry hfn g a s0.sp epoch (some au) f3
      hf3_b hfit hpc2 hrun2 hsp2' halign hx0_2 hx8_2 hcs2' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked3EncodedLenPinnedSpec, unchunked3PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentEncodedLenLocal1Name) (ekSentEncodedLenPinnedSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : CryptoVerification.Cli.SpqrV1.ProtoRepr.EkSentEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked71_entry_pinned_ok_ext b A ext _ (Or.inl rfl))

def _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderReceivedEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.ProtoRepr.headerReceivedEncodedLenLocal1Name) (headerReceivedEncodedLenPinnedSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.ProtoRepr.headerReceivedEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : CryptoVerification.Cli.SpqrV1.ProtoRepr.HeaderReceivedEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (CryptoVerification.Cli.SpqrV1.ProtoRepr.unchunked71_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl))))

end CryptoVerification.SpqrV1.ProtoRepr

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SameAccount
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Defs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.TryDecryptStateRatchetCoins
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSteps
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSteps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# CLI Ratchet Entry Segment `S0` under Distinct Account Identities

Layout-independent CLI proof of `<IdentityKey>::is_same_account` under `DistinctSid` and the initial
ratchet segment `S0` (`s0_ok_P`, `seedsLen32_of_pre_P`) for `try_decrypt` under
`remote ≠ local ∨ DistinctSid`, parameterized over arbitrary external hooks `ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.WireEntries

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoGames
open CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `<IdentityKey>::is_same_account` under `DistinctSid` -/

private theorem memRegion_16_eq_stackFrameFor_eq_cli (sp : BitVec 64) :
    memRegion (sp - 16#64) 16 =
      stackFrameFor libsignalSessionImage
        "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp := by
  rw [show (16 : Nat) = 8 * 2 by rfl, ProofLib.memRegion_cells (sp - 16#64) 2 (by decide)]
  cells_unfold
  simp only [stackFrameFor,
    (ls_lemma% frameBytes "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq"),
    reduceStackFrameAt]

private theorem memRegion_48_eq_stackFrameFor_ct_eq_cli (sp : BitVec 64) :
    memRegion (sp - 48#64) 48 =
      stackFrameFor libsignalSessionImage
        "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp := by
  rw [show (48 : Nat) = 8 * 6 by rfl, ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]
  cells_unfold
  simp only [stackFrameFor,
    (ls_lemma% frameBytes "<[u8] as subtle::ConstantTimeEq>::ct_eq"),
    reduceStackFrameAt]

private theorem stackAt_parseSidStack_eq_publicKeyEq_cli (sp : BitVec 64) :
    stackAt sp parseSidStack =
      memRegion (sp - 16#64) 16 ∗
      memRegion (sp - 16#64 - 48#64) 48 ∗
      memRegion (sp - 272#64) 208 := by
  simp only [stackAt, parseSidStack, uuidTryParseStack]
  have h64 : sp - 16#64 - 48#64 = sp - 64#64 := by bv_omega
  rw [h64,
      show (80 + 192 : Nat) = 272 from rfl,
      show BitVec.ofNat 64 272 = 272#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 272#64) (b' := sp - 64#64) (N := 272) (n := 208) (k := 64)
        (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (b' := sp - 16#64) (N := 64) (n := 48) (k := 16)
        (by decide) (by bv_omega) (by decide)]
  ac_rfl

private def publicKeyEqMem80Spec_cli :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackAt sp parseSidStack
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackAt sp parseSidStack

private theorem publicKeyEqMem80_ok_at_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (hEq : PublicKeyEqOkExt b ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr isSameAccountName +
        bv% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
          ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"))
      publicKeyEqMem80Spec_cli := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr publicKeyEqName =
      (tripleRatchetProgAtExt b ext).fnAddr isSameAccountName +
        bv% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
          ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") :=
    Program.fnAddr_rel (b := b) (X := Rust.withPanics ext)
      (k := num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
        ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"))
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")
      (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")
      (by decide)
  have hEq' : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr isSameAccountName +
        bv% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
          ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"))
      publicKeyEqSpec :=
    hrel.rec (motive := fun a _ => subroutine_ok (tripleRatchetProgAtExt b ext) a publicKeyEqSpec) hEq
  refine subroutine_ok_map hEq' ?_
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), memRegion (sp - 272#64) 208 ∗ R, ?_, ?_⟩
  · simp only [CryptoVerification.LibsignalTripleRatchet.Getters.publicKeyEqSpec,
      publicKeyEqMem80Spec_cli,
      stackAt_parseSidStack_eq_publicKeyEq_cli sp,
      ← memRegion_16_eq_stackFrameFor_eq_cli sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq_cli (sp - 16#64)] at hpre ⊢
    exact Satisfies.of_eq hpre (by ac_rfl)
  · intro sf hpost
    simp only [CryptoVerification.LibsignalTripleRatchet.Getters.publicKeyEqSpec,
      publicKeyEqMem80Spec_cli,
      stackAt_parseSidStack_eq_publicKeyEq_cli sp,
      ← memRegion_16_eq_stackFrameFor_eq_cli sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq_cli (sp - 16#64)] at hpost ⊢
    exact Satisfies.of_eq hpost (by ac_rfl)

private theorem memRegion_17_eq_cells_cli (a : BitVec 64) :
    memRegion a 17 =
      ∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  rw [show (17 : Nat) = 1 + (8 + 8) by decide,
    memRegion_split a 1 (8 + 8) (by decide),
    memRegion_split (a + 1#64) 8 8 (by decide),
    memRegion_one a, ProofLib.memRegion_eight (a + 1#64),
    ProofLib.memRegion_eight (a + 1#64 + 8#64)]
  have h9 : a + 1#64 + 8#64 = a + 9#64 := by bv_arith
  rw [h9, sepExists_sepConj_left]
  refine congrArg sepExists (funext fun b0 => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun w0 => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

private theorem pointsTo_17_entails_memRegion_cli (a : BitVec 64) (b0 : BitVec 8) (w0 w1 : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1)) ⊢ memRegion a 17 := by
  rw [memRegion_17_eq_cells_cli a]
  exact Entails.sepExists_right b0 (Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.refl _)))

private theorem memRegion_16_out_split_cli (a : BitVec 64) :
    memRegion (a + 1#64) 16 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  rw [show (16 : Nat) = 8 + 8 by decide, memRegion_split (a + 1#64) 8 8 (by decide)]
  have h9 : a + 1#64 + BitVec.ofNat 64 8 = a + 9#64 := by bv_arith
  rw [h9, ProofLib.memRegion_eight (a + 1#64), ProofLib.memRegion_eight (a + 9#64),
    sepExists_sepConj_left]
  refine congrArg sepExists (funext fun w0 => ?_)
  rw [sepExists_sepConj_right]

private theorem parseSidResultAt_entails_rel_cells_cli (out : BitVec 64)
    (res : Option (Bool × List.Vector (BitVec 8) 16)) :
    parseSidResultAt out res ⊢
      ∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ⌜SidCellsRel res b0 w0 w1⌝ ∗
        (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) := by
  cases res with
  | none =>
    simp only [parseSidResultAt, SidCellsRel, memRegion_16_out_split_cli,
      sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w1
    refine Entails.sepExists_right 2#8 (Entails.sepExists_right w0 (Entails.sepExists_right w1 ?_))
    exact Entails.pure_right rfl (Entails.of_eq (by ac_rfl))
  | some val =>
    rcases val with ⟨pni, uuid⟩
    rw [ParseServiceId.parseSidResultAt_some_eq out pni uuid]
    exact Entails.sepExists_right (kindByte pni)
      (Entails.sepExists_right (ParseServiceId.uuidWord0 uuid)
        (Entails.sepExists_right (ParseServiceId.uuidWord1 uuid)
          (Entails.pure_right ⟨rfl, rfl, rfl⟩ (Entails.refl _))))

private abbrev ParseSidRelGhost_cli :=
  BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 8 × BitVec 64 × BitVec 64

private def parseSidRelSpec_cli (parse : UuidParser) : Spec ParseSidRelGhost_cli where
  pre := fun (p, bs, out, b0, w0, w1) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) ∗
      stackAt s.sp parseSidStack
  post := fun (p, bs, out, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      (∃∗ b0' : BitVec 8, ∃∗ w0' : BitVec 64, ∃∗ w1' : BitVec 64,
        ⌜SidCellsRel (serviceIdParse parse bs) b0' w0' w1'⌝ ∗
        (out ↦₈ b0') ∗ ((out + 1#64) ↦₆₄ w0') ∗ ((out + 9#64) ↦₆₄ w1')) ∗
      stackAt s0.sp parseSidStack

private theorem parseSidRel_ok_at_ext (b : BitVec 64)
    (ext : String → Option (State → State))
    (hParse : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr parseSidName)
      (parseSidCodeSpec uuidTryParse)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr isSameAccountName +
        bv% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string" -
          ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"))
      (parseSidRelSpec_cli uuidTryParse) := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr parseSidName =
      (tripleRatchetProgAtExt b ext).fnAddr isSameAccountName +
        bv% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string" -
          ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") :=
    Program.fnAddr_rel (b := b) (X := Rust.withPanics ext)
      (k := num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string" -
        ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"))
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")
      (ls_lemma% fnOff "<libsignal_core::address::ServiceId>::parse_from_service_id_string")
      (by decide)
  have hps : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr isSameAccountName +
        bv% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string" -
          ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"))
      (parseSidCodeSpec uuidTryParse) :=
    hrel.rec
      (motive := fun a _ => subroutine_ok (tripleRatchetProgAtExt b ext) a (parseSidCodeSpec uuidTryParse))
      hParse
  refine subroutine_ok_map hps ?_
  rintro ⟨p, bs, out, b0, w0, w1⟩ R s0 hpre
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · simp only [parseSidRelSpec_cli, parseSidCodeSpec, parseSidSpec] at hpre ⊢
    have hm : s0.mem ⊨ ((out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1)) ∗
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧ s0.readReg64 .x8 = out⌝ ∗
          (p ↦ₛ bs) ∗ stackAt s0.sp parseSidStack ∗ R) :=
      Satisfies.of_eq hpre (by ac_rfl)
    have hm' :=
      Arm64.Satisfies.mono (sepConj_mono_left (pointsTo_17_entails_memRegion_cli out b0 w0 w1)) hm
    exact Satisfies.of_eq hm' (by ac_rfl)
  · simp only [parseSidCodeSpec, parseSidSpec, parseSidRelSpec_cli] at hpost ⊢
    have hm : sf.mem ⊨ parseSidResultAt out (serviceIdParse uuidTryParse bs) ∗
        (⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗ stackAt s0.sp parseSidStack ∗ R) :=
      Satisfies.of_eq hpost (by ac_rfl)
    have hm' :=
      Arm64.Satisfies.mono (sepConj_mono_left (parseSidResultAt_entails_rel_cells_cli out _)) hm
    exact Satisfies.of_eq hm' (by ac_rfl)

private theorem stackAt_isSameAccountDistinct_split_cli (sp : BitVec 64) :
    stackAt sp isSameAccountDistinctStack =
      stackAt (sp - 80#64) parseSidStack ∗
      memRegion (sp - 80#64) 12 ∗
      (∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 68#64) ↦₈ b0) ∗ ((sp - 67#64) ↦₆₄ w0) ∗ ((sp - 59#64) ↦₆₄ w1)) ∗
      memRegion (sp - 51#64) 3 ∗
      ProofLib.cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountDistinctStack, parseSidStack, uuidTryParseStack]
  rw [show (80 + (80 + 192) : Nat) = 352 from rfl,
      show (80 + 192 : Nat) = 272 from rfl,
      show BitVec.ofNat 64 352 = 352#64 from rfl,
      show BitVec.ofNat 64 272 = 272#64 from rfl,
      show sp - 80#64 - 272#64 = sp - 352#64 by bv_arith,
      show (352 : Nat) = 272 + (12 + (17 + (3 + 8 * 6))) by decide,
      memRegion_split (sp - 352#64) 272 (12 + (17 + (3 + 8 * 6))) (by decide),
      memRegion_split (sp - 352#64 + 272#64) 12 (17 + (3 + 8 * 6)) (by decide),
      memRegion_split (sp - 352#64 + 272#64 + 12#64) 17 (3 + 8 * 6) (by decide),
      memRegion_split (sp - 352#64 + 272#64 + 12#64 + 17#64) 3 (8 * 6) (by decide),
      ProofLib.memRegion_cells _ 6 (by decide),
      memRegion_17_eq_cells_cli]
  have h1 : sp - 352#64 + 272#64 = sp - 80#64 := by bv_arith
  have h2 : sp - 80#64 + 12#64 = sp - 68#64 := by bv_arith
  have h3 : sp - 68#64 + 1#64 = sp - 67#64 := by bv_arith
  have h4 : sp - 68#64 + 9#64 = sp - 59#64 := by bv_arith
  have h5 : sp - 68#64 + 17#64 = sp - 51#64 := by bv_arith
  have h6 : sp - 51#64 + 3#64 = sp - 48#64 := by bv_arith
  rw [h1, h2, h3, h4, h5, h6]

private theorem pack64_b0 (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    BitVec.extractLsb' 0 8 (pack64 x0 x1 x2 x3 x4 x5 x6 x7) = x0 := by unfold pack64; bv_kernel
private theorem pack64_b1 (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    BitVec.extractLsb' 8 8 (pack64 x0 x1 x2 x3 x4 x5 x6 x7) = x1 := by unfold pack64; bv_kernel
private theorem pack64_b2 (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    BitVec.extractLsb' 16 8 (pack64 x0 x1 x2 x3 x4 x5 x6 x7) = x2 := by unfold pack64; bv_kernel
private theorem pack64_b3 (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    BitVec.extractLsb' 24 8 (pack64 x0 x1 x2 x3 x4 x5 x6 x7) = x3 := by unfold pack64; bv_kernel
private theorem pack64_b4 (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    BitVec.extractLsb' 32 8 (pack64 x0 x1 x2 x3 x4 x5 x6 x7) = x4 := by unfold pack64; bv_kernel
private theorem pack64_b5 (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    BitVec.extractLsb' 40 8 (pack64 x0 x1 x2 x3 x4 x5 x6 x7) = x5 := by unfold pack64; bv_kernel
private theorem pack64_b6 (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    BitVec.extractLsb' 48 8 (pack64 x0 x1 x2 x3 x4 x5 x6 x7) = x6 := by unfold pack64; bv_kernel
private theorem pack64_b7 (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    BitVec.extractLsb' 56 8 (pack64 x0 x1 x2 x3 x4 x5 x6 x7) = x7 := by unfold pack64; bv_kernel

private theorem pack64_inj_cli (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h : pack64 a0 a1 a2 a3 a4 a5 a6 a7 = pack64 b0 b1 b2 b3 b4 b5 b6 b7) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 :=
  ⟨(pack64_b0 ..).symm.trans ((congrArg (BitVec.extractLsb' 0 8) h).trans (pack64_b0 ..)),
   (pack64_b1 ..).symm.trans ((congrArg (BitVec.extractLsb' 8 8) h).trans (pack64_b1 ..)),
   (pack64_b2 ..).symm.trans ((congrArg (BitVec.extractLsb' 16 8) h).trans (pack64_b2 ..)),
   (pack64_b3 ..).symm.trans ((congrArg (BitVec.extractLsb' 24 8) h).trans (pack64_b3 ..)),
   (pack64_b4 ..).symm.trans ((congrArg (BitVec.extractLsb' 32 8) h).trans (pack64_b4 ..)),
   (pack64_b5 ..).symm.trans ((congrArg (BitVec.extractLsb' 40 8) h).trans (pack64_b5 ..)),
   (pack64_b6 ..).symm.trans ((congrArg (BitVec.extractLsb' 48 8) h).trans (pack64_b6 ..)),
   (pack64_b7 ..).symm.trans ((congrArg (BitVec.extractLsb' 56 8) h).trans (pack64_b7 ..))⟩

private theorem uuid_eq_of_uuidWords_eq_cli {u1 u2 : List.Vector (BitVec 8) 16}
    (hw0 : ParseServiceId.uuidWord0 u1 = ParseServiceId.uuidWord0 u2)
    (hw1 : ParseServiceId.uuidWord1 u1 = ParseServiceId.uuidWord1 u2) :
    u1 = u2 := by
  rcases u1 with ⟨l1, hl1⟩
  rcases u2 with ⟨l2, hl2⟩
  rcases l1 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7,
    _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try cases hl1
  rcases l2 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try cases hl2
  simp only [ParseServiceId.uuidWord0, ParseServiceId.uuidWord1, List.Vector.toList, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hw0 hw1
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    pack64_inj_cli _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw0
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    pack64_inj_cli _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw1
  rfl

private theorem kindByte_inj_cli {p1 p2 : Bool} (h : kindByte p1 = kindByte p2) : p1 = p2 := by
  cases p1 <;> cases p2 <;> revert h <;> decide

private theorem sidCellsRel_ne_of_distinct_cli {parse : UuidParser} {bs1 bs2 : List (BitVec 8)}
    {b0_1 b0_2 : BitVec 8} {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hDist : DistinctSid parse bs1 bs2)
    (hrel1 : SidCellsRel (serviceIdParse parse bs1) b0_1 w0_1 w1_1)
    (hrel2 : SidCellsRel (serviceIdParse parse bs2) b0_2 w0_2 w1_2)
    (hb1 : b0_1 ≠ 2#8) (hb2 : b0_2 ≠ 2#8) (hkind : b0_1 = b0_2) :
    w0_1 = w0_2 ∧ w1_1 = w1_2 → False := by
  rintro ⟨hw0, hw1⟩
  cases hs1 : serviceIdParse parse bs1 with
  | none => rw [hs1, SidCellsRel] at hrel1; exact hb1 hrel1
  | some v1 =>
    rcases v1 with ⟨p1, u1⟩
    rw [hs1, SidCellsRel] at hrel1
    rcases hrel1 with ⟨hb0_1, hw0_1, hw1_1⟩
    cases hs2 : serviceIdParse parse bs2 with
    | none => rw [hs2, SidCellsRel] at hrel2; exact hb2 hrel2
    | some v2 =>
      rcases v2 with ⟨p2, u2⟩
      rw [hs2, SidCellsRel] at hrel2
      rcases hrel2 with ⟨hb0_2, hw0_2, hw1_2⟩
      have hp : p1 = p2 := kindByte_inj_cli (hb0_1.symm.trans (hkind.trans hb0_2))
      have hu : u1 = u2 := uuid_eq_of_uuidWords_eq_cli
        (hw0_1.symm.trans (hw0.trans hw0_2))
        (hw1_1.symm.trans (hw1.trans hw1_2))
      subst hp hu
      exact hDist (p1, u1) hs1 hs2

private theorem cond_uuid_words_ne_cli {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hne : w0_1 = w0_2 ∧ w1_1 = w1_2 → False) :
    (if (w0_1 == w0_2) = true then w1_1 != w1_2 else true) = true := by
  by_cases h0 : (w0_1 == w0_2) = true
  · simp only [h0, ↓reduceIte, bne_iff_ne]
    intro h1
    exact hne ⟨of_decide_eq_true h0, h1⟩
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountDistinctRaw_ok_ext
    (b : BitVec 64) (ext : String → Option (State → State))
    (hEq : PublicKeyEqOkExt b ext)
    (hParseSid : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr parseSidName)
      (parseSidCodeSpec uuidTryParse)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr isSameAccountName)
      (isSameAccountDistinctRawSpec uuidTryParse) := by
  simp only [isSameAccountDistinctRawSpec]
  have hEq' := publicKeyEqMem80_ok_at_ext b ext hEq
  simp only [publicKeyEqMem80Spec_cli] at hEq'
  have hParse := parseSidRel_ok_at_ext b ext hParseSid
  simp only [parseSidRelSpec_cli] at hParse
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")) 192
  dsimp only [tripleRatchetProgAtExt, isSameAccountName, BitVec.ofNat_eq_ofNat] at hEq' hParse ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::identity_key::IdentityKey>::is_same_account" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨localIkA, localIk, localAddr, localNamePtr, localNameBytes,
    remoteIkA, remoteIk, remoteAddr, remoteNamePtr, remoteNameBytes⟩ := x
  dsimp only at *
  have h_or : localIk ≠ remoteIk ∨ DistinctSid uuidTryParse localNameBytes remoteNameBytes := h
  subst h_1 h_2 h_3 h_4
  rw [stackAt_isSameAccountDistinct_split_cli s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b0_init
  apply SepWP.exists_elim; intro w0_init
  apply SepWP.exists_elim; intro w1_init
  cells_unfold
  wp_pull_exists
  wp_steps
  wp_call hEq' (s0.readReg64 (Reg.gpr 0#5), localIk.publicKey,
    s0.readReg64 (Reg.gpr 2#5), remoteIk.publicKey, s0.sp - 80#64)
  by_cases hpk : (localIk.publicKey == remoteIk.publicKey) = true
  · have hik_eq : localIk = remoteIk := by
      cases localIk; cases remoteIk
      have hpk' := of_decide_eq_true hpk
      subst hpk'; rfl
    have hDist : DistinctSid uuidTryParse localNameBytes remoteNameBytes :=
      h_or.resolve_left (not_not.mpr hik_eq)
    simp only [hpk, ↓reduceIte] at *
    wp_steps
    wp_call hParse
    wp_steps
    wp_if hb0
    · wp_steps
      wp_call hParse
      wp_steps
      wp_if hb1
      · wp_steps
        wp_done
      · wp_steps
        wp_if hb01
        · wp_steps
          wp_done
        · wp_steps
          have hrel1 : SidCellsRel (serviceIdParse uuidTryParse localNameBytes) _ _ _ := ‹_›
          have hrel2 : SidCellsRel (serviceIdParse uuidTryParse remoteNameBytes) _ _ _ := ‹_›
          have hne := cond_uuid_words_ne_cli (sidCellsRel_ne_of_distinct_cli hDist hrel1 hrel2
            (by clear * - hb0; bv_omega) (by clear * - hb1; bv_omega) (by clear * - hb01; bv_omega))
          wp_done
    · wp_steps
      wp_done
  · simp only [hpk, Bool.false_eq_true, ↓reduceIte] at *
    wp_steps
    wp_done

private def vecU8BufRest_cli (A : RustAlloc) (cap ptr : BitVec 64) (n : Nat) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 n) (cap.toNat - n)

private theorem vecU8At_buf_eq_cli (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (ptr ↦ₛ bs) ∗ vecU8BufRest_cli A cap ptr bs.length := by
  unfold vecU8BufRest_cli
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst hbs
    simp [pointsToBytes_nil]
  · simp only [hcap, ite_false]
    ac_rfl

private theorem vecU8At_expose_cli (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8BufRest_cli A cap ptr bs.length := by
  unfold vecU8At vecHeader
  trans (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      if cap = 0 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)))
  · ac_rfl
  · simp only [pure_sepConj]
    congr 1
    funext h
    apply propext
    refine and_congr_right fun ⟨hle, _, _⟩ => ?_
    rw [vecU8At_buf_eq_cli A cap ptr bs hle]

private def addrRest_cli (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ g.name.cap) ∗ vecU8BufRest_cli A g.name.cap g.name.ptr g.name.bytes.length ∗
    ((a + 24#64) ↦₈ g.device) ∗ memRegion (a + 0x19#64) 7

private theorem protocolAddressAt_expose_cli (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a =
      ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        addrRest_cli A g a := by
  unfold protocolAddressAt vecGhostAt addrRest_cli
  rw [vecU8At_expose_cli]
  ac_rfl

/-- `ext`-generic `subroutine_ok` predicate for `<IdentityKey>::is_same_account` under `DistinctSid`. -/
def _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.IsSameAccountDistinctOkExt
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr isSameAccountName)
    (isSameAccountDistinctSpec A uuidTryParse)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok_ext
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hEq : PublicKeyEqOkExt b ext)
    (hParseSid : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr parseSidName)
      (parseSidCodeSpec uuidTryParse)) :
    CryptoVerification.Cli.E2E.Pqxdh.WireEntries.IsSameAccountDistinctOkExt b A ext := by
  refine subroutine_ok_map
    (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountDistinctRaw_ok_ext b ext hEq hParseSid) ?_
  rintro ⟨localIkA, localIk, locA, loc, remoteIkA, remoteIk, remA, rem⟩ R s0 hpre
  simp only [isSameAccountDistinctSpec, protocolAddressAt_expose_cli] at hpre
  have hpre' : s0.mem ⊨
      ⌜s0.readReg64 .x0 = localIkA ∧ s0.readReg64 .x1 = locA ∧
        s0.readReg64 .x2 = remoteIkA ∧ s0.readReg64 .x3 = remA ∧
        (localIk ≠ remoteIk ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)⌝ ∗
      (⌜loc.name.bytes.length ≤ loc.name.cap.toNat ∧ loc.name.cap.toNat < 2 ^ 63 ∧
        loc.name.ptr ≠ 0⌝ ∗
        (⌜rem.name.bytes.length ≤ rem.name.cap.toNat ∧ rem.name.cap.toNat < 2 ^ 63 ∧
          rem.name.ptr ≠ 0⌝ ∗
          ((localIkA ↦ₛ localIk.publicKey.bytes.toList) ∗
           ((locA + 8#64) ↦₆₄ loc.name.ptr) ∗
           ((locA + 16#64) ↦₆₄ BitVec.ofNat 64 loc.name.bytes.length) ∗
           (loc.name.ptr ↦ₛ loc.name.bytes) ∗
           (remoteIkA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
           ((remA + 8#64) ↦₆₄ rem.name.ptr) ∗
           ((remA + 16#64) ↦₆₄ BitVec.ofNat 64 rem.name.bytes.length) ∗
           (rem.name.ptr ↦ₛ rem.name.bytes) ∗
           stackAt s0.sp isSameAccountDistinctStack ∗
           addrRest_cli A loc locA ∗ addrRest_cli A rem remA ∗ R))) :=
    Satisfies.of_eq hpre (by ac_rfl)
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1, hx2, hx3, hdist⟩, hpre'⟩
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hloc_pure, hpre'⟩
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hrem_pure, hm⟩
  refine ⟨⟨localIkA, localIk, locA, loc.name.ptr, loc.name.bytes,
    remoteIkA, remoteIk, remA, rem.name.ptr, rem.name.bytes⟩,
    addrRest_cli A loc locA ∗ addrRest_cli A rem remA ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [isSameAccountDistinctRawSpec]
    have hloc_lt : loc.name.bytes.length < 2 ^ 64 := by omega
    have hrem_lt : rem.name.bytes.length < 2 ^ 64 := by omega
    have hm' : s0.mem ⊨
        ⌜s0.readReg64 .x0 = localIkA ∧ s0.readReg64 .x1 = locA ∧
          s0.readReg64 .x2 = remoteIkA ∧ s0.readReg64 .x3 = remA ∧
          loc.name.bytes.length < 2 ^ 64 ∧ rem.name.bytes.length < 2 ^ 64 ∧
          (localIk ≠ remoteIk ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)⌝ ∗
        ((localIkA ↦ₛ localIk.publicKey.bytes.toList) ∗
         ((locA + 8#64) ↦₆₄ loc.name.ptr) ∗
         ((locA + 16#64) ↦₆₄ BitVec.ofNat 64 loc.name.bytes.length) ∗
         (loc.name.ptr ↦ₛ loc.name.bytes) ∗
         (remoteIkA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
         ((remA + 8#64) ↦₆₄ rem.name.ptr) ∗
         ((remA + 16#64) ↦₆₄ BitVec.ofNat 64 rem.name.bytes.length) ∗
         (rem.name.ptr ↦ₛ rem.name.bytes) ∗
         stackAt s0.sp isSameAccountDistinctStack ∗
         addrRest_cli A loc locA ∗ addrRest_cli A rem remA ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hloc_lt, hrem_lt, hdist⟩, hm⟩
    exact Satisfies.of_eq hm' (by ac_rfl)
  · simp only [isSameAccountDistinctRawSpec, isSameAccountDistinctSpec,
      protocolAddressAt_expose_cli] at hpost ⊢
    have hpost' : sf.mem ⊨
        ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
        ((localIkA ↦ₛ localIk.publicKey.bytes.toList) ∗
         ((locA + 8#64) ↦₆₄ loc.name.ptr) ∗
         ((locA + 16#64) ↦₆₄ BitVec.ofNat 64 loc.name.bytes.length) ∗
         (loc.name.ptr ↦ₛ loc.name.bytes) ∗
         (remoteIkA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
         ((remA + 8#64) ↦₆₄ rem.name.ptr) ∗
         ((remA + 16#64) ↦₆₄ BitVec.ofNat 64 rem.name.bytes.length) ∗
         (rem.name.ptr ↦ₛ rem.name.bytes) ∗
         stackAt s0.sp isSameAccountDistinctStack ∗
         addrRest_cli A loc locA ∗ addrRest_cli A rem remA ∗ R) :=
      Satisfies.of_eq hpost (by ac_rfl)
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hret, hpost'⟩
    have hpost'' : sf.mem ⊨
        ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
        (⌜loc.name.bytes.length ≤ loc.name.cap.toNat ∧ loc.name.cap.toNat < 2 ^ 63 ∧
          loc.name.ptr ≠ 0⌝ ∗
          (⌜rem.name.bytes.length ≤ rem.name.cap.toNat ∧ rem.name.cap.toNat < 2 ^ 63 ∧
            rem.name.ptr ≠ 0⌝ ∗
            ((localIkA ↦ₛ localIk.publicKey.bytes.toList) ∗
             ((locA + 8#64) ↦₆₄ loc.name.ptr) ∗
             ((locA + 16#64) ↦₆₄ BitVec.ofNat 64 loc.name.bytes.length) ∗
             (loc.name.ptr ↦ₛ loc.name.bytes) ∗
             (remoteIkA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
             ((remA + 8#64) ↦₆₄ rem.name.ptr) ∗
             ((remA + 16#64) ↦₆₄ BitVec.ofNat 64 rem.name.bytes.length) ∗
             (rem.name.ptr ↦ₛ rem.name.bytes) ∗
             stackAt s0.sp isSameAccountDistinctStack ∗
             addrRest_cli A loc locA ∗ addrRest_cli A rem remA ∗ R))) := by
      rw [satisfies_pure_sepConj]
      refine ⟨hret, ?_⟩
      rw [satisfies_pure_sepConj]
      refine ⟨hloc_pure, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hrem_pure, hpost'⟩
    exact Satisfies.of_eq hpost'' (by ac_rfl)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok
    (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr isSameAccountName)
      (isSameAccountDistinctSpec A uuidTryParse) :=
  CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok_ext
    b A (tripleRatchetExterns C ctl abs)
    (ConsumeMessageKeyTransfer.publicKeyEq_ok b C ctl abs)
    (parseSid_ok b C ctl abs)

/-! ## Lifting CLI ratchet `S0` to `tryDecryptSpecP` (`remote ≠ local ∨ DistinctSid`) -/

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_remote_some_wp_distinct_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hsame : CryptoVerification.Cli.E2E.Pqxdh.WireEntries.IsSameAccountDistinctOkExt b A ext)
    (x : TryDecryptGhost) (remIk : IdentityKey) (s : State)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (u400 : BitVec 64) (u408 : BitVec 8)
    (dw0 : BitVec 32) (db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 : BitVec 8)
    (dw3 : BitVec 64) (db31 : BitVec 8)
    (h_pc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 384#64)
    (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s.readReg64 .x11 = 1#64)
    (hx20 : s.readReg64 .x20 = s.sp + 320#64)
    (hx25 : s.readReg64 .x25 = x.locA)
    (hx29 : s.readReg64 .x29 = s.sp + 1408#64)
    (hrem_eq : ∀ a : BitVec 64,
      (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk ∨
      DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    SepWP (tripleRatchetProgAtExt b ext) (entry + bv% (472)) s
      (((s.sp + 48#64) ↦₆₄ x.remA) ∗
       ((s.sp + 400#64) ↦₆₄ u400) ∗
       ((s.sp + 408#64) ↦₈ u408) ∗
       ((s.sp + 352#64) ↦₆₄ w3) ∗
       ((s.sp + 360#64) ↦₈ b31) ∗
       ((s.sp + 976#64) ↦₃₂ w0) ∗
       ((s.sp + 980#64) ↦₈ b4) ∗
       ((s.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16
         db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗
       stackAt s.sp isSameAccountDistinctStack)
      (fun sf P_f =>
        sf.sp = s.sp ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (sf.readReg64 .x1).setWidth 32 = 0#32 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.sp + 320#64 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = x.locA ∧
        sf.readReg64 .x29 = s.sp + 1408#64 ∧
        (P_f ⊢
          ((s.sp + 48#64) ↦₆₄ x.remA) ∗
          ((s.sp + 400#64) ↦₈ b6) ∗
          ((s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
          ((s.sp + 352#64) ↦₆₄ w3) ∗
          ((s.sp + 360#64) ↦₈ b31) ∗
          ((s.sp + 976#64) ↦₃₂ w0) ∗
          ((s.sp + 980#64) ↦₈ b4) ∗
          ((s.sp + 981#64) ↦₈ b5) ∗
          ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
          ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗
          stackAt s.sp isSameAccountDistinctStack)) := by
  dsimp only
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
  have hsame_addr : (tripleRatchetProgAtExt b ext).fnAddr isSameAccountName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2 ^ 64) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.fnAddr_tryDecrypt_rel64
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") (by decide)
  have hsame' : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2 ^ 64))
      (isSameAccountDistinctSpec A uuidTryParse) :=
    hsame_addr.rec
      (motive := fun a _ => subroutine_ok (tripleRatchetProgAtExt b ext) a (isSameAccountDistinctSpec A uuidTryParse))
      hsame
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b (Rust.withPanics ext)
    hfn (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) 0x180 92
  clear hfn hsame_addr hsame
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  examples_hide_fetches
  unfold remoteGroupD
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  have hb14 : BitVec.zeroExtend 8 (pack64 b14 b15 b16 b17 b18 b19 b20 b21) = b14 := by
    clear * -; unfold pack64; bv_kernel
  have h400 :
      ((s.sp + 400#64) ↦₆₄ pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∗
       (s.sp + 408#64) ↦₈ b14) =
      ((s.sp + 400#64) ↦₈ b6 ∗
       (s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      bytes9_64_8_eq_8_64 (s.sp + 400#64) b6 b7 b8 b9 b10 b11 b12 b13 b14
  rw [hb14, ← sepConj_assoc ((s.sp + 400#64) ↦₆₄ _), h400, sepConj_assoc]
  wp_steps
  have hb6 : BitVec.zeroExtend 8 (pack64 b6 b7 b8 b9 b10 b11 b12 b13) = b6 := by
    clear * -; unfold pack64; bv_kernel
  have hb15_22 :
      BitVec.truncate 64 ((BitVec.zeroExtend 64 b22 ++ pack64 b14 b15 b16 b17 b18 b19 b20 b21) >>> 8) =
        pack64 b15 b16 b17 b18 b19 b20 b21 b22 := by
    clear * -; unfold pack64; bv_kernel
  have hrem56 :
      ((s.sp + 56#64) ↦₃₂ w0 ∗
       (s.sp + 60#64) ↦₈ b4 ∗
       (s.sp + 61#64) ↦₈ b5 ∗
       (s.sp + 62#64) ↦₈ b6 ∗
       (s.sp + 63#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14 ∗
       (s.sp + 71#64) ↦₆₄ pack64 b15 b16 b17 b18 b19 b20 b21 b22 ∗
       (s.sp + 79#64) ↦₆₄ w3 ∗
       (s.sp + 87#64) ↦₈ b31) =
      ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) := by
    simpa only [remoteGroupD, BitVec.add_assoc, BitVec.reduceAdd] using (hrem_eq (s.sp + 56#64)).symm
  rw [hb6, hb15_22, hrem56]
  wp_call hsame' ⟨s.sp + 1280#64, x.st.localIdentity, x.locA, x.loc, s.sp + 56#64, remIk, x.remA, x.rem⟩
  wp_steps
  wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], ?_⟩
  exact Entails.of_eq (by sep_ac_rfl)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_remote_some_wp_distinct
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (x : TryDecryptGhost) (remIk : IdentityKey) (s : State)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (u400 : BitVec 64) (u408 : BitVec 8)
    (dw0 : BitVec 32) (db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 : BitVec 8)
    (dw3 : BitVec 64) (db31 : BitVec 8)
    (h_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 384#64)
    (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s.readReg64 .x11 = 1#64)
    (hx20 : s.readReg64 .x20 = s.sp + 320#64)
    (hx25 : s.readReg64 .x25 = x.locA)
    (hx29 : s.readReg64 .x29 = s.sp + 1408#64)
    (hrem_eq : ∀ a : BitVec 64,
      (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk ∨
      DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes) :
    let entry := (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    SepWP (tripleRatchetProgAt b C ctl abs) (entry + 472#64) s
      (((s.sp + 48#64) ↦₆₄ x.remA) ∗
       ((s.sp + 400#64) ↦₆₄ u400) ∗
       ((s.sp + 408#64) ↦₈ u408) ∗
       ((s.sp + 352#64) ↦₆₄ w3) ∗
       ((s.sp + 360#64) ↦₈ b31) ∗
       ((s.sp + 976#64) ↦₃₂ w0) ∗
       ((s.sp + 980#64) ↦₈ b4) ∗
       ((s.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16
         db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗
       stackAt s.sp isSameAccountDistinctStack)
      (fun sf P_f =>
        sf.sp = s.sp ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (sf.readReg64 .x1).setWidth 32 = 0#32 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.sp + 320#64 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = x.locA ∧
        sf.readReg64 .x29 = s.sp + 1408#64 ∧
        (P_f ⊢
          ((s.sp + 48#64) ↦₆₄ x.remA) ∗
          ((s.sp + 400#64) ↦₈ b6) ∗
          ((s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
          ((s.sp + 352#64) ↦₆₄ w3) ∗
          ((s.sp + 360#64) ↦₈ b31) ∗
          ((s.sp + 976#64) ↦₃₂ w0) ∗
          ((s.sp + 980#64) ↦₈ b4) ∗
          ((s.sp + 981#64) ↦₈ b5) ∗
          ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
          ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗
          stackAt s.sp isSameAccountDistinctStack)) :=
  CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_remote_some_wp_distinct_ext
    (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok b C A ctl abs)
    x remIk s w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31
    u400 u408 dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31
    h_pc h_run h_sp_align hx8 hx9 hx10 hx11 hx20 hx25 hx29 hrem_eq hdiff

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step5_some_reaches_distinct_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hsame : CryptoVerification.Cli.E2E.Pqxdh.WireEntries.IsSameAccountDistinctOkExt b A ext)
    (x : TryDecryptGhost) (remIk : IdentityKey) (F : SepProp) (s0 s4 : State)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s4.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 384#64)
    (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64)
    (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx8 : s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s4.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s4.readReg64 .x11 = 1#64)
    (hx19 : s4.readReg64 .x19 = x.ret)
    (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s4.readReg64 .x21 = x.ss)
    (hx22 : s4.readReg64 .x22 = x.msgA)
    (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA)
    (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hrem_eq : ∀ a : BitVec 64,
      (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk ∨
      DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes)
    (hm : s4.mem ⊨
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      ((s0.sp - 1504#64 + 352#64) ↦₆₄ w3) ∗
      ((s0.sp - 1504#64 + 360#64) ↦₈ b31) ∗
      ((s0.sp - 1504#64 + 976#64) ↦₃₂ w0) ∗
      ((s0.sp - 1504#64 + 980#64) ↦₈ b4) ∗
      ((s0.sp - 1504#64 + 981#64) ↦₈ b5) ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 296 ∗
      memRegion ((s0.sp - 1504#64) + 361#64) 39 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 542 ∗
      memRegion ((s0.sp - 1504#64) + 982#64) 298 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      protocolAddressAt A x.loc x.locA ∗
      protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAtExt b ext) (entry + bv% (472)) s4
      (fun s5 =>
        s5.sp = sp ∧
        s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧
        s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧
        s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧
        s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 56#64) 1352 ∗
          protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗
          stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp isSameAccountDistinctStack (by decide)] at hm
  have hm_sub : s4.mem ⊨ (memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 296) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗ protocolAddressAt A x.loc x.locA ∗
         protocolAddressAt A x.rem x.remA ∗
       stackAt sp isSameAccountDistinctStack ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountDistinctStack) ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u400, u408, dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15, db16,
    db17, db18, db19, db20, db21, db22, dw3, db31, hm_ext⟩ :=
    identityKeys_step5_some_extract hm_sub
  have hm_pre : s4.mem ⊨
      (((s4.sp + 48#64) ↦₆₄ x.remA) ∗
       ((s4.sp + 400#64) ↦₆₄ u400) ∗
       ((s4.sp + 408#64) ↦₈ u408) ∗
       ((s4.sp + 352#64) ↦₆₄ w3) ∗
       ((s4.sp + 360#64) ↦₈ b31) ∗
       ((s4.sp + 976#64) ↦₃₂ w0) ∗
       ((s4.sp + 980#64) ↦₈ b4) ∗
       ((s4.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s4.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16
         db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s4.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗
       stackAt s4.sp isSameAccountDistinctStack) ∗
      (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗
       memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
       memRegion (sp + 1312#64) 96 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountDistinctStack) ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s4.readReg64 .x20 = s4.sp + 320#64 := by rw [h_sp]; exact hx20
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by
    rw [hx29, h_sp]; bv_omega
  have hwp := CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_remote_some_wp_distinct_ext hsame
    x remIk s4 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
    w3 b31 u400 u408 dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19
      db20 db21 db22 dw3 db31
    h_pc h_run h_sp_align hx8 hx9 hx10 hx11 hx20' hx25 hx29' hrem_eq hdiff
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
    hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨hsp5.trans h_sp, halign5, ⟨htr5.1.trans htr.1, htr5.2.trans htr.2⟩, hx1_5, hx19_5.trans hx19,
    by rw [hx20_5, h_sp], hx21_5.trans hx21, hx22_5.trans hx22, hx23_5.trans hx23,
    by change (s5.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_5]; exact hx24,
    hx25_5, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm2 := Arm64.Satisfies.mono (sepConj_mono_left hPf) hm_s5
  rw [h_sp] at hm2
  have hm3 : s5.mem ⊨
      (((sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
       memRegion (sp + 88#64) 264 ∗
       ((sp + 352#64) ↦₆₄ w3) ∗
       ((sp + 360#64) ↦₈ b31) ∗
       memRegion (sp + 361#64) 39 ∗
       ((sp + 400#64) ↦₈ b6) ∗
       ((sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
       memRegion (sp + 409#64) 25 ∗
       memRegion (sp + 434#64) 542 ∗
       ((sp + 976#64) ↦₃₂ w0) ∗
       ((sp + 980#64) ↦₈ b4) ∗
       ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗
       protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗
       (stackAt sp isSameAccountDistinctStack ∗
        memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountDistinctStack)) ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp isSameAccountDistinctStack (by decide)] at hm3
  have hm4 := Arm64.Satisfies.mono
    (sepConj_mono_left
      (identityKeys_step5_some_recombine sp x.st.localIdentity remIk w0 b4 b5 b6
        (pack64 b7 b8 b9 b10 b11 b12 b13 b14) w3 b31)) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step5_some_reaches_distinct
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (x : TryDecryptGhost) (remIk : IdentityKey) (F : SepProp) (s0 s4 : State)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s4.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 384#64)
    (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64)
    (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx8 : s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s4.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s4.readReg64 .x11 = 1#64)
    (hx19 : s4.readReg64 .x19 = x.ret)
    (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s4.readReg64 .x21 = x.ss)
    (hx22 : s4.readReg64 .x22 = x.msgA)
    (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA)
    (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hrem_eq : ∀ a : BitVec 64,
      (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk ∨
      DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes)
    (hm : s4.mem ⊨
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      ((s0.sp - 1504#64 + 352#64) ↦₆₄ w3) ∗
      ((s0.sp - 1504#64 + 360#64) ↦₈ b31) ∗
      ((s0.sp - 1504#64 + 976#64) ↦₃₂ w0) ∗
      ((s0.sp - 1504#64 + 980#64) ↦₈ b4) ∗
      ((s0.sp - 1504#64 + 981#64) ↦₈ b5) ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 296 ∗
      memRegion ((s0.sp - 1504#64) + 361#64) 39 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 542 ∗
      memRegion ((s0.sp - 1504#64) + 982#64) 298 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      protocolAddressAt A x.loc x.locA ∗
      protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let entry := (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAt b C ctl abs) (entry + 472#64) s4
      (fun s5 =>
        s5.sp = sp ∧
        s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧
        s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧
        s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧
        s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 56#64) 1352 ∗
          protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗
          stackAt sp tryDecryptSubStack ∗ F)) :=
  CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step5_some_reaches_distinct_ext
    (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok b C A ctl abs)
    x remIk F s0 s4 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31
    h_pc h_run h_sp h_sp_align htr hx8 hx9 hx10 hx11 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hrem_eq hdiff hm

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step45_reaches_distinct_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hsame : IsSameAccountOkExt img.base ext)
    (hsameDist : CryptoVerification.Cli.E2E.Pqxdh.WireEntries.IsSameAccountDistinctOkExt img.base A ext)
    (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State)
    (h_pc : s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 160#64)
    (h_run : s3.status = .Running)
    (h_sp : s3.sp = s0.sp - 1504#64)
    (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret)
    (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss)
    (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA)
    (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hnot_self : x.st.remoteIdentity ≠ some x.st.localIdentity ∨
      DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes)
    (hm : s3.mem ⊨
      remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff img ∗
      protocolAddressAt A x.loc x.locA ∗
      protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let entry := (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAtExt img.base ext) (entry + bv% (472)) s3
      (fun s5 =>
        s5.sp = sp ∧
        s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧
        s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧
        s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧
        s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 56#64) 1352 ∗
          logOff img ∗
          protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗
          stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hrem_opt : x.st.remoteIdentity with _ | remIk
  · have hne : x.st.remoteIdentity ≠ some x.st.localIdentity := by simp [hrem_opt]
    have hm' : s3.mem ⊨
        remoteIdentityOkAt (sp + 400#64) x.st.remoteIdentity ∗
        memRegion (sp + 56#64) 344 ∗
        memRegion (sp + 434#64) 846 ∗
        ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
        memRegion (sp + 1312#64) 96 ∗
        ((sp + 48#64) ↦₆₄ x.remA) ∗
        logOff img ∗
        stackAt sp tryDecryptSubStack ∗
        (protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗ F) := by
      dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
    refine reaches_pc_mono
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_step45_reaches
        himg hsame x (protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗ F)
        s0 s3 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hne hm') ?_
    intro s5 _ _ ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
      hx25_5, hx29_5, hm5⟩
    refine ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5,
      hx29_5, ?_⟩
    convert hm5 using 1; sep_ac_rfl
  · rw [hrem_opt] at hm
    dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega,
        show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20,
      b21, b22, w3, b31, hrem_c⟩ :=
      exists_remoteGroupC_of_length_32 (List.Vector.toList_length remIk.publicKey.bytes)
    have hent_402 :
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
          b21 b22 w3 b31 ⊢
          memRegion (sp + 402#64) 32 := by
      rw [← hrem_c (sp + 402#64)]
      have hlen : remIk.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
      have h := ProofLib.pointsToBytes_entails_memRegion (sp + 402#64) remIk.publicKey.bytes.toList
      rwa [hlen] at h
    rw [hrem_c (sp + 402#64)] at hm
    have hm_s4 : s3.mem ⊨
        ((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 1#8) ∗
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
          b21 b22 w3 b31 ∗
        memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
        (((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         logOff img ∗ stackAt sp tryDecryptSubStack ∗
         (protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗ F)) := by
      dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
    refine reaches_pc_seq
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_step4_reaches
        x _ s0 s3 1#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hent_402 hm_s4) ?_
    intro s4 hpc4 hrun4 ⟨hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4,
      hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩
    have hrem_d : ∀ a : BitVec 64,
        (a ↦ₛ remIk.publicKey.bytes.toList) =
          remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 :=
      fun a => (hrem_c a).trans (remoteGroupC_eq_remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
        b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    have hdiff : x.st.localIdentity ≠ remIk ∨
        DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes := by
      rcases hnot_self with hne | hdist
      · left; intro heq; apply hne; rw [hrem_opt, heq]
      · exact Or.inr hdist
    have hm4_re : s4.mem ⊨
        ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 400#64) 34 ∗
        ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
        ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
        memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
        ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
        memRegion (sp + 1312#64) 96 ∗
        protocolAddressAt A x.loc x.locA ∗
        protocolAddressAt A x.rem x.remA ∗
        stackAt sp tryDecryptSubStack ∗
        (logOff img ∗ F) := by
      dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
    refine reaches_pc_mono
      (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step5_some_reaches_distinct_ext
        hsameDist x remIk (logOff img ∗ F) s0 s4
        w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31
        hpc4 hrun4 hsp4 halign4 htr4 hx8_4 hx9_4 hx10_4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4
        hx24_4 hx25_4 hx29_4 hrem_d hdiff hm4_re) ?_
    intro s5 _ _ ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
      hx25_5, hx29_5, hm5⟩
    refine ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5,
      hx29_5, ?_⟩
    convert hm5 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step45_reaches_distinct
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State)
    (h_pc : s3.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 160#64)
    (h_run : s3.status = .Running)
    (h_sp : s3.sp = s0.sp - 1504#64)
    (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret)
    (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss)
    (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA)
    (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hnot_self : x.st.remoteIdentity ≠ some x.st.localIdentity ∨
      DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes)
    (hm : s3.mem ⊨
      remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff img ∗
      protocolAddressAt A x.loc x.locA ∗
      protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let entry := (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAt img.base C ctl abs) (entry + 472#64) s3
      (fun s5 =>
        s5.sp = sp ∧
        s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧
        s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧
        s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧
        s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 56#64) 1352 ∗
          logOff img ∗
          protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗
          stackAt sp tryDecryptSubStack ∗ F)) :=
  CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step45_reaches_distinct_ext
    himg
    (Glue.is_same_account_ok img.base C ctl abs)
    (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok img.base C A ctl abs)
    x F s0 s3 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hnot_self hm

private theorem coinsAfter_zero_sa (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.SignalSession.Coins.coinsAt ctl cur rest ⊢
      CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest 0 := by
  unfold CryptoVerification.SignalSession.Coins.coinsAt
    CryptoVerification.SignalSession.Coins.tapeAt2
    CryptoVerification.SignalSession.Coins.coinsAfter
    CryptoVerification.SignalSession.Coins.tapeAfter2
  have hcur : cur + BitVec.ofNat 64 0 = cur := by bv_omega
  have hlen : rest.length - 0 = rest.length := Nat.sub_zero _
  rw [hcur, hlen]
  exact Entails.pure_left (fun _ => Entails.refl _)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_ok_P_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hlocal : LocalIdentityKeyOkExt img A ext)
    (hremote : CryptoVerification.LibsignalTripleRatchet.Decrypt.RemoteIdentityKeyOkExt img A ext)
    (hsame : IsSameAccountOkExt img.base ext)
    (hsameDist : CryptoVerification.Cli.E2E.Pqxdh.WireEntries.IsSameAccountDistinctOkExt img.base A ext)
    (x : TryDecryptGhost) (R : SepProp) (s0 : State)
    (h_pc : s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
    (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗ R) :
    reaches_pc (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img) s0
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0) := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen0, hsym0⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hnot_self, _, _, _⟩, hm0⟩
  unfold sessionStateAt at hm0
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm0
  rcases hm0 with ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, hm0⟩
  have hm_s1 : s0.mem ⊨
      stackAt s0.sp rootStack ∗
      vecGhostAt A x.G.localIk x.ss ∗
      logOff img ∗
      (vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
       optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
       memRegion x.ret 48 ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm0 using 1; sep_ac_rfl
  have hcall_inv : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab :=
    ⟨hfrozen0, hsym0⟩
  have hentry :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.tryDecryptEntry_eq_fnAddr (ext := ext) himg
  have h_pc' : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName :=
    h_pc.trans hentry
  have h_segS1 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img =
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 472#64 := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC
    rw [hentry]
  rw [h_segS1]
  refine ChainLookup.reaches_pc_seq_callInv hcall_inv
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_step1_reaches
      hlocal x _ s0 h_pc' h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc hm_s1) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, halign1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx29_1, hm1⟩ hinv1
  have hm_s2 : s1.mem ⊨
      localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗
      (vecGhostAt A x.G.localIk x.ss ∗
       vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
        vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
        optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
        logOff img ∗
        memRegion x.ret 48 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  refine ChainLookup.reaches_pc_seq_callInv hinv1
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_step2_reaches
      x _ s0 s1 hpc1 hrun1 hsp1 halign1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hm_s2) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx29_2, hm2⟩ hinv2
  have hm_s3 : s2.mem ⊨
      vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      logOff img ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
       memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
       ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
       vecGhostAt A x.G.localIk x.ss ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
        vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
        optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
        memRegion x.ret 48 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  refine ChainLookup.reaches_pc_seq_callInv hinv2
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_step3_reaches
      hremote x _ s0 s2 hpc2 hrun2 hsp2 halign2 htr2 hx0_2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx29_2
      hdeser_rem hm_s3) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx29_3, hm3⟩ hinv3
  have hm_s45 : s3.mem ⊨
      remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff img ∗
      protocolAddressAt A x.loc x.locA ∗
      protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (vecGhostAt A x.G.localIk x.ss ∗
       vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
       optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
       memRegion x.ret 48 ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm3 using 1; sep_ac_rfl
  refine reaches_pc_mono
    (ChainLookup.reaches_pc_callInv hinv3
      (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step45_reaches_distinct_ext
        himg hsame hsameDist x _ s0 s3 hpc3 hrun3 hsp3 halign3 htr3 hx19_3 hx20_3 hx21_3
        hx22_3 hx23_3 hx24_3 hx25_3 hx29_3 hnot_self hm_s45)) ?_
  intro s5 hpc5 hrun5 ⟨⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
    hx24_5, hx25_5, hx29_5, hm5⟩, hfrozen5, hsym5⟩
  rw [← h_segS1] at hpc5
  refine ⟨hpc5, ⟨hrun5, hsp5, h_sp_align, halign5, hx29_5, htr5.1, hfrozen5, hsym5, htr5.2⟩,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx1_5, ?_⟩
  unfold sessionStateAt CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, ?_⟩
  have hm5_tape : s5.mem ⊨
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
      (((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       memRegion (s0.sp - 1504#64 + 56#64) 1352 ∗
       logOff img ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       vecGhostAt A x.G.localIk x.ss ∗
       vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
       optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
       memRegion x.ret 48 ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       A.pool ∗ R) := by
    convert hm5 using 1; sep_ac_rfl
  have hm5_after :=
    Arm64.Satisfies.mono (sepConj_mono_left (coinsAfter_zero_sa img.base x.cur x.rest)) hm5_tape
  convert hm5_after using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_ok_P
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hlocal : LocalIdentityKeyOk img C A ctl abs)
    (hremote : RemoteIdentityKeyOk img C A ctl abs)
    (x : TryDecryptGhost) (R : SepProp) (s0 : State)
    (h_pc : s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
    (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗ R) :
    reaches_pc (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img) s0
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0) :=
  CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_ok_P_ext himg hlocal hremote
    (Glue.is_same_account_ok img.base C ctl abs)
    (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok img.base C A ctl abs)
    x R s0 h_pc h_run h_sp_align hpre

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.seedsLen32_of_pre_P
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗ R) :
    SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat := by
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1.2.2.2.2.2.2.2

/-! ## Contract-backed (`extHookStack = 16384`) `is_same_account` and `S0` -/

abbrev _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.IsSameAccountDistinctOkXExt :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOkExt32

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok_of_pkEq_x_ext
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hEq : Getters.PublicKeyEqOkExt32 b ext) :
    CryptoVerification.Cli.E2E.Pqxdh.WireEntries.IsSameAccountDistinctOkXExt b A ext :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountEqDistinct_ok_of_pkEq b A ext hEq

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok_x_ext
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hbb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    CryptoVerification.Cli.E2E.Pqxdh.WireEntries.IsSameAccountDistinctOkXExt b A ext :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountEqDistinct_ok_ext32 b A ext hbb

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_remote_some_wp_distinct_x_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hsame : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOkExt32 b A ext)
    (x : TryDecryptGhost) (remIk : IdentityKey) (s : State)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (u400 : BitVec 64) (u408 : BitVec 8)
    (dw0 : BitVec 32) (db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 : BitVec 8)
    (dw3 : BitVec 64) (db31 : BitVec 8)
    (h_pc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 384#64)
    (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s.readReg64 .x11 = 1#64)
    (hx20 : s.readReg64 .x20 = s.sp + 320#64)
    (hx25 : s.readReg64 .x25 = x.locA)
    (hx29 : s.readReg64 .x29 = s.sp + 1408#64)
    (hrem_eq : ∀ a : BitVec 64,
      (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk ∨
      DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    SepWP (tripleRatchetProgAtExt b ext) (entry + bv% (472)) s
      (((s.sp + 48#64) ↦₆₄ x.remA) ∗
       ((s.sp + 400#64) ↦₆₄ u400) ∗
       ((s.sp + 408#64) ↦₈ u408) ∗
       ((s.sp + 352#64) ↦₆₄ w3) ∗
       ((s.sp + 360#64) ↦₈ b31) ∗
       ((s.sp + 976#64) ↦₃₂ w0) ∗
       ((s.sp + 980#64) ↦₈ b4) ∗
       ((s.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16
         db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗
       stackAt s.sp CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt)
      (fun sf P_f =>
        sf.sp = s.sp ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (sf.readReg64 .x1).setWidth 32 = 0#32 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.sp + 320#64 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = x.locA ∧
        sf.readReg64 .x29 = s.sp + 1408#64 ∧
        (P_f ⊢
          ((s.sp + 48#64) ↦₆₄ x.remA) ∗
          ((s.sp + 400#64) ↦₈ b6) ∗
          ((s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
          ((s.sp + 352#64) ↦₆₄ w3) ∗
          ((s.sp + 360#64) ↦₈ b31) ∗
          ((s.sp + 976#64) ↦₃₂ w0) ∗
          ((s.sp + 980#64) ↦₈ b4) ∗
          ((s.sp + 981#64) ↦₈ b5) ∗
          ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
          ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗
          stackAt s.sp CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt)) := by
  dsimp only
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
  have hsame_addr : (tripleRatchetProgAtExt b ext).fnAddr isSameAccountName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2 ^ 64) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.fnAddr_tryDecrypt_rel64
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") (by decide)
  have hsame' : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2 ^ 64))
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A uuidTryParse) :=
    hsame_addr.rec
      (motive := fun a _ => subroutine_ok (tripleRatchetProgAtExt b ext) a
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A uuidTryParse))
      hsame
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b (Rust.withPanics ext)
    hfn (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) 0x180 92
  clear hfn hsame_addr hsame
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  examples_hide_fetches
  unfold remoteGroupD
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  have hb14 : BitVec.zeroExtend 8 (pack64 b14 b15 b16 b17 b18 b19 b20 b21) = b14 := by
    clear * -; unfold pack64; bv_kernel
  have h400 :
      ((s.sp + 400#64) ↦₆₄ pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∗
       (s.sp + 408#64) ↦₈ b14) =
      ((s.sp + 400#64) ↦₈ b6 ∗
       (s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      bytes9_64_8_eq_8_64 (s.sp + 400#64) b6 b7 b8 b9 b10 b11 b12 b13 b14
  rw [hb14, ← sepConj_assoc ((s.sp + 400#64) ↦₆₄ _), h400, sepConj_assoc]
  wp_steps
  have hb6 : BitVec.zeroExtend 8 (pack64 b6 b7 b8 b9 b10 b11 b12 b13) = b6 := by
    clear * -; unfold pack64; bv_kernel
  have hb15_22 :
      BitVec.truncate 64 ((BitVec.zeroExtend 64 b22 ++ pack64 b14 b15 b16 b17 b18 b19 b20 b21) >>> 8) =
        pack64 b15 b16 b17 b18 b19 b20 b21 b22 := by
    clear * -; unfold pack64; bv_kernel
  have hrem56 :
      ((s.sp + 56#64) ↦₃₂ w0 ∗
       (s.sp + 60#64) ↦₈ b4 ∗
       (s.sp + 61#64) ↦₈ b5 ∗
       (s.sp + 62#64) ↦₈ b6 ∗
       (s.sp + 63#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14 ∗
       (s.sp + 71#64) ↦₆₄ pack64 b15 b16 b17 b18 b19 b20 b21 b22 ∗
       (s.sp + 79#64) ↦₆₄ w3 ∗
       (s.sp + 87#64) ↦₈ b31) =
      ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) := by
    simpa only [remoteGroupD, BitVec.add_assoc, BitVec.reduceAdd] using (hrem_eq (s.sp + 56#64)).symm
  rw [hb6, hb15_22, hrem56]
  wp_call hsame' ⟨s.sp + 1280#64, x.st.localIdentity, x.locA, x.loc, s.sp + 56#64, remIk, x.remA, x.rem⟩
  wp_steps
  wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], ?_⟩
  exact Entails.of_eq (by sep_ac_rfl)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step5_some_reaches_distinct_x_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hsame : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOkExt32 b A ext)
    (x : TryDecryptGhost) (remIk : IdentityKey) (F : SepProp) (s0 s4 : State)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s4.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 384#64)
    (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64)
    (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx8 : s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s4.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s4.readReg64 .x11 = 1#64)
    (hx19 : s4.readReg64 .x19 = x.ret)
    (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s4.readReg64 .x21 = x.ss)
    (hx22 : s4.readReg64 .x22 = x.msgA)
    (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA)
    (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hrem_eq : ∀ a : BitVec 64,
      (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk ∨
      DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes)
    (hm : s4.mem ⊨
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      ((s0.sp - 1504#64 + 352#64) ↦₆₄ w3) ∗
      ((s0.sp - 1504#64 + 360#64) ↦₈ b31) ∗
      ((s0.sp - 1504#64 + 976#64) ↦₃₂ w0) ∗
      ((s0.sp - 1504#64 + 980#64) ↦₈ b4) ∗
      ((s0.sp - 1504#64 + 981#64) ↦₈ b5) ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 296 ∗
      memRegion ((s0.sp - 1504#64) + 361#64) 39 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 542 ∗
      memRegion ((s0.sp - 1504#64) + 982#64) 298 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      protocolAddressAt A x.loc x.locA ∗
      protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAtExt b ext) (entry + bv% (472)) s4
      (fun s5 =>
        s5.sp = sp ∧
        s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧
        s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧
        s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧
        s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 56#64) 1352 ∗
          protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗
          stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  let stk := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt
  rw [stackAt_tryDecryptSubStack_sub s0.sp stk (by decide)] at hm
  have hm_sub : s4.mem ⊨ (memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 296) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗ protocolAddressAt A x.loc x.locA ∗
         protocolAddressAt A x.rem x.remA ∗
       stackAt sp stk ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - stk) ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u400, u408, dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15, db16,
    db17, db18, db19, db20, db21, db22, dw3, db31, hm_ext⟩ :=
    identityKeys_step5_some_extract hm_sub
  have hm_pre : s4.mem ⊨
      (((s4.sp + 48#64) ↦₆₄ x.remA) ∗
       ((s4.sp + 400#64) ↦₆₄ u400) ∗
       ((s4.sp + 408#64) ↦₈ u408) ∗
       ((s4.sp + 352#64) ↦₆₄ w3) ∗
       ((s4.sp + 360#64) ↦₈ b31) ∗
       ((s4.sp + 976#64) ↦₃₂ w0) ∗
       ((s4.sp + 980#64) ↦₈ b4) ∗
       ((s4.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s4.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16
         db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s4.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗
       stackAt s4.sp stk) ∗
      (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗
       memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
       memRegion (sp + 1312#64) 96 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - stk) ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s4.readReg64 .x20 = s4.sp + 320#64 := by rw [h_sp]; exact hx20
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by
    rw [hx29, h_sp]; bv_omega
  have hwp := CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_remote_some_wp_distinct_x_ext hsame
    x remIk s4 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
    w3 b31 u400 u408 dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19
      db20 db21 db22 dw3 db31
    h_pc h_run h_sp_align hx8 hx9 hx10 hx11 hx20' hx25 hx29' hrem_eq hdiff
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
    hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨hsp5.trans h_sp, halign5, ⟨htr5.1.trans htr.1, htr5.2.trans htr.2⟩, hx1_5, hx19_5.trans hx19,
    by rw [hx20_5, h_sp], hx21_5.trans hx21, hx22_5.trans hx22, hx23_5.trans hx23,
    by change (s5.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_5]; exact hx24,
    hx25_5, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm2 := Arm64.Satisfies.mono (sepConj_mono_left hPf) hm_s5
  rw [h_sp] at hm2
  have hm3 : s5.mem ⊨
      (((sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
       memRegion (sp + 88#64) 264 ∗
       ((sp + 352#64) ↦₆₄ w3) ∗
       ((sp + 360#64) ↦₈ b31) ∗
       memRegion (sp + 361#64) 39 ∗
       ((sp + 400#64) ↦₈ b6) ∗
       ((sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
       memRegion (sp + 409#64) 25 ∗
       memRegion (sp + 434#64) 542 ∗
       ((sp + 976#64) ↦₃₂ w0) ∗
       ((sp + 980#64) ↦₈ b4) ∗
       ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗
       protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗
       (stackAt sp stk ∗
        memRegion (s0.sp - 262144#64) (tryDecryptSubStack - stk)) ∗ F) := by
    dsimp only [sp, stk] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp stk (by decide)] at hm3
  have hm4 := Arm64.Satisfies.mono
    (sepConj_mono_left
      (identityKeys_step5_some_recombine sp x.st.localIdentity remIk w0 b4 b5 b6
        (pack64 b7 b8 b9 b10 b11 b12 b13 b14) w3 b31)) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step45_reaches_distinct_x_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hsameDist : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOkExt32 img.base A ext)
    (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State)
    (h_pc : s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 160#64)
    (h_run : s3.status = .Running)
    (h_sp : s3.sp = s0.sp - 1504#64)
    (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret)
    (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss)
    (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA)
    (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hnot_self : x.st.remoteIdentity ≠ some x.st.localIdentity ∨
      DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes)
    (hm : s3.mem ⊨
      remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff img ∗
      protocolAddressAt A x.loc x.locA ∗
      protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let entry := (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAtExt img.base ext) (entry + bv% (472)) s3
      (fun s5 =>
        s5.sp = sp ∧
        s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧
        s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧
        s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧
        s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 56#64) 1352 ∗
          logOff img ∗
          protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗
          stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hrem_opt : x.st.remoteIdentity with _ | remIk
  · let F' := protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗ F
    rw [hrem_opt] at hm
    dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega,
        show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    have hm_402 : s3.mem ⊨ memRegion (sp + 402#64) 32 ∗
        (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 0#8) ∗
         memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
         ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         logOff img ∗ stackAt sp tryDecryptSubStack ∗ F') := by
      dsimp only [sp, F'] at hm ⊢; convert hm using 1; sep_ac_rfl
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, w3, b31, hent_402, hm_402⟩ :=
      exists_remoteGroupC_of_memRegion_32 hm_402
    have hm_s4 : s3.mem ⊨
        ((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 0#8) ∗
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
        memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
        (((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         logOff img ∗ stackAt sp tryDecryptSubStack ∗ F') := by
      dsimp only [sp] at hm_402 ⊢; convert hm_402 using 1; sep_ac_rfl
    refine reaches_pc_seq
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_step4_reaches
        x _ s0 s3 0#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 (hent_402 (sp + 402#64)) hm_s4) ?_
    intro s4 hpc4 hrun4 ⟨hsp4, halign4, htr4, _, _, _, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩
    have hm4_re : s4.mem ⊨
        (memRegion (sp + 56#64) 296 ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
         memRegion (sp + 361#64) 39 ∗ memRegion (sp + 400#64) 34 ∗ memRegion (sp + 434#64) 542 ∗
         ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
         memRegion (sp + 982#64) 298 ∗
         ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96) ∗
        (logOff img ∗ (((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗ F')) := by
      dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
    have hm4_1352 :=
      Arm64.Satisfies.mono (sepConj_mono_left (identityKeys_step4_to_memRegion_1352 sp x.st.localIdentity w0 b4 b5 w3 b31)) hm4_re
    refine reaches_pc_mono
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_step5_none_reaches
        himg x (((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗ F')
        s0 s4 hpc4 hrun4 hsp4 halign4 htr4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx29_4 hm4_1352) ?_
    intro s5 _ _ ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩
    refine ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, ?_⟩
    dsimp only [sp, F'] at hm5 ⊢; convert hm5 using 1; sep_ac_rfl
  · rw [hrem_opt] at hm
    dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega,
        show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20,
      b21, b22, w3, b31, hrem_c⟩ :=
      exists_remoteGroupC_of_length_32 (List.Vector.toList_length remIk.publicKey.bytes)
    have hent_402 :
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
          b21 b22 w3 b31 ⊢
          memRegion (sp + 402#64) 32 := by
      rw [← hrem_c (sp + 402#64)]
      have hlen : remIk.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
      have h := ProofLib.pointsToBytes_entails_memRegion (sp + 402#64) remIk.publicKey.bytes.toList
      rwa [hlen] at h
    rw [hrem_c (sp + 402#64)] at hm
    have hm_s4 : s3.mem ⊨
        ((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 1#8) ∗
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
          b21 b22 w3 b31 ∗
        memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
        (((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         logOff img ∗ stackAt sp tryDecryptSubStack ∗
         (protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗ F)) := by
      dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
    refine reaches_pc_seq
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_step4_reaches
        x _ s0 s3 1#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hent_402 hm_s4) ?_
    intro s4 hpc4 hrun4 ⟨hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4,
      hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩
    have hrem_d : ∀ a : BitVec 64,
        (a ↦ₛ remIk.publicKey.bytes.toList) =
          remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 :=
      fun a => (hrem_c a).trans (remoteGroupC_eq_remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
        b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    have hdiff : x.st.localIdentity ≠ remIk ∨
        DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes := by
      rcases hnot_self with hne | hdist
      · left; intro heq; apply hne; rw [hrem_opt, heq]
      · exact Or.inr hdist
    have hm4_re : s4.mem ⊨
        ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 400#64) 34 ∗
        ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
        ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
        memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
        memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
        ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
        memRegion (sp + 1312#64) 96 ∗
        protocolAddressAt A x.loc x.locA ∗
        protocolAddressAt A x.rem x.remA ∗
        stackAt sp tryDecryptSubStack ∗
        (logOff img ∗ F) := by
      dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
    refine reaches_pc_mono
      (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step5_some_reaches_distinct_x_ext
        hsameDist x remIk (logOff img ∗ F) s0 s4
        w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31
        hpc4 hrun4 hsp4 halign4 htr4 hx8_4 hx9_4 hx10_4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4
        hx24_4 hx25_4 hx29_4 hrem_d hdiff hm4_re) ?_
    intro s5 _ _ ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
      hx25_5, hx29_5, hm5⟩
    refine ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5,
      hx29_5, ?_⟩
    convert hm5 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_ok_P_x_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hlocal : LocalIdentityKeyOkExt img A ext)
    (hremote : CryptoVerification.LibsignalTripleRatchet.Decrypt.RemoteIdentityKeyOkExt img A ext)
    (hsameDist : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOkExt32 img.base A ext)
    (x : TryDecryptGhost) (R : SepProp) (s0 : State)
    (h_pc : s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
    (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗ R) :
    reaches_pc (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img) s0
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0) := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen0, hsym0⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hnot_self, _, _, _⟩, hm0⟩
  unfold sessionStateAt at hm0
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm0
  rcases hm0 with ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, hm0⟩
  have hm_s1 : s0.mem ⊨
      stackAt s0.sp rootStack ∗
      vecGhostAt A x.G.localIk x.ss ∗
      logOff img ∗
      (vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
       optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
       memRegion x.ret 48 ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm0 using 1; sep_ac_rfl
  have hcall_inv : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab :=
    ⟨hfrozen0, hsym0⟩
  have hentry :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.tryDecryptEntry_eq_fnAddr (ext := ext) himg
  have h_pc' : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName :=
    h_pc.trans hentry
  have h_segS1 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img =
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 472#64 := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC
    rw [hentry]
  rw [h_segS1]
  refine ChainLookup.reaches_pc_seq_callInv hcall_inv
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_step1_reaches
      hlocal x _ s0 h_pc' h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc hm_s1) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, halign1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx29_1, hm1⟩ hinv1
  have hm_s2 : s1.mem ⊨
      localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗
      (vecGhostAt A x.G.localIk x.ss ∗
       vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
        vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
        optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
        logOff img ∗
        memRegion x.ret 48 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  refine ChainLookup.reaches_pc_seq_callInv hinv1
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_step2_reaches
      x _ s0 s1 hpc1 hrun1 hsp1 halign1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hm_s2) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx29_2, hm2⟩ hinv2
  have hm_s3 : s2.mem ⊨
      vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      logOff img ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
       memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
       ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
       vecGhostAt A x.G.localIk x.ss ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
        vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
        optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
        memRegion x.ret 48 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  refine ChainLookup.reaches_pc_seq_callInv hinv2
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_step3_reaches
      hremote x _ s0 s2 hpc2 hrun2 hsp2 halign2 htr2 hx0_2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx29_2
      hdeser_rem hm_s3) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx29_3, hm3⟩ hinv3
  have hm_s45 : s3.mem ⊨
      remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff img ∗
      protocolAddressAt A x.loc x.locA ∗
      protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (vecGhostAt A x.G.localIk x.ss ∗
       vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
       optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
       memRegion x.ret 48 ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm3 using 1; sep_ac_rfl
  refine reaches_pc_mono
    (ChainLookup.reaches_pc_callInv hinv3
      (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_step45_reaches_distinct_x_ext
        himg hsameDist x _ s0 s3 hpc3 hrun3 hsp3 halign3 htr3 hx19_3 hx20_3 hx21_3
        hx22_3 hx23_3 hx24_3 hx25_3 hx29_3 hnot_self hm_s45)) ?_
  intro s5 hpc5 hrun5 ⟨⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
    hx24_5, hx25_5, hx29_5, hm5⟩, hfrozen5, hsym5⟩
  rw [← h_segS1] at hpc5
  refine ⟨hpc5, ⟨hrun5, hsp5, h_sp_align, halign5, hx29_5, htr5.1, hfrozen5, hsym5, htr5.2⟩,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx1_5, ?_⟩
  unfold sessionStateAt CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, ?_⟩
  have hm5_tape : s5.mem ⊨
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
      (((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       memRegion (s0.sp - 1504#64 + 56#64) 1352 ∗
       logOff img ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       vecGhostAt A x.G.localIk x.ss ∗
       vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗
       vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
       optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
       memRegion x.ret 48 ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       A.pool ∗ R) := by
    convert hm5 using 1; sep_ac_rfl
  have hm5_after :=
    Arm64.Satisfies.mono (sepConj_mono_left (coinsAfter_zero_sa img.base x.cur x.rest)) hm5_tape
  convert hm5_after using 1; sep_ac_rfl

end CryptoVerification.E2E.Pqxdh.WireEntries

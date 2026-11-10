/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccount
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.InImage.Uuid
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Extern-Parameterized Account and Chain Callee Contracts for `initiate`

Proves `CliExternsOk P A ext`-parameterized `subroutine_ok` theorems on
`tripleRatchetProgAtExt img.base (cliExternsWith ext)` for `<IdentityKey>::is_same_account`,
`<PrivateKey>::calculate_agreement`, and `<RootKey>::create_chain`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

abbrev isSameAccountSym : String :=
  "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"

private theorem hookSat_cliExternsWith_chain {α : Type} {ext : String → Option (State → State)}
    {name : String} {spec : Spec α}
    (hnp : E2E.isImagePanicSymbol name = false)
    (h : HookSat ext name spec) :
    HookSat (cliExternsWith ext) name spec := by
  simp only [HookSat, cliExternsWith, withCliPanics_of_isImagePanicSymbol_false _ hnp]
  exact h

/-- Stack-parameterized `<IdentityKey>::is_same_account` distinct-account specification. -/
def isSameAccountDistinctAtSpec (A : RustAlloc) (parse : UuidParser) (isaStk : Nat) :
    Spec Pqxdh.WireEntries.IsSameAccountDistinctGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.localIkA ∧
      s.readReg64 .x1 = g.locA ∧
      s.readReg64 .x2 = g.remoteIkA ∧
      s.readReg64 .x3 = g.remA ∧
      (g.localIk ≠ g.remoteIk ∨
        Pqxdh.WireEntries.DistinctSid parse g.loc.name.bytes g.rem.name.bytes)⌝ ∗
    (g.localIkA ↦ₛ g.localIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.loc g.locA ∗
    (g.remoteIkA ↦ₛ g.remoteIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.rem g.remA ∗
    stackAt s.sp isaStk
  post := fun g s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
    (g.localIkA ↦ₛ g.localIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.loc g.locA ∗
    (g.remoteIkA ↦ₛ g.remoteIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.rem g.remA ∗
    stackAt s0.sp isaStk

/-! ## `<IdentityKey>::is_same_account` -/

section IsSameAccountExt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Stack budget for `<IdentityKey>::is_same_account` under `CliExternsOk` (`80 + publicKeyEqStackExt = 16528` bytes). -/
abbrev isSameAccountExtStack : Nat := 80 + Getters.publicKeyEqStackExt

private theorem publicKeyEq_ok_at_isSameAccount_ext (b : BitVec 64)
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr isSameAccountSym +
        BitVec.ofNat 64 (num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
          ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")))
      Getters.publicKeyEqSpecExt := by
  have hEq : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Getters.publicKeyEqName)
      Getters.publicKeyEqSpecExt :=
    Glue.publicKeyEq_ok_ext32 b h_bb
  dsimp only [tripleRatchetProgAtExt] at hEq ⊢
  rwa [← Program.fnAddr_rel
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")
    (k := num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
      ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")) rfl]

private theorem stackAt_16368_split_uuid (sp : BitVec 64) :
    stackAt sp 16368 = memRegion (sp - 16368#64) 16176 ∗ stackAt sp uuidTryParseStack := by
  simp only [stackAt, uuidTryParseStack]
  rw [show BitVec.ofNat 64 16368 = 16368#64 from rfl,
      show BitVec.ofNat 64 0xC0 = 192#64 from rfl]
  exact ProofLib.memRegion_split' (b := sp - 16368#64) (n := 16176) (k := 192)
    (b' := sp - 192#64) (by decide) (by bv_omega) (by decide)

private theorem stackAt_publicKeyEqStackExt_eq_parseSid16368 (sp : BitVec 64) :
    stackAt sp Getters.publicKeyEqStackExt =
      stackAt (sp - 80#64) 16368 ∗ stackAt sp parseSidFrameStack := by
  simp only [stackAt, Getters.publicKeyEqStackExt, extHookStack, parseSidFrameStack]
  have hsub : sp - 80#64 - BitVec.ofNat 64 16368 = sp - 16448#64 := by bv_omega
  rw [hsub, show (64 + 2 ^ 14 : Nat) = 16448 from rfl,
      show BitVec.ofNat 64 16448 = 16448#64 from rfl,
      show BitVec.ofNat 64 0x50 = 80#64 from rfl]
  exact ProofLib.memRegion_split' (b := sp - 16448#64) (n := 16368) (k := 80)
    (b' := sp - 80#64) (by decide) (by bv_omega) (by decide)

private theorem memRegion_17_eq_cells_ext (a : BitVec 64) :
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
  refine congrArg sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

private theorem pointsTo_17_entails_memRegion_ext (a : BitVec 64) (b0 : BitVec 8) (w0 w1 : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1)) ⊢ memRegion a 17 := by
  rw [memRegion_17_eq_cells_ext a]
  exact Entails.sepExists_right b0 (Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.refl _)))

private theorem memRegion_16_out_split_ext (a : BitVec 64) :
    memRegion (a + 1#64) 16 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  rw [show (16 : Nat) = 8 + 8 by decide, memRegion_split (a + 1#64) 8 8 (by decide)]
  have h9 : a + 1#64 + BitVec.ofNat 64 8 = a + 9#64 := by bv_arith
  rw [h9, ProofLib.memRegion_eight (a + 1#64), ProofLib.memRegion_eight (a + 9#64),
      sepExists_sepConj_left]
  refine congrArg sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right]

private theorem parseSidResultAt_entails_rel_cells_ext (out : BitVec 64)
    (res : Option (Bool × List.Vector (BitVec 8) 16)) :
    parseSidResultAt out res ⊢
      ∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ⌜Pqxdh.WireEntries.SidCellsRel res b0 w0 w1⌝ ∗
        (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) := by
  cases res with
  | none =>
    simp only [parseSidResultAt, Pqxdh.WireEntries.SidCellsRel, memRegion_16_out_split_ext,
      sepExists_sepConj_right]
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

private def parseSidRelExtSpec (parse : UuidParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 8 × BitVec 64 × BitVec 64) where
  pre := fun (p, bs, out, b0, w0, w1) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) ∗
      stackAt s.sp Getters.publicKeyEqStackExt
  post := fun (p, bs, out, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      (∃∗ b0' : BitVec 8, ∃∗ w0' : BitVec 64, ∃∗ w1' : BitVec 64,
        ⌜Pqxdh.WireEntries.SidCellsRel (serviceIdParse parse bs) b0' w0' w1'⌝ ∗
        (out ↦₈ b0') ∗ ((out + 1#64) ↦₆₄ w0') ∗ ((out + 9#64) ↦₆₄ w1')) ∗
      stackAt s0.sp Getters.publicKeyEqStackExt

private theorem parseSidRel_ok_at_ext (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr isSameAccountSym +
        BitVec.ofNat 64 (num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string" -
          ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")))
      (parseSidRelExtSpec uuidTryParse) := by
  have huuid16368 : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr uuidTryParseName)
      (uuidTryParseStackSpec 16368) := by
    refine subroutine_ok_map (uuidTryParse_ok_F b H) ?_
    rintro ⟨p, bs, out⟩ R s0 hpre
    dsimp only [uuidTryParseStackSpec] at hpre
    rw [stackAt_16368_split_uuid s0.sp] at hpre
    refine ⟨(p, bs, out), memRegion (s0.sp - 16368#64) 16176 ∗ R,
      Satisfies.of_eq hpre (by dsimp only [uuidTryParseCodeSpec]; ac_rfl),
      fun sf hpost => ?_⟩
    dsimp only [uuidTryParseCodeSpec, uuidTryParseStackSpec] at hpost ⊢
    rw [stackAt_16368_split_uuid s0.sp]
    exact Satisfies.of_eq hpost (by ac_rfl)
  have hps0 := parseSid_ok_of_contract_stack b H 16368 huuid16368
  have hps : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr isSameAccountSym +
        BitVec.ofNat 64 (num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string" -
          ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")))
      (parseSidCodeStackSpec 16368) := by
    rwa [← Program.fnAddr_rel
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")
      (ls_lemma% fnOff "<libsignal_core::address::ServiceId>::parse_from_service_id_string")
      (k := num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string" -
        ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")) rfl]
  refine subroutine_ok_map hps ?_
  rintro ⟨p, bs, out, b0, w0, w1⟩ R s0 hpre
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · simp only [parseSidRelExtSpec, parseSidCodeStackSpec, parseSidSpec,
      stackAt_publicKeyEqStackExt_eq_parseSid16368 s0.sp] at hpre ⊢
    have hm : s0.mem ⊨ ((out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1)) ∗
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧ s0.readReg64 .x8 = out⌝ ∗
          (p ↦ₛ bs) ∗ stackAt (s0.sp - 80#64) 16368 ∗ stackAt s0.sp parseSidFrameStack ∗ R) :=
      Satisfies.of_eq hpre (by ac_rfl)
    have hm' :=
      Arm64.Satisfies.mono (sepConj_mono_left (pointsTo_17_entails_memRegion_ext out b0 w0 w1)) hm
    exact Satisfies.of_eq hm' (by ac_rfl)
  · simp only [parseSidCodeStackSpec, parseSidSpec, parseSidRelExtSpec,
      stackAt_publicKeyEqStackExt_eq_parseSid16368 s0.sp] at hpost ⊢
    have hm : sf.mem ⊨ parseSidResultAt out (serviceIdParse uuidTryParse bs) ∗
        (⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗
          stackAt (s0.sp - 80#64) 16368 ∗ stackAt s0.sp parseSidFrameStack ∗ R) :=
      Satisfies.of_eq hpost (by ac_rfl)
    have hm' :=
      Arm64.Satisfies.mono (sepConj_mono_left (parseSidResultAt_entails_rel_cells_ext out _)) hm
    exact Satisfies.of_eq hm' (by ac_rfl)

private theorem stackAt_isSameAccountExt_split (sp : BitVec 64) :
    stackAt sp isSameAccountExtStack =
      stackAt (sp - 80#64) Getters.publicKeyEqStackExt ∗
      memRegion (sp - 80#64) 12 ∗
      (∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 68#64) ↦₈ b0) ∗ ((sp - 67#64) ↦₆₄ w0) ∗ ((sp - 59#64) ↦₆₄ w1)) ∗
      memRegion (sp - 51#64) 3 ∗
      ProofLib.cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountExtStack, Getters.publicKeyEqStackExt, extHookStack]
  rw [show (80 + (64 + 2 ^ 14) : Nat) = 16528 from rfl,
      show (64 + 2 ^ 14 : Nat) = 16448 from rfl,
      show BitVec.ofNat 64 16528 = 16528#64 from rfl,
      show BitVec.ofNat 64 16448 = 16448#64 from rfl,
      show sp - 80#64 - 16448#64 = sp - 16528#64 by bv_arith,
      show (16528 : Nat) = 16448 + (12 + (17 + (3 + 8 * 6))) by decide,
      memRegion_split (sp - 16528#64) 16448 (12 + (17 + (3 + 8 * 6))) (by decide),
      memRegion_split (sp - 16528#64 + 16448#64) 12 (17 + (3 + 8 * 6)) (by decide),
      memRegion_split (sp - 16528#64 + 16448#64 + 12#64) 17 (3 + 8 * 6) (by decide),
      memRegion_split (sp - 16528#64 + 16448#64 + 12#64 + 17#64) 3 (8 * 6) (by decide),
      ProofLib.memRegion_cells _ 6 (by decide),
      memRegion_17_eq_cells_ext]
  have h1 : sp - 16528#64 + 16448#64 = sp - 80#64 := by bv_arith
  have h2 : sp - 80#64 + 12#64 = sp - 68#64 := by bv_arith
  have h3 : sp - 68#64 + 1#64 = sp - 67#64 := by bv_arith
  have h4 : sp - 68#64 + 9#64 = sp - 59#64 := by bv_arith
  have h5 : sp - 68#64 + 17#64 = sp - 51#64 := by bv_arith
  have h6 : sp - 51#64 + 3#64 = sp - 48#64 := by bv_arith
  rw [h1, h2, h3, h4, h5, h6]

private theorem pack64_inj_ext (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h : pack64 a0 a1 a2 a3 a4 a5 a6 a7 = pack64 b0 b1 b2 b3 b4 b5 b6 b7) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  exact ⟨
    calc a0 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 0 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 0 8 := congrArg _ h
      _ = b0 := by unfold pack64; bv_bits,
    calc a1 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 8 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 8 8 := congrArg _ h
      _ = b1 := by unfold pack64; bv_bits,
    calc a2 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 16 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 16 8 := congrArg _ h
      _ = b2 := by unfold pack64; bv_bits,
    calc a3 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 24 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 24 8 := congrArg _ h
      _ = b3 := by unfold pack64; bv_bits,
    calc a4 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 32 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 32 8 := congrArg _ h
      _ = b4 := by unfold pack64; bv_bits,
    calc a5 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 40 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 40 8 := congrArg _ h
      _ = b5 := by unfold pack64; bv_bits,
    calc a6 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 48 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 48 8 := congrArg _ h
      _ = b6 := by unfold pack64; bv_bits,
    calc a7 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 56 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 56 8 := congrArg _ h
      _ = b7 := by unfold pack64; bv_bits⟩

private theorem uuid_eq_of_uuidWords_eq_ext {u1 u2 : List.Vector (BitVec 8) 16}
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
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := pack64_inj_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw0
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := pack64_inj_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw1
  rfl

private theorem kindByte_inj_ext {p1 p2 : Bool} (h : kindByte p1 = kindByte p2) : p1 = p2 := by
  cases p1 <;> cases p2 <;> revert h <;> decide

private theorem sidCellsRel_ne_of_distinct_ext {parse : UuidParser} {bs1 bs2 : List (BitVec 8)}
    {b0_1 b0_2 : BitVec 8} {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hDist : Pqxdh.WireEntries.DistinctSid parse bs1 bs2)
    (hrel1 : Pqxdh.WireEntries.SidCellsRel (serviceIdParse parse bs1) b0_1 w0_1 w1_1)
    (hrel2 : Pqxdh.WireEntries.SidCellsRel (serviceIdParse parse bs2) b0_2 w0_2 w1_2)
    (hb1 : b0_1 ≠ 2#8) (hb2 : b0_2 ≠ 2#8) (hkind : b0_1 = b0_2) :
    w0_1 = w0_2 ∧ w1_1 = w1_2 → False := by
  rintro ⟨hw0, hw1⟩
  cases hs1 : serviceIdParse parse bs1 with
  | none => rw [hs1, Pqxdh.WireEntries.SidCellsRel] at hrel1; exact hb1 hrel1
  | some v1 =>
    rcases v1 with ⟨p1, u1⟩
    rw [hs1, Pqxdh.WireEntries.SidCellsRel] at hrel1
    rcases hrel1 with ⟨hb0_1, hw0_1, hw1_1⟩
    cases hs2 : serviceIdParse parse bs2 with
    | none => rw [hs2, Pqxdh.WireEntries.SidCellsRel] at hrel2; exact hb2 hrel2
    | some v2 =>
      rcases v2 with ⟨p2, u2⟩
      rw [hs2, Pqxdh.WireEntries.SidCellsRel] at hrel2
      rcases hrel2 with ⟨hb0_2, hw0_2, hw1_2⟩
      have hp : p1 = p2 := kindByte_inj_ext (hb0_1.symm.trans (hkind.trans hb0_2))
      have hu : u1 = u2 := uuid_eq_of_uuidWords_eq_ext
        (hw0_1.symm.trans (hw0.trans hw0_2))
        (hw1_1.symm.trans (hw1.trans hw1_2))
      subst hp hu
      exact hDist (p1, u1) hs1 hs2

private theorem cond_uuid_words_ne_ext {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hne : w0_1 = w0_2 ∧ w1_1 = w1_2 → False) :
    (if (w0_1 == w0_2) = true then w1_1 != w1_2 else true) = true := by
  by_cases h0 : (w0_1 == w0_2) = true
  · simp only [h0, ↓reduceIte, bne_iff_ne]
    intro h1
    exact hne ⟨of_decide_eq_true h0, h1⟩
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]

private theorem sidCellsRel_b0_cases_ext {o : Option (Bool × List.Vector (BitVec 8) 16)}
    {b0 : BitVec 8} {w0 w1 : BitVec 64} (h : Pqxdh.WireEntries.SidCellsRel o b0 w0 w1) :
    b0 = 0#8 ∨ b0 = 1#8 ∨ b0 = 2#8 := by
  cases o with
  | none => right; right; exact h
  | some v => rcases v with ⟨p, _⟩; rcases h with ⟨rfl, _, _⟩; cases p <;> simp [kindByte]

private def isSameAccountDistinctRawExtSpec (parse : UuidParser) :
    Spec Pqxdh.WireEntries.IsSameAccountDistinctRawGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.localIkA ∧
      s.readReg64 .x1 = g.localAddr ∧
      s.readReg64 .x2 = g.remoteIkA ∧
      s.readReg64 .x3 = g.remoteAddr ∧
      g.localNameBytes.length < 2 ^ 64 ∧
      g.remoteNameBytes.length < 2 ^ 64 ∧
      (g.localIk ≠ g.remoteIk ∨ Pqxdh.WireEntries.DistinctSid parse g.localNameBytes g.remoteNameBytes)⌝ ∗
    (g.localIkA ↦ₛ g.localIk.publicKey.bytes.toList) ∗
    ((g.localAddr + 8#64) ↦₆₄ g.localNamePtr) ∗
    ((g.localAddr + 16#64) ↦₆₄ BitVec.ofNat 64 g.localNameBytes.length) ∗
    (g.localNamePtr ↦ₛ g.localNameBytes) ∗
    (g.remoteIkA ↦ₛ g.remoteIk.publicKey.bytes.toList) ∗
    ((g.remoteAddr + 8#64) ↦₆₄ g.remoteNamePtr) ∗
    ((g.remoteAddr + 16#64) ↦₆₄ BitVec.ofNat 64 g.remoteNameBytes.length) ∗
    (g.remoteNamePtr ↦ₛ g.remoteNameBytes) ∗
    stackAt s.sp isSameAccountExtStack
  post := fun g s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
    (g.localIkA ↦ₛ g.localIk.publicKey.bytes.toList) ∗
    ((g.localAddr + 8#64) ↦₆₄ g.localNamePtr) ∗
    ((g.localAddr + 16#64) ↦₆₄ BitVec.ofNat 64 g.localNameBytes.length) ∗
    (g.localNamePtr ↦ₛ g.localNameBytes) ∗
    (g.remoteIkA ↦ₛ g.remoteIk.publicKey.bytes.toList) ∗
    ((g.remoteAddr + 8#64) ↦₆₄ g.remoteNamePtr) ∗
    ((g.remoteAddr + 16#64) ↦₆₄ BitVec.ofNat 64 g.remoteNameBytes.length) ∗
    (g.remoteNamePtr ↦ₛ g.remoteNameBytes) ∗
    stackAt s0.sp isSameAccountExtStack

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
private theorem isSameAccountDistinctRaw_ext_ok {b : BitVec 64} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
      ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr isSameAccountSym)
      (isSameAccountDistinctRawExtSpec uuidTryParse) := by
  simp only [isSameAccountDistinctRawExtSpec]
  have hEq' := publicKeyEq_ok_at_isSameAccount_ext b
    (hookSat_cliExternsWith_chain (by rfl_kernel) hOk.blackBox)
  simp only [Getters.publicKeyEqSpecExt] at hEq'
  have hParse := parseSidRel_ok_at_ext b (Rust.withPanics (cliExternsWith ext))
  simp only [parseSidRelExtSpec] at hParse
  wp_init x s0
  have hfn : libsignalSessionCode.fnOff isSameAccountSym =
      num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") :=
    ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics (cliExternsWith ext)) hfn
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")) 192
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b
        (Rust.withPanics (cliExternsWith ext))).fnAddr isSameAccountSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hEq' hParse ⊢
  clear hfn hOk
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (cliExternsWith ext))).fnAddr isSameAccountSym = entry
  examples_hide_fetches
  obtain ⟨localIkA, localIk, localAddr, localNamePtr, localNameBytes,
    remoteIkA, remoteIk, remoteAddr, remoteNamePtr, remoteNameBytes⟩ := x
  dsimp only at *
  have h_or : localIk ≠ remoteIk ∨
      Pqxdh.WireEntries.DistinctSid uuidTryParse localNameBytes remoteNameBytes := h
  subst h_1 h_2 h_3 h_4
  rw [stackAt_isSameAccountExt_split s0.sp]
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
    have hDist : Pqxdh.WireEntries.DistinctSid uuidTryParse localNameBytes remoteNameBytes :=
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
          have hrel1 : Pqxdh.WireEntries.SidCellsRel (serviceIdParse uuidTryParse localNameBytes) _ _ _ := ‹_›
          have hrel2 : Pqxdh.WireEntries.SidCellsRel (serviceIdParse uuidTryParse remoteNameBytes) _ _ _ := ‹_›
          have hne := cond_uuid_words_ne_ext (sidCellsRel_ne_of_distinct_ext hDist hrel1 hrel2
            (by revert hb0; rcases sidCellsRel_b0_cases_ext hrel1 with rfl | rfl | rfl <;> decide)
            (by revert hb1; rcases sidCellsRel_b0_cases_ext hrel2 with rfl | rfl | rfl <;> decide)
            (by revert hb01; rcases sidCellsRel_b0_cases_ext hrel1 with rfl | rfl | rfl <;>
                rcases sidCellsRel_b0_cases_ext hrel2 with rfl | rfl | rfl <;> decide))
          wp_done
    · wp_steps
      wp_done
  · simp only [hpk, Bool.false_eq_true, ↓reduceIte] at *
    wp_steps
    wp_done

private def vecU8BufRest_ext (A : RustAlloc) (cap ptr : BitVec 64) (n : Nat) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 n) (cap.toNat - n)

private theorem vecU8At_buf_eq_ext (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (ptr ↦ₛ bs) ∗ vecU8BufRest_ext A cap ptr bs.length := by
  unfold vecU8BufRest_ext
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst hbs
    simp [pointsToBytes_nil]
  · simp only [hcap, ite_false]
    ac_rfl

private theorem vecU8At_expose_ext (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8BufRest_ext A cap ptr bs.length := by
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
    rw [vecU8At_buf_eq_ext A cap ptr bs hle]

private def addrRest_ext (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ g.name.cap) ∗ vecU8BufRest_ext A g.name.cap g.name.ptr g.name.bytes.length ∗
    ((a + 24#64) ↦₈ g.device) ∗ memRegion (a + 0x19#64) 7

private theorem protocolAddressAt_expose_ext (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a =
      ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        addrRest_ext A g a := by
  unfold protocolAddressAt vecGhostAt addrRest_ext
  rw [vecU8At_expose_ext]
  ac_rfl

/-- `<IdentityKey>::is_same_account` with distinct keys or distinct `ServiceId`s under `CliExternsOk P A ext`. -/
theorem isSameAccount_ext_ok {b : BitVec 64} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
      ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr isSameAccountSym)
      (isSameAccountDistinctAtSpec A uuidTryParse isSameAccountExtStack) := by
  refine subroutine_ok_map (isSameAccountDistinctRaw_ext_ok hOk) ?_
  rintro ⟨localIkA, localIk, locA, loc, remoteIkA, remoteIk, remA, rem⟩ R s0 hpre
  simp only [isSameAccountDistinctAtSpec, protocolAddressAt_expose_ext] at hpre
  have hpre' : s0.mem ⊨
      ⌜s0.readReg64 .x0 = localIkA ∧ s0.readReg64 .x1 = locA ∧
        s0.readReg64 .x2 = remoteIkA ∧ s0.readReg64 .x3 = remA ∧
        (localIk ≠ remoteIk ∨ Pqxdh.WireEntries.DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)⌝ ∗
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
           stackAt s0.sp isSameAccountExtStack ∗
           addrRest_ext A loc locA ∗ addrRest_ext A rem remA ∗ R))) :=
    Satisfies.of_eq hpre (by ac_rfl)
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1, hx2, hx3, hdist⟩, hpre'⟩
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hloc_pure, hpre'⟩
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hrem_pure, hm⟩
  refine ⟨⟨localIkA, localIk, locA, loc.name.ptr, loc.name.bytes,
    remoteIkA, remoteIk, remA, rem.name.ptr, rem.name.bytes⟩,
    addrRest_ext A loc locA ∗ addrRest_ext A rem remA ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [isSameAccountDistinctRawExtSpec]
    have hloc_lt : loc.name.bytes.length < 2 ^ 64 := by omega
    have hrem_lt : rem.name.bytes.length < 2 ^ 64 := by omega
    have hm' : s0.mem ⊨
        ⌜s0.readReg64 .x0 = localIkA ∧ s0.readReg64 .x1 = locA ∧
          s0.readReg64 .x2 = remoteIkA ∧ s0.readReg64 .x3 = remA ∧
          loc.name.bytes.length < 2 ^ 64 ∧ rem.name.bytes.length < 2 ^ 64 ∧
          (localIk ≠ remoteIk ∨ Pqxdh.WireEntries.DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)⌝ ∗
        ((localIkA ↦ₛ localIk.publicKey.bytes.toList) ∗
         ((locA + 8#64) ↦₆₄ loc.name.ptr) ∗
         ((locA + 16#64) ↦₆₄ BitVec.ofNat 64 loc.name.bytes.length) ∗
         (loc.name.ptr ↦ₛ loc.name.bytes) ∗
         (remoteIkA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
         ((remA + 8#64) ↦₆₄ rem.name.ptr) ∗
         ((remA + 16#64) ↦₆₄ BitVec.ofNat 64 rem.name.bytes.length) ∗
         (rem.name.ptr ↦ₛ rem.name.bytes) ∗
         stackAt s0.sp isSameAccountExtStack ∗
         addrRest_ext A loc locA ∗ addrRest_ext A rem remA ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hloc_lt, hrem_lt, hdist⟩, hm⟩
    exact Satisfies.of_eq hm' (by ac_rfl)
  · simp only [isSameAccountDistinctRawExtSpec, isSameAccountDistinctAtSpec,
      protocolAddressAt_expose_ext] at hpost ⊢
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
         stackAt s0.sp isSameAccountExtStack ∗
         addrRest_ext A loc locA ∗ addrRest_ext A rem remA ∗ R) :=
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
             stackAt s0.sp isSameAccountExtStack ∗
             addrRest_ext A loc locA ∗ addrRest_ext A rem remA ∗ R))) := by
      rw [satisfies_pure_sepConj]
      refine ⟨hret, ?_⟩
      rw [satisfies_pure_sepConj]
      refine ⟨hloc_pure, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hrem_pure, hpost'⟩
    exact Satisfies.of_eq hpost'' (by ac_rfl)

theorem isSameAccount_inImage_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr isSameAccountSym)
      ((isSameAccountDistinctAtSpec A uuidTryParse isSameAccountExtStack).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (isSameAccount_ext_ok hOk)

end IsSameAccountExt

/-! ## `<PrivateKey>::calculate_agreement` and `<RootKey>::create_chain` -/

section CreateChainExt

private theorem stackAt_calcSub_split_ext (sp : BitVec 64) :
    stackAt sp (48 + extHookStack) =
      memRegion (sp - 16432#64) 48 ∗ stackAt sp extHookStack := by
  change memRegion (sp - 16432#64) 16432 =
    memRegion (sp - 16432#64) 48 ∗ memRegion (sp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := sp - 16432#64) (n := 48) (k := 16384)
    (b' := sp - 16384#64) (by decide) (by bv_omega) (by decide)

private theorem stackAt_calcSub_eq_ctEqFrame_ext (sp : BitVec 64) :
    stackAt sp (48 + extHookStack) =
      stackFrameFor libsignalSessionImage ctEqName sp ∗ stackAt (sp - 48#64) extHookStack := by
  have hframe : memRegion (sp - 48#64) 48 =
      stackFrameFor libsignalSessionImage ctEqName sp := by
    rw [show (48 : Nat) = 8 * 6 by rfl, ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]
    cells_unfold
    simp only [stackFrameFor, ctEqName,
      (ls_lemma% frameBytes "<[u8] as subtle::ConstantTimeEq>::ct_eq"), reduceStackFrameAt]
  change memRegion (sp - 16432#64) 16432 =
    stackFrameFor libsignalSessionImage ctEqName sp ∗ memRegion (sp - 48#64 - 16384#64) 16384
  have hsub : sp - 48#64 - 16384#64 = sp - 16432#64 := by bv_omega
  rw [hsub, ← hframe,
      ProofLib.memRegion_split' (b := sp - 16432#64) (n := 16384) (k := 48)
        (b' := sp - 48#64) (by decide) (by bv_omega) (by decide)]
  ac_rfl

private theorem dhCallAt_of_stage2X {img : Obj.Image} {X : Ratchet.X25519Fn}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      ((LibsignalTripleRatchet.withStack (diffieHellmanSpec X) extHookStack).inImage img)) :
    subroutine_ok prog entry (Keys.dhCallSpecAt img X (48 + extHookStack)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨secA, sec, pubA, pub, ret, sp⟩ R s0 hpre
  dsimp only [Keys.dhCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx8, hsp⟩, hpre⟩
  subst hsp
  rw [stackAt_calcSub_split_ext s0.sp] at hpre
  refine ⟨(secA, sec, pubA, pub, ret), memRegion (s0.sp - 16432#64) 48 ∗ R, ?_, ?_⟩
  · dsimp only [Spec.inImage, LibsignalTripleRatchet.withStack, diffieHellmanSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hx8⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [Spec.inImage, LibsignalTripleRatchet.withStack, diffieHellmanSpec,
      Keys.dhCallSpecAt] at hpost ⊢
    rw [stackAt_calcSub_split_ext s0.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

private theorem zeroizeCallAt_of_stage2X {img : Obj.Image}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      ((LibsignalTripleRatchet.withStack zeroizeSecretSpec extHookStack).inImage img)) :
    subroutine_ok prog entry (Keys.zeroizeCallSpecAt img (48 + extHookStack)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨a, sp⟩ R s0 hpre
  dsimp only [Keys.zeroizeCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hsp⟩, hpre⟩
  subst hsp
  rw [stackAt_calcSub_split_ext s0.sp] at hpre
  refine ⟨a, memRegion (s0.sp - 16432#64) 48 ∗ R, ?_, ?_⟩
  · dsimp only [Spec.inImage, LibsignalTripleRatchet.withStack, zeroizeSecretSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, hx0, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [Spec.inImage, LibsignalTripleRatchet.withStack, zeroizeSecretSpec,
      Keys.zeroizeCallSpecAt] at hpost ⊢
    rw [stackAt_calcSub_split_ext s0.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

private theorem shimCallAt_of_stage2X {img : Obj.Image}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      ((LibsignalTripleRatchet.withStack sessionShimSpec (48 + extHookStack)).inImage img)) :
    subroutine_ok prog entry (Keys.shimCallSpecAt img (48 + extHookStack)) := by
  refine subroutine_ok_map h ?_
  rintro sp R s0 hpre
  dsimp only [Keys.shimCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsp⟩, hpre⟩
  subst hsp
  refine ⟨(), R, ?_, ?_⟩
  · dsimp only [Spec.inImage, LibsignalTripleRatchet.withStack, sessionShimSpec, noAllocShimSpec]
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, hpre⟩
  · intro sf hpost
    dsimp only [Spec.inImage, LibsignalTripleRatchet.withStack, sessionShimSpec, noAllocShimSpec,
      Keys.shimCallSpecAt] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

private theorem allocCallAt_of_stage2X {img : Obj.Image} {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      ((rustAllocSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok prog entry (Keys.allocCallSpecAt img A (48 + extHookStack)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨size, align, sp⟩ R s0 hpre
  dsimp only [Keys.allocCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hlay, hsp⟩, hpre⟩
  subst hsp
  rw [stackAt_calcSub_split_ext s0.sp] at hpre
  refine ⟨(size, align), memRegion (s0.sp - 16432#64) 48 ∗ R, ?_, ?_⟩
  · dsimp only [Spec.inImage, rustAllocSpecWithStack]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hlay⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [Spec.inImage, rustAllocSpecWithStack, Keys.allocCallSpecAt] at hpost ⊢
    rw [stackAt_calcSub_split_ext s0.sp]
    ac_nf at hpost ⊢

section CtEqWrap

attribute [local irreducible] libsignalSessionImage

set_option maxRecDepth 200000 in
private theorem ctEqCallAt_of_ext32 {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry ConsumeMessageKeyTransfer.ctEqSliceROSpecExt) :
    subroutine_ok prog entry (Keys.ctEqCallSpecAt img (48 + extHookStack)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  dsimp only [Keys.ctEqCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  rw [stackAt_calcSub_eq_ctEqFrame_ext sp] at hpre
  refine ⟨(p1, k1, p2, k2, sp), R, ?_, ?_⟩
  · dsimp only [ConsumeMessageKeyTransfer.ctEqSliceROSpecExt]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hx0, hx1, hsp, hk1, hk2⟩, Satisfies.of_eq hpre rfl⟩
  · intro sf hpost
    dsimp only [ConsumeMessageKeyTransfer.ctEqSliceROSpecExt, Keys.ctEqCallSpecAt] at hpost ⊢
    rw [stackAt_calcSub_eq_ctEqFrame_ext sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hres, htr⟩, hpost⟩
    refine ⟨⟨?_, htr⟩, hpost⟩
    have h8 : ((sf.readReg64 .x0).setWidth 32).setWidth 8 = (sf.readReg64 .x0).setWidth 8 := by
      bv_omega
    rw [← h8, hres]
    split <;> rfl

end CtEqWrap

/-- `<PrivateKey>::calculate_agreement` at residual stack `48 + extHookStack` under `CliExternsOk P A ext`. -/
theorem calculateAgreement_at_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr calculateAgreementName)
      ((Keys.calculateAgreementSpecAt P.C.X A (48 + extHookStack)).inImage img) := by
  have hC := (Slots.Stage2ContractsExt.of_externsOk hOk img).toStage2ContractsX
  have hct0 : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr ctEqName)
      ConsumeMessageKeyTransfer.ctEqSliceROSpecExt :=
    ConsumeMessageKeyTransfer.ctEqRO_ok_ext32 img.base
      (hookSat_cliExternsWith_chain (by rfl_kernel) hOk.blackBox)
  have hct_at : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" -
          ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")))
      ConsumeMessageKeyTransfer.ctEqSliceROSpecExt := by
    dsimp only [tripleRatchetProgAtExt] at hct0 ⊢
    rwa [← Program.fnAddr_rel
      (ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement")
      (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq")
      (k := num% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")) rfl]
  exact Keys.calculateAgreement_ok_of_hooks_gen (subStack := 48 + extHookStack) (by decide) himg
    (dhCallAt_of_stage2X (hC.dh_ok_at calculateAgreementName _))
    (zeroizeCallAt_of_stage2X (hC.shared_drop_ok_at calculateAgreementName _))
    (ctEqCallAt_of_ext32 hct_at)
    (shimCallAt_of_stage2X (hC.toAllocContractsX.shim_ok_at calculateAgreementName _ (48 + extHookStack)))
    (allocCallAt_of_stage2X (hC.toAllocContractsX.alloc_ok_at calculateAgreementName _))
    (zeroizeCallAt_of_stage2X (hC.static_drop_ok_at calculateAgreementName _))

private theorem stackAt_extract_split_calc (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 768 ∗ stackAt sp (160 + (48 + extHookStack)) := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 768 ∗ memRegion (sp - 16592#64) 16592
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 768) (k := 16592)
    (b' := sp - 16592#64) (by decide) (by bv_omega) (by decide)

private theorem stackAt_extract_split_expand (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 336 ∗ stackAt sp expandMultiInfoStackExt := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 336 ∗ memRegion (sp - 17024#64) 17024
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 336) (k := 17024)
    (b' := sp - 17024#64) (by decide) (by bv_omega) (by decide)

private theorem stackAt_extract_split_dealloc (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 976 ∗ stackAt sp extHookStack := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 976 ∗ memRegion (sp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 976) (k := 16384)
    (b' := sp - 16384#64) (by decide) (by bv_omega) (by decide)

private theorem calcCallAt_extractStackExt {img : Obj.Image} {X : Ratchet.X25519Fn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hag : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr calculateAgreementName)
      ((Keys.calculateAgreementSpecAt X A (48 + extHookStack)).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr createChainName +
        BitVec.ofNat 64 (num% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" -
          ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")))
      ((Keys.calculateAgreementCallSpecAt X A extractStackExt).inImage img) := by
  have hrel := Keys.subroutine_ok_rel_rebase
    (k := num% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" -
      ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"))
    hag
    (ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement")
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")
    (by decide)
  apply subroutine_ok_outcome_intro
  rintro ⟨ourA, our, theirA, their, ret, sp⟩ R s0 hpc hrun hpre hsp
  dsimp only [Spec.inImage, Keys.calculateAgreementCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hL, ⟨hx0, hx1, hx8, hsp_eq⟩, hpre⟩
  subst hsp_eq
  rw [stackAt_extract_split_calc s0.sp] at hpre
  have hpre' : s0.mem ⊨ ((Keys.calculateAgreementSpecAt X A (48 + extHookStack)).inImage img).pre
      ⟨ourA, our, theirA, their, ret⟩ s0 ∗ (memRegion (s0.sp - 17360#64) 768 ∗ R) := by
    dsimp only [Spec.inImage, Keys.calculateAgreementSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hL, ⟨hx0, hx1, hx8⟩, by arm64_sep_close⟩
  refine hrel.mono_outcome ⟨ourA, our, theirA, their, ret⟩ (memRegion (s0.sp - 17360#64) 768 ∗ R)
      s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, Keys.calculateAgreementSpecAt,
      Keys.calculateAgreementCallSpecAt] at hq ⊢
    rw [stackAt_extract_split_calc s0.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    exact ⟨htr, by arm64_sep_close⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, Keys.calculateAgreementSpecAt,
      Keys.calculateAgreementCallSpecAt] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    have hany : anyHeap ∗ memRegion (s0.sp - 17360#64) 768 ⊢ anyHeap :=
      entails_anyHeap _
    exact Satisfies.mono (sepConj_mono_left hany) (Satisfies.of_eq hq.2 (by ac_rfl))
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, by
      dsimp only [Spec.inImage, Keys.calculateAgreementSpecAt] at hq
      rw [satisfies_pure_sepConj] at hq; exact False.elim hq.1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom.1, by
      dsimp only [Spec.inImage, Keys.calculateAgreementSpecAt] at hoom
      rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.2.1⟩))

private theorem extractKey32_at_extractStackExt {img : Obj.Image} {C : Crypto}
    {H : String → Option (State → State)}
    (hext : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr extractName)
      ((extractSpecExt C.F).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr createChainName +
        BitVec.ofNat 64 (num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" -
          ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")))
      (Keys.extractKey32StackSpecAt C.F img extractStackExt) := by
  have hrel := Keys.subroutine_ok_rel_rebase
    (k := num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" -
      ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"))
    hext
    (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract")
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")
    (by decide)
  refine subroutine_ok_map hrel ?_
  rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [Keys.extractKey32StackSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hx4, hsp, hsalt_ne, hikm⟩, hpre⟩
  subst hsp
  refine ⟨⟨ret, saltA, some (Ratchet.keyToBytesVec32 rk), ikmA, ikm⟩, R, ?_, ?_⟩
  · dsimp only [Spec.inImage, extractSpecExt, optSaltAt]
    rw [eq_true hsalt_ne, pure_true, emp_sepConj, Keys.pointsTo_keyVec_toList]
    simp only [Option.isSome_some, reduceCtorEq, IsEmpty.forall_iff, forall_const, true_and,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hx2, hx3, hx4, hikm⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [Spec.inImage, extractSpecExt, ExtractGhost.prk, optSaltAt,
      Keys.extractKey32StackSpecAt] at hpost ⊢
    rw [eq_true hsalt_ne, pure_true, emp_sepConj, Keys.pointsTo_keyVec_toList] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

private theorem expandCells8_at_extractStackExt {img : Obj.Image} {C : Crypto}
    {H : String → Option (State → State)}
    (hexp : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr expandMultiInfoName)
      ((expandMultiInfoSpecExt C.F).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr createChainName +
        BitVec.ofNat 64 (num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" -
          ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")))
      (Keys.expandCellsStackSpecAt C.F img 8 extractStackExt) := by
  have hrel := Keys.subroutine_ok_rel_rebase
    (k := num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" -
      ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"))
    hexp
    (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info")
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")
    (by decide)
  refine subroutine_ok_map hrel ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [Keys.expandCellsStackSpecAt] at hpre
  rw [stackAt_extract_split_expand sp, ← ProofLib.memRegion_cells okmA 8 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hinfo, hlen⟩, hpre⟩
  subst hsp
  refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, 8 * 8⟩,
    memRegion (s0.sp - 17360#64) 336 ∗ R, ?_, ?_⟩
  · dsimp only [Spec.inImage, expandMultiInfoSpecExt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hx2, hx3, hprk, hinfo, hlen⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [Spec.inImage, expandMultiInfoSpecExt, Keys.expandCellsStackSpecAt] at hpost ⊢
    rw [stackAt_extract_split_expand s0.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand C.F prk info (8 * 8)) ∗
        stackAt s0.sp expandMultiInfoStackExt ∗ memRegion (s0.sp - 17360#64) 336) ∗ R)
      (Keys.hmacCore_entails_cells C.F hkdfA prk)
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

private theorem dealloc_at_extractStackExt {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)} {addr : BitVec 64}
    (hd : subroutine_ok (libsignalSessionCode.rebase img.base H) addr
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H) addr
      (Keys.deallocStackSpecAt A img extractStackExt) := by
  refine subroutine_ok_map (Keys.deallocExtStack_of_rustDeallocExtern_rebase hd) ?_
  rintro ⟨p, size, align, sp⟩ R s0 hpre
  dsimp only [Keys.deallocStackSpecAt] at hpre
  rw [stackAt_extract_split_dealloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨(p, size, align, sp), memRegion (sp - 17360#64) 976 ∗ R, ?_, ?_⟩
  · dsimp only [Keys.deallocExtStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [Keys.deallocExtStackSpec, Keys.deallocStackSpecAt] at hpost ⊢
    rw [stackAt_extract_split_dealloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

/-- `<RootKey>::create_chain` at `extractStackExt = 17360` bytes under `CliExternsOk P A ext`. -/
theorem rootKeyCreateChain_at_extractStackExt_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr createChainName)
      ((Keys.createChainSpecAt P.C A extractStackExt).inImage img) := by
  have hHkdf := HkdfContractsExt.of_externsOk img hOk
  have hA := Slots.allocContractsX_cliExternsWith_of_externsOk hOk img
  exact Keys.createChain_ok_of_hooks_gen (callStack := extractStackExt) (by decide) himg
    (calcCallAt_extractStackExt (calculateAgreement_at_ext_ok himg hOk))
    (extractKey32_at_extractStackExt (extract_ok_ext' img P.C (cliExternsWith ext) himg hHkdf))
    (expandCells8_at_extractStackExt (expand_multi_info_ok_ext' img P.C (cliExternsWith ext) hHkdf))
    (dealloc_at_extractStackExt (hA.dealloc_ok_at createChainName _))

end CreateChainExt

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate

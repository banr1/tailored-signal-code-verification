/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrAt
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::try_from`: Prologue and Early-Error Branches (`+0x000..+0x0f4`)

Symbolic execution of the prologue on `contractProg img.base ext`: empty input (`+0x04c`),
legacy/unrecognized version (`+0x060..+0x07c`), stack-frame initialization (`+0x080..+0x0b8`),
1-byte empty-body error (`+0x0bc → +0x504`), and non-empty decode-loop entry (`+0x0bc → +0x0f4`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
  bv_sub_add_lit' bv_sub_sub_lit
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
open CryptoVerification.SignalSession.Cli
open RunProofs.Pksm

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
private abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

attribute [local irreducible] Program.fetch Program.externAt?

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## Layout-Independent Fetch Macro -/

private theorem pl_bv_sub_add_lit (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b =
      x - (BitVec.ofNat 64 a - BitVec.ofNat 64 b) := by bv_omega

private theorem pl_bv_sub_add_lit' (x : BitVec 64) (a b : BitVec 64) :
    x - a + b = x - (a - b) := by bv_omega

private theorem pl_bv_sub_sub_lit (x a b : BitVec 64) :
    x - a - b = x - (a + b) := by bv_omega

private theorem pl_bv_add_sub_lit (x a b : BitVec 64) :
    x + a - b = x + (a - b) := by bv_omega

private theorem pl_bv_add_neg_8 (a : BitVec 64) :
    a + 18446744073709551608#64 = a - 8#64 := by bv_omega
private theorem pl_bv_add_neg_16 (a : BitVec 64) :
    a + 18446744073709551600#64 = a - 16#64 := by bv_omega
private theorem pl_bv_add_neg_24 (a : BitVec 64) :
    a + 18446744073709551592#64 = a - 24#64 := by bv_omega
private theorem pl_bv_add_neg_32 (a : BitVec 64) :
    a + 18446744073709551584#64 = a - 32#64 := by bv_omega
private theorem pl_bv_add_neg_40 (a : BitVec 64) :
    a + 18446744073709551576#64 = a - 40#64 := by bv_omega
private theorem pl_bv_add_neg_48 (a : BitVec 64) :
    a + 18446744073709551568#64 = a - 48#64 := by bv_omega
private theorem pl_bv_add_neg_55 (a : BitVec 64) :
    a + 18446744073709551561#64 = a - 55#64 := by bv_omega
private theorem pl_bv_add_neg_56 (a : BitVec 64) :
    a + 18446744073709551560#64 = a - 56#64 := by bv_omega
private theorem pl_bv_add_neg_64 (a : BitVec 64) :
    a + 18446744073709551552#64 = a - 64#64 := by bv_omega
private theorem pl_bv_add_neg_72 (a : BitVec 64) :
    a + 18446744073709551544#64 = a - 72#64 := by bv_omega
private theorem pl_bv_add_neg_80 (a : BitVec 64) :
    a + 18446744073709551536#64 = a - 80#64 := by bv_omega
private theorem pl_bv_add_neg_87 (a : BitVec 64) :
    a + 18446744073709551529#64 = a - 87#64 := by bv_omega
private theorem pl_bv_add_neg_88 (a : BitVec 64) :
    a + 18446744073709551528#64 = a - 88#64 := by bv_omega
private theorem pl_bv_add_neg_96 (a : BitVec 64) :
    a + 18446744073709551520#64 = a - 96#64 := by bv_omega
private theorem pl_bv_add_neg_104 (a : BitVec 64) :
    a + 18446744073709551512#64 = a - 104#64 := by bv_omega
private theorem pl_bv_add_neg_112 (a : BitVec 64) :
    a + 18446744073709551504#64 = a - 112#64 := by bv_omega
private theorem pl_bv_add_neg_128 (a : BitVec 64) :
    a + 18446744073709551488#64 = a - 128#64 := by bv_omega
private theorem pl_bv_add_neg_136 (a : BitVec 64) :
    a + 18446744073709551480#64 = a - 136#64 := by bv_omega
private theorem pl_bv_add_neg_152 (a : BitVec 64) :
    a + 18446744073709551464#64 = a - 152#64 := by bv_omega
private theorem pl_bv_add_neg_160 (a : BitVec 64) :
    a + 18446744073709551456#64 = a - 160#64 := by bv_omega
private theorem pl_bv_add_neg_168 (a : BitVec 64) :
    a + 18446744073709551448#64 = a - 168#64 := by bv_omega
private theorem pl_bv_add_neg_176 (a : BitVec 64) :
    a + 18446744073709551440#64 = a - 176#64 := by bv_omega
private theorem pl_bv_add_neg_184 (a : BitVec 64) :
    a + 18446744073709551432#64 = a - 184#64 := by bv_omega
private theorem pl_bv_add_neg_186 (a : BitVec 64) :
    a + 18446744073709551430#64 = a - 186#64 := by bv_omega
private theorem pl_bv_add_neg_191 (a : BitVec 64) :
    a + 18446744073709551425#64 = a - 191#64 := by bv_omega
private theorem pl_bv_add_neg_192 (a : BitVec 64) :
    a + 18446744073709551424#64 = a - 192#64 := by bv_omega
private theorem pl_bv_add_neg_196 (a : BitVec 64) :
    a + 18446744073709551420#64 = a - 196#64 := by bv_omega
private theorem pl_bv_add_neg_200 (a : BitVec 64) :
    a + 18446744073709551416#64 = a - 200#64 := by bv_omega
private theorem pl_bv_add_neg_216 (a : BitVec 64) :
    a + 18446744073709551400#64 = a - 216#64 := by bv_omega
private theorem pl_bv_add_neg_512 (a : BitVec 64) :
    a + 18446744073709551104#64 = a - 512#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  pl_bv_sub_add_lit pl_bv_sub_add_lit' pl_bv_sub_sub_lit pl_bv_add_sub_lit BitVec.toNat_zero
  pl_bv_add_neg_8 pl_bv_add_neg_16 pl_bv_add_neg_24 pl_bv_add_neg_32 pl_bv_add_neg_40
  pl_bv_add_neg_48 pl_bv_add_neg_55 pl_bv_add_neg_56 pl_bv_add_neg_64 pl_bv_add_neg_72
  pl_bv_add_neg_80 pl_bv_add_neg_87 pl_bv_add_neg_88 pl_bv_add_neg_96 pl_bv_add_neg_104
  pl_bv_add_neg_112 pl_bv_add_neg_128 pl_bv_add_neg_136 pl_bv_add_neg_152 pl_bv_add_neg_160
  pl_bv_add_neg_168 pl_bv_add_neg_176 pl_bv_add_neg_184 pl_bv_add_neg_186 pl_bv_add_neg_191
  pl_bv_add_neg_192 pl_bv_add_neg_196 pl_bv_add_neg_200 pl_bv_add_neg_216 pl_bv_add_neg_512

local macro "pl_prekey_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.ResponderWire.responderWireBin $b $H
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
    $k0 $len)

private theorem pl_spAligned_sub608 {s : State} (h : s.spAligned = true) :
    ((s.sp - 608#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned, beq_iff_eq] at h
  rw [beq_iff_eq]
  bv_bits

/-! ## Section 1: Pure Arithmetic & Condition Helpers for Version Byte & Length (`< 2 ^ 32`) -/

theorem ofNat64_length_ne_zero_w40 {bs : List (BitVec 8)} (hne : bs ≠ []) (hlt : bs.length < 2 ^ 32) :
    BitVec.ofNat 64 bs.length ≠ 0#64 := by
  have hpos : 0 < bs.length := List.length_pos_of_ne_nil hne
  intro h
  have hto := congrArg BitVec.toNat h
  have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
  rw [BitVec.toNat_ofNat, h0, Nat.mod_eq_of_lt (by omega)] at hto
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem cond_eq_subs1_false_w40 {n : Nat} (hge2 : 2 ≤ n) (hlt : n < 2 ^ 32) :
    ConditionHolds .EQ (subsPState64 (BitVec.ofNat 64 n) 1#64) = false := by
  rw [conditionHolds_eq_subsPState64, beq_eq_false_iff_ne]
  intro h
  have hto := congrArg BitVec.toNat h
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_ofNat, h1, Nat.mod_eq_of_lt (by omega)] at hto
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem cond_eq_len1 :
    ConditionHolds .EQ (subsPState64 1#64 1#64) = true := by
  unfold ConditionHolds subsPState64 AddWithCarry64
  decide

/-! ## Section 2: `sret` (`248` bytes) Splitting Helpers for `ErrAt.errCells_*` -/

theorem memRegion248_split_8_8_8 (sret : BitVec 64) :
    memRegion sret 248 ⊢
      ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w0 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗ ((sret + 16#64) ↦₆₄ w16) ∗
        memRegion (sret + 24#64) 224 := by
  rw [show (248 : Nat) = 8 + (8 + (8 + 224)) by decide,
    Prost.memRegion_split sret 8 240 (by decide),
    Prost.memRegion_split (sret + 8#64) 8 232 (by decide),
    Prost.memRegion_split (sret + 8#64 + 8#64) 8 224 (by decide),
    ProofLib.memRegion_eight sret,
    ProofLib.memRegion_eight (sret + 8#64),
    ProofLib.memRegion_eight (sret + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem memRegion248_split_8_8_1 (sret : BitVec 64) :
    memRegion sret 248 ⊢
      ∃∗ b16 : BitVec 8, ∃∗ w8 : BitVec 64, ∃∗ w0 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗ ((sret + 16#64) ↦₈ b16) ∗
        memRegion (sret + 17#64) 231 := by
  rw [show (248 : Nat) = 8 + (8 + (1 + 231)) by decide,
    Prost.memRegion_split sret 8 240 (by decide),
    Prost.memRegion_split (sret + 8#64) 8 232 (by decide),
    Prost.memRegion_split (sret + 8#64 + 8#64) 1 231 (by decide),
    ProofLib.memRegion_eight sret,
    ProofLib.memRegion_eight (sret + 8#64),
    ProofLib.memRegion_one (sret + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

private theorem pl_memRegion248_split16 (sret : BitVec 64) :
    memRegion sret 248 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗ memRegion (sret + 16#64) 232 := by
  rw [show (248 : Nat) = 8 + (8 + 232) by decide,
    Prost.memRegion_split sret 8 240 (by decide),
    Prost.memRegion_split (sret + 8#64) 8 232 (by decide),
    ProofLib.memRegion_eight sret, ProofLib.memRegion_eight (sret + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

/-! ## Section 3: Empty Slice (`x.bytes = []`, `+0x000..+0x024 → +0x04c..+0x05c → +0x504`) -/

/-- (``x.bytes = []`, `x1 = 0``): `cbz x1, +0x04c` at `+0x024` branches to
`+0x04c..+0x05c`, writing `Err(CiphertextMessageTooShort(0))` (`[sret] = errTag`,
`[sret + 8] = speWord 3`, `[sret + 16] = 0`) and jumping to `+0x504` (`1284`). -/
theorem prologue_nil_to_504_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {x : RunCompose.PksmGhost} {s0 : State}
    (_hnil : x.bytes = [])
    (hpc : s0.pc = (contractProg img.base ext).fnAddr preKeyTryFromName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx1 : s0.readReg64 .x1 = 0#64) (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗
        memRegion x.ret 248 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96)
      (fun sf Pf =>
        PostEpilogueState img s0 (s0.sp - 608#64) sf ∧
        (Pf ⊢ (x.ptr ↦ₛ x.bytes) ∗
          pksmErrE A [] x.ret (.ciphertextMessageTooShort 0) ∗
          preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  pl_prekey_fetches img.base H 0 40
  pl_prekey_fetches img.base H 76 20
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (memRegion248_split_8_8_8 x.ret)
      (memRegion96_split_preKeyCalleeSaved (s0.sp - 608#64)))) ?_
  simp only [pl_bv_sub_add_lit', BitVec.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 =>
    SepWPp.exists_pre fun ws16 => SepWPp.exists_pre fun ws8 =>
    SepWPp.exists_pre fun ws0 => ?_
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨by simp [arm64_norm], ?_, hF1, hsym1, by simp [arm64_norm]⟩, ?_⟩
  · rw [State.spAligned]
    simpa [arm64_norm] using pl_spAligned_sub608 hsp
  · unfold preKeyCalleeSavedAt
    simp only [pl_bv_sub_add_lit', BitVec.reduceSub, arm64_norm]
    have herr := errCells_tooShort A [] x.ret 0
    unfold errTag speWord at herr
    change (x.ret ↦₆₄ 18446744073709551615#64) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775811#64) ∗
      ((x.ret + 16#64) ↦₆₄ 0#64) ∗
      memRegion (x.ret + 24#64) 224 ⊢ _ at herr
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left herr))
    apply entails_of_eq; ac_rfl

/-! ## Section 4: Non-Empty Slice Entry (`x.bytes = vb :: body`, `+0x000..+0x024 → +0x028`) -/

/-- When `x.bytes ≠ []` and `x.bytes.length < 2 ^ 32`, steps `+0x000..+0x024` (`10` insns, `40` bytes)
save callee-saved registers, take `cbz x1, +0x04c` as false, and stop at `+0x028` (`40`) before
`ldrb w22, [x0]`. -/
theorem prologue_entry_ne_nil_wpX {img : Obj.Image} {ext : String → Option (State → State)}
    {x : RunCompose.PksmGhost} {s0 : State}
    (hne : x.bytes ≠ []) (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (contractProg img.base ext).fnAddr preKeyTryFromName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 40#64) s0
      (memRegion (s0.sp - 608#64 + 512#64) 96)
      (fun s1 P1 =>
        PostEpilogueState img s0 (s0.sp - 608#64) s1 ∧
        s1.readReg64 .x0 = x.ptr ∧
        s1.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧
        s1.readReg64 .x19 = x.ret ∧
        s1.readReg64 .x29 = s0.sp - 608#64 + 512#64 ∧
        (P1 ⊢ preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      (tryFromQp s0) := by
  have hlen_ne : BitVec.ofNat 64 x.bytes.length ≠ 0#64 :=
    ofNat64_length_ne_zero_w40 hne hlt
  have hlen_beq : (BitVec.ofNat 64 x.bytes.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hlen_ne
  refine SepWPp.mono_pre (memRegion96_split_preKeyCalleeSaved (s0.sp - 608#64)) ?_
  simp only [pl_bv_sub_add_lit', BitVec.reduceSub]
  refine SepWPp.exists_pre fun w19 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w21 => SepWPp.exists_pre fun w22 =>
    SepWPp.exists_pre fun w23 => SepWPp.exists_pre fun w24 =>
    SepWPp.exists_pre fun w25 => SepWPp.exists_pre fun w26 =>
    SepWPp.exists_pre fun w27 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w30 => SepWPp.exists_pre fun w29 => ?_
  let H := Rust.withPanics ext
  pl_prekey_fetches img.base H 0 40
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 40#64) _ _ _ _
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨by simp [arm64_norm], ?_, hF1, hsym1, by simp [arm64_norm]⟩,
    by simp [hx0, arm64_norm], by simp [hx1, arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], ?_⟩
  · rw [State.spAligned]
    simpa [arm64_norm] using pl_spAligned_sub608 hsp
  · unfold preKeyCalleeSavedAt
    simp only [pl_bv_sub_add_lit', BitVec.reduceSub, arm64_norm]
    apply entails_of_eq; ac_rfl

/-! ## Section 5: Version Dispatch at `+0x028` (`40` / Valid) -/

/-- (``(vb >>> 4) < 3#8`, i.e. `vb < 0x30#8``): `+0x028..+0x048` → `+0x070..+0x07c` → `+0x504` (`1284`), writing
`pksmErrE A [] x.ret (.legacyCiphertextVersion (vb >>> 4))`. -/
theorem prologue_28_legacyVer_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {body : List (BitVec 8)} {s0 s1 : State}
    (hcons : x.bytes = vb :: body)
    (hlt3 : (vb >>> 4) < 3#8)
    (hst : PostEpilogueState img s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx19 : s1.readReg64 .x19 = x.ret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s1
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248)
      (fun sf Pf =>
        PostEpilogueState img s0 (s0.sp - 608#64) sf ∧
        (Pf ⊢ pksmErrE A [] x.ret (.legacyCiphertextVersion (vb >>> 4)) ∗ (x.ptr ↦ₛ x.bytes)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcond := cond_cs_ver_of_lt3 hlt3
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body) := by
    rw [hcons, pointsToBytes_cons]
  rw [hbytes]
  refine SepWPp.mono_pre (sepConj_mono_right (memRegion248_split_8_8_1 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun bs16 => SepWPp.exists_pre fun ws8 =>
    SepWPp.exists_pre fun ws0 => ?_
  let H := Rust.withPanics ext
  pl_prekey_fetches img.base H 40 36
  pl_prekey_fetches img.base H 112 16
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s1.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 40#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF2 hsym2
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hF2, hsym2, by simp [htr, arm64_norm]⟩, ?_⟩
  have herr := errCells_legacyVersion A [] x.ret (vb >>> 4)
  unfold errTag speWord at herr
  change (x.ret ↦₆₄ 18446744073709551615#64) ∗
    ((x.ret + 8#64) ↦₆₄ 9223372036854775812#64) ∗
    ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
    memRegion (x.ret + 17#64) 231 ⊢ _ at herr
  refine Entails.trans (Q := ((x.ret ↦₆₄ 18446744073709551615#64) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775812#64) ∗
      ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
      memRegion (x.ret + 17#64) 231) ∗
      ((x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body)))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left herr

/-- (``¬ (vb >>> 4) < 3#8` and `4#8 < (vb >>> 4)`, i.e. `0x4f#8 < vb``): `+0x028..+0x03c` → `+0x060..+0x07c` → `+0x504` (`1284`), writing
`pksmErrE A [] x.ret (.unrecognizedCiphertextVersion (vb >>> 4))`. -/
theorem prologue_28_unrecognizedVer_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {body : List (BitVec 8)} {s0 s1 : State}
    (hcons : x.bytes = vb :: body)
    (hge3 : ¬ (vb >>> 4) < 3#8) (hgt4 : 4#8 < (vb >>> 4))
    (hst : PostEpilogueState img s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx19 : s1.readReg64 .x19 = x.ret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s1
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248)
      (fun sf Pf =>
        PostEpilogueState img s0 (s0.sp - 608#64) sf ∧
        (Pf ⊢ pksmErrE A [] x.ret (.unrecognizedCiphertextVersion (vb >>> 4)) ∗ (x.ptr ↦ₛ x.bytes)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_gt4 hgt4
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body) := by
    rw [hcons, pointsToBytes_cons]
  rw [hbytes]
  refine SepWPp.mono_pre (sepConj_mono_right (memRegion248_split_8_8_1 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun bs16 => SepWPp.exists_pre fun ws8 =>
    SepWPp.exists_pre fun ws0 => ?_
  let H := Rust.withPanics ext
  pl_prekey_fetches img.base H 40 24
  pl_prekey_fetches img.base H 96 32
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s1.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 40#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF2 hsym2
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hF2, hsym2, by simp [htr, arm64_norm]⟩, ?_⟩
  have herr := errCells_unrecognizedVersion A [] x.ret (vb >>> 4)
  unfold errTag speWord at herr
  change (x.ret ↦₆₄ 18446744073709551615#64) ∗
    ((x.ret + 8#64) ↦₆₄ 9223372036854775813#64) ∗
    ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
    memRegion (x.ret + 17#64) 231 ⊢ _ at herr
  refine Entails.trans (Q := ((x.ret ↦₆₄ 18446744073709551615#64) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775813#64) ∗
      ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
      memRegion (x.ret + 17#64) 231) ∗
      ((x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body)))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left herr

/-- Case `¬ (vb >>> 4) < 3#8` and `¬ 4#8 < (vb >>> 4)` (`0x30#8 ≤ vb ≤ 0x4f#8`):
`+0x028..+0x03c` → `+0x060..+0x064` → `+0x080` (`128`). -/
theorem prologue_28_validVer_wpX {img : Obj.Image} {ext : String → Option (State → State)}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {s0 s1 : State}
    (hge3 : ¬ (vb >>> 4) < 3#8) (hle4 : ¬ 4#8 < (vb >>> 4))
    (hst : PostEpilogueState img s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx1 : s1.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s1.readReg64 .x19 = x.ret)
    (hx29 : s1.readReg64 .x29 = s0.sp - 608#64 + 512#64) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 128#64) s1
      (x.ptr ↦₈ vb)
      (fun s2 P2 =>
        PostEpilogueState img s0 (s0.sp - 608#64) s2 ∧
        s2.readReg64 .x29 = s0.sp - 608#64 + 512#64 ∧
        s2.readReg64 .x27 = 0x8000000000000002#64 ∧
        s2.readReg64 .x22 = vb.zeroExtend 64 ∧
        s2.readReg64 .x21 = x.ptr ∧
        s2.readReg64 .x19 = x.ret ∧
        s2.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧
        (P2 ⊢ x.ptr ↦₈ vb))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_le4 hle4
  let H := Rust.withPanics ext
  pl_prekey_fetches img.base H 40 24
  pl_prekey_fetches img.base H 96 8
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 128#64) _ _ _ _
  change s1.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 40#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF2 hsym2
  exact ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hF2, hsym2, by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm],
    by simp [hx19, arm64_norm], by simp [hx1, arm64_norm], Entails.refl _⟩

/-! ## Section 6: Frame Initialization (`+0x080..+0x0b8 → +0x0bc`, `15` insns) -/

/-- Steps `+0x080..+0x0b8` (`128` to `188`, `15` insns): initializes the slice cursor at
`sp' + 296`, zeroes the 4 `Option<u32>` tags (`sp' + 408, 416, 424, 432`), sets the 4 `Vec<u8>`
capacities to `noneCap` (`sp' + 312, 336, 360, 384`), and writes `sp' + 296` to `sp' + 440`. -/
theorem prologue_80_init_wpX {img : Obj.Image} {ext : String → Option (State → State)}
    {sret sp' ptr len : BitVec 64} {vb : BitVec 8} {s0 s2 : State}
    (hst : PostEpilogueState img s0 sp' s2)
    (hpc : s2.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 128#64)
    (hrun : s2.status = .Running)
    (hx29 : s2.readReg64 .x29 = sp' + 512#64)
    (hx27 : s2.readReg64 .x27 = 0x8000000000000002#64)
    (hx22 : s2.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s2.readReg64 .x21 = ptr)
    (hx19 : s2.readReg64 .x19 = sret)
    (hx1 : s2.readReg64 .x1 = len) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 188#64) s2
      (memRegion (sp' + 296#64) 152)
      (fun s3 P3 =>
        PostEpilogueState img s0 sp' s3 ∧
        s3.pstate = subsPState64 len 1#64 ∧
        s3.readReg64 .x29 = sp' + 512#64 ∧
        s3.readReg64 .x27 = 0x8000000000000002#64 ∧
        s3.readReg64 .x22 = vb.zeroExtend 64 ∧
        s3.readReg64 .x21 = ptr ∧
        s3.readReg64 .x20 = len ∧
        s3.readReg64 .x19 = sret ∧
        s3.readReg64 .x8 = sp' + 296#64 ∧
        s3.readReg64 .x2 = len - 1#64 ∧
        (P3 ⊢ ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗
          ((sp' + 304#64) ↦₆₄ (len - 1#64)) ∗
          ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
          ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
          ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  refine SepWPp.mono_pre (memRegion152_init_cells sp') ?_
  refine SepWPp.exists_pre fun w440 =>
    SepWPp.exists_pre fun w432 => SepWPp.exists_pre fun w424 =>
    SepWPp.exists_pre fun w416 => SepWPp.exists_pre fun w408 =>
    SepWPp.exists_pre fun w384 => SepWPp.exists_pre fun w360 =>
    SepWPp.exists_pre fun w336 => SepWPp.exists_pre fun w312 =>
    SepWPp.exists_pre fun c1 => SepWPp.exists_pre fun c0 => ?_
  let H := Rust.withPanics ext
  pl_prekey_fetches img.base H 128 60
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 188#64) _ _ _ _
  change s2.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 128#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hF3, hsym3, by simp [htr, arm64_norm]⟩, by simp [arm64_norm],
    by simp [hx29, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [arm64_norm], by simp [hx19, arm64_norm],
    by simp [arm64_norm], by simp [BitVec.sub_eq_add_neg, arm64_norm], ?_⟩
  unfold noneCap
  try simp only [arm64_norm]
  apply entails_of_eq; ac_rfl

/-! ## Section 7A: Empty Protobuf Body (`body = []`, `x.bytes = [vb]`) -/

attribute [local simp, local arm64_norm, local wp_norm]
  cond_ne_noneCap_add2 cond_eq_noneCap_add1 cond_hi_noneCap_sub1_add3

/-- First half of `x.bytes = [vb]` (`len = 1#64`) after `+0x0bc`:
steps `+0x0bc → +0x300 → +0x460..+0x474 → +0x4e8..+0x4ec → +0x524` (`1316`). -/
theorem prologue_bc_len1_to_524_wpX {img : Obj.Image} {ext : String → Option (State → State)}
    {sret sp' s104 kyberPtr bkPtr ikPtr msgPtr : BitVec 64} {s0 s3 : State}
    (hst : PostEpilogueState img s0 sp' s3)
    (hpc : s3.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 188#64)
    (hrun : s3.status = .Running)
    (hpstate : s3.pstate = subsPState64 1#64 1#64)
    (hx29 : s3.readReg64 .x29 = sp' + 512#64)
    (hx27 : s3.readReg64 .x27 = 0x8000000000000002#64)
    (hx19 : s3.readReg64 .x19 = sret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1316#64) s3
      (((sp' + 104#64) ↦₆₄ s104) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr))
      (fun s4 P4 =>
        (PostEpilogueState img s0 sp' s4 ∧
        s4.readReg64 .x29 = sp' + 512#64 ∧
        s4.readReg64 .x28 = noneCap ∧
        s4.readReg64 .x27 = 0x8000000000000002#64 ∧
        s4.readReg64 .x26 = noneCap ∧
        s4.readReg64 .x23 = noneCap ∧
        s4.readReg64 .x19 = sret ∧
        s4.readReg64 .x8 = msgPtr ∧
        s4.readReg64 .x1 = noneCap) ∧
        (P4 ⊢ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  dsimp only [noneCap]
  let H := Rust.withPanics ext
  pl_prekey_fetches img.base H 188 4
  pl_prekey_fetches img.base H 768 8
  pl_prekey_fetches img.base H 1120 24
  pl_prekey_fetches img.base H 1256 8
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1316#64) _ _ _ _
  change s3.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 188#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF4 hsym4
  refine ⟨⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hF4, hsym4, by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [arm64_norm],
    by simp [hx27, arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [hx19, arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm]⟩, ?_⟩
  apply entails_of_eq; ac_rfl

/-- (``x.bytes = [vb]`, `len = 1#64`, second half `+0x524 → +0x504``): steps `+0x524..+0x550 → +0x5e0..+0x5f0 → +0x604..+0x60c → +0x654..+0x65c → +0x504` (`1284`),
writing `pksmErrE A [] sret .invalidProtobufEncoding`. -/
theorem prologue_524_len1_to_504_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {sret sp' s96 kyberPtr kyberLen bkPtr bkLen ikPtr ikLen msgPtr msgLen : BitVec 64}
    {u412 u420 u428 u436 : BitVec 32} {s0 s4 : State}
    (hst : PostEpilogueState img s0 sp' s4)
    (hpc : s4.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1316#64)
    (hrun : s4.status = .Running)
    (hx29 : s4.readReg64 .x29 = sp' + 512#64)
    (hx28 : s4.readReg64 .x28 = noneCap)
    (hx27 : s4.readReg64 .x27 = 0x8000000000000002#64)
    (hx26 : s4.readReg64 .x26 = noneCap)
    (hx23 : s4.readReg64 .x23 = noneCap)
    (hx19 : s4.readReg64 .x19 = sret)
    (hx1 : s4.readReg64 .x1 = noneCap) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s4
      (memRegion sret 248 ∗
        ((sp' + 96#64) ↦₆₄ s96) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 376#64) ↦₆₄ ikLen) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
        ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436))
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ pksmErrE A [] sret .invalidProtobufEncoding ∗
          ((sp' + 96#64) ↦₆₄ (s4.readReg64 .x8)) ∗
          ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
          ((sp' + 328#64) ↦₆₄ kyberLen) ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 352#64) ↦₆₄ bkLen) ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
          ((sp' + 376#64) ↦₆₄ ikLen) ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
          ((sp' + 400#64) ↦₆₄ msgLen) ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
          ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
          ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  dsimp only [noneCap] at hx28 hx26 hx23 hx1 ⊢
  refine SepWPp.mono_pre (sepConj_mono_left (pl_memRegion248_split16 sret)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun ws8 => SepWPp.exists_pre fun ws0 => ?_
  let H := Rust.withPanics ext
  pl_prekey_fetches img.base H 1316 48
  pl_prekey_fetches img.base H 1504 20
  pl_prekey_fetches img.base H 1540 12
  pl_prekey_fetches img.base H 1620 12
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1284#64) _ _ _ _
  change s4.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1316#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF5 hsym5
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hF5, hsym5, by simp [htr, arm64_norm]⟩, ?_⟩
  have herr := errCells_invalidProtobufEncoding A [] sret
  unfold errTag speWord at herr
  change (sret ↦₆₄ 18446744073709551615#64) ∗
    ((sret + 8#64) ↦₆₄ 9223372036854775810#64) ∗
    memRegion (sret + 16#64) 232 ⊢ _ at herr
  refine Entails.trans (Q := ((sret ↦₆₄ 18446744073709551615#64) ∗
      ((sret + 8#64) ↦₆₄ 9223372036854775810#64) ∗
      memRegion (sret + 16#64) 232) ∗
      (((sp' + 96#64) ↦₆₄ (s4.readReg64 .x8)) ∗
        ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ 18446744073709551615#64) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 360#64) ↦₆₄ 18446744073709551615#64) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 376#64) ↦₆₄ ikLen) ∗
        ((sp' + 384#64) ↦₆₄ 18446744073709551615#64) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
        ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436)))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono_left herr

private theorem memRegion296_split_96_16_184 (sp' : BitVec 64) :
    memRegion sp' 296 ⊢
      ∃∗ s104 : BitVec 64, ∃∗ s96 : BitVec 64,
        memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗ ((sp' + 104#64) ↦₆₄ s104) ∗
        memRegion (sp' + 112#64) 184 := by
  rw [show (296 : Nat) = 96 + (16 + 184) by decide,
    Prost.memRegion_split sp' 96 200 (by decide),
    Prost.memRegion_split (sp' + 96#64) 16 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (memRegion16_split8_8' (sp' + 96#64)))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem memRegion296_pack_96_16_184 (sp' s96 s104 : BitVec 64) :
    memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗ ((sp' + 104#64) ↦₆₄ s104) ∗
    memRegion (sp' + 112#64) 184 ⊢
      memRegion sp' 296 := by
  rw [show (296 : Nat) = 96 + (8 + (8 + 184)) by decide,
    Prost.memRegion_split sp' 96 200 (by decide),
    Prost.memRegion_split (sp' + 96#64) 8 192 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))

private theorem initCells_to_full_cells (sp' : BitVec 64) :
    ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
    ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
    ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
    ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
    ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
    ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
    ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
    ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ⊢
      ∃∗ u436 : BitVec 32, ∃∗ u428 : BitVec 32, ∃∗ u420 : BitVec 32, ∃∗ u412 : BitVec 32,
      ∃∗ msgLen : BitVec 64, ∃∗ msgPtr : BitVec 64,
      ∃∗ ikLen : BitVec 64, ∃∗ ikPtr : BitVec 64,
      ∃∗ bkLen : BitVec 64, ∃∗ bkPtr : BitVec 64,
      ∃∗ kyberLen : BitVec 64, ∃∗ kyberPtr : BitVec 64,
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 376#64) ↦₆₄ ikLen) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
        ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436) := by
  have hm4 (a : BitVec 64) : memRegion a 4 = (∃∗ u : BitVec 32, a ↦₃₂ u) :=
    ProofLib.memRegion_four a
  rw [hm4 (sp' + 412#64), hm4 (sp' + 420#64), hm4 (sp' + 428#64), hm4 (sp' + 436#64)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 320#64))
      (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 344#64))
        (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 368#64))
          (sepConj_mono_right (sepConj_mono_left (memRegion16_split8_8' (sp' + 392#64)))))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem full_cells_entails_memRegion128 (sp' : BitVec 64)
    (w312 kyberPtr kyberLen w336 bkPtr bkLen w360 ikPtr ikLen w384 msgPtr msgLen : BitVec 64)
    (u408 u412 u416 u420 u424 u428 u432 u436 : BitVec 32) :
    ((sp' + 312#64) ↦₆₄ w312) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
    ((sp' + 328#64) ↦₆₄ kyberLen) ∗
    ((sp' + 336#64) ↦₆₄ w336) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
    ((sp' + 352#64) ↦₆₄ bkLen) ∗
    ((sp' + 360#64) ↦₆₄ w360) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
    ((sp' + 376#64) ↦₆₄ ikLen) ∗
    ((sp' + 384#64) ↦₆₄ w384) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
    ((sp' + 400#64) ↦₆₄ msgLen) ∗
    ((sp' + 408#64) ↦₃₂ u408) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
    ((sp' + 416#64) ↦₃₂ u416) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
    ((sp' + 424#64) ↦₃₂ u424) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
    ((sp' + 432#64) ↦₃₂ u432) ∗ ((sp' + 436#64) ↦₃₂ u436) ⊢
      memRegion (sp' + 312#64) 128 := by
  have hw24 (a w0 w1 w2 : BitVec 64) :
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
    rw [show (24 : Nat) = 8 + (8 + 8) by decide,
      Prost.memRegion_split a 8 16 (by decide),
      Prost.memRegion_split (a + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  have hu8 (a : BitVec 64) (v0 v4 : BitVec 32) :
      (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v4) ⊢ memRegion a 8 := by
    rw [show (8 : Nat) = 4 + 4 by decide, Prost.memRegion_split a 4 4 (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _) (pointsTo32_entails_memRegion _ _)
  have h312 := hw24 (sp' + 312#64) w312 kyberPtr kyberLen
  have h336 := hw24 (sp' + 336#64) w336 bkPtr bkLen
  have h360 := hw24 (sp' + 360#64) w360 ikPtr ikLen
  have h384 := hw24 (sp' + 384#64) w384 msgPtr msgLen
  have h408 := hu8 (sp' + 408#64) u408 u412
  have h416 := hu8 (sp' + 416#64) u416 u420
  have h424 := hu8 (sp' + 424#64) u424 u428
  have h432 := hu8 (sp' + 432#64) u432 u436
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h312 h336 h360 h384 h408 h416 h424 h432
  rw [show (128 : Nat) = 24 + (24 + (24 + (24 + (8 + (8 + (8 + 8)))))) by decide,
    Prost.memRegion_split (sp' + 312#64) 24 104 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64) 24 80 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64) 24 56 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64) 24 32 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64) 8 24 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Q :=
      (((sp' + 312#64) ↦₆₄ w312) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen)) ∗
      (((sp' + 336#64) ↦₆₄ w336) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗ ((sp' + 352#64) ↦₆₄ bkLen)) ∗
      (((sp' + 360#64) ↦₆₄ w360) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen)) ∗
      (((sp' + 384#64) ↦₆₄ w384) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen)) ∗
      (((sp' + 408#64) ↦₃₂ u408) ∗ ((sp' + 412#64) ↦₃₂ u412)) ∗
      (((sp' + 416#64) ↦₃₂ u416) ∗ ((sp' + 420#64) ↦₃₂ u420)) ∗
      (((sp' + 424#64) ↦₃₂ u424) ∗ ((sp' + 428#64) ↦₃₂ u428)) ∗
      (((sp' + 432#64) ↦₃₂ u432) ∗ ((sp' + 436#64) ↦₃₂ u436)))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono h312
    (sepConj_mono h336
      (sepConj_mono h360
        (sepConj_mono h384
          (sepConj_mono h408
            (sepConj_mono h416
              (sepConj_mono h424 h432))))))

private theorem pl_region152_repack (sp' c0 c1 w440 : BitVec 64) :
    ((sp' + 296#64) ↦₆₄ c0) ∗ ((sp' + 304#64) ↦₆₄ c1) ∗
      memRegion (sp' + 312#64) 128 ∗ ((sp' + 440#64) ↦₆₄ w440) ⊢
      memRegion (sp' + 296#64) 152 := by
  rw [show (152 : Nat) = 8 + (8 + (128 + 8)) by decide,
    Prost.memRegion_split (sp' + 296#64) 8 144 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64) 8 136 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64 + 8#64) 128 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _) (pointsTo64_entails_memRegion _ _)))

/-- (``+0x0bc → +0x504` / `188 → 1284` combined segment for `len = 1#64`, `body = []``): writes `pksmErrE A [] sret .invalidProtobufEncoding` and repacks `memRegion sp' 296` and
`memRegion (sp' + 296) 152`. -/
theorem prologue_bc_len1_to_504_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {sret sp' ptr : BitVec 64} {s0 s3 : State}
    (hst : PostEpilogueState img s0 sp' s3)
    (hpc : s3.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 188#64)
    (hrun : s3.status = .Running)
    (hpstate : s3.pstate = subsPState64 1#64 1#64)
    (hx29 : s3.readReg64 .x29 = sp' + 512#64)
    (hx27 : s3.readReg64 .x27 = 0x8000000000000002#64)
    (hx19 : s3.readReg64 .x19 = sret) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64) s3
      (memRegion sret 248 ∗
        memRegion sp' 296 ∗
        ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗
        ((sp' + 304#64) ↦₆₄ 0#64) ∗
        (((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
          ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
          ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)))
      (fun sf Pf =>
        PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ pksmErrE A [] sret .invalidProtobufEncoding ∗
          memRegion sp' 296 ∗
          memRegion (sp' + 296#64) 152))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (memRegion296_split_96_16_184 sp')
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (initCells_to_full_cells sp')))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun u436 => SepWPp.exists_pre fun u428 =>
    SepWPp.exists_pre fun u420 => SepWPp.exists_pre fun u412 =>
    SepWPp.exists_pre fun msgLen => SepWPp.exists_pre fun msgPtr =>
    SepWPp.exists_pre fun ikLen => SepWPp.exists_pre fun ikPtr =>
    SepWPp.exists_pre fun bkLen => SepWPp.exists_pre fun bkPtr =>
    SepWPp.exists_pre fun kyberLen => SepWPp.exists_pre fun kyberPtr =>
    SepWPp.exists_pre fun s104 => SepWPp.exists_pre fun s96 => ?_
  refine SepWPp.mono_pre
    (P' := (((sp' + 104#64) ↦₆₄ s104) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr)) ∗
      (memRegion sret 248 ∗
        memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗ memRegion (sp' + 112#64) 184 ∗
        ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗ ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 376#64) ↦₆₄ ikLen) ∗ ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.bind_frame_entails
    (prologue_bc_len1_to_524_wpX hst hpc hrun hpstate hx29 hx27 hx19) ?_
  intro s4 hpc4 hrun4 ⟨hst4, hx29_4, hx28_4, hx27_4, hx26_4, hx23_4, hx19_4, _, hx1_4⟩
  refine SepWPp.mono_pre
    (P' := (memRegion sret 248 ∗
        ((sp' + 96#64) ↦₆₄ s96) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 376#64) ↦₆₄ ikLen) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
        ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436)) ∗
      (memRegion sp' 96 ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 112#64) 184 ∗
        ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (prologue_524_len1_to_504_wpE (A := A) hst4 hpc4 hrun4 hx29_4 hx28_4 hx27_4 hx26_4 hx23_4 hx19_4 hx1_4) ?_
  intro sf Pf ⟨hstf, hentf⟩
  refine ⟨hstf, Entails.trans (sepConj_mono_left hentf) ?_⟩
  have hm296 := memRegion296_pack_96_16_184 sp' (s4.readReg64 .x8) ikPtr
  have hm128 := full_cells_entails_memRegion128 sp'
    0x8000000000000002#64 kyberPtr kyberLen noneCap bkPtr bkLen noneCap ikPtr ikLen noneCap msgPtr msgLen
    0#32 u412 0#32 u420 0#32 u428 0#32 u436
  have hm152 := pl_region152_repack sp' (ptr + 1#64) 0#64 (sp' + 296#64)
  refine Entails.trans (Q := pksmErrE A [] sret .invalidProtobufEncoding ∗
      (memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ (s4.readReg64 .x8)) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 112#64) 184) ∗
      (((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        (((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
          ((sp' + 328#64) ↦₆₄ kyberLen) ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 352#64) ↦₆₄ bkLen) ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
          ((sp' + 376#64) ↦₆₄ ikLen) ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
          ((sp' + 400#64) ↦₆₄ msgLen) ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
          ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
          ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine sepConj_mono_right (sepConj_mono hm296 ?_)
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hm128)))
    (by simpa [sepConj_assoc] using hm152)

/-! ## Section 7B: Non-Empty Protobuf Body (`body = b1 :: bs1`, `+0x0bc..+0x0d0 → +0x0f4`) -/

/-- When `2 ≤ n < 2 ^ 32`, `b.eq +0x300` at `+0x0bc` is NOT taken;
steps `+0x0bc..+0x0d0` (`6` insns) initialize `x26, x23, x28, x25` and branch to `+0x0f4` (`244`)
with `PreKeyLoopRegs`. -/
theorem prologue_bc_gt1_to_f4_wpX {img : Obj.Image}
    {ext : String → Option (State → State)}
    {sret sp' ptr : BitVec 64} {vb : BitVec 8} {n : Nat}
    {s0 s3 : State}
    (hge2 : 2 ≤ n) (hlt : n < 2 ^ 32)
    (hst : PostEpilogueState img s0 sp' s3)
    (hpc : s3.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 188#64)
    (hrun : s3.status = .Running)
    (hpstate : s3.pstate = subsPState64 (BitVec.ofNat 64 n) 1#64)
    (hx29 : s3.readReg64 .x29 = sp' + 512#64)
    (hx27 : s3.readReg64 .x27 = 0x8000000000000002#64)
    (hx22 : s3.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s3.readReg64 .x21 = ptr)
    (hx20 : s3.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx19 : s3.readReg64 .x19 = sret)
    (hx8 : s3.readReg64 .x8 = sp' + 296#64)
    (hx2 : s3.readReg64 .x2 = BitVec.ofNat 64 n - 1#64) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 244#64) s3
      emp
      (fun s4 P4 =>
        (PreKeyLoopRegs sp' sret (BitVec.ofNat 64 n) ptr vb s4 ∧
        PostEpilogueState img s0 sp' s4 ∧
        s4.readReg64 .x28 = sp' + 296#64 ∧
        s4.readReg64 .x26 = sp' + 304#64 ∧
        s4.readReg64 .x2 = BitVec.ofNat 64 n - 1#64) ∧
        (P4 ⊢ emp))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr⟩
  have hcond_eq := cond_eq_subs1_false_w40 hge2 hlt
  let H := Rust.withPanics ext
  pl_prekey_fetches img.base H 188 24
  dsimp only [contractProg, tripleRatchetProgAtExt] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64) _ _ _ _
  change s3.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 188#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF4 hsym4
  refine ⟨⟨⟨by simp [hsp_eq, arm64_norm], by simp [hx29, arm64_norm],
    by simp [hx27, arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [hx22, arm64_norm],
    by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
    by simp [hx19, arm64_norm]⟩,
    ⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
      hF4, hsym4, by simp [htr, arm64_norm]⟩,
    by simp [arm64_norm],
    by simp [arm64_norm],
    by simp [hx2, arm64_norm]⟩, Entails.refl _⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

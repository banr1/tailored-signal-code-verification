/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunked
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import ProofLib.SepLogic.WPp

/-!
# Verification of `V1State.Chunked.HeaderSent::encoded_len` and Wired Chunked Theorems

Verifies `V1State.Chunked.HeaderSent::encoded_len` (`0x39fc8`, `0x69f70`, 67 instructions) and
wires `BL` callee contracts to establish `[local#1]` and `[local#2]` theorems for both
`Chunked.Ct1Sampled` and `Chunked.HeaderSent`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open EncodedLen

local notation "tripleRatchetProgAtExt" => CryptoVerification.LibsignalTripleRatchet.contractProg

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. `V1State.Chunked.HeaderSent::encoded_len` (`0x39fc8`, `0x69f70`, 67 insns) -/

/-- Entry-point membership for the two identical-structure copies of `chunked::HeaderSent::encoded_len`
    (`0x39fc8`, `0x69f70`). -/
def IsChunkedHeaderSentEntry (b : BitVec 64) (abs : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b abs).fnAddr chunkedHeaderSentEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr chunkedHeaderSentEncodedLenLocal2Name = entry

open Lean Elab Tactic in
elab "headerSent_fetches_range " hfn:ident kStart:num kEnd:num : tactic => do
  let offs := #[0x3a0ac, 0x64b78]
  let fnOffs := #[
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x3a0ac,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x64b78
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    if k != 32 && k != 92 && k != 192 then
      let decs := offs.map fun off =>
        mkIdent (`CryptoVerification.SpqrV1.ProtoRepr |>.str
          s!"spqrChunkedHeaderSentBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
      let d0 := decs[0]!; let d1 := decs[1]!
      let f0 := fnOffs[0]!; let f1 := fnOffs[1]!
      let kq := Syntax.mkNumLit (toString k)
      if k == 0 then
        let pf0 := mkIdent (`CryptoVerification.blkPC_188_rebase_fetch_base)
        let pf1 := mkIdent (`CryptoVerification.blkPC_414_rebase_fetch_base)
        evalTactic (← `(tactic|
          have := dualBlockP2_fetch_entry $hfn
            (fun b H => $fetchEntry (b := b) (H := H) $f0 (by decide) $d0)
            (fun b H => $fetchEntry (b := b) (H := H) $f1 (by decide) $d1)
            (fun [LibsignalPlacement] H => $pf0 _ H)
            (fun [LibsignalPlacement] H => $pf1 _ H)))
      else
        let kHex := String.ofList (Nat.toDigits 16 k)
        let pf0 := mkIdent (`CryptoVerification |>.str s!"blkPC_188_rebase_fetch_0x{kHex}")
        let pf1 := mkIdent (`CryptoVerification |>.str s!"blkPC_414_rebase_fetch_0x{kHex}")
        evalTactic (← `(tactic|
          have := dualBlockP2_fetch_add $hfn (k := $kq)
            (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f0 (by decide) $d0)
            (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f1 (by decide) $d1)
            (fun [LibsignalPlacement] H => $pf0 _ H)
            (fun [LibsignalPlacement] H => $pf1 _ H)))

/-- Unpacked representation of `chunkedHeaderSentPBPinnedAt` with the 3 option `cap` words exposed. -/
def chunkedHeaderSentUnpacked (A : RustAlloc) (g : ChunkedHeaderSentPBGhost)
    (a : BitVec 64) (m : V1State.Chunked.HeaderSent) : SepProp :=
  (a ↦₆₄ optEkSentCap g.uc m.uc) ∗ optEkSentRest A g.uc a m.uc ∗
    ((a + 80#64) ↦₆₄ optPolyEncCap g.sendingEk m.sendingEk) ∗
    optPolyEncRest A g.sendingEk (a + 80#64) m.sendingEk ∗
    ((a + 136#64) ↦₆₄ optPolyDecCap g.receivingCt1 m.receivingCt1) ∗
    optPolyDecRest A g.receivingCt1 (a + 136#64) m.receivingCt1

theorem chunkedHeaderSentPBPinnedAt_eq_unpacked (A : RustAlloc) (g : ChunkedHeaderSentPBGhost)
    (a : BitVec 64) (m : V1State.Chunked.HeaderSent) :
    chunkedHeaderSentPBPinnedAt A g a m = chunkedHeaderSentUnpacked A g a m := by
  unfold chunkedHeaderSentPBPinnedAt chunkedHeaderSentUnpacked
  rw [optEkSentPBPinnedAt_eq A g.uc a,
    optPolynomialEncoderPBPinnedAt_eq A g.sendingEk (a + 80#64),
    optPolynomialDecoderPBPinnedAt_eq A g.receivingCt1 (a + 136#64)]
  ac_rfl

theorem chunkedHeaderSentUnpacked_bounds {A : RustAlloc} {g : ChunkedHeaderSentPBGhost}
    {a : BitVec 64} {m : V1State.Chunked.HeaderSent} {R : SepProp} {mem : Memory}
    (hm : mem ⊨ chunkedHeaderSentUnpacked A g a m ∗ R) :
    ((optEkSentCap g.uc m.uc + 1#64 == 0#64) = !m.uc.isSome ∧
     (optEkSentCap g.uc m.uc + 1#64 != 0#64) = m.uc.isSome) ∧
    ((optPolyEncCap g.sendingEk m.sendingEk + 1#64 == 0#64) = !m.sendingEk.isSome ∧
     (optPolyEncCap g.sendingEk m.sendingEk + 1#64 != 0#64) = m.sendingEk.isSome) ∧
    ((optPolyDecCap g.receivingCt1 m.receivingCt1 + 1#64 == 0#64) = !m.receivingCt1.isSome ∧
     (optPolyDecCap g.receivingCt1 m.receivingCt1 + 1#64 != 0#64) = m.receivingCt1.isSome) := by
  unfold chunkedHeaderSentUnpacked at hm
  have h1 : mem ⊨ optEkSentRest A g.uc a m.uc ∗
      ((a ↦₆₄ optEkSentCap g.uc m.uc) ∗
       ((a + 80#64) ↦₆₄ optPolyEncCap g.sendingEk m.sendingEk) ∗
       optPolyEncRest A g.sendingEk (a + 80#64) m.sendingEk ∗
       ((a + 136#64) ↦₆₄ optPolyDecCap g.receivingCt1 m.receivingCt1) ∗
       optPolyDecRest A g.receivingCt1 (a + 136#64) m.receivingCt1 ∗ R) := by
    convert hm using 1; ac_rfl
  have h2 : mem ⊨ optPolyEncRest A g.sendingEk (a + 80#64) m.sendingEk ∗
      ((a ↦₆₄ optEkSentCap g.uc m.uc) ∗ optEkSentRest A g.uc a m.uc ∗
       ((a + 80#64) ↦₆₄ optPolyEncCap g.sendingEk m.sendingEk) ∗
       ((a + 136#64) ↦₆₄ optPolyDecCap g.receivingCt1 m.receivingCt1) ∗
       optPolyDecRest A g.receivingCt1 (a + 136#64) m.receivingCt1 ∗ R) := by
    convert hm using 1; ac_rfl
  have h3 : mem ⊨ optPolyDecRest A g.receivingCt1 (a + 136#64) m.receivingCt1 ∗
      ((a ↦₆₄ optEkSentCap g.uc m.uc) ∗ optEkSentRest A g.uc a m.uc ∗
       ((a + 80#64) ↦₆₄ optPolyEncCap g.sendingEk m.sendingEk) ∗
       optPolyEncRest A g.sendingEk (a + 80#64) m.sendingEk ∗
       ((a + 136#64) ↦₆₄ optPolyDecCap g.receivingCt1 m.receivingCt1) ∗ R) := by
    convert hm using 1; ac_rfl
  exact ⟨optEkSentRest_cap_bounds h1, optPolyEncRest_cap_bounds h2, optPolyDecRest_cap_bounds h3⟩

/-- Join point at `+0x0b0` (`176`) of `HeaderSent::encoded_len`: steps field 3 (`receiving_ct1`)
    and epilogue through `RET` at `+0x0f0` (`240`). -/
theorem step_headerSent_f3_ret (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedHeaderSentEntryP2 prog entry)
    (hbl3 : CallPinnedEncLenAtF Φ prog entry 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (g : ChunkedHeaderSentPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.HeaderSent)
    (hdec_beq : (optPolyDecCap g.receivingCt1 m.receivingCt1 + 1#64 == 0#64) = !m.receivingCt1.isSome)
    (hdec_bne : (optPolyDecCap g.receivingCt1 m.receivingCt1 + 1#64 != 0#64) = m.receivingCt1.isSome)
    (hfit : chunkedHeaderSentPBEncodedLen m < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = a)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64
      (optEkSentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingEk))
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedHeaderSentUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (chunkedHeaderSentPBEncodedLen m) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  headerSent_fetches_range hfn 176 264
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  cases hrec : m.receivingCt1 with
  | none =>
    simp only [hrec, Option.isSome_none, Bool.not_false] at hdec_beq hdec_bne
    have htot_eq : optEkSentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingEk =
        chunkedHeaderSentPBEncodedLen m := by
      unfold chunkedHeaderSentPBEncodedLen
      simp only [hrec, optPolynomialDecoderPBFieldEncodedLen, Nat.add_zero]
    unfold chunkedHeaderSentUnpacked
    apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPpF.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)
  | some dec =>
    simp only [hrec, Option.isSome_some, Bool.not_true] at hdec_beq hdec_bne
    have hdec_fit : polynomialDecoderPBEncodedLen dec < 2 ^ 64 := by
      unfold chunkedHeaderSentPBEncodedLen at hfit
      simp only [hrec, optPolynomialDecoderPBFieldEncodedLen] at hfit
      omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
      clear *- halign; bv_bits
    unfold chunkedHeaderSentUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 192#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    have hP_bl : ((((a ↦₆₄ optEkSentCap g.uc m.uc) ∗ optEkSentRest A g.uc a m.uc ∗
        ((a + 80#64) ↦₆₄ optPolyEncCap g.sendingEk m.sendingEk) ∗
        optPolyEncRest A g.sendingEk (a + 80#64) m.sendingEk ∗
        ((a + 136#64) ↦₆₄ optPolyDecCap g.receivingCt1 m.receivingCt1) ∗
        optPolyDecRest A g.receivingCt1 (a + 136#64) m.receivingCt1) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) =
      ((polynomialDecoderPBPinnedAt A g.receivingCt1 (a + 136#64) dec ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((a ↦₆₄ optEkSentCap g.uc m.uc) ∗ optEkSentRest A g.uc a m.uc ∗
          ((a + 80#64) ↦₆₄ optPolyEncCap g.sendingEk m.sendingEk) ∗
          optPolyEncRest A g.sendingEk (a + 80#64) m.sendingEk ∗
          ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)) := by
      have hopt := optPolynomialDecoderPBPinnedAt_eq A g.receivingCt1 (a + 136#64) (some dec)
      simp only [optPolynomialDecoderPBPinnedAt] at hopt
      rw [hrec, hopt]
      ac_rfl
    apply SepWPpF.congr_pre hP_bl
    refine hbl3 (s0.readReg64 .lr) g.receivingCt1 (a + 136#64) (sp - 32#64) dec _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align
      (by simp_all) hdec_fit ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2 hfp2
    apply SepWPpF.congr_pre hP_bl.symm
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2⟩
    have hf3_eq := bv_optMsgField_some (inner := polynomialDecoderPBEncodedLen dec)
      (tot := optPolynomialDecoderPBFieldEncodedLen (some dec)) rfl
    have htot_fit : optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 := by
      unfold chunkedHeaderSentPBEncodedLen at hfit
      simp only [hrec] at hfit; omega
    have hvlen_lt : varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) <
        optPolynomialDecoderPBFieldEncodedLen (some dec) := by
      simp only [optPolynomialDecoderPBFieldEncodedLen]; omega
    have ⟨hule_f3, hule_f3_rev, hult_f3, hsub_f3, hbeq_f3⟩ :=
      cmp_ls_false_of_lt hvlen_lt htot_fit
    have ⟨hadd_tot, hult_tot, hule_tot, _, _⟩ :=
      adds_no_overflow_of_eq
        (a := optPolynomialDecoderPBFieldEncodedLen (some dec))
        (b := optEkSentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingEk)
        (c := chunkedHeaderSentPBEncodedLen m)
        (by unfold chunkedHeaderSentPBEncodedLen; simp only [hrec])
        hfit
    apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPpF.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)

/-- Join point at `+0x05c` (`92`) of `HeaderSent::encoded_len` when `m.sendingEk = some enc`:
    steps field 2 (`sending_ek`) to `+0x0b0` (`176`). -/
theorem step_headerSent_f2_some (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedHeaderSentEntryP2 prog entry)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (g : ChunkedHeaderSentPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.HeaderSent)
    (enc : PolynomialEncoder) (henc : m.sendingEk = some enc)
    (hfit : chunkedHeaderSentPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 92#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a + 80#64)
    (hx19 : s.readReg64 .x19 = a)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (optEkSentPBFieldEncodedLen m.uc))
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedHeaderSentUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = entry + 176#64 →
      sf.status = .Running →
      sf.sp = sp - 32#64 →
      sf.trace = s.trace →
      sf.readReg64 .x19 = a →
      sf.readReg64 .x20 = BitVec.ofNat 64
        (optEkSentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingEk) →
      (sf.readReg64 .x21 = s0.readReg64 .x21 ∧ sf.readReg64 .x22 = s0.readReg64 .x22 ∧
       sf.readReg64 .x23 = s0.readReg64 .x23 ∧ sf.readReg64 .x24 = s0.readReg64 .x24 ∧
       sf.readReg64 .x25 = s0.readReg64 .x25 ∧ sf.readReg64 .x26 = s0.readReg64 .x26 ∧
       sf.readReg64 .x27 = s0.readReg64 .x27 ∧ sf.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) →
      SepWPpF Φ prog ret sf P Q Qp) :
    SepWPpF Φ prog ret s P Q Qp := by
  headerSent_fetches_range hfn 96 144
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have henc_fit : polynomialEncoderPBEncodedLen enc < 2 ^ 64 := by
    unfold chunkedHeaderSentPBEncodedLen at hfit
    simp only [henc, optPolynomialEncoderPBFieldEncodedLen] at hfit
    omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have hP_bl : ((chunkedHeaderSentUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) =
    ((polynomialEncoderPBPinnedAt A g.sendingEk (a + 80#64) enc ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      (((a ↦₆₄ optEkSentCap g.uc m.uc) ∗ optEkSentRest A g.uc a m.uc ∗
        ((a + 136#64) ↦₆₄ optPolyDecCap g.receivingCt1 m.receivingCt1) ∗
        optPolyDecRest A g.receivingCt1 (a + 136#64) m.receivingCt1 ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)) := by
    unfold chunkedHeaderSentUnpacked
    have hopt := optPolynomialEncoderPBPinnedAt_eq A g.sendingEk (a + 80#64) (some enc)
    simp only [optPolynomialEncoderPBPinnedAt] at hopt
    rw [henc, hopt]
    ac_rfl
  apply SepWPpF.congr_pre hP_bl
  refine hbl2 ret g.sendingEk (a + 80#64) (sp - 32#64) enc s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 henc_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  have hf2_eq := bv_optMsgField_some (inner := polynomialEncoderPBEncodedLen enc)
    (tot := optPolynomialEncoderPBFieldEncodedLen (some enc)) rfl
  have htot_fit : optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 := by
    unfold chunkedHeaderSentPBEncodedLen at hfit
    simp only [henc] at hfit; omega
  have hvlen_lt : varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) <
      optPolynomialEncoderPBFieldEncodedLen (some enc) := by
    simp only [optPolynomialEncoderPBFieldEncodedLen]; omega
  have ⟨hule_f2, hule_f2_rev, hult_f2, hsub_f2, hbeq_f2⟩ :=
    cmp_ls_false_of_lt hvlen_lt htot_fit
  have h12_fit : optEkSentPBFieldEncodedLen m.uc +
      optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 := by
    unfold chunkedHeaderSentPBEncodedLen at hfit; simp only [henc] at hfit; omega
  have ⟨hadd_12, hult_12, hule_12, _, _⟩ :=
    adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen (some enc))
      (b := optEkSentPBFieldEncodedLen m.uc)
      (c := optEkSentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen (some enc))
      (by omega)
      h12_fit
  unfold chunkedHeaderSentUnpacked
  apply SepWPpF.of_sepWP (mid := entry + 176#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1])
    (by simp [arm64_norm, htr1]) (by simp [arm64_norm, h19_1, hx19])
    (by simp [arm64_norm, henc, hadd_12, hf2_eq, h20_1, hx20, hx0_1])
    ⟨by simp [arm64_norm, h21_1, h21], by simp [arm64_norm, h22_1, h22],
     by simp [arm64_norm, h23_1, h23], by simp [arm64_norm, h24_1, h24],
     by simp [arm64_norm, h25_1, h25], by simp [arm64_norm, h26_1, h26],
     by simp [arm64_norm, h27_1, h27], by simp [arm64_norm, h28_1, h28]⟩

/-- Prologue + `m.uc` discriminant check (`+0x000..+0x01c`, `0..28` bytes):
    saves `fp, lr, x20, x19`, sets `x19 := a`, and branches to `entry + 28#64` (`+0x01c`)
    if `m.uc.isSome` or `entry + 148#64` (`+0x094`) if `m.uc = none`. -/
theorem step_headerSent_prologue (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedHeaderSentEntryP2 prog entry)
    (g : ChunkedHeaderSentPBGhost) (a sp v32 v24 v16 v8 : BitVec 64) (m : V1State.Chunked.HeaderSent)
    (huc_beq : (optEkSentCap g.uc m.uc + 1#64 == 0#64) = !m.uc.isSome)
    (huc_bne : (optEkSentCap g.uc m.uc + 1#64 != 0#64) = m.uc.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (chunkedHeaderSentUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.uc.isSome then entry + 28#64 else entry + 148#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s.trace →
      sm.readReg64 .x19 = a →
      (sm.readReg64 .x21 = s.readReg64 .x21 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
       sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
       sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
       sm.readReg64 .x27 = s.readReg64 .x27 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧ calleeSavedVRegs sm = calleeSavedVRegs s) →
      SepWPpF Φ prog ret sm
        ((chunkedHeaderSentUnpacked A g a m ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19) ∗
          stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) Q Qp) :
    SepWPpF Φ prog ret s P Q Qp := by
  headerSent_fetches_range hfn 0 28
  subst hP
  cases huc : m.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at huc_beq huc_bne
    unfold chunkedHeaderSentUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 148#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, huc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm]) (by simp [arm64_norm, hx0])
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at huc_beq huc_bne
    unfold chunkedHeaderSentUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 28#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, huc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm]) (by simp [arm64_norm, hx0])
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩

/-- When `m.uc = none`, steps from `entry + 148#64` (`+0x094`) to `entry + 92#64` (`+0x05c`)
    or `entry + 176#64` (`+0x0b0`). -/
theorem step_headerSent_f1_none (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedHeaderSentEntryP2 prog entry)
    (g : ChunkedHeaderSentPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.HeaderSent)
    (huc : m.uc = none)
    (henc_beq : (optPolyEncCap g.sendingEk m.sendingEk + 1#64 == 0#64) = !m.sendingEk.isSome)
    (henc_bne : (optPolyEncCap g.sendingEk m.sendingEk + 1#64 != 0#64) = m.sendingEk.isSome)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 148#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = a)
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedHeaderSentUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingEk.isSome then entry + 92#64 else entry + 176#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s0.trace →
      (m.sendingEk.isSome = true → sm.readReg64 .x0 = a + 80#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optEkSentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s0.readReg64 .x21 ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧
       sm.readReg64 .x23 = s0.readReg64 .x23 ∧ sm.readReg64 .x24 = s0.readReg64 .x24 ∧
       sm.readReg64 .x25 = s0.readReg64 .x25 ∧ sm.readReg64 .x26 = s0.readReg64 .x26 ∧
       sm.readReg64 .x27 = s0.readReg64 .x27 ∧ sm.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) →
      SepWPpF Φ prog ret sm P Q Qp) :
    SepWPpF Φ prog ret s P Q Qp := by
  headerSent_fetches_range hfn 148 176
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  cases henc : m.sendingEk with
  | none =>
    simp only [henc, Option.isSome_none, Bool.not_false] at henc_beq henc_bne
    unfold chunkedHeaderSentUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 176#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm, htr])
      (by intro h; simp [henc] at h) (by simp [arm64_norm, hx19])
      (by simp [arm64_norm, huc, optEkSentPBFieldEncodedLen])
      ⟨by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24],
       by simp [arm64_norm, h25], by simp [arm64_norm, h26],
       by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
  | some enc =>
    simp only [henc, Option.isSome_some, Bool.not_true] at henc_beq henc_bne
    unfold chunkedHeaderSentUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 92#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm, htr])
      (by intro _; simp [arm64_norm, hx19]) (by simp [arm64_norm, hx19])
      (by simp [arm64_norm, huc, optEkSentPBFieldEncodedLen])
      ⟨by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24],
       by simp [arm64_norm, h25], by simp [arm64_norm, h26],
       by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩

theorem step_headerSent_f1_some_post (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedHeaderSentEntryP2 prog entry)
    (g : ChunkedHeaderSentPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.HeaderSent)
    (u : V1State.Unchunked.EkSent) (huc : m.uc = some u)
    (henc_beq : (optPolyEncCap g.sendingEk m.sendingEk + 1#64 == 0#64) = !m.sendingEk.isSome)
    (henc_bne : (optPolyEncCap g.sendingEk m.sendingEk + 1#64 != 0#64) = m.sendingEk.isSome)
    (hfit : chunkedHeaderSentPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s0 s2 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc2 : s2.pc = entry + 36#64) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = sp - 32#64) (htr2 : s2.trace = s0.trace)
    (hx0_2 : s2.readReg64 .x0 = BitVec.ofNat 64 (ekSentPBEncodedLen u))
    (h19_2 : s2.readReg64 .x19 = a)
    (hcs2 : s2.readReg64 .x21 = s0.readReg64 .x21 ∧ s2.readReg64 .x22 = s0.readReg64 .x22 ∧
            s2.readReg64 .x23 = s0.readReg64 .x23 ∧ s2.readReg64 .x24 = s0.readReg64 .x24 ∧
            s2.readReg64 .x25 = s0.readReg64 .x25 ∧ s2.readReg64 .x26 = s0.readReg64 .x26 ∧
            s2.readReg64 .x27 = s0.readReg64 .x27 ∧ s2.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hP : P = (chunkedHeaderSentUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingEk.isSome then entry + 92#64 else entry + 176#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s0.trace →
      (m.sendingEk.isSome = true → sm.readReg64 .x0 = a + 80#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optEkSentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s0.readReg64 .x21 ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧
       sm.readReg64 .x23 = s0.readReg64 .x23 ∧ sm.readReg64 .x24 = s0.readReg64 .x24 ∧
       sm.readReg64 .x25 = s0.readReg64 .x25 ∧ sm.readReg64 .x26 = s0.readReg64 .x26 ∧
       sm.readReg64 .x27 = s0.readReg64 .x27 ∧ sm.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) →
      SepWPpF Φ prog ret sm P Q Qp) :
    SepWPpF Φ prog ret s2 P Q Qp := by
  headerSent_fetches_range hfn 36 92
  headerSent_fetches_range hfn 168 176
  rcases hcs2 with ⟨h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2⟩
  subst hP
  have hf1_eq := bv_optMsgField_some (inner := ekSentPBEncodedLen u)
    (tot := optEkSentPBFieldEncodedLen (some u)) rfl
  have htot_fit : optEkSentPBFieldEncodedLen (some u) < 2 ^ 64 := by
    unfold chunkedHeaderSentPBEncodedLen at hfit
    simp only [huc] at hfit; omega
  have hvlen_lt : varintLen (BitVec.ofNat 64 (ekSentPBEncodedLen u)) <
      optEkSentPBFieldEncodedLen (some u) := by
    simp only [optEkSentPBFieldEncodedLen]; omega
  have ⟨hule_f1, hule_f1_rev, hult_f1, hsub_f1, hbeq_f1⟩ :=
    cmp_ls_false_of_lt hvlen_lt htot_fit
  cases henc : m.sendingEk with
  | none =>
    simp only [henc, Option.isSome_none, Bool.not_false] at henc_beq henc_bne
    unfold chunkedHeaderSentUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 176#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun2])
      (by simp [arm64_norm, hsp2]) (by simp [arm64_norm, htr2])
      (by intro h; simp [henc] at h) (by simp [arm64_norm, h19_2])
      (by simp [arm64_norm, huc, hf1_eq, hx0_2])
      ⟨by simp [arm64_norm, h21_2], by simp [arm64_norm, h22_2],
       by simp [arm64_norm, h23_2], by simp [arm64_norm, h24_2],
       by simp [arm64_norm, h25_2], by simp [arm64_norm, h26_2],
       by simp [arm64_norm, h27_2], by simp [arm64_norm, h28_2]⟩
  | some enc =>
    simp only [henc, Option.isSome_some, Bool.not_true] at henc_beq henc_bne
    unfold chunkedHeaderSentUnpacked
    apply SepWPpF.of_sepWP (mid := entry + 92#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun2])
      (by simp [arm64_norm, hsp2]) (by simp [arm64_norm, htr2])
      (by intro _; simp [arm64_norm, h19_2]) (by simp [arm64_norm, h19_2])
      (by simp [arm64_norm, huc, hf1_eq, hx0_2])
      ⟨by simp [arm64_norm, h21_2], by simp [arm64_norm, h22_2],
       by simp [arm64_norm, h23_2], by simp [arm64_norm, h24_2],
       by simp [arm64_norm, h25_2], by simp [arm64_norm, h26_2],
       by simp [arm64_norm, h27_2], by simp [arm64_norm, h28_2]⟩

theorem step_headerSent_f1_some (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedHeaderSentEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF Φ prog entry 32
      (ekSentPBPinnedAt A) ekSentPBEncodedLen polyEncodedLenStack)
    (g : ChunkedHeaderSentPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.HeaderSent)
    (u : V1State.Unchunked.EkSent) (huc : m.uc = some u)
    (henc_beq : (optPolyEncCap g.sendingEk m.sendingEk + 1#64 == 0#64) = !m.sendingEk.isSome)
    (henc_bne : (optPolyEncCap g.sendingEk m.sendingEk + 1#64 != 0#64) = m.sendingEk.isSome)
    (hfit : chunkedHeaderSentPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 28#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64) (htr : s.trace = s0.trace)
    (halign : sp &&& 15#64 = 0#64) (hx19 : s.readReg64 .x19 = a)
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedHeaderSentUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingEk.isSome then entry + 92#64 else entry + 176#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s0.trace →
      (m.sendingEk.isSome = true → sm.readReg64 .x0 = a + 80#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optEkSentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s0.readReg64 .x21 ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧
       sm.readReg64 .x23 = s0.readReg64 .x23 ∧ sm.readReg64 .x24 = s0.readReg64 .x24 ∧
       sm.readReg64 .x25 = s0.readReg64 .x25 ∧ sm.readReg64 .x26 = s0.readReg64 .x26 ∧
       sm.readReg64 .x27 = s0.readReg64 .x27 ∧ sm.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) →
      SepWPpF Φ prog ret sm P Q Qp) :
    SepWPpF Φ prog ret s P Q Qp := by
  headerSent_fetches_range hfn 28 32
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hu_fit : ekSentPBEncodedLen u < 2 ^ 64 := by
    unfold chunkedHeaderSentPBEncodedLen at hfit
    simp only [huc, optEkSentPBFieldEncodedLen] at hfit
    omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have hP_bl : ((chunkedHeaderSentUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) =
    ((ekSentPBPinnedAt A g.uc a u ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      ((((a + 80#64) ↦₆₄ optPolyEncCap g.sendingEk m.sendingEk) ∗
        optPolyEncRest A g.sendingEk (a + 80#64) m.sendingEk ∗
        ((a + 136#64) ↦₆₄ optPolyDecCap g.receivingCt1 m.receivingCt1) ∗
        optPolyDecRest A g.receivingCt1 (a + 136#64) m.receivingCt1 ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)) := by
    unfold chunkedHeaderSentUnpacked
    have hopt := optEkSentPBPinnedAt_eq A g.uc a (some u)
    simp only [optEkSentPBPinnedAt] at hopt
    rw [huc, hopt]
    ac_rfl
  apply SepWPpF.of_sepWP (mid := entry + 32#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPpF.congr_pre hP_bl
  refine hbl1 ret g.uc a (sp - 32#64) u _ _ Q Qp
    (by simp_all) (by simp_all) (by simp_all) hsp_sub_align
    (by simp_all) hu_fit ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2 hfp2
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2⟩
  exact step_headerSent_f1_some_post Φ prog A entry hfn g a sp m u huc
    henc_beq henc_bne hfit hpc2 hrun2 hsp2 (by simp_all) hx0_2 (by simp_all)
    ⟨by simp_all, by simp_all, by simp_all, by simp_all,
     by simp_all, by simp_all, by simp_all, by simp_all⟩ rfl hnext

theorem step_headerSent_f1 (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedHeaderSentEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF Φ prog entry 32
      (ekSentPBPinnedAt A) ekSentPBEncodedLen polyEncodedLenStack)
    (g : ChunkedHeaderSentPBGhost) (a sp v32 v24 v16 v8 : BitVec 64) (m : V1State.Chunked.HeaderSent)
    (huc_beq : (optEkSentCap g.uc m.uc + 1#64 == 0#64) = !m.uc.isSome)
    (huc_bne : (optEkSentCap g.uc m.uc + 1#64 != 0#64) = m.uc.isSome)
    (henc_beq : (optPolyEncCap g.sendingEk m.sendingEk + 1#64 == 0#64) = !m.sendingEk.isSome)
    (henc_bne : (optPolyEncCap g.sendingEk m.sendingEk + 1#64 != 0#64) = m.sendingEk.isSome)
    (hfit : chunkedHeaderSentPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (chunkedHeaderSentUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingEk.isSome then entry + 92#64 else entry + 176#64) →
      sm.status = .Running →
      sm.sp = sp - 32#64 →
      sm.trace = s.trace →
      (m.sendingEk.isSome = true → sm.readReg64 .x0 = a + 80#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optEkSentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s.readReg64 .x21 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
       sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
       sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
       sm.readReg64 .x27 = s.readReg64 .x27 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧ calleeSavedVRegs sm = calleeSavedVRegs s) →
      SepWPpF Φ prog ret sm
        ((chunkedHeaderSentUnpacked A g a m ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19) ∗
          stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) Q Qp) :
    SepWPpF Φ prog ret s P Q Qp := by
  refine step_headerSent_prologue Φ prog A entry hfn g a sp v32 v24 v16 v8 m
    huc_beq huc_bne hpc hrun hsp halign hx0 hP ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hcs1
  cases huc : m.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact step_headerSent_f1_none Φ prog A entry hfn g a sp m huc
      henc_beq henc_bne hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 rfl hnext
  | some u =>
    simp only [huc, Option.isSome_some, ↓reduceIte] at hpc1
    exact step_headerSent_f1_some Φ prog A entry hfn hbl1 g a sp m u huc
      henc_beq henc_bne hfit hpc1 hrun1 hsp1 htr1 halign hx19_1 hcs1 rfl hnext

theorem headerSent_entry_pinned_wp_p2 (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedHeaderSentEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF Φ prog entry 32
      (ekSentPBPinnedAt A) ekSentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAtF Φ prog entry 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl3 : CallPinnedEncLenAtF Φ prog entry 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack) :
    ∀ (x : PinnedEncLenGhost ChunkedHeaderSentPBGhost V1State.Chunked.HeaderSent)
      (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ (chunkedHeaderSentEncodedLenPinnedSpec A).pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPpF Φ prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (chunkedHeaderSentEncodedLenPinnedSpec A).post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (chunkedHeaderSentEncodedLenPinnedSpec A).onPanic x s0 sf ∗ R)) := by
  intro ⟨a, g, m⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [chunkedHeaderSentEncodedLenPinnedSpec, chunkedHeaderSentPBPinnedAt_eq_unpacked,
    stackAt_chunkedEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v32, v24, v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have ⟨⟨huc_beq, huc_bne⟩, ⟨henc_beq, henc_bne⟩, ⟨hdec_beq, hdec_bne⟩⟩ :=
    chunkedHeaderSentUnpacked_bounds hpre
  refine ⟨(chunkedHeaderSentUnpacked A g a m ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
      stackAt (s0.sp - 32#64) polyEncodedLenStack) ∗ R, emp,
      by rw [sepConj_emp]; convert hpre using 1; ac_rfl, ?_⟩
  refine step_headerSent_f1 (F := R) Φ prog A entry hfn hbl1 g a s0.sp v32 v24 v16 v8 m
    huc_beq huc_bne henc_beq henc_bne hfit hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases henc : m.sendingEk with
  | none =>
    simp only [henc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hx20_1' : s1.readReg64 .x20 = BitVec.ofNat 64
        (optEkSentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingEk) := by
      simp only [henc, optPolynomialEncoderPBFieldEncodedLen, Nat.add_zero, hx20_1]
    refine step_headerSent_f3_ret (F := R) Φ prog A entry hfn hbl3 g a s0.sp m
      hdec_beq hdec_bne hfit hpc1 hrun1 hsp1 halign hx19_1 hx20_1' hcs1 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f; rw [sepConj_emp] at hm_f
    simp only [chunkedHeaderSentEncodedLenPinnedSpec, chunkedHeaderSentPBPinnedAt_eq_unpacked,
      stackAt_chunkedEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x20, s0.readReg64 .x19,
      ⟨hx0_f, by rw [htrf, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  | some enc =>
    simp only [henc, Option.isSome_some, ↓reduceIte, forall_const] at hpc1 hx0_1
    refine step_headerSent_f2_some (F := R) Φ prog A entry hfn hbl2 g a s0.sp m enc henc hfit
      hpc1 hrun1 hsp1 halign hx0_1 hx19_1 hx20_1 hcs1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
    refine step_headerSent_f3_ret (F := R) Φ prog A entry hfn hbl3 g a s0.sp m
      hdec_beq hdec_bne hfit hpc2 hrun2 hsp2 halign hx19_2 hx20_2 hcs2 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f; rw [sepConj_emp] at hm_f
    simp only [chunkedHeaderSentEncodedLenPinnedSpec, chunkedHeaderSentPBPinnedAt_eq_unpacked,
      stackAt_chunkedEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x20, s0.readReg64 .x19,
      ⟨hx0_f, by rw [htrf, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

theorem headerSent_entry_pinned_ok_p2 (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedHeaderSentEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF (fun _ => True) prog entry 32
      (ekSentPBPinnedAt A) ekSentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAtF (fun _ => True) prog entry 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl3 : CallPinnedEncLenAtF (fun _ => True) prog entry 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack) :
    subroutine_ok prog entry (chunkedHeaderSentEncodedLenPinnedSpec A) :=
  subroutine_ok_of_sepWPpF_true (headerSent_entry_pinned_wp_p2 (fun _ => True) prog A entry hfn hbl1 hbl2 hbl3)

theorem headerSent_entry_pinned_lscl_ok [LibsignalPlacement] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsChunkedHeaderSentEntryP2 prog entry)
    (hbl1 : CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) prog entry 32
      (ekSentPBPinnedAt A) ekSentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) prog entry 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl3 : CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) prog entry 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenPinnedSpec A)) :=
  subroutine_ok_of_sepWPpF_lscl (headerSent_entry_pinned_wp_p2 (LibsignalCodeLoaded lsmpl) prog A entry hfn hbl1 hbl2 hbl3)

theorem headerSent_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn : IsChunkedHeaderSentEntry b ext entry)
    (hbl1 : CallPinnedEncLenAt (tripleRatchetProgAtExt b ext) entry 32
      (ekSentPBPinnedAt A) ekSentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAt (tripleRatchetProgAtExt b ext) entry 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl3 : CallPinnedEncLenAt (tripleRatchetProgAtExt b ext) entry 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (chunkedHeaderSentEncodedLenPinnedSpec A) :=
  headerSent_entry_pinned_ok_p2 (tripleRatchetProgAtExt b ext) A entry (Or.inl ⟨b, ext, rfl, hfn⟩)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl1)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl2)
    (callPinnedEncLenAtF_true_of_callPinnedEncLenAt hbl3)

theorem chunkedHeaderSentEncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (chunkedHeaderSentEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (chunkedHeaderSentEncodedLenSpec A) := by
  apply subroutine_ok_outcome_intro
  intro ⟨a, m⟩ R s0 hpc hrun hpre hsp
  simp only [chunkedHeaderSentEncodedLenSpec, chunkedHeaderSentPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (subroutine_ok_apply_outcome hpinned ⟨a, g, m⟩ R hpc hrun hpre hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [chunkedHeaderSentEncodedLenSpec, chunkedHeaderSentPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem chunkedHeaderSentEncodedLen_lscl_ok_of_pinned {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (withLsCodeLoaded pl (chunkedHeaderSentEncodedLenPinnedSpec A))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (chunkedHeaderSentEncodedLenSpec A)) := by
  apply subroutine_ok_outcome_intro
  intro ⟨a, m⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  simp only [chunkedHeaderSentEncodedLenSpec, chunkedHeaderSentPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (subroutine_ok_apply_outcome hpinned ⟨a, g, m⟩ R hpc hrun hpre hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded] at hpost ⊢
    simp only [chunkedHeaderSentEncodedLenSpec, chunkedHeaderSentPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ## 2. Wired `[local#1]` and `[local#2]` Theorems for `Chunked.Ct1Sampled` and `Chunked.HeaderSent` -/

theorem chunkedCt1SampledEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal1PinnedOkExt b A ext := by
  refine ct1Sampled_entry_pinned_ok_ext b A ext _ (Or.inl rfl) ?_ ?_ ?_
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 32)
        libsignalSessionCode_fnOff_0x39974 (by decide) spqrChunkedCt1SampledBin_decode_0x39994)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x39974 libsignalSessionCode_fnOff_0x39a94)
      (ct1SentEncodedLen_local1_pinned_ok_ext b A ext)
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 92)
        libsignalSessionCode_fnOff_0x39974 (by decide) spqrChunkedCt1SampledBin_decode_0x399d0)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x39974 libsignalSessionCode_fnOff_0x38e70)
      (polynomialEncoderEncodedLen_local1_pinned_ok_ext b A ext)
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 192)
        libsignalSessionCode_fnOff_0x39974 (by decide) spqrChunkedCt1SampledBin_decode_0x39a34)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x39974 libsignalSessionCode_fnOff_0x39f7c)
      (polynomialDecoderEncodedLen_local1_pinned_ok_ext b A ext)

theorem chunkedCt1SampledEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal1OkExt b A ext :=
  chunkedCt1SampledEncodedLen_ok_of_pinned (chunkedCt1SampledEncodedLen_local1_pinned_ok_ext b A ext)
theorem chunkedCt1SampledEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal1PinnedOk b C A ctl abs :=
  chunkedCt1SampledEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem chunkedCt1SampledEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal1Ok b C A ctl abs :=
  chunkedCt1SampledEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)

theorem chunkedCt1SampledEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal2PinnedOkExt b A ext := by
  refine ct1Sampled_entry_pinned_ok_ext b A ext _ (Or.inr rfl) ?_ ?_ ?_
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 32)
        libsignalSessionCode_fnOff_0x63768 (by decide) spqrChunkedCt1SampledBin_decode_0x63788)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x63768 libsignalSessionCode_fnOff_0x63948)
      (ct1SentEncodedLen_local2_pinned_ok_ext b A ext)
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 92)
        libsignalSessionCode_fnOff_0x63768 (by decide) spqrChunkedCt1SampledBin_decode_0x637c4)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x63768 libsignalSessionCode_fnOff_0x615f4)
      (polynomialEncoderEncodedLen_local2_pinned_ok_ext b A ext)
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 192)
        libsignalSessionCode_fnOff_0x63768 (by decide) spqrChunkedCt1SampledBin_decode_0x63828)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x63768 libsignalSessionCode_fnOff_0x642fc)
      (polynomialDecoderEncodedLen_local2_pinned_ok_ext b A ext)

theorem chunkedCt1SampledEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal2OkExt b A ext :=
  chunkedCt1SampledEncodedLen_ok_of_pinned (chunkedCt1SampledEncodedLen_local2_pinned_ok_ext b A ext)
theorem chunkedCt1SampledEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal2PinnedOk b C A ctl abs :=
  chunkedCt1SampledEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem chunkedCt1SampledEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal2Ok b C A ctl abs :=
  chunkedCt1SampledEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)

theorem bl_reloc_target_eq (entry off tgt : BitVec 64) :
    entry + off + (tgt - entry - off) = tgt := by
  bv_kernel

theorem chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOkExt A ext := by
  refine ct1Sampled_entry_pinned_lscl_ok _ A _
    (Or.inr ⟨inferInstance, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩) ?_ ?_ ?_
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_179_rebase_fetch_0x20 _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (ct1SentEncodedLen_local1_pinned_placed_ok_ext A ext)
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_179_rebase_fetch_0x5c _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A ext)
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_179_rebase_fetch_0xc0 _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem chunkedCt1SampledEncodedLen_local1_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal1PlacedOkExt A ext :=
  chunkedCt1SampledEncodedLen_lscl_ok_of_pinned (chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_ext A ext)
theorem chunkedCt1SampledEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem chunkedCt1SampledEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal1PlacedOk C A ctl abs :=
  chunkedCt1SampledEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOkExt A ext := by
  refine ct1Sampled_entry_pinned_lscl_ok _ A _
    (Or.inr ⟨inferInstance, Rust.withPanics ext, Or.inr ⟨rfl, rfl⟩⟩) ?_ ?_ ?_
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_407_rebase_fetch_0x20 _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (ct1SentEncodedLen_local2_pinned_placed_ok_ext A ext)
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_407_rebase_fetch_0x5c _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A ext)
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_407_rebase_fetch_0xc0 _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem chunkedCt1SampledEncodedLen_local2_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal2PlacedOkExt A ext :=
  chunkedCt1SampledEncodedLen_lscl_ok_of_pinned (chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext A ext)
theorem chunkedCt1SampledEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem chunkedCt1SampledEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedCt1SampledEncodedLenLocal2PlacedOk C A ctl abs :=
  chunkedCt1SampledEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def ChunkedHeaderSentEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chunkedHeaderSentEncodedLenLocal1Name) (chunkedHeaderSentEncodedLenPinnedSpec A)
def ChunkedHeaderSentEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chunkedHeaderSentEncodedLenLocal1Name) (chunkedHeaderSentEncodedLenSpec A)
def ChunkedHeaderSentEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chunkedHeaderSentEncodedLenLocal1Name) (chunkedHeaderSentEncodedLenPinnedSpec A)
def ChunkedHeaderSentEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chunkedHeaderSentEncodedLenLocal1Name) (chunkedHeaderSentEncodedLenSpec A)
def ChunkedHeaderSentEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chunkedHeaderSentEncodedLenLocal2Name) (chunkedHeaderSentEncodedLenPinnedSpec A)
def ChunkedHeaderSentEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chunkedHeaderSentEncodedLenLocal2Name) (chunkedHeaderSentEncodedLenSpec A)
def ChunkedHeaderSentEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chunkedHeaderSentEncodedLenLocal2Name) (chunkedHeaderSentEncodedLenPinnedSpec A)
def ChunkedHeaderSentEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chunkedHeaderSentEncodedLenLocal2Name) (chunkedHeaderSentEncodedLenSpec A)

def ChunkedHeaderSentEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_188).rebase (blkPl_188).base (Rust.withPanics ext)) (blkPl_188).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenPinnedSpec A))
def ChunkedHeaderSentEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_188).rebase (blkPl_188).base (Rust.withPanics ext)) (blkPl_188).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenSpec A))
def ChunkedHeaderSentEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedHeaderSentEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)
def ChunkedHeaderSentEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedHeaderSentEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)
def ChunkedHeaderSentEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_414).rebase (blkPl_414).base (Rust.withPanics ext)) (blkPl_414).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenPinnedSpec A))
def ChunkedHeaderSentEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_414).rebase (blkPl_414).base (Rust.withPanics ext)) (blkPl_414).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenSpec A))
def ChunkedHeaderSentEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedHeaderSentEncodedLenLocal2PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)
def ChunkedHeaderSentEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedHeaderSentEncodedLenLocal2PlacedOkExt A (tripleRatchetExterns C ctl abs)

theorem chunkedHeaderSentEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal1PinnedOkExt b A ext := by
  refine headerSent_entry_pinned_ok_ext b A ext _ (Or.inl rfl) ?_ ?_ ?_
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 32)
        libsignalSessionCode_fnOff_0x3a0ac (by decide) spqrChunkedHeaderSentBin_decode_0x3a0cc)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x3a0ac libsignalSessionCode_fnOff_0x3a1cc)
      (ekSentEncodedLen_local1_pinned_ok_ext b A ext)
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 92)
        libsignalSessionCode_fnOff_0x3a0ac (by decide) spqrChunkedHeaderSentBin_decode_0x3a108)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x3a0ac libsignalSessionCode_fnOff_0x38e70)
      (polynomialEncoderEncodedLen_local1_pinned_ok_ext b A ext)
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 192)
        libsignalSessionCode_fnOff_0x3a0ac (by decide) spqrChunkedHeaderSentBin_decode_0x3a16c)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x3a0ac libsignalSessionCode_fnOff_0x39f7c)
      (polynomialDecoderEncodedLen_local1_pinned_ok_ext b A ext)

theorem chunkedHeaderSentEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal1OkExt b A ext :=
  chunkedHeaderSentEncodedLen_ok_of_pinned (chunkedHeaderSentEncodedLen_local1_pinned_ok_ext b A ext)
theorem chunkedHeaderSentEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal1PinnedOk b C A ctl abs :=
  chunkedHeaderSentEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem chunkedHeaderSentEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal1Ok b C A ctl abs :=
  chunkedHeaderSentEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)

theorem chunkedHeaderSentEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal2PinnedOkExt b A ext := by
  refine headerSent_entry_pinned_ok_ext b A ext _ (Or.inr rfl) ?_ ?_ ?_
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 32)
        libsignalSessionCode_fnOff_0x64b78 (by decide) spqrChunkedHeaderSentBin_decode_0x64b98)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x64b78 libsignalSessionCode_fnOff_0x64d94)
      (ekSentEncodedLen_local2_pinned_ok_ext b A ext)
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 92)
        libsignalSessionCode_fnOff_0x64b78 (by decide) spqrChunkedHeaderSentBin_decode_0x64bd4)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x64b78 libsignalSessionCode_fnOff_0x615f4)
      (polynomialEncoderEncodedLen_local2_pinned_ok_ext b A ext)
  · exact callPinnedEncLenAt_of_bl (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 192)
        libsignalSessionCode_fnOff_0x64b78 (by decide) spqrChunkedHeaderSentBin_decode_0x64c38)
      (fnAddr_bl_target libsignalSessionCode_fnOff_0x64b78 libsignalSessionCode_fnOff_0x642fc)
      (polynomialDecoderEncodedLen_local2_pinned_ok_ext b A ext)

theorem chunkedHeaderSentEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal2OkExt b A ext :=
  chunkedHeaderSentEncodedLen_ok_of_pinned (chunkedHeaderSentEncodedLen_local2_pinned_ok_ext b A ext)
theorem chunkedHeaderSentEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal2PinnedOk b C A ctl abs :=
  chunkedHeaderSentEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem chunkedHeaderSentEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal2Ok b C A ctl abs :=
  chunkedHeaderSentEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)

theorem chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal1PinnedPlacedOkExt A ext := by
  refine headerSent_entry_pinned_lscl_ok _ A _
    (Or.inr ⟨inferInstance, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩) ?_ ?_ ?_
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_188_rebase_fetch_0x20 _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (ekSentEncodedLen_local1_pinned_placed_ok_ext A ext)
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_188_rebase_fetch_0x5c _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A ext)
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_188_rebase_fetch_0xc0 _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (polynomialDecoderEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem chunkedHeaderSentEncodedLen_local1_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal1PlacedOkExt A ext :=
  chunkedHeaderSentEncodedLen_lscl_ok_of_pinned (chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_ext A ext)
theorem chunkedHeaderSentEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem chunkedHeaderSentEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal1PlacedOk C A ctl abs :=
  chunkedHeaderSentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal2PinnedPlacedOkExt A ext := by
  refine headerSent_entry_pinned_lscl_ok _ A _
    (Or.inr ⟨inferInstance, Rust.withPanics ext, Or.inr ⟨rfl, rfl⟩⟩) ?_ ?_ ?_
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_414_rebase_fetch_0x20 _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (ekSentEncodedLen_local2_pinned_placed_ok_ext A ext)
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_414_rebase_fetch_0x5c _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A ext)
  · exact callPinnedEncLenAtF_of_bl_plain (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (blkPC_414_rebase_fetch_0xc0 _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm]) (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem chunkedHeaderSentEncodedLen_local2_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal2PlacedOkExt A ext :=
  chunkedHeaderSentEncodedLen_lscl_ok_of_pinned (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A ext)
theorem chunkedHeaderSentEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem chunkedHeaderSentEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : ChunkedHeaderSentEncodedLenLocal2PlacedOk C A ctl abs :=
  chunkedHeaderSentEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end CryptoVerification.SpqrV1.ProtoRepr

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeserBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSomeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Post-Loop Composition for `<SignalMessage>::try_from`

Defines output-indexed post-loop allocator event envelopes (`TryFromPostPreEnv`, `TryFromPostEnv`),
proves `FreeOnlyEvs` transport lemmas, and composes the relocatable `[LibsignalPlacement]`
budget-threaded post-loop theorem `tryFrom_post_wp_placed` on Block `85`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession
  (ProtoSignalMessage PublicKey SignalMessage SignalProtocolError)
open CryptoVerification (LibsignalPlacement LibsignalHooks)
open CryptoVerification.RustHeap (RustAlloc vecHeader)
open CryptoVerification.LibsignalProtoCodec (decode protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet
  (TryFromGhost blkPl_85 logOff decodeErrorAt boxU8Buf)
open CryptoVerification.LibsignalTripleRatchetRepr
  (signalMessageResultAt speWord noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (skipFieldStackX wireSignalMessageOf)
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWPp → WSepWPp
open CryptoVerification.LibsignalTripleRatchet.Wire
  (tryFromPlacedProg tryFromPlacedImg
   PostEpilogueStatePlaced LoopExitStatePlaced tryFromQp
   deallocSlot vecU8Buf optVecU8Buf optVecU8Buf_entails_deallocSlot optU32TagVal
   optBoxU8Pending deserializeResult33At
   pkBytesOf pkLayoutAt pkLayoutAt_eq_pointsToBytes exists_pkBytesOf sevenBytesHeadAt
   pointsTo32_pair_eq_pointsTo64 memRegion120_split16
   tryFrom_eq_of_gt9 msg_bounds_of_decode
   spUnused0 spUnused104 memRegion72_104_pack memRegion72_104_unpack
   memRegion104_0_pack memRegion104_0_unpack pcVal_if_eq_getD
   wireSignalMessageOf_rk_some_entails
   memRegion112_of_48_64 memRegion112_of_33_15_64 memRegion112_of_8_40_64
   memRegion104_0_pack64 zext32_zext64_8
   memRegion176_split_88_16_72 memRegion176_split_104_72
   memRegion352_of_104_72_112_64 memRegion352_of_88_16_72_112_64
   pure_true_emp entails_of_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
   fitsEvents_append)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (TripleRatchetHooksWPlaced DropDecodeErrorOkWPlaced DropSpeOkWPlaced
   IntoBoxedSliceOkPlaced TryCloneFromRefOkPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget
  (postNoPanicQp wpp_to_tryFromQp wpp_mono_post_noPanic wpp_frame_noPanic post_none_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeserBudget
  (post_rk_none_wp_placed post_deser_err_wp_placed post_deser_ok_head_wp_placed
   post_counter_none_wp_placed post_counter_some_head_wp_placed post_ct_none_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSomeBudget
  (post_rk_some_head_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget
  (IntoBoxedCapEnv IntoBoxedOptCapEnv PostCtBoxesEnv PostCtBoxesPost
   TryCloneBytesEnv PostClonePackEnv
   post_ct_some_boxes_wp_placed post_clone_and_pack_wp_placed)

/-! ## Post-loop allocator event envelopes and transport lemmas -/

/-- Capacity-bounded allocator event envelope of `<Vec<u8>>::into_boxed_slice`:
quantifies over all valid `Vec<u8>` capacities `bs.length ≤ cap.toNat < 2 ^ 63`. -/
def IntoBoxedBoundedEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ cap : BitVec 64, bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ IntoBoxedCapEnv cap bs evs

/-- Optional capacity-bounded allocator event envelope for `m'.addresses`. -/
def IntoBoxedOptBoundedEnv : Option (List (BitVec 8)) → List AllocEvent → Prop
  | none => (· = [])
  | some ad => IntoBoxedBoundedEnv ad

/-- Allocation-phase envelope on the `.ok msg` path of `<SignalMessage>::try_from` post-loop:
`into_boxed_slice` on `ciphertext`, optional `into_boxed_slice` on `addresses`, and
`try_clone_from_ref_in` on `serialized`. -/
def TryFromPostOkAllocEnv (bs ct : List (BitVec 8))
    (adOpt : Option (List (BitVec 8))) : List AllocEvent → Prop :=
  SeqEnv (IntoBoxedBoundedEnv ct) (SeqEnv (IntoBoxedOptBoundedEnv adOpt) (TryCloneBytesEnv bs))

/-- Output-indexed precondition budget envelope of `<SignalMessage>::try_from` post-loop:
empty (`evs = []`, requiring zero budget) on `.error _`, and `SeqEnv FreeOnlyEvs TryFromPostOkAllocEnv`
on `.ok msg`. -/
def TryFromPostOutPreEnv : Except SignalProtocolError SignalMessage → List AllocEvent → Prop
  | .error _ => (· = [])
  | .ok msg =>
    SeqEnv FreeOnlyEvs (TryFromPostOkAllocEnv msg.serialized msg.ciphertext msg.addresses)

/-- Output-indexed postcondition event envelope of `<SignalMessage>::try_from` post-loop:
`TryFromPostOutPreEnv out` followed by trailing `FreeOnlyEvs` cleanup deallocations. -/
def TryFromPostOutEnv (out : Except SignalProtocolError SignalMessage) :
    List AllocEvent → Prop :=
  SeqEnv (TryFromPostOutPreEnv out) FreeOnlyEvs

/-- Input-bytes precondition budget envelope of `tryFrom_post_wp_placed`. -/
def TryFromPostPreEnv (bs : List (BitVec 8)) : List AllocEvent → Prop :=
  TryFromPostOutPreEnv (SignalMessage.tryFrom protoSignalCodec bs)

/-- Input-bytes postcondition event envelope of `tryFrom_post_wp_placed`. -/
def TryFromPostEnv (bs : List (BitVec 8)) : List AllocEvent → Prop :=
  TryFromPostOutEnv (SignalMessage.tryFrom protoSignalCodec bs)

theorem tryFromPostOutEnv_of_error_freeOnly {e : SignalProtocolError} {evs : List AllocEvent}
    (hf : FreeOnlyEvs evs) : TryFromPostOutEnv (.error e) evs :=
  SeqEnv.append (evs₁ := []) (evs₂ := evs) rfl hf

private theorem tryFromPostOutEnv_of_eq_error {out : Except SignalProtocolError SignalMessage}
    {e : SignalProtocolError} {evs : List AllocEvent}
    (hout : out = .error e) (hf : FreeOnlyEvs evs) : TryFromPostOutEnv out evs :=
  hout ▸ tryFromPostOutEnv_of_error_freeOnly hf

theorem freeOnly_of_tryFromPostOutEnv_error {e : SignalProtocolError} {evs : List AllocEvent}
    (h : TryFromPostOutEnv (.error e) evs) : FreeOnlyEvs evs := by
  rcases h with rfl | ⟨a, b, rfl, rfl, hfb⟩
  · exact .nil
  · exact hfb

theorem fitsEnv_tryFromPostOutPre_step_freeOnly {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {out : Except SignalProtocolError SignalMessage} {evs₀ : List AllocEvent}
    (hf : FreeOnlyEvs evs₀) (h : FitsEnv M lim st (TryFromPostOutPreEnv out)) :
    FitsEnv M lim (M.stepEvents evs₀ st) (TryFromPostOutPreEnv out) := by
  cases out with
  | error e =>
    intro evs hevs
    subst hevs
    trivial
  | ok msg =>
    intro evs hevs
    have hcomb : TryFromPostOutPreEnv (.ok msg) (evs₀ ++ evs) := by
      rcases hevs with h1 | ⟨e1, e2, rfl, h1, h2⟩
      · exact Or.inl (hf.append h1)
      · rw [← List.append_assoc]
        exact SeqEnv.append (hf.append h1) h2
    exact ((fitsEvents_append M lim evs₀ evs st).mp (h _ hcomb)).2

theorem tryFromPostOutEnv_prepend_freeOnly {out : Except SignalProtocolError SignalMessage}
    {evs₀ evs₁ : List AllocEvent}
    (hf : FreeOnlyEvs evs₀) (h : TryFromPostOutEnv out evs₁) :
    TryFromPostOutEnv out (evs₀ ++ evs₁) := by
  cases out with
  | error e =>
    exact tryFromPostOutEnv_of_error_freeOnly (hf.append (freeOnly_of_tryFromPostOutEnv_error h))
  | ok msg =>
    rcases h with hpre | ⟨e1, e2, rfl, hpre, hf2⟩
    · refine Or.inl ?_
      rcases hpre with h1 | ⟨a, b, rfl, h1, h2⟩
      · exact Or.inl (hf.append h1)
      · rw [← List.append_assoc]
        exact SeqEnv.append (hf.append h1) h2
    · rw [← List.append_assoc]
      refine SeqEnv.append ?_ hf2
      rcases hpre with h1 | ⟨a, b, rfl, h1, h2⟩
      · exact Or.inl (hf.append h1)
      · rw [← List.append_assoc]
        exact SeqEnv.append (hf.append h1) h2

private theorem intoBoxedOptBounded_of_cap {adCap : BitVec 64}
    {adOpt : Option (List (BitVec 8))} {evs : List AllocEvent}
    (had_bnd : ∀ ad, adOpt = some ad → ad.length ≤ adCap.toNat ∧ adCap.toNat < 2 ^ 63)
    (h : IntoBoxedOptCapEnv adCap adOpt evs) :
    IntoBoxedOptBoundedEnv adOpt evs := by
  cases adOpt with
  | none => exact h
  | some ad =>
    have hb := had_bnd ad rfl
    exact ⟨adCap, hb.1, hb.2, h⟩

private theorem fitsEnv_postCtBoxes_of_ok {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {msg : SignalMessage} {ctCap adCap : BitVec 64}
    (hct_le : msg.ciphertext.length ≤ ctCap.toNat) (hct_lt : ctCap.toNat < 2 ^ 63)
    (had_bnd : ∀ ad, msg.addresses = some ad → ad.length ≤ adCap.toNat ∧ adCap.toNat < 2 ^ 63)
    (hFit : FitsEnv M lim st (TryFromPostOutPreEnv (.ok msg))) :
    FitsEnv M lim st (PostCtBoxesEnv ctCap adCap msg.ciphertext msg.addresses) := by
  refine hFit.mono fun evs hevs => ?_
  rcases hevs with hf | ⟨e0, e12, rfl, hf, h12⟩
  · exact Or.inl hf
  · refine SeqEnv.append hf ?_
    rcases h12 with h1 | ⟨e1, e2, rfl, h1, h2⟩
    · exact Or.inl ⟨ctCap, hct_le, hct_lt, h1⟩
    · exact SeqEnv.append ⟨ctCap, hct_le, hct_lt, h1⟩ (Or.inl (intoBoxedOptBounded_of_cap had_bnd h2))

private theorem fitsEnv_tryClone_of_postCtBoxes {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {msg : SignalMessage} {ctCap adCap : BitVec 64} {evs_box : List AllocEvent}
    (hct_le : msg.ciphertext.length ≤ ctCap.toNat) (hct_lt : ctCap.toNat < 2 ^ 63)
    (had_bnd : ∀ ad, msg.addresses = some ad → ad.length ≤ adCap.toNat ∧ adCap.toNat < 2 ^ 63)
    (hFit : FitsEnv M lim st (TryFromPostOutPreEnv (.ok msg)))
    (hbox : PostCtBoxesPost ctCap adCap msg.ciphertext msg.addresses evs_box) :
    FitsEnv M lim (M.stepEvents evs_box st) (TryCloneBytesEnv msg.serialized) := by
  rcases hbox with ⟨evs₀, evs₁, evs₂, rfl, hf₀, h1, h2⟩
  have hFit1 := hFit.seq_right hf₀
  have hFit2 := hFit1.seq_right ⟨ctCap, hct_le, hct_lt, h1⟩
  have hFit3 := hFit2.seq_right (intoBoxedOptBounded_of_cap had_bnd h2)
  simpa only [M.stepEvents_append] using hFit3

private theorem tryFromPostOutEnv_of_boxes_clone {msg : SignalMessage}
    {ctCap adCap : BitVec 64} {evs_box evs_cp : List AllocEvent}
    (hct_le : msg.ciphertext.length ≤ ctCap.toNat) (hct_lt : ctCap.toNat < 2 ^ 63)
    (had_bnd : ∀ ad, msg.addresses = some ad → ad.length ≤ adCap.toNat ∧ adCap.toNat < 2 ^ 63)
    (hbox : PostCtBoxesPost ctCap adCap msg.ciphertext msg.addresses evs_box)
    (hcp : PostClonePackEnv msg.serialized evs_cp) :
    TryFromPostOutEnv (.ok msg) (evs_box ++ evs_cp) := by
  rcases hbox with ⟨evs₀, evs₁, evs₂, rfl, hf₀, h1, h2⟩
  have h1' : IntoBoxedBoundedEnv msg.ciphertext evs₁ := ⟨ctCap, hct_le, hct_lt, h1⟩
  have h2' : IntoBoxedOptBoundedEnv msg.addresses evs₂ := intoBoxedOptBounded_of_cap had_bnd h2
  rcases hcp with hclone | ⟨ec, ef, rfl, hclone, hff⟩
  · refine Or.inl ?_
    have heq : evs₀ ++ evs₁ ++ evs₂ ++ evs_cp = evs₀ ++ (evs₁ ++ (evs₂ ++ evs_cp)) := by
      simp [List.append_assoc]
    rw [heq]
    exact SeqEnv.append hf₀ (SeqEnv.append h1' (SeqEnv.append h2' hclone))
  · have heq : evs₀ ++ evs₁ ++ evs₂ ++ (ec ++ ef) = (evs₀ ++ (evs₁ ++ (evs₂ ++ ec))) ++ ef := by
      simp [List.append_assoc]
    rw [heq]
    exact SeqEnv.append (SeqEnv.append hf₀ (SeqEnv.append h1' (SeqEnv.append h2' hclone))) hff

/-! ## Local separation-logic entailment helpers -/

private theorem wpp_bind_frame_gen {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P F : SepProp} {Q1 Q : State → SepProp → Prop}
    (h1 : WSepWPp prog mid s P Q1 (postNoPanicQp s0))
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q1 sm Pm →
      WSepWPp prog ret sm (Pm ∗ F) Q (postNoPanicQp s0)) :
    WSepWPp prog ret s (P ∗ F) Q (postNoPanicQp s0) := by
  refine WSepWPp.bind
    (wpp_frame_noPanic (Q := fun sm PmF => ∃ Pm, Q1 sm Pm ∧ PmF = Pm ∗ F) h1
      fun sm Pm hq => ⟨Pm, hq, rfl⟩) ?_
  intro sm PmF hpcm hrunm ⟨Pm, hq, hEq⟩
  rw [hEq]
  exact h2 sm Pm hpcm hrunm hq

private theorem memRegion120_split24 (x19 : BitVec 64) :
    memRegion x19 120 ⊢
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ ((x19 + 16#64) ↦₆₄ w2) ∗
        memRegion (x19 + 24#64) 96 := by
  have hs1 := memRegion_split x19 8 112 (by decide)
  have hs2 := memRegion_split (x19 + 8#64) 8 104 (by decide)
  have hs3 := memRegion_split (x19 + 16#64) 8 96 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2 hs3
  rw [hs1, hs2, hs3, memRegion_eight x19, memRegion_eight (x19 + 8#64), memRegion_eight (x19 + 16#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

private theorem vecU8Buf_cap_bounds (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => ?_
  rw [pure_true_emp ⟨h.1, h.2.1⟩, emp_sepConj, pure_true_emp h, emp_sepConj]
  exact Entails.refl _

private theorem optVecU8Buf_cap_bounds (A : RustAlloc) (cap ptr len : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optVecU8Buf A cap ptr len opt ⊢
      ⌜∀ bs, opt = some bs → bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗
        optVecU8Buf A cap ptr len opt := by
  cases opt with
  | none =>
    rw [pure_true_emp (fun _ h => nomatch h), emp_sepConj]
    exact Entails.refl _
  | some bs =>
    dsimp only [optVecU8Buf, vecU8Buf]
    refine Entails.pure_left fun hlen => Entails.pure_left fun hb => ?_
    have hall : ∀ bs', (some bs : Option (List (BitVec 8))) = some bs' →
        bs'.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 := by
      intro bs' heq; cases heq; exact ⟨hb.1, hb.2.1⟩
    rw [pure_true_emp hall, emp_sepConj, pure_true_emp hlen, emp_sepConj,
      pure_true_emp hb, emp_sepConj]
    exact Entails.refl _

/-! ## Relocatable `[LibsignalPlacement]` post-loop composition theorems (Block `85`) -/

theorem post_after_578_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 x21 rkCap rkPtr ctCap ctPtr ctLen pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64}
    {w136 w144 w152 w15 w23 : BitVec 64}
    {counter w52 pcTag pcVal w9 : BitVec 32} {w13 : BitVec 16}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    (bs rk : List (BitVec 8)) (m' : ProtoSignalMessage) (pk : PublicKey)
    {out : Except SignalProtocolError SignalMessage}
    (hgt9 : 9 < bs.length) (hlt : bs.length < 2 ^ 32)
    (hdec : decode ((bs.take (bs.length - 8)).drop 1) = some m')
    (hpk : pk.bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hout : out =
      match m'.ciphertext with
      | none => .error .invalidProtobufEncoding
      | some ciphertext =>
        .ok { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey := pk, counter,
              previousCounter := m'.previousCounter.getD 0#32, ciphertext,
              pqRatchet := m'.pqRatchet.getD [], addresses := m'.addresses,
              serialized := bs })
    (hFit : FitsEnv M lim st (TryFromPostOutPreEnv out))
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1400#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = addsPState64 ctCap 1#64)
    (hx8 : s.readReg64 .x8 = (m'.previousCounter.getD 0#32).zeroExtend 64)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs.length)
    (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = adCap)
    (hx23 : s.readReg64 .x23 = (bs.headD 0#8).zeroExtend 64)
    (hx24 : s.readReg64 .x24 = b7.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap)
    (hx26 : s.readReg64 .x26 = speWord 2)
    (hx27 : s.readReg64 .x27 = ctCap)
    (hx28 : s.readReg64 .x28 = ctPtr) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (spUnused0 sp' ∗
        ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 16#64) ↦₆₄ adLen) ∗
        ((sp' + 28#64) ↦₃₂ counter) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
        ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₃₂ pcTag) ∗
        ((sp' + 52#64) ↦₃₂ w52) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
        ((sp' + 64#64) ↦₆₄ w15) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        spUnused104 sp' ∗
        ((sp' + 104#64) ↦₆₄ w23) ∗ ((sp' + 112#64) ↦₈ b31) ∗
        ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
        vecHeader (sp' + 136#64) w136 w144 w152 ∗
        ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
        memRegion (sp' + 224#64) 64 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        optVecU8Buf A.repAlloc ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A.repAlloc pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A.repAlloc adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, TryFromPostOutEnv out evs ∧
          (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
            memRegion (sp' + 176#64) 112 ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            (x21 ↦ₛ bs) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  have h48_pair := (pointsTo32_pair_eq_pointsTo64 (sp' + 48#64) pcTag w52).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48_pair
  cases hct : m'.ciphertext with
  | none =>
    simp only [hct] at hout
    have hct_eq : optVecU8Buf A.repAlloc ctCap ctPtr ctLen none = ⌜ctCap = noneCap⌝ := rfl
    rw [hct_eq]
    refine WSepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono
                    (optVecU8Buf_entails_deallocSlot A.repAlloc pqCap pqPtr pqLen m'.pqRatchet)
                    (sepConj_mono
                      (optVecU8Buf_entails_deallocSlot A.repAlloc adCap adPtr adLen m'.addresses)
                      (sepConj_mono_left (memRegion120_split16 x19)))))))))))))))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine WSepWPp.exists_pre fun w1 => WSepWPp.exists_pre fun w0 =>
      WSepWPp.exists_pre fun adAct => WSepWPp.exists_pre fun pqAct => ?_
    set F_ct_none := spUnused0 sp' ∗
      ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 16#64) ↦₆₄ adLen) ∗
      ((sp' + 28#64) ↦₃₂ counter) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
      ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₆₄ (w52 ++ pcTag)) ∗
      ((sp' + 60#64) ↦₃₂ pcVal) ∗ ((sp' + 64#64) ↦₆₄ w15) ∗
      spUnused104 sp' ∗
      ((sp' + 104#64) ↦₆₄ w23) ∗ ((sp' + 112#64) ↦₈ b31) ∗
      ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
      vecHeader (sp' + 136#64) w136 w144 w152 ∗
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
      memRegion (sp' + 224#64) 64 ∗
      (x21 ↦ₛ bs)
    refine WSepWPp.mono_pre (P' := ⌜ctCap = noneCap⌝ ∗
        ((((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
          vecU8Buf A.repAlloc rkCap rkPtr rk ∗
          deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_ct_none))
      (by dsimp only [F_ct_none]; rw [h48_pair]; apply entails_of_eq; sep_ac_rfl) ?_
    refine WSepWPp.pure_pre fun hct_cap => ?_
    subst hct_cap
    refine wpp_frame_noPanic
      (post_ct_none_wp_placed hS st rk pqAct adAct hout hst hpc hrun hpstate hx19 hx26 hx25 hx22)
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ =>
        ⟨hstf, evs, tryFromPostOutEnv_of_eq_error hout hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_ct_none]
    have hpack0 := memRegion104_0_pack64 sp' (b8.zeroExtend 32) counter pcVal
      adLen ctLen pqLen (w52 ++ pcTag) w15 rkPtr rkCap adPtr pqPtr
    have hpack104 := memRegion72_104_pack sp' w23 w136 w144 w152 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
    have hpack176 := memRegion112_of_8_40_64 sp' (speWord 2)
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono hpack104 (sepConj_mono_left hpack176)))
    apply entails_of_eq; sep_ac_rfl
  | some ct =>
    simp only [hct] at hout
    have hbnd := msg_bounds_of_decode hgt9 hlt hdec hct
    have hct_eq : optVecU8Buf A.repAlloc ctCap ctPtr ctLen (some ct) =
        ⌜ctLen = BitVec.ofNat 64 ct.length⌝ ∗ vecU8Buf A.repAlloc ctCap ctPtr ct := rfl
    rw [hct_eq]
    refine WSepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono
                    (sepConj_mono_right (vecU8Buf_cap_bounds A.repAlloc ctCap ctPtr ct))
                    (sepConj_mono_right
                      (sepConj_mono_left
                        (optVecU8Buf_cap_bounds A.repAlloc adCap adPtr adLen m'.addresses))))))))))))))))))))))))))))) ?_
    simp only [sepConj_assoc]
    set F_boxes := spUnused0 sp' ∗
      ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
      ((sp' + 28#64) ↦₃₂ counter) ∗
      ((sp' + 64#64) ↦₆₄ w15) ∗
      ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
      spUnused104 sp' ∗
      ((sp' + 104#64) ↦₆₄ w23) ∗ ((sp' + 112#64) ↦₈ b31) ∗
      ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
      memRegion (sp' + 224#64) 64 ∗
      vecU8Buf A.repAlloc rkCap rkPtr rk ∗
      memRegion x19 120 ∗
      (x21 ↦ₛ bs)
    refine WSepWPp.mono_pre (P' :=
        ⌜ctLen = BitVec.ofNat 64 ct.length⌝ ∗
        ⌜ct.length ≤ ctCap.toNat ∧ ctCap.toNat < 2 ^ 63⌝ ∗
        ⌜∀ ad, m'.addresses = some ad → ad.length ≤ adCap.toNat ∧ adCap.toNat < 2 ^ 63⌝ ∗
        ((((sp' + 16#64) ↦₆₄ adLen) ∗
          ((sp' + 32#64) ↦₆₄ ctLen) ∗
          ((sp' + 40#64) ↦₆₄ pqLen) ∗
          ((sp' + 48#64) ↦₆₄ (w52 ++ pcTag)) ∗
          ((sp' + 60#64) ↦₃₂ pcVal) ∗
          ((sp' + 88#64) ↦₆₄ adPtr) ∗
          ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          vecHeader (sp' + 136#64) w136 w144 w152 ∗
          ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
          vecU8Buf A.repAlloc ctCap ctPtr ct ∗
          optVecU8Buf A.repAlloc pqCap pqPtr pqLen m'.pqRatchet ∗
          optVecU8Buf A.repAlloc adCap adPtr adLen m'.addresses ∗
          A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_boxes))
      (by dsimp only [F_boxes]; rw [h48_pair]; apply entails_of_eq; sep_ac_rfl) ?_
    refine WSepWPp.pure_pre fun hct_len =>
      WSepWPp.pure_pre fun ⟨hct_le, hct_lt⟩ =>
      WSepWPp.pure_pre fun had_bnd => ?_
    subst hct_len
    set msg : SignalMessage :=
      { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey := pk, counter,
        previousCounter := m'.previousCounter.getD 0#32, ciphertext := ct,
        pqRatchet := m'.pqRatchet.getD [], addresses := m'.addresses,
        serialized := bs }
    have hFit_ok : FitsEnv M lim st (TryFromPostOutPreEnv (.ok msg)) := hout ▸ hFit
    have hFit_boxes := fitsEnv_postCtBoxes_of_ok (msg := msg) hct_le hct_lt had_bnd hFit_ok
    refine wpp_bind_frame_gen
      (post_ct_some_boxes_wp_placed hDropSpe hIntoBox st ct m'.pqRatchet m'.addresses
        hct_lt hFit_boxes hst hpc hrun hpstate hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28) ?_
    intro s2 P2 hpc2 hrun2 ⟨pqCap', pqPtr', ctBoxPtr, adBoxPtr, w96', evs_box, hbox_post,
      hst2, _, _, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hent2⟩
    have hFit_clone := fitsEnv_tryClone_of_postCtBoxes (msg := msg) hct_le hct_lt had_bnd hFit_ok hbox_post
    dsimp only [F_boxes]
    refine WSepWPp.mono_pre (sepConj_mono hent2
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (memRegion120_split16 x19))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine WSepWPp.exists_pre fun w1 => WSepWPp.exists_pre fun w0 => ?_
    set F_clone := spUnused0 sp' ∗
      ((sp' + 16#64) ↦₆₄ adLen) ∗
      ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
      ((sp' + 40#64) ↦₆₄ pqLen) ∗
      ((sp' + 88#64) ↦₆₄ adPtr) ∗
      spUnused104 sp' ∗
      vecHeader (sp' + 136#64) ctCap ctPtr (BitVec.ofNat 64 ct.length) ∗
      memRegion (sp' + 176#64) 48 ∗
      memRegion (sp' + 224#64) 64
    refine WSepWPp.mono_pre (P' :=
        ((x21 ↦ₛ msg.serialized) ∗
          ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 28#64) ↦₃₂ msg.counter) ∗
          ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
          ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
          ((sp' + 64#64) ↦₆₄ w15) ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          ((sp' + 96#64) ↦₆₄ w96') ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
          ((sp' + 112#64) ↦₈ b31) ∗
          ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
          vecU8Buf A.repAlloc rkCap rkPtr rk ∗
          vecU8Buf A.repAlloc pqCap' pqPtr' msg.pqRatchet ∗
          boxU8Buf A.repAlloc ctBoxPtr msg.ciphertext ∗
          optBoxU8Pending A.repAlloc adBoxPtr w96' msg.addresses ∗
          A.pool lim (M.stepEvents evs_box st) s2 ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_clone)
      (by dsimp only [F_clone, msg]; apply entails_of_eq; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (post_clone_and_pack_wp_placed hS hTryClone (M.stepEvents evs_box st) rk msg hout hbnd hpk rfl
        hFit_clone hst2 hpc2 hrun2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2)
      fun sf Pf ⟨hstf, evs_cp, hcp_env, hent⟩ =>
        ⟨hstf, evs_box ++ evs_cp,
          hout ▸ tryFromPostOutEnv_of_boxes_clone (msg := msg) hct_le hct_lt had_bnd hbox_post hcp_env,
          ?_⟩
    rw [M.stepEvents_append]
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_clone, msg]
    have hpack0 := memRegion104_0_pack64 sp' (b8.zeroExtend 32) counter (m'.previousCounter.getD 0#32)
      adLen (BitVec.ofNat 64 ct.length) pqLen ctBoxPtr w15 rkPtr rkCap adPtr w96'
    have hpack104 := memRegion72_104_pack sp' w23 ctCap ctPtr (BitVec.ofNat 64 ct.length)
      w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
    have hpack176 := memRegion112_of_48_64 sp'
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono hpack104 (sepConj_mono_left hpack176)))
    apply entails_of_eq; sep_ac_rfl

theorem post_after_54c_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 x21 rkCap rkPtr ctCap ctPtr ctLen pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64}
    {w136 w144 w152 w15 w23 : BitVec 64}
    {w12 w52 cTag cVal pcTag pcVal w68 w9 : BitVec 32} {w13 : BitVec 16}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    (bs rk : List (BitVec 8)) (m' : ProtoSignalMessage) (pk : PublicKey)
    {out : Except SignalProtocolError SignalMessage}
    (hgt9 : 9 < bs.length) (hlt : bs.length < 2 ^ 32)
    (hdec : decode ((bs.take (bs.length - 8)).drop 1) = some m')
    (hpk : pk.bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hc : optU32TagVal cTag cVal m'.counter)
    (hpc_tag : optU32TagVal pcTag pcVal m'.previousCounter)
    (hout : out =
      match m'.counter with
      | none => .error .invalidProtobufEncoding
      | some counter =>
        match m'.ciphertext with
        | none => .error .invalidProtobufEncoding
        | some ciphertext =>
          .ok { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey := pk, counter,
                previousCounter := m'.previousCounter.getD 0#32, ciphertext,
                pqRatchet := m'.pqRatchet.getD [], addresses := m'.addresses,
                serialized := bs })
    (hFit : FitsEnv M lim st (TryFromPostOutPreEnv out))
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1356#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 cTag 1#32)
    (hx8 : s.readReg64 .x8 = w15)
    (hx9 : s.readReg64 .x9 = (b8.zeroExtend 32).zeroExtend 64)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs.length)
    (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = adCap)
    (hx23 : s.readReg64 .x23 = (bs.headD 0#8).zeroExtend 64)
    (hx24 : s.readReg64 .x24 = (b7.zeroExtend 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap)
    (hx26 : s.readReg64 .x26 = speWord 2)
    (hx27 : s.readReg64 .x27 = ctCap)
    (hx28 : s.readReg64 .x28 = ctPtr) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (spUnused0 sp' ∗
        ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ adLen) ∗
        ((sp' + 28#64) ↦₃₂ cVal) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
        ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₃₂ pcTag) ∗
        ((sp' + 52#64) ↦₃₂ w52) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
        ((sp' + 64#64) ↦₆₄ (w68 ++ cTag)) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        spUnused104 sp' ∗
        ((sp' + 104#64) ↦₆₄ w23) ∗ ((sp' + 112#64) ↦₈ b31) ∗
        ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
        vecHeader (sp' + 136#64) w136 w144 w152 ∗
        ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
        memRegion (sp' + 224#64) 64 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        optVecU8Buf A.repAlloc ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A.repAlloc pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A.repAlloc adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, TryFromPostOutEnv out evs ∧
          (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
            memRegion (sp' + 176#64) 112 ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            (x21 ↦ₛ bs) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  cases hcnt : m'.counter with
  | none =>
    simp only [hcnt] at hout
    rw [hcnt] at hc
    dsimp only [optU32TagVal] at hc
    subst hc
    have h48_pair := (pointsTo32_pair_eq_pointsTo64 (sp' + 48#64) pcTag w52).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48_pair
    refine WSepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono
                    (optVecU8Buf_entails_deallocSlot A.repAlloc ctCap ctPtr ctLen m'.ciphertext)
                    (sepConj_mono
                      (optVecU8Buf_entails_deallocSlot A.repAlloc pqCap pqPtr pqLen m'.pqRatchet)
                      (sepConj_mono
                        (optVecU8Buf_entails_deallocSlot A.repAlloc adCap adPtr adLen m'.addresses)
                        (sepConj_mono_left (memRegion120_split16 x19)))))))))))))))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine WSepWPp.exists_pre fun w1 => WSepWPp.exists_pre fun w0 =>
      WSepWPp.exists_pre fun adAct => WSepWPp.exists_pre fun pqAct =>
      WSepWPp.exists_pre fun ctAct => ?_
    set F_cnt_none := spUnused0 sp' ∗
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ adLen) ∗
      ((sp' + 28#64) ↦₃₂ cVal) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
      ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₆₄ (w52 ++ pcTag)) ∗
      ((sp' + 60#64) ↦₃₂ pcVal) ∗ ((sp' + 64#64) ↦₆₄ (w68 ++ 0#32)) ∗
      spUnused104 sp' ∗
      ((sp' + 104#64) ↦₆₄ w23) ∗ ((sp' + 112#64) ↦₈ b31) ∗
      ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
      vecHeader (sp' + 136#64) w136 w144 w152 ∗
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
      memRegion (sp' + 224#64) 64 ∗
      (x21 ↦ₛ bs)
    refine WSepWPp.mono_pre (P' :=
        (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
          vecU8Buf A.repAlloc rkCap rkPtr rk ∗
          deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
          deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_cnt_none)
      (by dsimp only [F_cnt_none]; rw [h48_pair]; apply entails_of_eq; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (post_counter_none_wp_placed hS st rk ctAct pqAct adAct hout
        hst hpc hrun hpstate hx19 hx26 hx27 hx28 hx25 hx22)
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ =>
        ⟨hstf, evs, tryFromPostOutEnv_of_eq_error hout hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_cnt_none]
    have hpack0 := memRegion104_0_pack64 sp' w12 cVal pcVal
      adLen ctLen pqLen (w52 ++ pcTag) (w68 ++ 0#32) rkPtr rkCap adPtr pqPtr
    have hpack104 := memRegion72_104_pack sp' w23 w136 w144 w152 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
    have hpack176 := memRegion112_of_8_40_64 sp' (speWord 2)
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono hpack104 (sepConj_mono_left hpack176)))
    apply entails_of_eq; sep_ac_rfl
  | some counter =>
    simp only [hcnt] at hout
    rw [hcnt] at hc
    rcases hc with ⟨rfl, hcVal⟩
    subst cVal
    set F_cnt_some := spUnused0 sp' ∗
      ((sp' + 16#64) ↦₆₄ adLen) ∗
      ((sp' + 28#64) ↦₃₂ counter) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
      ((sp' + 40#64) ↦₆₄ pqLen) ∗
      ((sp' + 52#64) ↦₃₂ w52) ∗
      ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
      ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
      spUnused104 sp' ∗
      ((sp' + 104#64) ↦₆₄ w23) ∗ ((sp' + 112#64) ↦₈ b31) ∗
      ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
      vecHeader (sp' + 136#64) w136 w144 w152 ∗
      memRegion (sp' + 224#64) 64 ∗
      vecU8Buf A.repAlloc rkCap rkPtr rk ∗
      optVecU8Buf A.repAlloc ctCap ctPtr ctLen m'.ciphertext ∗
      optVecU8Buf A.repAlloc pqCap pqPtr pqLen m'.pqRatchet ∗
      optVecU8Buf A.repAlloc adCap adPtr adLen m'.addresses ∗
      memRegion x19 120 ∗
      (x21 ↦ₛ bs)
    refine WSepWPp.mono_pre (P' :=
        (((sp' + 12#64) ↦₃₂ w12) ∗
          ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
          ((sp' + 64#64) ↦₆₄ (w68 ++ 1#32)) ∗
          ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
          A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_cnt_some)
      (by dsimp only [F_cnt_some]; apply entails_of_eq; sep_ac_rfl) ?_
    refine wpp_bind_frame_gen
      (post_counter_some_head_wp_placed hDropSpe st
        hst hpc hrun hpstate hx8 hx9 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hpstate1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, evs₀, hfree₀, hent1⟩
    rw [pcVal_if_eq_getD hpc_tag] at hx8_1
    rw [zext32_zext64_8 b7] at hx24_1
    have hFit1 := fitsEnv_tryFromPostOutPre_step_freeOnly hfree₀ hFit
    dsimp only [F_cnt_some]
    refine WSepWPp.mono_pre (sepConj_mono_left hent1) ?_
    refine WSepWPp.mono_pre ?_
      (wpp_mono_post_noPanic ?_
        (post_after_578_wp_placed
          (rkCap := rkCap) (rkPtr := rkPtr) (ctLen := ctLen)
          (pqPtr := pqPtr) (pqLen := pqLen) (adPtr := adPtr) (adLen := adLen)
          (w136 := w136) (w144 := w144) (w152 := w152)
          (w52 := w52) (pcTag := pcTag) (pcVal := pcVal)
          hS hDropSpe hIntoBox hTryClone (M.stepEvents evs₀ st)
          bs rk m' pk hgt9 hlt hdec hpk hout hFit1
          hst1 hpc1 hrun1 hpstate1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
          hx25_1 hx26_1 hx27_1 hx28_1))
    · apply entails_of_eq; sep_ac_rfl
    · intro sf Pf ⟨hstf, evs₁, henv₁, hentf⟩
      refine ⟨hstf, evs₀ ++ evs₁, tryFromPostOutEnv_prepend_freeOnly hfree₀ henv₁, ?_⟩
      rw [M.stepEvents_append]
      exact hentf

theorem post_after_deser_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 x21 rkCap rkPtr ctCap ctPtr ctLen pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64}
    {w12 w52 cTag cVal pcTag pcVal w68 : BitVec 32}
    (bs rk : List (BitVec 8)) (m' : ProtoSignalMessage)
    {out : Except SignalProtocolError SignalMessage}
    (hgt9 : 9 < bs.length) (hlt : bs.length < 2 ^ 32)
    (hdec : decode ((bs.take (bs.length - 8)).drop 1) = some m')
    (hc : optU32TagVal cTag cVal m'.counter)
    (hpc_tag : optU32TagVal pcTag pcVal m'.previousCounter)
    (hout : out =
      match PublicKey.deserialize rk with
      | .error e => .error e
      | .ok senderRatchetKey =>
        match m'.counter with
        | none => .error .invalidProtobufEncoding
        | some counter =>
          match m'.ciphertext with
          | none => .error .invalidProtobufEncoding
          | some ciphertext =>
            .ok { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey, counter,
                  previousCounter := m'.previousCounter.getD 0#32, ciphertext,
                  pqRatchet := m'.pqRatchet.getD [], addresses := m'.addresses,
                  serialized := bs })
    (hFit : FitsEnv M lim st (TryFromPostOutPreEnv out))
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1220#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs.length)
    (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = adCap)
    (hx23 : s.readReg64 .x23 = (bs.headD 0#8).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap)
    (hx27 : s.readReg64 .x27 = ctCap)
    (hx28 : s.readReg64 .x28 = ctPtr) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (spUnused0 sp' ∗
        ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ adLen) ∗
        ((sp' + 28#64) ↦₃₂ cVal) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
        ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₃₂ pcTag) ∗
        ((sp' + 52#64) ↦₃₂ w52) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
        ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        memRegion (sp' + 104#64) 72 ∗
        deserializeResult33At (sp' + 176#64) (PublicKey.deserialize rk) ∗
        memRegion (sp' + 209#64) 15 ∗
        memRegion (sp' + 224#64) 64 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        optVecU8Buf A.repAlloc ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A.repAlloc pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A.repAlloc adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, TryFromPostOutEnv out evs ∧
          (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
            memRegion (sp' + 176#64) 112 ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            (x21 ↦ₛ bs) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  cases hdeser : PublicKey.deserialize rk with
  | error e =>
    simp only [hdeser] at hout
    refine WSepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono
                  (optVecU8Buf_entails_deallocSlot A.repAlloc ctCap ctPtr ctLen m'.ciphertext)
                  (sepConj_mono
                    (optVecU8Buf_entails_deallocSlot A.repAlloc pqCap pqPtr pqLen m'.pqRatchet)
                    (sepConj_mono
                      (optVecU8Buf_entails_deallocSlot A.repAlloc adCap adPtr adLen m'.addresses)
                      (sepConj_mono_left (memRegion120_split24 x19))))))))))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine WSepWPp.exists_pre fun w2 => WSepWPp.exists_pre fun w1 =>
      WSepWPp.exists_pre fun w0 => WSepWPp.exists_pre fun adAct =>
      WSepWPp.exists_pre fun pqAct => WSepWPp.exists_pre fun ctAct => ?_
    set F_deser_err := spUnused0 sp' ∗
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ adLen) ∗
      ((sp' + 28#64) ↦₃₂ cVal) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
      ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₃₂ pcTag) ∗
      ((sp' + 52#64) ↦₃₂ w52) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
      ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
      memRegion (sp' + 104#64) 72 ∗
      memRegion (sp' + 209#64) 15 ∗
      memRegion (sp' + 224#64) 64 ∗
      (x21 ↦ₛ bs)
    refine WSepWPp.mono_pre (P' :=
        (deserializeResult33At (sp' + 176#64) (.error e) ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ ((x19 + 16#64) ↦₆₄ w2) ∗
          memRegion (x19 + 24#64) 96 ∗
          vecU8Buf A.repAlloc rkCap rkPtr rk ∗
          deallocSlot A.repAlloc ctCap ctPtr ctAct ∗
          deallocSlot A.repAlloc pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A.repAlloc adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_deser_err)
      (by dsimp only [F_deser_err]; apply entails_of_eq; sep_ac_rfl) ?_
    refine wpp_frame_noPanic
      (post_deser_err_wp_placed hS st rk ctAct pqAct adAct e hdeser hout
        hst hpc hrun hx19 hx27 hx28 hx25 hx22)
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ =>
        ⟨hstf, evs, tryFromPostOutEnv_of_eq_error hout hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_deser_err]
    have hpack0 := memRegion104_0_pack sp' w12 cVal pcTag w52 pcVal cTag w68
      adLen ctLen pqLen rkPtr rkCap adPtr pqPtr
    have hpack176 := memRegion112_of_33_15_64 sp'
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono_right (sepConj_mono_left hpack176)))
    apply entails_of_eq; sep_ac_rfl
  | ok pk =>
    simp only [hdeser] at hout
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, w9, w13, w15, w23, b31, hpk⟩ :=
      exists_pkBytesOf pk.bytes.toList pk.bytes.2
    have hdeser_eq : deserializeResult33At (sp' + 176#64) (.ok pk) =
        ((sp' + 176#64) ↦₈ 0#8) ∗
        pkLayoutAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 := by
      dsimp only [deserializeResult33At]
      rw [hpk, ← pkLayoutAt_eq_pointsToBytes]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [hdeser_eq]
    refine WSepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (memRegion72_104_unpack sp'))))))))))))))))) ?_
    simp only [sepExists_sepConj_left]
    simp only [sepExists_sepConj_right]
    simp only [sepConj_assoc]
    refine WSepWPp.exists_pre fun w104 => WSepWPp.exists_pre fun b112 =>
      WSepWPp.exists_pre fun w120 => WSepWPp.exists_pre fun w124 =>
      WSepWPp.exists_pre fun c0 => WSepWPp.exists_pre fun c1 =>
      WSepWPp.exists_pre fun c2 => WSepWPp.exists_pre fun c3 =>
      WSepWPp.exists_pre fun c4 => WSepWPp.exists_pre fun c5 =>
      WSepWPp.exists_pre fun c6 => WSepWPp.exists_pre fun w136 =>
      WSepWPp.exists_pre fun w144 => WSepWPp.exists_pre fun w152 => ?_
    set F_deser_ok := spUnused0 sp' ∗
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ adLen) ∗
      ((sp' + 28#64) ↦₃₂ cVal) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
      ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₃₂ pcTag) ∗
      ((sp' + 52#64) ↦₃₂ w52) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
      ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
      ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
      spUnused104 sp' ∗
      vecHeader (sp' + 136#64) w136 w144 w152 ∗
      memRegion (sp' + 224#64) 64 ∗
      vecU8Buf A.repAlloc rkCap rkPtr rk ∗
      optVecU8Buf A.repAlloc ctCap ctPtr ctLen m'.ciphertext ∗
      optVecU8Buf A.repAlloc pqCap pqPtr pqLen m'.pqRatchet ∗
      optVecU8Buf A.repAlloc adCap adPtr adLen m'.addresses ∗
      memRegion x19 120 ∗
      (x21 ↦ₛ bs) ∗
      stackAt sp' (skipFieldStackX 100)
    refine WSepWPp.mono_pre (P' :=
        (((sp' + 176#64) ↦₈ 0#8) ∗
          pkLayoutAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
          memRegion (sp' + 209#64) 15 ∗
          ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
          ((sp' + 104#64) ↦₆₄ w104) ∗
          ((sp' + 112#64) ↦₈ b112) ∗
          ((sp' + 120#64) ↦₃₂ w120) ∗ ((sp' + 124#64) ↦₁₆ w124) ∗
          sevenBytesHeadAt (sp' + 128#64) c0 c1 c2 c3 c4 c5 c6 ∗
          A.pool lim st s) ∗ F_deser_ok)
      (by dsimp only [F_deser_ok]; apply entails_of_eq; sep_ac_rfl) ?_
    refine wpp_bind_frame_gen
      (post_deser_ok_head_wp_placed st hst hpc hrun) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hpstate1, hx8_1, hx9_1, hx24_1, hx26_1, hother1, hent1⟩
    have hx19_1 : s1.readReg64 .x19 = x19 := by
      rw [hother1 .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx19]
    have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
      rw [hother1 .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx20]
    have hx21_1 : s1.readReg64 .x21 = x21 := by
      rw [hother1 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx21]
    have hx22_1 : s1.readReg64 .x22 = adCap := by
      rw [hother1 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx22]
    have hx23_1 : s1.readReg64 .x23 = (bs.headD 0#8).zeroExtend 64 := by
      rw [hother1 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx23]
    have hx25_1 : s1.readReg64 .x25 = pqCap := by
      rw [hother1 .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx25]
    have hx27_1 : s1.readReg64 .x27 = ctCap := by
      rw [hother1 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx27]
    have hx28_1 : s1.readReg64 .x28 = ctPtr := by
      rw [hother1 .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx28]
    dsimp only [F_deser_ok]
    refine WSepWPp.mono_pre (sepConj_mono_left hent1) ?_
    refine WSepWPp.mono_pre (by apply entails_of_eq; sep_ac_rfl)
      (post_after_54c_wp_placed hS hDropSpe hIntoBox hTryClone st
        bs rk m' pk hgt9 hlt hdec hpk hc hpc_tag hout hFit
        hst1 hpc1 hrun1 hpstate1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
        hx25_1 hx26_1 hx27_1 hx28_1)

theorem tryFrom_post_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H)
    (st : M.σ) {x : TryFromGhost} {s0 s : State}
    (hgt9 : 9 < x.bytes.length)
    (hlt : x.bytes.length < 2 ^ 32)
    (hge3 : ¬ ((x.bytes.headD 0#8) >>> 4) < 3#8)
    (hle4 : ¬ 4#8 < ((x.bytes.headD 0#8) >>> 4))
    (hFit : FitsEnv M lim st (TryFromPostPreEnv x.bytes))
    (hpc : s.pc = (blkPl_85).base + 944#64)
    (hrun : s.status = .Running)
    (hst : LoopExitStatePlaced s0 (s0.sp - 448#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (memRegion (s0.sp - 448#64) 176 ∗
        memRegion (s0.sp - 448#64 + 288#64) 64 ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        A.pool lim st s ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100) ∗
        (match decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
         | some m' =>
           ⌜s.readReg64 .x24 = 0#64⌝ ∗ wireSignalMessageOf A.repAlloc (s0.sp - 448#64 + 176#64) m'
         | none =>
           ⌜s.readReg64 .x24 ≠ 0#64⌝ ∗ decodeErrorAt A.repAlloc (s.readReg64 .x24) ∗
             (∃∗ mErr, wireSignalMessageOf A.repAlloc (s0.sp - 448#64 + 176#64) mErr)) ∗
        memRegion x.ret 120 ∗ logOff tryFromPlacedImg)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        ∃ evs : List AllocEvent, TryFromPostEnv x.bytes evs ∧
          (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
            signalMessageResultAt A.repAlloc [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
            (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  set sp' := s0.sp - 448#64
  set out := SignalMessage.tryFrom protoSignalCodec x.bytes
  have hFit_out : FitsEnv M lim st (TryFromPostOutPreEnv out) := hFit
  have hout := tryFrom_eq_of_gt9 hgt9 hge3 hle4
  cases hdec : decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
  | none =>
    have hdec' : CryptoVerification.LibsignalProtoCodec.decode
        ((x.bytes.take (x.bytes.length - 8)).drop 1) = none := hdec
    simp only [hdec'] at hout
    rw [memRegion176_split_88_16_72 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine WSepWPp.exists_pre fun mErr => ?_
    set F_none := memRegion sp' 88 ∗ memRegion (sp' + 104#64) 72 ∗
      memRegion (sp' + 288#64) 64 ∗ (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg
    refine WSepWPp.mono_pre (P' :=
        ⌜s.readReg64 .x24 ≠ 0#64⌝ ∗
        ((wireSignalMessageOf A.repAlloc (sp' + 176#64) mErr ∗
          decodeErrorAt A.repAlloc (s.readReg64 .x24) ∗
          memRegion (sp' + 88#64) 16 ∗
          memRegion x.ret 120 ∗
          A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_none))
      (by dsimp only [F_none]; apply entails_of_eq; sep_ac_rfl) ?_
    refine WSepWPp.pure_pre fun hx24_ne => ?_
    refine wpp_frame_noPanic
      (post_none_wp_placed hS hDropErr st hout hst hpc hrun rfl hx24_ne mErr)
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ =>
        ⟨hstf, evs, tryFromPostOutEnv_of_eq_error hout hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_none]
    refine Entails.trans ?_
      (sepConj_mono_left (memRegion352_of_88_16_72_112_64 sp'))
    apply entails_of_eq; sep_ac_rfl
  | some m' =>
    have hdec' : CryptoVerification.LibsignalProtoCodec.decode
        ((x.bytes.take (x.bytes.length - 8)).drop 1) = some m' := hdec
    simp only [hdec'] at hout
    cases hrk : m'.ratchetKey with
    | none =>
      simp only [hrk] at hout
      rw [memRegion176_split_88_16_72 sp']
      simp only [sepConj_assoc]
      set F_rk_none := memRegion sp' 88 ∗ memRegion (sp' + 104#64) 72 ∗
        memRegion (sp' + 288#64) 64 ∗ (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg
      refine WSepWPp.mono_pre (P' :=
          ⌜s.readReg64 .x24 = 0#64⌝ ∗
          ((wireSignalMessageOf A.repAlloc (sp' + 176#64) m' ∗
            memRegion (sp' + 88#64) 16 ∗
            memRegion x.ret 120 ∗
            A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_rk_none))
        (by dsimp only [F_rk_none]; apply entails_of_eq; sep_ac_rfl) ?_
      refine WSepWPp.pure_pre fun hx24 => ?_
      refine wpp_frame_noPanic
        (post_rk_none_wp_placed hS st hrk hout hst hpc hrun hx24)
        fun sf Pf ⟨hstf, evs, hfree, hent⟩ =>
          ⟨hstf, evs, tryFromPostOutEnv_of_eq_error hout hfree, ?_⟩
      refine Entails.trans (sepConj_mono_left hent) ?_
      dsimp only [F_rk_none]
      refine Entails.trans ?_
        (sepConj_mono_left (memRegion352_of_88_16_72_112_64 sp'))
      apply entails_of_eq; sep_ac_rfl
    | some rk =>
      simp only [hrk] at hout
      rw [memRegion176_split_104_72 sp']
      simp only [sepConj_assoc]
      refine WSepWPp.mono_pre
        (sepConj_mono (memRegion104_0_unpack sp')
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (wireSignalMessageOf_rk_some_entails A.repAlloc sp' hrk))))))))) ?_
      simp only [sepExists_sepConj_left]
      simp only [sepExists_sepConj_right]
      simp only [sepConj_assoc]
      refine WSepWPp.exists_pre fun w12 => WSepWPp.exists_pre fun w16 =>
        WSepWPp.exists_pre fun w28 => WSepWPp.exists_pre fun w32 =>
        WSepWPp.exists_pre fun w40 => WSepWPp.exists_pre fun w48 =>
        WSepWPp.exists_pre fun w52 => WSepWPp.exists_pre fun w60 =>
        WSepWPp.exists_pre fun w64 => WSepWPp.exists_pre fun w68 =>
        WSepWPp.exists_pre fun w72 => WSepWPp.exists_pre fun w80 =>
        WSepWPp.exists_pre fun w88 => WSepWPp.exists_pre fun w96 =>
        WSepWPp.exists_pre fun rkCap => WSepWPp.exists_pre fun rkPtr =>
        WSepWPp.exists_pre fun ctCap => WSepWPp.exists_pre fun ctPtr =>
        WSepWPp.exists_pre fun ctLen => WSepWPp.exists_pre fun pqCap =>
        WSepWPp.exists_pre fun pqPtr => WSepWPp.exists_pre fun pqLen =>
        WSepWPp.exists_pre fun adCap => WSepWPp.exists_pre fun adPtr =>
        WSepWPp.exists_pre fun adLen => WSepWPp.exists_pre fun cTag =>
        WSepWPp.exists_pre fun cVal => WSepWPp.exists_pre fun pcTag =>
        WSepWPp.exists_pre fun pcVal => ?_
      set F_rk_head := spUnused0 sp' ∗
        ((sp' + 12#64) ↦₃₂ w12) ∗
        ((sp' + 52#64) ↦₃₂ w52) ∗
        ((sp' + 68#64) ↦₃₂ w68) ∗
        memRegion (sp' + 104#64) 72 ∗
        optVecU8Buf A.repAlloc ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A.repAlloc pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A.repAlloc adCap adPtr adLen m'.addresses ∗
        memRegion x.ret 120 ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        memRegion (sp' + 288#64) 64
      refine WSepWPp.mono_pre (P' :=
          ⌜s.readReg64 .x24 = 0#64⌝ ∗
          ⌜optU32TagVal cTag cVal m'.counter⌝ ∗
          ⌜optU32TagVal pcTag pcVal m'.previousCounter⌝ ∗
          ((((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
            ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
            ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
            ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
            ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
            vecHeader (sp' + 176#64) rkCap rkPtr (BitVec.ofNat 64 rk.length) ∗
            vecU8Buf A.repAlloc rkCap rkPtr rk ∗
            vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
            vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
            vecHeader (sp' + 248#64) adCap adPtr adLen ∗
            ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
            ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
            logOff tryFromPlacedImg ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_rk_head))
        (by dsimp only [F_rk_head]; apply entails_of_eq; sep_ac_rfl) ?_
      refine WSepWPp.pure_pre fun hx24 =>
        WSepWPp.pure_pre fun hc => WSepWPp.pure_pre fun hpc_tag => ?_
      refine wpp_bind_frame_gen
        (post_rk_some_head_wp_placed hDropSpe st rk hst hpc hrun hx24) ?_
      intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _,
        hx25_1, _, hx27_1, hx28_1, evs₀, hfree₀, hent1⟩
      have hFit1 := fitsEnv_tryFromPostOutPre_step_freeOnly hfree₀ hFit_out
      dsimp only [F_rk_head]
      set F_tail := memRegion (sp' + 288#64) 64 ∗ logOff tryFromPlacedImg
      refine WSepWPp.mono_pre (P' :=
          (spUnused0 sp' ∗
            ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ adLen) ∗
            ((sp' + 28#64) ↦₃₂ cVal) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
            ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₃₂ pcTag) ∗
            ((sp' + 52#64) ↦₃₂ w52) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
            ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
            ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
            ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
            memRegion (sp' + 104#64) 72 ∗
            deserializeResult33At (sp' + 176#64) (PublicKey.deserialize rk) ∗
            memRegion (sp' + 209#64) 15 ∗
            memRegion (sp' + 224#64) 64 ∗
            vecU8Buf A.repAlloc rkCap rkPtr rk ∗
            optVecU8Buf A.repAlloc ctCap ctPtr ctLen m'.ciphertext ∗
            optVecU8Buf A.repAlloc pqCap pqPtr pqLen m'.pqRatchet ∗
            optVecU8Buf A.repAlloc adCap adPtr adLen m'.addresses ∗
            memRegion x.ret 120 ∗
            (x.bytesA ↦ₛ x.bytes) ∗
            A.pool lim (M.stepEvents evs₀ st) s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_tail)
        (Entails.trans (sepConj_mono_left hent1) (by dsimp only [F_tail]; apply entails_of_eq; sep_ac_rfl)) ?_
      refine wpp_frame_noPanic
        (post_after_deser_wp_placed hS hDropSpe hIntoBox hTryClone (M.stepEvents evs₀ st)
          x.bytes rk m' hgt9 hlt hdec hc hpc_tag hout hFit1
          hst1 hpc1 hrun1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1)
        fun sf Pf ⟨hstf, evs₁, henv₁, hent⟩ =>
          ⟨hstf, evs₀ ++ evs₁, tryFromPostOutEnv_prepend_freeOnly hfree₀ henv₁, ?_⟩
      rw [M.stepEvents_append]
      refine Entails.trans (sepConj_mono_left hent) ?_
      dsimp only [F_tail]
      refine Entails.trans ?_
        (sepConj_mono_left (memRegion352_of_104_72_112_64 sp'))
      apply entails_of_eq; sep_ac_rfl

/-- `tryFromQp s0` weakening of `tryFrom_post_wp_placed` for callers using `tryFromQp`. -/
theorem tryFrom_post_wp_placed_tryFromQp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H)
    (st : M.σ) {x : TryFromGhost} {s0 s : State}
    (hgt9 : 9 < x.bytes.length)
    (hlt : x.bytes.length < 2 ^ 32)
    (hge3 : ¬ ((x.bytes.headD 0#8) >>> 4) < 3#8)
    (hle4 : ¬ 4#8 < ((x.bytes.headD 0#8) >>> 4))
    (hFit : FitsEnv M lim st (TryFromPostPreEnv x.bytes))
    (hpc : s.pc = (blkPl_85).base + 944#64)
    (hrun : s.status = .Running)
    (hst : LoopExitStatePlaced s0 (s0.sp - 448#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (memRegion (s0.sp - 448#64) 176 ∗
        memRegion (s0.sp - 448#64 + 288#64) 64 ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        A.pool lim st s ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100) ∗
        (match decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
         | some m' =>
           ⌜s.readReg64 .x24 = 0#64⌝ ∗ wireSignalMessageOf A.repAlloc (s0.sp - 448#64 + 176#64) m'
         | none =>
           ⌜s.readReg64 .x24 ≠ 0#64⌝ ∗ decodeErrorAt A.repAlloc (s.readReg64 .x24) ∗
             (∃∗ mErr, wireSignalMessageOf A.repAlloc (s0.sp - 448#64 + 176#64) mErr)) ∗
        memRegion x.ret 120 ∗ logOff tryFromPlacedImg)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        ∃ evs : List AllocEvent, TryFromPostEnv x.bytes evs ∧
          (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
            signalMessageResultAt A.repAlloc [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
            (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (tryFromQp s0) :=
  wpp_to_tryFromQp (tryFrom_post_wp_placed hS hDropErr hDropSpe hIntoBox hTryClone st
    hgt9 hlt hge3 hle4 hFit hpc hrun hst)

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget

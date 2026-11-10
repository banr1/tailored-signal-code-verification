/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one
attribute [local simp, local wp_norm] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one

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

theorem wireSignalMessageOf_rk_some_entails (A : RustAlloc) (sp' : BitVec 64)
    {m' : ProtoSignalMessage} {rk : List (BitVec 8)} (hrk : m'.ratchetKey = some rk) :
    wireSignalMessageOf A (sp' + 176#64) m' ⊢
      ∃∗ rkCap : BitVec 64, ∃∗ rkPtr : BitVec 64,
      ∃∗ ctCap : BitVec 64, ∃∗ ctPtr : BitVec 64, ∃∗ ctLen : BitVec 64,
      ∃∗ pqCap : BitVec 64, ∃∗ pqPtr : BitVec 64, ∃∗ pqLen : BitVec 64,
      ∃∗ adCap : BitVec 64, ∃∗ adPtr : BitVec 64, ∃∗ adLen : BitVec 64,
      ∃∗ cTag : BitVec 32, ∃∗ cVal : BitVec 32,
      ∃∗ pcTag : BitVec 32, ∃∗ pcVal : BitVec 32,
        ⌜optU32TagVal cTag cVal m'.counter⌝ ∗
        ⌜optU32TagVal pcTag pcVal m'.previousCounter⌝ ∗
        vecHeader (sp' + 176#64) rkCap rkPtr (BitVec.ofNat 64 rk.length) ∗
        vecU8Buf A rkCap rkPtr rk ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) := by
  unfold wireSignalMessageOf
  refine Entails.sepExists_elim fun g => ?_
  unfold wireSignalMessageAt
  rw [hrk]
  have hrk_eq : optVecU8At A g.rk (sp' + 176#64) (some rk) =
      vecHeader (sp' + 176#64) g.rk.1 g.rk.2 (BitVec.ofNat 64 rk.length) ∗
      vecU8Buf A g.rk.1 g.rk.2 rk := by
    unfold optVecU8At
    exact vecU8At_eq_header_buf A (sp' + 176#64) g.rk.1 g.rk.2 rk
  rw [hrk_eq, sepConj_assoc]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (optVecU8At_entails_header_buf A g.ct (sp' + 200#64) m'.ciphertext)
        (sepConj_mono (optVecU8At_entails_header_buf A g.pq (sp' + 224#64) m'.pqRatchet)
          (sepConj_mono (optVecU8At_entails_header_buf A g.addr (sp' + 248#64) m'.addresses)
            (sepConj_mono
              (by simpa [BitVec.add_assoc, BitVec.reduceAdd] using optU32At_entails_tag_val (sp' + 272#64) m'.counter)
              (by simpa [BitVec.add_assoc, BitVec.reduceAdd] using optU32At_entails_tag_val (sp' + 280#64) m'.previousCounter))))))) ?_
  simp only [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ctCap => Entails.sepExists_elim fun ctPtr =>
    Entails.sepExists_elim fun ctLen => Entails.sepExists_elim fun pqCap =>
    Entails.sepExists_elim fun pqPtr => Entails.sepExists_elim fun pqLen =>
    Entails.sepExists_elim fun adCap => Entails.sepExists_elim fun adPtr =>
    Entails.sepExists_elim fun adLen => Entails.sepExists_elim fun cTag =>
    Entails.sepExists_elim fun cVal => Entails.sepExists_elim fun pcTag =>
    Entails.sepExists_elim fun pcVal => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro g.rk.1)
  refine Entails.trans ?_ (Entails.sepExists_intro g.rk.2)
  refine Entails.trans ?_ (Entails.sepExists_intro ctCap)
  refine Entails.trans ?_ (Entails.sepExists_intro ctPtr)
  refine Entails.trans ?_ (Entails.sepExists_intro ctLen)
  refine Entails.trans ?_ (Entails.sepExists_intro pqCap)
  refine Entails.trans ?_ (Entails.sepExists_intro pqPtr)
  refine Entails.trans ?_ (Entails.sepExists_intro pqLen)
  refine Entails.trans ?_ (Entails.sepExists_intro adCap)
  refine Entails.trans ?_ (Entails.sepExists_intro adPtr)
  refine Entails.trans ?_ (Entails.sepExists_intro adLen)
  refine Entails.trans ?_ (Entails.sepExists_intro cTag)
  refine Entails.trans ?_ (Entails.sepExists_intro cVal)
  refine Entails.trans ?_ (Entails.sepExists_intro pcTag)
  refine Entails.trans ?_ (Entails.sepExists_intro pcVal)
  apply entails_of_eq; ac_rfl

theorem memRegion112_of_48_64 (sp' : BitVec 64) :
    memRegion (sp' + 176#64) 48 ∗ memRegion (sp' + 224#64) 64 ⊢
      memRegion (sp' + 176#64) 112 := by
  have hs := memRegion_split (sp' + 176#64) 48 64 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs
  rw [hs]
  exact Entails.refl _

theorem memRegion112_of_33_15_64 (sp' : BitVec 64) :
    memRegion (sp' + 176#64) 33 ∗ memRegion (sp' + 209#64) 15 ∗ memRegion (sp' + 224#64) 64 ⊢
      memRegion (sp' + 176#64) 112 := by
  have hs := memRegion_split (sp' + 176#64) 33 15 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs
  rw [← sepConj_assoc, ← hs]
  exact memRegion112_of_48_64 sp'

theorem memRegion112_of_8_40_64 (sp' w176 : BitVec 64) :
    ((sp' + 176#64) ↦₆₄ w176) ∗ memRegion (sp' + 184#64) 40 ∗ memRegion (sp' + 224#64) 64 ⊢
      memRegion (sp' + 176#64) 112 := by
  have hs := memRegion_split (sp' + 176#64) 8 40 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs
  refine Entails.trans
    (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 176#64) w176)) ?_
  rw [← sepConj_assoc, ← hs]
  exact memRegion112_of_48_64 sp'

theorem memRegion104_0_pack64 (sp' : BitVec 64)
    (w12 w28 w60 : BitVec 32)
    (w16 w32 w40 w48 w64 w72 w80 w88 w96 : BitVec 64) :
    spUnused0 sp' ∗
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ w16) ∗
      ((sp' + 28#64) ↦₃₂ w28) ∗ ((sp' + 32#64) ↦₆₄ w32) ∗
      ((sp' + 40#64) ↦₆₄ w40) ∗ ((sp' + 48#64) ↦₆₄ w48) ∗
      ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₆₄ w64) ∗
      ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
      ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ⊢
      memRegion sp' 104 := by
  rw [pointsTo64_split32 (sp' + 48#64) w48, pointsTo64_split32 (sp' + 64#64) w64]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact memRegion104_0_pack sp' w12 w28
    (w48.extractLsb' 0 32) (w48.extractLsb' 32 32) w60
    (w64.extractLsb' 0 32) (w64.extractLsb' 32 32)
    w16 w32 w40 w72 w80 w88 w96

theorem vecU8Buf_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => ?_
  rw [pure_true_emp h.2.1, emp_sepConj, pure_true_emp h, emp_sepConj]
  exact Entails.refl _

theorem zext32_zext64_8 (b : BitVec 8) :
    (b.zeroExtend 32).zeroExtend 64 = b.zeroExtend 64 := by bv_kernel

theorem SepWPp.bind_frame_tryFrom {prog : Program} {mid ret : BitVec 64} {s0 s : Arm64.State}
    {P F : SepProp} {Q' Q : Arm64.State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q' (tryFromQp s0))
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q' sm Pm →
      SepWPp prog ret sm (Pm ∗ F) Q (tryFromQp s0)) :
    SepWPp prog ret s (P ∗ F) Q (tryFromQp s0) := by
  refine SepWPp.bind (SepWPp.frame_tryFrom (Q := fun sm Pmf => ∃ Pm, Pmf = Pm ∗ F ∧ Q' sm Pm)
    h1 (fun _ Pm hqm => ⟨Pm, rfl, hqm⟩)) ?_
  intro sm Pmf hpc hrun ⟨Pm, hPmf, hqm⟩
  subst hPmf
  exact h2 sm Pm hpc hrun hqm

theorem post_after_578_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    (hDropSpe : DropSpeOkW img C A ctl abs)
    (hIntoBox : IntoBoxedSliceOk img C A ctl abs)
    (hTryClone : TryCloneFromRefOk img C A ctl abs)
    {s0 s : State}
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
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x578#64)
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
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
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
        vecU8Buf A rkCap rkPtr rk ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
          memRegion (sp' + 176#64) 112 ∗
          signalMessageResultAt A [] x19 out ∗
          (x21 ↦ₛ bs) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  have h48_pair := (pointsTo32_pair_eq_pointsTo64 (sp' + 48#64) pcTag w52).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48_pair
  cases hct : m'.ciphertext with
  | none =>
    simp only [hct] at hout
    have hct_eq : optVecU8Buf A ctCap ctPtr ctLen none = ⌜ctCap = noneCap⌝ := rfl
    rw [hct_eq]
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono (optVecU8Buf_entails_deallocSlot A pqCap pqPtr pqLen m'.pqRatchet)
                    (sepConj_mono (optVecU8Buf_entails_deallocSlot A adCap adPtr adLen m'.addresses)
                      (sepConj_mono_left (memRegion120_split16 x19)))))))))))))))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 =>
      SepWPp.exists_pre fun adAct => SepWPp.exists_pre fun pqAct => ?_
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
    refine SepWPp.mono_pre (P' := ⌜ctCap = noneCap⌝ ∗
        ((((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
          vecU8Buf A rkCap rkPtr rk ∗
          deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_ct_none))
      (by dsimp only [F_ct_none]; rw [h48_pair]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.pure_pre fun hct_cap => ?_
    subst hct_cap
    refine SepWPp.frame_tryFrom
      (post_ct_none_wp ctl hS rk pqAct adAct hout hst hpc hrun hpstate hx19 hx26 hx25 hx22)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_ct_none]
    have hpack0 := memRegion104_0_pack64 sp' (b8.zeroExtend 32) counter pcVal
      adLen ctLen pqLen (w52 ++ pcTag) w15 rkPtr rkCap adPtr pqPtr
    have hpack104 := memRegion72_104_pack sp' w23 w136 w144 w152 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
    have hpack176 := memRegion112_of_8_40_64 sp' (speWord 2)
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono hpack104 (sepConj_mono_left hpack176)))
    apply entails_of_eq; ac_rfl
  | some ct =>
    simp only [hct] at hout
    have hbnd := msg_bounds_of_decode hgt9 hlt hdec hct
    have hct_eq : optVecU8Buf A ctCap ctPtr ctLen (some ct) =
        ⌜ctLen = BitVec.ofNat 64 ct.length⌝ ∗ vecU8Buf A ctCap ctPtr ct := rfl
    rw [hct_eq]
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (vecU8Buf_cap_lt A ctCap ctPtr ct)))))))))))))))))))))))))))) ?_
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
      vecU8Buf A rkCap rkPtr rk ∗
      memRegion x19 120 ∗
      (x21 ↦ₛ bs)
    refine SepWPp.mono_pre (P' :=
        ⌜ctLen = BitVec.ofNat 64 ct.length⌝ ∗ ⌜ctCap.toNat < 2 ^ 63⌝ ∗
        ((((sp' + 16#64) ↦₆₄ adLen) ∗
          ((sp' + 32#64) ↦₆₄ ctLen) ∗
          ((sp' + 40#64) ↦₆₄ pqLen) ∗
          ((sp' + 48#64) ↦₆₄ (w52 ++ pcTag)) ∗
          ((sp' + 60#64) ↦₃₂ pcVal) ∗
          ((sp' + 88#64) ↦₆₄ adPtr) ∗
          ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          vecHeader (sp' + 136#64) w136 w144 w152 ∗
          ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
          vecU8Buf A ctCap ctPtr ct ∗
          optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
          optVecU8Buf A adCap adPtr adLen m'.addresses ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_boxes))
      (by dsimp only [F_boxes]; rw [h48_pair]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.pure_pre fun hct_len => SepWPp.pure_pre fun hct_lt => ?_
    subst hct_len
    refine SepWPp.bind_frame_tryFrom
      (post_ct_some_boxes_wp ctl hDropSpe hIntoBox ct m'.pqRatchet m'.addresses
        hct_lt hst hpc hrun hpstate hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28) ?_
    intro s2 P2 hpc2 hrun2 ⟨pqCap', pqPtr', ctBoxPtr, adBoxPtr, w96',
      hst2, _, _, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hent2⟩
    dsimp only [F_boxes]
    refine SepWPp.mono_pre (sepConj_mono hent2
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (memRegion120_split16 x19))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
    set msg : SignalMessage :=
      { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey := pk, counter,
        previousCounter := m'.previousCounter.getD 0#32, ciphertext := ct,
        pqRatchet := m'.pqRatchet.getD [], addresses := m'.addresses,
        serialized := bs }
    set F_clone := spUnused0 sp' ∗
      ((sp' + 16#64) ↦₆₄ adLen) ∗
      ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
      ((sp' + 40#64) ↦₆₄ pqLen) ∗
      ((sp' + 88#64) ↦₆₄ adPtr) ∗
      spUnused104 sp' ∗
      vecHeader (sp' + 136#64) ctCap ctPtr (BitVec.ofNat 64 ct.length) ∗
      memRegion (sp' + 176#64) 48 ∗
      memRegion (sp' + 224#64) 64
    refine SepWPp.mono_pre (P' :=
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
          vecU8Buf A rkCap rkPtr rk ∗
          vecU8Buf A pqCap' pqPtr' msg.pqRatchet ∗
          boxU8Buf A ctBoxPtr msg.ciphertext ∗
          optBoxU8Pending A adBoxPtr w96' msg.addresses ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_clone)
      (by dsimp only [F_clone, msg]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (post_clone_and_pack_wp ctl hS hTryClone rk msg hout hbnd hpk rfl
        hst2 hpc2 hrun2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_clone, msg]
    have hpack0 := memRegion104_0_pack64 sp' (b8.zeroExtend 32) counter (m'.previousCounter.getD 0#32)
      adLen (BitVec.ofNat 64 ct.length) pqLen ctBoxPtr w15 rkPtr rkCap adPtr w96'
    have hpack104 := memRegion72_104_pack sp' w23 ctCap ctPtr (BitVec.ofNat 64 ct.length)
      w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
    have hpack176 := memRegion112_of_48_64 sp'
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono hpack104 (sepConj_mono_left hpack176)))
    apply entails_of_eq; ac_rfl

theorem post_after_54c_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    (hDropSpe : DropSpeOkW img C A ctl abs)
    (hIntoBox : IntoBoxedSliceOk img C A ctl abs)
    (hTryClone : TryCloneFromRefOk img C A ctl abs)
    {s0 s : State}
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
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x54c#64)
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
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
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
        vecU8Buf A rkCap rkPtr rk ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
          memRegion (sp' + 176#64) 112 ∗
          signalMessageResultAt A [] x19 out ∗
          (x21 ↦ₛ bs) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  cases hcnt : m'.counter with
  | none =>
    simp only [hcnt] at hout
    rw [hcnt] at hc
    dsimp only [optU32TagVal] at hc
    subst hc
    have h48_pair := (pointsTo32_pair_eq_pointsTo64 (sp' + 48#64) pcTag w52).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48_pair
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono (optVecU8Buf_entails_deallocSlot A ctCap ctPtr ctLen m'.ciphertext)
                    (sepConj_mono (optVecU8Buf_entails_deallocSlot A pqCap pqPtr pqLen m'.pqRatchet)
                      (sepConj_mono (optVecU8Buf_entails_deallocSlot A adCap adPtr adLen m'.addresses)
                        (sepConj_mono_left (memRegion120_split16 x19)))))))))))))))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 =>
      SepWPp.exists_pre fun adAct => SepWPp.exists_pre fun pqAct =>
      SepWPp.exists_pre fun ctAct => ?_
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
    refine SepWPp.mono_pre (P' :=
        (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
          vecU8Buf A rkCap rkPtr rk ∗
          deallocSlot A ctCap ctPtr ctAct ∗
          deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_cnt_none)
      (by dsimp only [F_cnt_none]; rw [h48_pair]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (post_counter_none_wp ctl hS rk ctAct pqAct adAct hout
        hst hpc hrun hpstate hx19 hx26 hx27 hx28 hx25 hx22)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_cnt_none]
    have hpack0 := memRegion104_0_pack64 sp' w12 cVal pcVal
      adLen ctLen pqLen (w52 ++ pcTag) (w68 ++ 0#32) rkPtr rkCap adPtr pqPtr
    have hpack104 := memRegion72_104_pack sp' w23 w136 w144 w152 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
    have hpack176 := memRegion112_of_8_40_64 sp' (speWord 2)
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono hpack104 (sepConj_mono_left hpack176)))
    apply entails_of_eq; ac_rfl
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
      vecU8Buf A rkCap rkPtr rk ∗
      optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
      optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
      optVecU8Buf A adCap adPtr adLen m'.addresses ∗
      memRegion x19 120 ∗
      (x21 ↦ₛ bs)
    refine SepWPp.mono_pre (P' :=
        (((sp' + 12#64) ↦₃₂ w12) ∗
          ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
          ((sp' + 64#64) ↦₆₄ (w68 ++ 1#32)) ∗
          ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_cnt_some)
      (by dsimp only [F_cnt_some]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_tryFrom
      (post_counter_some_head_wp ctl hDropSpe
        hst hpc hrun hpstate hx8 hx9 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hpstate1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hent1⟩
    rw [pcVal_if_eq_getD hpc_tag] at hx8_1
    rw [zext32_zext64_8 b7] at hx24_1
    dsimp only [F_cnt_some]
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    refine SepWPp.mono_pre (by apply entails_of_eq; ac_rfl)
      (post_after_578_wp ctl hS hDropSpe hIntoBox hTryClone
        bs rk m' pk hgt9 hlt hdec hpk hout
        hst1 hpc1 hrun1 hpstate1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
        hx25_1 hx26_1 hx27_1 hx28_1)

theorem post_after_deser_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    (hDropSpe : DropSpeOkW img C A ctl abs)
    (hIntoBox : IntoBoxedSliceOk img C A ctl abs)
    (hTryClone : TryCloneFromRefOk img C A ctl abs)
    {s0 s : State}
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
    (hst : PostEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x4c4#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs.length)
    (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = adCap)
    (hx23 : s.readReg64 .x23 = (bs.headD 0#8).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap)
    (hx27 : s.readReg64 .x27 = ctCap)
    (hx28 : s.readReg64 .x28 = ctPtr) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
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
        vecU8Buf A rkCap rkPtr rk ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueState img s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
          memRegion (sp' + 176#64) 112 ∗
          signalMessageResultAt A [] x19 out ∗
          (x21 ↦ₛ bs) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  cases hdeser : PublicKey.deserialize rk with
  | error e =>
    simp only [hdeser] at hout
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (optVecU8Buf_entails_deallocSlot A ctCap ctPtr ctLen m'.ciphertext)
                  (sepConj_mono (optVecU8Buf_entails_deallocSlot A pqCap pqPtr pqLen m'.pqRatchet)
                    (sepConj_mono (optVecU8Buf_entails_deallocSlot A adCap adPtr adLen m'.addresses)
                      (sepConj_mono_left (memRegion120_split24 x19))))))))))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w1 =>
      SepWPp.exists_pre fun w0 => SepWPp.exists_pre fun adAct =>
      SepWPp.exists_pre fun pqAct => SepWPp.exists_pre fun ctAct => ?_
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
    refine SepWPp.mono_pre (P' :=
        (deserializeResult33At (sp' + 176#64) (.error e) ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ ((x19 + 16#64) ↦₆₄ w2) ∗
          memRegion (x19 + 24#64) 96 ∗
          vecU8Buf A rkCap rkPtr rk ∗
          deallocSlot A ctCap ctPtr ctAct ∗
          deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_deser_err)
      (by dsimp only [F_deser_err]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (post_deser_err_wp ctl hS rk ctAct pqAct adAct e hdeser hout
        hst hpc hrun hx19 hx27 hx28 hx25 hx22)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_deser_err]
    have hpack0 := memRegion104_0_pack sp' w12 cVal pcTag w52 pcVal cTag w68
      adLen ctLen pqLen rkPtr rkCap adPtr pqPtr
    have hpack176 := memRegion112_of_33_15_64 sp'
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono_right (sepConj_mono_left hpack176)))
    apply entails_of_eq; ac_rfl
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
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (memRegion72_104_unpack sp'))))))))))))))))) ?_
    simp only [sepExists_sepConj_left]
    simp only [sepExists_sepConj_right]
    simp only [sepConj_assoc]
    refine SepWPp.exists_pre fun w104 => SepWPp.exists_pre fun b112 =>
      SepWPp.exists_pre fun w120 => SepWPp.exists_pre fun w124 =>
      SepWPp.exists_pre fun c0 => SepWPp.exists_pre fun c1 =>
      SepWPp.exists_pre fun c2 => SepWPp.exists_pre fun c3 =>
      SepWPp.exists_pre fun c4 => SepWPp.exists_pre fun c5 =>
      SepWPp.exists_pre fun c6 => SepWPp.exists_pre fun w136 =>
      SepWPp.exists_pre fun w144 => SepWPp.exists_pre fun w152 => ?_
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
      vecU8Buf A rkCap rkPtr rk ∗
      optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
      optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
      optVecU8Buf A adCap adPtr adLen m'.addresses ∗
      memRegion x19 120 ∗
      (x21 ↦ₛ bs) ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100)
    refine SepWPp.mono_pre (P' :=
        (((sp' + 176#64) ↦₈ 0#8) ∗
          pkLayoutAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
          memRegion (sp' + 209#64) 15 ∗
          ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
          ((sp' + 104#64) ↦₆₄ w104) ∗
          ((sp' + 112#64) ↦₈ b112) ∗
          ((sp' + 120#64) ↦₃₂ w120) ∗ ((sp' + 124#64) ↦₁₆ w124) ∗
          sevenBytesHeadAt (sp' + 128#64) c0 c1 c2 c3 c4 c5 c6) ∗ F_deser_ok)
      (by dsimp only [F_deser_ok]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_tryFrom
      (post_deser_ok_head_wp ctl hst hpc hrun) ?_
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
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    refine SepWPp.mono_pre (by apply entails_of_eq; ac_rfl)
      (post_after_54c_wp ctl hS hDropSpe hIntoBox hTryClone
        bs rk m' pk hgt9 hlt hdec hpk hc hpc_tag hout
        hst1 hpc1 hrun1 hpstate1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
        hx25_1 hx26_1 hx27_1 hx28_1)

theorem memRegion176_split_88_16_72 (sp' : BitVec 64) :
    memRegion sp' 176 =
      memRegion sp' 88 ∗ memRegion (sp' + 88#64) 16 ∗ memRegion (sp' + 104#64) 72 := by
  have hs1 := memRegion_split sp' 88 88 (by decide)
  have hs2 := memRegion_split (sp' + 88#64) 16 72 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2
  rw [hs1, hs2]

theorem memRegion176_split_104_72 (sp' : BitVec 64) :
    memRegion sp' 176 = memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 := by
  have hs := memRegion_split sp' 104 72 (by decide)
  simp only [Nat.reduceAdd] at hs
  exact hs

theorem memRegion352_of_104_72_112_64 (sp' : BitVec 64) :
    memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
      memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 64 ⊢
      memRegion sp' 352 := by
  have hs1 := memRegion_split sp' 176 176 (by decide)
  have hs2 := memRegion_split (sp' + 176#64) 112 64 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hs1 hs2
  rw [hs1, hs2, memRegion176_split_104_72 sp', sepConj_assoc]
  exact Entails.refl _

theorem memRegion352_of_88_16_72_112_64 (sp' : BitVec 64) :
    memRegion sp' 88 ∗ memRegion (sp' + 88#64) 16 ∗ memRegion (sp' + 104#64) 72 ∗
      memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 64 ⊢
      memRegion sp' 352 := by
  have hs := memRegion_split sp' 88 16 (by decide)
  simp only [Nat.reduceAdd] at hs
  rw [← sepConj_assoc (memRegion sp' 88), ← hs]
  exact memRegion352_of_104_72_112_64 sp'

/-!
# `<SignalMessage>::try_from` Post-Loop Composition (`+0x3b0 .. +0x764`)

Assembles the post-loop validation, `PublicKey::deserialize`, slice boxing/cloning, `SignalMessage`
packing, and error cleanup tails into `tryFrom_post_wp` and its relocatable `[LibsignalPlacement]`
counterpart `tryFrom_post_wp_placed` (Block `85`).
-/

/-- Full post-loop theorem (`+0x3b0..+0x764` → `+0x440`) when `9 < x.bytes.length`
and `3#8 ≤ (x.bytes.headD 0#8) >>> 4 ≤ 4#8`. -/
theorem tryFrom_post_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (ctl : BitVec 64) {abs : String → Option (State → State)}
    (hS : TripleRatchetHooksW img C A S abs)
    (hDropErr : DropDecodeErrorOkW img C A ctl abs)
    (hDropSpe : DropSpeOkW img C A ctl abs)
    (hIntoBox : IntoBoxedSliceOk img C A ctl abs)
    (hTryClone : TryCloneFromRefOk img C A ctl abs)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    {x : TryFromGhost} {s0 s : State}
    (hgt9 : 9 < x.bytes.length)
    (hlt : x.bytes.length < 2 ^ 32)
    (hge3 : ¬ ((x.bytes.headD 0#8) >>> 4) < 3#8)
    (hle4 : ¬ 4#8 < ((x.bytes.headD 0#8) >>> 4))
    (hpc : s.pc = (tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x3b0#64)
    (hrun : s.status = .Running)
    (hst : LoopExitState img s0 (s0.sp - 448#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s) :
    SepWPp (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryFromName + 0x440#64) s
      (memRegion (s0.sp - 448#64) 176 ∗
        memRegion (s0.sp - 448#64 + 288#64) 64 ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100) ∗
        (match decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
         | some m' =>
           ⌜s.readReg64 .x24 = 0#64⌝ ∗ wireSignalMessageOf A (s0.sp - 448#64 + 176#64) m'
         | none =>
           ⌜s.readReg64 .x24 ≠ 0#64⌝ ∗ decodeErrorAt A (s.readReg64 .x24) ∗
             (∃∗ mErr, wireSignalMessageOf A (s0.sp - 448#64 + 176#64) mErr)) ∗
        memRegion x.ret 120 ∗ logOff img)
      (fun sf Pf =>
        PostEpilogueState img s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗
          stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  set out := SignalMessage.tryFrom protoSignalCodec x.bytes
  have hout := tryFrom_eq_of_gt9 hgt9 hge3 hle4
  cases hdec : decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
  | none =>
    have hdec' : LibsignalProtoCodec.decode ((x.bytes.take (x.bytes.length - 8)).drop 1) = none := hdec
    simp only [hdec'] at hout
    rw [memRegion176_split_88_16_72 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun mErr => ?_
    set F_none := memRegion sp' 88 ∗ memRegion (sp' + 104#64) 72 ∗
      memRegion (sp' + 288#64) 64 ∗ (x.bytesA ↦ₛ x.bytes) ∗ logOff img
    refine SepWPp.mono_pre (P' :=
        ⌜s.readReg64 .x24 ≠ 0#64⌝ ∗
        ((wireSignalMessageOf A (sp' + 176#64) mErr ∗
          decodeErrorAt A (s.readReg64 .x24) ∗
          memRegion (sp' + 88#64) 16 ∗
          memRegion x.ret 120 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_none))
      (by dsimp only [F_none]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.pure_pre fun hx24_ne => ?_
    refine SepWPp.frame_tryFrom
      (post_none_wp ctl hS hDropErr hout hst hpc hrun rfl hx24_ne mErr)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_none]
    refine Entails.trans ?_
      (sepConj_mono_left (memRegion352_of_88_16_72_112_64 sp'))
    apply entails_of_eq; ac_rfl
  | some m' =>
    have hdec' : LibsignalProtoCodec.decode ((x.bytes.take (x.bytes.length - 8)).drop 1) = some m' := hdec
    simp only [hdec'] at hout
    cases hrk : m'.ratchetKey with
    | none =>
      simp only [hrk] at hout
      rw [memRegion176_split_88_16_72 sp']
      simp only [sepConj_assoc]
      set F_rk_none := memRegion sp' 88 ∗ memRegion (sp' + 104#64) 72 ∗
        memRegion (sp' + 288#64) 64 ∗ (x.bytesA ↦ₛ x.bytes) ∗ logOff img
      refine SepWPp.mono_pre (P' :=
          ⌜s.readReg64 .x24 = 0#64⌝ ∗
          ((wireSignalMessageOf A (sp' + 176#64) m' ∗
            memRegion (sp' + 88#64) 16 ∗
            memRegion x.ret 120 ∗
            A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_rk_none))
        (by dsimp only [F_rk_none]; apply entails_of_eq; ac_rfl) ?_
      refine SepWPp.pure_pre fun hx24 => ?_
      refine SepWPp.frame_tryFrom
        (post_rk_none_wp ctl hS hrk hout hst hpc hrun hx24)
        fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hent) ?_
      dsimp only [F_rk_none]
      refine Entails.trans ?_
        (sepConj_mono_left (memRegion352_of_88_16_72_112_64 sp'))
      apply entails_of_eq; ac_rfl
    | some rk =>
      simp only [hrk] at hout
      rw [memRegion176_split_104_72 sp']
      simp only [sepConj_assoc]
      refine SepWPp.mono_pre
        (sepConj_mono (memRegion104_0_unpack sp')
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (wireSignalMessageOf_rk_some_entails A sp' hrk))))))))) ?_
      simp only [sepExists_sepConj_left]
      simp only [sepExists_sepConj_right]
      simp only [sepConj_assoc]
      refine SepWPp.exists_pre fun w12 => SepWPp.exists_pre fun w16 =>
        SepWPp.exists_pre fun w28 => SepWPp.exists_pre fun w32 =>
        SepWPp.exists_pre fun w40 => SepWPp.exists_pre fun w48 =>
        SepWPp.exists_pre fun w52 => SepWPp.exists_pre fun w60 =>
        SepWPp.exists_pre fun w64 => SepWPp.exists_pre fun w68 =>
        SepWPp.exists_pre fun w72 => SepWPp.exists_pre fun w80 =>
        SepWPp.exists_pre fun w88 => SepWPp.exists_pre fun w96 =>
        SepWPp.exists_pre fun rkCap => SepWPp.exists_pre fun rkPtr =>
        SepWPp.exists_pre fun ctCap => SepWPp.exists_pre fun ctPtr =>
        SepWPp.exists_pre fun ctLen => SepWPp.exists_pre fun pqCap =>
        SepWPp.exists_pre fun pqPtr => SepWPp.exists_pre fun pqLen =>
        SepWPp.exists_pre fun adCap => SepWPp.exists_pre fun adPtr =>
        SepWPp.exists_pre fun adLen => SepWPp.exists_pre fun cTag =>
        SepWPp.exists_pre fun cVal => SepWPp.exists_pre fun pcTag =>
        SepWPp.exists_pre fun pcVal => ?_
      set F_rk_head := spUnused0 sp' ∗
        ((sp' + 12#64) ↦₃₂ w12) ∗
        ((sp' + 52#64) ↦₃₂ w52) ∗
        ((sp' + 68#64) ↦₃₂ w68) ∗
        memRegion (sp' + 104#64) 72 ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        memRegion x.ret 120 ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        memRegion (sp' + 288#64) 64
      refine SepWPp.mono_pre (P' :=
          ⌜s.readReg64 .x24 = 0#64⌝ ∗
          ⌜optU32TagVal cTag cVal m'.counter⌝ ∗
          ⌜optU32TagVal pcTag pcVal m'.previousCounter⌝ ∗
          ((((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
            ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
            ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
            ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
            ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
            vecHeader (sp' + 176#64) rkCap rkPtr (BitVec.ofNat 64 rk.length) ∗
            vecU8Buf A rkCap rkPtr rk ∗
            vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
            vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
            vecHeader (sp' + 248#64) adCap adPtr adLen ∗
            ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
            ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
            logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_rk_head))
        (by dsimp only [F_rk_head]; apply entails_of_eq; ac_rfl) ?_
      refine SepWPp.pure_pre fun hx24 =>
        SepWPp.pure_pre fun hc => SepWPp.pure_pre fun hpc_tag => ?_
      refine SepWPp.bind_frame_tryFrom
        (post_rk_some_head_wp ctl hDropSpe hb rk hst hpc hrun hx24) ?_
      intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _,
        hx25_1, _, hx27_1, hx28_1, hent1⟩
      dsimp only [F_rk_head]
      set F_tail := memRegion (sp' + 288#64) 64 ∗ logOff img
      refine SepWPp.mono_pre (P' :=
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
            vecU8Buf A rkCap rkPtr rk ∗
            optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
            optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
            optVecU8Buf A adCap adPtr adLen m'.addresses ∗
            memRegion x.ret 120 ∗
            (x.bytesA ↦ₛ x.bytes) ∗
            A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_tail)
        (Entails.trans (sepConj_mono_left hent1) (by dsimp only [F_tail]; apply entails_of_eq; ac_rfl)) ?_
      refine SepWPp.frame_tryFrom
        (post_after_deser_wp ctl hS hDropSpe hIntoBox hTryClone
          x.bytes rk m' hgt9 hlt hdec hc hpc_tag hout
          hst1 hpc1 hrun1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1)
        fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hent) ?_
      dsimp only [F_tail]
      refine Entails.trans ?_
        (sepConj_mono_left (memRegion352_of_104_72_112_64 sp'))
      apply entails_of_eq; ac_rfl

/-! ## Multi-placed `LibsignalPlacement` variants -/

theorem post_after_578_wp_placed [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H)
    {s0 s : State}
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
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x578#64)
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
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
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
        vecU8Buf A rkCap rkPtr rk ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
          memRegion (sp' + 176#64) 112 ∗
          signalMessageResultAt A [] x19 out ∗
          (x21 ↦ₛ bs) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  have h48_pair := (pointsTo32_pair_eq_pointsTo64 (sp' + 48#64) pcTag w52).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48_pair
  cases hct : m'.ciphertext with
  | none =>
    simp only [hct] at hout
    have hct_eq : optVecU8Buf A ctCap ctPtr ctLen none = ⌜ctCap = noneCap⌝ := rfl
    rw [hct_eq]
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono (optVecU8Buf_entails_deallocSlot A pqCap pqPtr pqLen m'.pqRatchet)
                    (sepConj_mono (optVecU8Buf_entails_deallocSlot A adCap adPtr adLen m'.addresses)
                      (sepConj_mono_left (memRegion120_split16 x19)))))))))))))))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 =>
      SepWPp.exists_pre fun adAct => SepWPp.exists_pre fun pqAct => ?_
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
    refine SepWPp.mono_pre (P' := ⌜ctCap = noneCap⌝ ∗
        ((((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
          vecU8Buf A rkCap rkPtr rk ∗
          deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_ct_none))
      (by dsimp only [F_ct_none]; rw [h48_pair]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.pure_pre fun hct_cap => ?_
    subst hct_cap
    refine SepWPp.frame_tryFrom
      (post_ct_none_wp_placed hS rk pqAct adAct hout hst hpc hrun hpstate hx19 hx26 hx25 hx22)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_ct_none]
    have hpack0 := memRegion104_0_pack64 sp' (b8.zeroExtend 32) counter pcVal
      adLen ctLen pqLen (w52 ++ pcTag) w15 rkPtr rkCap adPtr pqPtr
    have hpack104 := memRegion72_104_pack sp' w23 w136 w144 w152 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
    have hpack176 := memRegion112_of_8_40_64 sp' (speWord 2)
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono hpack104 (sepConj_mono_left hpack176)))
    apply entails_of_eq; ac_rfl
  | some ct =>
    simp only [hct] at hout
    have hbnd := msg_bounds_of_decode hgt9 hlt hdec hct
    have hct_eq : optVecU8Buf A ctCap ctPtr ctLen (some ct) =
        ⌜ctLen = BitVec.ofNat 64 ct.length⌝ ∗ vecU8Buf A ctCap ctPtr ct := rfl
    rw [hct_eq]
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (vecU8Buf_cap_lt A ctCap ctPtr ct)))))))))))))))))))))))))))) ?_
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
      vecU8Buf A rkCap rkPtr rk ∗
      memRegion x19 120 ∗
      (x21 ↦ₛ bs)
    refine SepWPp.mono_pre (P' :=
        ⌜ctLen = BitVec.ofNat 64 ct.length⌝ ∗ ⌜ctCap.toNat < 2 ^ 63⌝ ∗
        ((((sp' + 16#64) ↦₆₄ adLen) ∗
          ((sp' + 32#64) ↦₆₄ ctLen) ∗
          ((sp' + 40#64) ↦₆₄ pqLen) ∗
          ((sp' + 48#64) ↦₆₄ (w52 ++ pcTag)) ∗
          ((sp' + 60#64) ↦₃₂ pcVal) ∗
          ((sp' + 88#64) ↦₆₄ adPtr) ∗
          ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          vecHeader (sp' + 136#64) w136 w144 w152 ∗
          ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
          vecU8Buf A ctCap ctPtr ct ∗
          optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
          optVecU8Buf A adCap adPtr adLen m'.addresses ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_boxes))
      (by dsimp only [F_boxes]; rw [h48_pair]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.pure_pre fun hct_len => SepWPp.pure_pre fun hct_lt => ?_
    subst hct_len
    refine SepWPp.bind_frame_tryFrom
      (post_ct_some_boxes_wp_placed hDropSpe hIntoBox ct m'.pqRatchet m'.addresses
        hct_lt hst hpc hrun hpstate hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28) ?_
    intro s2 P2 hpc2 hrun2 ⟨pqCap', pqPtr', ctBoxPtr, adBoxPtr, w96',
      hst2, _, _, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hent2⟩
    dsimp only [F_boxes]
    refine SepWPp.mono_pre (sepConj_mono hent2
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (memRegion120_split16 x19))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
    set msg : SignalMessage :=
      { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey := pk, counter,
        previousCounter := m'.previousCounter.getD 0#32, ciphertext := ct,
        pqRatchet := m'.pqRatchet.getD [], addresses := m'.addresses,
        serialized := bs }
    set F_clone := spUnused0 sp' ∗
      ((sp' + 16#64) ↦₆₄ adLen) ∗
      ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
      ((sp' + 40#64) ↦₆₄ pqLen) ∗
      ((sp' + 88#64) ↦₆₄ adPtr) ∗
      spUnused104 sp' ∗
      vecHeader (sp' + 136#64) ctCap ctPtr (BitVec.ofNat 64 ct.length) ∗
      memRegion (sp' + 176#64) 48 ∗
      memRegion (sp' + 224#64) 64
    refine SepWPp.mono_pre (P' :=
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
          vecU8Buf A rkCap rkPtr rk ∗
          vecU8Buf A pqCap' pqPtr' msg.pqRatchet ∗
          boxU8Buf A ctBoxPtr msg.ciphertext ∗
          optBoxU8Pending A adBoxPtr w96' msg.addresses ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_clone)
      (by dsimp only [F_clone, msg]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (post_clone_and_pack_wp_placed hS hTryClone rk msg hout hbnd hpk rfl
        hst2 hpc2 hrun2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_clone, msg]
    have hpack0 := memRegion104_0_pack64 sp' (b8.zeroExtend 32) counter (m'.previousCounter.getD 0#32)
      adLen (BitVec.ofNat 64 ct.length) pqLen ctBoxPtr w15 rkPtr rkCap adPtr w96'
    have hpack104 := memRegion72_104_pack sp' w23 ctCap ctPtr (BitVec.ofNat 64 ct.length)
      w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
    have hpack176 := memRegion112_of_48_64 sp'
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono hpack104 (sepConj_mono_left hpack176)))
    apply entails_of_eq; ac_rfl

theorem post_after_54c_wp_placed [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H)
    {s0 s : State}
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
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x54c#64)
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
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
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
        vecU8Buf A rkCap rkPtr rk ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
          memRegion (sp' + 176#64) 112 ∗
          signalMessageResultAt A [] x19 out ∗
          (x21 ↦ₛ bs) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  cases hcnt : m'.counter with
  | none =>
    simp only [hcnt] at hout
    rw [hcnt] at hc
    dsimp only [optU32TagVal] at hc
    subst hc
    have h48_pair := (pointsTo32_pair_eq_pointsTo64 (sp' + 48#64) pcTag w52).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48_pair
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono (optVecU8Buf_entails_deallocSlot A ctCap ctPtr ctLen m'.ciphertext)
                    (sepConj_mono (optVecU8Buf_entails_deallocSlot A pqCap pqPtr pqLen m'.pqRatchet)
                      (sepConj_mono (optVecU8Buf_entails_deallocSlot A adCap adPtr adLen m'.addresses)
                        (sepConj_mono_left (memRegion120_split16 x19)))))))))))))))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 =>
      SepWPp.exists_pre fun adAct => SepWPp.exists_pre fun pqAct =>
      SepWPp.exists_pre fun ctAct => ?_
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
    refine SepWPp.mono_pre (P' :=
        (((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
          vecU8Buf A rkCap rkPtr rk ∗
          deallocSlot A ctCap ctPtr ctAct ∗
          deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_cnt_none)
      (by dsimp only [F_cnt_none]; rw [h48_pair]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (post_counter_none_wp_placed hS rk ctAct pqAct adAct hout
        hst hpc hrun hpstate hx19 hx26 hx27 hx28 hx25 hx22)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_cnt_none]
    have hpack0 := memRegion104_0_pack64 sp' w12 cVal pcVal
      adLen ctLen pqLen (w52 ++ pcTag) (w68 ++ 0#32) rkPtr rkCap adPtr pqPtr
    have hpack104 := memRegion72_104_pack sp' w23 w136 w144 w152 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
    have hpack176 := memRegion112_of_8_40_64 sp' (speWord 2)
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono hpack104 (sepConj_mono_left hpack176)))
    apply entails_of_eq; ac_rfl
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
      vecU8Buf A rkCap rkPtr rk ∗
      optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
      optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
      optVecU8Buf A adCap adPtr adLen m'.addresses ∗
      memRegion x19 120 ∗
      (x21 ↦ₛ bs)
    refine SepWPp.mono_pre (P' :=
        (((sp' + 12#64) ↦₃₂ w12) ∗
          ((sp' + 48#64) ↦₃₂ pcTag) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
          ((sp' + 64#64) ↦₆₄ (w68 ++ 1#32)) ∗
          ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_cnt_some)
      (by dsimp only [F_cnt_some]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_tryFrom
      (post_counter_some_head_wp_placed hDropSpe
        hst hpc hrun hpstate hx8 hx9 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hpstate1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hent1⟩
    rw [pcVal_if_eq_getD hpc_tag] at hx8_1
    rw [zext32_zext64_8 b7] at hx24_1
    dsimp only [F_cnt_some]
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    refine SepWPp.mono_pre (by apply entails_of_eq; ac_rfl)
      (post_after_578_wp_placed hS hDropSpe hIntoBox hTryClone
        bs rk m' pk hgt9 hlt hdec hpk hout
        hst1 hpc1 hrun1 hpstate1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
        hx25_1 hx26_1 hx27_1 hx28_1)

theorem post_after_deser_wp_placed [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H)
    {s0 s : State}
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
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x4c4#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs.length)
    (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = adCap)
    (hx23 : s.readReg64 .x23 = (bs.headD 0#8).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap)
    (hx27 : s.readReg64 .x27 = ctCap)
    (hx28 : s.readReg64 .x28 = ctPtr) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
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
        vecU8Buf A rkCap rkPtr rk ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
          memRegion (sp' + 176#64) 112 ∗
          signalMessageResultAt A [] x19 out ∗
          (x21 ↦ₛ bs) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  cases hdeser : PublicKey.deserialize rk with
  | error e =>
    simp only [hdeser] at hout
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (optVecU8Buf_entails_deallocSlot A ctCap ctPtr ctLen m'.ciphertext)
                  (sepConj_mono (optVecU8Buf_entails_deallocSlot A pqCap pqPtr pqLen m'.pqRatchet)
                    (sepConj_mono (optVecU8Buf_entails_deallocSlot A adCap adPtr adLen m'.addresses)
                      (sepConj_mono_left (memRegion120_split24 x19))))))))))))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w1 =>
      SepWPp.exists_pre fun w0 => SepWPp.exists_pre fun adAct =>
      SepWPp.exists_pre fun pqAct => SepWPp.exists_pre fun ctAct => ?_
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
    refine SepWPp.mono_pre (P' :=
        (deserializeResult33At (sp' + 176#64) (.error e) ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ ((x19 + 16#64) ↦₆₄ w2) ∗
          memRegion (x19 + 24#64) 96 ∗
          vecU8Buf A rkCap rkPtr rk ∗
          deallocSlot A ctCap ctPtr ctAct ∗
          deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
          deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_deser_err)
      (by dsimp only [F_deser_err]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (post_deser_err_wp_placed hS rk ctAct pqAct adAct e hdeser hout
        hst hpc hrun hx19 hx27 hx28 hx25 hx22)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_deser_err]
    have hpack0 := memRegion104_0_pack sp' w12 cVal pcTag w52 pcVal cTag w68
      adLen ctLen pqLen rkPtr rkCap adPtr pqPtr
    have hpack176 := memRegion112_of_33_15_64 sp'
    refine Entails.trans ?_
      (sepConj_mono hpack0 (sepConj_mono_right (sepConj_mono_left hpack176)))
    apply entails_of_eq; ac_rfl
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
    refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (memRegion72_104_unpack sp'))))))))))))))))) ?_
    simp only [sepExists_sepConj_left]
    simp only [sepExists_sepConj_right]
    simp only [sepConj_assoc]
    refine SepWPp.exists_pre fun w104 => SepWPp.exists_pre fun b112 =>
      SepWPp.exists_pre fun w120 => SepWPp.exists_pre fun w124 =>
      SepWPp.exists_pre fun c0 => SepWPp.exists_pre fun c1 =>
      SepWPp.exists_pre fun c2 => SepWPp.exists_pre fun c3 =>
      SepWPp.exists_pre fun c4 => SepWPp.exists_pre fun c5 =>
      SepWPp.exists_pre fun c6 => SepWPp.exists_pre fun w136 =>
      SepWPp.exists_pre fun w144 => SepWPp.exists_pre fun w152 => ?_
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
      vecU8Buf A rkCap rkPtr rk ∗
      optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
      optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
      optVecU8Buf A adCap adPtr adLen m'.addresses ∗
      memRegion x19 120 ∗
      (x21 ↦ₛ bs) ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100)
    refine SepWPp.mono_pre (P' :=
        (((sp' + 176#64) ↦₈ 0#8) ∗
          pkLayoutAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
          memRegion (sp' + 209#64) 15 ∗
          ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
          ((sp' + 104#64) ↦₆₄ w104) ∗
          ((sp' + 112#64) ↦₈ b112) ∗
          ((sp' + 120#64) ↦₃₂ w120) ∗ ((sp' + 124#64) ↦₁₆ w124) ∗
          sevenBytesHeadAt (sp' + 128#64) c0 c1 c2 c3 c4 c5 c6) ∗ F_deser_ok)
      (by dsimp only [F_deser_ok]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_tryFrom
      (post_deser_ok_head_wp_placed hst hpc hrun) ?_
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
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    refine SepWPp.mono_pre (by apply entails_of_eq; ac_rfl)
      (post_after_54c_wp_placed hS hDropSpe hIntoBox hTryClone
        bs rk m' pk hgt9 hlt hdec hpk hc hpc_tag hout
        hst1 hpc1 hrun1 hpstate1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
        hx25_1 hx26_1 hx27_1 hx28_1)

theorem tryFrom_post_wp_placed [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H)
    {x : TryFromGhost} {s0 s : State}
    (hgt9 : 9 < x.bytes.length)
    (hlt : x.bytes.length < 2 ^ 32)
    (hge3 : ¬ ((x.bytes.headD 0#8) >>> 4) < 3#8)
    (hle4 : ¬ 4#8 < ((x.bytes.headD 0#8) >>> 4))
    (hpc : s.pc = (blkPl_85).base + 0x3b0#64)
    (hrun : s.status = .Running)
    (hst : LoopExitStatePlaced s0 (s0.sp - 448#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion (s0.sp - 448#64) 176 ∗
        memRegion (s0.sp - 448#64 + 288#64) 64 ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100) ∗
        (match decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
         | some m' =>
           ⌜s.readReg64 .x24 = 0#64⌝ ∗ wireSignalMessageOf A (s0.sp - 448#64 + 176#64) m'
         | none =>
           ⌜s.readReg64 .x24 ≠ 0#64⌝ ∗ decodeErrorAt A (s.readReg64 .x24) ∗
             (∃∗ mErr, wireSignalMessageOf A (s0.sp - 448#64 + 176#64) mErr)) ∗
        memRegion x.ret 120 ∗ logOff tryFromPlacedImg)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool ∗
          stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  set out := SignalMessage.tryFrom protoSignalCodec x.bytes
  have hout := tryFrom_eq_of_gt9 hgt9 hge3 hle4
  cases hdec : decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
  | none =>
    have hdec' : LibsignalProtoCodec.decode ((x.bytes.take (x.bytes.length - 8)).drop 1) = none := hdec
    simp only [hdec'] at hout
    rw [memRegion176_split_88_16_72 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun mErr => ?_
    set F_none := memRegion sp' 88 ∗ memRegion (sp' + 104#64) 72 ∗
      memRegion (sp' + 288#64) 64 ∗ (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg
    refine SepWPp.mono_pre (P' :=
        ⌜s.readReg64 .x24 ≠ 0#64⌝ ∗
        ((wireSignalMessageOf A (sp' + 176#64) mErr ∗
          decodeErrorAt A (s.readReg64 .x24) ∗
          memRegion (sp' + 88#64) 16 ∗
          memRegion x.ret 120 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_none))
      (by dsimp only [F_none]; apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.pure_pre fun hx24_ne => ?_
    refine SepWPp.frame_tryFrom
      (post_none_wp_placed hS hDropErr hout hst hpc hrun rfl hx24_ne mErr)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [F_none]
    refine Entails.trans ?_
      (sepConj_mono_left (memRegion352_of_88_16_72_112_64 sp'))
    apply entails_of_eq; ac_rfl
  | some m' =>
    have hdec' : LibsignalProtoCodec.decode ((x.bytes.take (x.bytes.length - 8)).drop 1) = some m' := hdec
    simp only [hdec'] at hout
    cases hrk : m'.ratchetKey with
    | none =>
      simp only [hrk] at hout
      rw [memRegion176_split_88_16_72 sp']
      simp only [sepConj_assoc]
      set F_rk_none := memRegion sp' 88 ∗ memRegion (sp' + 104#64) 72 ∗
        memRegion (sp' + 288#64) 64 ∗ (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg
      refine SepWPp.mono_pre (P' :=
          ⌜s.readReg64 .x24 = 0#64⌝ ∗
          ((wireSignalMessageOf A (sp' + 176#64) m' ∗
            memRegion (sp' + 88#64) 16 ∗
            memRegion x.ret 120 ∗
            A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_rk_none))
        (by dsimp only [F_rk_none]; apply entails_of_eq; ac_rfl) ?_
      refine SepWPp.pure_pre fun hx24 => ?_
      refine SepWPp.frame_tryFrom
        (post_rk_none_wp_placed hS hrk hout hst hpc hrun hx24)
        fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hent) ?_
      dsimp only [F_rk_none]
      refine Entails.trans ?_
        (sepConj_mono_left (memRegion352_of_88_16_72_112_64 sp'))
      apply entails_of_eq; ac_rfl
    | some rk =>
      simp only [hrk] at hout
      rw [memRegion176_split_104_72 sp']
      simp only [sepConj_assoc]
      refine SepWPp.mono_pre
        (sepConj_mono (memRegion104_0_unpack sp')
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (wireSignalMessageOf_rk_some_entails A sp' hrk))))))))) ?_
      simp only [sepExists_sepConj_left]
      simp only [sepExists_sepConj_right]
      simp only [sepConj_assoc]
      refine SepWPp.exists_pre fun w12 => SepWPp.exists_pre fun w16 =>
        SepWPp.exists_pre fun w28 => SepWPp.exists_pre fun w32 =>
        SepWPp.exists_pre fun w40 => SepWPp.exists_pre fun w48 =>
        SepWPp.exists_pre fun w52 => SepWPp.exists_pre fun w60 =>
        SepWPp.exists_pre fun w64 => SepWPp.exists_pre fun w68 =>
        SepWPp.exists_pre fun w72 => SepWPp.exists_pre fun w80 =>
        SepWPp.exists_pre fun w88 => SepWPp.exists_pre fun w96 =>
        SepWPp.exists_pre fun rkCap => SepWPp.exists_pre fun rkPtr =>
        SepWPp.exists_pre fun ctCap => SepWPp.exists_pre fun ctPtr =>
        SepWPp.exists_pre fun ctLen => SepWPp.exists_pre fun pqCap =>
        SepWPp.exists_pre fun pqPtr => SepWPp.exists_pre fun pqLen =>
        SepWPp.exists_pre fun adCap => SepWPp.exists_pre fun adPtr =>
        SepWPp.exists_pre fun adLen => SepWPp.exists_pre fun cTag =>
        SepWPp.exists_pre fun cVal => SepWPp.exists_pre fun pcTag =>
        SepWPp.exists_pre fun pcVal => ?_
      set F_rk_head := spUnused0 sp' ∗
        ((sp' + 12#64) ↦₃₂ w12) ∗
        ((sp' + 52#64) ↦₃₂ w52) ∗
        ((sp' + 68#64) ↦₃₂ w68) ∗
        memRegion (sp' + 104#64) 72 ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        memRegion x.ret 120 ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        memRegion (sp' + 288#64) 64
      refine SepWPp.mono_pre (P' :=
          ⌜s.readReg64 .x24 = 0#64⌝ ∗
          ⌜optU32TagVal cTag cVal m'.counter⌝ ∗
          ⌜optU32TagVal pcTag pcVal m'.previousCounter⌝ ∗
          ((((sp' + 16#64) ↦₆₄ w16) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
            ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
            ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₃₂ w64) ∗
            ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
            ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
            vecHeader (sp' + 176#64) rkCap rkPtr (BitVec.ofNat 64 rk.length) ∗
            vecU8Buf A rkCap rkPtr rk ∗
            vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
            vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
            vecHeader (sp' + 248#64) adCap adPtr adLen ∗
            ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
            ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) ∗
            logOff tryFromPlacedImg ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_rk_head))
        (by dsimp only [F_rk_head]; apply entails_of_eq; ac_rfl) ?_
      refine SepWPp.pure_pre fun hx24 =>
        SepWPp.pure_pre fun hc => SepWPp.pure_pre fun hpc_tag => ?_
      refine SepWPp.bind_frame_tryFrom
        (post_rk_some_head_wp_placed hDropSpe rk hst hpc hrun hx24) ?_
      intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _,
        hx25_1, _, hx27_1, hx28_1, hent1⟩
      dsimp only [F_rk_head]
      set F_tail := memRegion (sp' + 288#64) 64 ∗ logOff tryFromPlacedImg
      refine SepWPp.mono_pre (P' :=
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
            vecU8Buf A rkCap rkPtr rk ∗
            optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
            optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
            optVecU8Buf A adCap adPtr adLen m'.addresses ∗
            memRegion x.ret 120 ∗
            (x.bytesA ↦ₛ x.bytes) ∗
            A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_tail)
        (Entails.trans (sepConj_mono_left hent1) (by dsimp only [F_tail]; apply entails_of_eq; ac_rfl)) ?_
      refine SepWPp.frame_tryFrom
        (post_after_deser_wp_placed hS hDropSpe hIntoBox hTryClone
          x.bytes rk m' hgt9 hlt hdec hc hpc_tag hout
          hst1 hpc1 hrun1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1)
        fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hent) ?_
      dsimp only [F_tail]
      refine Entails.trans ?_
        (sepConj_mono_left (memRegion352_of_104_72_112_64 sp'))
      apply entails_of_eq; ac_rfl

end CryptoVerification.LibsignalTripleRatchet.Wire


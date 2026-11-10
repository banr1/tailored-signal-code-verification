/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWKyber
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bKyberPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCWPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# Relocatable `[LibsignalPlacement]` Kyber Dispatch Error Continuation (`PreKeyKyberErrWPlaced`)

Proves `preKeyKyberErrW_placed_proof` (`+0x684 → +0xa24 → +0x504 → ret`) on
`preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Kyber `Err` composition (`+0x684 → +0xa24`, `1668 → 2596`) under `[LibsignalPlacement]`
preserving the stack scratch regions `((sp' + 68) ↦₃₂ kpkTag)`, `memRegion (sp' + 112) 32`, and
`memRegion (sp' + 312) 48` for the epilogue stack fold while keeping the allocated `String` inside
`pksmErrE` (`speAt`). -/
theorem w8bKyberErr_684_to_a24_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : CodecHooksPlaced A H) (hC : PksmCalleesPlaced A H)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8}
    {kpkTag kpkVal : BitVec 32}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hkpk : w8bOptU32Cells kpkOpt (kpkTag, kpkVal))
    (herr : (kpkOpt.isSome != kyberOpt.isSome) = true ∨
      (kpkOpt = none ∧ kyberOpt = none ∧ 0x40 ≤ vb.toNat))
    (hst : BaseKeyOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk s)
    (hpc : s.pc = (blkPl_111).base + 1668#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2596#64) s
      ((((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
          ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15) ∗
        (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        KyberExitA24StatePlaced s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
        (Pf ⊢ (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          ((sp' + 68#64) ↦₃₂ kpkTag) ∗
          memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hst_ep, _, _, hpk_bytes,
    hx29, hx28, hx27, hx26, hx25, _, hx23, hx22, hx21, hx20, hx19⟩
  have hlen32 : ((bk.take 33).drop 1).length = 32 := by
    rw [← hpk_bytes]; exact (pkOf bk).bytes.toList_length
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, w9, w13, w15, w23, b31, hpk_of⟩ :=
    exists_pkBytesOf ((bk.take 33).drop 1) hlen32
  refine Wire.SepWPp.bind_frame_tryFrom
    (pk_scatter_head_placed_wp hpk_of hst_ep hpc hrun hx29 hx28 hx27 hx26 hx25 hx23 hx22 hx21 hx20 hx19) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hpstate1, _, _, _,
    hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, _, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
  have hm112 := memRegion32_112_pack sp' w23 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
  refine SepWPp.mono_pre (P' :=
      (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      (((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 312#64) 48))
    (by
      refine Entails.trans (sepConj_mono_left hent1) ?_
      refine Entails.trans (Q :=
        (spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6) ∗
        (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
        (((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 312#64) 48))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono_left hm112) ?_
      apply entails_of_eq; ac_rfl) ?_
  rcases herr with hhalf | ⟨rfl, rfl, hvb_ge⟩
  · have htag : kpkTag = if kpkOpt.isSome then 1#32 else 0#32 := by
      cases kpkOpt with
      | some _ => exact hkpk.1
      | none => exact hkpk
    refine SepWPp.frame_tryFrom
      (kyber_half_err_placed_wpE hH hC htag hhalf hst1 hpc1 hrun1 hpstate1
        hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; ac_rfl
  · have hkpk0 : kpkTag = 0#32 := hkpk
    subst hkpk0
    refine SepWPp.frame_tryFrom
      (kyber_neither_v4_err_placed_wpE hH hvb_ge hst1 hpc1 hrun1 hpstate1
        hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; ac_rfl

/-- Frame carried across `w8bKyberErr_684_to_a24_placed_wpE` (`+0x684 → +0xa24`). -/
def w8bKyberErr684FramePlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (bk ik msg bytes : List (BitVec 8)) : SepProp :=
  ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
    Wire.vecU8Buf A bkCap bkPtr bk ∗ lsLogOff ∗
    ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
    ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 56#64) ↦₆₄ BitVec.ofNat 64 ik.length) ∗ memRegion (sp' + 64#64) 4 ∗
    ((sp' + 88#64) ↦₆₄ bkCap) ∗
    ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
    memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
    memRegion sp' 16 ∗ memRegion (sp' + 144#64) 152 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ (ptr ↦ₛ bytes) ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

/-- Frame `R` carried across `ErrTailCWPlaced.tail_a24_placed_wpX` (`+0xa24 → +0x504`). -/
def w8bKyberErrA24RestPlaced [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkLen msgLen kyberLen ikLen : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32)
    (bytes : List (BitVec 8)) : SepProp :=
  (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
    ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
    ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkId) ∗
    ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
    ((sp' + 68#64) ↦₃₂ kpkTag) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗
    memRegion sp' 16 ∗ memRegion (sp' + 112#64) 184 ∗
    memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ (ptr ↦ₛ bytes) ∗ lsLogOff ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

/-- Regroups `w8bRowKPostPlaced ∗ w8bRowKFrame` into the `w8bKyberErr_684_to_a24_placed_wpE`
precondition ∗ `w8bKyberErr684FramePlaced`. -/
theorem w8bRowK_open_kyberErr_placed [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberCap kyberPtr kyberLen ikCap ikPtr msgCap msgPtr : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) (bk ik msg bytes : List (BitVec 8)) :
    w8bRowKPostPlaced A sp' bkCap bkPtr bk ∗
      w8bRowKFrame A s0 sp' sret ptr bkCap kyberCap kyberPtr kyberLen
        ikCap ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal
        kyberOpt ik msg bytes =
    (((((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
          ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15) ∗
        (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))) ∗
      w8bKyberErr684FramePlaced A s0 sp' ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
        regTag regVal opkTag opkVal spkId kpkVal bk ik msg bytes) := by
  unfold w8bRowKPostPlaced w8bRowKFrame w8bKyberErr684FramePlaced
  rw [w8b_memRegion184_split sp']
  ac_rfl

/-- Regroups the `w8bKyberErr_684_to_a24_placed_wpE` post ∗ `w8bKyberErr684FramePlaced` into the
existential `tail_a24_placed_wpX` precondition with `R := w8bKyberErrA24RestPlaced ...`. -/
theorem w8bKyberErr_open_a24_placed [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32)
    (bk ik msg bytes : List (BitVec 8)) :
    ((pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
        ((sp' + 68#64) ↦₃₂ kpkTag) ∗
        memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      w8bKyberErr684FramePlaced A s0 sp' ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
        regTag regVal opkTag opkVal spkId kpkVal bk ik msg bytes ⊢
    ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool,
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        w8bKyberErrA24RestPlaced A s0 sp' sret ptr (BitVec.ofNat 64 bk.length)
          (BitVec.ofNat 64 msg.length) kyberLen (BitVec.ofNat 64 ik.length)
          regTag regVal opkTag opkVal spkId kpkTag kpkVal bytes := by
  unfold w8bKyberErr684FramePlaced w8bKyberErrA24RestPlaced
  have hvec (cap ptr0 : BitVec 64) (bs : List (BitVec 8)) :
      Wire.vecU8Buf A cap ptr0 bs ⊢ ∃∗ active : Bool, deallocSlot A cap ptr0 active := by
    refine Entails.trans ?_
      (optVecU8Buf_entails_deallocSlot A cap ptr0 (BitVec.ofNat 64 bs.length) (some bs))
    dsimp only [optVecU8Buf]
    rw [pure_true_emp rfl, emp_sepConj]
    exact Entails.refl _
  have hmsg := hvec msgCap msgPtr msg
  have hik := hvec ikCap ikPtr ik
  have hbk := hvec bkCap bkPtr bk
  rw [w8b_memRegion184_split sp', w8bKyberErr_memRegion152_split48 sp']
  refine Entails.trans
    (Q := Wire.vecU8Buf A msgCap msgPtr msg ∗
      Wire.vecU8Buf A ikCap ikPtr ik ∗
      Wire.vecU8Buf A bkCap bkPtr bk ∗ _)
    (by sep_frame) ?_
  refine Entails.trans
    (sepConj_mono hmsg (sepConj_mono hik (sepConj_mono_left hbk))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bkAct =>
    Entails.sepExists_elim fun ikAct =>
    Entails.sepExists_elim fun msgAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  apply entails_of_eq; ac_rfl

/-- Final Kyber Err regroup at `+0x504` (`1284`): the `tail_a24_placed_wpX` post frame (with
`R := w8bKyberErrA24RestPlaced ...`) entails the `w8b_errTail_close_placed` precondition
(residue `anyHeap`). -/
theorem w8bKyberErr_placed_pack [LibsignalPlacement] {A : RustAlloc} {s0 : State}
    {sp' sret ptr bkLen msgLen kyberLen ikLen msgPtr ikPtr bkPtr bkCap : BitVec 64}
    {regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32}
    {bytes : List (BitVec 8)} :
    ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      w8bKyberErrA24RestPlaced A s0 sp' sret ptr bkLen msgLen kyberLen ikLen
        regTag regVal opkTag opkVal spkId kpkTag kpkVal bytes ⊢
    pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap ∗
      stackAt sp' preKeyTryFromSubStack ∗
      memRegion sp' 296 ∗
      memRegion (sp' + 296#64) 152 ∗
      memRegion (sp' + 448#64) 64 ∗
      preKeyCalleeSavedAt sp' s0 ∗
      (ptr ↦ₛ bytes) ∗ lsLogOff ∗ A.pool := by
  unfold w8bKyberErrA24RestPlaced
  have hm96 := w8bSeg1Cells_entails_memRegion96 sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen
    msgPtr msgLen regTag regVal opkTag opkVal spkId kpkTag kpkVal
  rw [stackAt_preKeyTryFromSubStack_skipField sp', w8bMemRegion296_split_16_96 sp']
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hm96))))))
  apply entails_of_eq; ac_rfl

/-- `PreKeyKyberErrWPlaced` from `w8bKyberErr_684_to_a24_placed_wpE`, `tail_a24_placed_wpX`, and
`w8b_errTail_close_placed`. -/
theorem preKeyKyberErrW_placed_proof [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : CodecHooksPlaced A H) (hC : PksmCalleesPlaced A H) :
    PreKeyKyberErrWPlaced A H := by
  intro x s0 sf vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
    kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hcons _hv3 _hv4 _hlen hdec _hbkO
    _hikO _hmsgO _hspkO _hreg _hopk hkpk _hd herrY hst hbkC hikC hmsgC hpc hrun
  have hparse : Pksm.pksmParse x.bytes = none :=
    hcons ▸ pksmParse_eq_none_of_w5b_kyber_err hdec herrY
  have hbkNe : bkCap ≠ noneCap := by rintro rfl; revert hbkC; decide
  have hikNe : ikCap ≠ noneCap := by rintro rfl; revert hikC; decide
  have hmsgNe : msgCap ≠ noneCap := by rintro rfl; revert hmsgC; decide
  rw [w8bRowK_open_kyberErr_placed]
  refine Wire.SepWPp.bind_frame_tryFrom
    (w8bKyberErr_684_to_a24_placed_wpE hH hC hkpk herrY hst hpc hrun) ?_
  rintro sm1 Pm1 hpc1 hrun1 ⟨⟨hst1, _hx29_1, hx26_1, hx23_1, _hx22_1, _hx21_1, _hx20_1, hx19_1⟩,
    hPm1⟩
  refine SepWPp.mono_pre (Entails.trans (sepConj_mono_left hPm1) (w8bKyberErr_open_a24_placed ..)) ?_
  refine SepWPp.exists_pre fun msgAct => SepWPp.exists_pre fun ikAct =>
    SepWPp.exists_pre fun bkAct => ?_
  refine SepWPp.bind
    (tail_a24_placed_wpX hC msgAct ikAct bkAct hst1 hpc1 hrun1 hx19_1 hx26_1 hx23_1 hmsgNe hikNe hbkNe) ?_
  rintro sm2 Pm2 hpc2 hrun2 ⟨hst2, _, hPm2⟩
  exact SepWPp.mono_pre (Entails.trans hPm2 w8bKyberErr_placed_pack)
    (w8b_errTail_close_placed hparse hst2 hpc2 hrun2)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

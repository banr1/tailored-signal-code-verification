/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bKyber
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailC
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberb
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberc
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWShared
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: Kyber Dispatch Error Continuation (`PreKeyKyberErrW`)

Proves `preKeyKyberErrW_proof` (`+0x684 → +0xa24 → +0x504 → ret`) from `pk_scatter_head_wp`,
`kyber_half_err_wpE` / `kyber_neither_v4_err_wpE`, `ErrTailC.tail_a24_wpX`, and
`w8b_errTail_close`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
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

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

theorem w8bKyberErr_memRegion152_split48 (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 152 =
      memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 312#64) 48 ∗
        memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
        memRegion (sp' + 440#64) 8 := by
  rw [show (152 : Nat) = 16 + (48 + (72 + (8 + 8))) by decide,
    Prost.memRegion_split (sp' + 296#64) 16 136 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 16#64) 48 88 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 16#64 + 48#64) 72 16 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 16#64 + 48#64 + 72#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Kyber `Err` composition (`+0x684 → +0xa24`, `1668 → 2596`) preserving the stack scratch
regions `((sp' + 68) ↦₃₂ kpkTag)`, `memRegion (sp' + 112) 32`, and `memRegion (sp' + 312) 48` for the
epilogue stack fold while keeping the allocated `String` inside `pksmErrE` (`speAt`). -/
theorem w8bKyberErr_684_to_a24_wpE {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8}
    {kpkTag kpkVal : BitVec 32}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hkpk : w8bOptU32Cells kpkOpt (kpkTag, kpkVal))
    (herr : (kpkOpt.isSome != kyberOpt.isSome) = true ∨
      (kpkOpt = none ∧ kyberOpt = none ∧ 0x40 ≤ vb.toNat))
    (hst : BaseKeyOkState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1668#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 2596#64) s
      ((((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
          ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15) ∗
        (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        KyberExitA24State img s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
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
  refine SepWPp.bind_frame_tryFrom
    (pk_scatter_head_wp hpk_of hst_ep hpc hrun hx29 hx28 hx27 hx26 hx25 hx23 hx22 hx21 hx20 hx19) ?_
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
      (kyber_half_err_wpE himg hA htag hhalf hst1 hpc1 hrun1 hpstate1
        hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; ac_rfl
  · have hkpk0 : kpkTag = 0#32 := hkpk
    subst hkpk0
    refine SepWPp.frame_tryFrom
      (kyber_neither_v4_err_wpE himg hA hvb_ge hst1 hpc1 hrun1 hpstate1
        hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; ac_rfl

/-- Frame carried across `w8bKyberErr_684_to_a24_wpE` (`+0x684 → +0xa24`). -/
def w8bKyberErr684Frame (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkVal : BitVec 32)
    (bk ik msg bytes : List (BitVec 8)) : SepProp :=
  ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
    Wire.vecU8Buf A bkCap bkPtr bk ∗ logOff img ∗
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

/-- Frame `R` carried across `ErrTailC.tail_a24_wpX` (`+0xa24 → +0x504`). -/
def w8bKyberErrA24Rest (img : Obj.Image) (A : RustAlloc) (s0 : State)
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
    preKeyCalleeSavedAt sp' s0 ∗ (ptr ↦ₛ bytes) ∗ logOff img ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

/-- Regroups `w8bRowKPost ∗ w8bRowKFrame` into the `w8bKyberErr_684_to_a24_wpE` precondition ∗
`w8bKyberErr684Frame`. -/
theorem w8bRowK_open_kyberErr (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberCap kyberPtr kyberLen ikCap ikPtr msgCap msgPtr : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) (bk ik msg bytes : List (BitVec 8)) :
    w8bRowKPost img A sp' bkCap bkPtr bk ∗
      w8bRowKFrame A s0 sp' sret ptr bkCap kyberCap kyberPtr kyberLen
        ikCap ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal
        kyberOpt ik msg bytes =
    (((((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
          ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15) ∗
        (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))) ∗
      w8bKyberErr684Frame img A s0 sp' ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
        regTag regVal opkTag opkVal spkId kpkVal bk ik msg bytes) := by
  unfold w8bRowKPost w8bRowKFrame w8bKyberErr684Frame
  rw [w8b_memRegion184_split sp']
  ac_rfl

/-- Regroups the `w8bKyberErr_684_to_a24_wpE` post ∗ `w8bKyberErr684Frame` into the existential
`tail_a24_wpX` precondition with `R := w8bKyberErrA24Rest ...`. -/
theorem w8bKyberErr_open_a24 (img : Obj.Image) (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr : BitVec 64)
    (regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32)
    (bk ik msg bytes : List (BitVec 8)) :
    ((pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
        ((sp' + 68#64) ↦₃₂ kpkTag) ∗
        memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      w8bKyberErr684Frame img A s0 sp' ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
        regTag regVal opkTag opkVal spkId kpkVal bk ik msg bytes ⊢
    ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool,
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A bkCap bkPtr bkAct ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        w8bKyberErrA24Rest img A s0 sp' sret ptr (BitVec.ofNat 64 bk.length)
          (BitVec.ofNat 64 msg.length) kyberLen (BitVec.ofNat 64 ik.length)
          regTag regVal opkTag opkVal spkId kpkTag kpkVal bytes := by
  unfold w8bKyberErr684Frame w8bKyberErrA24Rest
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

/-- Final Kyber Err regroup at `+0x504` (`1284`): the `tail_a24_wpX` post frame (with
`R := w8bKyberErrA24Rest ...`) entails the `w8b_errTail_close` precondition (residue `anyHeap`). -/
theorem w8bKyberErr_pack {img : Obj.Image} {A : RustAlloc} {s0 : State}
    {sp' sret ptr bkLen msgLen kyberLen ikLen msgPtr ikPtr bkPtr bkCap : BitVec 64}
    {regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32}
    {bytes : List (BitVec 8)} :
    ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      w8bKyberErrA24Rest img A s0 sp' sret ptr bkLen msgLen kyberLen ikLen
        regTag regVal opkTag opkVal spkId kpkTag kpkVal bytes ⊢
    pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap ∗
      stackAt sp' preKeyTryFromSubStack ∗
      memRegion sp' 296 ∗
      memRegion (sp' + 296#64) 152 ∗
      memRegion (sp' + 448#64) 64 ∗
      preKeyCalleeSavedAt sp' s0 ∗
      (ptr ↦ₛ bytes) ∗ logOff img ∗ A.pool := by
  unfold w8bKyberErrA24Rest
  have hm96 := w8bSeg1Cells_entails_memRegion96 sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen
    msgPtr msgLen regTag regVal opkTag opkVal spkId kpkTag kpkVal
  rw [stackAt_preKeyTryFromSubStack_skipField sp', w8bMemRegion296_split_16_96 sp']
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hm96))))))
  apply entails_of_eq; ac_rfl

/-- `PreKeyKyberErrW` from `w8bKyberErr_684_to_a24_wpE`, `tail_a24_wpX`, and `w8b_errTail_close`. -/
theorem preKeyKyberErrW_proof {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    (hC : PksmCallees img A ext) :
    PreKeyKyberErrW img A ext := by
  intro x s0 sf vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
    kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hcons _hv3 _hv4 _hlen hdec _hbkO
    _hikO _hmsgO _hspkO _hreg _hopk hkpk _hd herrY hst hbkC hikC hmsgC hpc hrun
  have hparse : Pksm.pksmParse x.bytes = none :=
    hcons ▸ pksmParse_eq_none_of_w5b_kyber_err hdec herrY
  have hbkNe : bkCap ≠ noneCap := by rintro rfl; revert hbkC; decide
  have hikNe : ikCap ≠ noneCap := by rintro rfl; revert hikC; decide
  have hmsgNe : msgCap ≠ noneCap := by rintro rfl; revert hmsgC; decide
  rw [w8bRowK_open_kyberErr]
  refine SepWPp.bind_frame_tryFrom
    (w8bKyberErr_684_to_a24_wpE himg hA hkpk herrY hst hpc hrun) ?_
  rintro sm1 Pm1 hpc1 hrun1 ⟨⟨hst1, _hx29_1, hx26_1, hx23_1, _hx22_1, _hx21_1, _hx20_1, hx19_1⟩,
    hPm1⟩
  refine SepWPp.mono_pre (Entails.trans (sepConj_mono_left hPm1) (w8bKyberErr_open_a24 ..)) ?_
  refine SepWPp.exists_pre fun msgAct => SepWPp.exists_pre fun ikAct =>
    SepWPp.exists_pre fun bkAct => ?_
  refine SepWPp.bind
    (tail_a24_wpX hC msgAct ikAct bkAct hst1 hpc1 hrun1 hx19_1 hx26_1 hx23_1 hmsgNe hikNe hbkNe) ?_
  rintro sm2 Pm2 hpc2 hrun2 ⟨hst2, _, hPm2⟩
  exact SepWPp.mono_pre (Entails.trans hPm2 w8bKyberErr_pack)
    (w8b_errTail_close hparse hst2 hpc2 hrun2)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

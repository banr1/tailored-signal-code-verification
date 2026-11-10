/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bPack
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bSigMsgPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.PackWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailWPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` `+0x8c0` `Ok` Packing, Deallocation, and Epilogue (`PreKey8c0OkWPlaced`)

Proves `preKey8c0OkW_placed_proof` (`+0x8c0 → +0x970 → +0x504 → ret`) on
`preKeyPlacedProg H` against `(pksmTryFromSpecPlaced A).post`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

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

/-! ## 1. The Untouched Residue (`[LibsignalPlacement]`) -/

/-- The part of `w8bRowSPost ∗ w8bRowSFramePlaced` at `+0x8c0` that `PackWPlaced`
does not read or write: passed as Pack's `frame`, refolded for the epilogue. -/
def w8bPackJunkPlaced [LibsignalPlacement] (s0 : State) (sp' ptr : BitVec 64)
    (regTag regVal : BitVec 32) (ik msg bytes : List (BitVec 8)) (kyberLen : BitVec 64) :
    SepProp :=
  ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
    ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 (BitVec.ofNat 64 ik.length)) ∗
    ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
    memRegion (sp' + 64#64) 4 ∗ spUnused112 sp' ∗
    lsLogOff ∗
    memRegion sp' 12 ∗ memRegion (sp' + 288#64) 8 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 312#64) 120 ∗ memRegion (sp' + 432#64) 8 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100) ∗
    (ptr ↦ₛ bytes)

/-! ## 2. Regrouping (`[LibsignalPlacement]`) -/

/-- `+0x8c0` state → Pack's pre (`R_heap := emp`, `frame := w8bPackJunkPlaced`,
`stackSz := Prost.skipFieldStackX 100`), with the three `Vec<u8>` slots opened to `deallocSlot`s. -/
theorem w8bPack_pre_open_placed [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen
      serBoxPtr : BitVec 64)
    (regTag regVal opkTag opkVal sid kpkVal regId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8) (body : List (BitVec 8))
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) (ipk : PublicKey)
    (innerMsg : SignalMessage) (msgG : SignalMessageGhost)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56)
    (ik0 ik1 ik2 ik3 : BitVec 64)
    (hb : bytes = vb :: body)
    (hreg : identRegId regTag regVal = regId)
    (hipk : ∀ a : BitVec 64, (a ↦ₛ ipk.bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3)) :
    w8bRowSPost A sp' serBoxPtr bytes innerMsg msgG rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 ∗
      w8bRowSFramePlaced A s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
        kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal sid kpkVal
        b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23 vb kpkOpt kyberOpt bk ik msg bytes ipk ⊢
    ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool,
      (((memRegion sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗
        ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ sid) ∗
        ((sp' + 56#64) ↦₃₂ regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion))) ∗
        (msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
          boxU8Buf A serBoxPtr (vb :: body) ∗
          kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ∗
          emp)) ∗
        (⌜msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap⌝ ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A msgCap msgPtr msgAct ∗
          deallocSlot A ikCap ikPtr ikAct ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          w8bPackJunkPlaced s0 sp' ptr regTag regVal ik msg bytes kyberLen)) := by
  subst hb hreg
  unfold w8bRowSPost w8bRowSFramePlaced w8bRowSRestPlaced w8bPackJunkPlaced
  rw [hipk (sp' + 144#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hik := Entails.trans (slice_rest_to_vecU8Buf A ikCap ikPtr ik)
    (vecU8Buf_entails_deallocSlot A ikCap ikPtr ik)
  have hbk := vecU8Buf_entails_deallocSlot A bkCap bkPtr bk
  have hmsg := vecU8Buf_entails_deallocSlot A msgCap msgPtr msg
  refine Entails.trans (Q := ((ikPtr ↦ₛ ik) ∗ vecU8Rest A ikCap ikPtr ik) ∗
      Wire.vecU8Buf A bkCap bkPtr bk ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗ _)
    (by sep_frame) ?_
  refine Entails.trans (sepConj_mono hik (sepConj_mono hbk (sepConj_mono_left hmsg))) ?_
  refine w8bPack_open3 fun ikAct bkAct msgAct hik_ne hbk_ne hmsg_ne => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  rw [pure_sepConj_of_true (φ := msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap)
    ⟨hmsg_ne, hik_ne, hbk_ne⟩, sepConj_emp]
  apply entails_of_eq; ac_rfl

/-- After `deallocChain_970_placed_wpX`: its `ErrTailQPlaced` frame, plus the Pack residue (`Q_res`,
the spill cells, `memRegion (sp' + 176) 112`, `w8bPackJunkPlaced`), regroups to
`epilogue_504_placed_w_wpX`'s pre. -/
theorem w8bPack_epi_regroup_placed [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (ptr bkCap bkPtr msgPtr ikPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal sid kpkVal regId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 ik0 ik1 ik2 ik3 : BitVec 64) (ik msg bytes : List (BitVec 8))
    (Q_res : SepProp) :
    (((s0.sp - 608#64 + 96#64) ↦₆₄ msgPtr) ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ ikPtr) ∗
        ((s0.sp - 608#64 + 80#64) ↦₆₄ bkPtr) ∗ ((s0.sp - 608#64 + 88#64) ↦₆₄ bkCap) ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100) ∗
        (Q_res ∗
          ((s0.sp - 608#64 + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((s0.sp - 608#64 + 16#64) ↦₃₂ kpkVal) ∗
          ((s0.sp - 608#64 + 20#64) ↦₃₂ opkTag) ∗
          ((s0.sp - 608#64 + 24#64) ↦₃₂ opkVal) ∗
          ((s0.sp - 608#64 + 28#64) ↦₃₂ sid) ∗
          ((s0.sp - 608#64 + 56#64) ↦₃₂ regId) ∗
          ((s0.sp - 608#64 + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((s0.sp - 608#64 + 72#64) ↦₆₄ w15) ∗
          ((s0.sp - 608#64 + 112#64) ↦₆₄ w23) ∗ ((s0.sp - 608#64 + 120#64) ↦₈ b31) ∗
          ((s0.sp - 608#64 + 128#64) ↦₃₂ w9) ∗ ((s0.sp - 608#64 + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (s0.sp - 608#64 + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((s0.sp - 608#64 + 144#64) ↦₆₄ ik0) ∗ ((s0.sp - 608#64 + 152#64) ↦₆₄ ik1) ∗
          ((s0.sp - 608#64 + 160#64) ↦₆₄ ik2) ∗ ((s0.sp - 608#64 + 168#64) ↦₆₄ ik3) ∗
          memRegion (s0.sp - 608#64 + 176#64) 112 ∗
          w8bPackJunkPlaced s0 (s0.sp - 608#64) ptr regTag regVal ik msg bytes kyberLen)) ⊢
      stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        Q_res ∗ (ptr ↦ₛ bytes) ∗ lsLogOff ∗ A.pool := by
  generalize s0.sp - 608#64 = sp'
  unfold w8bPackJunkPlaced
  have hm12 := pointsTo32_entails_memRegion (sp' + 12#64) (b7.zeroExtend 32)
  have hm96 := w8b_spills96_entails_memRegion sp' kpkVal opkTag opkVal sid regTag regVal regId
    (BitVec.extractLsb' 32 32 (BitVec.ofNat 64 ik.length)) (b8.zeroExtend 32)
    (BitVec.ofNat 64 msg.length) kyberLen w15 bkPtr bkCap msgPtr ikPtr
  have hm112 := memRegion32_112_pack sp' w23 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
  have hm144 :
      ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
      ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ⊢
        memRegion (sp' + 144#64) 32 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words4_entails_memRegion32 (sp' + 144#64) ik0 ik1 ik2 ik3
  have h152 : memRegion (sp' + 296#64) 152 =
      memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 312#64) 120 ∗
        memRegion (sp' + 432#64) 8 ∗ memRegion (sp' + 440#64) 8 := by
    rw [show (152 : Nat) = 16 + (120 + (8 + 8)) by decide,
      Prost.memRegion_split (sp' + 296#64) 16 136 (by decide),
      Prost.memRegion_split (sp' + 296#64 + 16#64) 120 16 (by decide),
      Prost.memRegion_split (sp' + 296#64 + 16#64 + 120#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [stackAt_sub_split sp' (Prost.skipFieldStackX 100) preKeyTryFromSubStack (by decide) (by decide),
    w8b_memRegion296_full_split sp', h152]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono hm12 (sepConj_mono hm96
        (sepConj_mono hm112 (sepConj_mono_left hm144)))))))
  simp only [sepConj_assoc]
  apply entails_of_eq; ac_rfl

/-! ## 3. Post (`[LibsignalPlacement]`) -/

/-- The Ok epilogue post (`sp`, callee-saved, `LibsignalCodeRoLoaded`, trace, `RunCompose.pksmResAt`)
meets `(pksmTryFromSpecPlaced A).post` (Ok twin of `W8bAssemblyPlaced.w8b_errPost_placed`). -/
theorem w8bPack_okPost_placed [LibsignalPlacement] {A : RustAlloc}
    {x : RunCompose.PksmGhost} {s0 sf : State}
    {Pf : SepProp}
    (h : sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
      (Pf ⊢ RunCompose.pksmResAt A x.ret (Pksm.pksmParse x.bytes) ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗
        stackAt s0.sp preKeyTryFromStack)) :
    sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ (pksmTryFromSpecPlaced A).post x s0 sf) := by
  obtain ⟨hsp, hcs, _hcl, htr, hent⟩ := h
  refine ⟨hsp, hcs, Entails.trans hent ?_⟩
  dsimp only [pksmTryFromSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  rw [pure_sepConj_of_true htr]
  change RunCompose.pksmResAt A x.ret (Pksm.pksmParse x.bytes) ∗
      (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool ∗ stackAt s0.sp preKeyTryFromStack ⊢
    RunCompose.pksmResAt A x.ret (Pksm.pksmParse x.bytes) ∗
      (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗ A.pool
  apply entails_of_eq; ac_rfl

/-! ## 4. `+0x8c0` `Ok` Continuation (`[LibsignalPlacement]`) -/

/-- the `+0x8c0` (`2240`) Ok edge returns with
`(pksmTryFromSpecPlaced A).post`. -/
theorem preKey8c0OkW_placed_proof [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) :
    PreKey8c0OkWPlaced A H := by
  intro x s0 sf vb b1 bs1 m bk ik msg spkId _pk ipk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen
    regTag regVal opkTag opkVal _kpkTag kpkVal kyberBoxPtr kyberBoxLen
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 innerMsg msgG rk0 rk1 rk2 rk3 addrW0 addrW1
    verHi56 clonePtr hx hge3 hle4 _hlen hdec hbk hik hmsg hsid hreg hopk _hkpk hpkD _hkyb hpkB
    hikD hinner hrk hst _hbkCap _hikCap _hmsgCap hpc hrun
  have hvlt := vb.isLt
  simp only [BitVec.lt_def, vb_lsr4_toNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    at hge3 hle4
  have hlo : 0x30 ≤ vb.toNat := by omega
  have hhi : vb.toNat ≤ 0x4f := by omega
  have hbk_ok : ecKeyParses bk = true := ecKeyParses_of_deserialize_ok hpkD
  have hpkb1 : (pkOf bk).bytes.toList = (bk.take 33).drop 1 := pkOf_bytes_of_ecKeyParses hbk_ok
  have hik_ok : ecKeyParses ik = true := ecKeyParses_of_deserialize_ok hikD
  have hikpk : pkOf ik = ipk := pkOf_of_deserialize_ok hikD
  obtain ⟨ik0, ik1, ik2, ik3, hipk⟩ := w8b_exists_words4_of_vector32 ipk.bytes
  have hikw : ∀ a : BitVec 64, (a ↦ₛ (pkOf ik).bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3) := by
    rw [hikpk]; exact hipk
  obtain ⟨hopkTag, hopkVal⟩ := w8bPack_opk hopk
  have hregId := w8bPack_regId hreg
  have hBridge := sret_cells_entails_pksmResAt A x.ret vb (b1 :: bs1) m bk ik msg spkId innerMsg
    msgG clonePtr kyberBoxPtr kyberBoxLen rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 ik0 ik1 ik2 ik3
    opkTag opkVal kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 emp hlo hhi hdec hbk hik
    hmsg hsid hbk_ok hik_ok hinner hopkTag hopkVal (hpkb1.trans hpkB) hrk hikw
  rw [hx] at hst
  refine SepWPp.mono_pre
    (w8bPack_pre_open_placed A s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap ikPtr
      msgCap msgPtr kyberBoxPtr kyberBoxLen clonePtr regTag regVal opkTag opkVal spkId kpkVal
      (m.registrationId.getD 0#32) p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb (b1 :: bs1)
      m.kyberPreKeyId m.kyberCiphertext bk ik msg x.bytes ipk innerMsg msgG rk0 rk1 rk2 rk3
      addrW0 addrW1 verHi56 ik0 ik1 ik2 ik3 hx hregId hipk) ?_
  refine SepWPp.exists_pre fun msgAct => SepWPp.exists_pre fun ikAct =>
    SepWPp.exists_pre fun bkAct => ?_
  refine SepWPp.bind
    (preKey_pack_8c0_to_970_dealloc_res_placed_wpX (msgAct := msgAct) (ikAct := ikAct)
      (bkAct := bkAct) (R_heap := emp) hopkTag hBridge hst hpc hrun) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
  refine SepWPp.mono_pre hent1 ?_
  refine SepWPp.bind (deallocChain_970_placed_wpX hC msgAct ikAct bkAct hst1 hpc1 hrun1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, _, hent2⟩
  refine SepWPp.mono_post
    (SepWPp.mono_pre
      (Entails.trans hent2
        (w8bPack_epi_regroup_placed A s0 x.ptr bkCap bkPtr msgPtr ikPtr kyberLen regTag
          regVal opkTag opkVal spkId kpkVal (m.registrationId.getD 0#32)
          p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 ik0 ik1 ik2 ik3
          ik msg x.bytes
          (RunCompose.pksmResAt A x.ret (Pksm.pksmParse (vb :: b1 :: bs1)))))
      (epilogue_504_placed_w_wpX (A := A) (x := x)
        (R := RunCompose.pksmResAt A x.ret (Pksm.pksmParse (vb :: b1 :: bs1)))
        hst2 hpc2 hrun2)) ?_
  intro sf' Pf _ _ hq
  obtain ⟨hsp, hcs, hcl', htr, hent⟩ := hq
  rw [← hx] at hent
  exact w8bPack_okPost_placed ⟨hsp, hcs, hcl', htr, hent⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

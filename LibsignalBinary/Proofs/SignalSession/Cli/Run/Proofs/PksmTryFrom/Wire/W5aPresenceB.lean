/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresence
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::try_from`: Presence-Failure Join Frames and Deallocation Bridges

Defines the presence-failure join frames (`BkNoneJoinFrame`, `IkNoneJoinFrame`,
`MsgNoneJoinFrame`, `SpkNoneJoinFrame`) and proves full-frame `deallocSlot` bridges from
`+0x460` / `+0x57c` / `+0x590` / `+0x5a4` to the error-tail entries `+0x5e0`, `+0x61c`,
`+0x66c`, and `+0x678`.
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
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli.RunProofs

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 4. Dealloc-Slot Bridges, Join Frames (`section D12JoinFrames`) -/

section D12JoinFrames

/-- Dealloc-slot bridge for `BkNone` (`+0x460 → +0x5e0`, dec `1120 → 1504`): steps `post_bk_none_to_5e0_wpW`
and bridges `optVecU8Buf` for `kyberOpt`, `ikOpt`, `msgOpt` via upstream
`optVecU8Buf_entails_deallocSlot` into the exact consumer pre-shape of `ErrTailB.entry_5e0_wpX`. -/
theorem post_bk_none_full_to_5e0_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {s0 s : State}
    {sp' sret len ptr0 w0 w1 kyberCap kyberPtr kyberLen bkPtr bkLen
      ikCap ikPtr ikLen msgCap msgPtr msgLen w96 w104 : BitVec 64} {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32}
    {kyberOpt ikOpt msgOpt : Option (List (BitVec 8))}
    (hst : PreKeyLoopExitState img s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1504#64) s
      ((((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
          vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
          vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
          vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)) ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          optVecU8Buf A ikCap ikPtr ikLen ikOpt ∗
          optVecU8Buf A msgCap msgPtr msgLen msgOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        BkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap spkTag vb sf ∧
        (Pf ⊢ ∃∗ kyAct : Bool, ∃∗ ikAct : Bool, ∃∗ msgAct : Bool,
          deallocSlot A kyberCap kyberPtr kyAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
          vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
          vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
          vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)))
      (tryFromQp s0) := by
  refine SepWPp.frame_tryFrom (post_bk_none_to_5e0_wpW hst hpc hrun hx24)
    fun sf Pf ⟨hbst, hent⟩ => ⟨hbst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  dsimp only [BkNoneTailMem]
  have hky := optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen kyberOpt
  have hik := optVecU8Buf_entails_deallocSlot A ikCap ikPtr ikLen ikOpt
  have hmsg := optVecU8Buf_entails_deallocSlot A msgCap msgPtr msgLen msgOpt
  refine Entails.trans (Q :=
      (∃∗ kyAct : Bool, deallocSlot A kyberCap kyberPtr kyAct) ∗
      (∃∗ ikAct : Bool, deallocSlot A ikCap ikPtr ikAct) ∗
      (∃∗ msgAct : Bool, deallocSlot A msgCap msgPtr msgAct) ∗
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
        vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)))
    ?_ ?_
  · refine Entails.trans (Q :=
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        optVecU8Buf A ikCap ikPtr ikLen ikOpt ∗
        optVecU8Buf A msgCap msgPtr msgLen msgOpt ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
          vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
          vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
          vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)))
      (by apply entails_of_eq; ac_rfl)
      (sepConj_mono hky (sepConj_mono hik (sepConj_mono_left hmsg)))
  · simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun msgAct =>
      Entails.sepExists_elim fun ikAct =>
      Entails.sepExists_elim fun kyAct => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
    refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
    refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
    apply entails_of_eq; ac_rfl

/-- Dealloc-slot bridge for `IkNone` (`+0x57c → +0x61c`, dec `1404 → 1564`): steps `post_ik_none_to_61c_wpW`
and bridges `Wire.vecU8Buf A bkCap bkPtr bk`, `optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt`,
and `optVecU8Buf A msgCap msgPtr msgLen msgOpt` into `bkCap ≠ noneCap` and the exact consumer
pre-shape of `ErrTailB.entry_61c_wpX`. -/
theorem post_ik_none_full_to_61c_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {s0 s : State}
    {sp' sret len ptr0 w0 w1 bkCap bkPtr kyberCap kyberPtr kyberLen
      msgCap msgPtr msgLen x24 : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {kyberOpt msgOpt : Option (List (BitVec 8))}
    (hst : IkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1404#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1564#64) s
      (memRegion (sp' + 312#64) 48 ∗
        (Wire.vecU8Buf A bkCap bkPtr bk ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          optVecU8Buf A msgCap msgPtr msgLen msgOpt ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        IkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb sf ∧
        bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ bkAct : Bool, ∃∗ kyAct : Bool, ∃∗ msgAct : Bool,
          deallocSlot A bkCap bkPtr bkAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A kyberCap kyberPtr kyAct ∗
          deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (vecU8Buf_entails_deallocSlot A bkCap bkPtr bk))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜bkCap ≠ noneCap⌝ ∗
      (memRegion (sp' + 312#64) 48 ∗
        ((∃∗ bkAct : Bool, deallocSlot A bkCap bkPtr bkAct) ∗
          (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          optVecU8Buf A msgCap msgPtr msgLen msgOpt ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hbk_ne => ?_
  refine SepWPp.frame_tryFrom (post_ik_none_to_61c_wpW hst hpc hrun)
    fun sf Pf ⟨hist, hent⟩ => ⟨hist, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen kyberOpt
  have hmsg := optVecU8Buf_entails_deallocSlot A msgCap msgPtr msgLen msgOpt
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hky (sepConj_mono_left hmsg)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun msgAct =>
    Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun bkAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  apply entails_of_eq; ac_rfl

/-- Dealloc-slot bridge for `MsgNone` (`+0x590 → +0x66c`, dec `1424 → 1644`): steps `post_msg_none_to_66c_wpW`
and bridges `Wire.vecU8Buf A ikCap ikPtr ik`, `Wire.vecU8Buf A bkCap bkPtr bk`, and
`optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt` into `ikCap ≠ noneCap ∧ bkCap ≠ noneCap` and
the exact consumer pre-shape of `ErrTailB.entry_66c_wpX`. -/
theorem post_msg_none_full_to_66c_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {s0 s : State}
    {sp' sret len ptr0 w0 w1 ikCap ikPtr bkCap bkPtr kyberCap kyberPtr kyberLen
      x24 : BitVec 64} {vb : BitVec 8}
    {ik bk : List (BitVec 8)} {kyberOpt : Option (List (BitVec 8))}
    (hst : MsgNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1424#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1644#64) s
      (memRegion (sp' + 312#64) 48 ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        MsgNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb sf ∧
        ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ ikAct : Bool, ∃∗ bkAct : Bool, ∃∗ kyAct : Bool,
          (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A kyberCap kyberPtr kyAct ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (vecU8Buf_entails_deallocSlot A ikCap ikPtr ik)
        (sepConj_mono_right (sepConj_mono_left (vecU8Buf_entails_deallocSlot A bkCap bkPtr bk))))))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜ikCap ≠ noneCap⌝ ∗ ⌜bkCap ≠ noneCap⌝ ∗
      (memRegion (sp' + 312#64) 48 ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          (∃∗ ikAct : Bool, deallocSlot A ikCap ikPtr ikAct) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (∃∗ bkAct : Bool, deallocSlot A bkCap bkPtr bkAct) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hik_ne => SepWPp.pure_pre fun hbk_ne => ?_
  refine SepWPp.frame_tryFrom (post_msg_none_to_66c_wpW hst hpc hrun)
    fun sf Pf ⟨hmst, hent⟩ => ⟨hmst, hik_ne, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen kyberOpt
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hky))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun bkAct =>
    Entails.sepExists_elim fun ikAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  apply entails_of_eq; ac_rfl

/-- Dealloc-slot bridge for `SpkNone` (`+0x5a4 → +0x678`, dec `1444 → 1656`): steps `post_spk_none_to_678_wpW`
and bridges `Wire.vecU8Buf` for `msg`, `ik`, `bk` and `optVecU8Buf` for `kyberOpt` into
`msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap` and the exact consumer pre-shape of
`ErrTailB.entry_678_wpX`. -/
theorem post_spk_none_full_to_678_wpW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {s0 s : State}
    {sp' sret len ptr0 w0 w1 msgCap msgPtr ikCap ikPtr bkCap bkPtr
      kyberCap kyberPtr kyberLen : BitVec 64} {vb : BitVec 8}
    {msg ik bk : List (BitVec 8)} {kyberOpt : Option (List (BitVec 8))}
    (hst : SpkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1444#64)
    (hrun : s.status = .Running) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 1656#64) s
      (memRegion (sp' + 312#64) 48 ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          Wire.vecU8Buf A msgCap msgPtr msg ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        SpkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool, ∃∗ kyAct : Bool,
          (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A kyberCap kyberPtr kyAct ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (vecU8Buf_entails_deallocSlot A msgCap msgPtr msg)
        (sepConj_mono_right (sepConj_mono (vecU8Buf_entails_deallocSlot A ikCap ikPtr ik)
          (sepConj_mono_right (sepConj_mono_left (vecU8Buf_entails_deallocSlot A bkCap bkPtr bk))))))))) ?_
  refine SepWPp.mono_pre (P' :=
      ⌜msgCap ≠ noneCap⌝ ∗ ⌜ikCap ≠ noneCap⌝ ∗ ⌜bkCap ≠ noneCap⌝ ∗
      (memRegion (sp' + 312#64) 48 ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          (∃∗ msgAct : Bool, deallocSlot A msgCap msgPtr msgAct) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          (∃∗ ikAct : Bool, deallocSlot A ikCap ikPtr ikAct) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (∃∗ bkAct : Bool, deallocSlot A bkCap bkPtr bkAct) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.pure_pre fun hmsg_ne =>
    SepWPp.pure_pre fun hik_ne =>
    SepWPp.pure_pre fun hbk_ne => ?_
  refine SepWPp.frame_tryFrom (post_spk_none_to_678_wpW hst hpc hrun)
    fun sf Pf ⟨hsst, hent⟩ => ⟨hsst, hmsg_ne, hik_ne, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen kyberOpt
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hky))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun bkAct =>
    Entails.sepExists_elim fun ikAct =>
    Entails.sepExists_elim fun msgAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  apply entails_of_eq; ac_rfl

/-- Join frame at `+0x5e0` (`1504`, `m.baseKey = none`), matching
`ErrTailB.entry_5e0_wpX` field-for-field with every continuation-read resource outside `R`. -/
def BkNoneJoinFrame (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (s0 s2 : State) : Prop :=
  s2.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1504#64 ∧
  s2.status = .Running ∧
  ∃ (sp' sret len ptr0 w0 w1 kyberCap kyberPtr ikCap ikPtr msgCap msgPtr : BitVec 64)
    (spkTag : BitVec 32) (vb : BitVec 8) (kyAct ikAct msgAct : Bool) (R : SepProp),
    BkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap spkTag vb s2 ∧
    (s2.mem ⊨ deallocSlot A kyberCap kyberPtr kyAct ∗
      (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)

/-- Join frame at `+0x61c` (`1564`, `m.identityKey = none`), matching
`ErrTailB.entry_61c_wpX` field-for-field with every continuation-read resource outside `R`. -/
def IkNoneJoinFrame (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (s0 s2 : State) : Prop :=
  s2.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1564#64 ∧
  s2.status = .Running ∧
  ∃ (sp' sret len ptr0 w0 w1 bkCap bkPtr kyberCap kyberPtr msgCap msgPtr x24 : BitVec 64)
    (vb : BitVec 8) (bkAct kyAct msgAct : Bool) (R : SepProp),
    IkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb s2 ∧
    bkCap ≠ noneCap ∧
    (s2.mem ⊨ deallocSlot A bkCap bkPtr bkAct ∗
      (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyberCap kyberPtr kyAct ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)

/-- Join frame at `+0x66c` (`1644`, `m.message = none`), matching
`ErrTailB.entry_66c_wpX` field-for-field with every continuation-read resource outside `R`. -/
def MsgNoneJoinFrame (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (s0 s2 : State) : Prop :=
  s2.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1644#64 ∧
  s2.status = .Running ∧
  ∃ (sp' sret len ptr0 w0 w1 ikCap ikPtr bkCap bkPtr kyberCap kyberPtr x24 : BitVec 64)
    (vb : BitVec 8) (ikAct bkAct kyAct : Bool) (R : SepProp),
    MsgNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb s2 ∧
    ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
    (s2.mem ⊨ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyberCap kyberPtr kyAct ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)

/-- Join frame at `+0x678` (`1656`, `m.signedPreKeyId = none`), matching
`ErrTailB.entry_678_wpX` field-for-field with every continuation-read resource outside `R`. -/
def SpkNoneJoinFrame (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (s0 s2 : State) : Prop :=
  s2.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1656#64 ∧
  s2.status = .Running ∧
  ∃ (sp' sret len ptr0 w0 w1 msgCap msgPtr ikCap ikPtr bkCap bkPtr kyberCap kyberPtr : BitVec 64)
    (vb : BitVec 8) (msgAct ikAct bkAct kyAct : Bool) (R : SepProp),
    SpkNoneTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s2 ∧
    msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
    (s2.mem ⊨ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyberCap kyberPtr kyAct ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R)

theorem presenceErrTailState_nonvacuous (img : Obj.Image) (s0 : State)
    (sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 : BitVec 64) (vb : BitVec 8)
    (hst : PostEpilogueState img s0 sp' s0) :
    ∃ sf : State,
      PresenceErrTailState img s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap x24 vb sf := by
  rcases hst with ⟨hsp0, hal, hF, hsym, _⟩
  refine ⟨((((((((((s0.writeReg64 .x29 (sp' + 512#64)).writeReg64 .x28 kyberCap).writeReg64
    .x27 0x8000000000000002#64).writeReg64 .x26 msgCap).writeReg64 .x25 kyberPtr).writeReg64
    .x24 x24).writeReg64 .x23 ikCap).writeReg64 .x22 (vb.zeroExtend 64)).writeReg64
    .x21 ptr0).writeReg64 .x20 len).writeReg64 .x19 sret, ?_⟩
  refine ⟨⟨by tryFromPost_sp [hsp0], by tryFromPost_sp_align hal,
      by simpa [Obj.Image.FrozenLoaded, arm64_norm] using hF,
      by simp [hsym, arm64_norm], by simp [arm64_norm]⟩,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩

theorem bkNoneJoinFrame_nonvacuous (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (sp' sret len ptr0 w0 w1 kyberCap kyberPtr ikCap ikPtr msgCap msgPtr : BitVec 64)
    (spkTag : BitVec 32) (vb : BitVec 8) (kyAct ikAct msgAct : Bool) (R : SepProp)
    (hst : PostEpilogueState img s0 sp' s0)
    (hmem : s0.mem ⊨ deallocSlot A kyberCap kyberPtr kyAct ∗
      (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) :
    ∃ s2 : State, BkNoneJoinFrame img A ext s0 s2 := by
  rcases hst with ⟨hsp0, hal, hF, hsym, _⟩
  let s0' : State := { s0 with
    pc := (contractProg img.base ext).fnAddr preKeyTryFromName + 1504#64
    status := .Running }
  refine ⟨((((((((((s0'.writeReg64 .x29 (sp' + 512#64)).writeReg64 .x28 kyberCap).writeReg64
    .x27 0x8000000000000002#64).writeReg64 .x26 msgCap).writeReg64 .x25 kyberPtr).writeReg64
    .x24 (spkTag.zeroExtend 64)).writeReg64 .x23 ikCap).writeReg64
    .x22 (vb.zeroExtend 64)).writeReg64 .x21 ptr0).writeReg64 .x20 len).writeReg64 .x19 sret,
    by simp [s0', arm64_norm], by simp [s0', arm64_norm],
    sp', sret, len, ptr0, w0, w1, kyberCap, kyberPtr, ikCap, ikPtr, msgCap, msgPtr,
    spkTag, vb, kyAct, ikAct, msgAct, R, ?_, ?_⟩
  · refine ⟨⟨by dsimp [s0']; tryFromPost_sp [hsp0], by dsimp [s0']; tryFromPost_sp_align hal,
        by simpa [s0', Obj.Image.FrozenLoaded, arm64_norm] using hF,
        by simp [s0', hsym, arm64_norm], by simp [s0', arm64_norm]⟩,
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm]⟩
  · simpa [s0', arm64_norm] using hmem

theorem ikNoneJoinFrame_nonvacuous (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (sp' sret len ptr0 w0 w1 bkCap bkPtr kyberCap kyberPtr msgCap msgPtr x24 : BitVec 64)
    (vb : BitVec 8) (bkAct kyAct msgAct : Bool) (R : SepProp)
    (hbk : bkCap ≠ noneCap) (hst : PostEpilogueState img s0 sp' s0)
    (hmem : s0.mem ⊨ deallocSlot A bkCap bkPtr bkAct ∗
      (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyberCap kyberPtr kyAct ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) :
    ∃ s2 : State, IkNoneJoinFrame img A ext s0 s2 := by
  rcases hst with ⟨hsp0, hal, hF, hsym, _⟩
  let s0' : State := { s0 with
    pc := (contractProg img.base ext).fnAddr preKeyTryFromName + 1564#64
    status := .Running }
  refine ⟨((((((((((s0'.writeReg64 .x29 (sp' + 512#64)).writeReg64 .x28 kyberCap).writeReg64
    .x27 0x8000000000000002#64).writeReg64 .x26 msgCap).writeReg64 .x25 kyberPtr).writeReg64
    .x24 x24).writeReg64 .x23 noneCap).writeReg64 .x22 (vb.zeroExtend 64)).writeReg64
    .x21 ptr0).writeReg64 .x20 len).writeReg64 .x19 sret,
    by simp [s0', arm64_norm], by simp [s0', arm64_norm],
    sp', sret, len, ptr0, w0, w1, bkCap, bkPtr, kyberCap, kyberPtr, msgCap, msgPtr, x24,
    vb, bkAct, kyAct, msgAct, R, ?_, hbk, ?_⟩
  · refine ⟨⟨by dsimp [s0']; tryFromPost_sp [hsp0], by dsimp [s0']; tryFromPost_sp_align hal,
        by simpa [s0', Obj.Image.FrozenLoaded, arm64_norm] using hF,
        by simp [s0', hsym, arm64_norm], by simp [s0', arm64_norm]⟩,
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm]⟩
  · simpa [s0', arm64_norm] using hmem

theorem msgNoneJoinFrame_nonvacuous (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (sp' sret len ptr0 w0 w1 ikCap ikPtr bkCap bkPtr kyberCap kyberPtr x24 : BitVec 64)
    (vb : BitVec 8) (ikAct bkAct kyAct : Bool) (R : SepProp)
    (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap) (hst : PostEpilogueState img s0 sp' s0)
    (hmem : s0.mem ⊨ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyberCap kyberPtr kyAct ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) :
    ∃ s2 : State, MsgNoneJoinFrame img A ext s0 s2 := by
  rcases hst with ⟨hsp0, hal, hF, hsym, _⟩
  let s0' : State := { s0 with
    pc := (contractProg img.base ext).fnAddr preKeyTryFromName + 1644#64
    status := .Running }
  refine ⟨((((((((((s0'.writeReg64 .x29 (sp' + 512#64)).writeReg64 .x28 kyberCap).writeReg64
    .x27 0x8000000000000002#64).writeReg64 .x26 noneCap).writeReg64 .x25 kyberPtr).writeReg64
    .x24 x24).writeReg64 .x23 ikCap).writeReg64 .x22 (vb.zeroExtend 64)).writeReg64
    .x21 ptr0).writeReg64 .x20 len).writeReg64 .x19 sret,
    by simp [s0', arm64_norm], by simp [s0', arm64_norm],
    sp', sret, len, ptr0, w0, w1, ikCap, ikPtr, bkCap, bkPtr, kyberCap, kyberPtr, x24,
    vb, ikAct, bkAct, kyAct, R, ?_, hik, hbk, ?_⟩
  · refine ⟨⟨by dsimp [s0']; tryFromPost_sp [hsp0], by dsimp [s0']; tryFromPost_sp_align hal,
        by simpa [s0', Obj.Image.FrozenLoaded, arm64_norm] using hF,
        by simp [s0', hsym, arm64_norm], by simp [s0', arm64_norm]⟩,
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm]⟩
  · simpa [s0', arm64_norm] using hmem

theorem spkNoneJoinFrame_nonvacuous (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (sp' sret len ptr0 w0 w1 msgCap msgPtr ikCap ikPtr bkCap bkPtr kyberCap kyberPtr : BitVec 64)
    (vb : BitVec 8) (msgAct ikAct bkAct kyAct : Bool) (R : SepProp)
    (hmsg : msgCap ≠ noneCap) (hik : ikCap ≠ noneCap) (hbk : bkCap ≠ noneCap)
    (hst : PostEpilogueState img s0 sp' s0)
    (hmem : s0.mem ⊨ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
      deallocSlot A msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      deallocSlot A ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      deallocSlot A bkCap bkPtr bkAct ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      deallocSlot A kyberCap kyberPtr kyAct ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) :
    ∃ s2 : State, SpkNoneJoinFrame img A ext s0 s2 := by
  rcases hst with ⟨hsp0, hal, hF, hsym, _⟩
  let s0' : State := { s0 with
    pc := (contractProg img.base ext).fnAddr preKeyTryFromName + 1656#64
    status := .Running }
  refine ⟨((((((((((s0'.writeReg64 .x29 (sp' + 512#64)).writeReg64 .x28 kyberCap).writeReg64
    .x27 0x8000000000000002#64).writeReg64 .x26 msgCap).writeReg64 .x25 kyberPtr).writeReg64
    .x24 0#64).writeReg64 .x23 ikCap).writeReg64 .x22 (vb.zeroExtend 64)).writeReg64
    .x21 ptr0).writeReg64 .x20 len).writeReg64 .x19 sret,
    by simp [s0', arm64_norm], by simp [s0', arm64_norm],
    sp', sret, len, ptr0, w0, w1, msgCap, msgPtr, ikCap, ikPtr, bkCap, bkPtr, kyberCap, kyberPtr,
    vb, msgAct, ikAct, bkAct, kyAct, R, ?_, hmsg, hik, hbk, ?_⟩
  · refine ⟨⟨by dsimp [s0']; tryFromPost_sp [hsp0], by dsimp [s0']; tryFromPost_sp_align hal,
        by simpa [s0', Obj.Image.FrozenLoaded, arm64_norm] using hF,
        by simp [s0', hsym, arm64_norm], by simp [s0', arm64_norm]⟩,
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm]⟩
  · simpa [s0', arm64_norm] using hmem

end D12JoinFrames

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

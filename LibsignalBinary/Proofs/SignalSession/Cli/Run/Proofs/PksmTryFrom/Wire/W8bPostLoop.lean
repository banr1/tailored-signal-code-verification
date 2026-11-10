/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssembly
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresence
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: Post-Loop `Ok` Dispatch (`+0x460 → +0x5b4` / Presence Error)

Proves `preKeyPostLoopOkW_of_5b4`, discharging `PreKeyPostLoopOkW` (`+0x460 → ret` on
`some m`) into `post_seg1_xok_to_5b4_wpW` + `PreKey5b4OkW` when all four required fields
are `some`, and `PreKeyPresenceErrW` when any required field is `none`.
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
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

/-! ## 1. Raw `Option<u32>` cells -/

/-- The raw `(tag, val)` cells of a stack `Option<u32>` holding `o` (`none`: `tag = 0`, `val`
arbitrary; `some v`: `tag = 1`, `val = v`). -/
def w8bOptU32Cells : Option (BitVec 32) → BitVec 32 × BitVec 32 → Prop
  | none, p => p.1 = 0#32
  | some v, p => p.1 = 1#32 ∧ p.2 = v

/-- `Option<u32>` at `a` as raw `(tag, val)` cells (witness bundled with its cell facts). -/
theorem w8b_optU32At_entails (a : BitVec 64) (o : Option (BitVec 32)) :
    CryptoVerification.LibsignalTripleRatchet.Prost.optU32At a o ⊢
      ∃∗ p : {p : BitVec 32 × BitVec 32 // w8bOptU32Cells o p},
        (a ↦₃₂ p.1.1) ∗ ((a + 4#64) ↦₃₂ p.1.2) := by
  cases o with
  | none =>
    have h4 : memRegion (a + 4#64) 4 = ∃∗ v : BitVec 32, (a + 4#64) ↦₃₂ v :=
      IsBlock.eq (IsBlock.memRegion (a + 4#64) 4)
        (IsBlock.sepExists fun v => IsBlock.pointsTo32 (a + 4#64) v)
        fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩
    simp only [CryptoVerification.LibsignalTripleRatchet.Prost.optU32At, h4,
      sepExists_sepConj_right]
    exact Entails.sepExists_elim fun v =>
      Entails.sepExists_intro
        (P := fun p : {p : BitVec 32 × BitVec 32 // w8bOptU32Cells none p} =>
          (a ↦₃₂ p.1.1) ∗ ((a + 4#64) ↦₃₂ p.1.2))
        ⟨(0#32, v), rfl⟩
  | some v =>
    simp only [CryptoVerification.LibsignalTripleRatchet.Prost.optU32At]
    exact Entails.sepExists_intro
      (P := fun p : {p : BitVec 32 × BitVec 32 // w8bOptU32Cells (some v) p} =>
        (a ↦₃₂ p.1.1) ∗ ((a + 4#64) ↦₃₂ p.1.2))
      ⟨(1#32, v), ⟨rfl, rfl⟩⟩

/-! ## 2. Stack-scratch split and wire-struct unfolding -/

theorem w8b_memRegion296_split (sp' : BitVec 64) :
    memRegion sp' 296 =
      memRegion sp' 16 ∗ memRegion (sp' + 16#64) 96 ∗ memRegion (sp' + 112#64) 184 := by
  rw [show (296 : Nat) = 16 + 280 by decide, Prost.memRegion_split sp' 16 280 (by decide),
    show (280 : Nat) = 96 + 184 by decide,
    Prost.memRegion_split (sp' + BitVec.ofNat 64 16) 96 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- `wirePreKeyAt` with the three required `Option<Vec<u8>>` fields and `signedPreKeyId` `some`. -/
theorem w8b_wirePreKeyAt_some_eq (A : RustAlloc) (g : WirePreKeyGhost) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) {bk ik msg : List (BitVec 8)} (hbk : m.baseKey = some bk)
    (hik : m.identityKey = some ik) (hmsg : m.message = some msg) {spkId : BitVec 32}
    (hspk : m.signedPreKeyId = some spkId) :
    wirePreKeyAt A g a m =
      (CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A g.kyberCt a
          m.kyberCiphertext ∗
        (vecHeader (a + 0x18#64) g.baseKey.cap g.baseKey.ptr (BitVec.ofNat 64 bk.length) ∗
          Wire.vecU8Buf A g.baseKey.cap g.baseKey.ptr bk) ∗
        (vecHeader (a + 0x30#64) g.identityKey.cap g.identityKey.ptr
            (BitVec.ofNat 64 ik.length) ∗
          Wire.vecU8Buf A g.identityKey.cap g.identityKey.ptr ik) ∗
        (vecHeader (a + 0x48#64) g.message.cap g.message.ptr (BitVec.ofNat 64 msg.length) ∗
          Wire.vecU8Buf A g.message.cap g.message.ptr msg) ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x60#64) m.registrationId ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x68#64) m.preKeyId ∗
        (((a + 0x70#64) ↦₃₂ 1#32) ∗ ((a + 0x70#64 + 4#64) ↦₃₂ spkId)) ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x78#64) m.kyberPreKeyId) := by
  unfold wirePreKeyAt
  rw [hbk, hik, hmsg, hspk]
  rfl

/-! ## 3. Frames and the `+0x5b4` continuation -/

/-- Presence check post-frame at `+0x5b4` (the `Pf` of `post_seg1_xok_to_5b4_wpW`). -/
def w8bXokPost (A : RustAlloc) (sp' bkCap bkPtr kyberCap kyberPtr kyberLen ikCap ikPtr msgCap msgPtr :
    BitVec 64) (regTag regVal opkTag opkVal spkId kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) (bk ik msg : List (BitVec 8)) : SepProp :=
  seg1SpillsAtW sp' bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
      ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
      regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
    memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
    optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
    Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗
    A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)

/-- The part of the `PreKeyPostLoopOkW` precondition untouched by `post_seg1_xok_to_5b4_wpW`. -/
def w8bPostLoopFrame (img : Obj.Image) (s0 : State) (sp' sret ptr : BitVec 64)
    (bytes : List (BitVec 8)) : SepProp :=
  memRegion sp' 16 ∗ memRegion (sp' + 112#64) 184 ∗ memRegion (sp' + 296#64) 16 ∗
    memRegion (sp' + 440#64) 8 ∗ memRegion (sp' + 448#64) 64 ∗
    preKeyCalleeSavedAt sp' s0 ∗ memRegion sret 248 ∗ (ptr ↦ₛ bytes) ∗ logOff img ∗
    memRegion (sp' - BitVec.ofNat 64 preKeyTryFromSubStack)
      (preKeyTryFromSubStack - Prost.skipFieldStackX 100)

/-- `+0x5b4` (`1460`) → `ret` when all four required fields are
`some`. -/
def PreKey5b4OkW (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  ∀ (x : RunCompose.PksmGhost) (s0 sf : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap kyberPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    PresenceOkState img s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberCap kyberPtr ikCap msgCap vb sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1460#64 →
    sf.status = .Running →
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) sf
      (w8bXokPost A (s0.sp - 608#64) bkCap bkPtr kyberCap kyberPtr kyberLen ikCap ikPtr msgCap
          msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal m.kyberCiphertext bk ik msg ∗
        w8bPostLoopFrame img s0 (s0.sp - 608#64) x.ret x.ptr x.bytes)
      (fun sf' Pf =>
        sf'.sp = s0.sp ∧ (calleeSavedVRegs sf' = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf') ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf'))
      (tryFromQp s0)

/-- `PreKeyPostLoopOkW` restricted to "some required field is `none`"
(presence-failure `Err` edges `+0x5e0` / `+0x61c` / `+0x66c` / `+0x678` → ErrTailB → `+0x504`
→ ret). -/
def PreKeyPresenceErrW (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  ∀ (x : RunCompose.PksmGhost) (s0 s : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    Pksm.decodeProto (b1 :: bs1) = some m →
    (m.baseKey = none ∨ m.identityKey = none ∨ m.message = none ∨ m.signedPreKeyId = none) →
    PreKeyLoopExitState img s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr vb s →
    s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64 →
    s.status = .Running →
    s.readReg64 .x24 = 0#64 →
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) s
      (wirePreKeyOf A (s0.sp - 608#64 + 312#64) m ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗
        A.pool ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf))
      (tryFromQp s0)

/-! ## 4. `PreKeyPostLoopOkW` -/

/-- the post-loop `some m` path, from Presence check + the `+0x5b4` continuation + the
presence-failure named hypothesis. -/
theorem preKeyPostLoopOkW_of_5b4 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDropSpe : DropSpeOkX img A ext)
    (hPresErr : PreKeyPresenceErrW img A ext)
    (hOk : PreKey5b4OkW img A ext) :
    PreKeyPostLoopOkW img A ext := by
  intro x s0 s vb b1 bs1 m hcons hv3 hv4 hlen hdec hst hpc hrun hx24
  rcases hbkO : m.baseKey with _ | bk
  · exact hPresErr x s0 s vb b1 bs1 m hcons hv3 hv4 hlen hdec (Or.inl hbkO) hst hpc hrun hx24
  rcases hikO : m.identityKey with _ | ik
  · exact hPresErr x s0 s vb b1 bs1 m hcons hv3 hv4 hlen hdec (Or.inr (Or.inl hikO))
      hst hpc hrun hx24
  rcases hmsgO : m.message with _ | msg
  · exact hPresErr x s0 s vb b1 bs1 m hcons hv3 hv4 hlen hdec (Or.inr (Or.inr (Or.inl hmsgO)))
      hst hpc hrun hx24
  rcases hspkO : m.signedPreKeyId with _ | spkId
  · exact hPresErr x s0 s vb b1 bs1 m hcons hv3 hv4 hlen hdec (Or.inr (Or.inr (Or.inr hspkO)))
      hst hpc hrun hx24
  rw [w8b_memRegion296_split, stackAt_preKeyTryFromSubStack_skipField]
  unfold wirePreKeyOf
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun g => ?_
  rw [w8b_wirePreKeyAt_some_eq A g _ m hbkO hikO hmsgO hspkO]
  simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (w8b_optU32At_entails _ m.kyberPreKeyId))))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun pKpk => ?_
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (w8b_optU32At_entails _ m.preKeyId)))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun pOpk => ?_
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (w8b_optU32At_entails _ m.registrationId))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun pReg => ?_
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_left (Wire.optVecU8At_entails_header_buf A g.kyberCt _ m.kyberCiphertext)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun kc => SepWPp.exists_pre fun kp => SepWPp.exists_pre fun kl => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.mono_pre (P' :=
      (memRegion (s0.sp - 608#64 + 16#64) 96 ∗
        vecHeader (s0.sp - 608#64 + 312#64) kc kp kl ∗
        optVecU8Buf A kc kp kl m.kyberCiphertext ∗
        vecHeader (s0.sp - 608#64 + 336#64) g.baseKey.cap g.baseKey.ptr
          (BitVec.ofNat 64 bk.length) ∗ Wire.vecU8Buf A g.baseKey.cap g.baseKey.ptr bk ∗
        vecHeader (s0.sp - 608#64 + 360#64) g.identityKey.cap g.identityKey.ptr
          (BitVec.ofNat 64 ik.length) ∗ Wire.vecU8Buf A g.identityKey.cap g.identityKey.ptr ik ∗
        vecHeader (s0.sp - 608#64 + 384#64) g.message.cap g.message.ptr
          (BitVec.ofNat 64 msg.length) ∗ Wire.vecU8Buf A g.message.cap g.message.ptr msg ∗
        ((s0.sp - 608#64 + 408#64) ↦₃₂ pReg.1.1) ∗ ((s0.sp - 608#64 + 412#64) ↦₃₂ pReg.1.2) ∗
        ((s0.sp - 608#64 + 416#64) ↦₃₂ pOpk.1.1) ∗ ((s0.sp - 608#64 + 420#64) ↦₃₂ pOpk.1.2) ∗
        ((s0.sp - 608#64 + 424#64) ↦₃₂ 1#32) ∗ ((s0.sp - 608#64 + 428#64) ↦₃₂ spkId) ∗
        ((s0.sp - 608#64 + 432#64) ↦₃₂ pKpk.1.1) ∗ ((s0.sp - 608#64 + 436#64) ↦₃₂ pKpk.1.2) ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100)) ∗
      (memRegion (s0.sp - 608#64) 16 ∗ memRegion (s0.sp - 608#64 + 112#64) 184 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗ memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗ memRegion x.ret 248 ∗
        (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗
        memRegion (s0.sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack)
          (preKeyTryFromSubStack - Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (post_seg1_xok_to_5b4_wpW (kyberOpt := m.kyberCiphertext) (bk := bk) (ik := ik) (msg := msg)
      hDropSpe hst hpc hrun hx24) ?_
  rintro sm Pm hpcm hrunm ⟨hstm, hbkC, hikC, hmsgC, hPm⟩
  exact SepWPp.mono_pre (sepConj_mono_left hPm)
    (hOk x s0 sm vb b1 bs1 m bk ik msg spkId g.baseKey.cap g.baseKey.ptr g.identityKey.cap
      g.identityKey.ptr g.message.cap g.message.ptr kc kp kl pReg.1.1 pReg.1.2 pOpk.1.1
      pOpk.1.2 pKpk.1.1 pKpk.1.2 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO pReg.2 pOpk.2
      pKpk.2 hstm hbkC hikC hmsgC hpcm hrunm)

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

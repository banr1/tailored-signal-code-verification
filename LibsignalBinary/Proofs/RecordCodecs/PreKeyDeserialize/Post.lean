/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# `PreKeyRecord::deserialize` Post-Loop `Ok` Packing and Cleanup Tails

Result/frame memory packing helpers, shared `Ok` tail (`+0x190 .. +0x1a4`), empty-input fast path
(`+0x174 .. +0x18c`), and `DecodeError` / `Vec<u8>` deallocation tails.
-/

@[expose] public section

namespace CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## Memory packing & unpacking helpers for result and frame -/

theorem extractLsb_lo_64 (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_kernel

theorem extractLsb_hi_64 (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_kernel

theorem vecU8Buf_zero_elim (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A 0#64 ptr bs ⊢ emp := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => ?_
  have hle := h.1
  have hbs : bs = [] := by simp at hle; exact hle
  subst hbs
  exact Entails.refl _

theorem emp_entails_two_vecU8Buf_zero (A : RustAlloc) :
    emp ⊢ vecU8Buf A 0#64 1#64 [] ∗ vecU8Buf A 0#64 1#64 [] := by
  have hz : emp ⊢ vecU8Buf A 0#64 1#64 [] := by
    unfold vecU8Buf
    rw [pure_true_emp ⟨by decide, by decide, by decide⟩, emp_sepConj]
    exact Entails.refl _
  rw [← emp_sepConj emp]
  exact sepConj_mono hz hz

theorem pkMemRegion40_unpack (sp' : BitVec 64) :
    memRegion sp' 40 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗
        ((sp' + 16#64) ↦₆₄ w2) ∗ ((sp' + 24#64) ↦₆₄ w3) ∗
        memRegion (sp' + 32#64) 8 := by
  rw [ProofLib.memRegion_split sp' 8 32 (by decide),
    ProofLib.memRegion_split (sp' + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro w0)
  refine Entails.trans ?_ (Entails.sepExists_intro w1)
  refine Entails.trans ?_ (Entails.sepExists_intro w2)
  refine Entails.trans ?_ (Entails.sepExists_intro w3)
  exact Entails.refl _

theorem pkMemRegion40_pack (sp' w0 w1 w2 w3 : BitVec 64) :
    (sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗
      ((sp' + 16#64) ↦₆₄ w2) ∗ ((sp' + 24#64) ↦₆₄ w3) ∗
      memRegion (sp' + 32#64) 8 ⊢ memRegion sp' 40 := by
  rw [show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) by decide,
    ProofLib.memRegion_split sp' 8 32 (by decide),
    ProofLib.memRegion_split (sp' + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))

theorem pkMemRegion56_unpack (a : BitVec 64) :
    memRegion a 56 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
      ∃∗ r3 : BitVec 64, ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r6 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2) ∗
        ((a + 24#64) ↦₆₄ r3) ∗ ((a + 32#64) ↦₆₄ r4) ∗
        ((a + 40#64) ↦₆₄ r5) ∗ ((a + 48#64) ↦₆₄ r6) := by
  rw [ProofLib.memRegion_split a 8 48 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun r6 => Entails.sepExists_elim fun r5 =>
    Entails.sepExists_elim fun r4 => Entails.sepExists_elim fun r3 =>
    Entails.sepExists_elim fun r2 => Entails.sepExists_elim fun r1 =>
    Entails.sepExists_elim fun r0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro r0)
  refine Entails.trans ?_ (Entails.sepExists_intro r1)
  refine Entails.trans ?_ (Entails.sepExists_intro r2)
  refine Entails.trans ?_ (Entails.sepExists_intro r3)
  refine Entails.trans ?_ (Entails.sepExists_intro r4)
  refine Entails.trans ?_ (Entails.sepExists_intro r5)
  refine Entails.trans ?_ (Entails.sepExists_intro r6)
  exact Entails.refl _

theorem pkMemRegion56_err_unpack (a : BitVec 64) :
    memRegion a 56 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r6 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ memRegion (a + 16#64) 24 ∗
        ((a + 40#64) ↦₆₄ r5) ∗ ((a + 48#64) ↦₆₄ r6) := by
  rw [ProofLib.memRegion_split a 8 48 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 24 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 24#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun r6 => Entails.sepExists_elim fun r5 =>
    Entails.sepExists_elim fun r1 => Entails.sepExists_elim fun r0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro r0)
  refine Entails.trans ?_ (Entails.sepExists_intro r1)
  refine Entails.trans ?_ (Entails.sepExists_intro r5)
  refine Entails.trans ?_ (Entails.sepExists_intro r6)
  exact Entails.refl _

theorem pkStruct56_pack (sp' pubCap pubPtr pubLen privCap privPtr privLen : BitVec 64)
    (idVal padVal : BitVec 32) :
    vecHeader (sp' + 56#64) pubCap pubPtr pubLen ∗
      vecHeader (sp' + 80#64) privCap privPtr privLen ∗
      ((sp' + 104#64) ↦₃₂ idVal) ∗ ((sp' + 108#64) ↦₃₂ padVal) ⊢
      memRegion (sp' + 56#64) 56 := by
  have hp8 : ((sp' + 104#64) ↦₃₂ idVal) ∗ ((sp' + 108#64) ↦₃₂ padVal) ⊢
      memRegion (sp' + 104#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      pointsTo32_pair_entails_memRegion8 (sp' + 104#64) idVal padVal
  rw [show (56 : Nat) = 24 + (24 + 8) by decide,
    ProofLib.memRegion_split (sp' + 56#64) 24 32 (by decide),
    ProofLib.memRegion_split (sp' + 56#64 + 24#64) 24 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (vecHeader_entails_memRegion24 (sp' + 56#64) pubCap pubPtr pubLen)
    (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 80#64) privCap privPtr privLen) hp8)

theorem pkMemRegion160_pack (sp' : BitVec 64) :
    memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗
      memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 112#64) 48 ⊢
      memRegion sp' 160 := by
  rw [show (160 : Nat) = 40 + (16 + (56 + 48)) by decide,
    ProofLib.memRegion_split sp' 40 120 (by decide),
    ProofLib.memRegion_split (sp' + 40#64) 16 104 (by decide),
    ProofLib.memRegion_split (sp' + 40#64 + 16#64) 56 48 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem pkSpeInvalidProto56_intro (A : RustAlloc) (x19 r5 r6 : BitVec 64)
    {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding) :
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
      memRegion (x19 + 16#64) 24 ∗
      ((x19 + 40#64) ↦₆₄ r5) ∗ ((x19 + 48#64) ↦₆₄ r6) ⊢
      preKeyResultAt A x19 out := by
  rw [herr]
  dsimp only [preKeyResultAt, errResultAt, speAt]
  have h0 : (56 : Nat) - 56 = 0 := rfl
  rw [h0, memRegion_zero, sepConj_emp]
  have h40 : memRegion (x19 + 8#64 + 8#64) 40 =
      memRegion (x19 + 16#64) 24 ∗ memRegion (x19 + 40#64) 8 ∗ memRegion (x19 + 48#64) 8 := by
    have ha1 : x19 + 8#64 + 8#64 = x19 + 16#64 := by bv_omega
    rw [ha1, show (40 : Nat) = 24 + (8 + 8) by decide,
      ProofLib.memRegion_split (x19 + 16#64) 24 16 (by decide),
      ProofLib.memRegion_split (x19 + 16#64 + 24#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h40]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))

theorem pkRecordOk56_intro (A : RustAlloc) (g : PreKeyGhost) (x19 : BitVec 64)
    (m : PreKeyRecordStructure) (pad32 : BitVec 32)
    {out : Except SignalProtocolError PreKeyRecord}
    (hok : out = .ok ⟨m⟩) :
    (x19 ↦₆₄ g.pub.cap) ∗ ((x19 + 8#64) ↦₆₄ g.pub.ptr) ∗
      ((x19 + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
      ((x19 + 24#64) ↦₆₄ g.priv.cap) ∗ ((x19 + 32#64) ↦₆₄ g.priv.ptr) ∗
      ((x19 + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
      ((x19 + 48#64) ↦₆₄ (pad32 ++ m.id)) ∗
      vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ∗
      vecU8Buf A g.priv.cap g.priv.ptr m.privateKey ⊢
      preKeyResultAt A x19 out := by
  rw [hok]
  dsimp only [preKeyResultAt]
  refine Entails.trans ?_ (preKeyStructAt_entails_recordAt A g x19 m)
  unfold preKeyStructAt
  rw [vecU8At_eq_header_buf, vecU8At_eq_header_buf]
  dsimp only [vecHeader]
  have hp : ((x19 + 48#64) ↦₆₄ (pad32 ++ m.id)) =
      ((x19 + 0x30#64) ↦₃₂ m.id) ∗ ((x19 + 0x34#64) ↦₃₂ pad32) := by
    have hs := (pointsTo32_pair (x19 + 48#64) m.id pad32).symm
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using hs
  rw [hp]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right
          (pointsTo32_entails_memRegion (x19 + 52#64) pad32))))))))))
  apply entails_of_eq; ac_rfl

/-! ## Shared `Ok` packing tail `+0x190..+0x1a4` + `+0x220` → `+0x224` -/

theorem pack_tail_190_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 ptr w0 w1 : BitVec 64} {pad32 : BitVec 32}
    {g : PreKeyGhost} {m : PreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord}
    (hok : out = .ok ⟨m⟩)
    (hst : PkEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x190#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx8 : s.readReg64 .x8 = g.pub.cap)
    (hx0 : s.readReg64 .x0 = g.pub.ptr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 m.publicKey.length)
    (hx9 : s.readReg64 .x9 = g.priv.cap)
    (hx11 : s.readReg64 .x11 = g.priv.ptr) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      ((sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗
        ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
        ((sp' + 24#64) ↦₆₄ (pad32 ++ m.id)) ∗
        memRegion (sp' + 32#64) 8 ∗
        memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 56#64) 56 ∗
        memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        memRegion x19 56 ∗
        vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ∗
        vecU8Buf A g.priv.cap g.priv.ptr m.privateKey ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr, hsaved⟩
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 400 24
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 544 4
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (pkMemRegion56_unpack x19))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
    Wire.SepWPp.exists_pre fun r2 => Wire.SepWPp.exists_pre fun r3 =>
    Wire.SepWPp.exists_pre fun r4 => Wire.SepWPp.exists_pre fun r5 =>
    Wire.SepWPp.exists_pre fun r6 => ?_
  have h19 : s.readReg64 (Reg.gpr 19#5) = x19 := hx19
  have h8 : s.readReg64 (Reg.gpr 8#5) = g.pub.cap := hx8
  have h0 : s.readReg64 (Reg.gpr 0#5) = g.pub.ptr := hx0
  have h10 : s.readReg64 (Reg.gpr 10#5) = BitVec.ofNat 64 m.publicKey.length := hx10
  have h9 : s.readReg64 (Reg.gpr 9#5) = g.priv.cap := hx9
  have h11 : s.readReg64 (Reg.gpr 11#5) = g.priv.ptr := hx11
  refine Wire.SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hF1, hsym1, by simp [htr, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved.x24,
     by simpa [arm64_norm] using hsaved.x25,
     by simpa [arm64_norm] using hsaved.x26,
     by simpa [arm64_norm] using hsaved.x27,
     by simpa [arm64_norm] using hsaved.x28⟩⟩, ?_⟩
  simp only [arm64_norm]
  have h40 := pkMemRegion40_pack sp'
    (BitVec.ofNat 64 m.privateKey.length) (pad32 ++ m.id)
    (BitVec.ofNat 64 m.privateKey.length) (pad32 ++ m.id)
  have h160 := pkMemRegion160_pack sp'
  have hrec := pkRecordOk56_intro A g x19 m pad32 hok
  unfold pkEpilogueMem
  refine Entails.trans ?_
    (sepConj_mono h160 (sepConj_mono_right (sepConj_mono_left hrec)))
  refine Entails.trans ?_
    (sepConj_mono_left (sepConj_mono_left h40))
  apply entails_of_eq; ac_rfl

/-! ## Fast empty path `+0x174..+0x18c` → `+0x190` → `+0x224` -/

theorem fast_empty_174_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {out : Except SignalProtocolError PreKeyRecord}
    (hok : out = .ok ⟨PreKeyRecordStructure.empty⟩)
    (hst : PkEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x174#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = sp' + 56#64) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (memRegion sp' 40 ∗
        memRegion (sp' + 40#64) 16 ∗
        vecHeader (sp' + 56#64) 0#64 1#64 0#64 ∗
        vecHeader (sp' + 80#64) 0#64 1#64 0#64 ∗
        ((sp' + 104#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 108#64) 4 ∗
        memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        memRegion x19 56 ∗
        (ptr ↦ₛ ([] : List (BitVec 8))) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePost img A s0 sp' x19 ptr [] out)
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr, hsaved⟩
  have hnext := @pack_tail_190_wp img A ext s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 372 28
  dsimp only [tripleRatchetProgAtExt] at hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (pkMemRegion40_unpack sp')
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (memRegion_four_entails (sp' + 108#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun pad32 => Wire.SepWPp.exists_pre fun w0 =>
    Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w2 =>
    Wire.SepWPp.exists_pre fun w3 => ?_
  have hp104 : ((sp' + 104#64) ↦₃₂ 0#32) ∗ ((sp' + 108#64) ↦₃₂ pad32) =
      ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (sp' + 104#64) 0#32 pad32
  refine Wire.SepWPp.mono_pre
    (P' := (sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗
      ((sp' + 16#64) ↦₆₄ w2) ∗ ((sp' + 24#64) ↦₆₄ w3) ∗
      memRegion (sp' + 32#64) 8 ∗
      memRegion (sp' + 40#64) 16 ∗
      ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ 1#64) ∗ ((sp' + 72#64) ↦₆₄ 0#64) ∗
      ((sp' + 80#64) ↦₆₄ 0#64) ∗ ((sp' + 88#64) ↦₆₄ 1#64) ∗ ((sp' + 96#64) ↦₆₄ 0#64) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) ∗
      memRegion (sp' + 112#64) 48 ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      memRegion x19 56 ∗
      (ptr ↦ₛ ([] : List (BitVec 8))) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (by
      dsimp only [vecHeader]
      rw [← sepConj_assoc ((sp' + 104#64) ↦₃₂ 0#32), hp104]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      exact Entails.refl _) ?_
  have h19 : s.readReg64 (Reg.gpr 19#5) = x19 := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hx20
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (400)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hnext (g := ⟨⟨0#64, 1#64⟩, ⟨0#64, 1#64⟩⟩) (m := PreKeyRecordStructure.empty)
      (w0 := w0) (w1 := w1) (pad32 := pad32) hok
      ⟨by simp [hsp_eq, arm64_norm],
       by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hF1, hsym1, by simp [htr, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved.x24,
        by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26,
        by simpa [arm64_norm] using hsaved.x27,
        by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [h19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [PreKeyRecordStructure.empty, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
  simp only [PreKeyRecordStructure.empty, arm64_norm]
  have h56 : ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ 1#64) ∗ ((sp' + 72#64) ↦₆₄ 0#64) ∗
      ((sp' + 80#64) ↦₆₄ 0#64) ∗ ((sp' + 88#64) ↦₆₄ 1#64) ∗ ((sp' + 96#64) ↦₆₄ 0#64) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) ⊢ memRegion (sp' + 56#64) 56 := by
    rw [← hp104]
    simpa [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      pkStruct56_pack sp' 0#64 1#64 0#64 0#64 1#64 0#64 0#32 pad32
  have hz2 := emp_entails_two_vecU8Buf_zero A
  rw [← emp_sepConj (A.pool ∗ stackAt sp' (skipFieldStackX 100)), ← sepConj_assoc (vecU8Buf A 0#64 1#64 [])]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono h56
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hz2)))))))))))
  apply entails_of_eq; ac_rfl

/-! ## Loop `Ok` exit `+0x23c..+0x254` → `+0x190` → `+0x224` -/

theorem post_ok_23c_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {m : PreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord}
    (hok : out = .ok ⟨m⟩)
    (hst : PkEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x23c#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = sp' + 56#64) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (memRegion sp' 40 ∗
        memRegion (sp' + 40#64) 16 ∗
        preKeyStructOf A (sp' + 56#64) m ∗
        memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr, hsaved⟩
  unfold preKeyStructOf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun g => ?_
  rw [preKeyStructAt_split_pub A g sp' m,
    vecU8At_eq_header_buf A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey,
    vecU8At_eq_header_buf A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey]
  simp only [sepConj_assoc]
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (pkMemRegion40_unpack sp')
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (memRegion_four_entails (sp' + 108#64)))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun pad32 => Wire.SepWPp.exists_pre fun w0 =>
    Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w2 =>
    Wire.SepWPp.exists_pre fun w3 => ?_
  have hpub_bounds : vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ⊢
      ⌜g.pub.cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A g.pub.cap g.pub.ptr m.publicKey := by
    unfold vecU8Buf
    refine Entails.pure_left fun h => ?_
    rw [pure_true_emp h, pure_true_emp h.2.1, emp_sepConj, emp_sepConj]
    exact Entails.refl _
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hpub_bounds)))))))) ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hpub_lt => ?_
  have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt g.pub.cap hpub_lt
  have hp104 : ((sp' + 104#64) ↦₃₂ m.id) ∗ ((sp' + 108#64) ↦₃₂ pad32) =
      ((sp' + 104#64) ↦₆₄ (pad32 ++ m.id)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (sp' + 104#64) m.id pad32
  have hnext := @pack_tail_190_wp img A ext s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 572 28
  dsimp only [tripleRatchetProgAtExt] at hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  refine Wire.SepWPp.mono_pre
    (P' := (sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗
      ((sp' + 16#64) ↦₆₄ w2) ∗ ((sp' + 24#64) ↦₆₄ w3) ∗
      memRegion (sp' + 32#64) 8 ∗
      memRegion (sp' + 40#64) 16 ∗
      ((sp' + 56#64) ↦₆₄ g.pub.cap) ∗ ((sp' + 64#64) ↦₆₄ g.pub.ptr) ∗
      ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
      ((sp' + 80#64) ↦₆₄ g.priv.cap) ∗ ((sp' + 88#64) ↦₆₄ g.priv.ptr) ∗
      ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ m.id)) ∗
      vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ∗
      vecU8Buf A g.priv.cap g.priv.ptr m.privateKey ∗
      memRegion (sp' + 112#64) 48 ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      memRegion x19 56 ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (by
      dsimp only [vecHeader]
      rw [← sepConj_assoc ((sp' + 104#64) ↦₃₂ m.id), hp104]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      apply entails_of_eq; ac_rfl) ?_
  have h19 : s.readReg64 (Reg.gpr 19#5) = x19 := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hx20
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (400)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hnext (g := g) (m := m) (w0 := w0) (w1 := w1) (pad32 := pad32) hok
      ⟨by simp [hsp_eq, arm64_norm],
       by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hF1, hsym1, by simp [htr, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved.x24,
        by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26,
        by simpa [arm64_norm] using hsaved.x27,
        by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [h19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
  simp only [arm64_norm]
  have h56 : ((sp' + 56#64) ↦₆₄ g.pub.cap) ∗ ((sp' + 64#64) ↦₆₄ g.pub.ptr) ∗
      ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
      ((sp' + 80#64) ↦₆₄ g.priv.cap) ∗ ((sp' + 88#64) ↦₆₄ g.priv.ptr) ∗
      ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ m.id)) ⊢ memRegion (sp' + 56#64) 56 := by
    rw [← hp104]
    simpa [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      pkStruct56_pack sp' g.pub.cap g.pub.ptr (BitVec.ofNat 64 m.publicKey.length)
        g.priv.cap g.priv.ptr (BitVec.ofNat 64 m.privateKey.length) m.id pad32
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56)))))))
  apply entails_of_eq; ac_rfl

/-! ## Error cleanup chain `+0x1d0 → +0x1f4 → +0x210 → +0x224` -/

theorem cleanup_err_210_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {bs : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding)
    (hst : PkEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x210#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = err)
    (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = speWord 2) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (memRegion sp' 40 ∗
        memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 56#64) 56 ∗
        memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        decodeErrorAt A err ∗
        memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr, hsaved⟩
  have hcall := dropDecodeError_ok_sub d
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 528 20
  dsimp only [tripleRatchetProgAtExt] at hcall hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have hstack := stackAt_sub_split sp' dropDecodeErrorStackX (skipFieldStackX 100)
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (pkMemRegion40_unpack sp')
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkMemRegion56_err_unpack x19)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun w0 => Wire.SepWPp.exists_pre fun w1 =>
    Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w3 =>
    Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
    Wire.SepWPp.exists_pre fun r5 => Wire.SepWPp.exists_pre fun r6 => ?_
  have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]") -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_noPanic_tryFrom err hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (532)) (by simp [arm64_norm])
    (T := decodeErrorAt A err ∗ A.pool ∗ stackAt sp' dropDecodeErrorStackX)
    (φ := err = err)
    (by simp [dropDecodeErrorSpecX, hsp_eq, h0, arm64_norm])
    rfl
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [dropDecodeErrorSpecX]
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x19 := by simpa [hx19, arm64_norm] using hcs2.1
  have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = speWord 2 := by simpa [hx22, arm64_norm] using hcs2.2.2.2.1
  have hsaved2 : PkSavedRegs s0 s2 :=
    ⟨by simpa [hsaved.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
     by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine Wire.SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine ⟨⟨by simp [hsp2_eq, arm64_norm],
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hF3, hsym3, by simp [htr2, htr, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved2.x24,
     by simpa [arm64_norm] using hsaved2.x25,
     by simpa [arm64_norm] using hsaved2.x26,
     by simpa [arm64_norm] using hsaved2.x27,
     by simpa [arm64_norm] using hsaved2.x28⟩⟩, ?_⟩
  simp only [arm64_norm]
  have h40 := pkMemRegion40_pack sp' r0 r1 r5 r6
  have h160 := pkMemRegion160_pack sp'
  have herr56 := pkSpeInvalidProto56_intro A x19 r0 r1 herr
  unfold pkEpilogueMem
  refine Entails.trans ?_
    (sepConj_mono h160 (sepConj_mono_right (sepConj_mono_left herr56)))
  refine Entails.trans ?_
    (sepConj_mono_left (sepConj_mono_left h40))
  apply entails_of_eq; rw [hstack, hsp_eq]; dsimp only [errTag, skipFieldStackX, dropDecodeErrorStackX, extHookStack]; ac_rfl

theorem cleanup_priv_1f4_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr err privCap privPtr : BitVec 64}
    {privBs bs : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding)
    (hst : PkEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x1f4#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = err)
    (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = speWord 2)
    (hx20 : s.readReg64 .x20 = privCap)
    (hx21 : s.readReg64 .x21 = privPtr) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (vecU8Buf A privCap privPtr privBs ∗
        memRegion sp' 40 ∗
        memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 56#64) 56 ∗
        memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        decodeErrorAt A err ∗
        memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr, hsaved⟩
  have hnext := @cleanup_err_210_wp img A ext d s0
  by_cases hcap : privCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_zero_elim A privPtr privBs)) ?_
    rw [emp_sepConj]
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
      img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 500 4
    dsimp only [tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
    examples_hide_fetches
    have h20 : s.readReg64 (Reg.gpr 20#5) = 0#64 := hx20
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (528)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact hnext (sp' := sp') (x19 := x19) (ptr := ptr) (err := err) (bs := bs) (out := out) herr
      ⟨by simp [hsp_eq, arm64_norm],
       by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hF1, hsym1, by simp [htr, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved.x24,
        by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26,
        by simpa [arm64_norm] using hsaved.x27,
        by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm]) (by simp [hx22, arm64_norm])
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A privCap privPtr privBs hcap)) ?_
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := dealloc_ok_sub hC
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
      img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 500 28
    dsimp only [tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
    examples_hide_fetches
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
    have h20 : s.readReg64 (Reg.gpr 20#5) = privCap := hx20
    have h21 : s.readReg64 (Reg.gpr 21#5) = privPtr := hx21
    have hbeq : (privCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine Wire.SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_noPanic_tryFrom (privPtr, privCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
      (ret_pc := entry + bv% (524)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live privPtr privCap.toNat 1 ∗ memRegion privPtr privCap.toNat ∗
        stackAt sp' extHookStack)
      (φ := privPtr = privPtr ∧ privCap.toNat = privCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk privCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, hsp_eq, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hx19, arm64_norm] using hcs2.1
    have hx22_2 : s2.readReg64 .x22 = speWord 2 := by simpa [hx22, arm64_norm] using hcs2.2.2.2.1
    have hx23_2 : s2.readReg64 .x23 = err := by simpa [h0, arm64_norm] using hcs2.2.2.2.2.1
    have hsaved2 : PkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
       by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (528)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (hnext (sp' := sp') (x19 := x19) (ptr := ptr) (err := err) (bs := bs) (out := out) herr
        ⟨by simp [hsp2_eq, arm64_norm],
         by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hF3, hsym3, by simp [htr2, htr, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved2.x24,
          by simpa [arm64_norm] using hsaved2.x25,
          by simpa [arm64_norm] using hsaved2.x26,
          by simpa [arm64_norm] using hsaved2.x27,
          by simpa [arm64_norm] using hsaved2.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        (by simp [arm64_norm])
        (by simp [hx19_2, arm64_norm])
        (by simp [hx22_2, arm64_norm]))
    simp only [hsp_eq, arm64_norm]
    apply entails_of_eq
    rw [hstack]
    ac_rfl

theorem post_err_1d0_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {mErr : PreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding)
    (hst : PkEpilogueState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x1d0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = err)
    (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = speWord 2) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (preKeyStructOf A (sp' + 56#64) mErr ∗
        memRegion sp' 40 ∗
        memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        decodeErrorAt A err ∗
        memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr, hsaved⟩
  unfold preKeyStructOf
  simp only [sepExists_sepConj_left]
  refine Wire.SepWPp.exists_pre fun g => ?_
  rcases g with ⟨⟨pubCap, pubPtr⟩, ⟨privCap, privPtr⟩⟩
  rw [preKeyStructAt_split_pub A ⟨⟨pubCap, pubPtr⟩, ⟨privCap, privPtr⟩⟩ sp' mErr,
    vecU8At_eq_header_buf A (sp' + 56#64) pubCap pubPtr mErr.publicKey,
    vecU8At_eq_header_buf A (sp' + 80#64) privCap privPtr mErr.privateKey]
  simp only [sepConj_assoc]
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (memRegion_four_entails (sp' + 108#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun pad32 => ?_
  have h56_pack := pkStruct56_pack sp' pubCap pubPtr (BitVec.ofNat 64 mErr.publicKey.length)
    privCap privPtr (BitVec.ofNat 64 mErr.privateKey.length) mErr.id pad32
  have hnext := @cleanup_priv_1f4_wp img A ext hC d s0
  by_cases hcap : pubCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_left (vecU8Buf_zero_elim A pubPtr mErr.publicKey))) ?_
    simp only [emp_sepConj]
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
      img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 464 12
    dsimp only [tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
    examples_hide_fetches
    refine Wire.SepWPp.mono_pre
      (P' := ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ pubPtr) ∗
        ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 mErr.publicKey.length) ∗
        ((sp' + 80#64) ↦₆₄ privCap) ∗ ((sp' + 88#64) ↦₆₄ privPtr) ∗
        ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 mErr.privateKey.length) ∗
        vecU8Buf A privCap privPtr mErr.privateKey ∗
        ((sp' + 104#64) ↦₃₂ mErr.id) ∗ ((sp' + 108#64) ↦₃₂ pad32) ∗
        memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ decodeErrorAt A err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (by dsimp only [vecHeader]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _) ?_
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (500)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.mono_pre ?_
      (hnext (sp' := sp') (x19 := x19) (ptr := ptr) (err := err)
        (privCap := privCap) (privPtr := privPtr) (privBs := mErr.privateKey)
        (bs := bs) (out := out) herr
        ⟨by simp [hsp_eq, arm64_norm],
         by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hF1, hsym1, by simp [htr, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x24,
          by simpa [arm64_norm] using hsaved.x25,
          by simpa [arm64_norm] using hsaved.x26,
          by simpa [arm64_norm] using hsaved.x27,
          by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm]) (by simp [hx22, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]))
    dsimp only [vecHeader] at h56_pack
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h56_pack
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56_pack))))
    apply entails_of_eq; ac_rfl
  · refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_left (vecU8Buf_dealloc A pubCap pubPtr mErr.publicKey hcap))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := dealloc_ok_sub hC
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
      img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 464 36
    dsimp only [tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
    examples_hide_fetches
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    have hbeq : (pubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
    refine Wire.SepWPp.mono_pre
      (P' := ((sp' + 56#64) ↦₆₄ pubCap) ∗ ((sp' + 64#64) ↦₆₄ pubPtr) ∗
        ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 mErr.publicKey.length) ∗
        A.live pubPtr pubCap.toNat 1 ∗ memRegion pubPtr pubCap.toNat ∗
        ((sp' + 80#64) ↦₆₄ privCap) ∗ ((sp' + 88#64) ↦₆₄ privPtr) ∗
        ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 mErr.privateKey.length) ∗
        vecU8Buf A privCap privPtr mErr.privateKey ∗
        ((sp' + 104#64) ↦₃₂ mErr.id) ∗ ((sp' + 108#64) ↦₃₂ pad32) ∗
        memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ decodeErrorAt A err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (by dsimp only [vecHeader]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _) ?_
    refine Wire.SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_noPanic_tryFrom (pubPtr, pubCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
      (ret_pc := entry + bv% (496)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live pubPtr pubCap.toNat 1 ∗ memRegion pubPtr pubCap.toNat ∗
        stackAt sp' extHookStack)
      (φ := pubPtr = pubPtr ∧ pubCap.toNat = pubCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk pubCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, hsp_eq, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hx19, arm64_norm] using hcs2.1
    have hx20_2 : s2.readReg64 .x20 = privCap := by simpa [hsp_eq, arm64_norm] using hcs2.2.1
    have hx21_2 : s2.readReg64 .x21 = privPtr := by simpa [hsp_eq, arm64_norm] using hcs2.2.2.1
    have hx22_2 : s2.readReg64 .x22 = speWord 2 := by simpa [hx22, arm64_norm] using hcs2.2.2.2.1
    have hx23_2 : s2.readReg64 .x23 = err := by simpa [h0, arm64_norm] using hcs2.2.2.2.2.1
    have hsaved2 : PkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
       by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (500)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (hnext (sp' := sp') (x19 := x19) (ptr := ptr) (err := err)
        (privCap := privCap) (privPtr := privPtr) (privBs := mErr.privateKey)
        (bs := bs) (out := out) herr
        ⟨by simp [hsp2_eq, arm64_norm],
         by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hF3, hsym3, by simp [htr2, htr, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved2.x24,
          by simpa [arm64_norm] using hsaved2.x25,
          by simpa [arm64_norm] using hsaved2.x26,
          by simpa [arm64_norm] using hsaved2.x27,
          by simpa [arm64_norm] using hsaved2.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        (by simp [arm64_norm]) (by simp [hx19_2, arm64_norm]) (by simp [hx22_2, arm64_norm])
        (by simp [hx20_2, arm64_norm]) (by simp [hx21_2, arm64_norm]))
    rw [hstack]
    simp only [hsp_eq, arm64_norm]
    dsimp only [vecHeader] at h56_pack
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h56_pack
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56_pack))))
    apply entails_of_eq; ac_rfl

/-! ## Stack split & epilogue `+0x224..+0x238` (`548..568` → `s0.readReg64 .x30`) -/

abbrev pkSubStack : Nat := smallRootStack - 224

theorem pkSpAligned_sub224 {s0 : State} (hsp0 : s0.spAligned = true) :
    ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned] at hsp0
  revert hsp0
  generalize s0.sp = sp
  intro hsp0
  bv_kernel

theorem pkFrame64_pack (sp' bufPtr : BitVec 64) (s0 : State) :
    pkCalleeSavedAt sp' s0 ∗ ((sp' + 184#64) ↦₆₄ bufPtr) ⊢
      memRegion (sp' + 160#64) 64 := by
  unfold pkCalleeSavedAt
  rw [ProofLib.memRegion_split (sp' + 160#64) 8 56 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (sp' + 160#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.trans ?_
    (sepConj_mono (pointsTo64_entails_memRegion (sp' + 160#64) (s0.readReg64 .x29))
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 168#64) (s0.readReg64 .x30))
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 176#64) (s0.readReg64 .x23))
          (sepConj_mono (pointsTo64_entails_memRegion (sp' + 184#64) bufPtr)
            (sepConj_mono (pointsTo64_entails_memRegion (sp' + 192#64) (s0.readReg64 .x22))
              (sepConj_mono (pointsTo64_entails_memRegion (sp' + 200#64) (s0.readReg64 .x21))
                (sepConj_mono (pointsTo64_entails_memRegion (sp' + 208#64) (s0.readReg64 .x20))
                  (pointsTo64_entails_memRegion (sp' + 216#64) (s0.readReg64 .x19)))))))))
  apply entails_of_eq; ac_rfl

theorem pkStack_smallRoot_split (sp : BitVec 64) :
    stackAt sp smallRootStack =
      stackAt (sp - 224#64) pkSubStack ∗
        memRegion (sp - 224#64) 160 ∗
        memRegion (sp - 224#64 + 160#64) 64 := by
  have h1 := stackAt_sub_split sp 224 smallRootStack
  have h2 : memRegion (sp - BitVec.ofNat 64 smallRootStack) pkSubStack =
      stackAt (sp - 224#64) pkSubStack := by
    unfold stackAt
    have ha : sp - BitVec.ofNat 64 smallRootStack =
        sp - 224#64 - BitVec.ofNat 64 pkSubStack := by
      change sp - 65536#64 = sp - 224#64 - 65312#64
      bv_omega
    rw [ha]
  have h3 : stackAt sp 224 =
      memRegion (sp - 224#64) 160 ∗ memRegion (sp - 224#64 + 160#64) 64 := by
    unfold stackAt
    exact ProofLib.memRegion_split (sp - 224#64) 160 64 (by decide)
  rw [h1, h2, h3]

theorem pkSubStack_split (sp' : BitVec 64) :
    stackAt sp' pkSubStack =
      stackAt sp' (skipFieldStackX 100) ∗
        memRegion (sp' - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100) := by
  have hs := stackAt_sub_split sp' (skipFieldStackX 100) pkSubStack
  rw [hs]
  ac_rfl

theorem pkStack_smallRoot_unsplit (sp : BitVec 64) (s0 : State) :
    memRegion (sp - 224#64) 160 ∗
      pkCalleeSavedAt (sp - 224#64) s0 ∗
      ((sp - 224#64 + 184#64) ↦₆₄ (sp - 224#64 + 40#64)) ∗
      stackAt (sp - 224#64) (skipFieldStackX 100) ∗
      memRegion (sp - 224#64 - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100) ⊢
      stackAt sp smallRootStack := by
  rw [pkStack_smallRoot_split sp, pkSubStack_split (sp - 224#64)]
  have hf64 := pkFrame64_pack (sp - 224#64) (sp - 224#64 + 40#64) s0
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right hf64))
  apply entails_of_eq; ac_rfl

theorem epilogue_224_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : DecodeGhost} {s0 s : State}
    (hst : PkEpilogueState img s0 (s0.sp - 224#64) s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64)
    (hrun : s.status = .Running) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (pkEpilogueMem A (s0.sp - 224#64) x.ret x.bytesA x.bytes
          (PreKeyRecord.deserialize x.bytes) ∗
        pkCalleeSavedAt (s0.sp - 224#64) s0 ∗
        memRegion (s0.sp - 224#64 - BitVec.ofNat 64 pkSubStack)
          (pkSubStack - skipFieldStackX 100))
      (fun sf Pf =>
        sf.sp = s0.sp ∧
        (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyDeserializeSpec A img).post x s0 sf))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, _hsp, hF, hsym, htr, hsaved⟩
  unfold pkEpilogueMem pkCalleeSavedAt
  simp only [sepConj_assoc]
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 548 24
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  refine Wire.SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro _ _
  refine ⟨by simp [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm],
      by simp [arm64_norm],
      by simp [arm64_norm],
      by simp [arm64_norm],
      by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved.x24,
      by simpa [arm64_norm] using hsaved.x25,
      by simpa [arm64_norm] using hsaved.x26,
      by simpa [arm64_norm] using hsaved.x27,
      by simpa [arm64_norm] using hsaved.x28,
      by simp [arm64_norm],
      hv⟩
  · dsimp only [preKeyDeserializeSpec, Spec.inImage]
    rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := pkStack_smallRoot_unsplit s0.sp s0
    unfold pkCalleeSavedAt at hstk
    simp only [arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk)))
    apply entails_of_eq; ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` Ok-Packing & Epilogue (Block `65`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

theorem pack_tail_190_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr w0 w1 : BitVec 64} {pad32 : BitVec 32}
    {g : PreKeyGhost} {m : PreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord} (hok : out = .ok ⟨m⟩)
    (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (400)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx8 : s.readReg64 .x8 = g.pub.cap)
    (hx0 : s.readReg64 .x0 = g.pub.ptr) (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 m.publicKey.length)
    (hx9 : s.readReg64 .x9 = g.priv.cap) (hx11 : s.readReg64 .x11 = g.priv.ptr) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      ((sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
        ((sp' + 24#64) ↦₆₄ (pad32 ++ m.id)) ∗ memRegion (sp' + 32#64) 8 ∗ memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        memRegion x19 56 ∗ vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ∗
        vecU8Buf A g.priv.cap g.priv.ptr m.privateKey ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (pkMemRegion56_unpack x19))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
    Wire.SepWPp.exists_pre fun r2 => Wire.SepWPp.exists_pre fun r3 =>
    Wire.SepWPp.exists_pre fun r4 => Wire.SepWPp.exists_pre fun r5 => Wire.SepWPp.exists_pre fun r6 => ?_
  have h19 : s.readReg64 (Reg.gpr 19#5) = x19 := hx19
  have h8 : s.readReg64 (Reg.gpr 8#5) = g.pub.cap := hx8
  have h0 : s.readReg64 (Reg.gpr 0#5) = g.pub.ptr := hx0
  have h10 : s.readReg64 (Reg.gpr 10#5) = BitVec.ofNat 64 m.publicKey.length := hx10
  have h9 : s.readReg64 (Reg.gpr 9#5) = g.priv.cap := hx9
  have h11 : s.readReg64 (Reg.gpr 11#5) = g.priv.ptr := hx11
  refine sepWPp_of_sepWP_end_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hcrl1, by simp [htr, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
     by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27,
     by simpa [arm64_norm] using hsaved.x28⟩⟩, ?_⟩
  simp only [arm64_norm]
  have h40 := pkMemRegion40_pack sp' (BitVec.ofNat 64 m.privateKey.length) (pad32 ++ m.id)
    (BitVec.ofNat 64 m.privateKey.length) (pad32 ++ m.id)
  unfold pkEpilogueMem
  refine Entails.trans ?_ (sepConj_mono (pkMemRegion160_pack sp') (sepConj_mono_right (sepConj_mono_left (pkRecordOk56_intro A g x19 m pad32 hok))))
  refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left h40))
  apply entails_of_eq; ac_rfl

theorem fast_empty_174_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64} {out : Except SignalProtocolError PreKeyRecord}
    (hok : out = .ok ⟨PreKeyRecordStructure.empty⟩) (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (372)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx20 : s.readReg64 .x20 = sp' + 56#64) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ vecHeader (sp' + 56#64) 0#64 1#64 0#64 ∗
        vecHeader (sp' + 80#64) 0#64 1#64 0#64 ∗ ((sp' + 104#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 108#64) 4 ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ memRegion x19 56 ∗
        (ptr ↦ₛ ([] : List (BitVec 8))) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A s0 sp' x19 ptr [] out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (pkMemRegion40_unpack sp') (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (memRegion_four_entails (sp' + 108#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun pad32 => Wire.SepWPp.exists_pre fun w0 =>
    Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w3 => ?_
  have hp104 : ((sp' + 104#64) ↦₃₂ 0#32) ∗ ((sp' + 108#64) ↦₃₂ pad32) = ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (sp' + 104#64) 0#32 pad32
  refine Wire.SepWPp.mono_pre
    (P' := (sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ w2) ∗ ((sp' + 24#64) ↦₆₄ w3) ∗
      memRegion (sp' + 32#64) 8 ∗ memRegion (sp' + 40#64) 16 ∗ ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ 1#64) ∗
      ((sp' + 72#64) ↦₆₄ 0#64) ∗ ((sp' + 80#64) ↦₆₄ 0#64) ∗ ((sp' + 88#64) ↦₆₄ 1#64) ∗ ((sp' + 96#64) ↦₆₄ 0#64) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) ∗ memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      memRegion x19 56 ∗ (ptr ↦ₛ ([] : List (BitVec 8))) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (by dsimp only [vecHeader]; rw [← sepConj_assoc ((sp' + 104#64) ↦₃₂ 0#32), hp104]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _) ?_
  have h19 : s.readReg64 (Reg.gpr 19#5) = x19 := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hx20
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (400)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine Wire.SepWPp.mono_pre ?_
    (pack_tail_190_placed_wp (g := ⟨⟨0#64, 1#64⟩, ⟨0#64, 1#64⟩⟩) (m := PreKeyRecordStructure.empty)
      (w0 := w0) (w1 := w1) (pad32 := pad32) hok
      ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp, hcrl1,
       by simp [htr, arm64_norm], ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [h19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [PreKeyRecordStructure.empty, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
  simp only [PreKeyRecordStructure.empty, arm64_norm]
  have h56 : ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ 1#64) ∗ ((sp' + 72#64) ↦₆₄ 0#64) ∗
      ((sp' + 80#64) ↦₆₄ 0#64) ∗ ((sp' + 88#64) ↦₆₄ 1#64) ∗ ((sp' + 96#64) ↦₆₄ 0#64) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) ⊢ memRegion (sp' + 56#64) 56 := by
    rw [← hp104]; simpa [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using pkStruct56_pack sp' 0#64 1#64 0#64 0#64 1#64 0#64 0#32 pad32
  rw [← emp_sepConj (A.pool ∗ stackAt sp' (skipFieldStackX 100)), ← sepConj_assoc (vecU8Buf A 0#64 1#64 [])]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono h56
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (emp_entails_two_vecU8Buf_zero A))))))))))))
  apply entails_of_eq; ac_rfl

theorem epilogue_224_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : DecodeGhost} {s0 s : State} (hst : PkEpilogueStatePlaced s0 (s0.sp - 224#64) s)
    (hpc : s.pc = (blkPl_65).base + bv% (548)) (hrun : s.status = .Running) :
    Wire.SepWPp (lsProg_65 H) (s0.readReg64 .x30) s
      (pkEpilogueMem A (s0.sp - 224#64) x.ret x.bytesA x.bytes (PreKeyRecord.deserialize x.bytes) ∗
        pkCalleeSavedAt (s0.sp - 224#64) s0 ∗
        memRegion (s0.sp - 224#64 - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100))
      (fun sf Pf => sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyDeserializePlacedSpec A).post x s0 sf)) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, _hsp, hcrl, htr, hsaved⟩
  unfold pkEpilogueMem pkCalleeSavedAt; simp only [sepConj_assoc]
  refine sepWPp_of_sepWP_end_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro _
  refine ⟨by simp [arm64_norm], fun hv => ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simpa [arm64_norm] using hsaved.x24,
    by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
    by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28,
    by simp [arm64_norm], hv⟩, ?_⟩
  dsimp only [preKeyDeserializePlacedSpec, withLsCodeRoLoaded, preKeyDeserializeRawSpec]
  rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
  have hstk := pkStack_smallRoot_unsplit s0.sp s0; unfold pkCalleeSavedAt at hstk
  simp only [arm64_norm]
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk)))
  apply entails_of_eq; ac_rfl

end Placed

end CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers

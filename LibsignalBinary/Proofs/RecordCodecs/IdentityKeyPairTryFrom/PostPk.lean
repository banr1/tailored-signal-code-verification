/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPrivAndOk
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Post-Loop `PublicKey::try_from` Validation

Verifies the post-loop `<PublicKey as TryFrom<&[u8]>>::try_from` call and error dispatch
(`+344 .. +392`, `+688 .. +756`) in `IdentityKeyPair::try_from`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PostPkStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pk (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_pk (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_pk (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_pk (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_pk (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_pk (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_pk (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pk (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_pk (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_pk (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pk (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_pk (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_pk (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pk (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_pk (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_pk (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end PostPkStateSimp

/-! ## Post-loop `PublicKey::try_from` & error dispatch (`+344 .. +392`, `+688 .. +756`) -/

private theorem pkErr_fold_spe7 (sp' : BitVec 64) (b9 : BitVec 8) :
    ((sp' + 96#64) ↦₈ 1#8) ∗ memRegion (sp' + 97#64) 7 ∗
      ((sp' + 104#64) ↦₈ 0#8) ∗ ((sp' + 105#64) ↦₈ b9) ∗
      memRegion (sp' + 106#64) 30 ∗ memRegion (sp' + 136#64) 8 ⊢
      memRegion (sp' + 96#64) 48 := by
  have hm96 : ((sp' + 96#64) ↦₈ 1#8) ⊢ memRegion (sp' + 96#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm104 : ((sp' + 104#64) ↦₈ 0#8) ⊢ memRegion (sp' + 104#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 0#8
  have hm105 : ((sp' + 105#64) ↦₈ b9) ⊢ memRegion (sp' + 105#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ b9
  rw [show (48 : Nat) = 1 + (7 + (1 + (1 + (30 + 8)))) by decide,
    Prost.memRegion_split (sp' + 96#64) 1 47 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64) 7 40 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64) 1 39 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64) 1 38 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64) 30 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono hm96
    (sepConj_mono_right (sepConj_mono hm104 (sepConj_mono_left hm105)))

private theorem pkErr_fold_spe8 (sp' : BitVec 64) (t : BitVec 8) :
    ((sp' + 96#64) ↦₈ 1#8) ∗ memRegion (sp' + 97#64) 7 ∗
      ((sp' + 104#64) ↦₈ 1#8) ∗ ((sp' + 105#64) ↦₈ t) ∗
      memRegion (sp' + 106#64) 30 ∗ memRegion (sp' + 136#64) 8 ⊢
      memRegion (sp' + 96#64) 48 := by
  have hm96 : ((sp' + 96#64) ↦₈ 1#8) ⊢ memRegion (sp' + 96#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm104 : ((sp' + 104#64) ↦₈ 1#8) ⊢ memRegion (sp' + 104#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm105 : ((sp' + 105#64) ↦₈ t) ⊢ memRegion (sp' + 105#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ t
  rw [show (48 : Nat) = 1 + (7 + (1 + (1 + (30 + 8)))) by decide,
    Prost.memRegion_split (sp' + 96#64) 1 47 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64) 7 40 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64) 1 39 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64) 1 38 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64) 30 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono hm96
    (sepConj_mono_right (sepConj_mono hm104 (sepConj_mono_left hm105)))

private theorem pkErr_fold_spe9 (sp' : BitVec 64) (b9 : BitVec 8) (n : Nat) :
    ((sp' + 96#64) ↦₈ 1#8) ∗ memRegion (sp' + 97#64) 7 ∗
      ((sp' + 104#64) ↦₈ 2#8) ∗ ((sp' + 105#64) ↦₈ b9) ∗
      memRegion (sp' + 106#64) 6 ∗ ((sp' + 112#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion (sp' + 120#64) 16 ∗ memRegion (sp' + 136#64) 8 ⊢
      memRegion (sp' + 96#64) 48 := by
  have hm96 : ((sp' + 96#64) ↦₈ 1#8) ⊢ memRegion (sp' + 96#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm104 : ((sp' + 104#64) ↦₈ 2#8) ⊢ memRegion (sp' + 104#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 2#8
  have hm105 : ((sp' + 105#64) ↦₈ b9) ⊢ memRegion (sp' + 105#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ b9
  rw [show (48 : Nat) = 1 + (7 + (1 + (1 + (6 + (8 + (16 + 8)))))) by decide,
    Prost.memRegion_split (sp' + 96#64) 1 47 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64) 7 40 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64) 1 39 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64) 1 38 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64) 6 32 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64 + 6#64) 8 24 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64 + 6#64 + 8#64) 16 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono hm96
    (sepConj_mono_right (sepConj_mono hm104
      (sepConj_mono hm105
        (sepConj_mono_right (sepConj_mono_left
          (pointsTo64_entails_memRegion (sp' + 112#64) (BitVec.ofNat 64 n)))))))

theorem post_344_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State}
    {sp' pkCap pkPtr skCap skPtr : BitVec 64}
    {m : IdentityKeyPairStructure}
    (hdec : IdentityKeyPairStructure.decode x.bytes = some m)
    (hpk_lt : m.publicKey.length < 2 ^ 64)
    (hsk_lt : m.privateKey.length < 2 ^ 64)
    (hst : IkpBaseState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 344#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx29 : s.readReg64 .x29 = sp' + 144#64)
    (hx24 : s.readReg64 .x24 = speWord 9)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 m.privateKey.length)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 m.publicKey.length) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ memRegion x.ret 72 ∗
        vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
        logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseState img s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  have hm96_split : memRegion (sp' + 96#64) 48 =
      memRegion (sp' + 96#64) 40 ∗ memRegion (sp' + 136#64) 8 := by
    have hs := Prost.memRegion_split (sp' + 96#64) 40 8 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  have hpk_unpack : vecU8Buf A pkCap pkPtr m.publicKey ⊢
      (pkPtr ↦ₛ m.publicKey) ∗ vecU8BufRest A pkCap pkPtr m.publicKey :=
    Entails.trans (vecU8Buf_entails_slice_rest A pkCap pkPtr m.publicKey)
      (Entails.pure_left fun _ => Entails.refl _)
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right
      (sepConj_mono (Entails.of_eq hm96_split)
        (sepConj_mono_right (sepConj_mono_left hpk_unpack)))) ?_
  simp only [sepConj_assoc]
  have hcall := ikp_pkTryFrom_ok d
  have hok_next := @post_pk_ok_396_wp img C A encFn decFn ext hC x s0
  have herr760 := @err_store_760_wp img C A encFn decFn ext hC x s0
  let H := Rust.withPanics ext
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    344 52
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    688 20
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    732 28
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hst.sp
  have _hsp_align := hst.spAligned
  have _hx1_nat : (BitVec.ofNat 64 m.publicKey.length).toNat = m.publicKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpk_lt]
  have ha96 : sp' + 144#64 - 48#64 = sp' + 96#64 := by bv_omega
  refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab
    (mid := entry + bv% ((ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_noPanic_tryFrom (pkPtr, m.publicKey, sp' + 96#64) hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hst.spAligned) hF1 hsym1
    (ret_pc := entry + bv% (356)) (by simp [*, arm64_norm])
    (T := (pkPtr ↦ₛ m.publicKey) ∗ memRegion (sp' + 96#64) 40 ∗ logOff img)
    (φ := pkPtr = pkPtr ∧ m.publicKey.length = m.publicKey.length ∧ sp' + 144#64 - 48#64 = sp' + 96#64)
    (by simp [*, pkTryFromCodeSpec, pkTryFromSpec, arm64_norm])
    ⟨rfl, rfl, ha96⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [pkTryFromCodeSpec, pkTryFromSpec]
  simp only [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  have hst1 : IkpBaseState img s0 sp' _ :=
    hst.of_steps hF1 hsym1 (by tryFromPost_sp [hsp_eq])
      (by simp [*, hst.trace, arm64_norm])
      (by simp [*, hst.x26, arm64_norm])
      (by simp [*, hst.x27, arm64_norm])
      (by simp [*, hst.x28, arm64_norm])
  have hst2 : IkpBaseState img s0 sp' s2 :=
    hst1.of_calleeSaved hsp2 hsp2_align hF2 hsym2 (htr2.trans hst1.trace) hcs2
  have _hsp2_eq := hst2.sp
  have _hsp2_align := hst2.spAligned
  have _hx19_2 : s2.readReg64 .x19 = x.ret := hcs2.1.trans (by simp [*, arm64_norm])
  have _hx20_2 : s2.readReg64 .x20 = pkPtr := hcs2.2.1.trans (by simp [*, arm64_norm])
  have _hx21_2 : s2.readReg64 .x21 = skCap := hcs2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx22_2 : s2.readReg64 .x22 = pkCap := hcs2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx23_2 : s2.readReg64 .x23 = skPtr := hcs2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx24_2 : s2.readReg64 .x24 = speWord 9 := hcs2.2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 m.privateKey.length :=
    hcs2.2.2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx29_2 : s2.readReg64 .x29 = sp' + 144#64 :=
    hcs2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have hpk_fold := slice_rest_entails_vecU8Buf A pkCap pkPtr m.publicKey
  refine Wire.SepWPp.mono_pre
    (P' := pkTryFromResultAt (sp' + 96#64) (PublicKey.deserialize m.publicKey) ∗
      memRegion (sp' + 136#64) 8 ∗ memRegion sp' 32 ∗ memRegion x.ret 72 ∗
      vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
      logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (by
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left hpk_fold)))))
      apply entails_of_eq; ac_rfl) ?_
  cases hpk : PublicKey.deserialize m.publicKey with
  | ok pk =>
    dsimp only [pkTryFromResultAt]
    obtain ⟨w0, b8, w9, h13, w15, w23, b31, hpk_cells⟩ :=
      pointsToBytes32_exists_pkCells pk.bytes.toList pk.bytes.2
    have hm15 : memRegion (sp' + 129#64) 7 ∗ memRegion (sp' + 136#64) 8 =
        memRegion (sp' + 129#64) 15 := by
      have hs := (Prost.memRegion_split (sp' + 129#64) 7 8 (by decide)).symm
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
      exact hs
    simp only [BitVec.add_assoc, BitVec.reduceAdd, hpk_cells (sp' + 97#64), pkCells, sepConj_assoc]
    have h15_pre :
        ((sp' + 96#64) ↦₈ 0#8) ∗ ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 105#64) ↦₈ b8) ∗
          ((sp' + 106#64) ↦₃₂ w9) ∗ ((sp' + 110#64) ↦₁₆ h13) ∗ ((sp' + 112#64) ↦₆₄ w15) ∗
          ((sp' + 120#64) ↦₆₄ w23) ∗ ((sp' + 128#64) ↦₈ b31) ∗
          memRegion (sp' + 129#64) 7 ∗ memRegion (sp' + 136#64) 8 ∗
          memRegion sp' 32 ∗ memRegion x.ret 72 ∗
          vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
          logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢
        ((sp' + 96#64) ↦₈ 0#8) ∗ ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 105#64) ↦₈ b8) ∗
          ((sp' + 106#64) ↦₃₂ w9) ∗ ((sp' + 110#64) ↦₁₆ h13) ∗ ((sp' + 112#64) ↦₆₄ w15) ∗
          ((sp' + 120#64) ↦₆₄ w23) ∗ ((sp' + 128#64) ↦₈ b31) ∗
          memRegion (sp' + 129#64) 15 ∗ memRegion sp' 32 ∗ memRegion x.ret 72 ∗
          vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
          logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) := by
      rw [← hm15]; apply entails_of_eq; ac_rfl
    refine Wire.SepWPp.mono_pre h15_pre ?_
    clear h15_pre
    refine Wire.SepWPp.of_sepWP_frozen hst2.frozen hst2.symtab (mid := entry + bv% (396)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF3 hsym3
    have _hb8_ext : ∀ u : BitVec 8, (u.zeroExtend 32).zeroExtend 64 = u.zeroExtend 64 := by decide
    refine Wire.SepWPp.mono_pre
      (P' := (memRegion sp' 32 ∗
        ((sp' + 96#64) ↦₈ 0#8) ∗ pkCells w0 b8 w9 h13 w15 w23 b31 (sp' + 97#64) ∗
        memRegion (sp' + 129#64) 15 ∗ memRegion x.ret 72 ∗
        vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ logOff img)
      (by
        unfold pkCells
        apply entails_of_eq
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := fun sf Pf => IkpBaseState img s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (hok_next hdec hpk hsk_lt
        (hst2.of_steps hF3 hsym3 (by tryFromPost_sp [hst2.sp])
          (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
          (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        hpk_cells
        (by simp [*, arm64_norm]))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; ac_rfl
  | error e =>
    have htry_err : IdentityKeyPair.tryFrom x.bytes = .error e := by
      unfold IdentityKeyPair.tryFrom decodeIdentityKey
      simp [hdec, hpk, Bind.bind, Except.bind, Except.map]
    cases e with
    | noKeyTypeIdentifier =>
      dsimp only [pkTryFromResultAt]
      have hm31 : memRegion (sp' + 96#64 + 9#64) 31 =
          (∃∗ b9 : BitVec 8, (sp' + 105#64) ↦₈ b9) ∗ memRegion (sp' + 106#64) 30 := by
        rw [Prost.memRegion_split (sp' + 96#64 + 9#64) 1 30 (by decide), memRegion_one]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [hm31]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun b9 => ?_
      refine Wire.SepWPp.of_sepWP_frozen hst2.frozen hst2.symtab (mid := entry + bv% (760)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
      intro hF3 hsym3
      refine Wire.SepWPp.mono_pre
        (P' := (memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr m.publicKey ∗
          vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
          (memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ logOff img))
        (by
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkErr_fold_spe7 sp' b9))))
          apply entails_of_eq
          try simp only [arm64_norm]
          ac_rfl) ?_
      refine Wire.SepWPp.frame_tryFrom
        (Q' := fun sf Pf => IkpBaseState img s0 sp' sf ∧
          (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
            A.pool ∗ stackAt sp' (skipFieldStackX 100)))
        (herr760
          (hst2.of_steps hF3 hsym3 (by tryFromPost_sp [hst2.sp])
            (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
            (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, speWord, arm64_norm])
          (rfl)
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (ikpResult_err_spe7 A x.ret _ htry_err))
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hentf) ?_
      apply entails_of_eq; ac_rfl
    | badKeyType t =>
      dsimp only [pkTryFromResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hst2.frozen hst2.symtab (mid := entry + bv% (760)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
      intro hF3 hsym3
      have _ht_mask : ∀ u : BitVec 8,
          0#64 ||| (((u.zeroExtend 32).zeroExtend 64) &&& 255#64) = u.zeroExtend 64 := by decide
      have _ht_mask2 : ∀ u : BitVec 8,
          0#64 ||| ((u.zeroExtend 64) &&& 255#64) = u.zeroExtend 64 := by decide
      refine Wire.SepWPp.mono_pre
        (P' := (memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr m.publicKey ∗
          vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
          (memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ logOff img))
        (by
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkErr_fold_spe8 sp' t))))
          apply entails_of_eq
          try simp only [arm64_norm]
          ac_rfl) ?_
      refine Wire.SepWPp.frame_tryFrom
        (Q' := fun sf Pf => IkpBaseState img s0 sp' sf ∧
          (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
            A.pool ∗ stackAt sp' (skipFieldStackX 100)))
        (herr760
          (hst2.of_steps hF3 hsym3 (by tryFromPost_sp [hst2.sp])
            (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
            (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, speWord, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (ikpResult_err_spe8 A x.ret t htry_err))
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hentf) ?_
      apply entails_of_eq; ac_rfl
    | badKeyLength n =>
      dsimp only [pkTryFromResultAt]
      have hm7 : memRegion (sp' + 96#64 + 9#64) 7 =
          (∃∗ b9 : BitVec 8, (sp' + 105#64) ↦₈ b9) ∗ memRegion (sp' + 106#64) 6 := by
        rw [Prost.memRegion_split (sp' + 96#64 + 9#64) 1 6 (by decide), memRegion_one]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [hm7]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun b9 => ?_
      refine Wire.SepWPp.of_sepWP_frozen hst2.frozen hst2.symtab (mid := entry + bv% (760)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
      intro hF3 hsym3
      refine Wire.SepWPp.mono_pre
        (P' := (memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr m.publicKey ∗
          vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
          (memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ logOff img))
        (by
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkErr_fold_spe9 sp' b9 n))))
          apply entails_of_eq
          try simp only [arm64_norm]
          ac_rfl) ?_
      refine Wire.SepWPp.frame_tryFrom
        (Q' := fun sf Pf => IkpBaseState img s0 sp' sf ∧
          (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
            A.pool ∗ stackAt sp' (skipFieldStackX 100)))
        (herr760
          (hst2.of_steps hF3 hsym3 (by tryFromPost_sp [hst2.sp])
            (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
            (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp only [arm64_norm]; generalize BitVec.ofNat 64 n = w; bv_kernel)
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (ikpResult_err_spe9 A x.ret n htry_err))
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hentf) ?_
      apply entails_of_eq; ac_rfl
    | _ =>
      dsimp only [pkTryFromResultAt]
      exact Wire.SepWPp.pure_pre fun h => h.elim

section Placed

open CryptoVerification.RecordCodecs.Placed

theorem post_344_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 s : State}
    {sp' pkCap pkPtr skCap skPtr : BitVec 64} {m : IdentityKeyPairStructure}
    (hdec : IdentityKeyPairStructure.decode x.bytes = some m)
    (hpk_lt : m.publicKey.length < 2 ^ 64) (hsk_lt : m.privateKey.length < 2 ^ 64)
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (344)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret) (hx29 : s.readReg64 .x29 = sp' + 144#64)
    (hx24 : s.readReg64 .x24 = speWord 9)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 m.privateKey.length)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 m.publicKey.length) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ memRegion x.ret 72 ∗
        vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
        lsLogOff ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          lsLogOff ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  have hm96_split : memRegion (sp' + 96#64) 48 =
      memRegion (sp' + 96#64) 40 ∗ memRegion (sp' + 136#64) 8 := by
    have hs := Prost.memRegion_split (sp' + 96#64) 40 8 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs; exact hs
  have hpk_unpack : vecU8Buf A pkCap pkPtr m.publicKey ⊢
      (pkPtr ↦ₛ m.publicKey) ∗ vecU8BufRest A pkCap pkPtr m.publicKey :=
    Entails.trans (vecU8Buf_entails_slice_rest A pkCap pkPtr m.publicKey)
      (Entails.pure_left fun _ => Entails.refl _)
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right
      (sepConj_mono (Entails.of_eq hm96_split)
        (sepConj_mono_right (sepConj_mono_left hpk_unpack)))) ?_
  simp only [sepConj_assoc]
  have hcall := ikp_pkTryFrom_placed_ok d
  have hok_next := @post_pk_ok_396_placed_wp _ A H d x s0
  have herr760 := @err_store_760_placed_wp _ A H d x s0
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hst.sp
  have _hsp_align := hst.spAligned
  have _hx1_nat : (BitVec.ofNat 64 m.publicKey.length).toNat = m.publicKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpk_lt]
  have ha96 : sp' + 144#64 - 48#64 = sp' + 96#64 := by bv_omega
  refine sepWPp_of_sepWP_lscro hst.crl (mid := lsmpl.base 211) ?_; wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (pkPtr, m.publicKey, sp' + 96#64) hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hst.spAligned) hcrl1
    (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (356))
    (by simp [*, hst.trace, arm64_norm])
    (T := (pkPtr ↦ₛ m.publicKey) ∗ memRegion (sp' + 96#64) 40 ∗ lsLogOff)
    (φ := pkPtr = pkPtr ∧ m.publicKey.length = m.publicKey.length ∧ sp' + 144#64 - 48#64 = sp' + 96#64)
    (by simp [*, pkTryFromPlacedSpec, pkTryFromSpec, arm64_norm])
    ⟨rfl, rfl, ha96⟩ (by sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [pkTryFromPlacedSpec, pkTryFromSpec]
  simp only [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  have hst1 := hst.of_steps hcrl1 (by tryFromPost_sp [hsp_eq])
    (by simp [*, hst.trace, arm64_norm]) (by simp [*, hst.x26, arm64_norm])
    (by simp [*, hst.x27, arm64_norm]) (by simp [*, hst.x28, arm64_norm])
  have hst2 := hst1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hst1.trace) hcs2
  have _hsp2_eq := hst2.sp
  have _hsp2_align := hst2.spAligned
  have _hx19_2 : s2.readReg64 .x19 = x.ret := hcs2.1.trans (by simp [*, arm64_norm])
  have _hx20_2 : s2.readReg64 .x20 = pkPtr := hcs2.2.1.trans (by simp [*, arm64_norm])
  have _hx21_2 : s2.readReg64 .x21 = skCap := hcs2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx22_2 : s2.readReg64 .x22 = pkCap := hcs2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx23_2 : s2.readReg64 .x23 = skPtr := hcs2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx24_2 : s2.readReg64 .x24 = speWord 9 := hcs2.2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 m.privateKey.length :=
    hcs2.2.2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have _hx29_2 : s2.readReg64 .x29 = sp' + 144#64 :=
    hcs2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have hpk_fold := slice_rest_entails_vecU8Buf A pkCap pkPtr m.publicKey
  refine Wire.SepWPp.mono_pre
    (P' := pkTryFromResultAt (sp' + 96#64) (PublicKey.deserialize m.publicKey) ∗
      memRegion (sp' + 136#64) 8 ∗ memRegion sp' 32 ∗ memRegion x.ret 72 ∗
      vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
      lsLogOff ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (by refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left hpk_fold)))))
        apply entails_of_eq; ac_rfl) ?_
  cases hpk : PublicKey.deserialize m.publicKey with
  | ok pk =>
    dsimp only [pkTryFromResultAt]
    obtain ⟨w0, b8, w9, h13, w15, w23, b31, hpk_cells⟩ :=
      pointsToBytes32_exists_pkCells pk.bytes.toList pk.bytes.2
    have hm15 : memRegion (sp' + 129#64) 7 ∗ memRegion (sp' + 136#64) 8 =
        memRegion (sp' + 129#64) 15 := by
      have hs := (Prost.memRegion_split (sp' + 129#64) 7 8 (by decide)).symm
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs; exact hs
    simp only [BitVec.add_assoc, BitVec.reduceAdd, hpk_cells (sp' + 97#64), pkCells, sepConj_assoc]
    have h15_pre :
        ((sp' + 96#64) ↦₈ 0#8) ∗ ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 105#64) ↦₈ b8) ∗
          ((sp' + 106#64) ↦₃₂ w9) ∗ ((sp' + 110#64) ↦₁₆ h13) ∗ ((sp' + 112#64) ↦₆₄ w15) ∗
          ((sp' + 120#64) ↦₆₄ w23) ∗ ((sp' + 128#64) ↦₈ b31) ∗
          memRegion (sp' + 129#64) 7 ∗ memRegion (sp' + 136#64) 8 ∗
          memRegion sp' 32 ∗ memRegion x.ret 72 ∗
          vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
          lsLogOff ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢
        ((sp' + 96#64) ↦₈ 0#8) ∗ ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 105#64) ↦₈ b8) ∗
          ((sp' + 106#64) ↦₃₂ w9) ∗ ((sp' + 110#64) ↦₁₆ h13) ∗ ((sp' + 112#64) ↦₆₄ w15) ∗
          ((sp' + 120#64) ↦₆₄ w23) ∗ ((sp' + 128#64) ↦₈ b31) ∗
          memRegion (sp' + 129#64) 15 ∗ memRegion sp' 32 ∗ memRegion x.ret 72 ∗
          vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
          lsLogOff ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) := by
      rw [← hm15]; apply entails_of_eq; ac_rfl
    refine Wire.SepWPp.mono_pre h15_pre ?_; clear h15_pre
    refine sepWPp_of_sepWP_lscro hst2.crl (mid := (blkPl_84).base + bv% (396)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have _hb8_ext : ∀ u : BitVec 8, (u.zeroExtend 32).zeroExtend 64 = u.zeroExtend 64 := by decide
    refine Wire.SepWPp.mono_pre
      (P' := (memRegion sp' 32 ∗ ((sp' + 96#64) ↦₈ 0#8) ∗
        pkCells w0 b8 w9 h13 w15 w23 b31 (sp' + 97#64) ∗
        memRegion (sp' + 129#64) 15 ∗ memRegion x.ret 72 ∗
        vecU8Buf A pkCap pkPtr m.publicKey ∗ vecU8Buf A skCap skPtr m.privateKey ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ lsLogOff)
      (by unfold pkCells; apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (hok_next hdec hpk hsk_lt
        (hst2.of_steps hcrl3 (by tryFromPost_sp [hst2.sp])
          (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
          (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        hpk_cells (by simp [*, arm64_norm]))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_; apply entails_of_eq; ac_rfl
  | error e =>
    have htry_err : IdentityKeyPair.tryFrom x.bytes = .error e := by
      unfold IdentityKeyPair.tryFrom decodeIdentityKey
      simp [hdec, hpk, Bind.bind, Except.bind, Except.map]
    cases e with
    | noKeyTypeIdentifier =>
      dsimp only [pkTryFromResultAt]
      have hm31 : memRegion (sp' + 96#64 + 9#64) 31 =
          (∃∗ b9 : BitVec 8, (sp' + 105#64) ↦₈ b9) ∗ memRegion (sp' + 106#64) 30 := by
        rw [Prost.memRegion_split (sp' + 96#64 + 9#64) 1 30 (by decide), memRegion_one]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [hm31]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun b9 => ?_
      refine sepWPp_of_sepWP_lscro hst2.crl (mid := (blkPl_84).base + bv% (760)) ?_; wp_steps
      refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
      refine Wire.SepWPp.mono_pre
        (P' := (memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr m.publicKey ∗
          vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
          (memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ lsLogOff))
        (by refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkErr_fold_spe7 sp' b9))))
            apply entails_of_eq; try simp only [arm64_norm]; ac_rfl) ?_
      refine Wire.SepWPp.frame_tryFrom
        (Q' := fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
          (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
            A.pool ∗ stackAt sp' (skipFieldStackX 100)))
        (herr760
          (hst2.of_steps hcrl3 (by tryFromPost_sp [hst2.sp])
            (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
            (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, speWord, arm64_norm]) rfl
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (ikpResult_err_spe7 A x.ret _ htry_err))
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hentf) ?_; apply entails_of_eq; ac_rfl
    | badKeyType t =>
      dsimp only [pkTryFromResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine sepWPp_of_sepWP_lscro hst2.crl (mid := (blkPl_84).base + bv% (760)) ?_; wp_steps
      refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
      have _ht_mask : ∀ u : BitVec 8,
          0#64 ||| (((u.zeroExtend 32).zeroExtend 64) &&& 255#64) = u.zeroExtend 64 := by decide
      have _ht_mask2 : ∀ u : BitVec 8,
          0#64 ||| ((u.zeroExtend 64) &&& 255#64) = u.zeroExtend 64 := by decide
      refine Wire.SepWPp.mono_pre
        (P' := (memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr m.publicKey ∗
          vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
          (memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ lsLogOff))
        (by refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkErr_fold_spe8 sp' t))))
            apply entails_of_eq; try simp only [arm64_norm]; ac_rfl) ?_
      refine Wire.SepWPp.frame_tryFrom
        (Q' := fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
          (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
            A.pool ∗ stackAt sp' (skipFieldStackX 100)))
        (herr760
          (hst2.of_steps hcrl3 (by tryFromPost_sp [hst2.sp])
            (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
            (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, speWord, arm64_norm])
          (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (ikpResult_err_spe8 A x.ret t htry_err))
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hentf) ?_; apply entails_of_eq; ac_rfl
    | badKeyLength n =>
      dsimp only [pkTryFromResultAt]
      have hm7 : memRegion (sp' + 96#64 + 9#64) 7 =
          (∃∗ b9 : BitVec 8, (sp' + 105#64) ↦₈ b9) ∗ memRegion (sp' + 106#64) 6 := by
        rw [Prost.memRegion_split (sp' + 96#64 + 9#64) 1 6 (by decide), memRegion_one]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [hm7]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun b9 => ?_
      refine sepWPp_of_sepWP_lscro hst2.crl (mid := (blkPl_84).base + bv% (760)) ?_; wp_steps
      refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
      refine Wire.SepWPp.mono_pre
        (P' := (memRegion x.ret 72 ∗ vecU8Buf A pkCap pkPtr m.publicKey ∗
          vecU8Buf A skCap skPtr m.privateKey ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
          (memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ lsLogOff))
        (by refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkErr_fold_spe9 sp' b9 n))))
            apply entails_of_eq; try simp only [arm64_norm]; ac_rfl) ?_
      refine Wire.SepWPp.frame_tryFrom
        (Q' := fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
          (Pf ⊢ identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
            A.pool ∗ stackAt sp' (skipFieldStackX 100)))
        (herr760
          (hst2.of_steps hcrl3 (by tryFromPost_sp [hst2.sp])
            (by simp [*, hst2.trace, arm64_norm]) (by simp [*, hst2.x26, arm64_norm])
            (by simp [*, hst2.x27, arm64_norm]) (by simp [*, hst2.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp only [arm64_norm]; generalize BitVec.ofNat 64 n = w; bv_kernel)
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (ikpResult_err_spe9 A x.ret n htry_err))
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hentf) ?_; apply entails_of_eq; ac_rfl
    | _ =>
      dsimp only [pkTryFromResultAt]
      exact Wire.SepWPp.pure_pre fun h => h.elim

end Placed

end CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers

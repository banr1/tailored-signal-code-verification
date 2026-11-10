/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom.LoopError
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom.LoopMerge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom.LoopVarint
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom.PostPk
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Protobuf Decode Loop and Entry Theorem

Proves the protobuf field-decoding loop induction, prologue, and top-level `subroutine_ok` for
`<IdentityKeyPair as TryFrom<&[u8]>>::try_from`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom

open CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers

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

section LoopStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_lp (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_lp (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_lp (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_lp (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_lp (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_lp (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_lp (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_lp (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_lp (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_lp (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_lp (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_lp (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_lp (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_lp (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_lp (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_lp (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end LoopStateSimp

/-! ## Loop exit (`+708..+728` → `+344` → `+812`), header (`+108..+120`), and induction -/

theorem loopExit_708_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {m : IdentityKeyPairStructure}
    (hlt : x.bytes.length < 2 ^ 32)
    (hdec : IdentityKeyPairStructure.decode x.bytes = some m)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 708#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr [] ∗
        ikpLoopCommon img A sp' x.ret 0 m)
      (ikpExitPost img A s0 sp' x.ret ptr [] (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hpost := @post_344_wp img C A S ext hC d x s0
  obtain ⟨hpk_le, hsk_le⟩ := ikp_decode_field_lengths hdec
  unfold sliceCursorAt ikpLoopCommon ikpStructLoopOf ikpStructAt
  simp only [vecU8At_eq_header_buf, vecHeader, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine Wire.SepWPp.exists_pre fun pk => Wire.SepWPp.exists_pre fun sk =>
    Wire.SepWPp.pure_pre fun _ => ?_
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (vecU8Buf_cap_lt63 A pk.cap pk.ptr m.publicKey))))))))) ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine Wire.SepWPp.pure_pre fun hpk_lt63 => ?_
  have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pk.cap hpk_lt63
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    708 24
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  have hsp_eq := hregs.base.sp
  subst hsp_eq
  let sp' := s.sp
  have _hsp_align := hregs.base.spAligned
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
    (mid := entry + bv% (344)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
  intro hF1 hsym1
  have hm16 := pointsTo64_pair_entails_memRegion16 (sp' + 32#64) ptr 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm16
  have h144 := ikpFold144 sp' pk.cap pk.ptr (BitVec.ofNat 64 m.publicKey.length)
    sk.cap sk.ptr (BitVec.ofNat 64 m.privateKey.length)
  dsimp only [vecHeader] at h144
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
  refine Wire.SepWPp.mono_pre
    (P' := (memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗ memRegion x.ret 72 ∗
      vecU8Buf A pk.cap pk.ptr m.publicKey ∗ vecU8Buf A sk.cap sk.ptr m.privateKey ∗
      logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
      (memRegion (sp' + 32#64) 16 ∗
        ((sp' + 48#64) ↦₆₄ pk.cap) ∗ ((sp' + 56#64) ↦₆₄ pk.ptr) ∗
        ((sp' + 64#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
        ((sp' + 72#64) ↦₆₄ sk.cap) ∗ ((sp' + 80#64) ↦₆₄ sk.ptr) ∗
        ((sp' + 88#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
        (ptr ↦ₛ [])))
    (by
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left hm16))
      apply entails_of_eq
      try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
      try simp only [BitVec.add_assoc]
      try simp only [BitVec.reduceAdd]
      try simp only [bv_sub_add_lit]
      try simp only [BitVec.add_assoc]
      try simp only [BitVec.reduceAdd]
      try simp only [bv_sub_add_lit]
      try simp only [arm64_norm]
      ac_rfl) ?_
  refine Wire.SepWPp.frame_tryFrom
    (Q' := fun sf Pf => IkpBaseState img s0 sp' sf ∧
      (Pf ⊢ memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗
        identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
        logOff img ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
    (hpost hdec (by omega) (by omega)
      (hregs.base.of_steps hF1 hsym1
        (by simp [*, arm64_norm])
        (by simp [*, hregs.base.trace, arm64_norm])
        (by simp [*, hregs.base.x26, arm64_norm])
        (by simp [*, hregs.base.x27, arm64_norm])
        (by simp [*, hregs.base.x28, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, hregs.x19, arm64_norm])
      (by simp [*, hregs.x29, arm64_norm]; rfl)
      (by simp [*, hregs.x24, arm64_norm])
      (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]))
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  unfold ikpExitMem
  refine Entails.trans (sepConj_mono_left hentf) ?_
  refine Entails.trans ?_ (sepConj_mono_left h144)
  apply entails_of_eq
  try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
  try simp only [BitVec.add_assoc]
  try simp only [BitVec.reduceAdd]
  try simp only [bv_sub_add_lit]
  try simp only [BitVec.add_assoc]
  try simp only [BitVec.reduceAdd]
  try simp only [bv_sub_add_lit]
  try simp only [arm64_norm]
  ac_rfl

theorem loopCheck_108_empty_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {m : IdentityKeyPairStructure}
    (hlt : x.bytes.length < 2 ^ 32)
    (hdec : IdentityKeyPairStructure.decode x.bytes = some m)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 108#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr [] ∗
        ikpLoopCommon img A sp' x.ret ([] : List (BitVec 8)).length m)
      (ikpExitPost img A s0 sp' x.ret ptr [] (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hexit := @loopExit_708_wp img C A S ext hC d x s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    108 16
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp
  have _hsp_align := hregs.base.spAligned
  have _h29 := hregs.x29
  unfold sliceCursorAt ikpLoopCommon
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
    (mid := entry + bv% (708)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre
    (P' := sliceCursorAt (sp' + 32#64) ptr [] ∗ ikpLoopCommon img A sp' x.ret 0 m)
    (by
      unfold sliceCursorAt ikpLoopCommon
      apply entails_of_eq
      try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
      try simp only [BitVec.add_assoc]
      try simp only [BitVec.reduceAdd]
      try simp only [bv_sub_add_lit]
      try simp only [BitVec.add_assoc]
      try simp only [BitVec.reduceAdd]
      try simp only [bv_sub_add_lit]
      try simp only [arm64_norm]
      ac_rfl) ?_
  exact hexit hlt hdec
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (hregs.of_steps hF1 hsym1
      (by simp [*, hregs.base.sp, arm64_norm])
      (by simp [*, hregs.base.trace, arm64_norm])
      (by simp [*, hregs.base.x26, arm64_norm])
      (by simp [*, hregs.base.x27, arm64_norm])
      (by simp [*, hregs.base.x28, arm64_norm])
      (by simp [*, hregs.x29, arm64_norm])
      (by simp [*, hregs.x19, arm64_norm])
      (by simp [*, hregs.x21, arm64_norm])
      (by simp [*, hregs.x24, arm64_norm]))

theorem loopCheck_108_cons_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : IdentityKeyPairStructure}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 108#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 124#64 →
      s1.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s1 →
      s1.readReg64 .x23 = sp' + 32#64 →
      s1.readReg64 .x22 = sp' + 40#64 →
      s1.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1
        (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
          ikpLoopCommon img A sp' x.ret (b0 :: bs1).length m) Q Qp) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
        ikpLoopCommon img A sp' x.ret (b0 :: bs1).length m) Q Qp := by
  let H := Rust.withPanics ext
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    108 16
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp
  have _hsp_align := hregs.base.spAligned
  have _h29 := hregs.x29
  obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen
  unfold sliceCursorAt ikpLoopCommon
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
    (mid := entry + bv% (124)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre
    (P' := sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
      ikpLoopCommon img A sp' x.ret (b0 :: bs1).length m)
    (by
      unfold sliceCursorAt ikpLoopCommon
      apply entails_of_eq
      simp only [arm64_norm]) ?_
  exact hcont _
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (hregs.of_steps hF1 hsym1
      (by simp [*, hregs.base.sp, arm64_norm])
      (by simp [*, hregs.base.trace, arm64_norm])
      (by simp [*, hregs.base.x26, arm64_norm])
      (by simp [*, hregs.base.x27, arm64_norm])
      (by simp [*, hregs.base.x28, arm64_norm])
      (by simp [*, hregs.x29, arm64_norm])
      (by simp [*, hregs.x19, arm64_norm])
      (by simp [*, hregs.x21, arm64_norm])
      (by simp [*, hregs.x24, arm64_norm]))
    (by simp [*, arm64_norm])
    (by simp [*, arm64_norm])
    (by simp [*, arm64_norm])

theorem decodeLoop_124_step_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {fuel : ℕ} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (ih : ∀ {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure},
      decodeFieldsLoop IdentityKeyPairStructure.mergeField fuel m bs =
        IdentityKeyPairStructure.decode x.bytes →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 108#64 →
      s.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s →
      bs.length ≤ fuel →
      bs.length < 2 ^ 63 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
        (sliceCursorAt (sp' + 32#64) ptr bs ∗
          ikpLoopCommon img A sp' x.ret bs.length m)
        (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hinv : decodeFieldsLoop IdentityKeyPairStructure.mergeField (fuel + 1) m (b0 :: bs1) =
      IdentityKeyPairStructure.decode x.bytes)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 124#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64)
    (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1)
    (hlen : (b0 :: bs1).length < 2 ^ 63) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
        ikpLoopCommon img A sp' x.ret (b0 :: bs1).length m)
      (ikpExitPost img A s0 sp' x.ret ptr (b0 :: bs1) (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  refine decodeKey_124_cps hC d hpc hrun hregs hx23 hx22 hx2 hlen
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hx0_1 hx1_1 => ?_)
    (fun hdk_none => by simp [IdentityKeyPair.tryFrom, ← hinv, decodeFieldsLoop, hdk_none])
  obtain ⟨k1, hk1_pos, hk1_le, hrest1_eq, htag_lt, htag_ge⟩ := decodeKey_suffix hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by simp [hrest1_eq]
  refine ikp_advance_cursor hk1_le hrest1_eq ?_
  refine Wire.SepWPp.mono_pre
    (P' := sliceCursorAt (sp' + 32#64) (ptr + BitVec.ofNat 64 k1) rest1 ∗
      ikpLoopCommon img A sp' x.ret rest1.length m)
    (sepConj_mono_right (by
      unfold ikpLoopCommon
      exact sepConj_mono_right (sepConj_mono_left
        (ikpStructLoopOf_mono A (sp' + 48#64) m (by omega))))) ?_
  refine mergeField_248_cps (bs := rest1) (m := m) hC d hpc1 hrun1 hregs1 hx0_1 hx1_1 htag_ge htag_lt (by omega)
    (fun m' rest2 s2 hmf hpc2 hrun2 hregs2 => ?_)
    (fun hmf_none => by simp [IdentityKeyPair.tryFrom, ← hinv, decodeFieldsLoop, hdk, hmf_none])
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := ikp_mergeField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by simp [hrest2_eq]
  refine ikp_advance_cursor hk2_le hrest2_eq ?_
  have hinv' : decodeFieldsLoop IdentityKeyPairStructure.mergeField fuel m' rest2 =
      IdentityKeyPairStructure.decode x.bytes := by
    simpa [decodeFieldsLoop, hdk, hmf] using hinv
  exact ih hinv' hpc2 hrun2 hregs2 (by omega) (by omega)

theorem decodeLoop_108_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 : State} {sp' : BitVec 64}
    (hlt : x.bytes.length < 2 ^ 32) :
    ∀ (fuel : ℕ) {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure},
      decodeFieldsLoop IdentityKeyPairStructure.mergeField fuel m bs =
        IdentityKeyPairStructure.decode x.bytes →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 108#64 →
      s.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s →
      bs.length ≤ fuel →
      bs.length < 2 ^ 63 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
        (sliceCursorAt (sp' + 32#64) ptr bs ∗
          ikpLoopCommon img A sp' x.ret bs.length m)
        (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0)
  | 0, s, ptr, bs, m, hinv, hpc, hrun, hregs, hfuel, _ => by
    cases bs with
    | nil => exact loopCheck_108_empty_wp hC d hlt hinv.symm hpc hrun hregs
    | cons b0 bs1 => simp at hfuel
  | fuel + 1, s, ptr, bs, m, hinv, hpc, hrun, hregs, hfuel, hlen => by
    cases bs with
    | nil => exact loopCheck_108_empty_wp hC d hlt hinv.symm hpc hrun hregs
    | cons b0 bs1 =>
      refine loopCheck_108_cons_cps hpc hrun hregs hlen ?_
      intro s1 hpc1 hrun1 hregs1 hx23_1 hx22_1 hx2_1
      exact decodeLoop_124_step_wp hC d (decodeLoop_108_wp hC d hlt fuel)
        hinv hpc1 hrun1 hregs1 hx23_1 hx22_1 hx2_1 hfuel hlen

/-! ## Prologue (`+0..+88`, `+324..+340`) and top-level `subroutine_ok` -/

theorem ikp_entry_to_812_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s0
      (memRegion (s0.sp - 224#64) 144 ∗
        memRegion (s0.sp - 224#64 + 144#64) 80 ∗
        memRegion x.ret 72 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (skipFieldStackX 100))
      (fun sf Pf => IkpBaseState img s0 (s0.sp - 224#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 224#64) 144 ∗
          ((s0.sp - 224#64 + 168#64) ↦₆₄ (s0.sp - 224#64 + 32#64)) ∗
          ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗
          stackAt (s0.sp - 224#64) (skipFieldStackX 100)))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hpost := @post_344_wp img C A S ext hC d x s0
  have hstep := @decodeLoop_124_step_wp img C A S ext hC d x s0
  have hloop := decodeLoop_108_wp (img := img) (C := C) (A := A) (S := S) (ext := ext) (x := x) (s0 := s0) (sp' := s0.sp - 224#64) hC d hlt
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (ikpMem144_prologue_cells (s0.sp - 224#64))
      (sepConj_mono_left (ikpMem80_cells (s0.sp - 224#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun w88 => Wire.SepWPp.exists_pre fun w80 =>
    Wire.SepWPp.exists_pre fun w72 => Wire.SepWPp.exists_pre fun w64 =>
    Wire.SepWPp.exists_pre fun w56 => Wire.SepWPp.exists_pre fun w48 =>
    Wire.SepWPp.exists_pre fun w40 => Wire.SepWPp.exists_pre fun w32 =>
    Wire.SepWPp.exists_pre fun c19 => Wire.SepWPp.exists_pre fun c20 =>
    Wire.SepWPp.exists_pre fun c21 => Wire.SepWPp.exists_pre fun c22 =>
    Wire.SepWPp.exists_pre fun c23 => Wire.SepWPp.exists_pre fun c24 =>
    Wire.SepWPp.exists_pre fun cbuf => Wire.SepWPp.exists_pre fun c25 =>
    Wire.SepWPp.exists_pre fun c30 => Wire.SepWPp.exists_pre fun c29 => ?_
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    0 92
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    324 20
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp224_b : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub224 hsp
  have _hsp224 : (s0.sp - 224#64) &&& 15#64 = 0#64 := eq_of_beq _hsp224_b
  rcases hbs : x.bytes with _ | ⟨b0, bs1⟩
  · have hx1_0 : s0.readReg64 .x1 = 0#64 := by simp [hx1, hbs]
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (344)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF1 hsym1
    have hdec0 : IdentityKeyPairStructure.decode x.bytes = some IdentityKeyPairStructure.empty := by
      simp [hbs, IdentityKeyPairStructure.decode, decodeFieldsLoop]
    have hbase1 : IkpBaseState img s0 (s0.sp - 224#64) _ := {
      sp := by simp [*, arm64_norm]
      spAligned := by rw [State.spAligned]; simpa [arm64_norm] using spAligned_sub224 hsp
      frozen := hF1
      symtab := hsym1
      trace := by simp [*, arm64_norm]
      x26 := by simp [*, arm64_norm]
      x27 := by simp [*, arm64_norm]
      x28 := by simp [*, arm64_norm]
    }
    have hm16 := pointsTo64_pair_entails_memRegion16 (s0.sp - 224#64 + 32#64) x.bytesA 0#64
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm16
    have h144 := ikpFold144 (s0.sp - 224#64) 0#64 1#64 0#64 0#64 1#64 0#64
    dsimp only [vecHeader] at h144
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
    refine Wire.SepWPp.mono_pre
      (P' := (memRegion (s0.sp - 224#64) 32 ∗ memRegion (s0.sp - 224#64 + 96#64) 48 ∗
        memRegion x.ret 72 ∗
        vecU8Buf A 0#64 1#64 IdentityKeyPairStructure.empty.publicKey ∗
        vecU8Buf A 0#64 1#64 IdentityKeyPairStructure.empty.privateKey ∗
        logOff img ∗ A.pool ∗ stackAt (s0.sp - 224#64) (skipFieldStackX 100)) ∗
        (memRegion (s0.sp - 224#64 + 32#64) 16 ∗
          ((s0.sp - 224#64 + 48#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 56#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 64#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 72#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 80#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 88#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 168#64) ↦₆₄ (s0.sp - 224#64 + 32#64)) ∗
          ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗
          (x.bytesA ↦ₛ x.bytes)))
      (by
        dsimp only [IdentityKeyPairStructure.empty]
        have hemp0 : (⌜([] : List (BitVec 8)) = []⌝ : SepProp) = emp := pure_true_emp rfl
        try simp only [vecU8Buf_zero]
        try simp only [hemp0]
        try simp only [emp_sepConj]
        refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left hm16))
        unfold ikpCalleeSavedAt
        dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
        try rw [hbs]
        apply entails_of_eq
        try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
        try simp only [BitVec.add_assoc]
        try simp only [BitVec.reduceAdd]
        try simp only [bv_sub_add_lit]
        try simp only [BitVec.add_assoc]
        try simp only [BitVec.reduceAdd]
        try simp only [bv_sub_add_lit]
        try simp only [arm64_norm]
        ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := fun sf Pf => IkpBaseState img s0 (s0.sp - 224#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 224#64) 32 ∗ memRegion (s0.sp - 224#64 + 96#64) 48 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          logOff img ∗ A.pool ∗ stackAt (s0.sp - 224#64) (skipFieldStackX 100)))
      (hpost hdec0 (by decide) (by decide) hbase1
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, speWord, arm64_norm]) (by simp [*, IdentityKeyPairStructure.empty, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, IdentityKeyPairStructure.empty, arm64_norm]))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    refine Entails.trans ?_ (sepConj_mono_left h144)
    rw [hbs]
    apply entails_of_eq
    try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [arm64_norm]
    ac_rfl
  · have hlen63 : (b0 :: bs1).length < 2 ^ 63 := by rw [← hbs]; omega
    obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen63
    have hx1_cons : s0.readReg64 .x1 = BitVec.ofNat 64 (b0 :: bs1).length := by
      simpa [hbs] using hx1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (124)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF1 hsym1
    have hregs1 : IkpLoopRegs img s0 (s0.sp - 224#64) x.ret _ := {
      base := {
        sp := by simp [*, arm64_norm]
        spAligned := by rw [State.spAligned]; simpa [arm64_norm] using spAligned_sub224 hsp
        frozen := hF1
        symtab := hsym1
        trace := by simp [*, arm64_norm]
        x26 := by simp [*, arm64_norm]
        x27 := by simp [*, arm64_norm]
        x28 := by simp [*, arm64_norm]
      }
      x29 := by simp [*, arm64_norm]
      x19 := by simp [*, arm64_norm]
      x21 := by simp [*, arm64_norm]
      x24 := by simp [*, speWord, arm64_norm]
    }
    have hemptyLoop :
        ((s0.sp - 224#64 + 48#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 56#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 64#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 72#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 80#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 88#64) ↦₆₄ 0#64) ⊢
          ikpStructLoopOf A (s0.sp - 224#64 + 48#64) (b0 :: bs1).length
            IdentityKeyPairStructure.empty :=
      Entails.trans (ikpEmptyCells_entails_structAt A (s0.sp - 224#64))
        (ikpStructAt_entails_loopOf A ⟨0#64, 1#64⟩ ⟨0#64, 1#64⟩
          (s0.sp - 224#64 + 48#64) (b0 :: bs1).length IdentityKeyPairStructure.empty
          bytesMergeCapOk_zero bytesMergeCapOk_zero)
    have hinv0 : decodeFieldsLoop IdentityKeyPairStructure.mergeField
        (bs1.length + 1) IdentityKeyPairStructure.empty (b0 :: bs1) =
        IdentityKeyPairStructure.decode x.bytes := by
      simp [hbs, IdentityKeyPairStructure.decode]
    refine Wire.SepWPp.mono_pre
      (P' := (sliceCursorAt (s0.sp - 224#64 + 32#64) x.bytesA (b0 :: bs1) ∗
        ikpLoopCommon img A (s0.sp - 224#64) x.ret (b0 :: bs1).length
          IdentityKeyPairStructure.empty) ∗
        ikpCalleeSavedAt (s0.sp - 224#64) s0)
      (by
        unfold sliceCursorAt ikpLoopCommon ikpCalleeSavedAt
        dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
        refine Entails.trans ?_
          (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left hemptyLoop))))
        try rw [hbs]
        apply entails_of_eq
        try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
        try simp only [BitVec.add_assoc]
        try simp only [BitVec.reduceAdd]
        try simp only [bv_sub_add_lit]
        try simp only [BitVec.add_assoc]
        try simp only [BitVec.reduceAdd]
        try simp only [bv_sub_add_lit]
        try simp only [arm64_norm]
        ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (Q' := ikpExitPost img A s0 (s0.sp - 224#64) x.ret x.bytesA (b0 :: bs1)
        (IdentityKeyPair.tryFrom x.bytes))
      (hstep (hloop bs1.length) hinv0
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        hregs1 (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (Nat.le_refl _) hlen63)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    unfold ikpExitMem at hentf
    refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq
    try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [arm64_norm]
    rw [hbs]
    ac_rfl

theorem ikp_subroutine_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName)
      (identityKeyPairTryFromSpec A img) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hL
  dsimp only [identityKeyPairTryFromSpec, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, ⟨hx0, hx1_nat, hlt, hx8⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ logOff img ∗
        stackAt s0.sp smallRootStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have h1 : Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ logOff img ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sm Pm =>
        IkpBaseState img s0 (s0.sp - 224#64) sm ∧
        (Pm ⊢ memRegion (s0.sp - 224#64 - BitVec.ofNat 64 ikpSubStack)
            (ikpSubStack - skipFieldStackX 100) ∗
          stackAt (s0.sp - 224#64) (skipFieldStackX 100) ∗
          memRegion (s0.sp - 224#64) 144 ∗
          ((s0.sp - 224#64 + 168#64) ↦₆₄ (s0.sp - 224#64 + 32#64)) ∗
          ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗
          identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool))
      (tryFromQp s0) := by
    refine Wire.SepWPp.mono_pre
      (P' := (memRegion (s0.sp - 224#64) 144 ∗
        memRegion (s0.sp - 224#64 + 144#64) 80 ∗
        memRegion x.ret 72 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (skipFieldStackX 100)) ∗
        memRegion (s0.sp - 224#64 - BitVec.ofNat 64 ikpSubStack)
          (ikpSubStack - skipFieldStackX 100))
      (by
        rw [ikpRootStack_split s0.sp]
        apply entails_of_eq
        try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
        try simp only [BitVec.add_assoc]
        try simp only [BitVec.reduceAdd]
        try simp only [bv_sub_add_lit]
        try simp only [BitVec.add_assoc]
        try simp only [BitVec.reduceAdd]
        try simp only [bv_sub_add_lit]
        try simp only [arm64_norm]
        ac_rfl) ?_
    refine Wire.SepWPp.frame_tryFrom
      (ikp_entry_to_812_wp hC d hlt hpc hrun hsp hF hsym hx0 hx1 hx8)
      fun sm Pm ⟨hstm, hentm⟩ => ⟨hstm, ?_⟩
    refine Entails.trans (sepConj_mono_left hentm) ?_
    apply entails_of_eq
    try dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x29, Reg.x30]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [BitVec.add_assoc]
    try simp only [BitVec.reduceAdd]
    try simp only [bv_sub_add_lit]
    try simp only [arm64_norm]
    ac_rfl
  have hfull : Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ logOff img ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (identityKeyPairTryFromSpec A img).post x s0 sf))
      (tryFromQp s0) := by
    refine Wire.SepWPp.bind h1 ?_
    intro sm Pm hpcm hrunm ⟨hstm, hentm⟩
    exact Wire.SepWPp.mono_pre hentm
      (epilogue_812_wp (img := img) (A := A) (ext := ext) (x := x)
        (wbuf := s0.sp - 224#64 + 32#64) hstm hpcm hrunm)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ |
    ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact reaches_outcome_steps hsteps
      (reaches_outcome.of_outcome (Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
        Satisfies.mono (sepConj_mono_left hent_f) hmf⟩))
  · exact reaches_outcome_steps hsteps
      (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)))
  · exact (allowPanic_not_exited hoom).elim

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom

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
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Field Merge Branches

Verifies the per-tag field merge branches for `publicKey` (tag 1, `+264`), `privateKey` (tag 2,
`+92`), unknown tags (`skip_field`, `+284`), and tag dispatch (`+248..+260`).
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

section LoopMergeStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_lm (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_lm (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_lm (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_lm (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_lm (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_lm (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_lm (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_lm (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_lm (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_lm (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_lm (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_lm (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_lm (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_lm (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_lm (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_lm (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end LoopMergeStateSimp

/-! ## Helper lemmas for loop invariants and frame splitting -/

theorem vecU8Buf_cap_lt63 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => ?_
  rw [pure_true_emp h.2.1, emp_sepConj, pure_true_emp h, emp_sepConj]
  exact Entails.refl _

theorem ikpStructAt_entails_of (A : RustAlloc) (pk sk : VecPin) (a : BitVec 64)
    (m : IdentityKeyPairStructure) :
    ikpStructAt A pk sk a m ⊢ ikpStructOf A a m :=
  Entails.trans (sepExists_intro (fun sk' => ikpStructAt A pk sk' a m) sk)
    (sepExists_intro (fun pk' => ∃∗ sk', ikpStructAt A pk' sk' a m) pk)

theorem ikpMem144_prologue_cells (sp' : BitVec 64) :
    memRegion sp' 144 ⊢
      ∃∗ w88 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w64 : BitVec 64,
      ∃∗ w56 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w32 : BitVec 64,
        memRegion sp' 32 ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₆₄ w48) ∗ ((sp' + 56#64) ↦₆₄ w56) ∗
        ((sp' + 64#64) ↦₆₄ w64) ∗ ((sp' + 72#64) ↦₆₄ w72) ∗
        ((sp' + 80#64) ↦₆₄ w80) ∗ ((sp' + 88#64) ↦₆₄ w88) ∗
        memRegion (sp' + 96#64) 48 := by
  rw [show (144 : Nat) = 32 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 48)))))))) by decide,
    Prost.memRegion_split sp' 32 112 (by decide),
    Prost.memRegion_split (sp' + 32#64) 8 104 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64) 8 96 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64) 8 88 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64) 8 80 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 72 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem ikpEmptyCells_entails_structAt (A : RustAlloc) (sp' : BitVec 64) :
    ((sp' + 48#64) ↦₆₄ 0#64) ∗ ((sp' + 56#64) ↦₆₄ 1#64) ∗ ((sp' + 64#64) ↦₆₄ 0#64) ∗
      ((sp' + 72#64) ↦₆₄ 0#64) ∗ ((sp' + 80#64) ↦₆₄ 1#64) ∗ ((sp' + 88#64) ↦₆₄ 0#64) ⊢
      ikpStructAt A ⟨0#64, 1#64⟩ ⟨0#64, 1#64⟩ (sp' + 48#64) IdentityKeyPairStructure.empty := by
  unfold ikpStructAt IdentityKeyPairStructure.empty
  have h1ne : (1#64 : BitVec 64) ≠ 0 := by decide
  simp only [vecU8At_eq_header_buf, vecHeader, vecU8Buf_zero,
    BitVec.add_assoc, BitVec.reduceAdd, List.length_nil,
    pure_true_emp (And.intro trivial h1ne), sepConj_emp, sepConj_assoc]
  exact Entails.refl _

theorem tag_ge3_conds (tag : ℕ) (hge : 3 ≤ tag) (hlt : tag < 2 ^ 32) :
    let w1 := (BitVec.ofNat 64 tag).setWidth 32
    ((w1 == 2#32) = false) ∧ ((w1 == 1#32) = false) ∧ ((w1 != 1#32) = true) := by
  dsimp only
  rw [setWidth32_ofNat64]
  have h2 : BitVec.ofNat 32 tag ≠ 2#32 := by bv_omega
  have h1 : BitVec.ofNat 32 tag ≠ 1#32 := by bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr h1, bne_iff_ne.mpr h1⟩

/-! ## Field merge branches: `publicKey` (`+264`), `privateKey` (`+92`), `skipField` (`+284`) -/

/-- Tag 1 (`publicKey`) merge branch `+264..+280` and error stub `+848..+880` → `+916`. -/
theorem mergePubKey_264_cps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 264#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 108#64 →
      s1.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s1 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommon img A sp' x.ret rest.length { m with publicKey := v })
        (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗
        ikpLoopCommon img A sp' x.ret bs.length m)
      (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hcall := ikp_bytesMerge_ok d
  have herr := @decodeErrorPush_916_wp img C A S ext hC d x s0
  unfold ikpLoopCommon ikpStructLoopOf ikpStructAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine Wire.SepWPp.exists_pre fun pk => Wire.SepWPp.exists_pre fun sk =>
    Wire.SepWPp.pure_pre fun ⟨hpk_ok, hsk_ok⟩ => ?_
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    264 20
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    848 36
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hregs.base.sp
  have _hsp_align := hregs.base.spAligned
  have h29 := hregs.x29
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
    (mid := entry + bv% (2 ^ 64 +
      (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
  intro hF1 hsym1
  have hregs1 := hregs.of_steps hF1 hsym1
    (by simp [*, arm64_norm])
    (by simp [*, hregs.base.trace, arm64_norm])
    (by simp [*, hregs.base.x26, arm64_norm])
    (by simp [*, hregs.base.x27, arm64_norm])
    (by simp [*, hregs.base.x28, arm64_norm])
    (by simp [*, arm64_norm])
    (by simp [*, hregs.x19, arm64_norm])
    (by simp [*, hregs.x21, arm64_norm])
    (by simp [*, hregs.x24, arm64_norm])
  refine Wire.SepWPp.call_tryFrom
    ⟨wt, sp' + 48#64, pk.cap, pk.ptr, m.publicKey, sp' + 168#64, sp' + 32#64, ptr, bs⟩ hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs1.base.spAligned) hF1 hsym1
    (ret_pc := entry + bv% (276)) (by simp [*, arm64_norm])
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := vecU8At A (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
      ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
      sliceCursorAt (sp' + 32#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 48#64 = sp' + 48#64 ∧ sp' + 168#64 = sp' + 168#64 ∧
      bs.length < 9223372036854775808 ∧ BytesMergeCapOk pk.cap bs.length)
    (by simp [*, bytesMergeRawSpecX, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, hlen, hpk_ok⟩
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, _, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => ?_
    simp only [sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hcap' => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
      (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hsp2_align := hregs2.base.spAligned
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (108)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF3 hsym3
    have hstruct : vecU8At A (sp' + 48#64) cap' ptr' v ∗
        vecU8At A (sp' + 72#64) sk.cap sk.ptr m.privateKey ⊢
        ikpStructLoopOf A (sp' + 48#64) rest.length { m with publicKey := v } := by
      simpa [ikpStructAt, BitVec.add_assoc] using
        ikpStructAt_entails_loopOf A ⟨cap', ptr'⟩ sk (sp' + 48#64) rest.length
          { m with publicKey := v } hcap' (bytesMergeCapOk_mono hsk_ok hrest_le)
    refine Wire.SepWPp.mono_pre
      (P' := sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
        ikpLoopCommon img A sp' x.ret rest.length { m with publicKey := v })
      (by
        unfold ikpLoopCommon
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
        apply entails_of_eq
        try rw [hstack]
        try rw [hregs1.base.sp]
        try rw [hregs2.base.sp]
        try simp only [arm64_norm]
        ac_rfl) ?_
    exact hcont v rest _ hm
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs2.of_steps hF3 hsym3
        (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm])
        (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm])
        (by simp [*, hregs2.base.x28, arm64_norm])
        (by simp [*, hregs2.x29, arm64_norm])
        (by simp [*, hregs2.x19, arm64_norm])
        (by simp [*, hregs2.x21, arm64_norm])
        (by simp [*, hregs2.x24, arm64_norm]))
  | none =>
    dsimp only
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
      (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hsp2_align := hregs2.base.spAligned
    have _hx29_2 := hregs2.x29
    have _hne : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne hx0_ne
    rw [ikpMem48_split8 sp', ProofLib.memRegion_eight (sp' + 96#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w0 => ?_
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (916)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF3 hsym3
    have hstruct : vecU8At A (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
        vecU8At A (sp' + 72#64) sk.cap sk.ptr m.privateKey ⊢
        ikpStructOf A (sp' + 48#64) m := by
      simpa [ikpStructAt, BitVec.add_assoc] using
        ikpStructAt_entails_of A pk sk (sp' + 48#64) m
    refine Wire.SepWPp.mono_pre
      (P' := memRegion sp' 32 ∗
        memRegion (sp' + 32#64) 16 ∗
        ikpStructOf A (sp' + 48#64) m ∗
        ((sp' + 96#64) ↦₆₄ s2.readReg64 (Reg.gpr 0#5)) ∗ memRegion (sp' + 104#64) 40 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
        memRegion x.ret 72 ∗
        (ptr ↦ₛ bs) ∗
        logOff img ∗
        A.pool ∗
        stackAt sp' (skipFieldStackX 100) ∗
        decodeErrorAtStackLen A (s2.readReg64 (Reg.gpr 0#5)) 0)
      (by
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
        apply entails_of_eq
        try rw [hstack]
        try rw [hregs1.base.sp]
        try rw [hregs2.base.sp]
        try simp only [arm64_norm]
        ac_rfl) ?_
    exact herr (hnone hm)
      (hregs2.of_steps hF3 hsym3
        (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm])
        (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm])
        (by simp [*, hregs2.base.x28, arm64_norm])
        (by simp [*, hregs2.x29, arm64_norm])
        (by simp [*, hregs2.x19, arm64_norm])
        (by simp [*, hregs2.x21, arm64_norm])
        (by simp [*, hregs2.x24, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) hx0_ne (by decide)

/-- Tag 2 (`privateKey`) merge branch `+92..+104` and error stub `+884..+912` → `+916`. -/
theorem mergePrivKey_92_cps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 92#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 108#64 →
      s1.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s1 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommon img A sp' x.ret rest.length { m with privateKey := v })
        (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗
        ikpLoopCommon img A sp' x.ret bs.length m)
      (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hcall := ikp_bytesMerge_ok d
  have herr := @decodeErrorPush_916_wp img C A S ext hC d x s0
  unfold ikpLoopCommon ikpStructLoopOf ikpStructAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine Wire.SepWPp.exists_pre fun pk => Wire.SepWPp.exists_pre fun sk =>
    Wire.SepWPp.pure_pre fun ⟨hpk_ok, hsk_ok⟩ => ?_
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    92 16
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    884 32
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hregs.base.sp
  have _hsp_align := hregs.base.spAligned
  have h29 := hregs.x29
  have h21 := hregs.x21
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
    (mid := entry + bv% (2 ^ 64 +
      (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
  intro hF1 hsym1
  have hregs1 := hregs.of_steps hF1 hsym1
    (by simp [*, arm64_norm])
    (by simp [*, hregs.base.trace, arm64_norm])
    (by simp [*, hregs.base.x26, arm64_norm])
    (by simp [*, hregs.base.x27, arm64_norm])
    (by simp [*, hregs.base.x28, arm64_norm])
    (by simp [*, arm64_norm])
    (by simp [*, hregs.x19, arm64_norm])
    (by simp [*, arm64_norm])
    (by simp [*, hregs.x24, arm64_norm])
  refine Wire.SepWPp.call_tryFrom
    ⟨wt, sp' + 72#64, sk.cap, sk.ptr, m.privateKey, sp' + 168#64, sp' + 32#64, ptr, bs⟩ hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs1.base.spAligned) hF1 hsym1
    (ret_pc := entry + bv% (104)) (by simp [*, arm64_norm])
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := vecU8At A (sp' + 72#64) sk.cap sk.ptr m.privateKey ∗
      ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
      sliceCursorAt (sp' + 32#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 72#64 = sp' + 72#64 ∧ sp' + 168#64 = sp' + 168#64 ∧
      bs.length < 9223372036854775808 ∧ BytesMergeCapOk sk.cap bs.length)
    (by simp [*, bytesMergeRawSpecX, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, hlen, hsk_ok⟩
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, _, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => ?_
    simp only [sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hcap' => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
      (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hsp2_align := hregs2.base.spAligned
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (108)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF3 hsym3
    have hstruct : vecU8At A (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
        vecU8At A (sp' + 72#64) cap' ptr' v ⊢
        ikpStructLoopOf A (sp' + 48#64) rest.length { m with privateKey := v } := by
      simpa [ikpStructAt, BitVec.add_assoc] using
        ikpStructAt_entails_loopOf A pk ⟨cap', ptr'⟩ (sp' + 48#64) rest.length
          { m with privateKey := v } (bytesMergeCapOk_mono hpk_ok hrest_le) hcap'
    refine Wire.SepWPp.mono_pre
      (P' := sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
        ikpLoopCommon img A sp' x.ret rest.length { m with privateKey := v })
      (by
        unfold ikpLoopCommon
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
        apply entails_of_eq
        try rw [hstack]
        try rw [hregs1.base.sp]
        try rw [hregs2.base.sp]
        try simp only [arm64_norm]
        ac_rfl) ?_
    exact hcont v rest _ hm
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs2.of_steps hF3 hsym3
        (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm])
        (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm])
        (by simp [*, hregs2.base.x28, arm64_norm])
        (by simp [*, hregs2.x29, arm64_norm])
        (by simp [*, hregs2.x19, arm64_norm])
        (by simp [*, hregs2.x21, arm64_norm])
        (by simp [*, hregs2.x24, arm64_norm]))
  | none =>
    dsimp only
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
      (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hsp2_align := hregs2.base.spAligned
    have _hx29_2 := hregs2.x29
    have _hne : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne hx0_ne
    rw [ikpMem48_split8 sp', ProofLib.memRegion_eight (sp' + 96#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w0 => ?_
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (916)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF3 hsym3
    have hstruct : vecU8At A (sp' + 48#64) pk.cap pk.ptr m.publicKey ∗
        vecU8At A (sp' + 72#64) sk.cap sk.ptr m.privateKey ⊢
        ikpStructOf A (sp' + 48#64) m := by
      simpa [ikpStructAt, BitVec.add_assoc] using
        ikpStructAt_entails_of A pk sk (sp' + 48#64) m
    refine Wire.SepWPp.mono_pre
      (P' := memRegion sp' 32 ∗
        memRegion (sp' + 32#64) 16 ∗
        ikpStructOf A (sp' + 48#64) m ∗
        ((sp' + 96#64) ↦₆₄ s2.readReg64 (Reg.gpr 0#5)) ∗ memRegion (sp' + 104#64) 40 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
        memRegion x.ret 72 ∗
        (ptr ↦ₛ bs) ∗
        logOff img ∗
        A.pool ∗
        stackAt sp' (skipFieldStackX 100) ∗
        decodeErrorAtStackLen A (s2.readReg64 (Reg.gpr 0#5)) 0)
      (by
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))
        apply entails_of_eq
        try rw [hstack]
        try rw [hregs1.base.sp]
        try rw [hregs2.base.sp]
        try simp only [arm64_norm]
        ac_rfl) ?_
    exact herr (hnone hm)
      (hregs2.of_steps hF3 hsym3
        (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm])
        (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm])
        (by simp [*, hregs2.base.x28, arm64_norm])
        (by simp [*, hregs2.x29, arm64_norm])
        (by simp [*, hregs2.x19, arm64_norm])
        (by simp [*, hregs2.x21, arm64_norm])
        (by simp [*, hregs2.x24, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, arm64_norm]) hx0_ne (by decide)

/-- Unknown-tag (`skip_field`) branch `+284..+300` and error stub `+612` → `+616`. -/
theorem mergeSkipField_284_cps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 284#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_lt : tag < 2 ^ 32)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (rest : List (BitVec 8)) (s1 : State),
      skipField (2 * bs.length + 2) 100 tag wt bs = some rest →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 108#64 →
      s1.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s1 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommon img A sp' x.ret rest.length m)
        (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : skipField (2 * bs.length + 2) 100 tag wt bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗
        ikpLoopCommon img A sp' x.ret bs.length m)
      (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hcall := ikp_skipField_ok d
  have herr := @decodeErr_616_wp img C A S ext hC d x s0
  unfold ikpLoopCommon
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    284 20
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    612 4
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hregs.base.sp
  have _hsp_align := hregs.base.spAligned
  have h29 := hregs.x29
  refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
    (mid := entry + bv% (2 ^ 64 +
      (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
  intro hF1 hsym1
  have hregs1 := hregs.of_steps hF1 hsym1
    (by simp [*, arm64_norm])
    (by simp [*, hregs.base.trace, arm64_norm])
    (by simp [*, hregs.base.x26, arm64_norm])
    (by simp [*, hregs.base.x27, arm64_norm])
    (by simp [*, hregs.base.x28, arm64_norm])
    (by simp [*, arm64_norm])
    (by simp [*, hregs.x19, arm64_norm])
    (by simp [*, hregs.x21, arm64_norm])
    (by simp [*, hregs.x24, arm64_norm])
  refine Wire.SepWPp.call_tryFrom ⟨wt, tag, 100, sp' + 168#64, sp' + 32#64, ptr, bs⟩ hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs1.base.spAligned) hF1 hsym1
    (ret_pc := entry + bv% (296)) (by simp [*, arm64_norm])
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗ sliceCursorAt (sp' + 32#64) ptr bs ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag ∧ tag < 4294967296 ∧
      sp' + 168#64 = sp' + 168#64 ∧
      (100#64 : BitVec 64).setWidth 32 = 100#32 ∧ 100 < 4294967296 ∧
      bs.length < 9223372036854775808)
    (by simp [*, skipFieldSpecX, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, setWidth32_ofNat64 tag, htag_lt, rfl, rfl, by decide, hlen⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [skipFieldSpecX]
  cases hs : skipField (2 * bs.length + 2) 100 tag wt bs with
  | some rest =>
    dsimp only
    obtain ⟨k, _, hrest⟩ := skipField_suffix hs
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
      (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hsp2_align := hregs2.base.spAligned
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (108)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre
      (P' := sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
        ikpLoopCommon img A sp' x.ret rest.length m)
      (by
        unfold ikpLoopCommon
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (ikpStructLoopOf_mono A (sp' + 48#64) m hrest_le))))
        apply entails_of_eq
        rw [hregs1.base.sp]
        try simp only [arm64_norm]
        ac_rfl) ?_
    exact hcont rest _ hs
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (hregs2.of_steps hF3 hsym3
        (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm])
        (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm])
        (by simp [*, hregs2.base.x28, arm64_norm])
        (by simp [*, hregs2.x29, arm64_norm])
        (by simp [*, hregs2.x19, arm64_norm])
        (by simp [*, hregs2.x21, arm64_norm])
        (by simp [*, hregs2.x24, arm64_norm]))
  | none =>
    dsimp only
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hF2 hsym2
      (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    have _hne : (s2.readReg64 .x0 == 0#64) = false := beq_false_of_ne hx0_ne
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (616)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre
      (P' := memRegion sp' 32 ∗
        memRegion (sp' + 32#64) 16 ∗
        ikpStructOf A (sp' + 48#64) m ∗
        memRegion (sp' + 96#64) 48 ∗
        ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
        memRegion x.ret 72 ∗
        (ptr ↦ₛ bs) ∗
        logOff img ∗
        A.pool ∗
        stackAt sp' (skipFieldStackX 100) ∗
        decodeErrorAt A (s2.readReg64 (Reg.gpr 0#5)))
      (by
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (ikpStructLoopOf_entails_of A (sp' + 48#64) bs.length m)
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (decodeErrorWith_entails_at A (s2.readReg64 (Reg.gpr 0#5)) 0)))))))))))
        apply entails_of_eq
        rw [hregs1.base.sp]
        try simp only [arm64_norm]
        ac_rfl) ?_
    exact herr (hnone hs)
      (hregs2.base.of_steps hF3 hsym3
        (by simp [*, hregs2.base.sp, arm64_norm])
        (by simp [*, hregs2.base.trace, arm64_norm])
        (by simp [*, hregs2.base.x26, arm64_norm])
        (by simp [*, hregs2.base.x27, arm64_norm])
        (by simp [*, hregs2.base.x28, arm64_norm]))
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
      (by simp [*, hregs2.x19, arm64_norm])
      (by simp [*, hregs2.x24, arm64_norm])
      (by simp [*, arm64_norm])

/-! ## Tag dispatch (`+248..+260`) and `mergeField_248_cps` -/

theorem dispatch_tag_248_cps {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {sp' ret : BitVec 64} {tag : ℕ}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 248#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' ret s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (h1 : tag = 1 → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 264#64 →
      s1.status = .Running → IkpLoopRegs img s0 sp' ret s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1 P Q Qp)
    (h2 : tag = 2 → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 92#64 →
      s1.status = .Running → IkpLoopRegs img s0 sp' ret s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1 P Q Qp)
    (h3 : 3 ≤ tag → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 284#64 →
      s1.status = .Running → IkpLoopRegs img s0 sp' ret s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1 P Q Qp) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s P Q Qp := by
  let H := Rust.withPanics ext
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    248 16
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp
  have _hsp_align := hregs.base.spAligned
  rcases tag with _ | _ | _ | n
  · omega
  · refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
      (mid := entry + bv% (264)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF1 hsym1
    exact h1 rfl _ (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
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
  · refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
      (mid := entry + bv% (92)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF1 hsym1
    exact h2 rfl _ (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
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
  · obtain ⟨hc2, hc1, hc1_ne⟩ := tag_ge3_conds (n + 3) (by omega) htag_lt
    refine Wire.SepWPp.of_sepWP_frozen hregs.base.frozen hregs.base.symtab
      (mid := entry + bv% (284)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_
    intro hF1 hsym1
    exact h3 (by omega) _ (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
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
      (by simp [*, arm64_norm]) (by simp [*, arm64_norm])

theorem mergeField_248_cps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 248#64)
    (hrun : s.status = .Running)
    (hregs : IkpLoopRegs img s0 sp' x.ret s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (m' : IdentityKeyPairStructure) (rest : List (BitVec 8)) (s1 : State),
      IdentityKeyPairStructure.mergeField m tag wt bs = some (m', rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 108#64 →
      s1.status = .Running →
      IkpLoopRegs img s0 sp' x.ret s1 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommon img A sp' x.ret rest.length m')
        (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
        (tryFromQp s0))
    (hnone : IdentityKeyPairStructure.mergeField m tag wt bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗
        ikpLoopCommon img A sp' x.ret bs.length m)
      (ikpExitPost img A s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (tryFromQp s0) := by
  refine dispatch_tag_248_cps hpc hrun hregs hx1 htag_ge htag_lt
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hx1_1 => ?_)
  · subst htag
    exact mergePubKey_264_cps hC d hpc1 hrun1 hregs1 (hx0_1.trans hx0) hlen
      (fun v rest s2 hm => hcont { m with publicKey := v } rest s2
        (by simp [IdentityKeyPairStructure.mergeField, hm]))
      (fun hm => hnone (by simp [IdentityKeyPairStructure.mergeField, hm]))
  · subst htag
    exact mergePrivKey_92_cps hC d hpc1 hrun1 hregs1 (hx0_1.trans hx0) hlen
      (fun v rest s2 hm => hcont { m with privateKey := v } rest s2
        (by simp [IdentityKeyPairStructure.mergeField, hm]))
      (fun hm => hnone (by simp [IdentityKeyPairStructure.mergeField, hm]))
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    exact mergeSkipField_284_cps hC d hpc1 hrun1 hregs1 (hx0_1.trans hx0) hx1_1 htag_lt hlen
      (fun rest s2 hs => hcont m rest s2
        (by simp [IdentityKeyPairStructure.mergeField, skipUnknown, recursionLimit, hs]))
      (fun hs => hnone
        (by simp [IdentityKeyPairStructure.mergeField, skipUnknown, recursionLimit, hs]))

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom

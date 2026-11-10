/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
import LibsignalBinary.Proofs.Cli.ShardFill.ChainMerge5Decode
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Ratchet-Key Field Decoding for `message::merge<Chain>`

Steps one iteration (`+0x0a8 → +0x0a8`) of `Chain3LoopAtW` inside
`prost::encoding::message::merge<Chain>` across protobuf tags 1 (`sender_ratchet_key`) and 2
(`sender_ratchet_key_private`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
  (sliceCursorAt sliceCursorAfter BytesMergeGhost BytesMergeCapOk DecodeVarintSlowGhost
   bytesMergeCapOk_of_len_lt32)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## Register preservation and stack alignment -/

/-- Register preservation across one `Chain3LoopAtW` iteration (`+0x0a8 → +0x0a8`), covering
`x19..x24`, `x26..x29`, and `calleeSavedVRegs` (`x25` is excluded from the loop invariant). -/
def Chain3LoopRegsPreserved (s0 s1 : State) : Prop :=
  s1.readReg64 .x19 = s0.readReg64 .x19 ∧
  s1.readReg64 .x20 = s0.readReg64 .x20 ∧
  s1.readReg64 .x21 = s0.readReg64 .x21 ∧
  s1.readReg64 .x22 = s0.readReg64 .x22 ∧
  s1.readReg64 .x23 = s0.readReg64 .x23 ∧
  s1.readReg64 .x24 = s0.readReg64 .x24 ∧
  s1.readReg64 .x26 = s0.readReg64 .x26 ∧
  s1.readReg64 .x27 = s0.readReg64 .x27 ∧
  s1.readReg64 .x28 = s0.readReg64 .x28 ∧
  s1.readReg64 .x29 = s0.readReg64 .x29 ∧
  calleeSavedVRegs s1 = calleeSavedVRegs s0

set_option maxHeartbeats 400000 in
theorem Chain3LoopRegsPreserved.refl (s : State) : Chain3LoopRegsPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 400000 in
theorem Chain3LoopRegsPreserved.trans {s0 s1 s2 : State}
    (h01 : Chain3LoopRegsPreserved s0 s1) (h12 : Chain3LoopRegsPreserved s1 s2) :
    Chain3LoopRegsPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2.2⟩

set_option maxHeartbeats 400000 in
theorem Chain3LoopRegsPreserved.of_calleeSaved {s0 s1 : State}
    (h : CalleeSavedPreserved s0 s1) : Chain3LoopRegsPreserved s0 s1 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

set_option maxHeartbeats 400000 in
theorem sp_sub_240_aligned_c3 {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0xf0#64) &&& 15#64 = 0#64 := by
  revert h; bv_robdd

set_option maxHeartbeats 400000 in
theorem sp0_aligned_of_sub_240_c3 {sp0 : BitVec 64} (h : (sp0 - 0xf0#64) &&& 15#64 = 0#64) :
    sp0 &&& 15#64 = 0#64 := by
  revert h; bv_robdd

set_option maxHeartbeats 400000 in
theorem decodeVarint_0a_cons (rest : List (BitVec 8)) :
    decodeVarint (0x0a#8 :: rest) = some (0x0a#64, rest) := rfl

set_option maxHeartbeats 400000 in
theorem decodeVarint_12_cons (rest : List (BitVec 8)) :
    decodeVarint (0x12#8 :: rest) = some (0x12#64, rest) := rfl

/-! ## Callee step helpers -/

set_option maxHeartbeats 400000 in
/-- Steps a `bl decode_varint` call inside `message::merge<Chain>` on a 1-byte varint
`b0 :: rem1` with `decodeVarint (b0 :: rem1) = some (v, rem1)`. -/
theorem step_chain3_decodeVarint_atW {A : RustAlloc} (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hC : Chain3CalleesWExt A img ext)
    (bufRef slot curPtr sp0 ret_pc v : BitVec 64) (b0 : BitVec 8) (rem1 : List (BitVec 8))
    (hdv : decodeVarint (b0 :: rem1) = some (v, rem1))
    (hlen_lt : (b0 :: rem1).length < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hP : P = ((bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr (b0 :: rem1) ∗
      A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      sm.readReg64 .x1 = v →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          (curPtr ↦₈ b0) ∗
          sliceCursorAt slot (curPtr + 1#64) rem1 ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R)) := by
  have hcall := c3_decodeVarint_ok_sub hC
  have hlen_lt63 : (b0 :: rem1).length < 2 ^ 63 := by omega
  rw [hP]
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_240_aligned_c3 halign
  refine SepWPp.call_frozen_seedChain
    (x := DecodeVarintSlowGhost.mk bufRef slot curPtr (b0 :: rem1))
    (F := memRegion (sp0 - 0xf0#64 - BitVec.ofNat 64 chainMerge3SubStackX)
      (chainMerge3SubStackX - decodeVarint2StackX) ∗ F)
    hcall hpc hrun hsp_aligned hF hsym hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_c3Sub_to_decodeVarint (sp0 - 0xf0#64)] at hm
    dsimp only [Spec.inImage, decodeVarint2SpecX]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ⟨hx0, hlen_lt63⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [Spec.inImage, decodeVarint2SpecX, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hFm hsymm hcsm
    rw [hsp] at hspm
    dsimp only [Spec.inImage, decodeVarint2SpecX]
    rw [hdv, hsp]
    dsimp only
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, hx1m⟩ => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr [b0] rem1
    simp only [List.singleton_append, List.length_singleton, pointsToBytes_cons,
      pointsToBytes_nil, sepConj_emp] at hcur
    refine SepWPp.mono_pre_seedChain ?_
      (hnext sm hpcm hrunm hspm hFm hsymm (htrm.trans htr) hcsm hx0m hx1m)
    rw [hcur, stackAt_c3Sub_to_decodeVarint (sp0 - 0xf0#64)]
    exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
/-- Steps a `bl bytes::merge` call inside `message::merge<Chain>` on a length-prefixed
non-empty field `[BitVec.ofNat 8 b.length] ++ b` (`b.length < 128`) into an empty `chain3VecAt`. -/
theorem step_chain3_bytesMerge_atW {A : RustAlloc} (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hC : Chain3CalleesWExt A img ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hb_ne : b ≠ [])
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = (chain3VecAt A v [] ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
      A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        ((chain3VecAt A v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R)) := by
  have hcall := c3_bytesMerge_ok_sub hC
  have hlen_lt63 : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 63 := by omega
  rw [hP]
  refine SepWPp.mono_pre_seedChain
    (sepConj_mono_left (sepConj_mono_left (chain3VecAt_nil_elim A v))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun ptr0 => ?_
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_240_aligned_c3 halign
  refine SepWPp.call_frozen_seedChain
    (x := BytesMergeGhost.mk .lengthDelimited v 0#64 ptr0 [] bufRef slot curPtr
      ([BitVec.ofNat 8 b.length] ++ b ++ rest))
    (F := F)
    hcall hpc hrun hsp_aligned hF hsym hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_c3Sub_eq_bytesMerge (sp0 - 0xf0#64)] at hm
    dsimp only [bytesMerge3Spec, Spec.inImage, bytesMerge3RawSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ⟨hx0, hx1, hx2, hlen_lt63, Prost.bytesMergeCapOk_zero⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [bytesMerge3Spec, Spec.inImage, bytesMerge3RawSpec, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hFm hsymm hcsm
    rw [hsp] at hspm
    have hmB := mergeBytes_lt128_seedChain b rest hb
    dsimp only [bytesMerge3Spec, Spec.inImage, bytesMerge3RawSpec]
    rw [hmB, hsp]
    dsimp only
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun _ => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    have hlen1 : ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 := by simp
    rw [hlen1] at hcur
    have hv : vecU8At A v cap' ptr' b ⊢ chain3VecAt A v b :=
      chain3VecAt_of_ne_nil A v cap' ptr' hb_ne
    refine SepWPp.mono_pre_seedChain ?_
      (hnext sm hpcm hrunm hspm hFm hsymm (htrm.trans htr) hcsm hx0m)
    rw [hcur, ← stackAt_c3Sub_eq_bytesMerge (sp0 - 0xf0#64)]
    have hEq1 :
        (bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗
          vecU8At A v cap' ptr' b ∗
          ((curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest) ∗ F =
        vecU8At A v cap' ptr' b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F) := by
      ac_rfl
    have hEq2 :
        chain3VecAt A v b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F) =
        (chain3VecAt A v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F := by
      ac_rfl
    rw [hEq1, ← hEq2]
    exact sepConj_mono_left hv

/-! ## Stepping tags 1 and 2 -/

set_option maxHeartbeats 400000 in
theorem step_chain3Tag1_atW {A : RustAlloc} (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hC : Chain3CalleesWExt A img ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (srk rest tail : List (BitVec 8))
    (hsrk_lt : srk.length < 128)
    (hsrk_ne : srk ≠ [])
    (hlen_lt : (pbBytes 1 srk ++ rest ++ tail).length < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      Chain3LoopRegsPreserved s0 sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          chain3VecAt A a srk ∗
          (ptr ↦ₛ pbBytes 1 srk) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 1 srk).length) (rest ++ tail) ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        chain3VecAt A a [] ∗
        sliceCursorAt slot ptr (pbBytes 1 srk ++ (rest ++ tail)) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R)) := by
  have hpb : pbBytes 1 srk = 0x0a#8 :: BitVec.ofNat 8 srk.length :: srk :=
    DeserializeGeneral.pbBytes_lt128_eq_seedChain 1 (by decide) srk hsrk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)
  have hcons_eq : pbBytes 1 srk ++ (rest ++ tail) = 0x0a#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x0a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x0a#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) →
      s1.status = .Running →
      s1.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded s1 →
      s1.symtab = img.symtab →
      s1.trace = s_init.trace →
      s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xc0#64 →
      s1.readReg64 .x0 = bufRef →
      Chain3LoopRegsPreserved s0 s1 →
      SepWPp (SP2Ext img.base ext) ret s1
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr (0x0a#8 :: rem1) ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ (chain3VecAt A a [] ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
  · intro hnext1
    chain3_fetches_range img.base (Rust.withPanics ext) 0xa8 0xbc
    dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext1 ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
    examples_hide_fetches
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h21 : s0.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := hx21
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64)) hF hsym ?_
    rw [hcons_eq]
    unfold sliceCursorAt
    simp only [sepConj_assoc]
    iterate 6 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hlr1 hx0_1 hregs1
    refine step_chain3_decodeVarint_atW img hC bufRef slot ptr sp0
      ((SP2Ext img.base ext).fnAddr chainMerge3Name + 0xc0#64) 0x0a#64 0x0a#8 rem1
      (decodeVarint_0a_cons rem1) hlen_cons_lt
      hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine (?_ :
      (∀ (s3 : State),
        s3.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name +
          bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) →
        s3.status = .Running →
        s3.sp = sp0 - 0xf0#64 →
        img.FrozenLoaded s3 →
        s3.symtab = img.symtab →
        s3.trace = s_init.trace →
        s3.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x1f0#64 →
        (s3.readReg64 .x0).setWidth 8 = 2#8 →
        s3.readReg64 .x1 = a →
        s3.readReg64 .x2 = bufRef →
        Chain3LoopRegsPreserved s0 s3 →
        SepWPp (SP2Ext img.base ext) ret s3
          ((chain3VecAt A a [] ∗
            (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot (ptr + 1#64) rem1 ∗
            A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ ((ptr ↦₈ 0x0a#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
    · intro hnext3
      chain3_fetches_range img.base (Rust.withPanics ext) 0xc0 0xf4
      chain3_fetches_range img.base (Rust.withPanics ext) 0x1e0 0x1ec
      dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc2 hnext3 ⊢
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
      examples_hide_fetches
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      have h1_2 : s2.readReg64 (Reg.gpr 1#5) = 0x0a#64 := hx1_2
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hregs2.1.trans hx19
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hregs2.2.1.trans hx20
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64)) hF2 hsym2 ?_
      iterate 18 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine SepWPp.mono_pre_seedChain ?_ (hnext3 _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (hregs2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      exact sep_ac_seedChain (by ac_rfl)
    · intro s3 hpc3 hrun3 hsp3 hF3 hsym3 htr3 hlr3 hx0_3 hx1_3 hx2_3 hregs3
      have hrem1_lt : ([BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)).length < 2 ^ 62 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chain3_bytesMerge_atW img hC
        a bufRef slot (ptr + 1#64) sp0
        ((SP2Ext img.base ext).fnAddr chainMerge3Name + 0x1f0#64)
        srk (rest ++ tail) hsrk_lt hsrk_ne hrem1_lt
        hpc3 hrun3 hsp3 halign hF3 hsym3 htr3 hlr3 hx0_3 hx1_3 hx2_3 rfl ?_
      intro s4 hpc4 hrun4 hsp4 hF4 hsym4 htr4 hcs4 hx0_4
      chain3_fetches_range img.base (Rust.withPanics ext) 0x1f0 0x1f4
      dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hpc4 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
      examples_hide_fetches
      have h0_4 : s4.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_4
      refine SepWPp.of_sepWP_frozen_seedChain (mid := s0.pc) hF4 hsym4 ?_
      iterate 2 wp_step
      refine SepWP.done (by simp only [hpc, arm64_norm]) (by simp only [hrun4, arm64_norm]) ?_
      intro hF5 hsym5
      have hregs4 : Chain3LoopRegsPreserved s0 s4 := hregs3.trans (.of_calleeSaved hcs4)
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun4, arm64_norm])
        (by simp only [hsp4, arm64_norm]) hF5 hsym5 (by simp only [htr4, arm64_norm])
        (hregs4.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [DeserializeGeneral.pbBytes_ptr_advance_seedChain 1 (by decide) ptr srk hsrk_lt,
        ← DeserializeGeneral.pbBytes_pointsTo_combine_seedChain 1 (by decide) ptr srk hsrk_lt]
      exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
theorem step_chain3Tag2_atW {A : RustAlloc} (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hC : Chain3CalleesWExt A img ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (priv rest tail : List (BitVec 8))
    (hpriv_lt : priv.length < 128)
    (hpriv_ne : priv ≠ [])
    (hlen_lt : (pbBytes 2 priv ++ rest ++ tail).length < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64 →
      sm.status = .Running →
      sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      Chain3LoopRegsPreserved s0 sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          chain3VecAt A (a + 0x18#64) priv ∗
          (ptr ↦ₛ pbBytes 2 priv) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 priv).length) (rest ++ tail) ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        chain3VecAt A (a + 0x18#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 priv ++ (rest ++ tail)) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R)) := by
  have hpb : pbBytes 2 priv = 0x12#8 :: BitVec.ofNat 8 priv.length :: priv :=
    DeserializeGeneral.pbBytes_lt128_eq_seedChain 2 (by decide) priv hpriv_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)
  have hcons_eq : pbBytes 2 priv ++ (rest ++ tail) = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) →
      s1.status = .Running →
      s1.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded s1 →
      s1.symtab = img.symtab →
      s1.trace = s_init.trace →
      s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xc0#64 →
      s1.readReg64 .x0 = bufRef →
      Chain3LoopRegsPreserved s0 s1 →
      SepWPp (SP2Ext img.base ext) ret s1
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr (0x12#8 :: rem1) ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ (chain3VecAt A (a + 0x18#64) [] ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
  · intro hnext1
    chain3_fetches_range img.base (Rust.withPanics ext) 0xa8 0xbc
    dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext1 ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
    examples_hide_fetches
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h21 : s0.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := hx21
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64)) hF hsym ?_
    rw [hcons_eq]
    unfold sliceCursorAt
    simp only [sepConj_assoc]
    iterate 6 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hlr1 hx0_1 hregs1
    refine step_chain3_decodeVarint_atW img hC bufRef slot ptr sp0
      ((SP2Ext img.base ext).fnAddr chainMerge3Name + 0xc0#64) 0x12#64 0x12#8 rem1
      (decodeVarint_12_cons rem1) hlen_cons_lt
      hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine (?_ :
      (∀ (s3 : State),
        s3.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name +
          bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) →
        s3.status = .Running →
        s3.sp = sp0 - 0xf0#64 →
        img.FrozenLoaded s3 →
        s3.symtab = img.symtab →
        s3.trace = s_init.trace →
        s3.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x110#64 →
        (s3.readReg64 .x0).setWidth 8 = 2#8 →
        s3.readReg64 .x1 = a + 0x18#64 →
        s3.readReg64 .x2 = bufRef →
        Chain3LoopRegsPreserved s0 s3 →
        SepWPp (SP2Ext img.base ext) ret s3
          ((chain3VecAt A (a + 0x18#64) [] ∗
            (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot (ptr + 1#64) rem1 ∗
            A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ ((ptr ↦₈ 0x12#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
    · intro hnext3
      chain3_fetches_range img.base (Rust.withPanics ext) 0xc0 0x10c
      dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc2 hnext3 ⊢
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
      examples_hide_fetches
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      have h1_2 : s2.readReg64 (Reg.gpr 1#5) = 0x12#64 := hx1_2
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hregs2.1.trans hx19
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hregs2.2.1.trans hx20
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64)) hF2 hsym2 ?_
      iterate 20 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine SepWPp.mono_pre_seedChain ?_ (hnext3 _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (hregs2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      exact sep_ac_seedChain (by ac_rfl)
    · intro s3 hpc3 hrun3 hsp3 hF3 hsym3 htr3 hlr3 hx0_3 hx1_3 hx2_3 hregs3
      have hrem1_lt : ([BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)).length < 2 ^ 62 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chain3_bytesMerge_atW img hC
        (a + 0x18#64) bufRef slot (ptr + 1#64) sp0
        ((SP2Ext img.base ext).fnAddr chainMerge3Name + 0x110#64)
        priv (rest ++ tail) hpriv_lt hpriv_ne hrem1_lt
        hpc3 hrun3 hsp3 halign hF3 hsym3 htr3 hlr3 hx0_3 hx1_3 hx2_3 rfl ?_
      intro s4 hpc4 hrun4 hsp4 hF4 hsym4 htr4 hcs4 hx0_4
      chain3_fetches_range img.base (Rust.withPanics ext) 0x110 0x110
      chain3_fetches_range img.base (Rust.withPanics ext) 0x1f4 0x1f4
      dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hpc4 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
      examples_hide_fetches
      have h0_4 : s4.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_4
      refine SepWPp.of_sepWP_frozen_seedChain (mid := s0.pc) hF4 hsym4 ?_
      iterate 2 wp_step
      refine SepWP.done (by simp only [hpc, arm64_norm]) (by simp only [hrun4, arm64_norm]) ?_
      intro hF5 hsym5
      have hregs4 : Chain3LoopRegsPreserved s0 s4 := hregs3.trans (.of_calleeSaved hcs4)
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun4, arm64_norm])
        (by simp only [hsp4, arm64_norm]) hF5 hsym5 (by simp only [htr4, arm64_norm])
        (hregs4.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [DeserializeGeneral.pbBytes_ptr_advance_seedChain 2 (by decide) ptr priv hpriv_lt,
        ← DeserializeGeneral.pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr priv hpriv_lt]
      exact sep_ac_seedChain (by ac_rfl)

/-! ## Ghost field helpers -/

private def tailFields (c : ChainG) : List ChainField :=
  (match c.ck with
   | some (i, key) => [ChainField.ck i key]
   | none => []) ++ c.keys.map ChainField.key

set_option maxHeartbeats 400000 in
private theorem fields_eq_tailFields (c : ChainG) :
    c.fields =
      (if c.srk = [] then [] else [ChainField.srk c.srk]) ++
        ((if c.priv = [] then [] else [ChainField.priv c.priv]) ++ tailFields c) := by
  unfold ChainG.fields tailFields
  cases c.ck <;> simp [List.append_assoc]

set_option maxHeartbeats 400000 in
private theorem getElem?_tailFields_ne_srk (c : ChainG) (j : Nat) (b : List (BitVec 8)) :
    (tailFields c)[j]? ≠ some (ChainField.srk b) := by
  unfold tailFields
  cases c.ck with
  | none =>
    simp only [List.nil_append, List.getElem?_map]
    cases c.keys[j]? <;> simp
  | some ik =>
    rcases ik with ⟨i, key⟩
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.singleton_append, List.getElem?_cons_succ, List.getElem?_map]
      cases c.keys[j']? <;> simp

set_option maxHeartbeats 400000 in
private theorem getElem?_tailFields_ne_priv (c : ChainG) (j : Nat) (b : List (BitVec 8)) :
    (tailFields c)[j]? ≠ some (ChainField.priv b) := by
  unfold tailFields
  cases c.ck with
  | none =>
    simp only [List.nil_append, List.getElem?_map]
    cases c.keys[j]? <;> simp
  | some ik =>
    rcases ik with ⟨i, key⟩
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.singleton_append, List.getElem?_cons_succ, List.getElem?_map]
      cases c.keys[j']? <;> simp

set_option maxHeartbeats 400000 in
private theorem mem_fields_srk_ne_nil {c : ChainG} {b : List (BitVec 8)}
    (hmem : ChainField.srk b ∈ c.fields) : b ≠ [] := by
  unfold ChainG.fields at hmem
  rcases c with ⟨srk, priv, ck, keys⟩
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
    simp [h1, h2] at hmem <;> subst hmem <;> exact h1

set_option maxHeartbeats 400000 in
private theorem mem_fields_priv_ne_nil {c : ChainG} {b : List (BitVec 8)}
    (hmem : ChainField.priv b ∈ c.fields) : b ≠ [] := by
  unfold ChainG.fields at hmem
  rcases c with ⟨srk, priv, ck, keys⟩
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
    simp [h1, h2] at hmem <;> subst hmem <;> exact h2

set_option maxHeartbeats 400000 in
private theorem chainGAfter_srk_eq_nil_of_getElem_srk {c : ChainG} {k : Nat}
    (hk : k < c.fields.length) {b : List (BitVec 8)}
    (hfl : c.fields[k]'hk = .srk b) : (chainGAfter c k).srk = [] := by
  have hfl? : c.fields[k]? = some (.srk b) := by
    rw [List.getElem?_eq_getElem hk, hfl]
  rw [fields_eq_tailFields c] at hfl?
  by_cases hs : c.srk = [] <;> by_cases hp : c.priv = []
  · simp only [hs, hp, ↓reduceIte, List.nil_append] at hfl?
    exact absurd hfl? (getElem?_tailFields_ne_srk c k b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => simp at hfl?
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_srk c k' b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_srk c k' b)
  · simp only [hs, hp, ↓reduceIte, List.singleton_append] at hfl?
    rcases k with _ | _ | k'
    · rfl
    · simp at hfl?
    · simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_srk c k' b)

set_option maxHeartbeats 400000 in
private theorem chainGAfter_priv_eq_nil_of_getElem_priv {c : ChainG} {k : Nat}
    (hk : k < c.fields.length) {b : List (BitVec 8)}
    (hfl : c.fields[k]'hk = .priv b) : (chainGAfter c k).priv = [] := by
  have hfl? : c.fields[k]? = some (.priv b) := by
    rw [List.getElem?_eq_getElem hk, hfl]
  rw [fields_eq_tailFields c] at hfl?
  by_cases hs : c.srk = [] <;> by_cases hp : c.priv = []
  · simp only [hs, hp, ↓reduceIte, List.nil_append] at hfl?
    exact absurd hfl? (getElem?_tailFields_ne_priv c k b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_priv c k' b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => simp at hfl?
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_priv c k' b)
  · simp only [hs, hp, ↓reduceIte, List.singleton_append] at hfl?
    rcases k with _ | _ | k'
    · simp at hfl?
    · unfold chainGAfter
      rw [fields_eq_tailFields c]
      simp [hs, hp, ChainG.empty, ChainG.apply]
    · simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_priv c k' b)

set_option maxHeartbeats 400000 in
theorem chain3GAt_apply_srk (A : RustAlloc) (a : BitVec 64) (c : ChainG) (b : List (BitVec 8)) :
    chain3GAt A a (c.apply (.srk b)) =
      chain3VecAt A a b ∗ chain3VecAt A (a + 0x18#64) c.priv ∗ chainGRest A a c := rfl

set_option maxHeartbeats 400000 in
theorem chain3GAt_apply_priv (A : RustAlloc) (a : BitVec 64) (c : ChainG) (b : List (BitVec 8)) :
    chain3GAt A a (c.apply (.priv b)) =
      chain3VecAt A a c.srk ∗ chain3VecAt A (a + 0x18#64) b ∗ chainGRest A a c := rfl

/-! ## Main theorems -/

set_option maxHeartbeats 400000 in
/-- Tags 1 (`sender_ratchet_key`) and 2 (`sender_ratchet_key_private`) advance `Chain3LoopAtW`
from `k` to `k + 1` for arbitrary `A : RustAlloc`. -/
theorem chain3Srk_ok_ext {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) :
    Chain3SrkStmtExt A img ext := by
  intro hC x R s0 k s hk htag hs hL
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hcOk, hlen, hmem⟩
  have hpc' : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64 := hpc
  have hsp_sub_align : (s0.sp - 0xf0#64) &&& 15#64 = 0#64 := by
    have h1 : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    rwa [hsp] at h1
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_240_c3 hsp_sub_align
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc
  have hlen_rem : ((x.c.fields[k]'hk).enc ++ rest ++ x.tail).length < 2 ^ 62 := by
    have h1 := hlen
    rw [payload_append_eq_preBytes x.c x.tail k, drop_flatMap_enc hk] at h1
    simp only [rest, List.length_append] at h1 ⊢
    omega
  generalize hfl_eq : x.c.fields[k]'hk = fl
  cases fl with
  | ck i key =>
    rw [hfl_eq] at htag
    simp [ChainField.tag] at htag
  | key mk =>
    rw [hfl_eq] at htag
    simp [ChainField.tag] at htag
  | srk b =>
    have hb_mem : ChainField.srk b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_srk_length_lt hcOk hb_mem
    have hb_ne : b ≠ [] := mem_fields_srk_ne_nil hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 1 b := by
      rw [hfl_eq]
      exact lenField_eq_pbBytes 1 (Or.inl rfl) b hb_lt
    have hlen_pb : (pbBytes 1 b ++ rest ++ x.tail).length < 2 ^ 62 := by
      rwa [← henc]
    let ck := chainGAfter x.c k
    have hck_srk : ck.srk = [] := chainGAfter_srk_eq_nil_of_getElem_srk hk hfl_eq
    let F : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗
      chain3VecAt A (x.a + 0x18#64) ck.priv ∗
      chainGRest A x.a ck ∗
      chain3SavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨
        (((x.bufRef ↦₆₄ x.slot) ∗
          chain3VecAt A x.a [] ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
          A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX) ∗ F) ∗ R := by
      rw [chain3GAt, hck_srk,
        sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢
      simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (SP2Ext img.base ext)
        (chain3PCAtW img ext 0xa8#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗
          chain3VecAt A x.a [] ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
          A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX) ∗ F)
        (fun sm Pm =>
          (sm.mem ⊨ Pm ∗ R) → Chain3LoopAtWExt A img ext x R s0 (k + 1) sm)
        (fun sf Pf =>
          (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R)) := by
      refine step_chain3Tag1_atW img hC x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        b rest x.tail hb_lt hb_ne hlen_pb hpc' hrun hsp hsp0_align hF hsym htr hx19 hx20 hx21 ?_
      intro sm hpcm hrunm hspm hFm hsymm htrm hregsm
      refine SepWPp.done hpcm hrunm ?_
      intro hmem_m
      have hal_m : sm.spAligned = true := by
        simp only [State.spAligned, hspm, ← hsp]
        exact hal
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.2.2.trans hvregs, hsymm, hFm, hspm, hal_m,
        hregsm.2.2.2.2.2.2.2.2.2.1.trans hx29,
        hregsm.1.trans hx19,
        hregsm.2.1.trans hx20,
        hregsm.2.2.1.trans hx21,
        hregsm.2.2.2.1.trans hx22,
        hregsm.2.2.2.2.1.trans hx23,
        hregsm.2.2.2.2.2.1.trans hx24,
        hregsm.2.2.2.2.2.2.1.trans hx26,
        hregsm.2.2.2.2.2.2.2.1.trans hx27,
        hregsm.2.2.2.2.2.2.2.2.1.trans hx28,
        hcOk, hlen, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗
            chain3VecAt A x.a b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 1 b) ∗
            sliceCursorAt x.slot
              (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 1 b).length)
              (rest ++ x.tail) ∗
            A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX) ∗ F) =
          (chain3GAt A x.a (chainGAfter x.c (k + 1)) ∗
            (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗
            chain3SavedRegs s0.sp s0) := by
        rw [chainGAfter_succ hk, hfl_eq, chain3GAt_apply_srk A x.a ck b,
          ← henc, ← curPtr_succ x.ptr hk,
          sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]
        ac_rfl
      rw [hpost_eq] at hmem_m
      simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, hex⟩ := hwp R hmem_pre hL
    rcases hex with ⟨_, _, Pf, hmf, hloop⟩ | ⟨hpan, Pf, hmf, hpan_mem⟩ | ⟨_, hoom⟩
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact ⟨sf, hsteps, Or.inr ⟨hpan, hpan_mem hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  | priv b =>
    have hb_mem : ChainField.priv b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_priv_length_lt hcOk hb_mem
    have hb_ne : b ≠ [] := mem_fields_priv_ne_nil hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 2 b := by
      rw [hfl_eq]
      exact lenField_eq_pbBytes 2 (Or.inr rfl) b hb_lt
    have hlen_pb : (pbBytes 2 b ++ rest ++ x.tail).length < 2 ^ 62 := by
      rwa [← henc]
    let ck := chainGAfter x.c k
    have hck_priv : ck.priv = [] := chainGAfter_priv_eq_nil_of_getElem_priv hk hfl_eq
    let F : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗
      chain3VecAt A x.a ck.srk ∗
      chainGRest A x.a ck ∗
      chain3SavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨
        (((x.bufRef ↦₆₄ x.slot) ∗
          chain3VecAt A (x.a + 0x18#64) [] ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
          A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX) ∗ F) ∗ R := by
      rw [chain3GAt, hck_priv,
        sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢
      simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (SP2Ext img.base ext)
        (chain3PCAtW img ext 0xa8#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗
          chain3VecAt A (x.a + 0x18#64) [] ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
          A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX) ∗ F)
        (fun sm Pm =>
          (sm.mem ⊨ Pm ∗ R) → Chain3LoopAtWExt A img ext x R s0 (k + 1) sm)
        (fun sf Pf =>
          (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R)) := by
      refine step_chain3Tag2_atW img hC x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        b rest x.tail hb_lt hb_ne hlen_pb hpc' hrun hsp hsp0_align hF hsym htr hx19 hx20 hx21 ?_
      intro sm hpcm hrunm hspm hFm hsymm htrm hregsm
      refine SepWPp.done hpcm hrunm ?_
      intro hmem_m
      have hal_m : sm.spAligned = true := by
        simp only [State.spAligned, hspm, ← hsp]
        exact hal
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.2.2.trans hvregs, hsymm, hFm, hspm, hal_m,
        hregsm.2.2.2.2.2.2.2.2.2.1.trans hx29,
        hregsm.1.trans hx19,
        hregsm.2.1.trans hx20,
        hregsm.2.2.1.trans hx21,
        hregsm.2.2.2.1.trans hx22,
        hregsm.2.2.2.2.1.trans hx23,
        hregsm.2.2.2.2.2.1.trans hx24,
        hregsm.2.2.2.2.2.2.1.trans hx26,
        hregsm.2.2.2.2.2.2.2.1.trans hx27,
        hregsm.2.2.2.2.2.2.2.2.1.trans hx28,
        hcOk, hlen, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗
            chain3VecAt A (x.a + 0x18#64) b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 2 b) ∗
            sliceCursorAt x.slot
              (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 2 b).length)
              (rest ++ x.tail) ∗
            A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX) ∗ F) =
          (chain3GAt A x.a (chainGAfter x.c (k + 1)) ∗
            (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗
            chain3SavedRegs s0.sp s0) := by
        rw [chainGAfter_succ hk, hfl_eq, chain3GAt_apply_priv A x.a ck b,
          ← henc, ← curPtr_succ x.ptr hk,
          sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]
        ac_rfl
      rw [hpost_eq] at hmem_m
      simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, hex⟩ := hwp R hmem_pre hL
    rcases hex with ⟨_, _, Pf, hmf, hloop⟩ | ⟨hpan, Pf, hmf, hpan_mem⟩ | ⟨_, hoom⟩
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact ⟨sf, hsteps, Or.inr ⟨hpan, hpan_mem hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim

theorem chain3Srk_ok (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3SrkStmt img ext := by
  rw [← Chain3SrkStmtExt_A0]
  exact chain3Srk_ok_ext img ext

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

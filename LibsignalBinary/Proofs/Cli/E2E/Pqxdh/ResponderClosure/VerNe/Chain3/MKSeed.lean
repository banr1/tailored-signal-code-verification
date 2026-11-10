/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
import LibsignalBinary.Proofs.Cli.ShardFill.ChainMerge5Decode
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# `message::merge<Chain> [local#5]`: MessageKeys Seed Field (`Chain3MkSeedStmt`)

Verifies step 4c (`+0x244 → +0x244`) of the tag-4 (`message_keys`) path: decodes inner key `0x2a`
(tag 5, wire type 2), merges `seed` into the empty `Vec<u8>` at `sp0 - 160` via `bytes::merge`, and
returns to the inner loop head `+0x244`.
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
  (sliceCursorAt sliceCursorAfter BytesMergeGhost BytesMergeCapOk DecodeVarintSlowGhost)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg Arm64.calleeSavedVRegs_writeVReg128_ite Arm64.isCalleeSavedVReg
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

/-! ## 1. Small helpers -/

set_option maxHeartbeats 400000 in
theorem c3seed_spAligned {s : State} {sp0 : BitVec 64} (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64) : s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  exact sp_sub_240_aligned_receiverChains halign

set_option maxHeartbeats 400000 in
theorem c3seed_pointsTo_2a_combine (ptr : BitVec 64) (seed : List (BitVec 8))
    (hseed : seed.length < 128) :
    (ptr ↦ₛ [0x2a#8]) ∗ ((ptr + 1#64) ↦ₛ ([BitVec.ofNat 8 seed.length] ++ seed)) =
      (ptr ↦ₛ pbBytes 5 seed) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  exact CryptoVerification.E2E.Record.DeserializeSeed.pbBytes_pointsTo_combine_seedChain
    5 (by decide) ptr seed hseed

/-! ## 2. Callee steps (`decode_varint [local#3]`, `bytes::merge [local#4]`) -/

set_option maxHeartbeats 400000 in
/-- `bl decode_varint [local#3]` on `enc ++ rest` with `decodeVarint (enc ++ rest) = some (v, rest)`. -/
theorem c3seed_dv_call {A : RustAlloc} (img : Obj.Image) {ext : String → Option (State → State)}
    (hC : Chain3CalleesWExt A img ext)
    (bufRef slot curPtr sp0 ret_pc v : BitVec 64) (enc rest : List (BitVec 8))
    (hdv : decodeVarint (enc ++ rest) = some (v, rest))
    (hlen_lt : (enc ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 → sm.readReg64 .x1 = v →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ enc) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 enc.length) rest ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot curPtr (enc ++ rest) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R)) := by
  have hcall := c3_decodeVarint_ok_sub hC
  have hlen_lt63 : (enc ++ rest).length < 2 ^ 63 := by omega
  refine SepWPp.call_frozen_seedChain
    (x := DecodeVarintSlowGhost.mk bufRef slot curPtr (enc ++ rest))
    (F := memRegion (sp0 - 0xf0#64 - BitVec.ofNat 64 chainMerge3SubStackX)
      (chainMerge3SubStackX - decodeVarint2StackX) ∗ F)
    hcall hpc hrun (c3seed_spAligned hsp halign) hF hsym hlr ?_ ?_ ?_ ?_
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
    dsimp only [Spec.inImage, decodeVarint2SpecX, chainMerge3SpecAtWExt,
      Serialization.allocPanic] at hm ⊢
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
    refine SepWPp.mono_pre_seedChain ?_
      (hnext sm hpcm hrunm hspm hFm hsymm (htrm.trans htr) hcsm hx0m hx1m)
    rw [sliceCursorAfter_append_eq_seedChain slot curPtr enc rest,
      stackAt_c3Sub_to_decodeVarint (sp0 - 0xf0#64)]
    exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
/-- `bl bytes::merge [local#4]` into an empty `Vec<u8>` (`cap = 0`, `ptr = 1`) at `v`, on a
`< 128`-byte field `[BitVec.ofNat 8 b.length] ++ b`. -/
theorem c3seed_bm_call {A : RustAlloc} (img : Obj.Image) {ext : String → Option (State → State)}
    (hC : Chain3CalleesWExt A img ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {F : SepProp} {Q : State → SepProp → Prop}
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
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 0xf0#64 →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        ((vecU8 A v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s
      ((vecU8At A v 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R)) := by
  have hcall := c3_bytesMerge_ok_sub hC
  have hlen_lt63 : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 63 := by omega
  refine SepWPp.call_frozen_seedChain
    (x := BytesMergeGhost.mk .lengthDelimited v 0#64 1#64 [] bufRef slot curPtr
      ([BitVec.ofNat 8 b.length] ++ b ++ rest))
    (F := F)
    hcall hpc hrun (c3seed_spAligned hsp halign) hF hsym hlr ?_ ?_ ?_ ?_
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
    dsimp only [bytesMerge3Spec, Spec.inImage, bytesMerge3RawSpec, chainMerge3SpecAtWExt,
      Serialization.allocPanic] at hm ⊢
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
    have hv : vecU8At A v cap' ptr' b ⊢ vecU8 A v b :=
      Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
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
        vecU8 A v b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F) =
        (vecU8 A v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F := by
      ac_rfl
    rw [hEq1, ← hEq2]
    exact sepConj_mono_left hv

/-! ## 3. Straight-line segments -/

set_option maxHeartbeats 400000 in
/-- Inner loop head (`+0x244 → +0x258`) when `remaining > x25 = |rest|`. -/
theorem step_c3seed_ihead (img : Obj.Image) {ext : String → Option (State → State)}
    (bufRef slot ptr : BitVec 64) (b0 : BitVec 8) (rem1 rest : List (BitVec 8))
    (hlen_gt : rest.length < (b0 :: rem1).length) (hlen_lt : (b0 :: rem1).length < 2 ^ 62)
    {ret : BitVec 64} {s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x244#64)
    (hrun : s.status = .Running)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) →
      s1.status = .Running → s1.sp = s.sp → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s.trace →
      s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x25c#64 →
      s1.readReg64 .x0 = bufRef → s1.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      Chain3MkRegs s s1 →
      SepWPp (SP2Ext img.base ext) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp := by
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_lt
  chain3_fetches_range img.base (Rust.withPanics ext) 0x244 0x258
  dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
  examples_hide_fetches
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 rest.length := hx25
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64)) hF hsym ?_
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 6 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm]) (by simp only [arm64_norm]) hF1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [h25, arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
/-- Inner key `0x2a` dispatch (`+0x25c → +0x2a4`): tag 5, wire type 2, `x1 = sp0 - 160`, `x2 = bufRef`. -/
theorem step_c3seed_key (img : Obj.Image) {ext : String → Option (State → State)}
    (bufRef sp0 : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x25c#64)
    (hrun : s.status = .Running)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = 0x2a#64)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx22 : s.readReg64 .x22 = sp0 - 0xe8#64)
    (hnext : ∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) →
      s1.status = .Running → s1.sp = s.sp → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s.trace →
      s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x2a8#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 → s1.readReg64 .x1 = sp0 - 160#64 →
      s1.readReg64 .x2 = bufRef →
      s1.readReg64 .x25 = s.readReg64 .x25 → Chain3MkRegs s s1 →
      SepWPp (SP2Ext img.base ext) ret s1 P Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s P Q Qp := by
  chain3_fetches_range img.base (Rust.withPanics ext) 0x25c 0x2a4
  dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
  examples_hide_fetches
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = 0x2a#64 := hx1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64)) hF hsym ?_
  iterate 19 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  exact hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm]) (by simp only [arm64_norm]) hF1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩

set_option maxHeartbeats 400000 in
/-- Post-call continuation (`+0x2a8 → +0x244`) back to the inner loop head when `x0 = 0`. -/
theorem step_c3seed_icont (img : Obj.Image) {ext : String → Option (State → State)}
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x2a8#64)
    (hrun : s.status = .Running)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x244#64 →
      s1.status = .Running → s1.sp = s.sp → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s.trace → s1.readReg64 .x25 = s.readReg64 .x25 → Chain3MkRegs s s1 →
      SepWPp (SP2Ext img.base ext) ret s1 P Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s P Q Qp := by
  chain3_fetches_range img.base (Rust.withPanics ext) 0x2a8 0x2a8
  chain3_fetches_range img.base (Rust.withPanics ext) 0x314 0x318
  dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
  examples_hide_fetches
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (580)) hF hsym ?_
  iterate 3 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  exact hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm]) (by simp only [arm64_norm]) hF1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩

/-! ## 4. Main theorem: `chain3MkSeed_ok` -/

set_option maxHeartbeats 400000 in
theorem chain3MkSeed_ok_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MkSeedStmtExt A img ext := by
  intro hC bufRef slot ptr sp0 seed rest x R s0 s F ret Q
    hseed_lt hlen_lt hpc hrun hsp halign hF hsym htr hx19 hx22 hx25 hnext
  have hpb : pbBytes 5 seed = 0x2a#8 :: BitVec.ofNat 8 seed.length :: seed :=
    CryptoVerification.E2E.Record.DeserializeSeed.pbBytes_lt128_eq_seedChain 5 (by decide) seed hseed_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 seed.length] ++ seed ++ rest
  have hcons_eq : pbBytes 5 seed ++ rest = 0x2a#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : rest.length < (0x2a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x2a#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; exact hlen_lt
  rw [hcons_eq]
  have hpc' : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x244#64 := hpc
  refine SepWPp.focus_pre
    (step_c3seed_ihead img bufRef slot ptr 0x2a#8 rem1 rest hlen_gt hlen_cons_lt
      hpc' hrun hF hsym hx19 hx25 ?_)
  intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hlr1 hx0_1 hx25_1 hregs1
  have hsp1' : s1.sp = sp0 - 0xf0#64 := hsp1.trans hsp
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hcons_app : (0x2a#8 :: rem1) = [0x2a#8] ++ rem1 := rfl
  rw [hcons_app]
  have hdv1 : decodeVarint ([0x2a#8] ++ rem1) = some (0x2a#64, rem1) := rfl
  refine SepWPp.focus_pre
    (c3seed_dv_call img hC bufRef slot ptr sp0
      ((SP2Ext img.base ext).fnAddr chainMerge3Name + 0x25c#64) 0x2a#64 [0x2a#8] rem1
      hdv1 hlen_cons_lt hpc1 hrun1 hsp1' halign hF1 hsym1 htr1' hlr1 hx0_1 ?_)
  intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2 hx1_2
  have hregs2 : Chain3MkRegs s s2 := hregs1.trans (Chain3MkRegs.of_calleeSaved hcs2)
  have hx19_2 : s2.readReg64 .x19 = bufRef := hregs2.1.trans hx19
  have hx22_2 : s2.readReg64 .x22 = sp0 - 0xe8#64 := hregs2.2.2.2.1.trans hx22
  have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
    hcs2.2.2.2.2.2.2.1.trans hx25_1
  refine step_c3seed_key img bufRef sp0 hpc2 hrun2 hF2 hsym2 hx0_2 hx1_2 hx19_2 hx22_2 ?_
  intro s3 hpc3 hrun3 hsp3 hF3 hsym3 htr3 hlr3 hx0_3 hx1_3 hx2_3 hx25_3 hregs3
  have hsp3' : s3.sp = sp0 - 0xf0#64 := hsp3.trans hsp2
  have htr3' : s3.trace = s0.trace := htr3.trans htr2
  have hregs3' : Chain3MkRegs s s3 := hregs2.trans hregs3
  have hx25_3' : s3.readReg64 .x25 = BitVec.ofNat 64 rest.length := hx25_3.trans hx25_2
  have hrem1_lt : ([BitVec.ofNat 8 seed.length] ++ seed ++ rest).length < 2 ^ 62 := by
    simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
  have hlen1 : BitVec.ofNat 64 ([0x2a#8] : List (BitVec 8)).length = 1#64 := rfl
  rw [hlen1]
  refine SepWPp.focus_pre
    (c3seed_bm_call img hC (sp0 - 160#64) bufRef slot (ptr + 1#64) sp0
      ((SP2Ext img.base ext).fnAddr chainMerge3Name + 0x2a8#64)
      seed rest hseed_lt hrem1_lt hpc3 hrun3 hsp3' halign hF3 hsym3 htr3'
      hlr3 hx0_3 hx1_3 hx2_3 ?_)
  intro s4 hpc4 hrun4 hsp4 hF4 hsym4 htr4 hcs4 hx0_4
  have hregs4 : Chain3MkRegs s s4 := hregs3'.trans (Chain3MkRegs.of_calleeSaved hcs4)
  have hx25_4 : s4.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
    hcs4.2.2.2.2.2.2.1.trans hx25_3'
  refine step_c3seed_icont img hpc4 hrun4 hF4 hsym4 hx0_4 ?_
  intro s5 hpc5 hrun5 hsp5 hF5 hsym5 htr5 hx25_5 hregs5
  have hsp5' : s5.sp = sp0 - 0xf0#64 := hsp5.trans hsp4
  have htr5' : s5.trace = s0.trace := htr5.trans htr4
  have hx25_5' : s5.readReg64 .x25 = BitVec.ofNat 64 rest.length := hx25_5.trans hx25_4
  have hregs5' : Chain3MkRegs s s5 := hregs4.trans hregs5
  refine SepWPp.mono_pre_seedChain ?_
    (hnext s5 hpc5 hrun5 hsp5' hF5 hsym5 htr5' hx25_5' hregs5')
  rw [CryptoVerification.E2E.Record.DeserializeSeed.pbBytes_ptr_advance_seedChain
      5 (by decide) ptr seed hseed_lt,
    ← c3seed_pointsTo_2a_combine ptr seed hseed_lt]
  exact sep_ac_seedChain (by ac_rfl)

theorem chain3MkSeed_ok (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MkSeedStmt img ext := by
  rw [← Chain3MkSeedStmtExt_A0]
  exact chain3MkSeed_ok_ext img ext

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

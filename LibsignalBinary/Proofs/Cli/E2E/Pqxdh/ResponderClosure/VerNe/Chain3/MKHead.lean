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
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# `message::merge<Chain> [local#5]`: MessageKeys Head (`Chain3MkHeadStmt`)

Verifies step 4a (`+0x0a8 → +0x244`) of the tag-4 (`message_keys`) path: outer key `0x22` decode,
default `MessageKey` initialization in the 104 scratch bytes at `sp0 - 0xe8`, body-length varint `L`
decode, and inner limit `x25 = |rest|`.
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
  (sliceCursorAt sliceCursorAfter DecodeVarintSlowGhost)
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

/-! ## 1. Small facts -/

set_option maxHeartbeats 400000 in
theorem c3hd_sp_sub_240_aligned {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0xf0#64) &&& 15#64 = 0#64 :=
  sp_sub_240_aligned_receiverChains h

set_option maxHeartbeats 400000 in
theorem c3hd_spAligned {s : State} {sp0 : BitVec 64} (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64) : s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  exact c3hd_sp_sub_240_aligned halign

set_option maxHeartbeats 400000 in
theorem c3hd_pointsTo_hdr_combine (ptr : BitVec 64) (b : BitVec 8) :
    (ptr ↦ₛ [0x22#8]) ∗ ((ptr + 1#64) ↦ₛ [b]) = (ptr ↦ₛ [0x22#8, b]) := by
  have h : ([0x22#8, b] : List (BitVec 8)) = [0x22#8] ++ [b] := rfl
  rw [h, pointsToBytes_append]; rfl

set_option maxHeartbeats 400000 in
theorem c3hd_ptr_add_one_add_one (ptr : BitVec 64) :
    ptr + 1#64 + 1#64 = ptr + 2#64 := by
  simp only [BitVec.add_assoc]; rfl

/-! ## 2. Callee step (`decode_varint [local#3]`) -/

set_option maxHeartbeats 400000 in
/-- `bl decode_varint [local#3]` on `enc ++ rest` with `decodeVarint (enc ++ rest) = some (v, rest)`. -/
theorem c3hd_dv_call {A : RustAlloc} (img : Obj.Image) {ext : String → Option (State → State)}
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
    hcall hpc hrun (c3hd_spAligned hsp halign) hF hsym hlr ?_ ?_ ?_ ?_
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
    dsimp only [Spec.inImage, decodeVarint2SpecX, chainMerge3SpecAtWExt, chainMerge5SpecAtWExt,
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

/-! ## 3. Frame pieces of the scratch `MessageKey` at `sp0 - 232` -/

set_option maxHeartbeats 400000 in
/-- The 104 scratch bytes `[sp0 - 232, sp0 - 128)` as 80 bytes, two words, a 32-bit word and 4 bytes. -/
theorem memRegion104_c3hd_split (sp0 : BitVec 64) :
    memRegion (sp0 - 232#64) 104 =
      memRegion (sp0 - 232#64) 80 ∗ (∃∗ c10 : BitVec 64, (sp0 - 152#64) ↦₆₄ c10) ∗
      (∃∗ c11 : BitVec 64, (sp0 - 144#64) ↦₆₄ c11) ∗ (∃∗ wc : BitVec 32, (sp0 - 136#64) ↦₃₂ wc) ∗
      memRegion (sp0 - 132#64) 4 := by
  have s80 := memRegion_split (sp0 - 232#64) 80 24 (by decide)
  have e80 : (sp0 - 232#64) + BitVec.ofNat 64 80 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (80 : Nat) + 24 = 104 by decide, e80] at s80
  have h24 := memRegion24_split_ck_seedChain (sp0 - 232#64)
  have eb0 : (sp0 - 232#64) + 0x50#64 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb1 : (sp0 - 232#64) + 0x58#64 = sp0 - 144#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb2 : (sp0 - 232#64) + 0x60#64 = sp0 - 136#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb3 : (sp0 - 232#64) + 0x64#64 = sp0 - 132#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [eb0, eb1, eb2, eb3] at h24; rw [s80, h24]

private theorem c3hd_emptyVec_entails_vecU8 (A : RustAlloc) (addr : BitVec 64) :
    (addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 1#64) ∗ ((addr + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A addr [] := by
  rw [emptyVec_eq_vecU8At_seedChain]
  change vecU8At A addr 0#64 1#64 [] ⊢ vecU8 A addr []
  unfold vecU8
  exact Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 (Entails.refl _))

set_option maxHeartbeats 400000 in
/-- The default `MessageKey` the stores `+0x134..+0x150` write: three empty `Vec<u8>`s (`cap 0`,
`ptr 1`, `len 0`) and the seed `Vec<u8>` at `sp0 - 160` kept as `vecU8At … 0 1 []` for
`bytes::merge`. -/
theorem c3hd_default_of_cells {A : RustAlloc} (sp0 : BitVec 64) :
    ((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
      ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
      ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 1#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
      ((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 1#64) ∗ ((sp0 - 144#64) ↦₆₄ 0#64) ⊢
    vecU8 A (sp0 - 232#64) [] ∗ vecU8 A (sp0 - 208#64) [] ∗ vecU8 A (sp0 - 184#64) [] ∗
      vecU8At A (sp0 - 160#64) 0#64 1#64 [] := by
  have v0 := c3hd_emptyVec_entails_vecU8 A (sp0 - 232#64)
  have v1 := c3hd_emptyVec_entails_vecU8 A (sp0 - 208#64)
  have v2 := c3hd_emptyVec_entails_vecU8 A (sp0 - 184#64)
  have v3 : ((sp0 - 160#64) ↦₆₄ 0#64) ∗ (((sp0 - 160#64) + 8#64) ↦₆₄ 1#64) ∗
      (((sp0 - 160#64) + 16#64) ↦₆₄ 0#64) = vecU8At A (sp0 - 160#64) 0#64 1#64 [] :=
    emptyVec_eq_vecU8At_seedChain (sp0 - 160#64)
  have e0a : (sp0 - 232#64) + 8#64 = sp0 - 224#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e0b : (sp0 - 232#64) + 16#64 = sp0 - 216#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1a : (sp0 - 208#64) + 8#64 = sp0 - 200#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1b : (sp0 - 208#64) + 16#64 = sp0 - 192#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2a : (sp0 - 184#64) + 8#64 = sp0 - 176#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2b : (sp0 - 184#64) + 16#64 = sp0 - 168#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3a : (sp0 - 160#64) + 8#64 = sp0 - 152#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3b : (sp0 - 160#64) + 16#64 = sp0 - 144#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e0a, e0b] at v0; rw [e1a, e1b] at v1; rw [e2a, e2b] at v2; rw [e3a, e3b] at v3
  have hgrp :
      ((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
        ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
        ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 1#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
        ((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 1#64) ∗ ((sp0 - 144#64) ↦₆₄ 0#64) =
      (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 1#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64)) ∗
       (((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 1#64) ∗ ((sp0 - 144#64) ↦₆₄ 0#64)))) := by
    ac_rfl
  rw [hgrp, v3]; exact sepConj_mono v0 (sepConj_mono v1 (sepConj_mono v2 (Entails.refl _)))

/-! ## 4. Straight-line segments -/

set_option maxHeartbeats 400000 in
/-- Outer loop head `+0x0a8 → bl decode_varint` (`+0x0bc`): `remaining > |tail|`. -/
theorem step_c3hd_head (img : Obj.Image) {ext : String → Option (State → State)}
    (bufRef slot ptr : BitVec 64) (b0 : BitVec 8) (rem1 tail : List (BitVec 8))
    (hlen_gt : tail.length < (b0 :: rem1).length) (hlen_lt : (b0 :: rem1).length < 2 ^ 62)
    {ret : BitVec 64} {s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64)
    (hrun : s.status = .Running)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) →
      s1.status = .Running → s1.sp = s.sp → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s.trace →
      s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xc0#64 →
      s1.readReg64 .x0 = bufRef → Chain3MkRegs s s1 →
      SepWPp (SP2Ext img.base ext) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp := by
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_lt
  chain3_fetches_range img.base (Rust.withPanics ext) 0xa8 0xbc
  dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
  examples_hide_fetches
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := hx21
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64)) hF hsym ?_
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 6 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) hF1 hsym1 (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
/-- Tag-4 key dispatch (`+0x0c0 → +0x154`): key `0x22` (tag 4, wire type 2) and default `MessageKey`
scratch stores at `x22 = sp0 - 232`. -/
theorem step_c3hd_key4 {A : RustAlloc} (img : Obj.Image) {ext : String → Option (State → State)}
    (bufRef sp0 : BitVec 64)
    {ret : BitVec 64} {s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xc0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = 0x22#64)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx22 : s.readReg64 .x22 = sp0 - 232#64)
    (hx23 : s.readReg64 .x23 = 1#64)
    (hnext : ∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) →
      s1.status = .Running → s1.sp = sp0 - 0xf0#64 → img.FrozenLoaded s1 →
      s1.symtab = img.symtab → s1.trace = s.trace →
      s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x158#64 →
      s1.readReg64 .x0 = bufRef → Chain3MkRegs s s1 →
      SepWPp (SP2Ext img.base ext) ret s1
        ((vecU8 A (sp0 - 232#64) [] ∗ vecU8 A (sp0 - 208#64) [] ∗ vecU8 A (sp0 - 184#64) [] ∗
          vecU8At A (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4) ∗ F) Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s (memRegion (sp0 - 232#64) 104 ∗ F) Q Qp := by
  have hal0 : (sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr halign
  have hal1 : ((sp0 - 0xf0#64) &&& 15#64 == 0#64) = true :=
    beq_iff_eq.mpr (c3hd_sp_sub_240_aligned halign)
  chain3_fetches_range img.base (Rust.withPanics ext) 0xc0 0xec
  chain3_fetches_range img.base (Rust.withPanics ext) 0x118 0x154
  dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
  examples_hide_fetches
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = 0x22#64 := hx1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 232#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64)) hF hsym ?_
  rw [memRegion104_c3hd_split sp0, memRegion80_chainInit_eq_cells10_receiverChains sp0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro c0
  apply SepWP.exists_elim; intro c1
  apply SepWP.exists_elim; intro c2
  apply SepWP.exists_elim; intro c3
  apply SepWP.exists_elim; intro c4
  apply SepWP.exists_elim; intro c5
  apply SepWP.exists_elim; intro c6
  apply SepWP.exists_elim; intro c7
  apply SepWP.exists_elim; intro c8
  apply SepWP.exists_elim; intro c9
  apply SepWP.exists_elim; intro c10
  apply SepWP.exists_elim; intro c11
  apply SepWP.exists_elim; intro wc
  iterate 28 wp_step
  apply SepWP.fold (@c3hd_default_of_cells A sp0) (by sep_focus)
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm]) (by simp only [hsp, arm64_norm]) hF1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
/-- Length post-step (`+0x158 → +0x244`): sets `x25 = remaining - L = |rest|` after decoding `L = |body|`. -/
theorem step_c3hd_len (img : Obj.Image) {ext : String → Option (State → State)}
    (bufRef slot ptr : BitVec 64) (body rest : List (BitVec 8))
    (hlen_lt : (body ++ rest).length < 2 ^ 62)
    {ret : BitVec 64} {s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x158#64)
    (hrun : s.status = .Running)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 body.length)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hnext : ∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x244#64 →
      s1.status = .Running → s1.sp = s.sp → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s.trace →
      s1.readReg64 .x25 = BitVec.ofNat 64 rest.length → Chain3MkRegs s s1 →
      SepWPp (SP2Ext img.base ext) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (body ++ rest)) ∗ F) Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (body ++ rest)) ∗ F) Q Qp := by
  have hlen_app : (body ++ rest).length = body.length + rest.length := List.length_append
  have hult := ult_ofNat_add_right_false_seedChain (m := body.length) (k := rest.length) (by omega)
  have hsub := CryptoVerification.E2E.Record.DeserializeSeed.bv_ofNat_add_sub_left_seedChain
    body.length rest.length
  chain3_fetches_range img.base (Rust.withPanics ext) 0x158 0x158
  chain3_fetches_range img.base (Rust.withPanics ext) 0x234 0x240
  dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
  examples_hide_fetches
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 body.length := hx1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (580)) hF hsym ?_
  unfold sliceCursorAt
  rw [hlen_app]
  simp only [sepConj_assoc]
  iterate 5 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm]) (by simp only [arm64_norm]) hF1 hsym1
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  unfold sliceCursorAt
  rw [hlen_app]
  exact sep_ac_seedChain (by ac_rfl)

/-! ## 5. Proof of `Chain3MkHeadStmt` -/

set_option maxHeartbeats 400000 in
/-- Step 4a (`Chain3MkHeadStmtExt`): tag-4 key, default scratch at `sp0 - 0xe8`, and length `L`. -/
theorem chain3MkHead_ok_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MkHeadStmtExt A img ext := by
  intro hC bufRef slot ptr sp0 body rest tail x R s0 s F ret Q hbody htail hlen_lt
    hpc hrun hsp halign hF hsym htr hx19 hx21 hx22 hx23 hnext
  let rem1 : List (BitVec 8) := BitVec.ofNat 8 body.length :: (body ++ rest)
  have hlen_gt : tail.length < (0x22#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x22#8 :: rem1).length < 2 ^ 62 := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_rem1_lt : ([BitVec.ofNat 8 body.length] ++ (body ++ rest)).length < 2 ^ 62 := by
    simp only [List.singleton_append, List.length_cons, List.length_append]; omega
  have hlen_body_rest_lt : (body ++ rest).length < 2 ^ 62 := by
    simp only [List.length_append]; omega
  have hdv_L : decodeVarint ([BitVec.ofNat 8 body.length] ++ (body ++ rest)) =
      some (BitVec.ofNat 64 body.length, body ++ rest) := by
    rw [← encodeVarint_lt128_seedChain body.length hbody]
    exact decodeVarint_encodeVarint (BitVec.ofNat 64 body.length) (body ++ rest)
  dsimp only [chain3PCAtW] at hpc hnext
  refine SepWPp.mono_pre_seedChain
    (show (((bufRef ↦₆₄ slot) ∗ memRegion (sp0 - 0xe8#64) 104 ∗
        sliceCursorAt slot ptr (0x22#8 :: rem1) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F) ⊢
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x22#8 :: rem1)) ∗
        (memRegion (sp0 - 0xe8#64) 104 ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F)) from
      sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_head img bufRef slot ptr 0x22#8 rem1 tail hlen_gt hlen_cons_lt
    hpc hrun hF hsym hx19 hx21 ?_
  intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hlr1 hx0_1 hregs1
  refine SepWPp.mono_pre_seedChain
    (show (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x22#8] ++ rem1)) ∗
        (memRegion (sp0 - 0xe8#64) 104 ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F)) ⊢
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x22#8] ++ rem1) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗
        (memRegion (sp0 - 0xe8#64) 104 ∗ F)) from
      sep_ac_seedChain (by ac_rfl)) ?_
  refine c3hd_dv_call img hC bufRef slot ptr sp0
    ((SP2Ext img.base ext).fnAddr chainMerge3Name + 0xc0#64)
    0x22#64 [0x22#8] rem1 rfl hlen_cons_lt
    hpc1 hrun1 (hsp1.trans hsp) halign hF1 hsym1 (htr1.trans htr) hlr1 hx0_1 ?_
  intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2 hx1_2
  have hregs2 : Chain3MkRegs s s2 := hregs1.trans (Chain3MkRegs.of_calleeSaved hcs2)
  have hx19_2 : s2.readReg64 .x19 = bufRef := hregs2.1.trans hx19
  have hx22_2 : s2.readReg64 .x22 = sp0 - 232#64 := hregs2.2.2.2.1.trans hx22
  have hx23_2 : s2.readReg64 .x23 = 1#64 := hregs2.2.2.2.2.1.trans hx23
  refine SepWPp.mono_pre_seedChain
    (show (((bufRef ↦₆₄ slot) ∗ (ptr ↦ₛ [0x22#8]) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗
        (memRegion (sp0 - 232#64) 104 ∗ F)) ⊢
      (memRegion (sp0 - 232#64) 104 ∗
        ((bufRef ↦₆₄ slot) ∗ (ptr ↦ₛ [0x22#8]) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F)) from
      sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_key4 (A := A) img bufRef sp0 hpc2 hrun2 hsp2 halign hF2 hsym2
    hx0_2 hx1_2 hx19_2 hx22_2 hx23_2 ?_
  intro s3 hpc3 hrun3 hsp3 hF3 hsym3 htr3 hlr3 hx0_3 hregs23
  have hregs3 : Chain3MkRegs s s3 := hregs2.trans hregs23
  refine SepWPp.mono_pre_seedChain
    (show ((vecU8 A (sp0 - 232#64) [] ∗ vecU8 A (sp0 - 208#64) [] ∗ vecU8 A (sp0 - 184#64) [] ∗
        vecU8At A (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
        memRegion (sp0 - 132#64) 4) ∗
        ((bufRef ↦₆₄ slot) ∗ (ptr ↦ₛ [0x22#8]) ∗
          sliceCursorAt slot (ptr + 1#64) ([BitVec.ofNat 8 body.length] ++ (body ++ rest)) ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F)) ⊢
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) ([BitVec.ofNat 8 body.length] ++ (body ++ rest)) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗
        (vecU8 A (sp0 - 232#64) [] ∗ vecU8 A (sp0 - 208#64) [] ∗ vecU8 A (sp0 - 184#64) [] ∗
          vecU8At A (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4 ∗ (ptr ↦ₛ [0x22#8]) ∗ F)) from
      sep_ac_seedChain (by ac_rfl)) ?_
  refine c3hd_dv_call img hC bufRef slot (ptr + 1#64) sp0
    ((SP2Ext img.base ext).fnAddr chainMerge3Name + 0x158#64)
    (BitVec.ofNat 64 body.length) [BitVec.ofNat 8 body.length] (body ++ rest)
    hdv_L hlen_rem1_lt
    hpc3 hrun3 hsp3 halign hF3 hsym3 (htr3.trans htr2) hlr3 hx0_3 ?_
  intro s4 hpc4 hrun4 hsp4 hF4 hsym4 htr4 hcs4 hx0_4 hx1_4
  have hregs4 : Chain3MkRegs s s4 := hregs3.trans (Chain3MkRegs.of_calleeSaved hcs4)
  have hx19_4 : s4.readReg64 .x19 = bufRef := hregs4.1.trans hx19
  refine SepWPp.mono_pre_seedChain
    (show (((bufRef ↦₆₄ slot) ∗ ((ptr + 1#64) ↦ₛ [BitVec.ofNat 8 body.length]) ∗
        sliceCursorAt slot (ptr + 1#64 + 1#64) (body ++ rest) ∗
        A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗
        (vecU8 A (sp0 - 232#64) [] ∗ vecU8 A (sp0 - 208#64) [] ∗ vecU8 A (sp0 - 184#64) [] ∗
          vecU8At A (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4 ∗ (ptr ↦ₛ [0x22#8]) ∗ F)) ⊢
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot (ptr + 2#64) (body ++ rest)) ∗
        (vecU8 A (sp0 - 232#64) [] ∗ vecU8 A (sp0 - 208#64) [] ∗ vecU8 A (sp0 - 184#64) [] ∗
          vecU8At A (sp0 - 160#64) 0#64 1#64 [] ∗ ((sp0 - 136#64) ↦₃₂ 0#32) ∗
          memRegion (sp0 - 132#64) 4 ∗ (ptr ↦ₛ [0x22#8]) ∗
          ((ptr + 1#64) ↦ₛ [BitVec.ofNat 8 body.length]) ∗
          A.pool ∗ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ F)) by
      rw [c3hd_ptr_add_one_add_one ptr]
      exact sep_ac_seedChain (by ac_rfl)) ?_
  refine step_c3hd_len img bufRef slot (ptr + 2#64) body rest hlen_body_rest_lt
    hpc4 hrun4 hF4 hsym4 hx0_4 hx1_4 hx19_4 ?_
  intro s5 hpc5 hrun5 hsp5 hF5 hsym5 htr5 hx25_5 hregs45
  have hregs5 : Chain3MkRegs s s5 := hregs4.trans hregs45
  refine SepWPp.mono_pre_seedChain ?_
    (hnext s5 hpc5 hrun5 (hsp5.trans hsp4) hF5 hsym5 (htr5.trans htr4) hx25_5 hregs5)
  rw [← c3hd_pointsTo_hdr_combine ptr (BitVec.ofNat 8 body.length)]
  exact sep_ac_seedChain (by ac_rfl)

theorem chain3MkHead_ok (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MkHeadStmt img ext := by
  rw [← Chain3MkHeadStmtExt_A0]
  exact chain3MkHead_ok_ext img ext

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF14AuxW
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `SessionStructure::merge_field` on Tag 14 (`pending_kyber_pre_key`)

Verifies `mergeField14KyberWA_ok`, `mergeField14KyberW_ok` (over `kyberAt14`), `mergeField14WA_ok`,
and `mergeField14W_ok` (over `prostSSGXNoPqAt_x14`) on `SP2Ext` at `mergeFieldStackX = 32768` with
slice length `< 2 ^ 62`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.E2E.Record
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.Serialization (OkAt allocPanic)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq
attribute [local wp_norm] kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq

private abbrev decodeVarintRelOff_mf14W : BitVec 64 :=
  bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint_slice") -
    (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64)

private abbrev int32MergeRelOff_mf14W : BitVec 64 :=
  bv% ((2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") -
    (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64)

private abbrev bytesMergeRelOff_mf14W : BitVec 64 :=
  bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
    (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64)

open Lean Elab Tactic in
local elab "mf14W_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn := mkIdent `Symbolic.Swarm.TRREF.B3DeserQ.mergeField_fnOff_mf14W
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (.str `Symbolic.Swarm.TRREF.B3DeserQ
      s!"mf14W_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))
    k := k + 4

open Lean Elab Tactic in
local elab "mf14W_fetch_named " nm:ident b:term:max H:term:max kLit:num : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let k := kLit.getNat
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn := mkIdent `Symbolic.Swarm.TRREF.B3DeserQ.mergeField_fnOff_mf14W
  let dec := mkIdent (.str `Symbolic.Swarm.TRREF.B3DeserQ
    s!"mf14W_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
  evalTactic (← `(tactic|
    have $nm := $fetchAdd (b := $b) (H := $H) (k := $kLit) $hfn (by decide) $dec))

def mergeField14KyberSpecAtWA (A : RustAlloc) (img : Obj.Image) (P : GenFieldX → Prop) :
    Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      kyberAt14 A x.ss x.v.ext.kyber ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
      A.pool ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      kyberAt14 A x.ss (x.v.apply x.fld).ext.kyber ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      A.pool ∗ stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

def MergeField14KyberOkAtWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (P : GenFieldX → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeField14KyberSpecAtWA A img P)

def mergeField14SpecAtWA (A : RustAlloc) (img : Obj.Image) (P : GenFieldX → Prop) :
    Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostSSGXNoPqAt_x14 A x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
      A.pool ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostSSGXNoPqAt_x14 A x.ss (x.v.apply x.fld) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      A.pool ∗ stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

def MergeField14OkAtWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (P : GenFieldX → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeField14SpecAtWA A img P)

theorem mergeField14OkAtWA_of_kyber {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {P : GenFieldX → Prop}
    (hP14 : ∀ fl, P fl → fl.tag = 14) (hP : MergeField14KyberOkAtWA img A ext P) :
    MergeField14OkAtWA img A ext P := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  simp only [mergeField14SpecAtWA, prostSSGXNoPqAt_x14_eq_kyber_sep_rest,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨h0, hm⟩ := hpre
  obtain ⟨i, ct, hfl⟩ := (genFieldX_tag_eq_14_iff x.fld).mp (hP14 x.fld h0.2.2.2.2.2.1)
  have hpre' : s0.mem ⊨ (mergeField14KyberSpecAtWA A img P).pre x s0 ∗
      (restX14NoPq A x.ss x.v ∗ R) := by
    simp only [mergeField14KyberSpecAtWA, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨h0, by convert hm using 1; ac_rfl⟩
  refine hP.mono_outcome x (restX14NoPq A x.ss x.v ∗ R) s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · left; refine ⟨hret, hcc, ?_⟩
    simp only [mergeField14SpecAtWA, prostSSGXNoPqAt_x14_eq_kyber_sep_rest,
      hfl, restX14NoPq_apply_kyber]
    simp only [mergeField14KyberSpecAtWA, hfl] at hpost
    convert hpost using 1; ac_rfl
  · right; left; refine ⟨hpan, ?_⟩
    dsimp only [mergeField14SpecAtWA, mergeField14KyberSpecAtWA] at hpost ⊢
    rw [← sepConj_assoc] at hpost; exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited hpost).elim

private theorem decodeVarintSlice_ok_sub_mf14WA {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : Prost.X.DecodeVarintSliceOkW img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint_slice") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64))
      ((Prost.X.decodeVarintSliceSpecW A).inImage img) := by
  have heq : (SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint_slice") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64) =
      (SP2Ext img.base ext).fnAddr Prost.decodeVarintSliceName := by
    dsimp only [SP2Ext]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"),
      (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")]
    bv_omega
  rw [heq]; exact h

private theorem decode_kyber_result_mf14A (A : RustAlloc) {ct : List (BitVec 8)}
    (_hct : ct.length = 1569) (tail : List (BitVec 8)) (ret : BitVec 64) :
    Prost.varintSliceResultAt A ret (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)
      (decodeVarint (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((ret + 16#64) ↦₆₄ 2#64) := by
  rw [decodeVarint_kyber]; dsimp only [Prost.varintSliceResultAt]
  have : (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail).length -
      (18#8 :: innerBytes ct tail).length = 2 := by simp only [List.length_cons]; omega
  rw [this]

private theorem decode_kyber_ne_result_mf14A (A : RustAlloc) (i : BitVec 32) {ct : List (BitVec 8)}
    (_hct : ct.length = 1569) (tail : List (BitVec 8)) (ret : BitVec 64) :
    Prost.varintSliceResultAt A ret (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)
      (decodeVarint (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)) =
      (ret ↦₆₄ 0#64) ∗
        ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((ret + 16#64) ↦₆₄ 2#64) := by
  rw [decodeVarint_kyber_ne]; dsimp only [Prost.varintSliceResultAt]
  have : (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail).length -
      (8#8 :: kyberIdBytes i ct tail).length = 2 := by simp only [List.length_cons]; omega
  rw [this]

private theorem post_of_decode_mf14WA (A : RustAlloc) {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8)) (ptr sp0 : BitVec 64) (sm sf : State)
    (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.decodeVarintSliceSpecW A).post
        ⟨sp0 - 232#64, ptr, 164#8 :: 12#8 :: 18#8 :: innerBytes ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
        ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
        ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
        A.pool ∗ stackAt (sp0 - 240#64) Prost.X.decodeVarintSliceStackW ∗ Fr := by
  dsimp only [Prost.X.decodeVarintSliceSpecW]
  rw [decode_kyber_result_mf14A A hct, hsp, bytes_kyber_split_mf14, pointsTo64_zero_split32_mf14,
    show sp0 - 232#64 + 8#64 = sp0 - 224#64 by bv_omega,
    show sp0 - 232#64 + 16#64 = sp0 - 216#64 by bv_omega]
  simp only [sepConj_assoc]

private theorem post_of_bytesMerge_mf14WA (A : RustAlloc) (ss bufRef slot ptr sp0 : BitVec 64)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.bytesMergeRawSpecW A).post
        ⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, ptr + 3#64,
          innerBytes ct tail⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7648 ∗ Fr) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        vecU8At A (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
        A.pool ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ Fr) := by
  dsimp only [Prost.X.bytesMergeRawSpecW]
  rw [mergeBytes_inner hct tail]; dsimp only
  rw [hsp, sliceCursorAfter_inner_unfold_mf14 slot ptr hct tail,
      stackAt_sub_to_bytesMerge_mf14W (sp0 - 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

private theorem final_post_entails_kyber_mf14WA (A : RustAlloc) (ss cap' ptr' : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8)) (sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
      A.pool ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗
      ((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128) ⊢
    kyberAt14 A ss (v.apply (GenFieldX.kyber 0#32 ct)).ext.kyber ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber 0#32 ct).payload ++ tail) tail ∗
      A.pool ∗ stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_kyber_fold_mf14 slot ptr hct tail]
  refine Entails.trans (Q :=
    (vecU8At A (ss + 296#64) cap' ptr' ct ∗ ((ss + 320#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 324#64) 4) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail)) ∗
    A.pool ∗
    ((((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64)) ∗
      (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepConj_mono (kyberAt14_some_fold A ss cap' ptr' v 0#32 ct) ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (sepConj_mono (cells24_entails_memRegion24_mf14 sp0 _ _)
    (Entails.refl _)) ?_
  refine Entails.trans ?_ (stackAt_mergeField_fold_mf14W sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19)
  rw [← memRegion160_fold_mf14]
  exact Entails.of_eq (by ac_rfl)

private theorem post_of_decode_ne_mf14WA (A : RustAlloc) (i : BitVec 32) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) (ptr sp0 : BitVec 64) (sm sf : State)
    (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.decodeVarintSliceSpecW A).post
        ⟨sp0 - 232#64, ptr, kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
        ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((sp0 - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) ∗
        A.pool ∗ stackAt (sp0 - 240#64) Prost.X.decodeVarintSliceStackW ∗ Fr := by
  dsimp only [Prost.X.decodeVarintSliceSpecW]
  rw [decode_kyber_ne_result_mf14A A i hct, hsp, bytes_kyber_ne_split_mf14,
      pointsTo64_zero_split32_mf14,
    show sp0 - 232#64 + 8#64 = sp0 - 224#64 by bv_omega,
    show sp0 - 232#64 + 16#64 = sp0 - 216#64 by bv_omega]
  simp only [sepConj_assoc]

private theorem pre_to_int32Merge_ne_mf14WA (A : RustAlloc) (ss bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (Fr : SepProp) :
    ((ss + 320#64) ↦₃₂ 0#32) ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + 3#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + (encodeVarint (i.setWidth 64)).length +
        tail.length)) ∗
      ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) ∗ A.pool ∗
      memRegion (sp0 - 240#64 - 32528#64) 7872 ∗
      stackAt (sp0 - 240#64) Prost.X.decodeVarintSliceStackW ∗ Fr ⊢
    (memRegion (ss + 320#64) 4 ∗ (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot (ptr + 3#64) (kyberIdBytes i ct tail) ∗ A.pool ∗
      stackAt (sp0 - 240#64) Prost.X.int32MergeStackW) ∗
    (memRegion (sp0 - 240#64 - 32528#64) 7792 ∗ Fr) := by
  rw [← sliceCursorAt_kyberId_fold_mf14 slot ptr i hct tail]
  have hpt32 : ((ss + 320#64) ↦₃₂ 0#32) ⊢ memRegion (ss + 320#64) 4 := by
    rw [ProofLib.memRegion_four]; exact Entails.sepExists_right 0#32 (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hpt32) ?_
  apply Entails.of_eq
  rw [← sepConj_assoc (memRegion (sp0 - 240#64 - 32528#64) 7872),
      decode_to_int32Merge_stack_mf14W (sp0 - 240#64)]
  ac_rfl

private theorem post_of_int32Merge_ne_mf14WA (A : RustAlloc) (ss bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.int32MergeSpecW A).post
        ⟨.varint, ss + 320#64, bufRef, slot, ptr + 3#64, kyberIdBytes i ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        ((ss + 320#64) ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ kyberPtr2 ptr i) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + tail.length)) ∗
        ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
        (kyberPtr2 ptr i ↦₈ 18#8) ∗
        ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
        A.pool ∗ stackAt (sp0 - 240#64) Prost.X.int32MergeStackW ∗ Fr := by
  dsimp only [Prost.X.int32MergeSpecW]
  rw [mergeUint32_kyberIdBytes i tail]; dsimp only
  rw [hsp, sliceCursorAfter_kyberId_unfold_mf14 slot ptr i hct tail]
  simp only [sepConj_assoc]; ac_rfl

private theorem post_of_bytesMerge_ne_mf14WA (A : RustAlloc) (ss bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.bytesMergeRawSpecW A).post
        ⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, kyberPtr2 ptr i + 1#64,
          innerBytes ct tail⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7648 ∗ Fr) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        vecU8At A (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
        A.pool ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ Fr) := by
  dsimp only [Prost.X.bytesMergeRawSpecW]
  rw [mergeBytes_inner hct tail]; dsimp only
  rw [hsp, sliceCursorAfter_inner_ne_unfold_mf14 slot ptr i hct tail,
      stackAt_sub_to_bytesMerge_mf14W (sp0 - 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

private theorem final_post_entails_ne_kyber_mf14WA (A : RustAlloc) (ss cap' ptr' : BitVec 64)
    (v : SSGX) (bufRef slot ptr : BitVec 64) {i : BitVec 32} (hi : i ≠ 0#32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
      A.pool ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((sp0 - 216#64) ↦₆₄ 2#64) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((ss + 320#64) ↦₃₂ i) ∗ memRegion (ss + 324#64) 4 ∗
      ((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128) ⊢
    kyberAt14 A ss (v.apply (GenFieldX.kyber i ct)).ext.kyber ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber i ct).payload ++ tail) tail ∗
      A.pool ∗ stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_kyber_ne_fold_mf14 slot ptr hi hct tail]
  refine Entails.trans (Q :=
    (vecU8At A (ss + 296#64) cap' ptr' ct ∗ ((ss + 320#64) ↦₃₂ i) ∗
      memRegion (ss + 324#64) 4) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail)) ∗
    A.pool ∗
    ((((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((sp0 - 216#64) ↦₆₄ 2#64)) ∗
      (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepConj_mono (kyberAt14_some_fold A ss cap' ptr' v i ct) ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (sepConj_mono (cells24_entails_memRegion24_mf14 sp0 _ _)
    (Entails.refl _)) ?_
  refine Entails.trans ?_ (stackAt_mergeField_fold_mf14W sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19)
  rw [← memRegion160_fold_mf14]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Minimal-footprint `merge_field` leaf for tag 14 (`pending_kyber_pre_key`) over `kyberAt14`
for arbitrary `A : RustAlloc`. -/
theorem mergeField14KyberWA_ok (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtWA img A ext) :
    MergeField14KyberOkAtWA img A ext (fun fl => fl.tag = 14) := by
  dsimp only [MergeField14KyberOkAtWA, OkAtX]
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  refine ⟨(mergeField14KyberSpecAtWA A img (fun fl => fl.tag = 14)).pre
    ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ s0, R, hpre, ?_⟩
  clear hpre
  dsimp only [mergeField14KyberSpecAtWA]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, htag, hOk, hFresh, hlen, hF0, hsym0⟩ => ?_
  obtain ⟨i, ct, rfl⟩ := (genFieldX_tag_eq_14_iff fld).mp htag
  have hct : ct.length = 1569 := hOk
  have hk : v.ext.kyber = none := hFresh
  dsimp only [GenFieldX.tag, GenFieldX.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 14#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  rw [State.spAligned] at hsp_align
  have hb : img.base &&& 4095#64 = 0#64 :=
    base_aligned_of_loads hLoads
  have hcallD := decodeVarintSlice_ok_sub_mf14WA hC.1
  have hcallI := int32Merge_ok_sub_mf14WA hC.2.1
  have hcallB := bytesMerge_ok_sub_mf14WA hC.2.2.1
  let H := Rust.withPanics ext
  mf14W_fetches_range img.base H 0 60
  mf14W_fetches_range img.base H 368 440
  mf14W_fetches_range img.base H 1208 1252
  mf14W_fetches_range img.base H 1320 1436
  mf14W_fetches_range img.base H 1440 1676
  mf14W_fetches_range img.base H 1680 1724
  mf14W_fetches_range img.base H 1880 1904
  mf14W_fetches_range img.base H 2328 2356
  dsimp only [SP2Ext] at hpc hcallD hcallI hcallB ⊢
  have hx2_tr : (s0.readReg64 (Reg.gpr 2#5)).truncate 32 &&& 255#32 = 2#32 :=
    wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 : BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr
      2#5))) &&& 255#64) = 2#32 :=
    wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  have hadrp :
      (((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr mergeFieldName + 40#64) &&&
        bv% (2 ^ 64 - 4096)) +
        bv% (ls_bytes% "0082775f19328d6db5d6cb6d" -
          page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40)) =
        img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d") := by
    rw [Program.fnAddr_rebase, mergeField_fnOff_mf14W]
    exact adrp_rodata_mf14W img.base hb
  mf14W_fetch_named hfetch_ldr8 img.base (Rust.withPanics ext) 52
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr mergeFieldName = entry
  examples_hide_fetches
  by_cases hi : i = 0#32
  · subst hi
    rw [kyber_payload_tail_length hct] at hlen
    have hL_ne0 : (BitVec.ofNat 64 (1574 + tail.length) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hL_ule10 : BitVec.ule (BitVec.ofNat 64 (1574 + tail.length)) 10#64 = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hL_ult10 : BitVec.ult 10#64 (BitVec.ofNat 64 (1574 + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    conv =>
      arg 4
      rw [kyberAt14_none_unfold A ss v hk,
          sliceCursorAt_kyber_unfold_mf14 slot ptr hct tail,
          bytes_kyber_split_mf14,
          stackAt_mergeField_unfold_mf14W s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w130 => SepWPp.exists_elim fun w138 =>
      SepWPp.exists_elim fun w140 => SepWPp.exists_elim fun v80 =>
      SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
      SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
      SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
      SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
      SepWPp.exists_elim fun v8 => ?_
    let mfStart := entry
    apply of_sepWP_frozen_mf14 hF0 hsym0 (mid := mfStart + 52#64)
    iterate 13 wp_step
    apply SepWP.done (by simp only [mfStart, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    intro hF1 hsym1
    obtain ⟨hread14, hcan14⟩ := rodata_jump_tag14_mf14W hLoads hF1
    apply of_sepWP_frozen_mf14 hF1 hsym1 (mid := entry + decodeVarintRelOff_mf14W)
    refine step_ldr8_ro_mf14 (pc := mfStart + 52#64) (pc' := mfStart + 56#64)
      (r := Reg.gpr 11#5) (v64 := 76#64)
      rfl (by simp only [wp_norm, arm64_norm, hrun]) hfetch_ldr8 rfl
      (ea := img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 13)) (wb := none)
      (by simp only [evalAddrMode, wp_norm, arm64_norm])
      hread14 hcan14 (by simp only [applyWriteback, wp_norm, arm64_norm]) ?_
    iterate 25 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    intro hF2 hsym2
    refine call_alloc_inImage_mf14W (s0 := s0) (R := R)
      (x := (⟨s0.sp - 232#64, ptr, 164#8 :: 12#8 :: 18#8 :: innerBytes ct tail⟩ :
        Prost.DecodeVarintSliceGhost))
      (T := memRegion (s0.sp - 232#64) 24 ∗
        (ptr ↦ₛ (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)) ∗ A.pool ∗
        stackAt (s0.sp - 240#64) Prost.X.decodeVarintSliceStackW)
      (F := memRegion (s0.sp - 240#64 - 32528#64) 7872 ∗
        ((ss + 296#64) ↦₆₄ 0#64) ∗ ((ss + 304#64) ↦₆₄ 1#64) ∗ ((ss + 312#64) ↦₆₄ 0#64) ∗
        ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗
        (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1574 + tail.length)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallD hF2 hsym2
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
      rfl
      (by simp only [Prost.X.decodeVarintSliceSpecW, wp_norm, arm64_norm]; rfl)
      ?_
      (by rw [bytes_kyber_split_mf14]; ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm])
      ?_
    · refine ⟨?_, ?_, Or.inl ?_⟩ <;>
        simp only [List.length_cons, innerBytes_length hct, BitVec.toNat_ofNat] <;> omega
    intro sf hpcf hrunf hspf hcsf hF3 hsym3
    simp only [wp_norm, arm64_norm] at hpcf
    have hsp_sf : sf.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm] using hspf
    have hx19_sf : sf.readReg64 (Reg.gpr 19#5) = slot := by
      simpa only [wp_norm, arm64_norm] using hcsf.1
    have hx20_sf : sf.readReg64 (Reg.gpr 20#5) = 99#64 := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.1
    have hx21_sf : sf.readReg64 (Reg.gpr 21#5) = ss := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
    have hx22_sf : sf.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
    rw [post_of_decode_mf14WA A hct tail ptr s0.sp _ sf (by simp only [wp_norm, arm64_norm])]
    refine SepWPp.pure_elim fun htr_sf => ?_
    have hc_ult2 : BitVec.ult (BitVec.ofNat 64 (1574 + tail.length)) 2#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub2 : BitVec.ofNat 64 (1574 + tail.length) - 2#64 =
        BitVec.ofNat 64 (1572 + tail.length) := len_sub_mf14W (by omega) (by omega)
    have hc_ult1572 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length)) 1572#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub1572 : BitVec.ofNat 64 (1572 + tail.length) - 1572#64 =
        BitVec.ofNat 64 tail.length := by
      have := len_sub_mf14W (a := 1572) (b := 1572) (n := tail.length) (by omega) (by omega)
      simpa using this
    have hc_ule1572 : BitVec.ule 1572#64 (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ule_n2 : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n2 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_ule_n : BitVec.ule (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_eq_n : (BitVec.ofNat 64 (1572 + tail.length) == BitVec.ofNat 64 tail.length) =
      false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hc_sub1 : BitVec.ofNat 64 (1572 + tail.length) - 1#64 =
        BitVec.ofNat 64 (1571 + tail.length) := len_sub_mf14W (by omega) (by omega)
    apply of_sepWP_frozen_mf14 hF3 hsym3 (mid := entry + bytesMergeRelOff_mf14W)
    have htr_sf' : sf.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm] using htr_sf
    have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
    have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
    have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
    iterate 47 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf])
    intro hF4 hsym4
    refine call_alloc_inImage_mf14W (s0 := s0) (R := R)
      (x := (⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, ptr + 3#64,
        innerBytes ct tail⟩ : Prost.BytesMergeGhost))
      (T := vecU8At A (ss + 296#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot (ptr + 3#64) (innerBytes ct tail) ∗ A.pool ∗
        stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW)
      (F := memRegion (s0.sp - 240#64 - 32528#64) 7648 ∗
        ((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((s0.sp - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
        ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallB hF4 hsym4
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunf])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm, hsp_sf] using hsp_align)
      rfl
      (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm, hsp_sf]; rfl)
      (by simp only [innerBytes_length hct]; omega)
      (by
        rw [← emptyVec_kyber_eq_vecU8At, ← sliceCursorAt_inner_fold_mf14 slot ptr hct tail,
          ← sepConj_assoc (stackAt _ _), sepConj_comm (stackAt _ _),
          decode_to_bytesMerge_stack_mf14W]
        ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm, htr_sf'])
      ?_
    intro sf2 hpcf2 hrunf2 hspf2 hcsf2 _ _
    simp only [wp_norm, arm64_norm] at hpcf2
    have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm, hsp_sf] using hspf2
    rw [post_of_bytesMerge_mf14WA A ss bufRef slot ptr s0.sp hct tail _ sf2
      (by simp only [wp_norm, arm64_norm, hsp_sf])]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
      SepWPp.pure_elim fun htr_sf2 => SepWPp.pure_elim fun hx0_sf2 => ?_
    have htr_sf2' : sf2.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm, htr_sf'] using htr_sf2
    have hx0_sf2' : sf2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf2
    have hx26_sf2 : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm, hx26_sf] using hcsf2.2.2.2.2.2.2.2.1
    have hx27_sf2 : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm, hx27_sf] using hcsf2.2.2.2.2.2.2.2.2.1
    have hx28_sf2 : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm, hx28_sf] using hcsf2.2.2.2.2.2.2.2.2.2.1
    have hvregs_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
      have h1 : calleeSavedVRegs sf2 = calleeSavedVRegs sf := by
        simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
      exact h1.trans hvregs_sf
    have hx21_sf2 : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
      simpa only [wp_norm, arm64_norm] using hcsf2.2.2.1
    have hx22_sf2 : sf2.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsf2.2.2.2.1
    have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = false := by
      simp [BitVec.ult]
    have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = true := by
      simp [BitVec.ule]
    apply SepWPp.of_sepWP_ret
    iterate 19 wp_step
    apply SepWP.fold (final_post_entails_kyber_mf14WA A ss cap' ptr' v bufRef slot ptr hct tail s0.sp
      (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) v80
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
      (sepConj_emp _).symm
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf2])
    refine ⟨fun hmf => sat_pure_true_mf14W ⟨?_, ?_⟩ hmf,
      by simp only [wp_norm, arm64_norm],
      by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm, hx26_sf2,
        hx27_sf2, hx28_sf2]; exact hvregs_sf2⟩
    · simp only [wp_norm, arm64_norm, htr_sf2']
    · simp only [wp_norm, arm64_norm]
  · -- Case `hi : i ≠ 0#32`
    have hm_bounds := encodeVarint_length_bounds_mf14 (i.setWidth 64)
    rw [kyber_ne_payload_tail_length hi hct] at hlen
    have hL_ne0 : (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hL_ule10 : BitVec.ule (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length)) 10#64 = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hL_ult10 : BitVec.ult 10#64 (BitVec.ofNat 64 (1575 +
      (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    conv =>
      arg 4
      rw [kyberAt14_none_unfold A ss v hk,
          sliceCursorAt_kyber_ne_unfold_mf14 slot ptr hi hct tail,
          bytes_kyber_ne_split_mf14,
          stackAt_mergeField_unfold_mf14W s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w130 => SepWPp.exists_elim fun w138 =>
      SepWPp.exists_elim fun w140 => SepWPp.exists_elim fun v80 =>
      SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
      SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
      SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
      SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
      SepWPp.exists_elim fun v8 => ?_
    let mfStart := entry
    apply of_sepWP_frozen_mf14 hF0 hsym0 (mid := mfStart + 52#64)
    iterate 13 wp_step
    apply SepWP.done (by simp only [mfStart, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    intro hF1 hsym1
    obtain ⟨hread14, hcan14⟩ := rodata_jump_tag14_mf14W hLoads hF1
    apply of_sepWP_frozen_mf14 hF1 hsym1 (mid := entry + decodeVarintRelOff_mf14W)
    refine step_ldr8_ro_mf14 (pc := mfStart + 52#64) (pc' := mfStart + 56#64)
      (r := Reg.gpr 11#5) (v64 := 76#64)
      rfl (by simp only [wp_norm, arm64_norm, hrun]) hfetch_ldr8 rfl
      (ea := img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 13)) (wb := none)
      (by simp only [evalAddrMode, wp_norm, arm64_norm])
      hread14 hcan14 (by simp only [applyWriteback, wp_norm, arm64_norm]) ?_
    iterate 25 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    intro hF2 hsym2
    refine call_alloc_inImage_mf14W (s0 := s0) (R := R)
      (x := (⟨s0.sp - 232#64, ptr, kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail⟩ :
        Prost.DecodeVarintSliceGhost))
      (T := memRegion (s0.sp - 232#64) 24 ∗
        (ptr ↦ₛ (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)) ∗ A.pool ∗
        stackAt (s0.sp - 240#64) Prost.X.decodeVarintSliceStackW)
      (F := memRegion (s0.sp - 240#64 - 32528#64) 7872 ∗
        ((ss + 296#64) ↦₆₄ 0#64) ∗ ((ss + 304#64) ↦₆₄ 1#64) ∗ ((ss + 312#64) ↦₆₄ 0#64) ∗
        ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗
        (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
          tail.length)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallD hF2 hsym2
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
      rfl
      (by simp only [Prost.X.decodeVarintSliceSpecW, wp_norm, arm64_norm]; rfl)
      ?_
      (by rw [bytes_kyber_ne_split_mf14]; ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm])
      ?_
    · refine ⟨?_, ?_, Or.inl ?_⟩ <;>
        simp only [List.length_cons, kyberIdBytes_length i hct, BitVec.toNat_ofNat] <;> omega
    intro sf hpcf hrunf hspf hcsf hF3 hsym3
    simp only [wp_norm, arm64_norm] at hpcf
    have hsp_sf : sf.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm] using hspf
    have hx19_sf : sf.readReg64 (Reg.gpr 19#5) = slot := by
      simpa only [wp_norm, arm64_norm] using hcsf.1
    have hx20_sf : sf.readReg64 (Reg.gpr 20#5) = 99#64 := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.1
    have hx21_sf : sf.readReg64 (Reg.gpr 21#5) = ss := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
    have hx22_sf : sf.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
    rw [post_of_decode_ne_mf14WA A i hct tail ptr s0.sp _ sf (by simp only [wp_norm, arm64_norm])]
    refine SepWPp.pure_elim fun htr_sf => ?_
    have hc_ult2' : BitVec.ult (BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length)) 2#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub2' : BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
      tail.length) - 2#64 =
        BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length) := by
      have hsub := len_sub_mf14W (a := 1575 + (encodeVarint (i.setWidth 64)).length) (b :=
        2) (n := tail.length) (by omega) (by omega)
      have heq : 1575 + (encodeVarint (i.setWidth 64)).length - 2 + tail.length =
          1573 + (encodeVarint (i.setWidth 64)).length + tail.length := by omega
      rwa [heq] at hsub
    have hc_ult_body : BitVec.ult (BitVec.ofNat 64 (1573 +
      (encodeVarint (i.setWidth 64)).length + tail.length))
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_sub_body : BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length) -
        BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length) =
        BitVec.ofNat 64 tail.length := by
      have := len_sub_mf14W (a := 1573 + (encodeVarint (i.setWidth 64)).length)
        (b := 1573 + (encodeVarint (i.setWidth 64)).length) (n := tail.length) (by omega) (by omega)
      simpa using this
    have hc_ule_body : BitVec.ule (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length))
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ule_n2' : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n' : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n2' : BitVec.ult (BitVec.ofNat 64 (1573 +
      (encodeVarint (i.setWidth 64)).length + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_ule_n' : BitVec.ule (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_eq_n' : (BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length + tail.length) ==
        BitVec.ofNat 64 tail.length) = false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hc_sub1' : BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length +
      tail.length) - 1#64 =
        BitVec.ofNat 64 (1572 + (encodeVarint (i.setWidth 64)).length + tail.length) := by
      have hsub := len_sub_mf14W (a := 1573 + (encodeVarint (i.setWidth 64)).length) (b :=
        1) (n := tail.length) (by omega) (by omega)
      have heq : 1573 + (encodeVarint (i.setWidth 64)).length - 1 + tail.length =
          1572 + (encodeVarint (i.setWidth 64)).length + tail.length := by omega
      rwa [heq] at hsub
    apply of_sepWP_frozen_mf14 hF3 hsym3 (mid := entry + int32MergeRelOff_mf14W)
    have htr_sf' : sf.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm] using htr_sf
    have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
    have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
    have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
    iterate 45 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf])
    intro hF4 hsym4
    refine call_alloc_entails_inImage_mf14W (s0 := s0) (R := R)
      (x := (⟨.varint, ss + 320#64, bufRef, slot, ptr + 3#64, kyberIdBytes i ct tail⟩ :
        Prost.Int32MergeGhost))
      (T := memRegion (ss + 320#64) 4 ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot (ptr + 3#64) (kyberIdBytes i ct tail) ∗ A.pool ∗
        stackAt (s0.sp - 240#64) Prost.X.int32MergeStackW)
      (F := memRegion (s0.sp - 240#64 - 32528#64) 7792 ∗
        ((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((s0.sp - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ss + 296#64) ↦₆₄ 0#64) ∗ ((ss + 304#64) ↦₆₄ 1#64) ∗ ((ss + 312#64) ↦₆₄ 0#64) ∗
        memRegion (ss + 324#64) 4 ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallI hF4 hsym4
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunf])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm, hsp_sf] using hsp_align)
      rfl
      (by simp only [Prost.X.int32MergeSpecW, wp_norm, arm64_norm, hsp_sf]; rfl)
      (by rw [kyberIdBytes_length i hct]; omega)
      (by
        refine Entails.trans ?_ (pre_to_int32Merge_ne_mf14WA A ss bufRef slot ptr s0.sp i hct tail _)
        exact Entails.of_eq (by ac_rfl))
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm, htr_sf'])
      ?_
    intro sfI hpcfI hrunfI hspfI hcsfI hF5 hsym5
    simp only [wp_norm, arm64_norm] at hpcfI
    have hsp_sfI : sfI.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm, hsp_sf] using hspfI
    rw [post_of_int32Merge_ne_mf14WA A ss bufRef slot ptr s0.sp i hct tail _ sfI
      (by simp only [wp_norm, arm64_norm, hsp_sf])]
    refine SepWPp.pure_elim fun htr_sfI => SepWPp.pure_elim fun hx0_sfI => ?_
    have htr_sfI' : sfI.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm, htr_sf'] using htr_sfI
    have hx0_sfI' : sfI.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sfI
    have hx19_sfI : sfI.readReg64 (Reg.gpr 19#5) = 98#64 := by
      simpa only [wp_norm, arm64_norm] using hcsfI.1
    have hx20_sfI : sfI.readReg64 (Reg.gpr 20#5) = ss := by
      simpa only [wp_norm, arm64_norm] using hcsfI.2.1
    have hx21_sfI : sfI.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
      simpa only [wp_norm, arm64_norm] using hcsfI.2.2.1
    have hx22_sfI : sfI.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm] using hcsfI.2.2.2.1
    have hx26_sfI : sfI.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm, hx26_sf] using hcsfI.2.2.2.2.2.2.2.1
    have hx27_sfI : sfI.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm, hx27_sf] using hcsfI.2.2.2.2.2.2.2.2.1
    have hx28_sfI : sfI.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm, hx28_sf] using hcsfI.2.2.2.2.2.2.2.2.2.1
    have hvregs_sfI : calleeSavedVRegs sfI = calleeSavedVRegs s0 := by
      have h1 : calleeSavedVRegs sfI = calleeSavedVRegs sf := by
        simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsfI.2.2.2.2.2.2.2.2.2.2.2
      exact h1.trans hvregs_sf
    have hc_ule_n2 : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 (1572 + tail.length)) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hc_ult_n2 : BitVec.ult (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_ule_n : BitVec.ule (BitVec.ofNat 64 (1572 + tail.length))
        (BitVec.ofNat 64 tail.length) = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hc_eq_n : (BitVec.ofNat 64 (1572 + tail.length) == BitVec.ofNat 64 tail.length) =
      false := by
      rw [beq_eq_false_iff_ne]; intro heq
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at h1; omega
    have hc_sub1 : BitVec.ofNat 64 (1572 + tail.length) - 1#64 =
        BitVec.ofNat 64 (1571 + tail.length) := len_sub_mf14W (by omega) (by omega)
    apply of_sepWP_frozen_mf14 hF5 hsym5 (mid := entry + bytesMergeRelOff_mf14W)
    iterate 33 wp_step
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunfI])
    intro hF6 hsym6
    refine call_alloc_inImage_mf14W (s0 := s0) (R := R)
      (x := (⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, kyberPtr2 ptr i + 1#64,
        innerBytes ct tail⟩ : Prost.BytesMergeGhost))
      (T := vecU8At A (ss + 296#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        Prost.sliceCursorAt slot (kyberPtr2 ptr i + 1#64) (innerBytes ct tail) ∗ A.pool ∗
        stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW)
      (F := memRegion (s0.sp - 240#64 - 32528#64) 7648 ∗
        ((s0.sp - 232#64) ↦₃₂ 0#32) ∗ ((s0.sp - 228#64) ↦₃₂ 0#32) ∗
        ((s0.sp - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((s0.sp - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
        (kyberPtr2 ptr i ↦₈ 18#8) ∗
        ((ss + 320#64) ↦₃₂ i) ∗ memRegion (ss + 324#64) 4 ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 208#64) 128)
      hcallB hF6 hsym6
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrunfI])
      (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm, hsp_sfI] using hsp_align)
      rfl
      (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm, hsp_sfI]; rfl)
      (by simp only [innerBytes_length hct]; omega)
      (by
        rw [← emptyVec_kyber_eq_vecU8At, ← sliceCursorAt_inner_ne_fold_mf14 slot ptr i hct tail,
          ← sepConj_assoc (stackAt _ _), sepConj_comm (stackAt _ _),
          int32Merge_to_bytesMerge_stack_mf14W]
        ac_rfl)
      (fun _ _ => rfl) (fun _ => rfl)
      (by simp only [wp_norm, arm64_norm, htr_sfI'])
      ?_
    intro sf2 hpcf2 hrunf2 hspf2 hcsf2 _ _
    simp only [wp_norm, arm64_norm] at hpcf2
    have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
      simpa only [wp_norm, arm64_norm, hsp_sfI] using hspf2
    rw [post_of_bytesMerge_ne_mf14WA A ss bufRef slot ptr s0.sp i hct tail _ sf2
      (by simp only [wp_norm, arm64_norm, hsp_sfI])]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
      SepWPp.pure_elim fun htr_sf2 => SepWPp.pure_elim fun hx0_sf2 => ?_
    have htr_sf2' : sf2.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm, htr_sfI'] using htr_sf2
    have hx0_sf2' : sf2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf2
    have hx26_sf2 : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
      simpa only [wp_norm, arm64_norm, hx26_sfI] using hcsf2.2.2.2.2.2.2.2.1
    have hx27_sf2 : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      simpa only [wp_norm, arm64_norm, hx27_sfI] using hcsf2.2.2.2.2.2.2.2.2.1
    have hx28_sf2 : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      simpa only [wp_norm, arm64_norm, hx28_sfI] using hcsf2.2.2.2.2.2.2.2.2.2.1
    have hvregs_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
      have h1 : calleeSavedVRegs sf2 = calleeSavedVRegs sfI := by
        simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
      exact h1.trans hvregs_sfI
    have hx21_sf2 : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
      simpa only [wp_norm, arm64_norm, hx21_sfI] using hcsf2.2.2.1
    have hx22_sf2 : sf2.readReg64 (Reg.gpr 22#5) = bufRef := by
      simpa only [wp_norm, arm64_norm, hx22_sfI] using hcsf2.2.2.2.1
    have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = false := by
      simp [BitVec.ult]
    have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length)
        (BitVec.ofNat 64 tail.length) = true := by
      simp [BitVec.ule]
    apply SepWPp.of_sepWP_ret
    iterate 19 wp_step
    apply SepWP.fold (final_post_entails_ne_kyber_mf14WA A ss cap' ptr' v bufRef slot ptr hi hct tail s0.sp
      (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) v80
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
      (sepConj_emp _).symm
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm,
      hrunf2])
    refine ⟨fun hmf => sat_pure_true_mf14W ⟨?_, ?_⟩ hmf,
      by simp only [wp_norm, arm64_norm],
      by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm, hx26_sf2,
        hx27_sf2, hx28_sf2]; exact hvregs_sf2⟩
    · simp only [wp_norm, arm64_norm, htr_sf2']
    · simp only [wp_norm, arm64_norm]

/-- Minimal-footprint `merge_field` leaf for tag 14 (`pending_kyber_pre_key`) over `kyberAt14`
on `A0`. -/
theorem mergeField14KyberW_ok (img : Obj.Image)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtW img ext) :
    MergeField14KyberOkAtW img ext (fun fl => fl.tag = 14) :=
  okAtX_of_eq_pre_post_mf14 (mergeField14KyberWA_ok img A0 ext hLoads hC)
    (fun _ _ => by
      dsimp only [mergeField14KyberSpecAtWA, mergeField14KyberSpecAtW]
      rw [show A0.pool = emp from rfl]; ac_rfl)
    (fun _ _ _ => by
      dsimp only [mergeField14KyberSpecAtWA, mergeField14KyberSpecAtW]
      rw [show A0.pool = emp from rfl]; ac_rfl)
    rfl rfl rfl

/-- `merge_field` leaf for tag 14 (`pending_kyber_pre_key`) over `prostSSGXNoPqAt_x14` for
arbitrary `A : RustAlloc`. -/
theorem mergeField14WA_ok (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtWA img A ext) :
    MergeField14OkAtWA img A ext (fun fl => fl.tag = 14) :=
  mergeField14OkAtWA_of_kyber (fun _ h => h) (mergeField14KyberWA_ok img A ext hLoads hC)

/-- `merge_field` leaf for tag 14 (`pending_kyber_pre_key`) over `prostSSGXNoPqAt_x14` on `A0`,
derived from `mergeField14KyberW_ok` by framing `restX14NoPq A0 ss v`. -/
theorem mergeField14W_ok (img : Obj.Image)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtW img ext) :
    MergeField14OkAtW img ext (fun fl => fl.tag = 14) :=
  mergeField14OkAtW_of_kyber (fun _ h => h) (mergeField14KyberW_ok img ext hLoads hC)

/-- Lift `MergeField14OkAtWA` (over `prostSSGXNoPqAt_x14`) to `MergeFieldQOkAtWA` by framing
`vecU8 A (x.ss + 0x78#64) x.v.ext.pq` via `prostSSGQAt_eq_x14_sep_pq`. -/
theorem mergeFieldQOkAtWA_of_14 (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (h14 : MergeField14OkAtWA img A ext (fun fl => fl.tag = 14)) :
    MergeFieldQOkAtWA img A ext (fun fl => ∃ i ct, fl = .kyber i ct) := by
  refine okAtX_of_imp_frame_mf14 h14 (fun _ _ _ _ => rfl) allocPanic_frame_mf14 ?_
    (fun _ _ _ => rfl)
  intro x s0 R hpre
  dsimp only [mergeFieldQSpecAtWA] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, ⟨i, ct, hfl⟩, hok, hfresh, hlen, hF, hsym⟩, hmem⟩
  let fx : GenFieldX := .kyber i ct
  have hfl' : x.fld = GenFieldX.toGenFieldQ fx := hfl
  rw [hfl'] at hx1 hx2 hok hfresh hlen hmem
  rw [toGenFieldQ_tag] at hx1; rw [toGenFieldQ_wt] at hx2; rw [toGenFieldQ_payload] at hlen hmem
  have hok_fx : fx.Ok := (toGenFieldQ_ok fx).mp hok
  have hfresh_fx : fx.Fresh x.v.toSSGX := ((toGenFieldQ_fresh_iff x.v fx).mp hfresh).1
  have hnpq : GenFieldX.NoPq fx := trivial
  refine ⟨⟨x.ss, x.v.toSSGX, fx, x.bufRef, x.slot, x.ptr, x.tail⟩,
    vecU8 A (x.ss + 0x78#64) x.v.ext.pq, ?_, ?_⟩
  · dsimp only [mergeField14SpecAtWA]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, rfl, hok_fx, hfresh_fx, hlen, hF, hsym⟩, ?_⟩
    rw [prostSSGQAt_eq_x14_sep_pq A x.ss x.v] at hmem
    convert hmem using 1; ac_rfl
  · intro sf hpost
    dsimp only [mergeField14SpecAtWA] at hpost
    dsimp only [mergeFieldQSpecAtWA]
    rw [hfl', toGenFieldQ_payload,
      prostSSGQAt_eq_x14_sep_pq A x.ss (x.v.apply (GenFieldX.toGenFieldQ fx)),
      apply_toGenFieldQ_toSSGX x.v fx hnpq, apply_toGenFieldQ_pq x.v fx hnpq]
    convert hpost using 1; ac_rfl

end Symbolic.Swarm.TRREF.B3DeserQ

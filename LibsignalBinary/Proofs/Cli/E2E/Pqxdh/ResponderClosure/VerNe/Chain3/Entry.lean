/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
import LibsignalBinary.Proofs.Cli.ShardFill.ChainMerge5Decode
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `message::merge<Chain> [local#5]`: Entry Slice

Verifies `Chain3EntryStmtExt` (`+0x000 → +0x0a8`, `k = 0`), covering the `0xf0`-byte frame prologue,
wire-type check (`wt == 2`), delimited length `decode_varint` call at `+0x034`, and loop-limit setup
(`x21 = |tail|`, `x22 = sp + 8`, `w23 = 1`, `w24 = 104`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## 1. Pure helpers -/

set_option maxHeartbeats 400000 in
private theorem w0_and_255_eq_two_c3 {w : BitVec 64} (h : w.setWidth 8 = 2#8) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 w) &&& 255#64 = 2#64 := by
  apply BitVec.eq_of_toNat_eq
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
    BitVec.toNat_and, BitVec.toNat_ofNat] at h' ⊢
  rw [show 255 % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

set_option maxHeartbeats 400000 in
private theorem bv_ofNat_add_sub_left_c3 (m k : Nat) :
    BitVec.ofNat 64 (m + k) - BitVec.ofNat 64 m = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add, BitVec.add_comm, BitVec.add_sub_cancel]

set_option maxHeartbeats 400000 in
private theorem ult_ofNat_add_left_false_c3 {m k : Nat} (hlt : m + k < 2 ^ 62) :
    (BitVec.ofNat 64 (m + k)).ult (BitVec.ofNat 64 m) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

set_option maxHeartbeats 400000 in
private theorem ule_ofNat_add_right_true_c3 {m k : Nat} (hlt : m + k < 2 ^ 62) :
    (BitVec.ofNat 64 m).ule (BitVec.ofNat 64 (m + k)) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_true_eq]
  omega

set_option maxHeartbeats 400000 in
private theorem sp_sub_f0_aligned_c3 {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0xf0#64) &&& 15#64 = 0#64 := by
  have := sp_and_15_sub_aligned sp0 0xf0#64 (by decide)
  simpa only [show (0b1111#64 : BitVec 64) = 15#64 from rfl, h] using this

set_option maxHeartbeats 400000 in
private theorem allocFailedIn_of_trace_eq_c3 {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rwa [htr] at h

set_option maxHeartbeats 400000 in
private theorem chainG_enc_eq_fields_c3 (c : ChainG) :
    c.enc = c.fields.flatMap ChainField.enc := by
  rcases c with ⟨srk, priv, ck, keys⟩
  unfold ChainG.enc ChainG.fields
  simp only [List.flatMap_append, List.flatMap_map]
  have h1 : bytesField 1 srk =
      List.flatMap ChainField.enc (if srk = [] then [] else [ChainField.srk srk]) := by
    unfold bytesField; split <;> simp [ChainField.enc]
  have h2 : bytesField 2 priv =
      List.flatMap ChainField.enc (if priv = [] then [] else [ChainField.priv priv]) := by
    unfold bytesField; split <;> simp [ChainField.enc]
  have h3 : msgField 3 (Option.map (fun ik => uint32Field 1 ik.1 ++ bytesField 2 ik.2) ck) =
      List.flatMap ChainField.enc
        (match ck with | some (i, k) => [ChainField.ck i k] | none => []) := by
    cases ck <;> simp [msgField, ChainField.enc]
  have h4 : (List.map (fun m => lenField 4 (encMessageKey m)) keys).flatten =
      List.flatMap (fun a => (ChainField.key a).enc) keys := by
    rw [← List.flatMap_def]; rfl
  rw [h1, h2, h3, h4]; rfl

/-! ## 2. Pre-call segment `+0x000 → bl decode_varint [local#3]` -/

set_option maxHeartbeats 400000 in
/-- Prologue, `wt == 2`, `x0 = x19 = bufRef`, `x20 = a`, and the `bl` at `+0x034`. -/
theorem step_chain3Entry_pre (img : Obj.Image)
    {ext : String → Option (State → State)}
    (a bufRef sp0 : BitVec 64)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8) (hx1 : s0.readReg64 .x1 = a)
    (hx2 : s0.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64) →
      sm.status = .Running → sm.sp = sp0 - 0xf0#64 → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x38#64 →
      sm.readReg64 .x0 = bufRef → sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a →
      sm.readReg64 .x26 = s0.readReg64 .x26 → sm.readReg64 .x27 = s0.readReg64 .x27 →
      sm.readReg64 .x28 = s0.readReg64 .x28 → sm.readReg64 .x29 = sp0 - 0x50#64 →
      ∀ Pm, (Pm ⊢ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ chain3SavedRegs sp0 s0) →
        post sm Pm) :
    SepWP (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainMerge3Name + bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]")) % 2 ^ 64)) s0
      (stackAt sp0 chainMerge3StackX) post := by
  subst hsp
  have hsp_sub_align : (s0.sp - 0xf0#64) &&& 15#64 = 0#64 := sp_sub_f0_aligned_c3 hsp_align
  chain3_fetches_range img.base (Rust.withPanics ext) 0x0 0x34
  dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
  examples_hide_fetches
  have h1 : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = bufRef := hx2
  have hw0 : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64 =
      2#64 := w0_and_255_eq_two_c3 hx0
  rw [stackAt_chainMerge3StackX_split s0.sp]
  unfold chain3Cells
  simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w80; apply SepWP.exists_elim; intro w72
  apply SepWP.exists_elim; intro w64; apply SepWP.exists_elim; intro w56
  apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
  apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
  apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
  iterate 14 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) _ ?_
  unfold chain3SavedRegs
  rw [ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_right w56 (sep_ac_seedChain (by ac_rfl))

/-! ## 3. Post-call segment `+0x038 → +0x0a8` -/

set_option maxHeartbeats 400000 in
/-- After `decode_varint [local#3]` returned `x0 = 0`, `x1 = m` with `k` bytes left after the
body: `tbnz` (not taken), `x21 = (m + k) - m = k`, `b.hs` (taken), `x22 = sp + 8`, `w23 = 1`,
`w24 = 104`. -/
theorem step_chain3Entry_post (img : Obj.Image)
    {ext : String → Option (State → State)}
    (a bufRef slot ptr' sp0 x26 x27 x28 : BitVec 64) (m k : Nat) (hlt : m + k < 2 ^ 62)
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x38#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64) (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = 0#64) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 m)
    (hx19 : s.readReg64 .x19 = bufRef) (hx20 : s.readReg64 .x20 = a)
    (hx26 : s.readReg64 .x26 = x26) (hx27 : s.readReg64 .x27 = x27)
    (hx28 : s.readReg64 .x28 = x28) (hx29 : s.readReg64 .x29 = sp0 - 0x50#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64 →
      sm.status = .Running → sm.sp = sp0 - 0xf0#64 → sm.trace = s.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 k → sm.readReg64 .x22 = sp0 - 0xe8#64 →
      sm.readReg64 .x23 = 1#64 → sm.readReg64 .x24 = 104#64 →
      sm.readReg64 .x26 = x26 → sm.readReg64 .x27 = x27 → sm.readReg64 .x28 = x28 →
      sm.readReg64 .x29 = sp0 - 0x50#64 →
      ∀ Pm, (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr') ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (m + k))) → post sm Pm) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64) s
      ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr') ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (m + k)))
      post := by
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact sp_sub_f0_aligned_c3 hsp_align
  chain3_fetches_range img.base (Rust.withPanics ext) 0x38 0x50
  chain3_fetches_range img.base (Rust.withPanics ext) 0x9c 0xa4
  dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
  examples_hide_fetches
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 m := hx1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h26 : s.readReg64 (Reg.gpr 26#5) = x26 := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = x27 := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = x28 := hx28
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have hsub := bv_ofNat_add_sub_left_c3 m k
  have hult := ult_ofNat_add_left_false_c3 hlt
  have hule := ule_ofNat_add_right_true_c3 hlt
  iterate 10 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [h19, arm64_norm]) (by simp only [h20, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [h26, arm64_norm]) (by simp only [h27, arm64_norm])
    (by simp only [h28, arm64_norm]) (by simp only [h29, arm64_norm]) _ ?_
  exact sep_ac_seedChain (by ac_rfl)

/-! ## 4. The Entry slice -/

set_option maxHeartbeats 400000 in
/-- Entry slice (`+0x000 → +0x0a8` with `k = 0` fields consumed), parameterized over `A : RustAlloc`. -/
theorem chain3Entry_ok_ext {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) :
    Chain3EntryStmtExt A img ext := by
  intro hC x R s0 hpc hrun hpre hal hL0
  rcases x with ⟨a, c, bufRef, slot, ptr, tail⟩
  dsimp only [chainMerge3SpecAtWExt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hcOk, hlen_lt, hF0, hsym0⟩, hmem⟩
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hal
  have hsp_sub_align : (s0.sp - 0xf0#64) &&& 15#64 = 0#64 := sp_sub_f0_aligned_c3 hsp_align
  have hmem1 : s0.mem ⊨ stackAt s0.sp chainMerge3StackX ∗
      (chain3GAt A a ChainG.empty ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (c.payload ++ tail) ∗ A.pool ∗ R) :=
    Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, hsp1, htr1, hvregs1, hlr1, hx0_1, hx19_1, hx20_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hent1⟩ | ⟨_, hoom1⟩⟩ :=
    (step_chain3Entry_pre (img := img) (ext := ext) a bufRef s0.sp
      (post := fun sm Pm =>
        sm.sp = s0.sp - 0xf0#64 ∧ sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x38#64 ∧
        sm.readReg64 .x0 = bufRef ∧ sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧
        sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧ sm.readReg64 .x29 = s0.sp - 0x50#64 ∧
        (Pm ⊢ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0))
      hpc hrun rfl hsp_align hx0 hx1 hx2
      (fun _ _ _ hsp' htr' hvregs' hlr' hx0' hx19' hx20' hx26' hx27' hx28' hx29' _ hent =>
        ⟨hsp', htr', hvregs', hlr', hx0', hx19', hx20', hx26', hx27', hx28', hx29',
          hent⟩)).elim hmem1 hL0
  rotate_left; · exact (not_satisfies_false_sepConj hoom1).elim
  have hm1' := Satisfies.mono (sepConj_mono_left hent1) hm1
  have hal1 : s1.spAligned = true := by
    simp only [State.spAligned, hsp1, beq_iff_eq]; exact hsp_sub_align
  let gvar : CryptoVerification.LibsignalTripleRatchet.Prost.DecodeVarintSlowGhost := ⟨bufRef, slot, ptr, c.payload ++ tail⟩
  let F_call : SepProp :=
    memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 chainMerge3SubStackX)
        (chainMerge3SubStackX - decodeVarint2StackX) ∗
      chain3SavedRegs s0.sp s0 ∗ chain3GAt A a ChainG.empty
  have hlen63 : (c.payload ++ tail).length < 2 ^ 63 := Nat.lt_trans hlen_lt (by decide)
  have hm1_call : s1.mem ⊨
      ((decodeVarint2SpecX A).inImage img).pre gvar s1 ∗
        (F_call ∗ R) := by
    unfold Spec.inImage decodeVarint2SpecX
    dsimp only [gvar]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hst1.frozenLoaded hF0, hst1.symtab_eq.trans hsym0⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_1, hlen63⟩, ?_⟩
    rw [stackAt_c3Sub_to_decodeVarint (s0.sp - 0xf0#64)] at hm1'
    rw [hsp1]
    dsimp only [F_call]
    convert hm1' using 1
    ac_rfl
  have hsub_dv := c3_decodeVarint_ok_sub hC
  obtain ⟨s2, hst2, hpost2, -⟩ :=
    hsub_dv.no_fault_before_outcome gvar (F_call ∗ R) s1 hpc1 hrun1 hm1_call hal1
      (hst1.codeLoaded hL0)
  rcases hpost2 with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hm2⟩ | ⟨hpan2, hm2_pan⟩ |
    ⟨code, _, hm2_ex⟩ | ⟨_, hm2_oom⟩
  · have hpc2' : s2.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0x38#64 := by
      rw [hpc2, hlr1]
    have hsp2' : s2.sp = s0.sp - 0xf0#64 := by rw [hsp2, hsp1]
    have hx19_2 : s2.readReg64 .x19 = bufRef := hcs2.1.trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = a := hcs2.2.1.trans hx20_1
    have hx26_2 : s2.readReg64 .x26 = s0.readReg64 .x26 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
    have hx27_2 : s2.readReg64 .x27 = s0.readReg64 .x27 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
    have hx28_2 : s2.readReg64 .x28 = s0.readReg64 .x28 :=
      hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
    have hx29_2 : s2.readReg64 .x29 = s0.sp - 0x50#64 :=
      hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 :=
      hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    have hpay_split : c.payload ++ tail =
        encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.enc ++ tail) := by
      unfold ChainG.payload; rw [List.append_assoc]
    have hdec : decodeVarint (c.payload ++ tail) =
        some (BitVec.ofNat 64 c.enc.length, c.enc ++ tail) := by
      rw [hpay_split]; exact decodeVarint_encodeVarint (BitVec.ofNat 64 c.enc.length) (c.enc ++ tail)
    unfold Spec.inImage decodeVarint2SpecX at hm2
    dsimp only [gvar] at hm2
    rw [hdec] at hm2
    dsimp only at hm2
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨⟨hx0_2, hx1_2⟩, htr2, hm2⟩
    rw [hsp1] at hm2
    have hlenA : (c.enc ++ tail).length = c.enc.length + tail.length := List.length_append
    have hlt2 : c.enc.length + tail.length < 2 ^ 62 := by
      unfold ChainG.payload at hlen_lt; simp only [List.length_append] at hlen_lt; omega
    let p1 := ptr + BitVec.ofNat 64 ((c.payload ++ tail).length - (c.enc ++ tail).length)
    unfold sliceCursorAfter at hm2
    have hm2_post : s2.mem ⊨
        ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ p1) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc.length + tail.length))) ∗
        ((ptr ↦ₛ (c.payload ++ tail)) ∗ A.pool ∗
          stackAt (s0.sp - 0xf0#64) decodeVarint2StackX ∗
          F_call ∗ R) := by
      rw [← hlenA]
      dsimp only [p1]
      refine Satisfies.mono (sep_ac_seedChain ?_) hm2
      ac_rfl
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, hsp3, htr3, hvregs3, hx19_3, hx20_3, hx21_3,
        hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3, hx29_3, hent3⟩ | ⟨_, hoom3⟩⟩ :=
      (step_chain3Entry_post (img := img) (ext := ext) a bufRef slot p1 s0.sp
        (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28)
        c.enc.length tail.length hlt2
        (post := fun sm Pm =>
          sm.sp = s0.sp - 0xf0#64 ∧ sm.trace = s2.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s2 ∧
          sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 tail.length ∧
          sm.readReg64 .x22 = s0.sp - 0xe8#64 ∧ sm.readReg64 .x23 = 1#64 ∧
          sm.readReg64 .x24 = 104#64 ∧
          sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧
          sm.readReg64 .x28 = s0.readReg64 .x28 ∧ sm.readReg64 .x29 = s0.sp - 0x50#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ p1) ∗
            ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc.length + tail.length))))
        hpc2' hrun2 hsp2' hsp_align hx0_2 hx1_2 hx19_2 hx20_2 hx26_2 hx27_2 hx28_2 hx29_2
        (fun _ _ _ hsp' htr' hvregs' hx19' hx20' hx21' hx22' hx23' hx24' hx26' hx27' hx28'
            hx29' _ hent =>
          ⟨hsp', htr', hvregs', hx19', hx20', hx21', hx22', hx23', hx24', hx26', hx27', hx28',
            hx29', hent⟩)).elim hm2_post ((hst1.trans hst2).codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj hoom3).elim
    have hm3' := Satisfies.mono (sepConj_mono_left hent3) hm3
    have hst_all := (hst1.trans hst2).trans hst3
    refine ⟨s3, hst_all, Or.inl ⟨hpc3, hrun3, (htr3.trans htr2).trans htr1,
      hvregs3.trans hvregs2, hst_all.symtab_eq.trans hsym0, hst_all.frozenLoaded hF0, hsp3,
      by simp only [State.spAligned, hsp3, beq_iff_eq]; exact hsp_sub_align,
      hx29_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3,
      hcOk, hlen_lt, ?_⟩⟩
    dsimp only
    have hchain0 : chainGAfter c 0 = ChainG.empty := rfl
    have hdrop0 : (c.fields.drop 0).flatMap ChainField.enc = c.enc := by
      rw [List.drop_zero, ← chainG_enc_eq_fields_c3 c]
    rw [hchain0, hdrop0]
    unfold sliceCursorAfter
    rw [hlenA, stackAt_c3Sub_to_decodeVarint (s0.sp - 0xf0#64)]
    dsimp only [F_call, p1] at hm3'
    rw [hlenA] at hm3'
    refine Satisfies.mono (sep_ac_seedChain ?_) hm3'
    ac_rfl
  · refine ⟨s2, hst1.trans hst2, Or.inr ⟨hpan2, ?_⟩⟩
    unfold Spec.inImage decodeVarint2SpecX at hm2_pan
    dsimp only at hm2_pan
    dsimp only [chainMerge3SpecAtWExt, Serialization.allocPanic]
    refine allowPanic_frame (F := F_call) (allocFailedIn_of_trace_eq_c3 htr1) ?_
    rw [sepConj_assoc _ F_call R]
    exact hm2_pan
  · exact False.elim (not_satisfies_false_sepConj hm2_ex)
  · exact False.elim (not_satisfies_false_sepConj hm2_oom)

theorem chain3Entry_ok (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3EntryStmt img ext := by
  rw [← Chain3EntryStmtExt_A0]
  exact chain3Entry_ok_ext img ext

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

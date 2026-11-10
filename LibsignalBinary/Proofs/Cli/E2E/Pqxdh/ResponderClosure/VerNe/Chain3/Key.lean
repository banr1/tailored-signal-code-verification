/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeyDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeyInner
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeySeg3a
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeySeg3c
import LibsignalBinary.Proofs.Cli.ShardFill.ChainMerge5Decode
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# `message::merge<Chain> [local#5]`: ChainKey Slice

Proves the inner-loop exit `step_chain3_seg3d` (`+0x368 → +0x3f0 → +0x0a8`) and assembles segments
3a (`KeySeg3a`), 3b (`KeyInner`), 3c (`KeySeg3c`), and 3d into the unconditional tag-3 `ChainKey`
slice `chain3ChainKey_ok_ext` (`Chain3ChainKeyStmtExt`).
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
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## 1. Segment 3d: Inner loop exit (`+0x368 → +0x3f0 → +0x0a8`) -/

set_option maxHeartbeats 400000 in
/-- Inner loop exit (`+0x368 → +0x0a8`) when remaining slice is `afterCk`. -/
theorem step_chain3_seg3d (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3Seg3dStmt img ext := by
  intro a bufRef slot ptr sp0 afterCk outerTailLen ret s_init s0 F Q Qp
    hpc hrun hF hsym htr hvregs hregs hnext
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  chain3_fetches_range img.base (Rust.withPanics ext) 0x368 0x374
  chain3_fetches_range img.base (Rust.withPanics ext) 0x3f0 0x3f8
  dsimp only [SP2Ext, contractProg, chainMerge3Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]" = entry
  examples_hide_fetches
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s0.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s0.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 afterCk.length := hx25
  have h26 : s0.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s0.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s0.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (168)) hF hsym ?_
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 7 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm])
    hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    ⟨by simp only [hsp, arm64_norm],
     by simp only [h29, arm64_norm],
     by simp only [h19, arm64_norm],
     by simp only [h20, arm64_norm],
     by simp only [h21, arm64_norm],
     by simp only [h22, arm64_norm],
     by simp only [h23, arm64_norm],
     by simp only [h24, arm64_norm],
     by simp only [h25, arm64_norm],
     by simp only [h26, arm64_norm],
     by simp only [h27, arm64_norm],
     by simp only [h28, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

/-! ## 2. Assembly of `Chain3ChainKeyStmt` from `Seg3a`, `Seg3b`, `Seg3c`, `Seg3d` -/

set_option maxHeartbeats 400000 in
/-- Assemble `Chain3ChainKeyStmtExt A img ext` from `Chain3Seg3aStmtExt`, `Chain3Seg3bStmtExt`, and
`Chain3Seg3cStmtExt` (with `step_chain3_seg3d` proved above). -/
theorem chain3ChainKey_ok_of_segs_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (h3a : Chain3Seg3aStmtExt A img ext)
    (h3b : Chain3Seg3bStmtExt A img ext)
    (h3c : Chain3Seg3cStmtExt A img ext) :
    Chain3ChainKeyStmtExt A img ext := by
  intro hC x R s0 k s hk htag hs
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hcOk, hlen_lt, hmem⟩
  intro hL
  have hsp_sub_align : (s0.sp - 0xf0#64) &&& 15#64 = 0#64 := by
    have : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    simpa [hsp] using this
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_240_aligned hsp_sub_align
  obtain ⟨⟨i, key, hck_some, hfl_eq⟩, hck_none⟩ := chainField_tag_three_info x.c k hk htag
  have hkey_len : key.length = 32 := hcOk.2.2.1 (i, key) hck_some
  have hkey_lt : key.length < 128 := by omega
  have hck_bounds := ckEnc_length_bounds_seedChain i hkey_len
  let b3b : List (BitVec 8) := pbVarint 1 i.toNat
  let b3c : List (BitVec 8) := pbBytes 2 key
  let ck_body : List (BitVec 8) := b3b ++ b3c
  have hck_lt : ck_body.length < 128 := by dsimp [ck_body, b3b, b3c]; omega
  let b3a : List (BitVec 8) := [0x1a#8, BitVec.ofNat 8 ck_body.length]
  let pfx : List (BitVec 8) := pfx_k x.c k
  let afterCk : List (BitVec 8) := rem_k x.c (k + 1) x.tail
  have hfl_enc : (x.c.fields[k]'hk).enc = b3a ++ (b3b ++ b3c) := by
    rw [hfl_eq]
    exact chainField_ck_enc_eq i hkey_len
  have hrem_k : rem_k x.c k x.tail = 0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk) := by
    rw [rem_k_eq_cons x.c k x.tail hk, hfl_enc]
    dsimp [b3a, ck_body]
  have hpay_eq : x.c.payload ++ x.tail = pfx ++ rem_k x.c k x.tail :=
    payload_append_eq_pfx_rem x.c k x.tail
  have houter_le : x.tail.length ≤ afterCk.length := by
    dsimp [afterCk, rem_k]
    simp only [List.length_append]
    omega
  have hlen_lt3a : (2 + (ck_body.length + afterCk.length)) < 2 ^ 62 := by
    have h1 := hlen_lt
    rw [hpay_eq, hrem_k] at h1
    simp only [List.length_append, List.length_cons] at h1
    omega
  have hlen_lt3b : (b3b ++ b3c ++ afterCk).length < 2 ^ 62 := by
    have h1 : (b3b ++ b3c ++ afterCk).length = ck_body.length + afterCk.length :=
      List.length_append
    omega
  have hlen_lt3c : (b3c ++ afterCk).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_lt3b ⊢
    omega
  let c0 : ChainG := chainGAfter x.c k
  let ptr3a : BitVec 64 := x.ptr + BitVec.ofNat 64 pfx.length
  let ptr3b : BitVec 64 := ptr3a + 2#64
  let ptr3c : BitVec 64 := ptr3b + BitVec.ofNat 64 b3b.length
  let ptrEnd : BitVec 64 := ptr3c + BitVec.ofNat 64 b3c.length
  have hcur_init :
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) := by
    change sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rem_k x.c k x.tail) = _
    rw [hpay_eq, sliceCursorAfter_append_eq_seedChain x.slot x.ptr pfx (rem_k x.c k x.tail), hrem_k]
  have hmem_init : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗
        ((x.a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (x.a + 0x50#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX) ∗
        (chain3VecAt A x.a c0.srk ∗ chain3VecAt A (x.a + 0x18#64) c0.priv ∗
          vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chain3SavedRegs s0.sp s0)) ∗ R := by
    change s.mem ⊨
      chain3GAt A x.a c0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0 ∗ R at hmem
    rw [chain3GAt_ck_none_eq_ext A x.a c0 hck_none, hcur_init] at hmem
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hfull : SepWPp (SP2Ext img.base ext) (chain3PCAtW img ext 0xa8#64) s
      (((x.bufRef ↦₆₄ x.slot) ∗
        ((x.a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (x.a + 0x50#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX) ∗
        (chain3VecAt A x.a c0.srk ∗ chain3VecAt A (x.a + 0x18#64) c0.priv ∗
          vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chain3SavedRegs s0.sp s0))
      (fun sf Pf =>
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        Chain3InnerLoopRegs s0.sp x.bufRef x.a x.tail.length afterCk.length s0 sf ∧
        (Pf ⊢ chain3GAt A x.a (chainGAfter x.c (k + 1)) ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
            (((x.c.fields.drop (k + 1)).flatMap ChainField.enc) ++ x.tail) ∗
          A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (chainMerge3SpecAtWExt A img).onPanic x s0 sf ∗ R)) := by
    have hpc' : s.pc = (SP2Ext img.base ext).fnAddr chainMerge3Name + 0xa8#64 := hpc
    refine h3a hC x.a x.bufRef x.slot ptr3a s0.sp
      ck_body afterCk x.tail.length hck_lt houter_le hlen_lt3a
      hpc' hrun hsp hsp0_align hF hsym htr hvregs hx29 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 ?_
    intro s4 hpc4 hrun4 hF4 hsym4 htr4 hvregs4 hregs4
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        ((x.a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt x.slot ptr3b (b3b ++ (b3c ++ afterCk)) ∗
        A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX) ∗
        ((ptr3a ↦ₛ b3a) ∗
          chain3VecAt A (x.a + 0x48#64) [] ∗
          memRegion (x.a + 0x64#64) 4 ∗
          chain3VecAt A x.a c0.srk ∗ chain3VecAt A (x.a + 0x18#64) c0.priv ∗
          vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chain3SavedRegs s0.sp s0)))
      (by
        have hck_eq : ck_body ++ afterCk = b3b ++ (b3c ++ afterCk) := by
          simp [ck_body, b3b, b3c, List.append_assoc]
        dsimp only [ptr3b, b3a]
        rw [hck_eq]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine h3b hC x.a x.bufRef x.slot ptr3b s0.sp
      i b3c afterCk x.tail.length hlen_lt3b
      hpc4 hrun4 hsp0_align hF4 hsym4 htr4 hvregs4 hregs4 ?_
    intro s5 hpc5 hrun5 hF5 hsym5 htr5 hvregs5 hregs5
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        chain3VecAt A (x.a + 0x48#64) [] ∗
        sliceCursorAt x.slot ptr3c (b3c ++ afterCk) ∗
        A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX) ∗
        ((ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          ((x.a + 0x60#64) ↦₃₂ i) ∗
          memRegion (x.a + 0x64#64) 4 ∗
          chain3VecAt A x.a c0.srk ∗ chain3VecAt A (x.a + 0x18#64) c0.priv ∗
          vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chain3SavedRegs s0.sp s0)))
      (by dsimp only [ptr3c, b3b]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine h3c hC x.a x.bufRef x.slot ptr3c s0.sp
      key afterCk x.tail.length hkey_lt hlen_lt3c
      hpc5 hrun5 hsp0_align hF5 hsym5 htr5 hvregs5 hregs5 ?_
    intro s6 hpc6 hrun6 hF6 hsym6 htr6 hvregs6 hregs6
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd afterCk ∗
        stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX) ∗
        (A.pool ∗
          (ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          (ptr3c ↦ₛ b3c) ∗
          vecU8 A (x.a + 0x48#64) key ∗
          ((x.a + 0x60#64) ↦₃₂ i) ∗
          memRegion (x.a + 0x64#64) 4 ∗
          chain3VecAt A x.a c0.srk ∗ chain3VecAt A (x.a + 0x18#64) c0.priv ∗
          vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chain3SavedRegs s0.sp s0)))
      (by dsimp only [ptrEnd, b3c]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chain3_seg3d img ext x.a x.bufRef x.slot ptrEnd s0.sp
      afterCk x.tail.length hpc6 hrun6 hF6 hsym6 htr6 hvregs6 hregs6 ?_
    intro sf hpcf hrunf hFf hsymf htrf hvregsf hregsf
    refine SepWPp.done hpcf hrunf ⟨hFf, hsymf, htrf, hvregsf, hregsf, ?_⟩
    have hc_succ : chainGAfter x.c (k + 1) = c0.apply (ChainField.ck i key) := by
      rw [chainGAfter_succ x.c k hk, hfl_eq]
    rw [hc_succ, chain3GAt_apply_ck_eq_ext A x.a c0 i key]
    have hcur_end := combine_tag3_cursor x.slot x.ptr pfx b3a b3b b3c afterCk rfl
    dsimp only at hcur_end
    have htotal_end : (pfx ++ (b3a ++ (b3b ++ b3c))) ++ afterCk = x.c.payload ++ x.tail := by
      rw [← hfl_enc, ← pfx_k_succ x.c k hk]
      exact (payload_append_eq_pfx_rem x.c (k + 1) x.tail).symm
    rw [htotal_end] at hcur_end
    change _ ⊢
      (chain3VecAt A x.a c0.srk ∗ chain3VecAt A (x.a + 0x18#64) c0.priv ∗
        vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
        vecU8 A (x.a + 0x48#64) key ∗ ((x.a + 0x60#64) ↦₃₂ i) ∗ memRegion (x.a + 0x64#64) 4) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) afterCk ∗
      A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0
    rw [← hcur_end]
    dsimp only [ptr3a, ptr3b, ptr3c, ptrEnd]
    exact sep_ac_seedChain (by ac_rfl)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem_init hL
  rcases hex with ⟨hpcf, hrunf, Pf, hmf, hFf, hsymf, htrf, hvregsf, hregsf, hentf⟩ | ⟨hpan, Pf, hmf, htrf⟩ | ⟨_, hoom⟩
  · rcases hregsf with ⟨hspf, hx29f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, _, hx26f, hx27f, hx28f⟩
    have half : sf.spAligned = true := by
      rw [State.spAligned, hspf, ← hsp]
      exact hal
    have hmemf := Satisfies.mono (sepConj_mono_left hentf) hmf
    simp only [sepConj_assoc] at hmemf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, htrf, hvregsf, hsymf, hFf, hspf, half, hx29f, hx19f, hx20f,
      hx21f, hx22f, hx23f, hx24f, hx26f, hx27f, hx28f, hcOk, hlen_lt, hmemf⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, htrf hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem chain3ChainKey_ok_of_segs (img : Obj.Image) (ext : String → Option (State → State))
    (h3a : Chain3Seg3aStmt img ext)
    (h3b : Chain3Seg3bStmt img ext)
    (h3c : Chain3Seg3cStmt img ext) :
    Chain3ChainKeyStmt img ext := by
  rw [← Chain3ChainKeyStmtExt_A0]
  exact chain3ChainKey_ok_of_segs_ext img ext
    (by rwa [Chain3Seg3aStmtExt_A0])
    (by rwa [Chain3Seg3bStmtExt_A0])
    (by rwa [Chain3Seg3cStmtExt_A0])

set_option maxHeartbeats 400000 in
/-- Tag-3 (`chain_key`) slice (`+0x0a8 → +0x0a8`) of `message::merge<Chain> [local#5]` for arbitrary `A : RustAlloc`. -/
theorem chain3ChainKey_ok_ext {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3ChainKeyStmtExt A img ext :=
  chain3ChainKey_ok_of_segs_ext img ext
    (step_chain3_seg3a_ext img ext)
    (chain3_seg3b_ext img ext)
    (chain3_seg3c_ext img ext)

theorem chain3ChainKey_ok (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3ChainKeyStmt img ext := by
  rw [← Chain3ChainKeyStmtExt_A0]
  exact chain3ChainKey_ok_ext img ext

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `chain_key` Sub-Loop and Epilogue Segments for Seed `message::merge<Chain>`

Proves the segment lemmas for outer field `3` (`chain_key` at `a + 0x48`) and function exit of
`prost::encoding::message::merge::<Chain>` (`0x3974`, block `11`):
* Segment 3a (`+0x120 → +0x4c8`): outer field `3` header `[0x1a#8, len]` and `ChainKey::default()` init.
* Segment 3b (`+0x4c8 → +0x4c8`): inner field `1` (`index` varint via `int32::merge`).
* Segment 3c (`+0x4c8 → +0x4c8`): inner field `2` (`key` bytes via `bytes::merge`).
* Segment 3d (`+0x4c8 → ret`): inner and outer loop exits and epilogue.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter BytesMergeOk Int32MergeOk)
open CryptoVerification.E2E.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
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

/-! ## Outer Field `3` Header (`+0x120 → +0x4c8`) -/

theorem ck_hdr_pointsTo_combine_seedChain (ptr : BitVec 64) (n : Nat) :
    (ptr ↦₈ 0x1a#8) ∗ ((ptr + 1#64) ↦₈ BitVec.ofNat 8 n) =
      (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 n]) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem step_chainMerge_seg3a_seedChain (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body tail : List (BitVec 8))
    (hck_lt : ck_body.length < 128)
    (hlen_lt : (2 + (ck_body.length + tail.length)) < 2 ^ 32)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx26 : s0.readReg64 .x26 = 1#64)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x23 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q Qp) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q Qp := by
  have hlen_gt : tail.length < (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail)).length < 2 ^ 32 := by
    simp only [List.length_cons, List.length_append]; omega
  have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x1a#8 (BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail))
  have hrem1_lt : (BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail)).length < 2 ^ 32 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz2 := cbz_len_cons_false_seedChain (b0 := BitVec.ofNat 8 ck_body.length)
    (bs1 := ck_body ++ tail) hrem1_lt
  have hse0 := signExtend64_ofNat8_lt128_seedChain hck_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hck_lt
  have hsub2 := len_cons_sub_one_seedChain (BitVec.ofNat 8 ck_body.length) (ck_body ++ tail)
  have hlen_ck_append : (ck_body ++ tail).length = ck_body.length + tail.length := List.length_append
  have hule_ck_sub := ule_ofNat_add_right_true_seedChain (m := ck_body.length) (k := tail.length) (by omega)
  have hsub_ck_tail := bv_ofNat_add_sub_left_seedChain ck_body.length tail.length
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x120 0x144
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x188 0x1ac
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x1d8 0x1dc
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x268 0x2a8
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x49c 0x4ac
  dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
  have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1224)) hF hsym ?_
  rw [memRegion24_split_ck_seedChain a]
  unfold sliceCursorAt noneCap
  rw [pointsToBytes_cons, pointsToBytes_cons]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w50
  apply SepWP.exists_elim; intro w58
  apply SepWP.exists_elim; intro w60
  iterate 44 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm])
    (by simp only [hvregs, arm64_norm])
    (by simp only [h19, arm64_norm])
    (by simp only [h20, arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [h24, arm64_norm]))
  unfold sliceCursorAt
  rw [← hlen_ck_append, ← ck_hdr_pointsTo_combine_seedChain ptr ck_body.length]
  have hvec := emptyVec_entails_vecU8_seedChain (a + 0x48#64)
  have h48_8 : (a + 0x48#64) + 8#64 = a + 0x50#64 := by bv_omega
  have h48_16 : (a + 0x48#64) + 16#64 = a + 0x58#64 := by bv_omega
  have hptr2 : ptr + 1#64 + 1#64 = ptr + 2#64 := by bv_omega
  rw [h48_8, h48_16] at hvec
  rw [hptr2]
  have hEq1 :
      bufRef ↦₆₄ slot ∗
        (a + 72#64) ↦₆₄ 0#64 ∗
          (a + 80#64) ↦₆₄ 1#64 ∗
            (a + 88#64) ↦₆₄ 0#64 ∗
              (a + 96#64) ↦₃₂ 0#32 ∗
                memRegion (a + 100#64) 4 ∗
                  slot ↦₆₄ (ptr + 2#64) ∗
                    (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ tail).length ∗
                      ptr ↦₈ 26#8 ∗
                        (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length ∗
                          (ptr + 2#64) ↦ₛ (ck_body ++ tail) ∗
                            stackAt (sp0 - 256#64) chainMergeSubStack ∗ F =
      (((a + 0x48#64) ↦₆₄ 0#64) ∗ ((a + 0x50#64) ↦₆₄ 1#64) ∗ ((a + 0x58#64) ↦₆₄ 0#64)) ∗
        (bufRef ↦₆₄ slot ∗
          (a + 0x60#64) ↦₃₂ 0#32 ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
          (slot ↦₆₄ (ptr + 2#64) ∗
            (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ tail).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ tail)) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack ∗ F) := by ac_rfl
  have hEq2 :
      vecU8 A0 (a + 0x48#64) [] ∗
        (bufRef ↦₆₄ slot ∗
          (a + 0x60#64) ↦₃₂ 0#32 ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
          (slot ↦₆₄ (ptr + 2#64) ∗
            (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ tail).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ tail)) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack ∗ F) =
      (bufRef ↦₆₄ slot ∗
        vecU8 A0 (a + 0x48#64) [] ∗
        (a + 0x60#64) ↦₃₂ 0#32 ∗
        memRegion (a + 0x64#64) 4 ∗
        (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
        (slot ↦₆₄ (ptr + 2#64) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ tail).length ∗
          (ptr + 2#64) ↦ₛ (ck_body ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F := by ac_rfl
  rw [hEq1, ← hEq2]
  exact sepConj_mono_left hvec

/-! ## Inner Field `1`: `ChainKey.index` (`+0x4c8 → +0x4c8`) -/

theorem pbVarint1_pointsTo_combine_seedChain (ptr : BitVec 64) (n : Nat) (hn : n ≠ 0) :
    (ptr ↦₈ 0x08#8) ∗ ((ptr + 1#64) ↦ₛ pbVarintBody 5 n) =
      (ptr ↦ₛ pbVarint 1 n) := by
  have hpb : pbVarint 1 n = 0x08#8 :: pbVarintBody 5 n := by
    unfold pbVarint; simp [hn]; rfl
  rw [hpb, pointsToBytes_cons]

theorem pbVarint1_ptr_advance_seedChain (ptr : BitVec 64) (n : Nat) (hn : n ≠ 0) :
    ptr + 1#64 + BitVec.ofNat 64 (pbVarintBody 5 n).length =
      ptr + BitVec.ofNat 64 (pbVarint 1 n).length := by
  have hpb : pbVarint 1 n = 0x08#8 :: pbVarintBody 5 n := by
    unfold pbVarint; simp [hn]; rfl
  rw [hpb]
  simp only [List.length_cons]
  bv_omega

theorem step_chainMerge_seg3b_seedChain (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hIM : Prost.Int32MergeOk sessionImg0.base C A0 ctl abs)
    (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest tail : List (BitVec 8))
    (hlen_lt : (pbVarint 1 i.toNat ++ rest ++ tail).length < 2 ^ 32)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx23 : s0.readReg64 .x23 = BitVec.ofNat 64 tail.length)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x23 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R)) := by
  by_cases hi0 : i = 0#32
  · subst hi0
    have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    rw [hpb0] at hnext ⊢
    simp only [List.nil_append, List.length_nil,
      BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    refine SepWPp.mono_pre_seedChain ?_ (hnext s0 hpc hrun hsp hF hsym htr hvregs hx19 hx20 hx23 hx24)
    exact sep_ac_seedChain (by ac_rfl)
  · have hi_pos : i.toNat ≠ 0 := by
      intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    have hpb : pbVarint 1 i.toNat = 0x08#8 :: pbVarintBody 5 i.toNat := by
      unfold pbVarint; simp [hi_pos]; rfl
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest ++ tail)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest ++ tail) = 0x08#8 :: rem1 := by
      rw [hpb]; simp [rem1, List.cons_append]
    have hlen_gt : tail.length < (0x08#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 32 := by
      rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
    have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
    have hsub1 := len_cons_sub_one_seedChain 0x08#8 rem1
    refine (?_ :
      (∀ (s1 : State),
        s1.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName +
          bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) →
        s1.status = .Running →
        s1.sp = sp0 - 256#64 →
        sessionImg0.FrozenLoaded s1 →
        s1.symtab = sessionImg0.symtab →
        s1.trace = s_init.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s_init →
        s1.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x588#64 →
        (s1.readReg64 .x0).setWidth 8 = 0#8 →
        s1.readReg64 .x1 = a + 0x60#64 →
        s1.readReg64 .x2 = bufRef →
        s1.readReg64 .x19 = bufRef →
        s1.readReg64 .x20 = a →
        s1.readReg64 .x23 = BitVec.ofNat 64 tail.length →
        s1.readReg64 .x24 = BitVec.ofNat 64 tail.length →
        SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s1
          ((((a + 0x60#64) ↦₃₂ 0#32) ∗
            (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot (ptr + 1#64) rem1 ∗
            stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x08#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R))) → _) ?_
    · intro hnext1
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x4c8 0x4ec
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x530 0x554
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x578 0x584
      dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext1 ⊢
      generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
      have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
      have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 tail.length := hx23
      have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))) hF hsym ?_
      rw [hcons_eq]
      unfold sliceCursorAt
      rw [pointsToBytes_cons]
      simp only [sepConj_assoc]
      iterate 24 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm])
        (by simp only [hvregs, arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [h19, arm64_norm])
        (by simp only [h20, arm64_norm])
        (by simp only [h23, arm64_norm])
        (by simp only [h24, arm64_norm]))
      unfold sliceCursorAt
      exact sep_ac_seedChain (by ac_rfl)
    · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx23_1 hx24_1
      have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest ++ tail)).length < 2 ^ 32 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_int32Merge_seedChain C ctl hIM
        (a + 0x60#64) bufRef slot (ptr + 1#64) sp0
        ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x588#64)
        0#32 i (rest ++ tail) hrem1_lt
        hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
      intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x588 0x588
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x4c4 0x4c4
      dsimp only [tripleRatchetProgAt, chainMergeName] at hpc2 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1224)) hF2 hsym2 ?_
      iterate 2 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
      have h23_2 : s2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.1.trans hx23_1
      have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm])
        (by simp only [hvregs_2, arm64_norm])
        (by simp only [h19_2, arm64_norm])
        (by simp only [h20_2, arm64_norm])
        (by simp only [h23_2, arm64_norm])
        (by simp only [h24_2, arm64_norm]))
      rw [pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos,
        ← pbVarint1_pointsTo_combine_seedChain ptr i.toNat hi_pos]
      exact sep_ac_seedChain (by ac_rfl)

/-! ## Inner Field `2`: `ChainKey.key` (`+0x4c8 → +0x4c8`) -/

theorem step_chainMerge_seg3c_seedChain (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hBM : Prost.BytesMergeOk sessionImg0 C A0 ctl abs)
    (a bufRef slot ptr sp0 : BitVec 64)
    (k tail : List (BitVec 8))
    (hk_lt : k.length < 128)
    (hlen_lt : (pbBytes 2 k ++ tail).length < 2 ^ 32)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx23 : s0.readReg64 .x23 = BitVec.ofNat 64 tail.length)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x23 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) k ∗
          (ptr ↦ₛ pbBytes 2 k) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 k).length) tail ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 k ++ tail) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R)) := by
  have hpb : pbBytes 2 k = 0x12#8 :: BitVec.ofNat 8 k.length :: k :=
    pbBytes_lt128_eq_seedChain 2 (by decide) k hk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 k.length] ++ k ++ tail
  have hcons_eq : pbBytes 2 k ++ tail = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 32 := by
    rw [← hcons_eq]; exact hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x12#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) →
      s1.status = .Running →
      s1.sp = sp0 - 256#64 →
      sessionImg0.FrozenLoaded s1 →
      s1.symtab = sessionImg0.symtab →
      s1.trace = s_init.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x570#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a + 0x48#64 →
      s1.readReg64 .x2 = bufRef →
      s1.readReg64 .x19 = bufRef →
      s1.readReg64 .x20 = a →
      s1.readReg64 .x23 = BitVec.ofNat 64 tail.length →
      s1.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s1
        ((vecU8 A0 (a + 0x48#64) [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x12#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R))) → _) ?_
  · intro hnext1
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x4c8 0x4ec
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x530 0x56c
    dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext1 ⊢
    generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 tail.length := hx23
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))) hF hsym ?_
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    simp only [sepConj_assoc]
    iterate 26 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm])
      (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [h19, arm64_norm])
      (by simp only [h20, arm64_norm])
      (by simp only [h23, arm64_norm])
      (by simp only [h24, arm64_norm]))
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx23_1 hx24_1
    have hrem1_lt : ([BitVec.ofNat 8 k.length] ++ k ++ tail).length < 2 ^ 32 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_seedChain C ctl hBM
      (a + 0x48#64) bufRef slot (ptr + 1#64) sp0
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x570#64)
      [] k tail hk_lt hrem1_lt
      hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x570 0x570
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x4c4 0x4c4
    dsimp only [tripleRatchetProgAt, chainMergeName] at hpc2 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1224)) hF2 hsym2 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
    have h23_2 : s2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.1.trans hx23_1
    have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
    have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm])
      (by simp only [hvregs_2, arm64_norm])
      (by simp only [h19_2, arm64_norm])
      (by simp only [h20_2, arm64_norm])
      (by simp only [h23_2, arm64_norm])
      (by simp only [h24_2, arm64_norm]))
    rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr k hk_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr k hk_lt]
    exact sep_ac_seedChain (by ac_rfl)

/-! ## Loop Exits and Epilogue (`+0x4c8 → ret`) -/

theorem step_chainMerge_seg3d_seedChain (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (bufRef slot ptr sp0 : BitVec 64)
    (tail : List (BitVec 8))
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x4c8#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hlr_init : s_init.readReg64 .lr = ret)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx23 : s0.readReg64 .x23 = BitVec.ofNat 64 tail.length)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = ret →
      sm.status = .Running →
      sm.sp = sp0 →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s_init.trace →
      sm.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s_init sm →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr tail ∗
          stackAt sp0 chainMergeStack) ∗ F)
        Q Qp) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr tail ∗
        stackAt (sp0 - 256#64) chainMergeSubStack ∗
        chainMergeSavedRegs sp0 s_init) ∗ F)
      Q Qp := by
  have hsp_sub_align : s0.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp_sub_256_aligned_seedChain halign
  have hsp_restore : sp0 - 256#64 + 256#64 = sp0 := BitVec.sub_add_cancel sp0 256#64
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x4c8 0x4d4
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x5a8 0x5b0
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x120 0x12c
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x674 0x67c
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x0f0 0x10c
  dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 tail.length := hx23
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
  have h30_init : s_init.readReg64 (Reg.gpr 30#5) = ret := hlr_init
  refine SepWPp.of_sepWP_frozen_seedChain (mid := ret) hF hsym ?_
  unfold sliceCursorAt chainMergeSavedRegs
  simp only [sepConj_assoc]
  iterate 22 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm])
    hF1 hsym1 (by simp only [htr, arm64_norm])
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [hvregs, arm64_norm]⟩)
  rw [stackAt_chainMergeStack_split_seedChain sp0]
  unfold sliceCursorAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.trans ?_
    (Entails.sepExists_right (s_init.readReg64 .x29)
      (Entails.sepExists_right (s_init.readReg64 .x30)
        (Entails.sepExists_right (s_init.readReg64 .x28)
          (Entails.sepExists_right (s_init.readReg64 .x27)
            (Entails.sepExists_right (s_init.readReg64 .x26)
              (Entails.sepExists_right (s_init.readReg64 .x25)
                (Entails.sepExists_right (s_init.readReg64 .x24)
                  (Entails.sepExists_right (s_init.readReg64 .x23)
                    (Entails.sepExists_right (s_init.readReg64 .x22)
                      (Entails.sepExists_right (s_init.readReg64 .x21)
                        (Entails.sepExists_right (s_init.readReg64 .x20)
                          (Entails.sepExists_right (s_init.readReg64 .x19)
                            (Entails.refl _)))))))))))))
  exact sep_ac_seedChain (by ac_rfl)

/-! ## Relocatable `[LibsignalPlacement]` Segments (`lsProg_11 H`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem step_chainMerge_seg3a_placed_seedChain [LibsignalPlacement]
    {H : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body tail : List (BitVec 8))
    (hck_lt : ck_body.length < 128)
    (hlen_lt : (2 + (ck_body.length + tail.length)) < 2 ^ 32)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hx26 : s0.readReg64 .x26 = 1#64)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x4c8#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x23 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q Qp := by
  have hlen_gt : tail.length < (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail)).length < 2 ^ 32 := by
    simp only [List.length_cons, List.length_append]; omega
  have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x1a#8 (BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail))
  have hrem1_lt : (BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail)).length < 2 ^ 32 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz2 := cbz_len_cons_false_seedChain (b0 := BitVec.ofNat 8 ck_body.length)
    (bs1 := ck_body ++ tail) hrem1_lt
  have hse0 := signExtend64_ofNat8_lt128_seedChain hck_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hck_lt
  have hsub2 := len_cons_sub_one_seedChain (BitVec.ofNat 8 ck_body.length) (ck_body ++ tail)
  have hlen_ck_append : (ck_body ++ tail).length = ck_body.length + tail.length := List.length_append
  have hule_ck_sub := ule_ofNat_add_right_true_seedChain (m := ck_body.length) (k := tail.length) (by omega)
  have hsub_ck_tail := bv_ofNat_add_sub_left_seedChain ck_body.length tail.length
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
  have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := (blkPl_11).base + 0x4c8#64) hcrl ?_
  rw [memRegion24_split_ck_seedChain a]
  unfold sliceCursorAt noneCap
  rw [pointsToBytes_cons, pointsToBytes_cons]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w50
  apply SepWP.exists_elim; intro w58
  apply SepWP.exists_elim; intro w60
  iterate 44 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcrl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) hcrl1 (by simp only [htr, arm64_norm])
    (by simp only [hvregs, arm64_norm])
    (by simp only [h19, arm64_norm])
    (by simp only [h20, arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [h24, arm64_norm]))
  unfold sliceCursorAt
  rw [← hlen_ck_append, ← ck_hdr_pointsTo_combine_seedChain ptr ck_body.length]
  have hvec := emptyVec_entails_vecU8_seedChain (a + 0x48#64)
  have h48_8 : (a + 0x48#64) + 8#64 = a + 0x50#64 := by bv_omega
  have h48_16 : (a + 0x48#64) + 16#64 = a + 0x58#64 := by bv_omega
  have hptr2 : ptr + 1#64 + 1#64 = ptr + 2#64 := by bv_omega
  rw [h48_8, h48_16] at hvec
  rw [hptr2]
  have hEq1 :
      bufRef ↦₆₄ slot ∗
        (a + 72#64) ↦₆₄ 0#64 ∗
          (a + 80#64) ↦₆₄ 1#64 ∗
            (a + 88#64) ↦₆₄ 0#64 ∗
              (a + 96#64) ↦₃₂ 0#32 ∗
                memRegion (a + 100#64) 4 ∗
                  slot ↦₆₄ (ptr + 2#64) ∗
                    (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ tail).length ∗
                      ptr ↦₈ 26#8 ∗
                        (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length ∗
                          (ptr + 2#64) ↦ₛ (ck_body ++ tail) ∗
                            stackAt (sp0 - 256#64) chainMergeSubStack ∗ F =
      (((a + 0x48#64) ↦₆₄ 0#64) ∗ ((a + 0x50#64) ↦₆₄ 1#64) ∗ ((a + 0x58#64) ↦₆₄ 0#64)) ∗
        (bufRef ↦₆₄ slot ∗
          (a + 0x60#64) ↦₃₂ 0#32 ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
          (slot ↦₆₄ (ptr + 2#64) ∗
            (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ tail).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ tail)) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack ∗ F) := by ac_rfl
  have hEq2 :
      vecU8 A0 (a + 0x48#64) [] ∗
        (bufRef ↦₆₄ slot ∗
          (a + 0x60#64) ↦₃₂ 0#32 ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
          (slot ↦₆₄ (ptr + 2#64) ∗
            (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ tail).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ tail)) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack ∗ F) =
      (bufRef ↦₆₄ slot ∗
        vecU8 A0 (a + 0x48#64) [] ∗
        (a + 0x60#64) ↦₃₂ 0#32 ∗
        memRegion (a + 0x64#64) 4 ∗
        (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
        (slot ↦₆₄ (ptr + 2#64) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ tail).length ∗
          (ptr + 2#64) ↦ₛ (ck_body ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F := by ac_rfl
  rw [hEq1, ← hEq2]
  exact sepConj_mono_left hvec

theorem step_chainMerge_seg3b_placed_seedChain [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hIM : subroutine_ok ((blkPC_8).rebase (blkPl_8).base H) (blkPl_8).base
      (withLsCodeLoaded lsmpl (Prost.int32MergeSpec A0)))
    (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest tail : List (BitVec 8))
    (hlen_lt : (pbVarint 1 i.toNat ++ rest ++ tail).length < 2 ^ 32)
    {α : Type} {x : α} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x4c8#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx23 : s0.readReg64 .x23 = BitVec.ofNat 64 tail.length)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x4c8#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x23 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R)) := by
  by_cases hi0 : i = 0#32
  · subst hi0
    have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    rw [hpb0] at hnext ⊢
    simp only [List.nil_append, List.length_nil,
      BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    refine SepWPp.mono_pre_seedChain ?_ (hnext s0 hpc hrun hsp hcrl htr hvregs hx19 hx20 hx23 hx24)
    exact sep_ac_seedChain (by ac_rfl)
  · have hi_pos : i.toNat ≠ 0 := by
      intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    have hpb : pbVarint 1 i.toNat = 0x08#8 :: pbVarintBody 5 i.toNat := by
      unfold pbVarint; simp [hi_pos]; rfl
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest ++ tail)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest ++ tail) = 0x08#8 :: rem1 := by
      rw [hpb]; simp [rem1, List.cons_append]
    have hlen_gt : tail.length < (0x08#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 32 := by
      rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
    have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
    have hsub1 := len_cons_sub_one_seedChain 0x08#8 rem1
    refine (?_ :
      (∀ (s1 : State),
        s1.pc = lsmpl.base 8 →
        s1.status = .Running →
        s1.sp = sp0 - 256#64 →
        LibsignalCodeRoLoaded lsmpl s1.mem →
        s1.trace = s_init.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s_init →
        s1.readReg64 .lr = (blkPl_11).base + 0x588#64 →
        (s1.readReg64 .x0).setWidth 8 = 0#8 →
        s1.readReg64 .x1 = a + 0x60#64 →
        s1.readReg64 .x2 = bufRef →
        s1.readReg64 .x19 = bufRef →
        s1.readReg64 .x20 = a →
        s1.readReg64 .x23 = BitVec.ofNat 64 tail.length →
        s1.readReg64 .x24 = BitVec.ofNat 64 tail.length →
        SepWPp (lsProg_11 H) ret s1
          ((((a + 0x60#64) ↦₃₂ 0#32) ∗
            (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot (ptr + 1#64) rem1 ∗
            stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x08#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R))) → _) ?_
    · intro hnext1
      have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
      have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
      have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 tail.length := hx23
      have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
      refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 8) hcrl ?_
      rw [hcons_eq]
      unfold sliceCursorAt
      rw [pointsToBytes_cons]
      simp only [sepConj_assoc]
      iterate 24 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hcrl1
      refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        (by simp only [hsp, arm64_norm]) hcrl1 (by simp only [htr, arm64_norm])
        (by simp only [hvregs, arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [h19, arm64_norm])
        (by simp only [h20, arm64_norm])
        (by simp only [h23, arm64_norm])
        (by simp only [h24, arm64_norm]))
      unfold sliceCursorAt
      exact sep_ac_seedChain (by ac_rfl)
    · intro s1 hpc1 hrun1 hsp1 hcrl1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx23_1 hx24_1
      have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest ++ tail)).length < 2 ^ 32 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_int32Merge_placed_seedChain hIM
        (a + 0x60#64) bufRef slot (ptr + 1#64) sp0
        ((blkPl_11).base + 0x588#64)
        0#32 i (rest ++ tail) hrem1_lt
        hpc1 hrun1 hsp1 halign hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
      intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hcs2 hx0_2
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := (blkPl_11).base + 0x4c8#64) hcrl2 ?_
      iterate 2 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
      intro hcrl3
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
      have h23_2 : s2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.1.trans hx23_1
      have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        (by simp only [hsp2, arm64_norm]) hcrl3 (by simp only [htr2, arm64_norm])
        (by simp only [hvregs_2, arm64_norm])
        (by simp only [h19_2, arm64_norm])
        (by simp only [h20_2, arm64_norm])
        (by simp only [h23_2, arm64_norm])
        (by simp only [h24_2, arm64_norm]))
      rw [pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos,
        ← pbVarint1_pointsTo_combine_seedChain ptr i.toNat hi_pos]
      exact sep_ac_seedChain (by ac_rfl)

theorem step_chainMerge_seg3c_placed_seedChain [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hBM : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.bytesMergeRawSpec A0)))
    (a bufRef slot ptr sp0 : BitVec 64)
    (k tail : List (BitVec 8))
    (hk_lt : k.length < 128)
    (hlen_lt : (pbBytes 2 k ++ tail).length < 2 ^ 32)
    {α : Type} {x : α} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x4c8#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx23 : s0.readReg64 .x23 = BitVec.ofNat 64 tail.length)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x4c8#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x23 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) k ∗
          (ptr ↦ₛ pbBytes 2 k) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 k).length) tail ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 k ++ tail) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R)) := by
  have hpb : pbBytes 2 k = 0x12#8 :: BitVec.ofNat 8 k.length :: k :=
    pbBytes_lt128_eq_seedChain 2 (by decide) k hk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 k.length] ++ k ++ tail
  have hcons_eq : pbBytes 2 k ++ tail = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 32 := by
    rw [← hcons_eq]; exact hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x12#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = lsmpl.base 7 →
      s1.status = .Running →
      s1.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s_init.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = (blkPl_11).base + 0x570#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a + 0x48#64 →
      s1.readReg64 .x2 = bufRef →
      s1.readReg64 .x19 = bufRef →
      s1.readReg64 .x20 = a →
      s1.readReg64 .x23 = BitVec.ofNat 64 tail.length →
      s1.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      SepWPp (lsProg_11 H) ret s1
        ((vecU8 A0 (a + 0x48#64) [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x12#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R))) → _) ?_
  · intro hnext1
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 tail.length := hx23
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl ?_
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    simp only [sepConj_assoc]
    iterate 26 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcrl1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) hcrl1 (by simp only [htr, arm64_norm])
      (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [h19, arm64_norm])
      (by simp only [h20, arm64_norm])
      (by simp only [h23, arm64_norm])
      (by simp only [h24, arm64_norm]))
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hcrl1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx23_1 hx24_1
    have hrem1_lt : ([BitVec.ofNat 8 k.length] ++ k ++ tail).length < 2 ^ 32 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_placed_seedChain hBM
      (a + 0x48#64) bufRef slot (ptr + 1#64) sp0
      ((blkPl_11).base + 0x570#64)
      [] k tail hk_lt hrem1_lt
      hpc1 hrun1 hsp1 halign hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hcs2 hx0_2
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := (blkPl_11).base + 0x4c8#64) hcrl2 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcrl3
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
    have h23_2 : s2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.1.trans hx23_1
    have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
    have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hcrl3 (by simp only [htr2, arm64_norm])
      (by simp only [hvregs_2, arm64_norm])
      (by simp only [h19_2, arm64_norm])
      (by simp only [h20_2, arm64_norm])
      (by simp only [h23_2, arm64_norm])
      (by simp only [h24_2, arm64_norm]))
    rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr k hk_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr k hk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_chainMerge_seg3d_placed_seedChain [LibsignalPlacement]
    {H : String → Option (State → State)}
    (bufRef slot ptr sp0 : BitVec 64)
    (tail : List (BitVec 8))
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x4c8#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hlr_init : s_init.readReg64 .lr = ret)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx23 : s0.readReg64 .x23 = BitVec.ofNat 64 tail.length)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = ret →
      sm.status = .Running →
      sm.sp = sp0 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      sm.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s_init sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr tail ∗
          stackAt sp0 chainMergeStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr tail ∗
        stackAt (sp0 - 256#64) chainMergeSubStack ∗
        chainMergeSavedRegs sp0 s_init) ∗ F)
      Q Qp := by
  have hsp_sub_align : s0.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp_sub_256_aligned_seedChain halign
  have hsp_restore : sp0 - 256#64 + 256#64 = sp0 := BitVec.sub_add_cancel sp0 256#64
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 tail.length := hx23
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
  have h30_init : s_init.readReg64 (Reg.gpr 30#5) = ret := hlr_init
  refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := ret) hcrl ?_
  unfold sliceCursorAt chainMergeSavedRegs
  simp only [sepConj_assoc]
  iterate 22 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcrl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm])
    hcrl1 (by simp only [htr, arm64_norm])
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [hvregs, arm64_norm]⟩)
  rw [stackAt_chainMergeStack_split_seedChain sp0]
  unfold sliceCursorAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.trans ?_
    (Entails.sepExists_right (s_init.readReg64 .x29)
      (Entails.sepExists_right (s_init.readReg64 .x30)
        (Entails.sepExists_right (s_init.readReg64 .x28)
          (Entails.sepExists_right (s_init.readReg64 .x27)
            (Entails.sepExists_right (s_init.readReg64 .x26)
              (Entails.sepExists_right (s_init.readReg64 .x25)
                (Entails.sepExists_right (s_init.readReg64 .x24)
                  (Entails.sepExists_right (s_init.readReg64 .x23)
                    (Entails.sepExists_right (s_init.readReg64 .x22)
                      (Entails.sepExists_right (s_init.readReg64 .x21)
                        (Entails.sepExists_right (s_init.readReg64 .x20)
                          (Entails.sepExists_right (s_init.readReg64 .x19)
                            (Entails.refl _)))))))))))))
  exact sep_ac_seedChain (by ac_rfl)

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed

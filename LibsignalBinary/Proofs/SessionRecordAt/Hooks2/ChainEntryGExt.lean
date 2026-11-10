/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
/-!
# `message::merge<Chain>` Entry Leaf Proof (`chainEntryG_ok`)

Proves the entry segment (`+0x000 → +0x120`, covering both single-byte `< 128` and multi-byte
`decode_varint_slice` length prefixes) of `prost::encoding::message::merge<Chain>`, including
X-stack (`_atW`, `_atWA`) and relocatable `[LibsignalPlacement]` (`lsProg_11 H`, Block `11`)
variants.
-/

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace ChainMergeStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre_seedChain (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre_seedChain (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre_seedChain (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre_seedChain (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl
@[local simp, local arm64_norm]
theorem getLsbD_63_eq_seedChain (v : BitVec 64) :
    v.getLsbD 63 = !(v >>> 56).ult 128#64 := by
  bv_robdd
end ChainMergeStateSimp
open ChainMergeStateSimp

attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

theorem w0_and_255_eq_two_seedChain {w : BitVec 64} (h : w.setWidth 8 = 2#8) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 w) &&& 255#64 = 2#64 := by
  apply BitVec.eq_of_toNat_eq
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
    BitVec.toNat_and, BitVec.toNat_ofNat] at h' ⊢
  rw [show 255 % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem signExtend64_ofNat8_lt128_seedChain {n : Nat} (hn : n < 128) :
    BitVec.signExtend 64 (BitVec.ofNat 8 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_eq_toNat_cond,
    BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat64_lsr56_eq_zero_seedChain {n : Nat} (hn : n < 128) :
    BitVec.ofNat 64 n >>> 56 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  change (n % 2 ^ 64) / 2 ^ 56 = 0
  omega

theorem cbz_len_cons_false_seedChain {b0 : BitVec 8} {bs1 : List (BitVec 8)}
    (hlen : (b0 :: bs1).length < 2 ^ 32) :
    (BitVec.ofNat 64 (b0 :: bs1).length == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  simp at h1

theorem len_cons_sub_one_seedChain (b0 : BitVec 8) (bs1 : List (BitVec 8)) :
    BitVec.ofNat 64 (b0 :: bs1).length - 1#64 = BitVec.ofNat 64 bs1.length := by
  change BitVec.ofNat 64 (bs1.length + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 bs1.length
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem bv_ofNat_add_sub_left_seedChain (m k : Nat) :
    BitVec.ofNat 64 (m + k) - BitVec.ofNat 64 m = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add, BitVec.add_comm, BitVec.add_sub_cancel]

theorem ule_ofNat_add_right_true_seedChain {m k : Nat} (hlt : m + k < 2 ^ 32) :
    (BitVec.ofNat 64 m).ule (BitVec.ofNat 64 (m + k)) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_true_eq]
  omega

theorem ult_ofNat_add_left_false_seedChain {m k : Nat} (hlt : m + k < 2 ^ 32) :
    (BitVec.ofNat 64 (m + k)).ult (BitVec.ofNat 64 m) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_false_iff_not]
  omega


/-! ## 1. Callee offset, stack & frame splitting, and varint helpers -/

private theorem signExtend64_lsr56_of_gt_0x7f_cme (b0 : BitVec 8) (h : 0x7F < b0.toNat) :
    (b0.signExtend 64) >>> 56 = 0xff#64 := by
  revert b0 h; decide

private theorem allocFailedIn_of_trace_eq_cme {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rwa [htr] at h

private theorem allowPanic_frame_trace_cme {s0 sm sf : State} {F R : SepProp}
    (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eq_cme htr) h



/-! ## 2. Main entry theorem `chainEntryG_ok_impl` -/

private theorem chainG_enc_eq_fields_cme (c : ChainG) :
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
      List.flatMap ChainField.enc (match ck with | some (i, k) => [ChainField.ck i k] | none => []) := by
    cases ck <;> simp [msgField, ChainField.enc]
  have h4 : (List.map (fun m => lenField 4 (encMessageKey m)) keys).flatten =
      List.flatMap (fun a => (ChainField.key a).enc) keys := by
    rw [← List.flatMap_def]; rfl
  rw [h1, h2, h3, h4]; rfl

/-! ## 3. `_atW` versions on `SP2Ext img.base ext` (X-Stack) -/

abbrev decodeVarintSlice_ok_sub_cme_extW := @Proofs.libsignal.Hooks2.decodeVarintSlice_ok_sub_cme_extW

theorem step_chainMerge_seg0_1byte_cme_extW {img : Obj.Image}
    {ext : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (body tail : List (BitVec 8))
    (hbody_lt : body.length < 128) (hlen_lt : (1 + (body.length + tail.length)) < 2 ^ 62)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8) (hx1 : s0.readReg64 .x1 = a)
    (hx2 : s0.readReg64 .x2 = bufRef) (hx3 : (s0.readReg64 .x3).setWidth 32 = 99#32)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x29 = sp0 - 96#64 → sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x21 = 98#64 → sm.readReg64 .x22 = 97#64 →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      ∀ Pm, (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (ptr ↦₈ BitVec.ofNat 8 body.length) ∗
        sliceCursorAt slot (ptr + 1#64) (body ++ tail) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs sp0 s0) → post sm Pm) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64) s0
      ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (BitVec.ofNat 8 body.length :: (body ++ tail)) ∗
        stackAt sp0 chainMergeStackX) post := by
  subst hsp
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x0 0x11c
  dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h1 : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = bufRef := hx2
  have hw3 : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 3#5)) = 99#32 := hx3
  have hw0 : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64 = 2#64 :=
    w0_and_255_eq_two_seedChain hx0
  have hlen_cons : (BitVec.ofNat 8 body.length :: (body ++ tail)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz := cbz_len_cons_false_seedChain62 hlen_cons
  have hse0 := signExtend64_ofNat8_lt128_seedChain hbody_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hbody_lt
  have hsub_len := len_cons_sub_one_seedChain (BitVec.ofNat 8 body.length) (body ++ tail)
  have hlen_append : (body ++ tail).length = body.length + tail.length := List.length_append
  have hule_sub := ule_ofNat_add_right_true_seedChain62 (m := body.length) (k := tail.length) (by omega)
  have hsub_tail := bv_ofNat_add_sub_left_seedChain body.length tail.length
  rw [stackAt_chainMergeStackX_split_seedChain s0.sp]
  unfold sliceCursorAt
  rw [pointsToBytes_cons]
  simp only [sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w96; apply SepWP.exists_elim; intro w88
  apply SepWP.exists_elim; intro w80; apply SepWP.exists_elim; intro w72
  apply SepWP.exists_elim; intro w64; apply SepWP.exists_elim; intro w56
  apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
  apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
  apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
  iterate 31 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) _ (by
      unfold sliceCursorAt chainMergeSavedRegs; rw [← hlen_append]; exact sep_ac_seedChain (by ac_rfl))

theorem step_chainMerge_seg0_ge128_pre_cme_extW {img : Obj.Image}
    {ext : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (n : Nat) (rest0 : List (BitVec 8))
    (hgt10 : 10 < (BitVec.ofNat 8 (n % 128 + 128) :: rest0).length)
    (hlen_lt : (BitVec.ofNat 8 (n % 128 + 128) :: rest0).length < 2 ^ 62)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8) (hx1 : s0.readReg64 .x1 = a)
    (hx2 : s0.readReg64 .x2 = bufRef) (hx3 : (s0.readReg64 .x3).setWidth 32 = 99#32)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMergeName + 0x9c#64 →
      sm.readReg64 .x0 = sp0 - 248#64 → sm.readReg64 .x1 = ptr →
      sm.readReg64 .x2 = BitVec.ofNat 64 (BitVec.ofNat 8 (n % 128 + 128) :: rest0).length →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = slot → sm.readReg64 .x22 = 99#64 →
      sm.readReg64 .x29 = sp0 - 96#64 →
      ∀ Pm, (Pm ⊢ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (BitVec.ofNat 8 (n % 128 + 128) :: rest0) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs sp0 s0) → post sm Pm) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr chainMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) s0
      ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (BitVec.ofNat 8 (n % 128 + 128) :: rest0) ∗
        stackAt sp0 chainMergeStackX) post := by
  subst hsp
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x0 0x48
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x7c 0x98
  dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h1 : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = bufRef := hx2
  have hw3 : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 3#5)) = 99#32 := hx3
  have hw0 : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64 = 2#64 :=
    w0_and_255_eq_two_seedChain hx0
  have hcbz := cbz_len_cons_false_seedChain62 hlen_lt
  have hlsr56 := signExtend64_contByte_lsr56_cme n
  have hhi10 := ult_10_of_gt_cme62 hgt10 hlen_lt
  have hule10 := ule_10_of_gt_false_cme62 hgt10 hlen_lt
  rw [stackAt_chainMergeStackX_split_seedChain s0.sp]
  unfold sliceCursorAt
  rw [pointsToBytes_cons]
  simp only [sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w96; apply SepWP.exists_elim; intro w88
  apply SepWP.exists_elim; intro w80; apply SepWP.exists_elim; intro w72
  apply SepWP.exists_elim; intro w64; apply SepWP.exists_elim; intro w56
  apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
  apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
  apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
  iterate 24 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) _ (by
      unfold sliceCursorAt chainMergeSavedRegs
      rw [pointsToBytes_cons]
      exact sep_ac_seedChain (by ac_rfl))

theorem step_chainMerge_seg0_ge128_post_cme_extW {img : Obj.Image}
    {ext : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (vlen : Nat) (body tail : List (BitVec 8))
    (hlen_lt : (vlen + (body.length + tail.length)) < 2 ^ 62)
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x9c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64) (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = bufRef) (hx20 : s.readReg64 .x20 = a) (hx21 : s.readReg64 .x21 = slot)
    (hx22 : s.readReg64 .x22 = 99#64) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.trace = s.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x29 = sp0 - 96#64 → sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x21 = 98#64 → sm.readReg64 .x22 = 97#64 →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      ∀ Pm, (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length) ∗ memRegion (sp0 - 248#64) 24) →
      post sm Pm) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64) s
      ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (vlen + (body.length + tail.length))) ∗
        ((sp0 - 248#64) ↦₃₂ 0#32) ∗ ((sp0 - 244#64) ↦₃₂ 0#32) ∗
        ((sp0 - 240#64) ↦₆₄ BitVec.ofNat 64 body.length) ∗ ((sp0 - 232#64) ↦₆₄ BitVec.ofNat 64 vlen))
      post := by
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact sp_sub_256_aligned_seedChain hsp_align
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x9c 0xa0
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0xac 0xdc
  chainMerge_fetches_range img.base (Rust.withPanics ext) 0x110 0x11c
  dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = slot := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 99#64 := hx22
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  have hlen_append : (body ++ tail).length = body.length + tail.length := List.length_append
  have hsub_vlen := bv_ofNat_add_sub_left_seedChain vlen (body.length + tail.length)
  have hult_vlen := ult_ofNat_add_left_false_seedChain62 (m := vlen) (k := body.length + tail.length) hlen_lt
  have hule_vlen := ule_ofNat_add_right_true_seedChain62 (m := vlen) (k := body.length + tail.length) hlen_lt
  have hsub_tail := bv_ofNat_add_sub_left_seedChain body.length tail.length
  have hbody_tail_lt : body.length + tail.length < 2 ^ 62 := by omega
  have hule_sub := ule_ofNat_add_right_true_seedChain62 (m := body.length) (k := tail.length) hbody_tail_lt
  have hult_sub := ult_ofNat_add_left_false_seedChain62 (m := body.length) (k := tail.length) hbody_tail_lt
  iterate 19 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [h29, arm64_norm]) (by simp only [h19, arm64_norm])
    (by simp only [h20, arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) _ ?_
  have hcells := cells24_entails_memRegion24_cme sp0 (BitVec.ofNat 64 body.length) (BitVec.ofNat 64 vlen)
  rw [← hlen_append]
  have hEq1 : bufRef ↦₆₄ slot ∗ slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length) ∗
      ((sp0 - 248#64) ↦₃₂ 0#32) ∗ ((sp0 - 244#64) ↦₃₂ 0#32) ∗
      ((sp0 - 240#64) ↦₆₄ BitVec.ofNat 64 body.length) ∗ ((sp0 - 232#64) ↦₆₄ BitVec.ofNat 64 vlen) =
    (((sp0 - 248#64) ↦₃₂ 0#32) ∗ ((sp0 - 244#64) ↦₃₂ 0#32) ∗
      ((sp0 - 240#64) ↦₆₄ BitVec.ofNat 64 body.length) ∗ ((sp0 - 232#64) ↦₆₄ BitVec.ofNat 64 vlen)) ∗
    ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length)) := by ac_rfl
  have hEq2 : memRegion (sp0 - 248#64) 24 ∗ ((bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length)) =
    (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length) ∗ memRegion (sp0 - 248#64) 24 := by ac_rfl
  rw [hEq1, ← hEq2]; exact sepConj_mono_left hcells

theorem chainEntryG_ok_impl_atW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hC : DeserializeCalleesAtW img ext) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (chainMergeGenSpecAtW img).pre x s0 ∗ R) (hal : s0.spAligned = true) :
    ChainStepGAtW img ext x R s0 s0 (ChainLoopGAtW img ext x R s0 0) := by
  intro hL0
  rcases x with ⟨a, c, bufRef, slot, ptr, tail⟩
  dsimp only [chainMergeGenSpecAtW] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hcOk, hlen_lt, hF0, hsym0⟩, hmem⟩
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
  have hsp_sub_align : (s0.sp - 256#64) &&& 15#64 = 0#64 := sp_sub_256_aligned_seedChain hsp_align
  have hdrop0 : ((c.fields.drop 0).flatMap ChainField.enc) = c.enc := by rw [List.drop_zero, ← chainG_enc_eq_fields_cme c]
  have hchain0 : chainGAfter c 0 = ChainG.empty := rfl
  by_cases hbody_lt : c.enc.length < 128
  · have hvar : encodeVarint (BitVec.ofNat 64 c.enc.length) = [BitVec.ofNat 8 c.enc.length] :=
      encodeVarint_lt128_seedChain c.enc.length hbody_lt
    have hpay : c.payload ++ tail = BitVec.ofNat 8 c.enc.length :: (c.enc ++ tail) := by
      unfold ChainG.payload; rw [hvar, List.singleton_append, List.cons_append]
    have hlen_lt1 : (1 + (c.enc.length + tail.length)) < 2 ^ 62 := by
      rw [hpay, List.length_cons, List.length_append] at hlen_lt; omega
    have hmem1 : s0.mem ⊨
        ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (BitVec.ofNat 8 c.enc.length :: (c.enc ++ tail)) ∗ stackAt s0.sp chainMergeStackX) ∗
        (prostChainGAt A0 a ChainG.empty ∗ R) := by rw [← hpay]; convert hmem using 1; ac_rfl
    obtain ⟨sm, hst, ⟨hpcm, hrunm, Pm, hmm, hspm, htrm, hvregsm, hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m, hent⟩ | ⟨_, _hoom⟩⟩ :=
      (step_chainMerge_seg0_1byte_cme_extW (img := img) (ext := ext) a bufRef slot ptr s0.sp c.enc tail
        (post := fun sm Pm =>
          sm.sp = s0.sp - 256#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧ sm.readReg64 .x24 = BitVec.ofNat 64 tail.length ∧
          sm.readReg64 .x21 = 98#64 ∧ sm.readReg64 .x22 = 97#64 ∧ sm.readReg64 .x25 = s0.sp - 248#64 ∧ sm.readReg64 .x26 = 1#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (ptr ↦₈ BitVec.ofNat 8 c.enc.length) ∗
            sliceCursorAt slot (ptr + 1#64) (c.enc ++ tail) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0))
        hbody_lt hlen_lt1 hpc hrun rfl hsp_align hx0 hx1 hx2 hx3
        (fun _ _ _ hsp' htr' hvregs' hx29' hx19' hx20' hx24' hx21' hx22' hx25' hx26' _ hent =>
          ⟨hsp', htr', hvregs', hx29', hx19', hx20', hx24', hx21', hx22', hx25', hx26', hent⟩)).elim hmem1 hL0
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hmm' := Satisfies.mono (sepConj_mono_left hent) hmm
    refine ⟨sm, hst, Or.inl ⟨hpcm, hrunm, htrm, hvregsm, hst.symtab_eq.trans hsym0, hst.frozenLoaded hF0,
      hspm, by simp only [State.spAligned, hspm, beq_iff_eq]; exact hsp_sub_align,
      hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m, hcOk, hlen_lt, ?_⟩⟩
    rw [hchain0, hdrop0, hpay]
    have hcur := sliceCursorAfter_append_eq_seedChain slot ptr [BitVec.ofNat 8 c.enc.length] (c.enc ++ tail)
    rw [List.singleton_append] at hcur; rw [hcur]
    simp only [List.length_singleton, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    convert hmm' using 1; ac_rfl
  · have hbody_ge : 128 ≤ c.enc.length := by omega
    have hbody_lt62 : c.enc.length < 2 ^ 62 := by
      unfold ChainG.payload at hlen_lt; simp only [List.length_append] at hlen_lt; omega
    obtain ⟨vtail, hvar⟩ := encodeVarint_ge128_cons_cme62 hbody_ge hbody_lt62
    let b0 := BitVec.ofNat 8 (c.enc.length % 128 + 128)
    let rest0 := vtail ++ (c.enc ++ tail)
    have hpay : c.payload ++ tail = b0 :: rest0 := by
      unfold ChainG.payload; dsimp only [b0, rest0]
      rw [hvar, List.cons_append, List.cons_append, List.append_assoc]
    have hgt10 : 10 < (b0 :: rest0).length := by
      rw [← hpay]; unfold ChainG.payload; simp only [List.length_append]; omega
    have hlen_lt0 : (b0 :: rest0).length < 2 ^ 62 := by rw [← hpay]; exact hlen_lt
    have hmem1 : s0.mem ⊨
        ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rest0) ∗ stackAt s0.sp chainMergeStackX) ∗
        (prostChainGAt A0 a ChainG.empty ∗ R) := by rw [← hpay]; convert hmem using 1; ac_rfl
    obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, hsp1, htr1, hvregs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1, hx29_1, hent1⟩ | ⟨_, _hoom⟩⟩ :=
      (step_chainMerge_seg0_ge128_pre_cme_extW (img := img) (ext := ext) a bufRef slot ptr s0.sp c.enc.length rest0
        (post := fun sm Pm =>
          sm.sp = s0.sp - 256#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMergeName + 0x9c#64 ∧
          sm.readReg64 .x0 = s0.sp - 248#64 ∧ sm.readReg64 .x1 = ptr ∧ sm.readReg64 .x2 = BitVec.ofNat 64 (b0 :: rest0).length ∧
          sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧ sm.readReg64 .x21 = slot ∧ sm.readReg64 .x22 = 99#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rest0) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0))
        hgt10 hlen_lt0 hpc hrun rfl hsp_align hx0 hx1 hx2 hx3
        (fun _ _ _ hsp' htr' hvregs' hlr' hx0' hx1' hx2' hx19' hx20' hx21' hx22' hx29' _ hent =>
          ⟨hsp', htr', hvregs', hlr', hx0', hx1', hx2', hx19', hx20', hx21', hx22', hx29', hent⟩)).elim hmem1 hL0
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hm1' := Satisfies.mono (sepConj_mono_left hent1) hm1
    have hal1 : s1.spAligned = true := by simp only [State.spAligned, hsp1, beq_iff_eq]; exact hsp_sub_align
    have hx2_1_nat : (s1.readReg64 .x2).toNat = (c.payload ++ tail).length := by
      rw [hx2_1, ← hpay, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpre_slice : Prost.VarintSlicePre (c.payload ++ tail) := by refine Or.inl ?_; rw [hpay]; omega
    let gvar : Prost.DecodeVarintSliceGhost := ⟨s0.sp - 248#64, ptr, c.payload ++ tail⟩
    let savedTail : SepProp :=
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
    let F_call : SepProp :=
      (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.payload ++ tail).length) ∗
      memRegion (s0.sp - 256#64 - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.decodeVarintSliceStackW) ∗
      memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 224#64) 128 ∗ savedTail ∗ prostChainGAt A0 a ChainG.empty
    have hm1_call : s1.mem ⊨ ((Prost.X.decodeVarintSliceSpecW A0).inImage img).pre gvar s1 ∗ (F_call ∗ R) := by
      unfold Spec.inImage Prost.X.decodeVarintSliceSpecW
      dsimp only [gvar]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hst1.frozenLoaded hF0, hst1.symtab_eq.trans hsym0⟩, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      have hlen_lt63 : (c.payload ++ tail).length < 2 ^ 63 := Nat.lt_trans hlen_lt (by decide)
      refine ⟨⟨hx0_1, hx1_1, hx2_1_nat, hlen_lt63, hpre_slice⟩, ?_⟩
      have hsaved : chainMergeSavedRegs s0.sp s0 =
          memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 24 ∗
            memRegion (s0.sp - 224#64) 128 ∗ savedTail := by
        unfold chainMergeSavedRegs; rw [memRegion160_split_varint_cme s0.sp]; dsimp only [savedTail]; ac_rfl
      rw [← hpay, stackAt_sub_to_varintSlice_cmeW (s0.sp - 256#64), hsaved] at hm1'
      unfold sliceCursorAt at hm1'
      have hpool : A0.pool = emp := rfl
      rw [hsp1, hpool]; dsimp only [F_call]; convert hm1' using 1; ac_rfl
    have hsub_varint := decodeVarintSlice_ok_sub_cme_extW (img := img) (A := A0) (ext := ext) hC.1
    have hwpp2 : ProofLib.SepWPp (SP2Ext img.base ext) (s1.readReg64 .lr) s1
        (((Prost.X.decodeVarintSliceSpecW A0).inImage img).pre gvar s1 ∗ F_call)
        (fun sf P_f => sf.sp = s1.sp ∧ CalleeSavedPreserved s1 sf ∧
          P_f = ((Prost.X.decodeVarintSliceSpecW A0).inImage img).post gvar s1 sf ∗ F_call)
        (fun sf P_f => P_f = ((Prost.X.decodeVarintSliceSpecW A0).inImage img).onPanic gvar s1 sf ∗ F_call)
        (fun _ => ⌜False⌝) :=
      ProofLib.SepWPp.call (x := gvar) (F := F_call) hsub_varint hpc1 hrun1 hal1 rfl
        (fun _ hm' => by simpa only [sepConj_assoc] using hm')
        (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
        (fun _ _ => rfl)
        (fun sf hpcsf hrunsf hspsf hcssf => ProofLib.SepWPp.done hpcsf hrunsf ⟨hspsf, hcssf, rfl⟩)
        (fun _ _ _ hoom => (not_satisfies_false_sepConj hoom).elim)
    obtain ⟨s2, hst2, ⟨hpc2, hrun2, _, hm2, hsp2, hcs2, rfl⟩ | ⟨hpan2, _, hm2_pan, rfl⟩ | ⟨_, hm2_oom⟩⟩ :=
      hwpp2 R (by simpa only [sepConj_assoc] using hm1_call) (hst1.codeLoaded hL0)
    · rw [sepConj_assoc] at hm2
      have hpc2' : s2.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x9c#64 := by rw [hpc2, hlr1]
      have hsp2' : s2.sp = s0.sp - 256#64 := by rw [hsp2, hsp1]
      have hx19_2 : s2.readReg64 .x19 = bufRef := hcs2.1.trans hx19_1
      have hx20_2 : s2.readReg64 .x20 = a := hcs2.2.1.trans hx20_1
      have hx21_2 : s2.readReg64 .x21 = slot := hcs2.2.2.1.trans hx21_1
      have hx22_2 : s2.readReg64 .x22 = 99#64 := hcs2.2.2.2.1.trans hx22_1
      have hx29_2 : s2.readReg64 .x29 = s0.sp - 96#64 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
      have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      let vlen := (encodeVarint (BitVec.ofNat 64 c.enc.length)).length
      have hpay_split : c.payload ++ tail = encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.enc ++ tail) := by
        unfold ChainG.payload; rw [List.append_assoc]
      have hdec : decodeVarint (c.payload ++ tail) = some (BitVec.ofNat 64 c.enc.length, c.enc ++ tail) := by
        rw [hpay_split]; exact decodeVarint_encodeVarint (BitVec.ofNat 64 c.enc.length) (c.enc ++ tail)
      have hlen_sub : (c.payload ++ tail).length - (c.enc ++ tail).length = vlen := by
        rw [hpay_split, List.length_append, Nat.add_sub_cancel_right]
      have hlen_tot : (c.payload ++ tail).length = vlen + (c.enc.length + tail.length) := by
        rw [hpay_split, List.length_append, List.length_append]
      have hlen_lt_v : (vlen + (c.enc.length + tail.length)) < 2 ^ 62 := by rw [← hlen_tot]; exact hlen_lt
      unfold Spec.inImage Prost.X.decodeVarintSliceSpecW at hm2
      dsimp only [gvar] at hm2
      rw [hdec] at hm2; dsimp only [Prost.varintSliceResultAt] at hm2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
      rcases hm2 with ⟨htr2, hm2⟩
      have hm2_post : s2.mem ⊨
          ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗
            ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (vlen + (c.enc.length + tail.length))) ∗
            ((s0.sp - 248#64) ↦₃₂ 0#32) ∗ ((s0.sp - 244#64) ↦₃₂ 0#32) ∗
            ((s0.sp - 240#64) ↦₆₄ BitVec.ofNat 64 c.enc.length) ∗
            ((s0.sp - 232#64) ↦₆₄ BitVec.ofNat 64 vlen)) ∗
          ((ptr ↦ₛ (c.payload ++ tail)) ∗ stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
            memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 224#64) 128 ∗
            savedTail ∗ prostChainGAt A0 a ChainG.empty ∗ R) := by
        dsimp only [F_call] at hm2
        have hpool : A0.pool = emp := rfl
        have ha8 : (s0.sp - 248#64) + 8#64 = s0.sp - 240#64 := by bv_omega
        have ha16 : (s0.sp - 248#64) + 16#64 = s0.sp - 232#64 := by bv_omega
        rw [hsp1, hpool, ha8, ha16, hlen_sub, hlen_tot, pointsTo64_zero_split32_cme s0.sp] at hm2
        rw [stackAt_sub_to_varintSlice_cmeW (s0.sp - 256#64)]
        convert hm2 using 1; ac_rfl
      obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, hsp3, htr3, hvregs3, hx29_3, hx19_3, hx20_3, hx24_3, hx21_3, hx22_3, hx25_3, hx26_3, hent3⟩ | ⟨_, _hoom⟩⟩ :=
        (step_chainMerge_seg0_ge128_post_cme_extW (img := img) (ext := ext)
          a bufRef slot ptr s0.sp vlen c.enc tail
          (post := fun sm Pm =>
            sm.sp = s0.sp - 256#64 ∧ sm.trace = s2.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s2 ∧
            sm.readReg64 .x29 = s0.sp - 96#64 ∧
            sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧ sm.readReg64 .x24 = BitVec.ofNat 64 tail.length ∧
            sm.readReg64 .x21 = 98#64 ∧ sm.readReg64 .x22 = 97#64 ∧ sm.readReg64 .x25 = s0.sp - 248#64 ∧ sm.readReg64 .x26 = 1#64 ∧
            (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
              ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc ++ tail).length) ∗ memRegion (s0.sp - 248#64) 24))
          hlen_lt_v hpc2' hrun2 hsp2' hsp_align hx19_2 hx20_2 hx21_2 hx22_2 hx29_2
          (fun _ _ _ hsp' htr' hvregs' hx29' hx19' hx20' hx24' hx21' hx22' hx25' hx26' _ hent =>
            ⟨hsp', htr', hvregs', hx29', hx19', hx20', hx24', hx21', hx22', hx25', hx26', hent⟩)).elim
          hm2_post ((hst1.trans hst2).codeLoaded hL0)
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      have hm3' := Satisfies.mono (sepConj_mono_left hent3) hm3
      have hst_all := (hst1.trans hst2).trans hst3
      refine ⟨s3, hst_all, Or.inl ⟨hpc3, hrun3, (htr3.trans htr2).trans htr1, hvregs3.trans hvregs2,
        hst_all.symtab_eq.trans hsym0,
        hst_all.frozenLoaded hF0, hsp3, by simp only [State.spAligned, hsp3, beq_iff_eq]; exact hsp_sub_align,
        hx29_3, hx19_3, hx20_3, hx24_3, hx21_3, hx22_3, hx25_3, hx26_3, hcOk, hlen_lt, ?_⟩⟩
      rw [hchain0, hdrop0]
      unfold sliceCursorAfter; rw [hlen_sub]
      have hsaved : chainMergeSavedRegs s0.sp s0 = memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 128 ∗ savedTail := by
        unfold chainMergeSavedRegs; rw [memRegion160_split_varint_cme s0.sp]; dsimp only [savedTail]; ac_rfl
      rw [hsaved]; convert hm3' using 1; ac_rfl
    · refine ⟨s2, hst1.trans hst2, Or.inr ⟨hpan2, ?_⟩⟩
      unfold Spec.inImage Prost.X.decodeVarintSliceSpecW at hm2_pan
      dsimp only at hm2_pan
      exact allowPanic_frame_trace_cme htr1 hm2_pan
    · exact False.elim (not_satisfies_false_sepConj hm2_oom)

theorem chainEntryG_ok_impl_atWA (img : Obj.Image) (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hC : DeserializeCalleesAtWA img A ext) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (chainMergeGenSpecAtWA A img).pre x s0 ∗ R) (hal : s0.spAligned = true) :
    ChainStepGAtWA img A ext x R s0 s0 (ChainLoopGAtWA img A ext x R s0 0) := by
  intro hL0
  rcases x with ⟨a, c, bufRef, slot, ptr, tail⟩
  dsimp only [chainMergeGenSpecAtWA] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hcOk, hlen_lt, hF0, hsym0⟩, hmem⟩
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
  have hsp_sub_align : (s0.sp - 256#64) &&& 15#64 = 0#64 := sp_sub_256_aligned_seedChain hsp_align
  have hdrop0 : ((c.fields.drop 0).flatMap ChainField.enc) = c.enc := by rw [List.drop_zero, ← chainG_enc_eq_fields_cme c]
  have hchain0 : chainGAfter c 0 = ChainG.empty := rfl
  by_cases hbody_lt : c.enc.length < 128
  · have hvar : encodeVarint (BitVec.ofNat 64 c.enc.length) = [BitVec.ofNat 8 c.enc.length] :=
      encodeVarint_lt128_seedChain c.enc.length hbody_lt
    have hpay : c.payload ++ tail = BitVec.ofNat 8 c.enc.length :: (c.enc ++ tail) := by
      unfold ChainG.payload; rw [hvar, List.singleton_append, List.cons_append]
    have hlen_lt1 : (1 + (c.enc.length + tail.length)) < 2 ^ 62 := by
      rw [hpay, List.length_cons, List.length_append] at hlen_lt; omega
    have hmem1 : s0.mem ⊨
        ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (BitVec.ofNat 8 c.enc.length :: (c.enc ++ tail)) ∗ stackAt s0.sp chainMergeStackX) ∗
        (prostChainGAt A a ChainG.empty ∗ A.pool ∗ R) := by rw [← hpay]; convert hmem using 1; ac_rfl
    obtain ⟨sm, hst, ⟨hpcm, hrunm, Pm, hmm, hspm, htrm, hvregsm, hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m, hent⟩ | ⟨_, _hoom⟩⟩ :=
      (step_chainMerge_seg0_1byte_cme_extW (img := img) (ext := ext) a bufRef slot ptr s0.sp c.enc tail
        (post := fun sm Pm =>
          sm.sp = s0.sp - 256#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧ sm.readReg64 .x24 = BitVec.ofNat 64 tail.length ∧
          sm.readReg64 .x21 = 98#64 ∧ sm.readReg64 .x22 = 97#64 ∧ sm.readReg64 .x25 = s0.sp - 248#64 ∧ sm.readReg64 .x26 = 1#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (ptr ↦₈ BitVec.ofNat 8 c.enc.length) ∗
            sliceCursorAt slot (ptr + 1#64) (c.enc ++ tail) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0))
        hbody_lt hlen_lt1 hpc hrun rfl hsp_align hx0 hx1 hx2 hx3
        (fun _ _ _ hsp' htr' hvregs' hx29' hx19' hx20' hx24' hx21' hx22' hx25' hx26' _ hent =>
          ⟨hsp', htr', hvregs', hx29', hx19', hx20', hx24', hx21', hx22', hx25', hx26', hent⟩)).elim hmem1 hL0
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hmm' := Satisfies.mono (sepConj_mono_left hent) hmm
    refine ⟨sm, hst, Or.inl ⟨hpcm, hrunm, htrm, hvregsm, hst.symtab_eq.trans hsym0, hst.frozenLoaded hF0,
      hspm, by simp only [State.spAligned, hspm, beq_iff_eq]; exact hsp_sub_align,
      hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m, hcOk, hlen_lt, ?_⟩⟩
    rw [hchain0, hdrop0, hpay]
    have hcur := sliceCursorAfter_append_eq_seedChain slot ptr [BitVec.ofNat 8 c.enc.length] (c.enc ++ tail)
    rw [List.singleton_append] at hcur; rw [hcur]
    simp only [List.length_singleton, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    convert hmm' using 1; ac_rfl
  · have hbody_ge : 128 ≤ c.enc.length := by omega
    have hbody_lt62 : c.enc.length < 2 ^ 62 := by
      unfold ChainG.payload at hlen_lt; simp only [List.length_append] at hlen_lt; omega
    obtain ⟨vtail, hvar⟩ := encodeVarint_ge128_cons_cme62 hbody_ge hbody_lt62
    let b0 := BitVec.ofNat 8 (c.enc.length % 128 + 128)
    let rest0 := vtail ++ (c.enc ++ tail)
    have hpay : c.payload ++ tail = b0 :: rest0 := by
      unfold ChainG.payload; dsimp only [b0, rest0]
      rw [hvar, List.cons_append, List.cons_append, List.append_assoc]
    have hgt10 : 10 < (b0 :: rest0).length := by
      rw [← hpay]; unfold ChainG.payload; simp only [List.length_append]; omega
    have hlen_lt0 : (b0 :: rest0).length < 2 ^ 62 := by rw [← hpay]; exact hlen_lt
    have hmem1 : s0.mem ⊨
        ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rest0) ∗ stackAt s0.sp chainMergeStackX) ∗
        (prostChainGAt A a ChainG.empty ∗ A.pool ∗ R) := by rw [← hpay]; convert hmem using 1; ac_rfl
    obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, hsp1, htr1, hvregs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1, hx29_1, hent1⟩ | ⟨_, _hoom⟩⟩ :=
      (step_chainMerge_seg0_ge128_pre_cme_extW (img := img) (ext := ext) a bufRef slot ptr s0.sp c.enc.length rest0
        (post := fun sm Pm =>
          sm.sp = s0.sp - 256#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMergeName + 0x9c#64 ∧
          sm.readReg64 .x0 = s0.sp - 248#64 ∧ sm.readReg64 .x1 = ptr ∧ sm.readReg64 .x2 = BitVec.ofNat 64 (b0 :: rest0).length ∧
          sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧ sm.readReg64 .x21 = slot ∧ sm.readReg64 .x22 = 99#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rest0) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0))
        hgt10 hlen_lt0 hpc hrun rfl hsp_align hx0 hx1 hx2 hx3
        (fun _ _ _ hsp' htr' hvregs' hlr' hx0' hx1' hx2' hx19' hx20' hx21' hx22' hx29' _ hent =>
          ⟨hsp', htr', hvregs', hlr', hx0', hx1', hx2', hx19', hx20', hx21', hx22', hx29', hent⟩)).elim hmem1 hL0
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hm1' := Satisfies.mono (sepConj_mono_left hent1) hm1
    have hal1 : s1.spAligned = true := by simp only [State.spAligned, hsp1, beq_iff_eq]; exact hsp_sub_align
    have hx2_1_nat : (s1.readReg64 .x2).toNat = (c.payload ++ tail).length := by
      rw [hx2_1, ← hpay, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpre_slice : Prost.VarintSlicePre (c.payload ++ tail) := by refine Or.inl ?_; rw [hpay]; omega
    let gvar : Prost.DecodeVarintSliceGhost := ⟨s0.sp - 248#64, ptr, c.payload ++ tail⟩
    let savedTail : SepProp :=
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
    let F_call : SepProp :=
      (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.payload ++ tail).length) ∗
      memRegion (s0.sp - 256#64 - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.decodeVarintSliceStackW) ∗
      memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 224#64) 128 ∗ savedTail ∗ prostChainGAt A a ChainG.empty
    have hm1_call : s1.mem ⊨ ((Prost.X.decodeVarintSliceSpecW A).inImage img).pre gvar s1 ∗ (F_call ∗ R) := by
      unfold Spec.inImage Prost.X.decodeVarintSliceSpecW
      dsimp only [gvar]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hst1.frozenLoaded hF0, hst1.symtab_eq.trans hsym0⟩, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      have hlen_lt63 : (c.payload ++ tail).length < 2 ^ 63 := Nat.lt_trans hlen_lt (by decide)
      refine ⟨⟨hx0_1, hx1_1, hx2_1_nat, hlen_lt63, hpre_slice⟩, ?_⟩
      have hsaved : chainMergeSavedRegs s0.sp s0 =
          memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 24 ∗
            memRegion (s0.sp - 224#64) 128 ∗ savedTail := by
        unfold chainMergeSavedRegs; rw [memRegion160_split_varint_cme s0.sp]; dsimp only [savedTail]; ac_rfl
      rw [← hpay, stackAt_sub_to_varintSlice_cmeW (s0.sp - 256#64), hsaved] at hm1'
      unfold sliceCursorAt at hm1'
      rw [hsp1]; dsimp only [F_call]; convert hm1' using 1; ac_rfl
    have hsub_varint := decodeVarintSlice_ok_sub_cme_extW (img := img) (A := A) (ext := ext) hC.1
    have hwpp2 : ProofLib.SepWPp (SP2Ext img.base ext) (s1.readReg64 .lr) s1
        (((Prost.X.decodeVarintSliceSpecW A).inImage img).pre gvar s1 ∗ F_call)
        (fun sf P_f => sf.sp = s1.sp ∧ CalleeSavedPreserved s1 sf ∧
          P_f = ((Prost.X.decodeVarintSliceSpecW A).inImage img).post gvar s1 sf ∗ F_call)
        (fun sf P_f => P_f = ((Prost.X.decodeVarintSliceSpecW A).inImage img).onPanic gvar s1 sf ∗ F_call)
        (fun _ => ⌜False⌝) :=
      ProofLib.SepWPp.call (x := gvar) (F := F_call) hsub_varint hpc1 hrun1 hal1 rfl
        (fun _ hm' => by simpa only [sepConj_assoc] using hm')
        (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
        (fun _ _ => rfl)
        (fun sf hpcsf hrunsf hspsf hcssf => ProofLib.SepWPp.done hpcsf hrunsf ⟨hspsf, hcssf, rfl⟩)
        (fun _ _ _ hoom => (not_satisfies_false_sepConj hoom).elim)
    obtain ⟨s2, hst2, ⟨hpc2, hrun2, _, hm2, hsp2, hcs2, rfl⟩ | ⟨hpan2, _, hm2_pan, rfl⟩ | ⟨_, hm2_oom⟩⟩ :=
      hwpp2 R (by simpa only [sepConj_assoc] using hm1_call) (hst1.codeLoaded hL0)
    · rw [sepConj_assoc] at hm2
      have hpc2' : s2.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x9c#64 := by rw [hpc2, hlr1]
      have hsp2' : s2.sp = s0.sp - 256#64 := by rw [hsp2, hsp1]
      have hx19_2 : s2.readReg64 .x19 = bufRef := hcs2.1.trans hx19_1
      have hx20_2 : s2.readReg64 .x20 = a := hcs2.2.1.trans hx20_1
      have hx21_2 : s2.readReg64 .x21 = slot := hcs2.2.2.1.trans hx21_1
      have hx22_2 : s2.readReg64 .x22 = 99#64 := hcs2.2.2.2.1.trans hx22_1
      have hx29_2 : s2.readReg64 .x29 = s0.sp - 96#64 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
      have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      let vlen := (encodeVarint (BitVec.ofNat 64 c.enc.length)).length
      have hpay_split : c.payload ++ tail = encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.enc ++ tail) := by
        unfold ChainG.payload; rw [List.append_assoc]
      have hdec : decodeVarint (c.payload ++ tail) = some (BitVec.ofNat 64 c.enc.length, c.enc ++ tail) := by
        rw [hpay_split]; exact decodeVarint_encodeVarint (BitVec.ofNat 64 c.enc.length) (c.enc ++ tail)
      have hlen_sub : (c.payload ++ tail).length - (c.enc ++ tail).length = vlen := by
        rw [hpay_split, List.length_append, Nat.add_sub_cancel_right]
      have hlen_tot : (c.payload ++ tail).length = vlen + (c.enc.length + tail.length) := by
        rw [hpay_split, List.length_append, List.length_append]
      have hlen_lt_v : (vlen + (c.enc.length + tail.length)) < 2 ^ 62 := by rw [← hlen_tot]; exact hlen_lt
      unfold Spec.inImage Prost.X.decodeVarintSliceSpecW at hm2
      dsimp only [gvar] at hm2
      rw [hdec] at hm2; dsimp only [Prost.varintSliceResultAt] at hm2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
      rcases hm2 with ⟨htr2, hm2⟩
      have hm2_post : s2.mem ⊨
          ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗
            ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (vlen + (c.enc.length + tail.length))) ∗
            ((s0.sp - 248#64) ↦₃₂ 0#32) ∗ ((s0.sp - 244#64) ↦₃₂ 0#32) ∗
            ((s0.sp - 240#64) ↦₆₄ BitVec.ofNat 64 c.enc.length) ∗
            ((s0.sp - 232#64) ↦₆₄ BitVec.ofNat 64 vlen)) ∗
          ((ptr ↦ₛ (c.payload ++ tail)) ∗ stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
            memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 224#64) 128 ∗
            savedTail ∗ prostChainGAt A a ChainG.empty ∗ A.pool ∗ R) := by
        dsimp only [F_call] at hm2
        have ha8 : (s0.sp - 248#64) + 8#64 = s0.sp - 240#64 := by bv_omega
        have ha16 : (s0.sp - 248#64) + 16#64 = s0.sp - 232#64 := by bv_omega
        rw [hsp1, ha8, ha16, hlen_sub, hlen_tot, pointsTo64_zero_split32_cme s0.sp] at hm2
        rw [stackAt_sub_to_varintSlice_cmeW (s0.sp - 256#64)]
        convert hm2 using 1; ac_rfl
      obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, hsp3, htr3, hvregs3, hx29_3, hx19_3, hx20_3, hx24_3, hx21_3, hx22_3, hx25_3, hx26_3, hent3⟩ | ⟨_, _hoom⟩⟩ :=
        (step_chainMerge_seg0_ge128_post_cme_extW (img := img) (ext := ext)
          a bufRef slot ptr s0.sp vlen c.enc tail
          (post := fun sm Pm =>
            sm.sp = s0.sp - 256#64 ∧ sm.trace = s2.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s2 ∧
            sm.readReg64 .x29 = s0.sp - 96#64 ∧
            sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧ sm.readReg64 .x24 = BitVec.ofNat 64 tail.length ∧
            sm.readReg64 .x21 = 98#64 ∧ sm.readReg64 .x22 = 97#64 ∧ sm.readReg64 .x25 = s0.sp - 248#64 ∧ sm.readReg64 .x26 = 1#64 ∧
            (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
              ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc ++ tail).length) ∗ memRegion (s0.sp - 248#64) 24))
          hlen_lt_v hpc2' hrun2 hsp2' hsp_align hx19_2 hx20_2 hx21_2 hx22_2 hx29_2
          (fun _ _ _ hsp' htr' hvregs' hx29' hx19' hx20' hx24' hx21' hx22' hx25' hx26' _ hent =>
            ⟨hsp', htr', hvregs', hx29', hx19', hx20', hx24', hx21', hx22', hx25', hx26', hent⟩)).elim
          hm2_post ((hst1.trans hst2).codeLoaded hL0)
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      have hm3' := Satisfies.mono (sepConj_mono_left hent3) hm3
      have hst_all := (hst1.trans hst2).trans hst3
      refine ⟨s3, hst_all, Or.inl ⟨hpc3, hrun3, (htr3.trans htr2).trans htr1, hvregs3.trans hvregs2,
        hst_all.symtab_eq.trans hsym0,
        hst_all.frozenLoaded hF0, hsp3, by simp only [State.spAligned, hsp3, beq_iff_eq]; exact hsp_sub_align,
        hx29_3, hx19_3, hx20_3, hx24_3, hx21_3, hx22_3, hx25_3, hx26_3, hcOk, hlen_lt, ?_⟩⟩
      rw [hchain0, hdrop0]
      unfold sliceCursorAfter; rw [hlen_sub]
      have hsaved : chainMergeSavedRegs s0.sp s0 = memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 128 ∗ savedTail := by
        unfold chainMergeSavedRegs; rw [memRegion160_split_varint_cme s0.sp]; dsimp only [savedTail]; ac_rfl
      rw [hsaved]; convert hm3' using 1; ac_rfl
    · refine ⟨s2, hst1.trans hst2, Or.inr ⟨hpan2, ?_⟩⟩
      unfold Spec.inImage Prost.X.decodeVarintSliceSpecW at hm2_pan
      dsimp only at hm2_pan
      exact allowPanic_frame_trace_cme htr1 hm2_pan
    · exact False.elim (not_satisfies_false_sepConj hm2_oom)

/-! ## 4. Relocatable `[LibsignalPlacement]` Proof of `message::merge<Chain>` Entry (`lsProg_11 H`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_ChainEntryGExt_Placed : True := trivial

private theorem step_chainMerge_seg0_1byte_cme_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (a bufRef slot ptr sp0 : BitVec 64) (body tail : List (BitVec 8))
    (hbody_lt : body.length < 128) (hlen_lt : (1 + (body.length + tail.length)) < 2 ^ 62)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8) (hx1 : s0.readReg64 .x1 = a)
    (hx2 : s0.readReg64 .x2 = bufRef) (hx3 : (s0.readReg64 .x3).setWidth 32 = 99#32)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x120#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x29 = sp0 - 96#64 → sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x21 = 98#64 → sm.readReg64 .x22 = 97#64 →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      ∀ Pm, (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (ptr ↦₈ BitVec.ofNat 8 body.length) ∗
        sliceCursorAt slot (ptr + 1#64) (body ++ tail) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs sp0 s0) → post sm Pm) :
    SepWP (lsProg_11 H) ((blkPl_11).base + 0x120#64) s0
      ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (BitVec.ofNat 8 body.length :: (body ++ tail)) ∗
        stackAt sp0 chainMergeStackX) post := by
  subst hsp
  have h1 : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = bufRef := hx2
  have hw3 : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 3#5)) = 99#32 := hx3
  have hw0 : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64 = 2#64 :=
    w0_and_255_eq_two_seedChain hx0
  have hlen_cons : (BitVec.ofNat 8 body.length :: (body ++ tail)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz := cbz_len_cons_false_seedChain62 hlen_cons
  have hse0 := signExtend64_ofNat8_lt128_seedChain hbody_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hbody_lt
  have hsub_len := len_cons_sub_one_seedChain (BitVec.ofNat 8 body.length) (body ++ tail)
  have hlen_append : (body ++ tail).length = body.length + tail.length := List.length_append
  have hule_sub := ule_ofNat_add_right_true_seedChain62 (m := body.length) (k := tail.length) (by omega)
  have hsub_tail := bv_ofNat_add_sub_left_seedChain body.length tail.length
  rw [stackAt_chainMergeStackX_split_seedChain s0.sp]
  unfold sliceCursorAt
  rw [pointsToBytes_cons]
  simp only [sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w96; apply SepWP.exists_elim; intro w88
  apply SepWP.exists_elim; intro w80; apply SepWP.exists_elim; intro w72
  apply SepWP.exists_elim; intro w64; apply SepWP.exists_elim; intro w56
  apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
  apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
  apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
  iterate 31 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) _ (by
      unfold sliceCursorAt chainMergeSavedRegs; rw [← hlen_append]; exact sep_ac_seedChain (by ac_rfl))

private theorem step_chainMerge_seg0_ge128_pre_cme_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (a bufRef slot ptr sp0 : BitVec 64) (n : Nat) (rest0 : List (BitVec 8))
    (hgt10 : 10 < (BitVec.ofNat 8 (n % 128 + 128) :: rest0).length)
    (hlen_lt : (BitVec.ofNat 8 (n % 128 + 128) :: rest0).length < 2 ^ 62)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8) (hx1 : s0.readReg64 .x1 = a)
    (hx2 : s0.readReg64 .x2 = bufRef) (hx3 : (s0.readReg64 .x3).setWidth 32 = 99#32)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 76 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .lr = (blkPl_11).base + 0x9c#64 →
      sm.readReg64 .x0 = sp0 - 248#64 → sm.readReg64 .x1 = ptr →
      sm.readReg64 .x2 = BitVec.ofNat 64 (BitVec.ofNat 8 (n % 128 + 128) :: rest0).length →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = slot → sm.readReg64 .x22 = 99#64 →
      sm.readReg64 .x29 = sp0 - 96#64 →
      ∀ Pm, (Pm ⊢ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (BitVec.ofNat 8 (n % 128 + 128) :: rest0) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs sp0 s0) → post sm Pm) :
    SepWP (lsProg_11 H) (lsmpl.base 76) s0
      ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (BitVec.ofNat 8 (n % 128 + 128) :: rest0) ∗
        stackAt sp0 chainMergeStackX) post := by
  subst hsp
  have h1 : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = bufRef := hx2
  have hw3 : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 3#5)) = 99#32 := hx3
  have hw0 : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64 = 2#64 :=
    w0_and_255_eq_two_seedChain hx0
  have hcbz := cbz_len_cons_false_seedChain62 hlen_lt
  have hlsr56 := signExtend64_contByte_lsr56_cme n
  have hhi10 := ult_10_of_gt_cme62 hgt10 hlen_lt
  have hule10 := ule_10_of_gt_false_cme62 hgt10 hlen_lt
  rw [stackAt_chainMergeStackX_split_seedChain s0.sp]
  unfold sliceCursorAt
  rw [pointsToBytes_cons]
  simp only [sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w96; apply SepWP.exists_elim; intro w88
  apply SepWP.exists_elim; intro w80; apply SepWP.exists_elim; intro w72
  apply SepWP.exists_elim; intro w64; apply SepWP.exists_elim; intro w56
  apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
  apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
  apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
  iterate 24 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) _ (by
      unfold sliceCursorAt chainMergeSavedRegs
      rw [pointsToBytes_cons]
      exact sep_ac_seedChain (by ac_rfl))

private theorem step_chainMerge_seg0_ge128_post_cme_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (a bufRef slot ptr sp0 : BitVec 64) (vlen : Nat) (body tail : List (BitVec 8))
    (hlen_lt : (vlen + (body.length + tail.length)) < 2 ^ 62)
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_11).base + 0x9c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64) (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = bufRef) (hx20 : s.readReg64 .x20 = a) (hx21 : s.readReg64 .x21 = slot)
    (hx22 : s.readReg64 .x22 = 99#64) (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x120#64 →
      sm.status = .Running → sm.sp = sp0 - 256#64 → sm.trace = s.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x29 = sp0 - 96#64 → sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a → sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x21 = 98#64 → sm.readReg64 .x22 = 97#64 →
      sm.readReg64 .x25 = sp0 - 248#64 → sm.readReg64 .x26 = 1#64 →
      ∀ Pm, (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length) ∗ memRegion (sp0 - 248#64) 24) →
      post sm Pm) :
    SepWP (lsProg_11 H) ((blkPl_11).base + 0x120#64) s
      ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (vlen + (body.length + tail.length))) ∗
        ((sp0 - 248#64) ↦₃₂ 0#32) ∗ ((sp0 - 244#64) ↦₃₂ 0#32) ∗
        ((sp0 - 240#64) ↦₆₄ BitVec.ofNat 64 body.length) ∗ ((sp0 - 232#64) ↦₆₄ BitVec.ofNat 64 vlen))
      post := by
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact sp_sub_256_aligned_seedChain hsp_align
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = slot := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 99#64 := hx22
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  have hlen_append : (body ++ tail).length = body.length + tail.length := List.length_append
  have hsub_vlen := bv_ofNat_add_sub_left_seedChain vlen (body.length + tail.length)
  have hult_vlen := ult_ofNat_add_left_false_seedChain62 (m := vlen) (k := body.length + tail.length) hlen_lt
  have hule_vlen := ule_ofNat_add_right_true_seedChain62 (m := vlen) (k := body.length + tail.length) hlen_lt
  have hsub_tail := bv_ofNat_add_sub_left_seedChain body.length tail.length
  have hbody_tail_lt : body.length + tail.length < 2 ^ 62 := by omega
  have hule_sub := ule_ofNat_add_right_true_seedChain62 (m := body.length) (k := tail.length) hbody_tail_lt
  have hult_sub := ult_ofNat_add_left_false_seedChain62 (m := body.length) (k := tail.length) hbody_tail_lt
  iterate 19 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [h29, arm64_norm]) (by simp only [h19, arm64_norm])
    (by simp only [h20, arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) _ ?_
  have hcells := cells24_entails_memRegion24_cme sp0 (BitVec.ofNat 64 body.length) (BitVec.ofNat 64 vlen)
  rw [← hlen_append]
  have hEq1 : bufRef ↦₆₄ slot ∗ slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length) ∗
      ((sp0 - 248#64) ↦₃₂ 0#32) ∗ ((sp0 - 244#64) ↦₃₂ 0#32) ∗
      ((sp0 - 240#64) ↦₆₄ BitVec.ofNat 64 body.length) ∗ ((sp0 - 232#64) ↦₆₄ BitVec.ofNat 64 vlen) =
    (((sp0 - 248#64) ↦₃₂ 0#32) ∗ ((sp0 - 244#64) ↦₃₂ 0#32) ∗
      ((sp0 - 240#64) ↦₆₄ BitVec.ofNat 64 body.length) ∗ ((sp0 - 232#64) ↦₆₄ BitVec.ofNat 64 vlen)) ∗
    ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length)) := by ac_rfl
  have hEq2 : memRegion (sp0 - 248#64) 24 ∗ ((bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length)) =
    (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length) ∗ memRegion (sp0 - 248#64) 24 := by ac_rfl
  rw [hEq1, ← hEq2]; exact sepConj_mono_left hcells

/-- Relocatable `message::merge<Chain>` entry (`+0x000` → `+0x120`, `k = 0`) on `lsProg_11 H`. -/
theorem chainEntryG_placed_okW [LibsignalPlacement] (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (blkPl_11).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ chainMergeGenPlacedSpecW.pre x s0 ∗ R) (hal : s0.spAligned = true) :
    ChainStepGPlacedW H x R s0 s0 (ChainLoopGPlacedW x R s0 0) := by
  intro hL0
  rcases x with ⟨a, c, bufRef, slot, ptr, tail⟩
  obtain ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [chainMergeGenRawSpecW] at hpre_raw
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, hcOk, hlen_lt⟩, hmem⟩
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
  have hsp_sub_align : (s0.sp - 256#64) &&& 15#64 = 0#64 := sp_sub_256_aligned_seedChain hsp_align
  have hdrop0 : ((c.fields.drop 0).flatMap ChainField.enc) = c.enc := by rw [List.drop_zero, ← chainG_enc_eq_fields_cme c]
  have hchain0 : chainGAfter c 0 = ChainG.empty := rfl
  by_cases hbody_lt : c.enc.length < 128
  · have hvar : encodeVarint (BitVec.ofNat 64 c.enc.length) = [BitVec.ofNat 8 c.enc.length] :=
      encodeVarint_lt128_seedChain c.enc.length hbody_lt
    have hpay : c.payload ++ tail = BitVec.ofNat 8 c.enc.length :: (c.enc ++ tail) := by
      unfold ChainG.payload; rw [hvar, List.singleton_append, List.cons_append]
    have hlen_lt1 : (1 + (c.enc.length + tail.length)) < 2 ^ 62 := by
      rw [hpay, List.length_cons, List.length_append] at hlen_lt; omega
    have hmem1 : s0.mem ⊨
        ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (BitVec.ofNat 8 c.enc.length :: (c.enc ++ tail)) ∗ stackAt s0.sp chainMergeStackX) ∗
        (prostChainGAt A0 a ChainG.empty ∗ R) := by rw [← hpay]; convert hmem using 1; ac_rfl
    obtain ⟨sm, hst, ⟨hpcm, hrunm, Pm, hmm, hspm, htrm, hvregsm, hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m, hent⟩ | ⟨_, _hoom⟩⟩ :=
      (step_chainMerge_seg0_1byte_cme_placedW (H := H) a bufRef slot ptr s0.sp c.enc tail
        (post := fun sm Pm =>
          sm.sp = s0.sp - 256#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧ sm.readReg64 .x24 = BitVec.ofNat 64 tail.length ∧
          sm.readReg64 .x21 = 98#64 ∧ sm.readReg64 .x22 = 97#64 ∧ sm.readReg64 .x25 = s0.sp - 248#64 ∧ sm.readReg64 .x26 = 1#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (ptr ↦₈ BitVec.ofNat 8 c.enc.length) ∗
            sliceCursorAt slot (ptr + 1#64) (c.enc ++ tail) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0))
        hbody_lt hlen_lt1 hpc hrun rfl hsp_align hx0 hx1 hx2 hx3
        (fun _ _ _ hsp' htr' hvregs' hx29' hx19' hx20' hx24' hx21' hx22' hx25' hx26' _ hent =>
          ⟨hsp', htr', hvregs', hx29', hx19', hx20', hx24', hx21', hx22', hx25', hx26', hent⟩)).elim hmem1 hL0
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hmm' := Satisfies.mono (sepConj_mono_left hent) hmm
    refine ⟨sm, hst, Or.inl ⟨hpcm, hrunm, htrm, hvregsm, hcrl0.of_keepsFrozen hst.keepsFrozen,
      hspm, by simp only [State.spAligned, hspm, beq_iff_eq]; exact hsp_sub_align,
      hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m, hcOk, hlen_lt, ?_⟩⟩
    rw [hchain0, hdrop0, hpay]
    have hcur := sliceCursorAfter_append_eq_seedChain slot ptr [BitVec.ofNat 8 c.enc.length] (c.enc ++ tail)
    rw [List.singleton_append] at hcur; rw [hcur]
    simp only [List.length_singleton, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    convert hmm' using 1; ac_rfl
  · have hbody_ge : 128 ≤ c.enc.length := by omega
    have hbody_lt62 : c.enc.length < 2 ^ 62 := by
      unfold ChainG.payload at hlen_lt; simp only [List.length_append] at hlen_lt; omega
    obtain ⟨vtail, hvar⟩ := encodeVarint_ge128_cons_cme62 hbody_ge hbody_lt62
    let b0 := BitVec.ofNat 8 (c.enc.length % 128 + 128)
    let rest0 := vtail ++ (c.enc ++ tail)
    have hpay : c.payload ++ tail = b0 :: rest0 := by
      unfold ChainG.payload; dsimp only [b0, rest0]
      rw [hvar, List.cons_append, List.cons_append, List.append_assoc]
    have hgt10 : 10 < (b0 :: rest0).length := by
      rw [← hpay]; unfold ChainG.payload; simp only [List.length_append]; omega
    have hlen_lt0 : (b0 :: rest0).length < 2 ^ 62 := by rw [← hpay]; exact hlen_lt
    have hmem1 : s0.mem ⊨
        ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rest0) ∗ stackAt s0.sp chainMergeStackX) ∗
        (prostChainGAt A0 a ChainG.empty ∗ R) := by rw [← hpay]; convert hmem using 1; ac_rfl
    obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, hsp1, htr1, hvregs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1, hx29_1, hent1⟩ | ⟨_, _hoom⟩⟩ :=
      (step_chainMerge_seg0_ge128_pre_cme_placedW (H := H) a bufRef slot ptr s0.sp c.enc.length rest0
        (post := fun sm Pm =>
          sm.sp = s0.sp - 256#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .lr = (blkPl_11).base + 0x9c#64 ∧
          sm.readReg64 .x0 = s0.sp - 248#64 ∧ sm.readReg64 .x1 = ptr ∧ sm.readReg64 .x2 = BitVec.ofNat 64 (b0 :: rest0).length ∧
          sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧ sm.readReg64 .x21 = slot ∧ sm.readReg64 .x22 = 99#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rest0) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0))
        hgt10 hlen_lt0 hpc hrun rfl hsp_align hx0 hx1 hx2 hx3
        (fun _ _ _ hsp' htr' hvregs' hlr' hx0' hx1' hx2' hx19' hx20' hx21' hx22' hx29' _ hent =>
          ⟨hsp', htr', hvregs', hlr', hx0', hx1', hx2', hx19', hx20', hx21', hx22', hx29', hent⟩)).elim hmem1 hL0
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hm1' := Satisfies.mono (sepConj_mono_left hent1) hm1
    have hal1 : s1.spAligned = true := by simp only [State.spAligned, hsp1, beq_iff_eq]; exact hsp_sub_align
    have hx2_1_nat : (s1.readReg64 .x2).toNat = (c.payload ++ tail).length := by
      rw [hx2_1, ← hpay, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpre_slice : Prost.VarintSlicePre (c.payload ++ tail) := by refine Or.inl ?_; rw [hpay]; omega
    let gvar : Prost.DecodeVarintSliceGhost := ⟨s0.sp - 248#64, ptr, c.payload ++ tail⟩
    let savedTail : SepProp :=
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
    let F_call : SepProp :=
      (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.payload ++ tail).length) ∗
      memRegion (s0.sp - 256#64 - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.decodeVarintSliceStackW) ∗
      memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 224#64) 128 ∗ savedTail ∗ prostChainGAt A0 a ChainG.empty
    have hm1_call : s1.mem ⊨
        (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.decodeVarintSliceSpecW A0)).pre
          gvar s1 ∗ (F_call ∗ R) := by
      dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl0.of_keepsFrozen hst1.keepsFrozen, ?_⟩
      unfold Prost.X.decodeVarintSliceSpecW
      dsimp only [gvar]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      have hlen_lt63 : (c.payload ++ tail).length < 2 ^ 63 := Nat.lt_trans hlen_lt (by decide)
      refine ⟨⟨hx0_1, hx1_1, hx2_1_nat, hlen_lt63, hpre_slice⟩, ?_⟩
      have hsaved : chainMergeSavedRegs s0.sp s0 =
          memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 24 ∗
            memRegion (s0.sp - 224#64) 128 ∗ savedTail := by
        unfold chainMergeSavedRegs; rw [memRegion160_split_varint_cme s0.sp]; dsimp only [savedTail]; ac_rfl
      rw [← hpay, stackAt_sub_to_varintSlice_cmeW (s0.sp - 256#64), hsaved] at hm1'
      unfold sliceCursorAt at hm1'
      have hpool : A0.pool = emp := rfl
      rw [hsp1, hpool]; dsimp only [F_call]; convert hm1' using 1; ac_rfl
    have hsub_varint := decodeVarintSlice_placed_ok_sub_cmeW (A := A0) (H := H) hC.1
    have hwpp2 : ProofLib.SepWPp (lsProg_11 H) (s1.readReg64 .lr) s1
        ((LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.decodeVarintSliceSpecW A0)).pre gvar s1 ∗ F_call)
        (fun sf P_f => sf.sp = s1.sp ∧ CalleeSavedPreserved s1 sf ∧
          P_f = (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.decodeVarintSliceSpecW A0)).post gvar s1 sf ∗ F_call)
        (fun sf P_f => P_f = (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.decodeVarintSliceSpecW A0)).onPanic gvar s1 sf ∗ F_call)
        (fun _ => ⌜False⌝) :=
      ProofLib.SepWPp.call (x := gvar) (F := F_call) hsub_varint hpc1 hrun1 hal1 rfl
        (fun _ hm' => by simpa only [sepConj_assoc] using hm')
        (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
        (fun _ _ => rfl)
        (fun sf hpcsf hrunsf hspsf hcssf => ProofLib.SepWPp.done hpcsf hrunsf ⟨hspsf, hcssf, rfl⟩)
        (fun _ _ _ hoom => (not_satisfies_false_sepConj hoom).elim)
    obtain ⟨s2, hst2, ⟨hpc2, hrun2, _, hm2, hsp2, hcs2, rfl⟩ | ⟨hpan2, _, hm2_pan, rfl⟩ | ⟨_, hm2_oom⟩⟩ :=
      hwpp2 R (by simpa only [sepConj_assoc] using hm1_call) (hst1.codeLoaded hL0)
    · rw [sepConj_assoc] at hm2
      have hpc2' : s2.pc = (blkPl_11).base + 0x9c#64 := by rw [hpc2, hlr1]
      have hsp2' : s2.sp = s0.sp - 256#64 := by rw [hsp2, hsp1]
      have hx19_2 : s2.readReg64 .x19 = bufRef := hcs2.1.trans hx19_1
      have hx20_2 : s2.readReg64 .x20 = a := hcs2.2.1.trans hx20_1
      have hx21_2 : s2.readReg64 .x21 = slot := hcs2.2.2.1.trans hx21_1
      have hx22_2 : s2.readReg64 .x22 = 99#64 := hcs2.2.2.2.1.trans hx22_1
      have hx29_2 : s2.readReg64 .x29 = s0.sp - 96#64 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
      have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      let vlen := (encodeVarint (BitVec.ofNat 64 c.enc.length)).length
      have hpay_split : c.payload ++ tail = encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.enc ++ tail) := by
        unfold ChainG.payload; rw [List.append_assoc]
      have hdec : decodeVarint (c.payload ++ tail) = some (BitVec.ofNat 64 c.enc.length, c.enc ++ tail) := by
        rw [hpay_split]; exact decodeVarint_encodeVarint (BitVec.ofNat 64 c.enc.length) (c.enc ++ tail)
      have hlen_sub : (c.payload ++ tail).length - (c.enc ++ tail).length = vlen := by
        rw [hpay_split, List.length_append, Nat.add_sub_cancel_right]
      have hlen_tot : (c.payload ++ tail).length = vlen + (c.enc.length + tail.length) := by
        rw [hpay_split, List.length_append, List.length_append]
      have hlen_lt_v : (vlen + (c.enc.length + tail.length)) < 2 ^ 62 := by rw [← hlen_tot]; exact hlen_lt
      dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hm2
      unfold Prost.X.decodeVarintSliceSpecW at hm2
      dsimp only [gvar] at hm2
      rw [hdec] at hm2; dsimp only [Prost.varintSliceResultAt] at hm2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
      rcases hm2 with ⟨htr2, hm2⟩
      have hm2_post : s2.mem ⊨
          ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗
            ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (vlen + (c.enc.length + tail.length))) ∗
            ((s0.sp - 248#64) ↦₃₂ 0#32) ∗ ((s0.sp - 244#64) ↦₃₂ 0#32) ∗
            ((s0.sp - 240#64) ↦₆₄ BitVec.ofNat 64 c.enc.length) ∗
            ((s0.sp - 232#64) ↦₆₄ BitVec.ofNat 64 vlen)) ∗
          ((ptr ↦ₛ (c.payload ++ tail)) ∗ stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
            memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 224#64) 128 ∗
            savedTail ∗ prostChainGAt A0 a ChainG.empty ∗ R) := by
        dsimp only [F_call] at hm2
        have hpool : A0.pool = emp := rfl
        have ha8 : (s0.sp - 248#64) + 8#64 = s0.sp - 240#64 := by bv_omega
        have ha16 : (s0.sp - 248#64) + 16#64 = s0.sp - 232#64 := by bv_omega
        rw [hsp1, hpool, ha8, ha16, hlen_sub, hlen_tot, pointsTo64_zero_split32_cme s0.sp] at hm2
        rw [stackAt_sub_to_varintSlice_cmeW (s0.sp - 256#64)]
        convert hm2 using 1; ac_rfl
      obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, hsp3, htr3, hvregs3, hx29_3, hx19_3, hx20_3, hx24_3, hx21_3, hx22_3, hx25_3, hx26_3, hent3⟩ | ⟨_, _hoom⟩⟩ :=
        (step_chainMerge_seg0_ge128_post_cme_placedW (H := H)
          a bufRef slot ptr s0.sp vlen c.enc tail
          (post := fun sm Pm =>
            sm.sp = s0.sp - 256#64 ∧ sm.trace = s2.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s2 ∧
            sm.readReg64 .x29 = s0.sp - 96#64 ∧
            sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧ sm.readReg64 .x24 = BitVec.ofNat 64 tail.length ∧
            sm.readReg64 .x21 = 98#64 ∧ sm.readReg64 .x22 = 97#64 ∧ sm.readReg64 .x25 = s0.sp - 248#64 ∧ sm.readReg64 .x26 = 1#64 ∧
            (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
              ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc ++ tail).length) ∗ memRegion (s0.sp - 248#64) 24))
          hlen_lt_v hpc2' hrun2 hsp2' hsp_align hx19_2 hx20_2 hx21_2 hx22_2 hx29_2
          (fun _ _ _ hsp' htr' hvregs' hx29' hx19' hx20' hx24' hx21' hx22' hx25' hx26' _ hent =>
            ⟨hsp', htr', hvregs', hx29', hx19', hx20', hx24', hx21', hx22', hx25', hx26', hent⟩)).elim
          hm2_post ((hst1.trans hst2).codeLoaded hL0)
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      have hm3' := Satisfies.mono (sepConj_mono_left hent3) hm3
      have hst_all := (hst1.trans hst2).trans hst3
      refine ⟨s3, hst_all, Or.inl ⟨hpc3, hrun3, (htr3.trans htr2).trans htr1, hvregs3.trans hvregs2,
        hcrl0.of_keepsFrozen hst_all.keepsFrozen,
        hsp3, by simp only [State.spAligned, hsp3, beq_iff_eq]; exact hsp_sub_align,
        hx29_3, hx19_3, hx20_3, hx24_3, hx21_3, hx22_3, hx25_3, hx26_3, hcOk, hlen_lt, ?_⟩⟩
      rw [hchain0, hdrop0]
      unfold sliceCursorAfter; rw [hlen_sub]
      have hsaved : chainMergeSavedRegs s0.sp s0 = memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 128 ∗ savedTail := by
        unfold chainMergeSavedRegs; rw [memRegion160_split_varint_cme s0.sp]; dsimp only [savedTail]; ac_rfl
      rw [hsaved]; convert hm3' using 1; ac_rfl
    · refine ⟨s2, hst1.trans hst2, Or.inr ⟨hpan2, ?_⟩⟩
      dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hm2_pan
      unfold Prost.X.decodeVarintSliceSpecW at hm2_pan
      dsimp only at hm2_pan
      exact allowPanic_frame_trace_cme htr1 hm2_pan
    · exact False.elim (not_satisfies_false_sepConj hm2_oom)

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG

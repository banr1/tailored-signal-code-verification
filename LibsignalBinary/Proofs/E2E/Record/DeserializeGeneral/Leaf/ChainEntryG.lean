/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.BodyDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Entry Segment Leaf (`chainEntryG_ok`) for General `message::merge<Chain>`

Proves `chainEntryG_ok` (`+0x000 → +0x120`, `k = 0`) for `prost::encoding::message::merge::<Chain>`
(`0x3974`), covering both the 1-byte (`< 128`) and multi-byte (`decode_varint_slice`) length paths.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

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

/-! ## Callee Offsets, Stack Splitting, and Varint Helpers -/

theorem decodeVarintSlice_ok_sub_cme {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : Prost.DecodeVarintSliceOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr chainMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))
      (Prost.decodeVarintSliceSpec A) := by
  have heq : (tripleRatchetProgAt b C ctl abs).fnAddr chainMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") =
      (tripleRatchetProgAt b C ctl abs).fnAddr Prost.decodeVarintSliceName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")]
    bv_omega
  rw [heq]; exact h

theorem stackAt_sub_to_varintSlice_cme (sp : BitVec 64) :
    stackAt sp chainMergeSubStack =
      memRegion (sp - BitVec.ofNat 64 chainMergeSubStack)
        (chainMergeSubStack - Prost.decodeVarintSliceStack) ∗
        stackAt sp Prost.decodeVarintSliceStack :=
  stackAt_sub_split_seedChain sp Prost.decodeVarintSliceStack chainMergeSubStack

theorem memRegion160_split_varint_cme (sp0 : BitVec 64) :
    memRegion (sp0 - 256#64) 160 =
      memRegion (sp0 - 256#64) 8 ∗
      memRegion (sp0 - 248#64) 24 ∗
      memRegion (sp0 - 224#64) 128 := by
  have h1 := memRegion_split (sp0 - 256#64) 8 152 (by decide)
  have h2 := memRegion_split (sp0 - 248#64) 24 128 (by decide)
  have ha1 : (sp0 - 256#64) + BitVec.ofNat 64 8 = sp0 - 248#64 := by bv_omega
  have ha2 : (sp0 - 248#64) + BitVec.ofNat 64 24 = sp0 - 224#64 := by bv_omega
  rw [show (8 : Nat) + 152 = 160 by decide, ha1] at h1
  rw [show (24 : Nat) + 128 = 152 by decide, ha2] at h2
  rw [h1, h2]

theorem pointsTo64_zero_split32_cme (sp0 : BitVec 64) :
    ((sp0 - 248#64) ↦₆₄ 0#64) =
      ((sp0 - 248#64) ↦₃₂ 0#32) ∗ ((sp0 - 244#64) ↦₃₂ 0#32) := by
  have hs := pointsTo64_split32 (sp0 - 248#64) 0#64
  have ha : (sp0 - 248#64) + 4#64 = sp0 - 244#64 := by bv_omega
  simpa [ha] using hs

theorem cells24_entails_memRegion24_cme (sp0 w1 w2 : BitVec 64) :
    ((sp0 - 248#64) ↦₃₂ 0#32) ∗ ((sp0 - 244#64) ↦₃₂ 0#32) ∗
      ((sp0 - 240#64) ↦₆₄ w1) ∗ ((sp0 - 232#64) ↦₆₄ w2) ⊢
    memRegion (sp0 - 248#64) 24 := by
  rw [← sepConj_assoc, ← pointsTo64_zero_split32_cme sp0]
  have h1 := memRegion_split (sp0 - 248#64) 8 16 (by decide)
  have h2 := memRegion_split (sp0 - 240#64) 8 8 (by decide)
  have ha1 : (sp0 - 248#64) + BitVec.ofNat 64 8 = sp0 - 240#64 := by bv_omega
  have ha2 : (sp0 - 240#64) + BitVec.ofNat 64 8 = sp0 - 232#64 := by bv_omega
  rw [show (8 : Nat) + 16 = 24 by decide, ha1] at h1
  rw [show (8 : Nat) + 8 = 16 by decide, ha2] at h2
  rw [h1, h2, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  exact sepConj_mono (Entails.sepExists_right 0#64 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (Entails.sepExists_right w2 (Entails.refl _)))

private theorem signExtend64_lsr56_of_gt_0x7f_cme (b0 : BitVec 8) (h : 0x7F < b0.toNat) :
    (b0.signExtend 64) >>> 56 = 0xff#64 := by
  revert b0 h; decide

theorem encodeVarint_ge128_cons_cme {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 32) :
    ∃ vtail : List (BitVec 8),
      encodeVarint (BitVec.ofNat 64 n) = BitVec.ofNat 8 (n % 128 + 128) :: vtail := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnlt : ¬ (BitVec.ofNat 64 n).toNat < 0x80 := by omega
  refine ⟨encodeVarintAux 9 (BitVec.ofNat 64 n >>> 7), ?_⟩
  unfold encodeVarint encodeVarintAux
  simp only [hnlt, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := n % 128) (by omega) 1
  simp only [Nat.reducePow, Nat.reduceMul] at hor
  have hand : (BitVec.ofNat 64 n &&& 0x7F).toNat = n % 128 := by
    rw [BitVec.toNat_and, htoNat, show (0x7F : BitVec 64).toNat = 127 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod n 7
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, hand,
    show (0x80 : BitVec 64).toNat = 128 from rfl, Nat.or_comm, ← hor, BitVec.toNat_ofNat]
  omega

theorem signExtend64_contByte_lsr56_cme (n : Nat) :
    (BitVec.signExtend 64 (BitVec.ofNat 8 (n % 128 + 128))) >>> 56 = 0xff#64 := by
  apply signExtend64_lsr56_of_gt_0x7f_cme
  rw [BitVec.toNat_ofNat]
  omega

theorem ult_10_of_gt_cme {n : Nat} (hgt : 10 < n) (hlt : n < 2 ^ 32) :
    (10#64).ult (BitVec.ofNat 64 n) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_true_eq]
  omega

theorem ule_10_of_gt_false_cme {n : Nat} (hgt : 10 < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).ule 10#64 = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

private theorem allocFailedIn_of_trace_eq_cme {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rwa [htr] at h

private theorem allowPanic_frame_trace_cme {s0 sm sf : State} {F R : SepProp}
    (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eq_cme htr) h

/-! ## Single-Byte Length Path (`body.length < 128`): `+0x000 → +0x120` -/

theorem step_chainMerge_seg0_1byte_cme (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (body tail : List (BitVec 8))
    (hbody_lt : body.length < 128)
    (hlen_lt : (1 + (body.length + tail.length)) < 2 ^ 32)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0)
    (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s0.readReg64 .x1 = a)
    (hx2 : s0.readReg64 .x2 = bufRef)
    (hx3 : (s0.readReg64 .x3).setWidth 32 = 99#32)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x29 = sp0 - 96#64 →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 →
      sm.readReg64 .x25 = sp0 - 248#64 →
      sm.readReg64 .x26 = 1#64 →
      ∀ Pm, (Pm ⊢
        (bufRef ↦₆₄ slot) ∗
          (ptr ↦₈ BitVec.ofNat 8 body.length) ∗
          sliceCursorAt slot (ptr + 1#64) (body ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack ∗
          chainMergeSavedRegs sp0 s0) →
      post sm Pm) :
    SepWP (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64) s0
      ((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (BitVec.ofNat 8 body.length :: (body ++ tail)) ∗
        stackAt sp0 chainMergeStack)
      post := by
  subst hsp
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x0 0x11c
  dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h1 : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = bufRef := hx2
  have hw3 : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 3#5)) = 99#32 := hx3
  have hw0 : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64 = 2#64 :=
    w0_and_255_eq_two_seedChain hx0
  have hlen_cons : (BitVec.ofNat 8 body.length :: (body ++ tail)).length < 2 ^ 32 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz := cbz_len_cons_false_seedChain hlen_cons
  have hse0 := signExtend64_ofNat8_lt128_seedChain hbody_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hbody_lt
  have hsub_len := len_cons_sub_one_seedChain (BitVec.ofNat 8 body.length) (body ++ tail)
  have hlen_append : (body ++ tail).length = body.length + tail.length := List.length_append
  have hule_sub := ule_ofNat_add_right_true_seedChain (m := body.length) (k := tail.length) (by omega)
  have hsub_tail := bv_ofNat_add_sub_left_seedChain body.length tail.length
  rw [stackAt_chainMergeStack_split_seedChain s0.sp]
  unfold sliceCursorAt
  rw [pointsToBytes_cons]
  simp only [sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w96
  apply SepWP.exists_elim; intro w88
  apply SepWP.exists_elim; intro w80
  apply SepWP.exists_elim; intro w72
  apply SepWP.exists_elim; intro w64
  apply SepWP.exists_elim; intro w56
  apply SepWP.exists_elim; intro w48
  apply SepWP.exists_elim; intro w40
  apply SepWP.exists_elim; intro w32
  apply SepWP.exists_elim; intro w24
  apply SepWP.exists_elim; intro w16
  apply SepWP.exists_elim; intro w8
  iterate 31 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) _ ?_
  unfold sliceCursorAt chainMergeSavedRegs
  rw [← hlen_append]
  exact sep_ac_seedChain (by ac_rfl)

/-! ## Multi-Byte Length Path (`128 ≤ body.length`): `+0x000 → +0x098 → +0x120` -/

theorem step_chainMerge_seg0_ge128_pre_cme (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (n : Nat) (rest0 : List (BitVec 8))
    (hgt10 : 10 < (BitVec.ofNat 8 (n % 128 + 128) :: rest0).length)
    (hlen_lt : (BitVec.ofNat 8 (n % 128 + 128) :: rest0).length < 2 ^ 32)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0)
    (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s0.readReg64 .x1 = a)
    (hx2 : s0.readReg64 .x2 = bufRef)
    (hx3 : (s0.readReg64 .x3).setWidth 32 = 99#32)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x9c#64 →
      sm.readReg64 .x0 = sp0 - 248#64 →
      sm.readReg64 .x1 = ptr →
      sm.readReg64 .x2 = BitVec.ofNat 64 (BitVec.ofNat 8 (n % 128 + 128) :: rest0).length →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = slot →
      sm.readReg64 .x22 = 99#64 →
      sm.readReg64 .x29 = sp0 - 96#64 →
      ∀ Pm, (Pm ⊢
        (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr (BitVec.ofNat 8 (n % 128 + 128) :: rest0) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack ∗
          chainMergeSavedRegs sp0 s0) →
      post sm Pm) :
    SepWP (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) s0
      ((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (BitVec.ofNat 8 (n % 128 + 128) :: rest0) ∗
        stackAt sp0 chainMergeStack)
      post := by
  subst hsp
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x0 0x48
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x7c 0x98
  dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h1 : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = bufRef := hx2
  have hw3 : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 3#5)) = 99#32 := hx3
  have hw0 : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64 = 2#64 :=
    w0_and_255_eq_two_seedChain hx0
  have hcbz := cbz_len_cons_false_seedChain hlen_lt
  have hlsr56 := signExtend64_contByte_lsr56_cme n
  have hhi10 := ult_10_of_gt_cme hgt10 hlen_lt
  have hule10 := ule_10_of_gt_false_cme hgt10 hlen_lt
  rw [stackAt_chainMergeStack_split_seedChain s0.sp]
  unfold sliceCursorAt
  rw [pointsToBytes_cons]
  simp only [sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w96
  apply SepWP.exists_elim; intro w88
  apply SepWP.exists_elim; intro w80
  apply SepWP.exists_elim; intro w72
  apply SepWP.exists_elim; intro w64
  apply SepWP.exists_elim; intro w56
  apply SepWP.exists_elim; intro w48
  apply SepWP.exists_elim; intro w40
  apply SepWP.exists_elim; intro w32
  apply SepWP.exists_elim; intro w24
  apply SepWP.exists_elim; intro w16
  apply SepWP.exists_elim; intro w8
  iterate 24 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) _ ?_
  unfold sliceCursorAt chainMergeSavedRegs
  rw [pointsToBytes_cons]
  exact sep_ac_seedChain (by ac_rfl)

theorem step_chainMerge_seg0_ge128_post_cme (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (vlen : Nat) (body tail : List (BitVec 8))
    (hlen_lt : (vlen + (body.length + tail.length)) < 2 ^ 32)
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x9c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64)
    (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = bufRef)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = slot)
    (hx22 : s.readReg64 .x22 = 99#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      sm.trace = s.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x29 = sp0 - 96#64 →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x21 = 98#64 →
      sm.readReg64 .x22 = 97#64 →
      sm.readReg64 .x25 = sp0 - 248#64 →
      sm.readReg64 .x26 = 1#64 →
      ∀ Pm, (Pm ⊢
        (bufRef ↦₆₄ slot) ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length) ∗
          memRegion (sp0 - 248#64) 24) →
      post sm Pm) :
    SepWP (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64) s
      ((bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ ptr) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (vlen + (body.length + tail.length))) ∗
        ((sp0 - 248#64) ↦₃₂ 0#32) ∗
        ((sp0 - 244#64) ↦₃₂ 0#32) ∗
        ((sp0 - 240#64) ↦₆₄ BitVec.ofNat 64 body.length) ∗
        ((sp0 - 232#64) ↦₆₄ BitVec.ofNat 64 vlen))
      post := by
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by
    rw [hsp]; exact sp_sub_256_aligned_seedChain hsp_align
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x9c 0xa0
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0xac 0xdc
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x110 0x11c
  dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = slot := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = 99#64 := hx22
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 96#64 := hx29
  have hlen_append : (body ++ tail).length = body.length + tail.length := List.length_append
  have hsub_vlen := bv_ofNat_add_sub_left_seedChain vlen (body.length + tail.length)
  have hult_vlen := ult_ofNat_add_left_false_seedChain (m := vlen) (k := body.length + tail.length) hlen_lt
  have hule_vlen := ule_ofNat_add_right_true_seedChain (m := vlen) (k := body.length + tail.length) hlen_lt
  have hsub_tail := bv_ofNat_add_sub_left_seedChain body.length tail.length
  have hule_sub := ule_ofNat_add_right_true_seedChain (m := body.length) (k := tail.length) (by omega)
  have hult_sub := ult_ofNat_add_left_false_seedChain (m := body.length) (k := tail.length) (by omega)
  iterate 19 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [hsp, arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [h29, arm64_norm]) (by simp only [h19, arm64_norm])
    (by simp only [h20, arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) _ ?_
  have hcells := cells24_entails_memRegion24_cme sp0
    (BitVec.ofNat 64 body.length) (BitVec.ofNat 64 vlen)
  rw [← hlen_append]
  have hEq1 :
      bufRef ↦₆₄ slot ∗
        slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length ∗
            (sp0 - 248#64) ↦₃₂ 0#32 ∗
              (sp0 - 244#64) ↦₃₂ 0#32 ∗
                (sp0 - 240#64) ↦₆₄ BitVec.ofNat 64 body.length ∗
                  (sp0 - 232#64) ↦₆₄ BitVec.ofNat 64 vlen =
      (((sp0 - 248#64) ↦₃₂ 0#32) ∗ ((sp0 - 244#64) ↦₃₂ 0#32) ∗
        ((sp0 - 240#64) ↦₆₄ BitVec.ofNat 64 body.length) ∗
        ((sp0 - 232#64) ↦₆₄ BitVec.ofNat 64 vlen)) ∗
      ((bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length)) := by ac_rfl
  have hEq2 :
      memRegion (sp0 - 248#64) 24 ∗
        ((bufRef ↦₆₄ slot) ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length)) =
      (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (body ++ tail).length) ∗
        memRegion (sp0 - 248#64) 24 := by ac_rfl
  rw [hEq1, ← hEq2]
  exact sepConj_mono_left hcells

/-! ## Main Entry Proof (`chainEntryG_ok`) -/

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

theorem chainEntryG_ok_impl (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (recordProg C ctl abs).fnAddr chainMergeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ chainMergeGenSpec.pre x s0 ∗ R) (hal : s0.spAligned = true) :
    ChainStepG C ctl x R s0 s0 (ChainLoopG C ctl x R s0 0) abs := by
  intro hL0
  rcases x with ⟨a, c, bufRef, slot, ptr, tail⟩
  dsimp only [chainMergeGenSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hcOk, hlen_lt, hF0, hsym0⟩, hmem⟩
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hal
  have hsp_sub_align : (s0.sp - 256#64) &&& 15#64 = 0#64 :=
    sp_sub_256_aligned_seedChain hsp_align
  have hdrop0 : ((c.fields.drop 0).flatMap ChainField.enc) = c.enc := by
    rw [List.drop_zero, ← chainG_enc_eq_fields_cme c]
  have hchain0 : chainGAfter c 0 = ChainG.empty := rfl
  by_cases hbody_lt : c.enc.length < 128
  · have hvar : encodeVarint (BitVec.ofNat 64 c.enc.length) = [BitVec.ofNat 8 c.enc.length] :=
      encodeVarint_lt128_seedChain c.enc.length hbody_lt
    have hpay : c.payload ++ tail = BitVec.ofNat 8 c.enc.length :: (c.enc ++ tail) := by
      unfold ChainG.payload
      rw [hvar, List.singleton_append, List.cons_append]
    have hlen_lt1 : (1 + (c.enc.length + tail.length)) < 2 ^ 32 := by
      rw [hpay, List.length_cons, List.length_append] at hlen_lt
      omega
    have hmem1 : s0.mem ⊨
        ((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr (BitVec.ofNat 8 c.enc.length :: (c.enc ++ tail)) ∗
          stackAt s0.sp chainMergeStack) ∗
        (prostChainGAt A0 a ChainG.empty ∗ R) := by
      rw [← hpay]
      convert hmem using 1; ac_rfl
    obtain ⟨sm, hst, ⟨hpcm, hrunm, Pm, hmm,
      hspm, htrm, hvregsm, hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m, hent⟩ | ⟨_, _hoom⟩⟩ :=
      (step_chainMerge_seg0_1byte_cme C ctl a bufRef slot ptr s0.sp c.enc tail
        (post := fun sm Pm =>
          sm.sp = s0.sp - 256#64 ∧ sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x19 = bufRef ∧
          sm.readReg64 .x20 = a ∧ sm.readReg64 .x24 = BitVec.ofNat 64 tail.length ∧
          sm.readReg64 .x21 = 98#64 ∧ sm.readReg64 .x22 = 97#64 ∧
          sm.readReg64 .x25 = s0.sp - 248#64 ∧ sm.readReg64 .x26 = 1#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗
            (ptr ↦₈ BitVec.ofNat 8 c.enc.length) ∗
            sliceCursorAt slot (ptr + 1#64) (c.enc ++ tail) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStack ∗
            chainMergeSavedRegs s0.sp s0))
        hbody_lt hlen_lt1 hpc hrun rfl hsp_align hx0 hx1 hx2 hx3
        (fun _ _ _ hsp' htr' hvregs' hx29' hx19' hx20' hx24' hx21' hx22' hx25' hx26' _ hent =>
          ⟨hsp', htr', hvregs', hx29', hx19', hx20', hx24', hx21', hx22', hx25', hx26', hent⟩)).elim
        hmem1 hL0
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hmm' := Satisfies.mono (sepConj_mono_left hent) hmm
    refine ⟨sm, hst, Or.inl ?_⟩
    refine ⟨hpcm, hrunm, htrm, hvregsm, hst.symtab_eq.trans hsym0, hst.frozenLoaded hF0,
      hspm, ?_, hx29m, hx19m, hx20m, hx24m, hx21m, hx22m, hx25m, hx26m,
      hcOk, hlen_lt, ?_⟩
    · simp only [State.spAligned, hspm, beq_iff_eq]
      exact hsp_sub_align
    · rw [hchain0, hdrop0, hpay]
      have hcur := sliceCursorAfter_append_eq_seedChain slot ptr [BitVec.ofNat 8 c.enc.length] (c.enc ++ tail)
      rw [List.singleton_append] at hcur
      rw [hcur]
      simp only [List.length_singleton, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
      convert hmm' using 1; ac_rfl
  · have hbody_ge : 128 ≤ c.enc.length := by omega
    have hbody_lt32 : c.enc.length < 2 ^ 32 := by
      unfold ChainG.payload at hlen_lt
      simp only [List.length_append] at hlen_lt
      omega
    obtain ⟨vtail, hvar⟩ := encodeVarint_ge128_cons_cme hbody_ge hbody_lt32
    let b0 := BitVec.ofNat 8 (c.enc.length % 128 + 128)
    let rest0 := vtail ++ (c.enc ++ tail)
    have hpay : c.payload ++ tail = b0 :: rest0 := by
      unfold ChainG.payload
      dsimp only [b0, rest0]
      rw [hvar, List.cons_append, List.cons_append, List.append_assoc]
    have hgt10 : 10 < (b0 :: rest0).length := by
      rw [← hpay]
      unfold ChainG.payload
      simp only [List.length_append]
      omega
    have hlen_lt0 : (b0 :: rest0).length < 2 ^ 32 := by
      rw [← hpay]; exact hlen_lt
    have hmem1 : s0.mem ⊨
        ((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr (b0 :: rest0) ∗
          stackAt s0.sp chainMergeStack) ∗
        (prostChainGAt A0 a ChainG.empty ∗ R) := by
      rw [← hpay]
      convert hmem using 1; ac_rfl
    obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1,
      hsp1, htr1, hvregs1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1, hx29_1, hent1⟩ | ⟨_, _hoom⟩⟩ :=
      (step_chainMerge_seg0_ge128_pre_cme C ctl a bufRef slot ptr s0.sp c.enc.length rest0
        (post := fun sm Pm =>
          sm.sp = s0.sp - 256#64 ∧ sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x9c#64 ∧
          sm.readReg64 .x0 = s0.sp - 248#64 ∧ sm.readReg64 .x1 = ptr ∧
          sm.readReg64 .x2 = BitVec.ofNat 64 (b0 :: rest0).length ∧
          sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧
          sm.readReg64 .x21 = slot ∧ sm.readReg64 .x22 = 99#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot ptr (b0 :: rest0) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStack ∗
            chainMergeSavedRegs s0.sp s0))
        hgt10 hlen_lt0 hpc hrun rfl hsp_align hx0 hx1 hx2 hx3
        (fun _ _ _ hsp' htr' hvregs' hlr' hx0' hx1' hx2' hx19' hx20' hx21' hx22' hx29' _ hent =>
          ⟨hsp', htr', hvregs', hlr', hx0', hx1', hx2', hx19', hx20', hx21', hx22', hx29', hent⟩)).elim
        hmem1 hL0
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hm1' := Satisfies.mono (sepConj_mono_left hent1) hm1
    have hal1 : s1.spAligned = true := by
      simp only [State.spAligned, hsp1, beq_iff_eq]
      exact hsp_sub_align
    have hx2_1_nat : (s1.readReg64 .x2).toNat = (c.payload ++ tail).length := by
      rw [hx2_1, ← hpay, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpre_slice : Prost.VarintSlicePre (c.payload ++ tail) := by
      refine Or.inl ?_
      rw [hpay]; omega
    let gvar : Prost.DecodeVarintSliceGhost := ⟨s0.sp - 248#64, ptr, c.payload ++ tail⟩
    let savedTail : SepProp :=
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
    let F_call : SepProp :=
      (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.payload ++ tail).length) ∗
      memRegion (s0.sp - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
        (chainMergeSubStack - Prost.decodeVarintSliceStack) ∗
      memRegion (s0.sp - 256#64) 8 ∗
      memRegion (s0.sp - 224#64) 128 ∗
      savedTail ∗
      prostChainGAt A0 a ChainG.empty
    have hm1_call : s1.mem ⊨ (Prost.decodeVarintSliceSpec A0).pre gvar s1 ∗ (F_call ∗ R) := by
      unfold Prost.decodeVarintSliceSpec; dsimp only [gvar]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, hx1_1, hx2_1_nat, Nat.lt_of_lt_of_le hlen_lt (by decide), hpre_slice⟩, ?_⟩
      have hsaved : chainMergeSavedRegs s0.sp s0 =
          memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 24 ∗
            memRegion (s0.sp - 224#64) 128 ∗ savedTail := by
        unfold chainMergeSavedRegs
        rw [memRegion160_split_varint_cme s0.sp]
        dsimp only [savedTail]
        ac_rfl
      rw [← hpay, stackAt_sub_to_varintSlice_cme (s0.sp - 256#64), hsaved] at hm1'
      unfold sliceCursorAt at hm1'
      have hpool : A0.pool = emp := rfl
      rw [hsp1, hpool]
      dsimp only [F_call]
      convert hm1' using 1; ac_rfl
    have hsub_varint := decodeVarintSlice_ok_sub_cme hC.1
    obtain ⟨s2, hst2, hpost2, -⟩ :=
      hsub_varint.no_fault_before_outcome gvar (F_call ∗ R) s1 hpc1 hrun1 hm1_call hal1 (hst1.codeLoaded hL0)
    rcases hpost2 with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hm2⟩ | ⟨hpan2, hm2_pan⟩ | ⟨code, _, hm2_ex⟩ | ⟨_, hoom2⟩
    · have hpc2' : s2.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x9c#64 := by
        rw [hpc2, hlr1]
      have hsp2' : s2.sp = s0.sp - 256#64 := by rw [hsp2, hsp1]
      have hx19_2 : s2.readReg64 .x19 = bufRef := hcs2.1.trans hx19_1
      have hx20_2 : s2.readReg64 .x20 = a := hcs2.2.1.trans hx20_1
      have hx21_2 : s2.readReg64 .x21 = slot := hcs2.2.2.1.trans hx21_1
      have hx22_2 : s2.readReg64 .x22 = 99#64 := hcs2.2.2.2.1.trans hx22_1
      have hx29_2 : s2.readReg64 .x29 = s0.sp - 96#64 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
      have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s1 := hcs2.2.2.2.2.2.2.2.2.2.2.2
      let vlen := (encodeVarint (BitVec.ofNat 64 c.enc.length)).length
      have hpay_split : c.payload ++ tail =
          encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.enc ++ tail) := by
        unfold ChainG.payload; rw [List.append_assoc]
      have hdec : decodeVarint (c.payload ++ tail) =
          some (BitVec.ofNat 64 c.enc.length, c.enc ++ tail) := by
        rw [hpay_split]
        exact decodeVarint_encodeVarint (BitVec.ofNat 64 c.enc.length) (c.enc ++ tail)
      have hlen_sub : (c.payload ++ tail).length - (c.enc ++ tail).length = vlen := by
        rw [hpay_split, List.length_append, Nat.add_sub_cancel_right]
      have hlen_tot : (c.payload ++ tail).length = vlen + (c.enc.length + tail.length) := by
        rw [hpay_split, List.length_append, List.length_append]
      have hlen_lt_v : (vlen + (c.enc.length + tail.length)) < 2 ^ 32 := by
        rw [← hlen_tot]; exact hlen_lt
      unfold Prost.decodeVarintSliceSpec at hm2; dsimp only [gvar] at hm2
      rw [hdec] at hm2; dsimp only [Prost.varintSliceResultAt] at hm2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
      rcases hm2 with ⟨htr2, hm2⟩
      have hm2_post : s2.mem ⊨
          ((bufRef ↦₆₄ slot) ∗
            (slot ↦₆₄ ptr) ∗
            ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (vlen + (c.enc.length + tail.length))) ∗
            ((s0.sp - 248#64) ↦₃₂ 0#32) ∗
            ((s0.sp - 244#64) ↦₃₂ 0#32) ∗
            ((s0.sp - 240#64) ↦₆₄ BitVec.ofNat 64 c.enc.length) ∗
            ((s0.sp - 232#64) ↦₆₄ BitVec.ofNat 64 vlen)) ∗
          ((ptr ↦ₛ (c.payload ++ tail)) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStack ∗
            memRegion (s0.sp - 256#64) 8 ∗
            memRegion (s0.sp - 224#64) 128 ∗
            savedTail ∗
            prostChainGAt A0 a ChainG.empty ∗ R) := by
        dsimp only [F_call] at hm2
        have hpool : A0.pool = emp := rfl
        have ha8 : (s0.sp - 248#64) + 8#64 = s0.sp - 240#64 := by bv_omega
        have ha16 : (s0.sp - 248#64) + 16#64 = s0.sp - 232#64 := by bv_omega
        rw [hsp1, hpool, ha8, ha16, hlen_sub, hlen_tot, pointsTo64_zero_split32_cme s0.sp] at hm2
        rw [stackAt_sub_to_varintSlice_cme (s0.sp - 256#64)]
        convert hm2 using 1; ac_rfl
      obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3,
        hsp3, htr3, hvregs3, hx29_3, hx19_3, hx20_3, hx24_3, hx21_3, hx22_3, hx25_3, hx26_3, hent3⟩ | ⟨_, _hoom⟩⟩ :=
        (step_chainMerge_seg0_ge128_post_cme C ctl a bufRef slot ptr s0.sp vlen c.enc tail
          (post := fun sm Pm =>
            sm.sp = s0.sp - 256#64 ∧ sm.trace = s2.trace ∧
            calleeSavedVRegs sm = calleeSavedVRegs s2 ∧
            sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x19 = bufRef ∧
            sm.readReg64 .x20 = a ∧ sm.readReg64 .x24 = BitVec.ofNat 64 tail.length ∧
            sm.readReg64 .x21 = 98#64 ∧ sm.readReg64 .x22 = 97#64 ∧
            sm.readReg64 .x25 = s0.sp - 248#64 ∧ sm.readReg64 .x26 = 1#64 ∧
            (Pm ⊢ (bufRef ↦₆₄ slot) ∗
              (slot ↦₆₄ (ptr + BitVec.ofNat 64 vlen)) ∗
              ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc ++ tail).length) ∗
              memRegion (s0.sp - 248#64) 24))
          hlen_lt_v hpc2' hrun2 hsp2' hsp_align hx19_2 hx20_2 hx21_2 hx22_2 hx29_2
          (fun _ _ _ hsp' htr' hvregs' hx29' hx19' hx20' hx24' hx21' hx22' hx25' hx26' _ hent =>
            ⟨hsp', htr', hvregs', hx29', hx19', hx20', hx24', hx21', hx22', hx25', hx26', hent⟩)).elim
          hm2_post ((hst1.trans hst2).codeLoaded hL0)
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      have hm3' := Satisfies.mono (sepConj_mono_left hent3) hm3
      have hst_all := (hst1.trans hst2).trans hst3
      refine ⟨s3, hst_all, Or.inl ?_⟩
      refine ⟨hpc3, hrun3, (htr3.trans htr2).trans htr1, (hvregs3.trans hvregs2).trans hvregs1, hst_all.symtab_eq.trans hsym0,
        hst_all.frozenLoaded hF0, hsp3, ?_, hx29_3, hx19_3, hx20_3, hx24_3,
        hx21_3, hx22_3, hx25_3, hx26_3, hcOk, hlen_lt, ?_⟩
      · simp only [State.spAligned, hsp3, beq_iff_eq]
        exact hsp_sub_align
      · rw [hchain0, hdrop0]
        unfold sliceCursorAfter
        rw [hlen_sub]
        have hsaved : chainMergeSavedRegs s0.sp s0 =
            memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 24 ∗
              memRegion (s0.sp - 224#64) 128 ∗ savedTail := by
          unfold chainMergeSavedRegs
          rw [memRegion160_split_varint_cme s0.sp]
          dsimp only [savedTail]
          ac_rfl
        rw [hsaved]
        convert hm3' using 1; ac_rfl
    · refine ⟨s2, hst1.trans hst2, Or.inr ⟨hpan2, ?_⟩⟩
      unfold Prost.decodeVarintSliceSpec at hm2_pan; dsimp only at hm2_pan
      have hm2_pan' : s2.mem ⊨
          ((⌜allocFailedIn s1 s2 ∧ s1.trace <+: s2.trace⌝ ∗ anyHeap) ∗ F_call) ∗ R := by
        convert hm2_pan using 1; ac_rfl
      exact allowPanic_frame_trace_cme htr1 hm2_pan'
    · exact False.elim (not_satisfies_false_sepConj hm2_ex)
    · exact False.elim (not_satisfies_false_sepConj hoom2)

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG

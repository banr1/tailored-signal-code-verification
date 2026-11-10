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
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Prologue and Ratchet-Key Segments for Seed `message::merge<Chain>`

Proves the entry and ratchet-key segment lemmas for `prost::encoding::message::merge::<Chain>`
(`0x3974`, block `11`):
* Segment 0 (`+0x000 → +0x120`): prologue and outer 1-byte length varint.
* Segment 1 (`+0x120 → +0x120`): outer field `1` (`sender_ratchet_key` via `bytes::merge`).
* Segment 2 (`+0x120 → +0x120`): optional outer field `2` (`sender_ratchet_key_private` via `bytes::merge`).
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

namespace ChainMergeStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre_seedChain (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

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
  have h1 : v.getLsbD 63 = decide (9223372036854775808 ≤ v.toNat) := by
    rw [show (63 : Nat) = 64 - 1 from rfl, ← BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_toNat]
  have h2 : (v >>> 56).ult 128#64 = decide (v.toNat < 9223372036854775808) := by
    simp only [BitVec.ult, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, decide_eq_decide]
    omega
  rw [h1, h2, ← decide_not]
  simp only [decide_eq_decide]
  omega

end ChainMergeStateSimp

/-! ## BitVec Branch and Arithmetic Helpers -/

theorem sep_ac_seedChain {P Q : SepProp} (h : P = Q) : P ⊢ Q := by
  rw [h]; exact Entails.refl Q

theorem w0_and_255_eq_two_seedChain {w : BitVec 64} (h : w.setWidth 8 = 2#8) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 w) &&& 255#64 = 2#64 := by
  apply BitVec.eq_of_toNat_eq
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
    BitVec.toNat_and, BitVec.toNat_ofNat] at h' ⊢
  rw [show 255 % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem ofNat8_le_0x7f_seedChain {n : Nat} (hn : n < 128) :
    BitVec.ofNat 8 n ≤ 0x7f#8 := by
  rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  change n ≤ 127
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

theorem ult_ofNat_add_left_false_seedChain {m k : Nat} (hlt : m + k < 2 ^ 32) :
    (BitVec.ofNat 64 (m + k)).ult (BitVec.ofNat 64 m) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

theorem ule_ofNat_add_right_true_seedChain {m k : Nat} (hlt : m + k < 2 ^ 32) :
    (BitVec.ofNat 64 m).ule (BitVec.ofNat 64 (m + k)) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_true_eq]
  omega

theorem ule_ofNat_of_gt_false_seedChain {n k : Nat} (hgt : k < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 k) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

theorem ult_ofNat_of_gt_true_seedChain {n k : Nat} (hgt : k < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 k).ult (BitVec.ofNat 64 n) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    decide_eq_true_eq]
  omega

/-! ## Prologue and Outer Length Varint (`+0x000 → +0x120`) -/

theorem step_chainMerge_seg0_seedChain (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (body tail : List (BitVec 8))
    (hbody_lt : body.length < 128)
    (hlen_lt : (1 + (body.length + tail.length)) < 2 ^ 32)
    {ret : BitVec 64} {s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0)
    (hsp_align : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s0.readReg64 .x1 = a)
    (hx2 : s0.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .lr = s0.readReg64 .lr →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x26 = 1#64 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          (ptr ↦₈ BitVec.ofNat 8 body.length) ∗
          sliceCursorAt slot (ptr + 1#64) (body ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack ∗
          chainMergeSavedRegs sp0 s0) ∗ F)
        Q Qp) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (BitVec.ofNat 8 body.length :: (body ++ tail)) ∗
        stackAt sp0 chainMergeStack) ∗ F)
      Q Qp := by
  subst hsp
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x0 0x11c
  dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h1 : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = bufRef := hx2
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
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (288)) hF hsym ?_
  rw [stackAt_chainMergeStack_split_seedChain s0.sp]
  unfold sliceCursorAt
  rw [pointsToBytes_cons]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
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
  intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) hF1 hsym1 (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]))
  unfold sliceCursorAt chainMergeSavedRegs
  rw [← hlen_append]
  exact sep_ac_seedChain (by ac_rfl)

/-! ## Outer Field `1`: `sender_ratchet_key` (`+0x120 → +0x120`) -/

theorem pbBytes_lt128_eq_seedChain (tag : Nat) (_htag : tag < 16)
    (b : List (BitVec 8)) (_hb : b.length < 128) :
    pbBytes tag b = BitVec.ofNat 8 (tag * 8 + 2) :: BitVec.ofNat 8 b.length :: b :=
  rfl

theorem pbBytes_pointsTo_combine_seedChain (tag : Nat) (htag : tag < 16)
    (ptr : BitVec 64) (b : List (BitVec 8)) (hb : b.length < 128) :
    (ptr ↦₈ BitVec.ofNat 8 (tag * 8 + 2)) ∗ ((ptr + 1#64) ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) =
      (ptr ↦ₛ pbBytes tag b) := by
  rw [pbBytes_lt128_eq_seedChain tag htag b hb, pointsToBytes_cons]
  rfl

theorem pbBytes_ptr_advance_seedChain (tag : Nat) (htag : tag < 16)
    (ptr : BitVec 64) (b : List (BitVec 8)) (hb : b.length < 128) :
    ptr + 1#64 + BitVec.ofNat 64 (b.length + 1) =
      ptr + BitVec.ofNat 64 (pbBytes tag b).length := by
  rw [pbBytes_lt128_eq_seedChain tag htag b hb]
  simp only [List.length_cons]
  bv_omega

theorem step_chainMerge_seg1_seedChain (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hBM : Prost.BytesMergeOk sessionImg0 C A0 ctl abs)
    (a bufRef slot ptr sp0 : BitVec 64)
    (srk rest tail : List (BitVec 8))
    (hsrk_lt : srk.length < 128)
    (hlen_lt : (pbBytes 1 srk ++ rest ++ tail).length < 2 ^ 32)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x26 = s0.readReg64 .x26 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 a srk ∗
          (ptr ↦ₛ pbBytes 1 srk) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 1 srk).length) (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 a [] ∗
        sliceCursorAt slot ptr (pbBytes 1 srk ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R)) := by
  have hpb : pbBytes 1 srk = 0x0a#8 :: BitVec.ofNat 8 srk.length :: srk :=
    pbBytes_lt128_eq_seedChain 1 (by decide) srk hsrk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)
  have hcons_eq : pbBytes 1 srk ++ (rest ++ tail) = 0x0a#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x0a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x0a#8 :: rem1).length < 2 ^ 32 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x0a#8 rem1
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
      s1.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x25c#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a →
      s1.readReg64 .x2 = bufRef →
      s1.readReg64 .x19 = bufRef →
      s1.readReg64 .x20 = a →
      s1.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      s1.readReg64 .x26 = s0.readReg64 .x26 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s1
        ((vecU8 A0 a [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x0a#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R))) → _) ?_
  · intro hnext1
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x120 0x144
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x188 0x1b4
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x24c 0x258
    dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext1 ⊢
    generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
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
      (by simp only [h24, arm64_norm])
      (by simp only [arm64_norm]))
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx24_1 hx26_1
    have hrem1_lt : ([BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)).length < 2 ^ 32 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_seedChain C ctl hBM
      a bufRef slot (ptr + 1#64) sp0
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x25c#64)
      [] srk (rest ++ tail) hsrk_lt hrem1_lt
      hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
    chainMerge_fetches_range sessionImg0.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x25c 0x260
    dsimp only [tripleRatchetProgAt, chainMergeName] at hpc2 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (288)) hF2 hsym2 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
    have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
    have h26_2 : s2.readReg64 (Reg.gpr 26#5) = s0.readReg64 .x26 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
    have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm])
      (by simp only [hvregs_2, arm64_norm])
      (by simp only [h19_2, arm64_norm])
      (by simp only [h20_2, arm64_norm])
      (by simp only [h24_2, arm64_norm])
      (by simp only [h26_2, arm64_norm]))
    rw [pbBytes_ptr_advance_seedChain 1 (by decide) ptr srk hsrk_lt,
      ← pbBytes_pointsTo_combine_seedChain 1 (by decide) ptr srk hsrk_lt]
    exact sep_ac_seedChain (by ac_rfl)

/-! ## Optional Outer Field `2`: `sender_ratchet_key_private` (`+0x120 → +0x120`) -/

theorem step_chainMerge_seg2_seedChain (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hBM : Prost.BytesMergeOk sessionImg0 C A0 ctl abs)
    (a bufRef slot ptr sp0 : BitVec 64)
    (priv rest tail : List (BitVec 8))
    (hpriv : priv = [] ∨ priv.length = 32)
    (hlen_lt : ((if priv = [] then [] else pbBytes 2 priv) ++ rest ++ tail).length < 2 ^ 32)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x26 = s0.readReg64 .x26 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          (ptr ↦ₛ (if priv = [] then [] else pbBytes 2 priv)) ∗
          sliceCursorAt slot
            (ptr + BitVec.ofNat 64 (if priv = [] then [] else pbBytes 2 priv).length)
            (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x18#64) [] ∗
        sliceCursorAt slot ptr ((if priv = [] then [] else pbBytes 2 priv) ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R)) := by
  rcases hpriv with rfl | hpriv_len
  · simp only [ite_true, List.nil_append, List.length_nil,
      BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    refine SepWPp.mono_pre_seedChain ?_ (hnext s0 hpc hrun hsp hF hsym htr hvregs hx19 hx20 hx24 rfl)
    exact sep_ac_seedChain (by ac_rfl)
  · have hpriv_ne : priv ≠ [] := by intro h; subst h; simp at hpriv_len
    have hpriv_lt : priv.length < 128 := by omega
    simp only [hpriv_ne, ↓reduceIte] at hlen_lt hnext ⊢
    have hpb : pbBytes 2 priv = 0x12#8 :: BitVec.ofNat 8 priv.length :: priv :=
      pbBytes_lt128_eq_seedChain 2 (by decide) priv hpriv_lt
    let rem1 : List (BitVec 8) := [BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)
    have hcons_eq : pbBytes 2 priv ++ (rest ++ tail) = 0x12#8 :: rem1 := by
      rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
    have hlen_gt : tail.length < (0x12#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 32 := by
      rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
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
        s1.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x1d0#64 →
        (s1.readReg64 .x0).setWidth 8 = 2#8 →
        s1.readReg64 .x1 = a + 0x18#64 →
        s1.readReg64 .x2 = bufRef →
        s1.readReg64 .x19 = bufRef →
        s1.readReg64 .x20 = a →
        s1.readReg64 .x24 = BitVec.ofNat 64 tail.length →
        s1.readReg64 .x26 = s0.readReg64 .x26 →
        SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s1
          ((vecU8 A0 (a + 0x18#64) [] ∗
            (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot (ptr + 1#64) rem1 ∗
            stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x12#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s_init sf ∗ R))) → _) ?_
    · intro hnext1
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x120 0x144
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x188 0x1cc
      dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext1 ⊢
      generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
      have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
      have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))) hF hsym ?_
      rw [hcons_eq]
      unfold sliceCursorAt
      rw [pointsToBytes_cons]
      simp only [sepConj_assoc]
      iterate 28 wp_step
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
        (by simp only [h24, arm64_norm])
        (by simp only [arm64_norm]))
      unfold sliceCursorAt
      exact sep_ac_seedChain (by ac_rfl)
    · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx24_1 hx26_1
      have hrem1_lt : ([BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)).length < 2 ^ 32 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_bytesMerge_seedChain C ctl hBM
        (a + 0x18#64) bufRef slot (ptr + 1#64) sp0
        ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x1d0#64)
        [] priv (rest ++ tail) hpriv_lt hrem1_lt
        hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
      intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x1d0 0x1d0
      chainMerge_fetches_range sessionImg0.base
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x260 0x260
      dsimp only [tripleRatchetProgAt, chainMergeName] at hpc2 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (288)) hF2 hsym2 ?_
      iterate 2 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
      have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
      have h26_2 : s2.readReg64 (Reg.gpr 26#5) = s0.readReg64 .x26 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm])
        (by simp only [hvregs_2, arm64_norm])
        (by simp only [h19_2, arm64_norm])
        (by simp only [h20_2, arm64_norm])
        (by simp only [h24_2, arm64_norm])
        (by simp only [h26_2, arm64_norm]))
      rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr priv hpriv_lt,
        ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr priv hpriv_lt]
      exact sep_ac_seedChain (by ac_rfl)

/-! ## Relocatable `[LibsignalPlacement]` Segments (`lsProg_11 H`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem step_chainMerge_seg0_placed_seedChain [LibsignalPlacement]
    {H : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (body tail : List (BitVec 8))
    (hbody_lt : body.length < 128)
    (hlen_lt : (1 + (body.length + tail.length)) < 2 ^ 32)
    {ret : BitVec 64} {s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0)
    (hsp_align : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s0.readReg64 .x1 = a)
    (hx2 : s0.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .lr = s0.readReg64 .lr →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x26 = 1#64 →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          (ptr ↦₈ BitVec.ofNat 8 body.length) ∗
          sliceCursorAt slot (ptr + 1#64) (body ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack ∗
          chainMergeSavedRegs sp0 s0) ∗ F)
        Q Qp) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (BitVec.ofNat 8 body.length :: (body ++ tail)) ∗
        stackAt sp0 chainMergeStack) ∗ F)
      Q Qp := by
  subst hsp
  have h1 : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = bufRef := hx2
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
  refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := (blkPl_11).base + 0x120#64) hcrl ?_
  rw [stackAt_chainMergeStack_split_seedChain s0.sp]
  unfold sliceCursorAt
  rw [pointsToBytes_cons]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
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
  intro hcrl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm]) hcrl1 (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]))
  unfold sliceCursorAt chainMergeSavedRegs
  rw [← hlen_append]
  exact sep_ac_seedChain (by ac_rfl)

theorem step_chainMerge_seg1_placed_seedChain [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hBM : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.bytesMergeRawSpec A0)))
    (a bufRef slot ptr sp0 : BitVec 64)
    (srk rest tail : List (BitVec 8))
    (hsrk_lt : srk.length < 128)
    (hlen_lt : (pbBytes 1 srk ++ rest ++ tail).length < 2 ^ 32)
    {α : Type} {x : α} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x26 = s0.readReg64 .x26 →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 a srk ∗
          (ptr ↦ₛ pbBytes 1 srk) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 1 srk).length) (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 a [] ∗
        sliceCursorAt slot ptr (pbBytes 1 srk ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R)) := by
  have hpb : pbBytes 1 srk = 0x0a#8 :: BitVec.ofNat 8 srk.length :: srk :=
    pbBytes_lt128_eq_seedChain 1 (by decide) srk hsrk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)
  have hcons_eq : pbBytes 1 srk ++ (rest ++ tail) = 0x0a#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x0a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x0a#8 :: rem1).length < 2 ^ 32 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x0a#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = lsmpl.base 7 →
      s1.status = .Running →
      s1.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s_init.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = (blkPl_11).base + 0x25c#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a →
      s1.readReg64 .x2 = bufRef →
      s1.readReg64 .x19 = bufRef →
      s1.readReg64 .x20 = a →
      s1.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      s1.readReg64 .x26 = s0.readReg64 .x26 →
      SepWPp (lsProg_11 H) ret s1
        ((vecU8 A0 a [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x0a#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R))) → _) ?_
  · intro hnext1
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
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
      (by simp only [h24, arm64_norm])
      (by simp only [arm64_norm]))
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hcrl1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx24_1 hx26_1
    have hrem1_lt : ([BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)).length < 2 ^ 32 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_placed_seedChain hBM
      a bufRef slot (ptr + 1#64) sp0
      ((blkPl_11).base + 0x25c#64)
      [] srk (rest ++ tail) hsrk_lt hrem1_lt
      hpc1 hrun1 hsp1 halign hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hcs2 hx0_2
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := (blkPl_11).base + 0x120#64) hcrl2 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcrl3
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
    have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
    have h26_2 : s2.readReg64 (Reg.gpr 26#5) = s0.readReg64 .x26 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
    have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hcrl3 (by simp only [htr2, arm64_norm])
      (by simp only [hvregs_2, arm64_norm])
      (by simp only [h19_2, arm64_norm])
      (by simp only [h20_2, arm64_norm])
      (by simp only [h24_2, arm64_norm])
      (by simp only [h26_2, arm64_norm]))
    rw [pbBytes_ptr_advance_seedChain 1 (by decide) ptr srk hsrk_lt,
      ← pbBytes_pointsTo_combine_seedChain 1 (by decide) ptr srk hsrk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_chainMerge_seg2_placed_seedChain [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hBM : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.bytesMergeRawSpec A0)))
    (a bufRef slot ptr sp0 : BitVec 64)
    (priv rest tail : List (BitVec 8))
    (hpriv : priv = [] ∨ priv.length = 32)
    (hlen_lt : ((if priv = [] then [] else pbBytes 2 priv) ++ rest ++ tail).length < 2 ^ 32)
    {α : Type} {x : α} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      sm.readReg64 .x19 = bufRef →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x24 = BitVec.ofNat 64 tail.length →
      sm.readReg64 .x26 = s0.readReg64 .x26 →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          (ptr ↦ₛ (if priv = [] then [] else pbBytes 2 priv)) ∗
          sliceCursorAt slot
            (ptr + BitVec.ofNat 64 (if priv = [] then [] else pbBytes 2 priv).length)
            (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x18#64) [] ∗
        sliceCursorAt slot ptr ((if priv = [] then [] else pbBytes 2 priv) ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R)) := by
  rcases hpriv with rfl | hpriv_len
  · simp only [ite_true, List.nil_append, List.length_nil,
      BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    refine SepWPp.mono_pre_seedChain ?_ (hnext s0 hpc hrun hsp hcrl htr hvregs hx19 hx20 hx24 rfl)
    exact sep_ac_seedChain (by ac_rfl)
  · have hpriv_ne : priv ≠ [] := by intro h; subst h; simp at hpriv_len
    have hpriv_lt : priv.length < 128 := by omega
    simp only [hpriv_ne, ↓reduceIte] at hlen_lt hnext ⊢
    have hpb : pbBytes 2 priv = 0x12#8 :: BitVec.ofNat 8 priv.length :: priv :=
      pbBytes_lt128_eq_seedChain 2 (by decide) priv hpriv_lt
    let rem1 : List (BitVec 8) := [BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)
    have hcons_eq : pbBytes 2 priv ++ (rest ++ tail) = 0x12#8 :: rem1 := by
      rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
    have hlen_gt : tail.length < (0x12#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 32 := by
      rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
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
        s1.readReg64 .lr = (blkPl_11).base + 0x1d0#64 →
        (s1.readReg64 .x0).setWidth 8 = 2#8 →
        s1.readReg64 .x1 = a + 0x18#64 →
        s1.readReg64 .x2 = bufRef →
        s1.readReg64 .x19 = bufRef →
        s1.readReg64 .x20 = a →
        s1.readReg64 .x24 = BitVec.ofNat 64 tail.length →
        s1.readReg64 .x26 = s0.readReg64 .x26 →
        SepWPp (lsProg_11 H) ret s1
          ((vecU8 A0 (a + 0x18#64) [] ∗
            (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot (ptr + 1#64) rem1 ∗
            stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x12#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s_init sf ∗ R))) → _) ?_
    · intro hnext1
      have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
      have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
      have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
      refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl ?_
      rw [hcons_eq]
      unfold sliceCursorAt
      rw [pointsToBytes_cons]
      simp only [sepConj_assoc]
      iterate 28 wp_step
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
        (by simp only [h24, arm64_norm])
        (by simp only [arm64_norm]))
      unfold sliceCursorAt
      exact sep_ac_seedChain (by ac_rfl)
    · intro s1 hpc1 hrun1 hsp1 hcrl1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx24_1 hx26_1
      have hrem1_lt : ([BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)).length < 2 ^ 32 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_bytesMerge_placed_seedChain hBM
        (a + 0x18#64) bufRef slot (ptr + 1#64) sp0
        ((blkPl_11).base + 0x1d0#64)
        [] priv (rest ++ tail) hpriv_lt hrem1_lt
        hpc1 hrun1 hsp1 halign hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
      intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hcs2 hx0_2
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := (blkPl_11).base + 0x120#64) hcrl2 ?_
      iterate 2 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
      intro hcrl3
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hcs2.1.trans hx19_1
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hcs2.2.1.trans hx20_1
      have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hcs2.2.2.2.2.2.1.trans hx24_1
      have h26_2 : s2.readReg64 (Reg.gpr 26#5) = s0.readReg64 .x26 := hcs2.2.2.2.2.2.2.2.1.trans hx26_1
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init := hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        (by simp only [hsp2, arm64_norm]) hcrl3 (by simp only [htr2, arm64_norm])
        (by simp only [hvregs_2, arm64_norm])
        (by simp only [h19_2, arm64_norm])
        (by simp only [h20_2, arm64_norm])
        (by simp only [h24_2, arm64_norm])
        (by simp only [h26_2, arm64_norm]))
      rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr priv hpriv_lt,
        ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr priv hpriv_lt]
      exact sep_ac_seedChain (by ac_rfl)

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed

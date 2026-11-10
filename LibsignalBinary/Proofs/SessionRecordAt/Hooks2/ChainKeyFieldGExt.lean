/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
/-!
# `message::merge<Chain>` Tag 3 (`chain_key`) Leaf Proof

Proves `chainKeyFieldG_ok` (`+0x120 → +0x120` on tag 3 `chain_key` in
`prost::encoding::message::merge<Chain>`), including X-stack (`_atW`, `_atWA`) and relocatable
`[LibsignalPlacement]` (`lsProg_11 H`, Block `11`) variants.
-/

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter BytesMergeOk Int32MergeOk)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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
  bv_robdd

end ChainMergeStateSimp
open ChainMergeStateSimp

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

/-! ## 1. Pure helpers for `ChainG`, `ChainField.ck`, `chainGAfter`, and cursor splitting -/

private theorem map_key_getElem_tag_ne_three (keys : List MessageKeyGenerator) (j : Nat)
    (hj : j < (keys.map ChainField.key).length) :
    ((keys.map ChainField.key)[j]'hj).tag ≠ 3 := by
  simp [ChainField.tag]

/-! ## 2. Segment steps for tag 3 (`+0x120 → +0x4c8 → +0x4c8 → +0x4c8 → +0x120`) -/

theorem cbz_len_cons_false_seedChain {b0 : BitVec 8} {bs1 : List (BitVec 8)}
    (hlen : (b0 :: bs1).length < 2 ^ 32) :
    (BitVec.ofNat 64 (b0 :: bs1).length == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  simp at h1

theorem pbVarint1_ptr_advance_seedChain (ptr : BitVec 64) (n : Nat) (hn : n ≠ 0) :
    ptr + 1#64 + BitVec.ofNat 64 (pbVarintBody 5 n).length =
      ptr + BitVec.ofNat 64 (pbVarint 1 n).length := by
  have hpb : pbVarint 1 n = 0x08#8 :: pbVarintBody 5 n := by
    unfold pbVarint; simp [hn]; rfl
  rw [hpb]
  simp only [List.length_cons]
  bv_omega

theorem pbVarint1_pointsTo_combine_seedChain (ptr : BitVec 64) (n : Nat) (hn : n ≠ 0) :
    (ptr ↦₈ 0x08#8) ∗ ((ptr + 1#64) ↦ₛ pbVarintBody 5 n) =
      (ptr ↦ₛ pbVarint 1 n) := by
  have hpb : pbVarint 1 n = 0x08#8 :: pbVarintBody 5 n := by
    unfold pbVarint; simp [hn]; rfl
  rw [hpb, pointsToBytes_cons]

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

theorem ck_hdr_pointsTo_combine_seedChain (ptr : BitVec 64) (n : Nat) :
    (ptr ↦₈ 0x1a#8) ∗ ((ptr + 1#64) ↦₈ BitVec.ofNat 8 n) =
      (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 n]) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]


/-! ## 3. `_atW[A]` versions on `SP2Ext img.base ext` (X-Stack) -/

private theorem emptyVec_entails_vecU8A (A : RustAlloc) (addr : BitVec 64) :
    (addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 1#64) ∗ ((addr + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A addr [] := by
  rw [emptyVec_eq_vecU8At_seedChain]
  change vecU8At A addr 0#64 1#64 [] ⊢ vecU8 A addr []
  unfold vecU8
  exact Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 (Entails.refl _))

private theorem prostChainGAt_ck_none_eqA (A : RustAlloc) (a : BitVec 64) (c0 : ChainG)
    (hck : c0.ck = none) :
    prostChainGAt A a c0 =
      vecU8 A a c0.srk ∗ vecU8 A (a + 0x18#64) c0.priv ∗
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c0.keys ∗
      ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 := by
  unfold prostChainGAt
  rw [hck]

private theorem prostChainGAt_apply_ck_eqA (A : RustAlloc) (a : BitVec 64) (c0 : ChainG)
    (i : BitVec 32) (key : List (BitVec 8)) :
    prostChainGAt A a (c0.apply (ChainField.ck i key)) =
      vecU8 A a c0.srk ∗ vecU8 A (a + 0x18#64) c0.priv ∗
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c0.keys ∗
      vecU8 A (a + 0x48#64) key ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4 := by
  unfold prostChainGAt ChainG.apply
  rfl

/-- Outer field 3 header (`[0x1a#8, len]`, `+0x120 → +0x4c8`) with general `afterCk` and `outerTailLen` on `SP2Ext` (`*WA`). -/
theorem step_chainMerge_seg3a_g_atWA (img : Obj.Image) {A : RustAlloc}
    {ext : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hck_lt : ck_body.length < 128)
    (houter_le : outerTailLen ≤ afterCk.length)
    (hlen_lt : (2 + (ck_body.length + afterCk.length)) < 2 ^ 62)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 outerTailLen)
    (hx25 : s0.readReg64 .x25 = sp0 - 0xf8#64)
    (hx26 : s0.readReg64 .x26 = 1#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ afterCk) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q Qp := by
  have hlen_gt : outerTailLen < (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x1a#8 (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk))
  have hrem1_lt : (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz2 := cbz_len_cons_false_seedChain62 (b0 := BitVec.ofNat 8 ck_body.length)
    (bs1 := ck_body ++ afterCk) hrem1_lt
  have hse0 := signExtend64_ofNat8_lt128_seedChain hck_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hck_lt
  have hsub2 := len_cons_sub_one_seedChain (BitVec.ofNat 8 ck_body.length) (ck_body ++ afterCk)
  have hlen_ck_append : (ck_body ++ afterCk).length = ck_body.length + afterCk.length := List.length_append
  have hule_ck_sub := ule_ofNat_add_right_true_seedChain62 (m := ck_body.length) (k := afterCk.length) (by omega)
  have hsub_ck_tail := bv_ofNat_add_sub_left_seedChain ck_body.length afterCk.length
  chainMerge_fetches_range img.base
    (Rust.withPanics ext) 0x120 0x144
  chainMerge_fetches_range img.base
    (Rust.withPanics ext) 0x188 0x1ac
  chainMerge_fetches_range img.base
    (Rust.withPanics ext) 0x1d8 0x1dc
  chainMerge_fetches_range img.base
    (Rust.withPanics ext) 0x268 0x2a8
  chainMerge_fetches_range img.base
    (Rust.withPanics ext) 0x49c 0x4ac
  dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
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
    hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    ⟨by simp only [hsp, arm64_norm],
     by simp only [h29, arm64_norm],
     by simp only [h19, arm64_norm],
     by simp only [h20, arm64_norm],
     by simp only [h21, arm64_norm],
     by simp only [h22, arm64_norm],
     by simp only [arm64_norm],
     by simp only [h24, arm64_norm],
     by simp only [h25, arm64_norm],
     by simp only [h26, arm64_norm]⟩)
  unfold sliceCursorAt
  rw [← hlen_ck_append, ← ck_hdr_pointsTo_combine_seedChain ptr ck_body.length]
  have hvec := emptyVec_entails_vecU8A A (a + 0x48#64)
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
                    (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
                      ptr ↦₈ 26#8 ∗
                        (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length ∗
                          (ptr + 2#64) ↦ₛ (ck_body ++ afterCk) ∗
                            stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F =
      (((a + 0x48#64) ↦₆₄ 0#64) ∗ ((a + 0x50#64) ↦₆₄ 1#64) ∗ ((a + 0x58#64) ↦₆₄ 0#64)) ∗
        (bufRef ↦₆₄ slot ∗
          (a + 0x60#64) ↦₃₂ 0#32 ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
          (slot ↦₆₄ (ptr + 2#64) ∗
            (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ afterCk)) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F) := by ac_rfl
  have hEq2 :
      vecU8 A (a + 0x48#64) [] ∗
        (bufRef ↦₆₄ slot ∗
          (a + 0x60#64) ↦₃₂ 0#32 ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
          (slot ↦₆₄ (ptr + 2#64) ∗
            (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ afterCk)) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F) =
      (bufRef ↦₆₄ slot ∗
        vecU8 A (a + 0x48#64) [] ∗
        (a + 0x60#64) ↦₃₂ 0#32 ∗
        memRegion (a + 0x64#64) 4 ∗
        (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
        (slot ↦₆₄ (ptr + 2#64) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F := by ac_rfl
  rw [hEq1, ← hEq2]
  exact sepConj_mono_left hvec

/-- Outer field 3 header (`[0x1a#8, len]`, `+0x120 → +0x4c8`) with general `afterCk` and `outerTailLen` on `SP2Ext`. -/
theorem step_chainMerge_seg3a_g_atW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hck_lt : ck_body.length < 128)
    (houter_le : outerTailLen ≤ afterCk.length)
    (hlen_lt : (2 + (ck_body.length + afterCk.length)) < 2 ^ 62)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 outerTailLen)
    (hx25 : s0.readReg64 .x25 = sp0 - 0xf8#64)
    (hx26 : s0.readReg64 .x26 = 1#64)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ afterCk) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q Qp :=
  step_chainMerge_seg3a_g_atWA (A := A0) img a bufRef slot ptr sp0 ck_body afterCk outerTailLen
    hck_lt houter_le hlen_lt hpc hrun hsp hF hsym htr hvregs hx29 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hnext

/-- Inner field 1 (`pbVarint 1 i.toNat`, `+0x4c8 → +0x4c8`) preserving `InnerLoopRegs` on `SP2Ext` (`*WA`). -/
theorem step_chainMerge_seg3b_g_atWA (img : Obj.Image) {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hIM : Prost.X.Int32MergeOkW img A ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hlen_lt : (pbVarint 1 i.toNat ++ rest ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x4c8#64)
    (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s0)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ afterCk) ∗
          A.pool ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ afterCk)) ∗
        A.pool ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R)) := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
  by_cases hi0 : i = 0#32
  · subst hi0
    have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    rw [hpb0] at hnext ⊢
    simp only [List.nil_append, List.length_nil,
      BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    refine SepWPp.mono_pre_seedChain ?_ (hnext s0 hpc hrun hF hsym htr hvregs
      ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩)
    exact sep_ac_seedChain (by ac_rfl)
  · have hi_pos : i.toNat ≠ 0 := by
      intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    have hpb : pbVarint 1 i.toNat = 0x08#8 :: pbVarintBody 5 i.toNat := by
      unfold pbVarint; simp [hi_pos]; rfl
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest ++ afterCk)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest ++ afterCk) = 0x08#8 :: rem1 := by
      rw [hpb]; simp [rem1, List.cons_append]
    have hlen_gt : afterCk.length < (0x08#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 62 := by
      rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
    have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
    have hsub1 := len_cons_sub_one_seedChain 0x08#8 rem1
    refine (?_ :
      (∀ (s1 : State),
        s1.pc = (SP2Ext img.base ext).fnAddr chainMergeName +
          bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) →
        s1.status = .Running →
        img.FrozenLoaded s1 →
        s1.symtab = img.symtab →
        s1.trace = s_init.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s_init →
        s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMergeName + 0x588#64 →
        (s1.readReg64 .x0).setWidth 8 = 0#8 →
        s1.readReg64 .x1 = a + 0x60#64 →
        s1.readReg64 .x2 = bufRef →
        InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s1 →
        SepWPp (SP2Ext img.base ext) ret s1
          ((((a + 0x60#64) ↦₃₂ 0#32) ∗
            (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot (ptr + 1#64) rem1 ∗
            A.pool ∗
            stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x08#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
    · intro hnext1
      chainMerge_fetches_range img.base
        (Rust.withPanics ext) 0x4c8 0x4ec
      chainMerge_fetches_range img.base
        (Rust.withPanics ext) 0x530 0x554
      chainMerge_fetches_range img.base
        (Rust.withPanics ext) 0x578 0x584
      dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext1 ⊢
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
      have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
      have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
      have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
      have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
      have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
      have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
      have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
      have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))) hF hsym ?_
      rw [hcons_eq]
      unfold sliceCursorAt
      rw [pointsToBytes_cons]
      simp only [sepConj_assoc]
      iterate 24 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [hsp, arm64_norm],
         by simp only [h29, arm64_norm],
         by simp only [h19, arm64_norm],
         by simp only [h20, arm64_norm],
         by simp only [h21, arm64_norm],
         by simp only [h22, arm64_norm],
         by simp only [h23, arm64_norm],
         by simp only [h24, arm64_norm],
         by simp only [h25, arm64_norm],
         by simp only [h26, arm64_norm]⟩)
      unfold sliceCursorAt
      exact sep_ac_seedChain (by ac_rfl)
    · intro s1 hpc1 hrun1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
      have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest ++ afterCk)).length < 2 ^ 62 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_int32Merge_atWA (x := dummySeedGhost) img hIM
        (a + 0x60#64) bufRef slot (ptr + 1#64) sp0
        ((SP2Ext img.base ext).fnAddr chainMergeName + 0x588#64)
        0#32 i (rest ++ afterCk) hrem1_lt
        hpc1 hrun1 hregs1.1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
      intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
      have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
      have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init :=
        hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      rcases hregs2 with ⟨hsp2, hx29_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2⟩
      chainMerge_fetches_range img.base
        (Rust.withPanics ext) 0x588 0x588
      chainMerge_fetches_range img.base
        (Rust.withPanics ext) 0x4c4 0x4c4
      dsimp only [SP2Ext, contractProg, chainMergeName] at hpc2 hnext ⊢
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
      examples_hide_fetches
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29_2
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19_2
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hx20_2
      have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hx21_2
      have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hx22_2
      have h23_2 : s2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23_2
      have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24_2
      have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25_2
      have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hx26_2
      refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1224)) hF2 hsym2 ?_
      iterate 2 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        hF3 hsym3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
        ⟨by simp only [hsp2, arm64_norm],
         by simp only [h29_2, arm64_norm],
         by simp only [h19_2, arm64_norm],
         by simp only [h20_2, arm64_norm],
         by simp only [h21_2, arm64_norm],
         by simp only [h22_2, arm64_norm],
         by simp only [h23_2, arm64_norm],
         by simp only [h24_2, arm64_norm],
         by simp only [h25_2, arm64_norm],
         by simp only [h26_2, arm64_norm]⟩)
      rw [pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos,
        ← pbVarint1_pointsTo_combine_seedChain ptr i.toNat hi_pos]
      exact sep_ac_seedChain (by ac_rfl)

/-- Inner field 1 (`pbVarint 1 i.toNat`, `+0x4c8 → +0x4c8`) preserving `InnerLoopRegs` on `SP2Ext`. -/
theorem step_chainMerge_seg3b_g_atW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hIM : Prost.X.Int32MergeOkW img A0 ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hlen_lt : (pbVarint 1 i.toNat ++ rest ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x4c8#64)
    (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s0)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ afterCk) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtW img).onPanic x s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ afterCk)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtW img).onPanic x s_init sf ∗ R)) := by
  have hp : A0.pool = emp := rfl
  have h := step_chainMerge_seg3b_g_atWA (A := A0) (x := x) (R := R) img hIM a bufRef slot ptr sp0
    i rest afterCk outerTailLen hlen_lt hpc hrun halign hF hsym htr hvregs hregs
    (fun sm h1 h2 h3 h4 h5 h6 h7 => by rw [hp, emp_sepConj]; exact hnext sm h1 h2 h3 h4 h5 h6 h7)
  rwa [hp, emp_sepConj] at h

/-- Inner field 2 (`pbBytes 2 k`, `+0x4c8 → +0x4c8`) preserving `InnerLoopRegs` on `SP2Ext` (`*WA`). -/
theorem step_chainMerge_seg3c_g_atWA (img : Obj.Image) {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hBM : Prost.X.BytesMergeOkW img A ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (k afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hk_lt : k.length < 128)
    (hlen_lt : (pbBytes 2 k ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x4c8#64)
    (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s0)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A (a + 0x48#64) k ∗
          (ptr ↦ₛ pbBytes 2 k) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 k).length) afterCk ∗
          A.pool ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 k ++ afterCk) ∗
        A.pool ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s_init sf ∗ R)) := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
  have hpb : pbBytes 2 k = 0x12#8 :: BitVec.ofNat 8 k.length :: k :=
    pbBytes_lt128_eq_seedChain 2 (by decide) k hk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 k.length] ++ k ++ afterCk
  have hcons_eq : pbBytes 2 k ++ afterCk = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : afterCk.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; exact hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x12#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMergeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) →
      s1.status = .Running →
      img.FrozenLoaded s1 →
      s1.symtab = img.symtab →
      s1.trace = s_init.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMergeName + 0x570#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a + 0x48#64 →
      s1.readReg64 .x2 = bufRef →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s1 →
      SepWPp (SP2Ext img.base ext) ret s1
        ((vecU8 A (a + 0x48#64) [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          A.pool ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x12#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
  · intro hnext1
    chainMerge_fetches_range img.base
      (Rust.withPanics ext) 0x4c8 0x4ec
    chainMerge_fetches_range img.base
      (Rust.withPanics ext) 0x530 0x56c
    dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext1 ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
    have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
    have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
    have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
    have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))) hF hsym ?_
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    simp only [sepConj_assoc]
    iterate 26 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      hF1 hsym1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      ⟨by simp only [hsp, arm64_norm],
       by simp only [h29, arm64_norm],
       by simp only [h19, arm64_norm],
       by simp only [h20, arm64_norm],
       by simp only [h21, arm64_norm],
       by simp only [h22, arm64_norm],
       by simp only [h23, arm64_norm],
       by simp only [h24, arm64_norm],
       by simp only [h25, arm64_norm],
       by simp only [h26, arm64_norm]⟩)
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hF1 hsym1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 k.length] ++ k ++ afterCk).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_atWA (x := dummySeedGhost) img hBM
      (a + 0x48#64) bufRef slot (ptr + 1#64) sp0
      ((SP2Ext img.base ext).fnAddr chainMergeName + 0x570#64)
      [] k afterCk hk_lt hrem1_lt
      hpc1 hrun1 hregs1.1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
    have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init :=
      hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    rcases hregs2 with ⟨hsp2, hx29_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2⟩
    chainMerge_fetches_range img.base
      (Rust.withPanics ext) 0x570 0x570
    chainMerge_fetches_range img.base
      (Rust.withPanics ext) 0x4c4 0x4c4
    dsimp only [SP2Ext, contractProg, chainMergeName] at hpc2 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29_2
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19_2
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hx20_2
    have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hx21_2
    have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hx22_2
    have h23_2 : s2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23_2
    have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24_2
    have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25_2
    have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hx26_2
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (1224)) hF2 hsym2 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      hF3 hsym3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
      ⟨by simp only [hsp2, arm64_norm],
       by simp only [h29_2, arm64_norm],
       by simp only [h19_2, arm64_norm],
       by simp only [h20_2, arm64_norm],
       by simp only [h21_2, arm64_norm],
       by simp only [h22_2, arm64_norm],
       by simp only [h23_2, arm64_norm],
       by simp only [h24_2, arm64_norm],
       by simp only [h25_2, arm64_norm],
       by simp only [h26_2, arm64_norm]⟩)
    rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr k hk_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr k hk_lt]
    exact sep_ac_seedChain (by ac_rfl)

/-- Inner field 2 (`pbBytes 2 k`, `+0x4c8 → +0x4c8`) preserving `InnerLoopRegs` on `SP2Ext`. -/
theorem step_chainMerge_seg3c_g_atW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hBM : Prost.X.BytesMergeOkW img A0 ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (k afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hk_lt : k.length < 128)
    (hlen_lt : (pbBytes 2 k ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x4c8#64)
    (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s0)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x4c8#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) k ∗
          (ptr ↦ₛ pbBytes 2 k) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 k).length) afterCk ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtW img).onPanic x s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 k ++ afterCk) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtW img).onPanic x s_init sf ∗ R)) := by
  have hp : A0.pool = emp := rfl
  have h := step_chainMerge_seg3c_g_atWA (A := A0) (x := x) (R := R) img hBM a bufRef slot ptr sp0
    k afterCk outerTailLen hk_lt hlen_lt hpc hrun halign hF hsym htr hvregs hregs
    (fun sm h1 h2 h3 h4 h5 h6 h7 => by rw [hp, emp_sepConj]; exact hnext sm h1 h2 h3 h4 h5 h6 h7)
  rwa [hp, emp_sepConj] at h

/-- Inner loop exit (`+0x4c8 → +0x120`) when remaining slice is `afterCk` on `SP2Ext`. -/
theorem step_chainMerge_seg3d_g_atW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64)
    (afterCk : List (BitVec 8)) (outerTailLen : Nat)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x4c8#64)
    (hrun : s0.status = .Running)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s0)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr afterCk ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr afterCk ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
  chainMerge_fetches_range img.base
    (Rust.withPanics ext) 0x4c8 0x4d4
  chainMerge_fetches_range img.base
    (Rust.withPanics ext) 0x5a8 0x5b0
  dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
  have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (288)) hF hsym ?_
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
     by simp only [h26, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

/-- Leaf CM-3 (`*WA`): `+0x120` with tag 3 `→ +0x120` with `k + 1` on `SP2Ext img.base ext` for `(A : RustAlloc)`. -/
theorem chainKeyFieldG_ok_atWA (img : Obj.Image) (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hC : DeserializeCalleesAtWA img A ext) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length) (htag : (x.c.fields[k]'hk).tag = 3)
    (hs : ChainLoopGAtWA img A ext x R s0 k s) :
    ChainStepGAtWA img A ext x R s0 s (ChainLoopGAtWA img A ext x R s0 (k + 1)) := by
  obtain ⟨_, hIM, hBM, _⟩ := hC
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hal, hx29, hx19, hx20, hx24,
    hx21, hx22, hx25, hx26, hcOk, hlen_lt, hmem⟩
  intro hL
  have hsp_sub_align : (s0.sp - 256#64) &&& 15#64 = 0#64 := by
    have : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    simpa [hsp] using this
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_256_aligned hsp_sub_align
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
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
        (vecU8 A x.a c0.srk ∗ vecU8 A (x.a + 0x18#64) c0.priv ∗
          vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗ A.pool ∗
          chainMergeSavedRegs s0.sp s0)) ∗ R := by
    change s.mem ⊨
      prostChainGAt A x.a c0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      A.pool ∗ stackAt (s0.sp - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0 ∗ R at hmem
    rw [prostChainGAt_ck_none_eqA A x.a c0 hck_none, hcur_init] at hmem
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hfull : SepWPp (SP2Ext img.base ext) (chainPCAtX img ext 0x120#64) s
      (((x.bufRef ↦₆₄ x.slot) ∗
        ((x.a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (x.a + 0x50#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
        (vecU8 A x.a c0.srk ∗ vecU8 A (x.a + 0x18#64) c0.priv ∗
          vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗ A.pool ∗
          chainMergeSavedRegs s0.sp s0))
      (fun sf Pf =>
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        InnerLoopRegs s0.sp x.bufRef x.a x.tail.length afterCk.length sf ∧
        (Pf ⊢ prostChainGAt A x.a (chainGAfter x.c (k + 1)) ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
            (((x.c.fields.drop (k + 1)).flatMap ChainField.enc) ++ x.tail) ∗
          A.pool ∗ stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s0 sf ∗ R)) := by
    have hpc' : s.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 := hpc
    refine step_chainMerge_seg3a_g_atWA (A := A) img x.a x.bufRef x.slot ptr3a s0.sp
      ck_body afterCk x.tail.length hck_lt houter_le hlen_lt3a
      hpc' hrun hsp hF hsym htr hvregs hx29 hx19 hx20 hx21 hx22 hx24 hx25 hx26 ?_
    intro s4 hpc4 hrun4 hF4 hsym4 htr4 hvregs4 hregs4
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        ((x.a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt x.slot ptr3b (b3b ++ (b3c ++ afterCk)) ∗
        A.pool ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
        ((ptr3a ↦ₛ b3a) ∗
          vecU8 A (x.a + 0x48#64) [] ∗
          memRegion (x.a + 0x64#64) 4 ∗
          vecU8 A x.a c0.srk ∗ vecU8 A (x.a + 0x18#64) c0.priv ∗
          vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0)))
      (by
        have hck_eq : ck_body ++ afterCk = b3b ++ (b3c ++ afterCk) := by
          simp [ck_body, b3b, b3c, List.append_assoc]
        dsimp only [ptr3b, b3a]
        rw [hck_eq]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3b_g_atWA img hIM x.a x.bufRef x.slot ptr3b s0.sp
      i b3c afterCk x.tail.length hlen_lt3b
      hpc4 hrun4 hsp0_align hF4 hsym4 htr4 hvregs4 hregs4 ?_
    intro s5 hpc5 hrun5 hF5 hsym5 htr5 hvregs5 hregs5
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        vecU8 A (x.a + 0x48#64) [] ∗
        sliceCursorAt x.slot ptr3c (b3c ++ afterCk) ∗
        A.pool ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
        ((ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          ((x.a + 0x60#64) ↦₃₂ i) ∗
          memRegion (x.a + 0x64#64) 4 ∗
          vecU8 A x.a c0.srk ∗ vecU8 A (x.a + 0x18#64) c0.priv ∗
          vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0)))
      (by dsimp only [ptr3c, b3b]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3c_g_atWA img hBM x.a x.bufRef x.slot ptr3c s0.sp
      key afterCk x.tail.length hkey_lt hlen_lt3c
      hpc5 hrun5 hsp0_align hF5 hsym5 htr5 hvregs5 hregs5 ?_
    intro s6 hpc6 hrun6 hF6 hsym6 htr6 hvregs6 hregs6
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd afterCk ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
        ((ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          (ptr3c ↦ₛ b3c) ∗
          vecU8 A (x.a + 0x48#64) key ∗
          ((x.a + 0x60#64) ↦₃₂ i) ∗
          memRegion (x.a + 0x64#64) 4 ∗
          vecU8 A x.a c0.srk ∗ vecU8 A (x.a + 0x18#64) c0.priv ∗
          vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗ A.pool ∗
          chainMergeSavedRegs s0.sp s0)))
      (by dsimp only [ptrEnd, b3c]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3d_g_atW img x.a x.bufRef x.slot ptrEnd s0.sp
      afterCk x.tail.length hpc6 hrun6 hF6 hsym6 htr6 hvregs6 hregs6 ?_
    intro sf hpcf hrunf hFf hsymf htrf hvregsf hregsf
    refine SepWPp.done hpcf hrunf ⟨hFf, hsymf, htrf, hvregsf, hregsf, ?_⟩
    have hc_succ : chainGAfter x.c (k + 1) = c0.apply (ChainField.ck i key) := by
      rw [chainGAfter_succ x.c k hk, hfl_eq]
    rw [hc_succ, prostChainGAt_apply_ck_eqA A x.a c0 i key]
    have hcur_end := combine_tag3_cursor x.slot x.ptr pfx b3a b3b b3c afterCk rfl
    dsimp only at hcur_end
    have htotal_end : (pfx ++ (b3a ++ (b3b ++ b3c))) ++ afterCk = x.c.payload ++ x.tail := by
      rw [← hfl_enc, ← pfx_k_succ x.c k hk]
      exact (payload_append_eq_pfx_rem x.c (k + 1) x.tail).symm
    rw [htotal_end] at hcur_end
    change _ ⊢
      (vecU8 A x.a c0.srk ∗ vecU8 A (x.a + 0x18#64) c0.priv ∗
        vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64) c0.keys ∗
        vecU8 A (x.a + 0x48#64) key ∗ ((x.a + 0x60#64) ↦₃₂ i) ∗ memRegion (x.a + 0x64#64) 4) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) afterCk ∗
      A.pool ∗ stackAt (s0.sp - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0
    rw [← hcur_end]
    dsimp only [ptr3a, ptr3b, ptr3c, ptrEnd]
    exact sep_ac_seedChain (by ac_rfl)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem_init hL
  rcases hex with ⟨hpcf, hrunf, Pf, hmf, hFf, hsymf, htrf, hvregsf, hregsf, hentf⟩ | ⟨hpan, Pf, hmf, htrf⟩ | ⟨_, hoom⟩
  · rcases hregsf with ⟨hspf, hx29f, hx19f, hx20f, hx21f, hx22f, _, hx24f, hx25f, hx26f⟩
    have half : sf.spAligned = true := by
      rw [State.spAligned, hspf, ← hsp]
      exact hal
    have hmemf := Satisfies.mono (sepConj_mono_left hentf) hmf
    simp only [sepConj_assoc] at hmemf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, htrf, hvregsf, hsymf, hFf, hspf, half, hx29f, hx19f, hx20f,
      hx24f, hx21f, hx22f, hx25f, hx26f, hcOk, hlen_lt, hmemf⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, htrf hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Leaf CM-3: `+0x120` with tag 3 `→ +0x120` with `k + 1` on `SP2Ext img.base ext`. -/
theorem chainKeyFieldG_ok_atW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hC : DeserializeCalleesAtW img ext) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length) (htag : (x.c.fields[k]'hk).tag = 3)
    (hs : ChainLoopGAtW img ext x R s0 k s) :
    ChainStepGAtW img ext x R s0 s (ChainLoopGAtW img ext x R s0 (k + 1)) := by
  have hp : A0.pool = emp := rfl
  have hsA : ChainLoopGAtWA img A0 ext x R s0 k s := by
    simpa only [ChainLoopGAtWA, ChainLoopGAtW, hp, emp_sepConj] using hs
  intro hL
  obtain ⟨sf, hsteps, hex⟩ := chainKeyFieldG_ok_atWA img A0 hC x R s0 k s hk htag hsA hL
  refine ⟨sf, hsteps, hex.imp ?_ id⟩
  intro hloop
  simpa only [ChainLoopGAtWA, ChainLoopGAtW, hp, emp_sepConj] using hloop

/-! ## 4. Relocatable `[LibsignalPlacement]` Proof of `message::merge<Chain>` Tag 3 (`lsProg_11 H`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_ChainKeyFieldGExt_Placed : True := trivial

private theorem of_sepWP_lscro [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ :=
    hnext (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem step_chainMerge_seg3a_g_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (a bufRef slot ptr sp0 : BitVec 64)
    (ck_body afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hck_lt : ck_body.length < 128)
    (houter_le : outerTailLen ≤ afterCk.length)
    (hlen_lt : (2 + (ck_body.length + afterCk.length)) < 2 ^ 62)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hx29 : s0.readReg64 .x29 = sp0 - 0x60#64)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = 98#64)
    (hx22 : s0.readReg64 .x22 = 97#64)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 outerTailLen)
    (hx25 : s0.readReg64 .x25 = sp0 - 0xf8#64)
    (hx26 : s0.readReg64 .x26 = 1#64)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x4c8#64 →
      sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) [] ∗
          ((a + 0x60#64) ↦₃₂ 0#32) ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 ck_body.length]) ∗
          sliceCursorAt slot (ptr + 2#64) (ck_body ++ afterCk) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q Qp := by
  have hlen_gt : outerTailLen < (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length := by
    simp only [List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x1a#8 (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk))
  have hrem1_lt : (BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)).length < 2 ^ 62 := by
    simp only [List.length_cons, List.length_append]; omega
  have hcbz2 := cbz_len_cons_false_seedChain62 (b0 := BitVec.ofNat 8 ck_body.length)
    (bs1 := ck_body ++ afterCk) hrem1_lt
  have hse0 := signExtend64_ofNat8_lt128_seedChain hck_lt
  have hlsr56 := ofNat64_lsr56_eq_zero_seedChain hck_lt
  have hsub2 := len_cons_sub_one_seedChain (BitVec.ofNat 8 ck_body.length) (ck_body ++ afterCk)
  have hlen_ck_append : (ck_body ++ afterCk).length = ck_body.length + afterCk.length := List.length_append
  have hule_ck_sub := ule_ofNat_add_right_true_seedChain62 (m := ck_body.length) (k := afterCk.length) (by omega)
  have hsub_ck_tail := bv_ofNat_add_sub_left_seedChain ck_body.length afterCk.length
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
  have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  refine of_sepWP_lscro (mid := (blkPl_11).base + 0x4c8#64) hcrl ?_
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
    hcrl1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    ⟨by simp only [hsp, arm64_norm],
     by simp only [h29, arm64_norm],
     by simp only [h19, arm64_norm],
     by simp only [h20, arm64_norm],
     by simp only [h21, arm64_norm],
     by simp only [h22, arm64_norm],
     by simp only [arm64_norm],
     by simp only [h24, arm64_norm],
     by simp only [h25, arm64_norm],
     by simp only [h26, arm64_norm]⟩)
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
                    (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
                      ptr ↦₈ 26#8 ∗
                        (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length ∗
                          (ptr + 2#64) ↦ₛ (ck_body ++ afterCk) ∗
                            stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F =
      (((a + 0x48#64) ↦₆₄ 0#64) ∗ ((a + 0x50#64) ↦₆₄ 1#64) ∗ ((a + 0x58#64) ↦₆₄ 0#64)) ∗
        (bufRef ↦₆₄ slot ∗
          (a + 0x60#64) ↦₃₂ 0#32 ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
          (slot ↦₆₄ (ptr + 2#64) ∗
            (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ afterCk)) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F) := by ac_rfl
  have hEq2 :
      vecU8 A0 (a + 0x48#64) [] ∗
        (bufRef ↦₆₄ slot ∗
          (a + 0x60#64) ↦₃₂ 0#32 ∗
          memRegion (a + 0x64#64) 4 ∗
          (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
          (slot ↦₆₄ (ptr + 2#64) ∗
            (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ afterCk)) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX ∗ F) =
      (bufRef ↦₆₄ slot ∗
        vecU8 A0 (a + 0x48#64) [] ∗
        (a + 0x60#64) ↦₃₂ 0#32 ∗
        memRegion (a + 0x64#64) 4 ∗
        (ptr ↦₈ 0x1a#8 ∗ (ptr + 1#64) ↦₈ BitVec.ofNat 8 ck_body.length) ∗
        (slot ↦₆₄ (ptr + 2#64) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (ck_body ++ afterCk).length ∗
            (ptr + 2#64) ↦ₛ (ck_body ++ afterCk)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F := by ac_rfl
  rw [hEq1, ← hEq2]
  exact sepConj_mono_left hvec

theorem step_chainMerge_seg3b_g_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (hIM : Prost.X.Int32MergePlacedOkW A0 H)
    (a bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) (rest afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hlen_lt : (pbVarint 1 i.toNat ++ rest ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x4c8#64)
    (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s0)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x4c8#64 →
      sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          (ptr ↦ₛ pbVarint 1 i.toNat) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbVarint 1 i.toNat).length) (rest ++ afterCk) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr (pbVarint 1 i.toNat ++ (rest ++ afterCk)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R)) := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
  by_cases hi0 : i = 0#32
  · subst hi0
    have hpb0 : pbVarint 1 (0#32).toNat = [] := rfl
    rw [hpb0] at hnext ⊢
    simp only [List.nil_append, List.length_nil,
      BitVec.add_zero, pointsToBytes_nil] at hnext ⊢
    refine SepWPp.mono_pre_seedChain ?_ (hnext s0 hpc hrun hcrl htr hvregs
      ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩)
    exact sep_ac_seedChain (by ac_rfl)
  · have hi_pos : i.toNat ≠ 0 := by
      intro h; apply hi0; apply BitVec.eq_of_toNat_eq; simpa using h
    have hpb : pbVarint 1 i.toNat = 0x08#8 :: pbVarintBody 5 i.toNat := by
      unfold pbVarint; simp [hi_pos]; rfl
    let rem1 : List (BitVec 8) := pbVarintBody 5 i.toNat ++ (rest ++ afterCk)
    have hcons_eq : pbVarint 1 i.toNat ++ (rest ++ afterCk) = 0x08#8 :: rem1 := by
      rw [hpb]; simp [rem1, List.cons_append]
    have hlen_gt : afterCk.length < (0x08#8 :: rem1).length := by
      simp only [rem1, List.length_cons, List.length_append]; omega
    have hlen_cons_lt : (0x08#8 :: rem1).length < 2 ^ 62 := by
      rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
    have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
    have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
    have hsub1 := len_cons_sub_one_seedChain 0x08#8 rem1
    refine (?_ :
      (∀ (s1 : State),
        s1.pc = lsmpl.base 8 →
        s1.status = .Running →
        LibsignalCodeRoLoaded lsmpl s1.mem →
        s1.trace = s_init.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s_init →
        s1.readReg64 .lr = (blkPl_11).base + 0x588#64 →
        (s1.readReg64 .x0).setWidth 8 = 0#8 →
        s1.readReg64 .x1 = a + 0x60#64 →
        s1.readReg64 .x2 = bufRef →
        InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s1 →
        SepWPp (lsProg_11 H) ret s1
          ((((a + 0x60#64) ↦₃₂ 0#32) ∗
            (bufRef ↦₆₄ slot) ∗
            sliceCursorAt slot (ptr + 1#64) rem1 ∗
            stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x08#8) ∗ F))
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R))) → _) ?_
    · intro hnext1
      have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
      have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
      have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
      have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
      have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
      have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
      have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
      have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
      have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
      refine of_sepWP_lscro (mid := lsmpl.base 8) hcrl ?_
      rw [hcons_eq]
      unfold sliceCursorAt
      rw [pointsToBytes_cons]
      simp only [sepConj_assoc]
      iterate 24 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hcrl1
      refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        hcrl1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [hsp, arm64_norm],
         by simp only [h29, arm64_norm],
         by simp only [h19, arm64_norm],
         by simp only [h20, arm64_norm],
         by simp only [h21, arm64_norm],
         by simp only [h22, arm64_norm],
         by simp only [h23, arm64_norm],
         by simp only [h24, arm64_norm],
         by simp only [h25, arm64_norm],
         by simp only [h26, arm64_norm]⟩)
      unfold sliceCursorAt
      exact sep_ac_seedChain (by ac_rfl)
    · intro s1 hpc1 hrun1 hcrl1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
      have hrem1_lt : (pbVarintBody 5 i.toNat ++ (rest ++ afterCk)).length < 2 ^ 62 := by
        simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
      refine step_chainMerge_int32Merge_placedW (x := x) hIM
        (a + 0x60#64) bufRef slot (ptr + 1#64) sp0
        ((blkPl_11).base + 0x588#64)
        0#32 i (rest ++ afterCk) hrem1_lt
        hpc1 hrun1 hregs1.1 halign hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
      intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hcs2 hx0_2
      have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
      have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init :=
        hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      rcases hregs2 with ⟨hsp2, hx29_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2⟩
      have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29_2
      have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19_2
      have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hx20_2
      have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hx21_2
      have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hx22_2
      have h23_2 : s2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23_2
      have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24_2
      have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25_2
      have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hx26_2
      refine of_sepWP_lscro (mid := (blkPl_11).base + 0x4c8#64) hcrl2 ?_
      iterate 2 wp_step
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
      intro hcrl3
      refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        hcrl3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
        ⟨by simp only [hsp2, arm64_norm],
         by simp only [h29_2, arm64_norm],
         by simp only [h19_2, arm64_norm],
         by simp only [h20_2, arm64_norm],
         by simp only [h21_2, arm64_norm],
         by simp only [h22_2, arm64_norm],
         by simp only [h23_2, arm64_norm],
         by simp only [h24_2, arm64_norm],
         by simp only [h25_2, arm64_norm],
         by simp only [h26_2, arm64_norm]⟩)
      rw [pbVarint1_ptr_advance_seedChain ptr i.toNat hi_pos,
        ← pbVarint1_pointsTo_combine_seedChain ptr i.toNat hi_pos]
      exact sep_ac_seedChain (by ac_rfl)

theorem step_chainMerge_seg3c_g_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (hBM : Prost.X.BytesMergePlacedOkW A0 H)
    (a bufRef slot ptr sp0 : BitVec 64)
    (k afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hk_lt : k.length < 128)
    (hlen_lt : (pbBytes 2 k ++ afterCk).length < 2 ^ 62)
    {x : ChainMergeGenGhost} {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x4c8#64)
    (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s0)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x4c8#64 →
      sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x48#64) k ∗
          (ptr ↦ₛ pbBytes 2 k) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 k).length) afterCk ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 k ++ afterCk) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R)) := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
  have hpb : pbBytes 2 k = 0x12#8 :: BitVec.ofNat 8 k.length :: k :=
    pbBytes_lt128_eq_seedChain 2 (by decide) k hk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 k.length] ++ k ++ afterCk
  have hcons_eq : pbBytes 2 k ++ afterCk = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : afterCk.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; exact hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x12#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = lsmpl.base 7 →
      s1.status = .Running →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s_init.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = (blkPl_11).base + 0x570#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a + 0x48#64 →
      s1.readReg64 .x2 = bufRef →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s1 →
      SepWPp (lsProg_11 H) ret s1
        ((vecU8 A0 (a + 0x48#64) [] ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x12#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s_init sf ∗ R))) → _) ?_
  · intro hnext1
    have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
    have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
    have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
    have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
    have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
    refine of_sepWP_lscro (mid := lsmpl.base 7) hcrl ?_
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    simp only [sepConj_assoc]
    iterate 26 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcrl1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      hcrl1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      ⟨by simp only [hsp, arm64_norm],
       by simp only [h29, arm64_norm],
       by simp only [h19, arm64_norm],
       by simp only [h20, arm64_norm],
       by simp only [h21, arm64_norm],
       by simp only [h22, arm64_norm],
       by simp only [h23, arm64_norm],
       by simp only [h24, arm64_norm],
       by simp only [h25, arm64_norm],
       by simp only [h26, arm64_norm]⟩)
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hcrl1 htr1 hvregs1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 k.length] ++ k ++ afterCk).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_placedW (x := x) hBM
      (a + 0x48#64) bufRef slot (ptr + 1#64) sp0
      ((blkPl_11).base + 0x570#64)
      [] k afterCk hk_lt hrem1_lt
      hpc1 hrun1 hregs1.1 halign hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hcs2 hx0_2
    have hregs2 := hregs1.of_calleeSaved hsp2 hcs2
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s_init :=
      hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    rcases hregs2 with ⟨hsp2, hx29_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2⟩
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29_2
    have h19_2 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19_2
    have h20_2 : s2.readReg64 (Reg.gpr 20#5) = a := hx20_2
    have h21_2 : s2.readReg64 (Reg.gpr 21#5) = 98#64 := hx21_2
    have h22_2 : s2.readReg64 (Reg.gpr 22#5) = 97#64 := hx22_2
    have h23_2 : s2.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23_2
    have h24_2 : s2.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24_2
    have h25_2 : s2.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25_2
    have h26_2 : s2.readReg64 (Reg.gpr 26#5) = 1#64 := hx26_2
    refine of_sepWP_lscro (mid := (blkPl_11).base + 0x4c8#64) hcrl2 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcrl3
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      hcrl3 (by simp only [htr2, arm64_norm]) (by simp only [hvregs2, arm64_norm])
      ⟨by simp only [hsp2, arm64_norm],
       by simp only [h29_2, arm64_norm],
       by simp only [h19_2, arm64_norm],
       by simp only [h20_2, arm64_norm],
       by simp only [h21_2, arm64_norm],
       by simp only [h22_2, arm64_norm],
       by simp only [h23_2, arm64_norm],
       by simp only [h24_2, arm64_norm],
       by simp only [h25_2, arm64_norm],
       by simp only [h26_2, arm64_norm]⟩)
    rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr k hk_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr k hk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_chainMerge_seg3d_g_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (a bufRef slot ptr sp0 : BitVec 64)
    (afterCk : List (BitVec 8)) (outerTailLen : Nat)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x4c8#64)
    (hrun : s0.status = .Running)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s0)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x120#64 →
      sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr afterCk ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr afterCk ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26⟩
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x60#64 := hx29
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = 98#64 := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = 97#64 := hx22
  have h23 : s0.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 afterCk.length := hx23
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 outerTailLen := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = sp0 - 0xf8#64 := hx25
  have h26 : s0.readReg64 (Reg.gpr 26#5) = 1#64 := hx26
  refine of_sepWP_lscro (mid := (blkPl_11).base + 0x120#64) hcrl ?_
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 7 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcrl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm])
    hcrl1 (by simp only [htr, arm64_norm]) (by simp only [hvregs, arm64_norm])
    ⟨by simp only [hsp, arm64_norm],
     by simp only [h29, arm64_norm],
     by simp only [h19, arm64_norm],
     by simp only [h20, arm64_norm],
     by simp only [h21, arm64_norm],
     by simp only [h22, arm64_norm],
     by simp only [h23, arm64_norm],
     by simp only [h24, arm64_norm],
     by simp only [h25, arm64_norm],
     by simp only [h26, arm64_norm]⟩)
  unfold sliceCursorAt
  exact sep_ac_seedChain (by ac_rfl)

theorem chainKeyFieldG_placed_okW [LibsignalPlacement]
    {H : LibsignalHooks}
    (hC : DeserializeCalleesPlacedW H) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length) (htag : (x.c.fields[k]'hk).tag = 3)
    (hs : ChainLoopGPlacedW x R s0 k s) :
    ChainStepGPlacedW H x R s0 s (ChainLoopGPlacedW x R s0 (k + 1)) := by
  obtain ⟨_, hIM, hBM, _⟩ := hC
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcrl, hsp, hal, hx29, hx19, hx20, hx24,
    hx21, hx22, hx25, hx26, hcOk, hlen_lt, hmem⟩
  intro hL
  have hsp_sub_align : (s0.sp - 256#64) &&& 15#64 = 0#64 := by
    have : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    simpa [hsp] using this
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_256_aligned hsp_sub_align
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
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
        (vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0)) ∗ R := by
    change s.mem ⊨
      prostChainGAt A0 x.a c0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      stackAt (s0.sp - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0 ∗ R at hmem
    rw [prostChainGAt_ck_none_eq x.a c0 hck_none, hcur_init] at hmem
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hfull : SepWPp (lsProg_11 H) (chainPlacedPC 0x120#64) s
      (((x.bufRef ↦₆₄ x.slot) ∗
        ((x.a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (x.a + 0x50#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
        (vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0))
      (fun sf Pf =>
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        InnerLoopRegs s0.sp x.bufRef x.a x.tail.length afterCk.length sf ∧
        (Pf ⊢ prostChainGAt A0 x.a (chainGAfter x.c (k + 1)) ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
            (((x.c.fields.drop (k + 1)).flatMap ChainField.enc) ++ x.tail) ∗
          stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s0 sf ∗ R)) := by
    have hpc' : s.pc = (blkPl_11).base + 0x120#64 := hpc
    refine step_chainMerge_seg3a_g_placedW x.a x.bufRef x.slot ptr3a s0.sp
      ck_body afterCk x.tail.length hck_lt houter_le hlen_lt3a
      hpc' hrun hsp hcrl htr hvregs hx29 hx19 hx20 hx21 hx22 hx24 hx25 hx26 ?_
    intro s4 hpc4 hrun4 hcrl4 htr4 hvregs4 hregs4
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        ((x.a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt x.slot ptr3b (b3b ++ (b3c ++ afterCk)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
        ((ptr3a ↦ₛ b3a) ∗
          vecU8 A0 (x.a + 0x48#64) [] ∗
          memRegion (x.a + 0x64#64) 4 ∗
          vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0)))
      (by
        have hck_eq : ck_body ++ afterCk = b3b ++ (b3c ++ afterCk) := by
          simp [ck_body, b3b, b3c, List.append_assoc]
        dsimp only [ptr3b, b3a]
        rw [hck_eq]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3b_g_placedW hIM x.a x.bufRef x.slot ptr3b s0.sp
      i b3c afterCk x.tail.length hlen_lt3b
      hpc4 hrun4 hsp0_align hcrl4 htr4 hvregs4 hregs4 ?_
    intro s5 hpc5 hrun5 hcrl5 htr5 hvregs5 hregs5
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        vecU8 A0 (x.a + 0x48#64) [] ∗
        sliceCursorAt x.slot ptr3c (b3c ++ afterCk) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
        ((ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          ((x.a + 0x60#64) ↦₃₂ i) ∗
          memRegion (x.a + 0x64#64) 4 ∗
          vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0)))
      (by dsimp only [ptr3c, b3b]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3c_g_placedW hBM x.a x.bufRef x.slot ptr3c s0.sp
      key afterCk x.tail.length hkey_lt hlen_lt3c
      hpc5 hrun5 hsp0_align hcrl5 htr5 hvregs5 hregs5 ?_
    intro s6 hpc6 hrun6 hcrl6 htr6 hvregs6 hregs6
    refine SepWPp.mono_pre_seedChain
      (P' := (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd afterCk ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗
        ((ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          (ptr3c ↦ₛ b3c) ∗
          vecU8 A0 (x.a + 0x48#64) key ∗
          ((x.a + 0x60#64) ↦₃₂ i) ∗
          memRegion (x.a + 0x64#64) 4 ∗
          vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
          vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
          (x.ptr ↦ₛ pfx) ∗
          chainMergeSavedRegs s0.sp s0)))
      (by dsimp only [ptrEnd, b3c]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3d_g_placedW x.a x.bufRef x.slot ptrEnd s0.sp
      afterCk x.tail.length hpc6 hrun6 hcrl6 htr6 hvregs6 hregs6 ?_
    intro sf hpcf hrunf hcrlf htrf hvregsf hregsf
    refine SepWPp.done hpcf hrunf ⟨hcrlf, htrf, hvregsf, hregsf, ?_⟩
    have hc_succ : chainGAfter x.c (k + 1) = c0.apply (ChainField.ck i key) := by
      rw [chainGAfter_succ x.c k hk, hfl_eq]
    rw [hc_succ, prostChainGAt_apply_ck_eq x.a c0 i key]
    have hcur_end := combine_tag3_cursor x.slot x.ptr pfx b3a b3b b3c afterCk rfl
    dsimp only at hcur_end
    have htotal_end : (pfx ++ (b3a ++ (b3b ++ b3c))) ++ afterCk = x.c.payload ++ x.tail := by
      rw [← hfl_enc, ← pfx_k_succ x.c k hk]
      exact (payload_append_eq_pfx_rem x.c (k + 1) x.tail).symm
    rw [htotal_end] at hcur_end
    change _ ⊢
      (vecU8 A0 x.a c0.srk ∗ vecU8 A0 (x.a + 0x18#64) c0.priv ∗
        vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64) c0.keys ∗
        vecU8 A0 (x.a + 0x48#64) key ∗ ((x.a + 0x60#64) ↦₃₂ i) ∗ memRegion (x.a + 0x64#64) 4) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) afterCk ∗
      stackAt (s0.sp - 256#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0
    rw [← hcur_end]
    dsimp only [ptr3a, ptr3b, ptr3c, ptrEnd]
    exact sep_ac_seedChain (by ac_rfl)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem_init hL
  rcases hex with ⟨hpcf, hrunf, Pf, hmf, hcrlf, htrf, hvregsf, hregsf, hentf⟩ | ⟨hpan, Pf, hmf, htrf⟩ | ⟨_, hoom⟩
  · rcases hregsf with ⟨hspf, hx29f, hx19f, hx20f, hx21f, hx22f, _, hx24f, hx25f, hx26f⟩
    have half : sf.spAligned = true := by
      rw [State.spAligned, hspf, ← hsp]
      exact hal
    have hmemf := Satisfies.mono (sepConj_mono_left hentf) hmf
    simp only [sepConj_assoc] at hmemf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, htrf, hvregsf, hcrlf, hspf, half, hx29f, hx19f, hx20f,
      hx24f, hx21f, hx22f, hx25f, hx26f, hcOk, hlen_lt, hmemf⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, htrf hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG


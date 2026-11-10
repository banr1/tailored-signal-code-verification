/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Tag-1/2 Field Leaf (`chainSenderRatchetKeyG_ok`) for General `message::merge<Chain>`

Proves `chainSenderRatchetKeyG_ok` (`+0x120 → +0x120`, `k → k + 1`) for `sender_ratchet_key`
(tag `1`, `a`) and `sender_ratchet_key_private` (tag `2`, `a + 0x18`) via `bytes::merge`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter BytesMergeOk)
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

/-! ## Pure `ChainG`, `ChainField`, and `chainGAfter` Helpers -/

theorem chainGAfter_succ {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    chainGAfter c (k + 1) = (chainGAfter c k).apply (c.fields[k]'hk) := by
  simp only [chainGAfter, List.take_succ_eq_append_getElem hk, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem drop_flatMap_enc {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    (c.fields.drop k).flatMap ChainField.enc =
      (c.fields[k]'hk).enc ++ (c.fields.drop (k + 1)).flatMap ChainField.enc := by
  rw [List.drop_eq_getElem_cons hk, List.flatMap_cons]

theorem mem_fields_srk_length_lt {c : ChainG} (hc : c.Ok) {b : List (BitVec 8)}
    (hmem : ChainField.srk b ∈ c.fields) : b.length < 128 := by
  unfold ChainG.fields at hmem
  rcases c with ⟨srk, priv, ck, keys⟩
  have hsrk : srk.length = 33 := hc.1
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
    simp [h1, h2] at hmem <;> subst hmem <;> omega

theorem mem_fields_priv_length_lt {c : ChainG} (hc : c.Ok) {b : List (BitVec 8)}
    (hmem : ChainField.priv b ∈ c.fields) : b.length < 128 := by
  unfold ChainG.fields at hmem
  rcases c with ⟨srk, priv, ck, keys⟩
  have hpriv : priv = [] ∨ priv.length = 32 := hc.2.1
  rcases hpriv with rfl | h32
  · by_cases h1 : srk = [] <;> cases ck <;> simp [h1] at hmem
  · by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
      simp [h1, h2] at hmem <;> subst hmem <;> omega

theorem chainG_enc_eq_fields_local (c : ChainG) :
    c.enc = c.fields.flatMap ChainField.enc := by
  unfold ChainG.enc ChainG.fields msgField
  rcases c with ⟨srk, priv, ck, keys⟩
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;>
    (cases ck with
     | none =>
       simp [bytesField, h1, h2, ChainField.enc, Function.comp_def,
         List.append_assoc, List.flatMap_def]
     | some ik =>
       rcases ik with ⟨i, k⟩
       simp [bytesField, h1, h2, ChainField.enc, Function.comp_def,
         List.append_assoc, List.flatMap_def])

theorem lenField_eq_pbBytes (tag : Nat) (htag : tag = 1 ∨ tag = 2)
    (b : List (BitVec 8)) (hb : b.length < 128) :
    lenField tag b = pbBytes tag b := by
  unfold lenField pbBytes pbKey encodeKey WireType.toNat
  rw [encodeVarint_lt128_seedChain b.length hb]
  rcases htag with rfl | rfl <;> rfl

/-! ## Cursor and `prostChainGAt` Helpers -/

def preBytes (c : ChainG) (k : Nat) : List (BitVec 8) :=
  encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.fields.take k).flatMap ChainField.enc

def curPtr (ptr : BitVec 64) (c : ChainG) (k : Nat) : BitVec 64 :=
  ptr + BitVec.ofNat 64 (preBytes c k).length

theorem payload_append_eq_preBytes (c : ChainG) (tail : List (BitVec 8)) (k : Nat) :
    c.payload ++ tail =
      preBytes c k ++ (((c.fields.drop k).flatMap ChainField.enc) ++ tail) := by
  have henc : c.enc =
      (c.fields.take k).flatMap ChainField.enc ++ (c.fields.drop k).flatMap ChainField.enc := by
    rw [← List.flatMap_append, List.take_append_drop]
    exact chainG_enc_eq_fields_local c
  unfold ChainG.payload preBytes
  rw [henc]
  simp only [List.append_assoc]

theorem sliceCursorAfter_eq_preBytes (slot ptr : BitVec 64) (c : ChainG)
    (tail : List (BitVec 8)) (k : Nat) :
    sliceCursorAfter slot ptr (c.payload ++ tail)
      (((c.fields.drop k).flatMap ChainField.enc) ++ tail) =
      (ptr ↦ₛ preBytes c k) ∗
        sliceCursorAt slot (curPtr ptr c k)
          (((c.fields.drop k).flatMap ChainField.enc) ++ tail) := by
  conv_lhs => rw [payload_append_eq_preBytes c tail k]
  exact sliceCursorAfter_append_eq_seedChain slot ptr (preBytes c k) _

theorem preBytes_succ {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    preBytes c (k + 1) = preBytes c k ++ (c.fields[k]'hk).enc := by
  simp only [preBytes, List.take_succ_eq_append_getElem hk, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem curPtr_succ (ptr : BitVec 64) {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    curPtr ptr c (k + 1) = curPtr ptr c k + BitVec.ofNat 64 (c.fields[k]'hk).enc.length := by
  unfold curPtr
  rw [preBytes_succ hk, List.length_append, BitVec.ofNat_add]
  bv_omega

theorem pointsToBytes_preBytes_succ (ptr : BitVec 64) {c : ChainG} {k : Nat}
    (hk : k < c.fields.length) :
    (ptr ↦ₛ preBytes c k) ∗ (curPtr ptr c k ↦ₛ (c.fields[k]'hk).enc) =
      (ptr ↦ₛ preBytes c (k + 1)) := by
  rw [preBytes_succ hk, pointsToBytes_append, ← curPtr]

def prostChainGRestAt (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

theorem prostChainGAt_eq_split (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c =
      vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗ prostChainGRestAt A a c := by
  unfold prostChainGAt prostChainGRestAt
  ac_rfl

theorem prostChainGAt_apply_srk (A : RustAlloc) (a : BitVec 64) (c : ChainG)
    (b : List (BitVec 8)) :
    prostChainGAt A a (c.apply (.srk b)) =
      vecU8 A a b ∗ vecU8 A (a + 0x18#64) c.priv ∗ prostChainGRestAt A a c := by
  rw [prostChainGAt_eq_split]
  rfl

theorem prostChainGAt_apply_priv (A : RustAlloc) (a : BitVec 64) (c : ChainG)
    (b : List (BitVec 8)) :
    prostChainGAt A a (c.apply (.priv b)) =
      vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) b ∗ prostChainGRestAt A a c := by
  rw [prostChainGAt_eq_split]
  rfl

/-! ## Register Preservation and Stack Alignment Helpers -/

def LoopRegsPreserved (s s' : State) : Prop :=
  s'.readReg64 .x19 = s.readReg64 .x19 ∧
  s'.readReg64 .x20 = s.readReg64 .x20 ∧
  s'.readReg64 .x21 = s.readReg64 .x21 ∧
  s'.readReg64 .x22 = s.readReg64 .x22 ∧
  s'.readReg64 .x24 = s.readReg64 .x24 ∧
  s'.readReg64 .x25 = s.readReg64 .x25 ∧
  s'.readReg64 .x26 = s.readReg64 .x26 ∧
  s'.readReg64 .x29 = s.readReg64 .x29 ∧
  calleeSavedVRegs s' = calleeSavedVRegs s

theorem LoopRegsPreserved.trans {s0 s1 s2 : State}
    (h01 : LoopRegsPreserved s0 s1) (h12 : LoopRegsPreserved s1 s2) :
    LoopRegsPreserved s0 s2 := by
  reg_chain

theorem LoopRegsPreserved.of_calleeSaved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) : LoopRegsPreserved s1 s2 := by
  reg_chain

theorem sp0_aligned_of_sub_256 {sp0 : BitVec 64} (h : (sp0 - 256#64) &&& 15#64 = 0#64) :
    sp0 &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

def dummySeedGhost : ChainMergeGhost := ⟨0, ⟨[], [], none⟩, 0, 0, 0, [], []⟩

/-! ## Tag-1 and Tag-2 Stepping Lemmas -/

theorem step_chainTag1_g (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hBM : Prost.BytesMergeOk sessionImg0 C A0 ctl abs)
    (a bufRef slot ptr sp0 : BitVec 64)
    (bs0 srk rest tail : List (BitVec 8))
    (hsrk_lt : srk.length < 128)
    (hlen_lt : (pbBytes 1 srk ++ rest ++ tail).length < 2 ^ 32)
    {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
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
      LoopRegsPreserved s0 sm →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 a srk ∗
          (ptr ↦ₛ pbBytes 1 srk) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 1 srk).length) (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 a bs0 ∗
        sliceCursorAt slot ptr (pbBytes 1 srk ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R)) := by
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
      s1.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x25c#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a →
      s1.readReg64 .x2 = bufRef →
      LoopRegsPreserved s0 s1 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s1
        ((vecU8 A0 a bs0 ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x0a#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
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
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)).length < 2 ^ 32 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_seedChain (x := dummySeedGhost) C ctl hBM
      a bufRef slot (ptr + 1#64) sp0
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x25c#64)
      bs0 srk (rest ++ tail) hsrk_lt hrem1_lt
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
    have hregs2 : LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm])
      (hregs2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm]⟩))
    rw [pbBytes_ptr_advance_seedChain 1 (by decide) ptr srk hsrk_lt,
      ← pbBytes_pointsTo_combine_seedChain 1 (by decide) ptr srk hsrk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_chainTag2_g (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hBM : Prost.BytesMergeOk sessionImg0 C A0 ctl abs)
    (a bufRef slot ptr sp0 : BitVec 64)
    (bs0 priv rest tail : List (BitVec 8))
    (hpriv_lt : priv.length < 128)
    (hlen_lt : (pbBytes 2 priv ++ rest ++ tail).length < 2 ^ 32)
    {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
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
      LoopRegsPreserved s0 sm →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          (ptr ↦ₛ pbBytes 2 priv) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 priv).length) (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x18#64) bs0 ∗
        sliceCursorAt slot ptr (pbBytes 2 priv ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R)) := by
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
      s1.readReg64 .lr = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x1d0#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a + 0x18#64 →
      s1.readReg64 .x2 = bufRef →
      LoopRegsPreserved s0 s1 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s1
        ((vecU8 A0 (a + 0x18#64) bs0 ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ ((ptr ↦₈ 0x12#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
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
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)).length < 2 ^ 32 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_seedChain (x := dummySeedGhost) C ctl hBM
      (a + 0x18#64) bufRef slot (ptr + 1#64) sp0
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x1d0#64)
      bs0 priv (rest ++ tail) hpriv_lt hrem1_lt
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
    have hregs2 : LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm])
      (hregs2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm]⟩))
    rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr priv hpriv_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr priv hpriv_lt]
    exact sep_ac_seedChain (by ac_rfl)

/-! ## Main Leaf Theorem (`chainSenderRatchetKeyG_ok`) -/

theorem chainSenderRatchetKeyG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length)
    (htag : (x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2)
    (hs : ChainLoopG C ctl x R s0 k s) :
    ChainStepG C ctl x R s0 s (ChainLoopG C ctl x R s0 (k + 1)) abs := by
  intro hL
  obtain ⟨_, _, hBM, _⟩ := hC
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hal, hx29, hx19, hx20, hx24, hx21, hx22, hx25,
    hx26, hcOk, hlen, hmem⟩
  have hpc' : s.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64 := hpc
  have hsp_sub_align : (s0.sp - 256#64) &&& 15#64 = 0#64 := by
    have h1 : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    rwa [hsp] at h1
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_256 hsp_sub_align
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc
  have hlen_rem : ((x.c.fields[k]'hk).enc ++ rest ++ x.tail).length < 2 ^ 32 := by
    have h1 := hlen
    rw [payload_append_eq_preBytes x.c x.tail k, drop_flatMap_enc hk] at h1
    simp only [rest, List.length_append] at h1 ⊢
    omega
  generalize hfl_eq : x.c.fields[k]'hk = fl
  cases fl with
  | ck i key =>
    rw [hfl_eq] at htag
    simp [ChainField.tag] at htag
  | key mk =>
    rw [hfl_eq] at htag
    simp [ChainField.tag] at htag
  | srk b =>
    have hb_mem : ChainField.srk b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_srk_length_lt hcOk hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 1 b := by
      rw [hfl_eq]
      exact lenField_eq_pbBytes 1 (Or.inl rfl) b hb_lt
    have hlen_pb : (pbBytes 1 b ++ rest ++ x.tail).length < 2 ^ 32 := by
      rwa [← henc]
    let ck := chainGAfter x.c k
    let F : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗
      vecU8 A0 (x.a + 0x18#64) ck.priv ∗
      prostChainGRestAt A0 x.a ck ∗
      chainMergeSavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A0 x.a ck.srk ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
          stackAt (s0.sp - 256#64) chainMergeSubStack) ∗ F) ∗ R := by
      rw [prostChainGAt_eq_split A0 x.a ck,
        sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢
      simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs)
        (chainPC C ctl 0x120#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A0 x.a ck.srk ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
          stackAt (s0.sp - 256#64) chainMergeSubStack) ∗ F)
        (fun sm Pm =>
          (sm.mem ⊨ Pm ∗ R) → ChainLoopG C ctl x R s0 (k + 1) sm)
        (fun sf Pf =>
          (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R)) := by
      refine step_chainTag1_g C ctl hBM x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        ck.srk b rest x.tail hb_lt hlen_pb hpc' hrun hsp hsp0_align hF hsym htr hx19 hx20 hx24 ?_
      intro sm hpcm hrunm hspm hFm hsymm htrm hregsm
      refine SepWPp.done hpcm hrunm ?_
      intro hmem_m
      have hal_m : sm.spAligned = true := by
        simp only [State.spAligned, hspm, ← hsp]
        exact hal
      refine ⟨hpcm, hrunm, htrm, by reg_chain, hsymm, hFm, hspm, hal_m, by reg_chain, by reg_chain, by reg_chain,
        by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, hcOk, hlen, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗
            vecU8 A0 x.a b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 1 b) ∗
            sliceCursorAt x.slot
              (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 1 b).length)
              (rest ++ x.tail) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStack) ∗ F) =
          (prostChainGAt A0 x.a (chainGAfter x.c (k + 1)) ∗
            (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            stackAt (s0.sp - 0x100#64) chainMergeSubStack ∗
            chainMergeSavedRegs s0.sp s0) := by
        rw [chainGAfter_succ hk, hfl_eq, prostChainGAt_apply_srk A0 x.a ck b,
          ← henc, ← curPtr_succ x.ptr hk,
          sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]
        ac_rfl
      rw [hpost_eq] at hmem_m
      simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, hex⟩ := hwp R hmem_pre hL
    rcases hex with ⟨_, _, Pf, hmf, hloop⟩ | ⟨hpan, Pf, hmf, hpan_mem⟩ | ⟨_, hoom⟩
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact ⟨sf, hsteps, Or.inr ⟨hpan, hpan_mem hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  | priv b =>
    have hb_mem : ChainField.priv b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_priv_length_lt hcOk hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 2 b := by
      rw [hfl_eq]
      exact lenField_eq_pbBytes 2 (Or.inr rfl) b hb_lt
    have hlen_pb : (pbBytes 2 b ++ rest ++ x.tail).length < 2 ^ 32 := by
      rwa [← henc]
    let ck := chainGAfter x.c k
    let F : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗
      vecU8 A0 x.a ck.srk ∗
      prostChainGRestAt A0 x.a ck ∗
      chainMergeSavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A0 (x.a + 0x18#64) ck.priv ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
          stackAt (s0.sp - 256#64) chainMergeSubStack) ∗ F) ∗ R := by
      rw [prostChainGAt_eq_split A0 x.a ck,
        sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢
      simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs)
        (chainPC C ctl 0x120#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A0 (x.a + 0x18#64) ck.priv ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
          stackAt (s0.sp - 256#64) chainMergeSubStack) ∗ F)
        (fun sm Pm =>
          (sm.mem ⊨ Pm ∗ R) → ChainLoopG C ctl x R s0 (k + 1) sm)
        (fun sf Pf =>
          (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R)) := by
      refine step_chainTag2_g C ctl hBM x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        ck.priv b rest x.tail hb_lt hlen_pb hpc' hrun hsp hsp0_align hF hsym htr hx19 hx20 hx24 ?_
      intro sm hpcm hrunm hspm hFm hsymm htrm hregsm
      refine SepWPp.done hpcm hrunm ?_
      intro hmem_m
      have hal_m : sm.spAligned = true := by
        simp only [State.spAligned, hspm, ← hsp]
        exact hal
      refine ⟨hpcm, hrunm, htrm, by reg_chain, hsymm, hFm, hspm, hal_m, by reg_chain, by reg_chain, by reg_chain,
        by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, hcOk, hlen, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗
            vecU8 A0 (x.a + 0x18#64) b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 2 b) ∗
            sliceCursorAt x.slot
              (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 2 b).length)
              (rest ++ x.tail) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStack) ∗ F) =
          (prostChainGAt A0 x.a (chainGAfter x.c (k + 1)) ∗
            (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            stackAt (s0.sp - 0x100#64) chainMergeSubStack ∗
            chainMergeSavedRegs s0.sp s0) := by
        rw [chainGAfter_succ hk, hfl_eq, prostChainGAt_apply_priv A0 x.a ck b,
          ← henc, ← curPtr_succ x.ptr hk,
          sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]
        ac_rfl
      rw [hpost_eq] at hmem_m
      simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, hex⟩ := hwp R hmem_pre hL
    rcases hex with ⟨_, _, Pf, hmf, hloop⟩ | ⟨hpan, Pf, hmf, hpan_mem⟩ | ⟨_, hoom⟩
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact ⟨sf, hsteps, Or.inr ⟨hpan, hpan_mem hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG

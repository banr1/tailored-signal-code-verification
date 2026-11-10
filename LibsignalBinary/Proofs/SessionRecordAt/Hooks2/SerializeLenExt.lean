/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLen
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLen
import LibsignalBinary.Proofs.E2E.Record.Serialization.VecVecClone
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Pure Serialization Length and Empty-Clone Leaves

Verifies the stub-free serialization helpers `<Vec<Vec<u8>> as Clone>::clone` on an empty vector
(Block `117`), `<MessageKey as prost::Message>::encoded_len` (`0x2d6bc`, Block `118`), and
`<Chain as prost::Message>::encoded_len` (`0x26aa0`, Block `88`) on `SP2Ext` and under relocatable
`[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E.Record
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  hwVarintLen_eq_encodeVarint_length' hwVarintLen_bvShift_eq_encodeVarint_length'
  hwVarintLen_mix1_eq_encodeVarint_length hwVarintLen_mix2_eq_encodeVarint_length
  ule_zero_64 ult_zero_64

/-! ## `Vec<Vec<u8>>::clone` on an empty vector -/

private gen_decodes libsignalSessionCode_tree vecVecClone [(ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone") → (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" + 36), (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" + 196) → (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" + 232)]

private theorem stackAt_vecVecClone (sp : BitVec 64) :
    stackAt sp vecVecCloneStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        stackAt (sp - 96#64) allocHookStack ∗
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := LibsignalTripleRatchet.stackAt_split_cells sp allocHookStack 12 (by decide)
  have hadd : allocHookStack + 8 * 12 = vecVecCloneStack := by decide
  rw [hadd] at h1
  change stackAt sp vecVecCloneStack =
    stackAt (sp - 96#64) allocHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]
  simp only [sepExists_sepConj_right]

private theorem memRegion_24_cells (dst : BitVec 64) :
    memRegion dst 24 =
      (∃∗ d0 : BitVec 64, dst ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (dst + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (dst + 16#64) ↦₆₄ d2) := by
  have h1 := memRegion_split dst 8 16 (by decide)
  have h2 := memRegion_split (dst + 8#64) 8 8 (by decide)
  have hadd : dst + 8#64 + 8#64 = dst + 16#64 := by rw [BitVec.add_assoc]; rfl
  change memRegion dst 24 = memRegion dst 8 ∗ memRegion (dst + 8#64) 16 at h1
  change memRegion (dst + 8#64) 16 = memRegion (dst + 8#64) 8 ∗ memRegion (dst + 8#64 + 8#64) 8 at h2
  rw [h1, h2, hadd, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]

theorem vecVecCloneEmpty_ok_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr vecVecCloneName) vecVecCloneEmptySpec := by
  unfold vecVecCloneEmptySpec
  simp only [stackAt_vecVecClone, memRegion_24_cells, vecHeader,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff vecVecCloneName = num% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone") :=
    (ls_lemma% fnOff "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone")
  code_fetches_from CryptoVerification.libsignalSessionCode vecVecClone b
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone")) 0 40
  code_fetches_from CryptoVerification.libsignalSessionCode vecVecClone b
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone")) 0xc4 40
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨dst, src⟩ := x
  dsimp only at *
  wp_steps
  wp_done

/-! ## `MessageKey::encoded_len` (`0x2d6bc`) -/

gen_decodes libsignalSessionCode_tree mkLen [(ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len") → (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" + 48), (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" + 120) → (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" + 132),
    (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" + 164) → (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" + 248)]

private def msgKeyCells (a : BitVec 64) (mk : MessageKeyGenerator) : SepProp :=
  ((a + 16#64) ↦₆₄ 0#64) ∗
  ((a + 40#64) ↦₆₄ 0#64) ∗
  ((a + 64#64) ↦₆₄ 0#64) ∗
  ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mk.seed.length) ∗
  ((a + 96#64) ↦₃₂ mk.counter)

private def msgKeyRest (A : RustAlloc) (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    SepProp :=
  ⌜gk.2.seed ≠ []⌝ ∗
  (a ↦₆₄ gk.1.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.1.cipher.ptr) ∗ RustHeap.vecU8Buf A gk.1.cipher.cap gk.1.cipher.ptr [] ∗
  ((a + 24#64) ↦₆₄ gk.1.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.1.mac.ptr) ∗ RustHeap.vecU8Buf A gk.1.mac.cap gk.1.mac.ptr [] ∗
  ((a + 48#64) ↦₆₄ gk.1.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.1.iv.ptr) ∗ RustHeap.vecU8Buf A gk.1.iv.cap gk.1.iv.ptr [] ∗
  ((a + 72#64) ↦₆₄ gk.1.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.1.seed.ptr) ∗ RustHeap.vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
  memRegion (a + 100#64) 4

private theorem messageKeyAt_eq_cells_sep_rest (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A gk a = msgKeyCells a gk.2 ∗ msgKeyRest A gk a := by
  simp only [messageKeyAt, msgKeyCells, msgKeyRest, RustHeap.vecU8At_eq_header_sep_buf, vecHeader,
    List.length_nil, sepConj_assoc, arm64_norm]
  ac_rfl

private theorem msgKeyRest_seed_bounds {A : RustAlloc} {gk : MessageKeyGhost × MessageKeyGenerator}
    {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ msgKeyRest A gk a ∗ R) :
    gk.2.seed ≠ [] ∧ gk.2.seed.length < 2 ^ 63 := by
  unfold msgKeyRest at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  refine ⟨hm.1, ?_⟩
  have hbuf : m ⊨ RustHeap.vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      ((a ↦₆₄ gk.1.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.1.cipher.ptr) ∗
        RustHeap.vecU8Buf A gk.1.cipher.cap gk.1.cipher.ptr [] ∗
        ((a + 24#64) ↦₆₄ gk.1.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.1.mac.ptr) ∗
        RustHeap.vecU8Buf A gk.1.mac.cap gk.1.mac.ptr [] ∗
        ((a + 48#64) ↦₆₄ gk.1.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.1.iv.ptr) ∗
        RustHeap.vecU8Buf A gk.1.iv.cap gk.1.iv.ptr [] ∗
        ((a + 72#64) ↦₆₄ gk.1.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
        memRegion (a + 100#64) 4 ∗ R) := by
    convert hm.2 using 1; ac_rfl
  unfold RustHeap.vecU8Buf at hbuf
  rw [sepConj_assoc, satisfies_pure_sepConj] at hbuf
  have h1 := hbuf.1.1
  have h2 := hbuf.1.2.1
  omega

private theorem seed_len_beq_zero_false {bs : List (BitVec 8)}
    (hne : bs ≠ []) (hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  have hpos : 0 < bs.length := List.length_pos_iff.mpr hne
  rw [beq_eq_false_iff_ne]
  intro heq
  have h := congrArg BitVec.toNat heq
  change bs.length % 2 ^ 64 = 0 at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  omega

private theorem bv_uint32Field_1_ne_zero {v : BitVec 32} (h : (v == 0#32) = false) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length + 1#64 =
      BitVec.ofNat 64 (uint32Field 1 v).length := by
  have hv : v ≠ 0 := by rwa [beq_eq_false_iff_ne] at h
  have hkey : (encodeKey 1 .varint).length = 1 := rfl
  simp only [uint32Field, hv, ↓reduceIte, List.length_append, hkey,
    ← BitVec.ofNat_add, Nat.add_comm]

private theorem uint32Field_1_length_le (v : BitVec 32) :
    (uint32Field 1 v).length ≤ 11 := by
  unfold uint32Field
  split
  · simp
  · have hkey : (encodeKey 1 .varint).length = 1 := rfl
    have hb := (encodeVarint_length_bounds (v.setWidth 64)).2
    simp only [List.length_append, hkey]
    omega

private theorem bv_bytesField_5_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    BitVec.ofNat 64 bs.length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length + 1#64 =
      BitVec.ofNat 64 (bytesField 5 bs).length := by
  have hkey : (encodeKey 5 .lengthDelimited).length = 1 := rfl
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hkey, ← BitVec.ofNat_add]
  congr 1
  omega

private theorem bytesField_5_length_lt {bs : List (BitVec 8)} (hne : bs ≠ []) :
    (bytesField 5 bs).length ≤ bs.length + 11 := by
  have hkey : (encodeKey 5 .lengthDelimited).length = 1 := rfl
  have hb := (encodeVarint_length_bounds (BitVec.ofNat 64 bs.length)).2
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hkey]
  omega

private theorem encMessageKey_length_eq (mk : MessageKeyGenerator) :
    (encMessageKey mk).length =
      (uint32Field 1 mk.counter).length + (bytesField 5 mk.seed).length := by
  simp only [encMessageKey, List.length_append]

private theorem stackAt_msgKeyLen_eq (sp : BitVec 64) :
    stackAt sp msgKeyLenStack = ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) :=
  stackAt_encodedLen_eq sp

@[local simp, local arm64_norm]
private theorem ule_self_64 (x : BitVec 64) : BitVec.ule x x = true := by
  simp [BitVec.ule]

@[local simp, local arm64_norm]
private theorem ult_self_64 (x : BitVec 64) : BitVec.ult x x = false := by
  simp [BitVec.ult]

private theorem step_mkLen_f1_ext (b : BitVec 64) (ext : String → Option (State → State))
    (a sp v16 v8 : BitVec 64) (mk : MessageKeyGenerator)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr msgKeyLenName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (msgKeyCells a mk ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext b ext).fnAddr msgKeyLenName + 120#64 →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (uint32Field 1 mk.counter).length →
      sm.readReg64 .x9 = 0#64 →
      EncLenCalleeSaved s sm →
      SepWPp (SP2Ext b ext) ret sm
        ((msgKeyCells a mk ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (SP2Ext b ext) ret s P Q Qp := by
  mkLen_fetches_range b (Rust.withPanics ext) 0 52
  mkLen_fetches_range b (Rust.withPanics ext) 224 252
  generalize_entry (SP2Ext b ext).fnAddr msgKeyLenName = entry
  subst hP
  have hcells : msgKeyCells a mk =
      ((a + 16#64) ↦₆₄ 0#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mk.seed.length) ∗ ((a + 96#64) ↦₃₂ mk.counter) := rfl
  by_cases hcnt : (mk.counter == 0#32) = true
  · have hcnt0 : mk.counter = 0#32 := by rwa [beq_iff_eq] at hcnt
    rw [hcells]
    apply SepWPp.of_sepWP (mid := entry + bv% (120))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hcells]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [uint32Field]) (by simp_all)
      (by simp_all [EncLenCalleeSaved])
  · have hcnt_f : (mk.counter == 0#32) = false := Bool.eq_false_iff.mpr hcnt
    have henc := bv_uint32Field_1_ne_zero hcnt_f
    rw [hcells]
    apply SepWPp.of_sepWP (mid := entry + bv% (120))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hcells]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EncLenCalleeSaved])

private theorem step_mkLen_f2_ext (b : BitVec 64) (ext : String → Option (State → State))
    (a sp : BitVec 64) (mk : MessageKeyGenerator) (s1 : Nat)
    (hseed_ne : mk.seed ≠ [])
    (hseed_lt : mk.seed.length < 2 ^ 63)
    (hfit : s1 + (bytesField 5 mk.seed).length < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext b ext).fnAddr msgKeyLenName + 120#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hx9 : s.readReg64 .x9 = 0#64)
    (hcs : EncLenCalleeSaved s0 s)
    (hP : P = (msgKeyCells a mk ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (s1 + (bytesField 5 mk.seed).length) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (SP2Ext b ext) (s0.readReg64 .lr) s P Q Qp := by
  mkLen_fetches_range b (Rust.withPanics ext) 120 136
  mkLen_fetches_range b (Rust.withPanics ext) 164 224
  generalize_entry (SP2Ext b ext).fnAddr msgKeyLenName = entry
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  have hseed_beq := seed_len_beq_zero_false hseed_ne hseed_lt
  have henc := bv_bytesField_5_ne_nil hseed_ne
  have hcs_ovf := ult_ofNat_add_of_lt hfit
  have hule_ovf := ule_ofNat_add_of_lt hfit
  have hadd := bv_add_ofNat_comm s1 (bytesField 5 mk.seed).length
  subst hP
  have hcells : msgKeyCells a mk =
      ((a + 16#64) ↦₆₄ 0#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mk.seed.length) ∗ ((a + 96#64) ↦₃₂ mk.counter) := rfl
  rw [hcells]
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  rw [← hcells]
  apply SepWPp.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by encodedLen_cc_close)

theorem msgKeyLen_ok_ext (b : BitVec 64) (ext : String → Option (State → State)) (A : RustAlloc) :
    subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr msgKeyLenName) (msgKeyLenSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, gk⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [msgKeyLenSpec, messageKeyAt_eq_cells_sep_rest, stackAt_msgKeyLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, hx0, hpre⟩
  have hrest_sat : s0.mem ⊨ msgKeyRest A gk a ∗
      (msgKeyCells a gk.2 ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R) := by
    convert hpre using 1; ac_rfl
  obtain ⟨hseed_ne, hseed_lt⟩ := msgKeyRest_seed_bounds hrest_sat
  let FRest : SepProp := msgKeyRest A gk a ∗ R
  have hmem0 : s0.mem ⊨
      (msgKeyCells a gk.2 ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ FRest := by
    dsimp [FRest]; convert hpre using 1; ac_rfl
  refine ⟨(msgKeyCells a gk.2 ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ FRest, emp,
      by rwa [sepConj_emp], ?_⟩
  refine step_mkLen_f1_ext (F := FRest) b ext a s0.sp v16 v8 gk.2
    hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1
  have h1 := uint32Field_1_length_le gk.2.counter
  have h5 := bytesField_5_length_lt hseed_ne
  refine step_mkLen_f2_ext (F := FRest) b ext a s0.sp gk.2
    (uint32Field 1 gk.2.counter).length
    hseed_ne hseed_lt (by omega)
    hpc1 hrun1 hsp1 halign hx0_1 hx8_1 hx9_1 hcs1 rfl ?_
  intro sf hpcf hrunf hspf htrf hx0_f hcsf
  have htr_all : sf.trace = s0.trace := by rw [htrf, htr1]
  rw [← encMessageKey_length_eq] at hx0_f
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp] at hm_f
  simp only [msgKeyLenSpec, messageKeyAt_eq_cells_sep_rest, stackAt_msgKeyLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, htr_all⟩, ?_⟩
  dsimp [FRest] at hm_f
  convert hm_f using 1
  ac_rfl

/-! ## `Chain::encoded_len` (`0x26aa0`) -/

theorem msgKeyLen_fnAddr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr msgKeyLenName =
      (SP2Ext b ext).fnAddr chainLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") := by
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len"),
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len"), BitVec.add_assoc]
  rfl

/-- Prologue and Tag 1 (`sender_ratchet_key`, `+0x000` to `+0x038`). -/
private theorem chainLen_senderRatchetKey_ext (b : BitVec 64) (ext : String → Option (State → State)) (A : RustAlloc)
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64)
    (hsrk_lt : g.srk.bytes.length < 2 ^ 63)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64)
    (s0 : State) (Frame : SepProp)
    (hpc : s0.pc = (SP2Ext b ext).fnAddr chainLenName)
    (hrun : s0.status = .Running)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = a) :
    SepWP (SP2Ext b ext)
      ((SP2Ext b ext).fnAddr chainLenName + 56#64)
      s0
      (chainFieldsAt A g c a ∗
        chainLenSavedAt s0.sp v0 v1 v2 v3 v4 v5 v6 v7 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ chainFieldsAt A g c a ∗
          chainLenSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x23) v3 (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
          Frame) ∧
        Saved64Preserved s0 sm (s0.sp - 64#64) ∧
        sm.readReg64 .x0 = a ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 (bytesField 1 g.srk.bytes).length) := by
  chainLen_fetches_range b (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") (num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")) 0 56
  dsimp only [SP2Ext, contractProg, chainLenName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  have halign' : s0.sp &&& 15#64 = 0#64 := by
    simpa [beq_iff_eq] using halign
  dsimp only [chainFieldsAt, chainLenSavedAt]
  by_cases hsrk : g.srk.bytes = []
  · simp only [hsrk, bytesField, ↓reduceIte, List.length_nil]
    wp_steps
    wp_done
  · have hne0 := ofNat_len_beq_zero_of_ne_nil hsrk hsrk_lt
    have hbf := bv_bytesField_length_of_ne_nil (tag := 1) hsrk rfl
    wp_steps
    wp_done

/-- Tag 2 (`sender_ratchet_key_private`, `+0x038` to `+0x064`). -/
private theorem chainLen_senderRatchetKeyPrivate_ext (b : BitVec 64) (ext : String → Option (State → State)) (A : RustAlloc)
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64) (s1 : Nat)
    (hpriv_lt : g.priv.bytes.length < 2 ^ 63)
    (hfit12 : s1 + (bytesField 2 g.priv.bytes).length < 2 ^ 64)
    (s0 s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (SP2Ext b ext).fnAddr chainLenName + 56#64)
    (hrun : s.status = .Running)
    (hpres : Saved64Preserved s0 s fsp)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1) :
    SepWP (SP2Ext b ext)
      ((SP2Ext b ext).fnAddr chainLenName + 100#64)
      s
      (chainFieldsAt A g c a ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ chainFieldsAt A g c a ∗ Frame) ∧
        Saved64Preserved s0 sm fsp ∧
        sm.readReg64 .x0 = a ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (bytesField 2 g.priv.bytes).length)) := by
  chainLen_fetches_range b (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") (num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")) 56 100
  dsimp only [SP2Ext, contractProg, chainLenName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩
  dsimp only [chainFieldsAt]
  by_cases hpriv : g.priv.bytes = []
  · simp only [hpriv, bytesField, ↓reduceIte, List.length_nil, Nat.add_zero]
    have hovf0 := ult_zero_64 (BitVec.ofNat 64 s1)
    wp_steps
    wp_done
  · have hne0 := ofNat_len_beq_zero_of_ne_nil hpriv hpriv_lt
    have hbf := bv_bytesField_length_of_ne_nil (tag := 2) hpriv rfl
    have hovf := ult_ofNat_add_of_lt hfit12
    have hadd := bv_add_ofNat_comm s1 (bytesField 2 g.priv.bytes).length
    wp_steps
    wp_done

/-- Tag 3 (`chain_key: Option<ChainKey>` at `a + 72#64`, `+0x064` to `+0x0ec`). -/
private theorem chainLen_chainKey_ext (b : BitVec 64) (ext : String → Option (State → State)) (A : RustAlloc)
    (g : ChainGhost) (c : ReceiverChain) (a : BitVec 64) (s12 : Nat)
    (hck : ∀ ck, c.chainKey = some ck → g.ck.cap.toNat < 2 ^ 63)
    (hfit123 : s12 + (msgField 3 (c.chainKey.map encChainKey)).length < 2 ^ 64)
    (s0 s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (SP2Ext b ext).fnAddr chainLenName + 100#64)
    (hrun : s.status = .Running)
    (hpres : Saved64Preserved s0 s fsp)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12) :
    SepWP (SP2Ext b ext)
      ((SP2Ext b ext).fnAddr chainLenName + 236#64)
      s
      (chainFieldsAt A g c a ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ chainFieldsAt A g c a ∗ Frame) ∧
        Saved64Preserved s0 sm fsp ∧
        sm.readReg64 .x0 = a ∧
        sm.readReg64 .x20 = BitVec.ofNat 64 (s12 + (msgField 3 (c.chainKey.map encChainKey)).length)) := by
  chainLen_fetches_range b (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") (num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")) 100 224
  chainLen_fetches_range b (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") (num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")) 228 236
  chainLen_fetches_range b (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") (num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")) 368 376
  dsimp only [SP2Ext, contractProg, chainLenName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩
  dsimp only [chainFieldsAt]
  cases hck_eq : c.chainKey with
  | none =>
    rw [optChainKeyAt_none_offset72_eq]
    simp only [Option.map_none, msgField, List.length_nil, Nat.add_zero]
    have hovf0 := ult_zero_64 (BitVec.ofNat 64 s12)
    wp_steps
    wp_done
  | some ck =>
    have hcap_lt : g.ck.cap.toNat < 2 ^ 63 := hck ck hck_eq
    have hcap_ne := cap_add_one_beq_zero_false hcap_lt
    rw [hck_eq] at hfit123
    rw [optChainKeyAt_some_offset72_eq]
    rcases ck with ⟨key, idx⟩
    by_cases hidx : idx = 0#32
    · subst hidx
      have hmsg36 := msgField3_encChainKey_zero_length key
      simp only [Option.map_some, hmsg36] at hfit123 ⊢
      have hcc36 := ule_ofNat_add_of_lt hfit123
      have hadd36 := bv_add_ofNat_comm s12 36
      wp_steps
      wp_done
    · simp only [Option.map_some] at hfit123 ⊢
      have hidx_beq : (idx == 0#32) = false := beq_eq_false_iff_ne.mpr hidx
      have hu32 := bv_uint32Field1_length_of_ne_zero hidx
      have heck := bv_encChainKey_length ⟨key, idx⟩
      have hmsg := bv_msgField3_encChainKey_length ⟨key, idx⟩
      have hcc := ule_ofNat_add_of_lt hfit123
      have hadd := bv_add_ofNat_comm s12 (msgField 3 (some (encChainKey ⟨key, idx⟩))).length
      wp_steps
      wp_done

/-- Loop body (`+0x100` to `+0x12c`, offsets `256..300`): calls `MessageKey::encoded_len` (`0x2d6bc`)
on `cur` and adds `mkBodyLen mk` into `x22`. -/
private theorem chainLen_mk_body_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmk_at : subroutine_ok (SP2Ext b ext)
      ((SP2Ext b ext).fnAddr chainLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len"))
      (msgKeyLenSpec A))
    (s0 : State) (fsp v20 v21 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (acc : Nat) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (s : State) (Frame : SepProp),
      acc + mkBodyLen mk < 2 ^ 64 →
      s.pc = (SP2Ext b ext).fnAddr chainLenName + 256#64 →
      s.status = .Running →
      Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = cur →
      s.readReg64 .x20 = v20 →
      s.readReg64 .x21 = v21 →
      s.readReg64 .x22 = BitVec.ofNat 64 acc →
      s.readReg64 .x23 = cnt →
      SepWP (SP2Ext b ext)
        ((SP2Ext b ext).fnAddr chainLenName + 300#64)
        s
        (messageKeyAt A (pin, mk) cur ∗ stackAt fsp msgKeyLenStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ messageKeyAt A (pin, mk) cur ∗ stackAt fsp msgKeyLenStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cur ∧
          sm.readReg64 .x20 = v20 ∧
          sm.readReg64 .x21 = v21 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (acc + mkBodyLen mk) ∧
          sm.readReg64 .x23 = cnt) := by
  simp only [msgKeyLenSpec] at hmk_at
  chainLen_fetches_range b (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") (num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")) 256 300
  dsimp only [SP2Ext, contractProg, chainLenName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  intro cur cnt acc pin mk s Frame hfit hpc hrun hpres hx19 hx20 hx21 hx22 hx23
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩
  have hmk_fit : mkBodyLen mk < 2 ^ 64 := by omega
  have hovf1 := mkBodyLen_ult hmk_fit
  have hbody := bv_mkBodyLen_eq mk
  have hovf2 := ult_ofNat_add_of_lt hfit
  have hadd := bv_add_ofNat_comm acc (mkBodyLen mk)
  wp_steps
  wp_call hmk_at (⟨cur, (pin, mk)⟩ : MsgKeyLenGhost)
  wp_steps
  refine SepWP.align_pre (by rw [hsp]) ?_
  wp_done

/-- Loop over `rest : List (MessageKeyGhost × MessageKeyGenerator)` (`+0x100` to `+0x138`,
offsets `256..312`): accumulates `mksBodyLen (rest.map Prod.snd)` into `x22`. -/
private theorem chainLen_mk_loop_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmk_at : subroutine_ok (SP2Ext b ext)
      ((SP2Ext b ext).fnAddr chainLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len"))
      (msgKeyLenSpec A))
    (s0 : State) (fsp v20 v21 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64) (acc : Nat)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      acc + mksBodyLen (rest.map Prod.snd) < 2 ^ 64 →
      s.pc = (SP2Ext b ext).fnAddr chainLenName + 256#64 →
      s.status = .Running →
      Saved64Preserved s0 s fsp →
      s.readReg64 .x19 = cur →
      s.readReg64 .x20 = v20 →
      s.readReg64 .x21 = v21 →
      s.readReg64 .x22 = BitVec.ofNat 64 acc →
      s.readReg64 .x23 = BitVec.ofNat 64 rest.length →
      SepWP (SP2Ext b ext)
        ((SP2Ext b ext).fnAddr chainLenName + 312#64)
        s
        (arrayAt (messageKeyAt A) 104 cur rest ∗ stackAt fsp msgKeyLenStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ arrayAt (messageKeyAt A) 104 cur rest ∗ stackAt fsp msgKeyLenStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧
          sm.readReg64 .x20 = v20 ∧
          sm.readReg64 .x21 = v21 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (acc + mksBodyLen (rest.map Prod.snd))) := by
  have hbody := chainLen_mk_body_ext (b := b) (ext := ext)
    hmk_at s0 fsp v20 v21 hfsp_align
  chainLen_fetches_range b (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") (num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")) 300 312
  dsimp only [SP2Ext, contractProg, chainLenName, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur acc s Frame _ hlen hfit hpc hrun hpres hx19 hx20 hx21 hx22 hx23
    have hfit_mk : acc + mkBodyLen mk < 2 ^ 64 := by
      simp only [List.map_cons, mksBodyLen] at hfit; omega
    have hfit_tl : (acc + mkBodyLen mk) + mksBodyLen (tl.map Prod.snd) < 2 ^ 64 := by
      simp only [List.map_cons, mksBodyLen] at hfit; omega
    rw [show arrayAt (messageKeyAt A) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A (pin, mk) cur ∗ arrayAt (messageKeyAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_mk]
    refine SepWP.seq_clean (mid := entry + bv% (300))
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) acc pin mk s
        (arrayAt (messageKeyAt A) 104 (cur + 104#64) tl ∗ Frame)
        hfit_mk hpc hrun hpres hx19 hx20 hx21 hx22 hx23) ?_
    intro s1 hpc1 hrun1 ⟨⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.map_nil,
        mksBodyLen, Nat.add_zero, arrayAt, emp_sepConj] at hx23_1 ⊢
      wp_steps
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len : (hd2 :: tl2).length * 104 < 2 ^ 63 := Getters.DropGlueFacts.tail_len_mul_lt hlen
      rw [show ((pin, mk) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          Getters.DropGlueFacts.ofNat_succ_eq_add_one] at hx23_1
      have hne1 : (BitVec.ofNat 64 (hd2 :: tl2).length + 1#64 != 1#64) = true := by
        have h := Getters.DropGlueFacts.ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
        simpa [bne] using h
      wp_steps
      rw [sep_push_mk]
      have hacc_assoc :
          acc + mksBodyLen (List.map Prod.snd ((pin, mk) :: hd2 :: tl2)) =
            (acc + mkBodyLen mk) + mksBodyLen (List.map Prod.snd (hd2 :: tl2)) := by
        simp only [List.map_cons, mksBodyLen, Nat.add_assoc]
      rw [hacc_assoc]
      refine SepWP.mono
        (ih (cur + 104#64) (acc + mkBodyLen mk) _ (messageKeyAt A (pin, mk) cur ∗ Frame)
          htl_ne htl_len hfit_tl rfl (by assumption)
          ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
          rfl hx20_1 hx21_1 hx22_1 rfl) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [sep_rejoin_mk]
      exact Entails.refl _

theorem chainLen_ok_ext (b : BitVec 64) (ext : String → Option (State → State)) (A : RustAlloc)
    (hmk : subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr msgKeyLenName) (msgKeyLenSpec A)) :
    subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr chainLenName) (chainLenSpec A) := by
  have hmk_at : subroutine_ok (SP2Ext b ext)
      ((SP2Ext b ext).fnAddr chainLenName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len"))
      (msgKeyLenSpec A) := by
    rw [← msgKeyLen_fnAddr_eq_ext]
    exact hmk
  simp only [chainLenSpec]
  have hphases : PLift (_ ∧ _ ∧ _ ∧ _) :=
    ⟨⟨chainLen_senderRatchetKey_ext (b := b) (ext := ext) A,
      chainLen_senderRatchetKeyPrivate_ext (b := b) (ext := ext) A,
      chainLen_chainKey_ext (b := b) (ext := ext) A,
      chainLen_mk_loop_ext (b := b) (ext := ext) hmk_at⟩⟩
  chainLen_fetches_range b (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") (num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")) 236 256
  chainLen_fetches_range b (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len") (num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")) 312 356
  have hname_eq : chainLenName =
      "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" := rfl
  have hsp2_eq : SP2Ext b ext =
      libsignalSessionCode.rebase b (Rust.withPanics ext) := rfl
  rw [hname_eq, hsp2_eq] at hphases ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" = entry
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨a, g, c⟩
  dsimp only at hpre ⊢
  rcases hphases with ⟨⟨hp1a, hp1b, hp2, hloop⟩⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hfit_all : (encChainMem (g, c)).length < 2 ^ 32 := by assumption
  have halign : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have halign' : s0.sp &&& 15#64 = 0#64 := by simpa [beq_iff_eq] using halign
  have hfsp_align : ((s0.sp - 64#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 64#64 halign (by decide)
  have hfsp_align' : (s0.sp - 64#64) &&& 15#64 = 0#64 := by
    simpa [beq_iff_eq] using hfsp_align
  rw [encChainMem_length] at hfit_all
  nth_rw 1 [stackAt_chainLen_split s0.sp]
  rw [cells8_sub64_eq s0.sp]
  wp_pull_exists
  rename_i v0 v1 v2 v3 v4 v5 v6 v7
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_expose A g c a)) ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hsrk_des, hmax, hklen, hsrk_lt, hpriv_lt, hck_lt, hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  set s1 := (bytesField 1 g.srk.bytes).length
  set s2 := (bytesField 2 g.priv.bytes).length
  set s3 := (msgField 3 (c.chainKey.map encChainKey)).length
  set s4 := ((c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length
  have hfit12 : s1 + s2 < 2 ^ 64 := by omega
  have hfit123 : (s1 + s2) + s3 < 2 ^ 64 := by omega
  have hfit1234 : ((s1 + s2) + s3) + s4 < 2 ^ 64 := by omega
  have hpre_eq :
      chainFieldsAt A g c a ∗
        arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack ∗
        chainLenSavedAt s0.sp v0 v1 v2 v3 v4 v5 v6 v7 =
      chainFieldsAt A g c a ∗
        chainLenSavedAt s0.sp v0 v1 v2 v3 v4 v5 v6 v7 ∗
        (arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
          stackAt (s0.sp - 64#64) msgKeyLenStack) := by
    ac_rfl
  rw [hpre_eq]
  refine SepWP.seq_clean
    (hp1a g c a hsrk_lt v0 v1 v2 v3 v4 v5 v6 v7 s0
      (arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack)
      (by assumption) (by assumption) halign hx0) ?_
  intro s1_st hpc1 hrun1 ⟨hpres1, hx0_1, hx8_1⟩
  let SavedSlot : SepProp :=
    chainLenSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x23) v3 (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)
  let RestFrame : SepProp :=
    SavedSlot ∗
      (arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack)
  refine SepWP.seq_clean
    (hp1b g c a s1 hpriv_lt hfit12 s0 s1_st (s0.sp - 64#64) RestFrame
      hpc1 hrun1 hpres1 hx0_1 hx8_1) ?_
  intro s2_st hpc2 hrun2 ⟨hpres2, hx0_2, hx8_2⟩
  refine SepWP.seq_clean
    (hp2 g c a (s1 + s2) hck_lt hfit123 s0 s2_st (s0.sp - 64#64) RestFrame
      hpc2 hrun2 hpres2 hx0_2 hx8_2) ?_
  intro s3_st hpc3 hrun3 ⟨hpres3, hx0_3, hx20_3⟩

  have hrestore_all :
      chainFieldsAt A g c a ∗
        arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack ∗
        SavedSlot ⊢
      protoChainAt A (g, c) a ∗ stackAt s0.sp chainLenStack := by
    have hpull :
        (chainFieldsAt A g c a ∗
          arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys) ∗
          stackAt (s0.sp - 64#64) msgKeyLenStack ∗
          SavedSlot) =
        ((chainFieldsAt A g c a ∗
          arrayAt (messageKeyAt A) 104 g.mkPtr (g.keys.zip c.messageKeys)) ∗
         (stackAt (s0.sp - 64#64) msgKeyLenStack ∗ SavedSlot)) := by
      ac_rfl
    rw [hpull]
    exact sepConj_mono
      (chainAt_restore A g c a hsrk_des hmax hklen hlen_le hcap_lt hptr_ne)
      (stack_restore_chainLen s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x23) v3 (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19))
  cases hmks : g.keys.zip c.messageKeys with
  | nil =>
    have hcmk_nil : c.messageKeys = [] := by
      have h := zip_map_snd_eq hklen
      rw [hmks, List.map_nil] at h
      exact h.symm
    have hs4_0 : s4 = 0 := by simp [s4, hcmk_nil]
    have henc_eq : (encChainMem (g, c)).length = (s1 + s2) + s3 := by
      rw [encChainMem_length]
      change s1 + s2 + s3 + s4 = (s1 + s2) + s3
      omega
    rcases hpres3 with ⟨hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩
    dsimp only [RestFrame, SavedSlot, chainFieldsAt, chainLenSavedAt]
    simp only [hmks, List.length_nil, henc_eq]
    have hcc0 := ule_zero_64 0#64
    have hovf0 := ult_zero_64 (BitVec.ofNat 64 ((s1 + s2) + s3))
    wp_steps
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq ?_) hrestore_all) ?_
    · dsimp only [SavedSlot, chainFieldsAt, chainLenSavedAt]; simp only [hmks]; ac_rfl
    · wp_done
  | cons hd tl =>
    have hmks_ne : hd :: tl ≠ [] := List.cons_ne_nil _ _
    have hmks_len_lt : (hd :: tl).length * 104 < 2 ^ 63 := by
      simpa [hmks] using hlen_lt
    have hne0 := Getters.DropGlueFacts.ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hmks_len_lt
    have hmap_snd : (hd :: tl).map Prod.snd = c.messageKeys := by
      rw [← hmks]
      exact zip_map_snd_eq hklen
    have hlen_mks : (hd :: tl).length = c.messageKeys.length := by
      rw [← hmks]
      exact zip_length_eq hklen
    have hs4_eq : s4 = mksBodyLen c.messageKeys + c.messageKeys.length :=
      flatten_lenField4_length c.messageKeys
    have hfit_loop : 0 + mksBodyLen ((hd :: tl).map Prod.snd) < 2 ^ 64 := by
      rw [Nat.zero_add, hmap_snd]; omega
    refine SepWP.seq_clean (mid := entry + bv% (256))
      (P_mid := arrayAt (messageKeyAt A) 104 g.mkPtr (hd :: tl) ∗
        stackAt (s0.sp - 64#64) msgKeyLenStack ∗
        (chainFieldsAt A g c a ∗ SavedSlot))
      (Q := fun sm =>
        Saved64Preserved s0 sm (s0.sp - 64#64) ∧
        sm.readReg64 .x19 = g.mkPtr ∧
        sm.readReg64 .x20 = BitVec.ofNat 64 ((s1 + s2) + s3) ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (hd :: tl).length ∧
        sm.readReg64 .x22 = 0#64 ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (hd :: tl).length)
      ?_ ?_
    · rcases hpres3 with ⟨hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩
      dsimp only [RestFrame, chainFieldsAt]
      simp only [hmks]
      change s3_st.readReg64 .x20 = BitVec.ofNat 64 ((s1 + s2) + s3) at hx20_3
      wp_steps
      refine SepWP.align_pre (by ac_rfl) ?_
      wp_done
    · intro s4_st hpc4 hrun4 ⟨hpres4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4⟩
      refine SepWP.seq_clean (mid := entry + bv% (312))
        (hloop s0 (s0.sp - 64#64) (BitVec.ofNat 64 ((s1 + s2) + s3)) (BitVec.ofNat 64 (hd :: tl).length)
          hfsp_align (hd :: tl) g.mkPtr 0 s4_st (chainFieldsAt A g c a ∗ SavedSlot)
          hmks_ne hmks_len_lt hfit_loop hpc4 hrun4 hpres4
          hx19_4 hx20_4 hx21_4 hx22_4 hx23_4) ?_
      intro s5_st hpc5 hrun5 ⟨⟨hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5⟩, hx20_5, hx21_5, hx22_5⟩
      rw [Nat.zero_add, hmap_snd] at hx22_5
      rw [hlen_mks] at hx21_5
      have hfit_s4 : mksBodyLen c.messageKeys + c.messageKeys.length < 2 ^ 64 := by omega
      have hadd_s4 :
          BitVec.ofNat 64 (mksBodyLen c.messageKeys) + BitVec.ofNat 64 c.messageKeys.length =
            BitVec.ofNat 64 (mksBodyLen c.messageKeys + c.messageKeys.length) :=
        (BitVec.ofNat_add (mksBodyLen c.messageKeys) c.messageKeys.length).symm
      have hovf_s4' := ult_ofNat_add_left_of_lt hfit_s4
      have hovf_s4 :
          BitVec.ult
            (BitVec.ofNat 64 (mksBodyLen c.messageKeys) + BitVec.ofNat 64 c.messageKeys.length)
            (BitVec.ofNat 64 (mksBodyLen c.messageKeys)) = false := by
        rw [hadd_s4]
        exact hovf_s4'
      have hfit_tot : ((s1 + s2) + s3) + (mksBodyLen c.messageKeys + c.messageKeys.length) < 2 ^ 64 := by omega
      have hovf_total := ult_ofNat_add_of_lt hfit_tot
      have hadd_total := bv_add_ofNat_comm ((s1 + s2) + s3) (mksBodyLen c.messageKeys + c.messageKeys.length)
      have henc_eq : (encChainMem (g, c)).length =
          ((s1 + s2) + s3) + (mksBodyLen c.messageKeys + c.messageKeys.length) := by
        rw [encChainMem_length, ← hs4_eq]
      dsimp only [SavedSlot, chainLenSavedAt]
      simp only [henc_eq]
      wp_steps
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq ?_) hrestore_all) ?_
      · dsimp only [SavedSlot, chainFieldsAt, chainLenSavedAt]; simp only [hmks]; ac_rfl
      · wp_done

/-! ## Relocatable `[LibsignalPlacement]` proofs -/

section Placed

open CryptoVerification.E2E.Record.Placed

/-- Block `117` (`Vec<Vec<u8>>::clone` on empty source) wrapped in `withLsCodeLoaded lsmpl`. -/
theorem vecVecCloneEmpty_placed_ok_ext [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_117 H) (blkPl_117).base
      (withLsCodeLoaded lsmpl vecVecCloneEmptySpec) :=
  subroutine_ok_withLsCodeLoaded_of_plain (vecVecCloneEmpty_placed_ok H)

theorem vecVecCloneEmpty_placed_ok_cl [LibsignalPlacement]
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 117)
      (withLsCl lsmpl vecVecCloneEmptySpec) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (vecVecCloneEmpty_placed_ok_ext H)

/-- Block `118` (`MessageKey::encoded_len`) wrapped in `withLsCodeLoaded lsmpl`. -/
theorem msgKeyLen_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (msgKeyLen_placed_ok A H)

theorem msgKeyLen_placed_ok_cl [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 118)
      (withLsCl lsmpl (msgKeyLenSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (msgKeyLen_placed_ok_ext A H)

/-- Block `88` (`Chain::encoded_len`) under `[LibsignalPlacement]`. -/
theorem chainLen_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)) :=
  chainLen_placed_ok A H

theorem chainLen_placed_ok_cl [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 88)
      (withLsCl lsmpl (chainLenSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (chainLen_placed_ok A H)

end Placed

end CryptoVerification.E2E.Record.Serialization

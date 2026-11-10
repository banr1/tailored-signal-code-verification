/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymB
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymD
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymE
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.FromRecordCalleesCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import ProofLib.SepLogic.SymWP
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Body proof of `SessionRecord::serialize` (`0x1857c`) from callee contracts

Proves `serialize_ok_of_leaves` and its relocatable `[LibsignalPlacement]` counterparts (block `52`)
across the six stages of `SessionRecord::serialize`:
1. Optional `SessionStructure::clone` (`0x240f0`) of `current_session` (`self + 0x18`) into stack scratch;
2. `Vec<Vec<u8>>::clone` (`0x2c75c`) of the empty `previous_sessions` vector;
3. `SessionStructure::encoded_len` (`0x25fd0`) and exact buffer allocation via `__rust_alloc`;
4. Writing outer key `0x0a`, payload length varint (`encode_varint`), and `SessionStructure::encode_raw`;
5. Dropping the cloned `SessionStructure` (`0x25b4`);
6. Writing `Ok(v)` (`okTagVec = -2`) into the `sret` output slot `x8`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
  encSessionMem lenField encodeVarint
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  serialize_varintLen_eq serialize_varintLen_bvShift_eq lenField_one_bv_eq
attribute [local wp_norm] serialize_varintLen_eq serialize_varintLen_bvShift_eq lenField_one_bv_eq

private def serializeNoneSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (self, out, prevPtr) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = out⌝ ∗
      ((self + 8#64) ↦₆₄ prevPtr) ∗ ((self + 16#64) ↦₆₄ 0#64) ∗
      ((self + 24#64) ↦₆₄ noneCap) ∗
      memRegion out 32 ∗ stackAt s.sp serializeStack
  post := fun (self, out, prevPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((self + 8#64) ↦₆₄ prevPtr) ∗ ((self + 16#64) ↦₆₄ 0#64) ∗
      ((self + 24#64) ↦₆₄ noneCap) ∗
      (out ↦₆₄ okTagVec) ∗ vecU8 A (out + 8#64) [] ∗
      stackAt s0.sp serializeStack

private theorem memRegion_out32_cells (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ out3 : BitVec 64, ∃∗ out2 : BitVec 64, ∃∗ out1 : BitVec 64, ∃∗ out0 : BitVec 64,
        (out ↦₆₄ out0) ∗ ((out + 8#64) ↦₆₄ out1) ∗
        ((out + 16#64) ↦₆₄ out2) ∗ ((out + 24#64) ↦₆₄ out3)) := by
  rw [memRegion_split out 8 24 (by decide),
    memRegion_split (out + 8#64) 8 16 (by decide),
    memRegion_split (out + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight out,
    ProofLib.memRegion_eight (out + 8#64),
    ProofLib.memRegion_eight (out + 8#64 + 8#64),
    ProofLib.memRegion_eight (out + 8#64 + 8#64 + 8#64)]
  have h16 : out + 8#64 + 8#64 = out + 16#64 := by rw [BitVec.add_assoc]; rfl
  have h24 : out + 16#64 + 8#64 = out + 24#64 := by rw [BitVec.add_assoc]; rfl
  rw [h16, h24]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem memRegion_out32_stack_none (out sp : BitVec 64) :
    memRegion out 32 ∗ stackAt sp serializeStack =
      (∃∗ out3 : BitVec 64, ∃∗ out2 : BitVec 64, ∃∗ out1 : BitVec 64, ∃∗ out0 : BitVec 64,
        (out ↦₆₄ out0) ∗ ((out + 8#64) ↦₆₄ out1) ∗
        ((out + 16#64) ↦₆₄ out2) ∗ ((out + 24#64) ↦₆₄ out3)) ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ bs336 : List (BitVec 8),
       ∃∗ w_none : BitVec 64,
        ⌜bs336.length = 336⌝ ∗
        stackAt (sp - 800#64) serializeSubStack ∗
        memRegion (sp - 800#64) 24 ∗
        ((sp - 776#64) ↦₆₄ w_none) ∗
        memRegion (sp - 768#64) 336 ∗
        ((sp - 432#64) ↦ₛ bs336) ∗
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  rw [memRegion_out32_cells, stackAt_serialize_none_pre]

private theorem sepWP_exists_left_sep {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {post : State → SepProp → Prop}
    (h : ∀ x, SepWP prog pc s (P x ∗ F) post) :
    SepWP prog pc s ((∃∗ x, P x) ∗ F) post := by
  rw [sepExists_sepConj_left]
  exact SepWP.exists_left h

private theorem sepWP_pure_left_sep {prog : Program} {pc : BitVec 64} {s : State}
    {φ : Prop} {P F : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog pc s (P ∗ F) post) :
    SepWP prog pc s ((⌜φ⌝ ∗ P) ∗ F) post := by
  rw [sepConj_assoc]
  exact SepWP.pure_elim h

private theorem vecU8_nil_from_out_cells (A : RustAlloc) (out : BitVec 64) :
    (((out + 8#64) ↦₆₄ 0#64) ∗ ((out + 16#64) ↦₆₄ 1#64) ∗ ((out + 24#64) ↦₆₄ 0#64)) ⊢
      vecU8 A (out + 8#64) [] := by
  have hp := pointsTo64_pair_out out 0#64 1#64
  have hpull :
      (((out + 8#64) ↦₆₄ 0#64) ∗ ((out + 16#64) ↦₆₄ 1#64) ∗ ((out + 24#64) ↦₆₄ 0#64)) =
      ((((out + 8#64) ↦₆₄ 0#64) ∗ ((out + 16#64) ↦₆₄ 1#64)) ∗ ((out + 24#64) ↦₆₄ 0#64)) := by
    ac_rfl
  rw [hpull, ← hp]
  exact vecU8_nil_from_out_stores A out

private theorem vecU8_from_out_cells (A : RustAlloc) (out cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (((out + 8#64) ↦₆₄ cap) ∗ ((out + 16#64) ↦₆₄ ptr) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      RustHeap.vecU8Buf A cap ptr bs) ⊢
      vecU8 A (out + 8#64) bs := by
  have hp := pointsTo64_pair_out out cap ptr
  have hpull :
      (((out + 8#64) ↦₆₄ cap) ∗ ((out + 16#64) ↦₆₄ ptr) ∗
        ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs) =
      ((((out + 8#64) ↦₆₄ cap) ∗ ((out + 16#64) ↦₆₄ ptr)) ∗
        ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs) := by
    ac_rfl
  rw [hpull, ← hp]
  exact vecU8_from_out_stores A out cap ptr bs

private theorem sessionAt_eq_head_tail (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (s : LibsignalSessionApi.Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s =
      ∃∗ bs336 : List (BitVec 8),
        ⌜bs336.length = 336 ∧ G.localIk.cap.toNat < 2 ^ 63 ∧
          SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)⌝ ∗
        (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦ₛ bs336) ∗ sessionAtHeap A G s := by
  apply ProofLib.sepProp_eq_of_entails
  · exact sessionAt_unpack_head_tail A ss G s
  · apply Entails.sepExists_elim; intro bs336
    apply Entails.pure_left; rintro ⟨_, _, hinl⟩
    exact sessionAt_pack_head_tail A ss G s hinl

private theorem vecHeader_cells_800 (sp : BitVec 64) :
    (((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64)) =
      vecHeader (sp - 800#64) 0#64 8#64 0#64 := by
  unfold vecHeader
  have e1 : sp - 800#64 + 8#64 = sp - 792#64 := bv_sub_add_lit sp 800 8
  have e2 : sp - 800#64 + 16#64 = sp - 784#64 := bv_sub_add_lit sp 800 16
  rw [e1, e2]

private theorem repack_stack_some_cells (sp w0 w1 w2 : BitVec 64) :
    (stackAt (sp - 800#64) serializeSubStack ∗
      ((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64) ∗
      memRegion (sp - 776#64) 344 ∗
      ((sp - 432#64) ↦₆₄ w0) ∗
      ((sp - 424#64) ↦₆₄ w1) ∗
      ((sp - 416#64) ↦₆₄ w2) ∗
      memRegion (sp - 408#64) 312 ∗
      cells (sp - 96#64) 12) ⊢
      stackAt sp serializeStack := by
  have hp : ((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1) =
      ((sp - 432#64) ↦₁₂₈ (w1 ++ w0)) := pointsTo64_pair_sub sp 432 w0 w1
  have hv := vecHeader_cells_800 sp
  have hpull :
      (stackAt (sp - 800#64) serializeSubStack ∗
        ((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64) ∗
        memRegion (sp - 776#64) 344 ∗
        ((sp - 432#64) ↦₆₄ w0) ∗
        ((sp - 424#64) ↦₆₄ w1) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) =
      (stackAt (sp - 800#64) serializeSubStack ∗
        (((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64)) ∗
        memRegion (sp - 776#64) 344 ∗
        (((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1)) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) := by
    ac_rfl
  rw [hpull, hv, hp]
  exact repack_stack_some sp (w1 ++ w0) w2

private theorem repack_stack_none_cells (sp wn w0 w1 w2 : BitVec 64)
    {bs336 : List (BitVec 8)} (h336 : bs336.length = 336) :
    (stackAt (sp - 800#64) serializeSubStack ∗
      ((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64) ∗
      ((sp - 776#64) ↦₆₄ wn) ∗
      ((sp - 768#64) ↦ₛ bs336) ∗
      ((sp - 432#64) ↦₆₄ w0) ∗
      ((sp - 424#64) ↦₆₄ w1) ∗
      ((sp - 416#64) ↦₆₄ w2) ∗
      memRegion (sp - 408#64) 312 ∗
      cells (sp - 96#64) 12) ⊢
      stackAt sp serializeStack := by
  have hp : ((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1) =
      ((sp - 432#64) ↦₁₂₈ (w1 ++ w0)) := pointsTo64_pair_sub sp 432 w0 w1
  have hv := vecHeader_cells_800 sp
  have hpull :
      (stackAt (sp - 800#64) serializeSubStack ∗
        ((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64) ∗
        ((sp - 776#64) ↦₆₄ wn) ∗
        ((sp - 768#64) ↦ₛ bs336) ∗
        ((sp - 432#64) ↦₆₄ w0) ∗
        ((sp - 424#64) ↦₆₄ w1) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) =
      (stackAt (sp - 800#64) serializeSubStack ∗
        (((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64)) ∗
        ((sp - 776#64) ↦₆₄ wn) ∗
        ((sp - 768#64) ↦ₛ bs336) ∗
        (((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1)) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) := by
    ac_rfl
  rw [hpull, hv, hp]
  exact repack_stack_none sp wn (w1 ++ w0) w2 h336

private theorem serialize_none_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hVV : OkAt b C ctl abs vecVecCloneName vecVecCloneEmptySpec) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName)
      (serializeNoneSpec A) := by
  unfold serializeNoneSpec
  simp only [noneCap, okTagVec, memRegion_out32_stack_none,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff serializeName = 0x1857c :=
    libsignalSessionCode_fnOff_serialize
  have hmemcpy := framelessMemcpy_ok_at (b := b) (C := C) (ctl := ctl) (abs := abs)
    (name := serializeName) (k := num% (ls_off% "memcpy" - 0x1857c))
  have hvv := vecVecClone_sub_ok hVV
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0 56
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x5c 48
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x10c 12
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x128 4
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x188 20
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x1a8 24
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x2b4 32
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x2dc 8
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x310 8
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x32c 32
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨self, out, prevPtr⟩ := x
  dsimp only at *
  wp_steps
  wp_apply
  wp_simp_pre [vecHeader, arm64_norm]
  wp_steps
  rw [← h]
  wp_apply
  refine SepWP.fold (bytes336_to_w012 s0.sp h) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro w0
  apply sepWP_exists_left_sep; intro w1
  apply sepWP_exists_left_sep; intro w2
  wp_steps
  refine SepWP.fold (vecU8_nil_from_out_cells A out) (by sep_focus) ?_
  refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (repack_stack_none_cells s0.sp _ _ _ _ h) (by sep_focus) ?_
  wp_done

private theorem sessionAt_pack_776 (A : RustAlloc) (sp : BitVec 64)
    (G : SessionGhost) (s : LibsignalSessionApi.Session (List (BitVec 8)))
    {bs336 : List (BitVec 8)}
    (hinl : SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)) :
    (((sp - 776#64) ↦₆₄ G.localIk.cap) ∗ ((sp - 768#64) ↦ₛ bs336) ∗ sessionAtHeap A G s) ⊢
      sessionStateReprAt A (sp - 776#64) G s := by
  have h := sessionAt_pack_head_tail A (sp - 776#64) G s hinl
  have e : sp - 776#64 + 8#64 = sp - 768#64 := bv_sub_add_lit sp 776 8
  rwa [e] at h

private theorem sessionAt_unpack_800 (A : RustAlloc) (sp : BitVec 64)
    (G : SessionGhost) (s : LibsignalSessionApi.Session (List (BitVec 8))) :
    sessionStateReprAt A (sp - 800#64) G s ⊢
      ∃∗ bs336 : List (BitVec 8),
        ⌜bs336.length = 336 ∧ G.localIk.cap.toNat < 2 ^ 63 ∧
          SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)⌝ ∗
        ((sp - 800#64) ↦₆₄ G.localIk.cap) ∗ ((sp - 792#64) ↦ₛ bs336) ∗ sessionAtHeap A G s := by
  have h := sessionAt_unpack_head_tail A (sp - 800#64) G s
  have e : sp - 800#64 + 8#64 = sp - 792#64 := bv_sub_add_lit sp 800 8
  rwa [e] at h

private theorem memRegion_out32_stack_some (out sp : BitVec 64) :
    memRegion out 32 ∗ stackAt sp serializeStack =
      (∃∗ out3 : BitVec 64, ∃∗ out2 : BitVec 64, ∃∗ out1 : BitVec 64, ∃∗ out0 : BitVec 64,
        (out ↦₆₄ out0) ∗ ((out + 8#64) ↦₆₄ out1) ∗
        ((out + 16#64) ↦₆₄ out2) ∗ ((out + 24#64) ↦₆₄ out3)) ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        stackAt (sp - 800#64) serializeSubStack ∗
        memRegion (sp - 800#64) 344 ∗
        memRegion (sp - 456#64) 24 ∗
        memRegion (sp - 432#64) 336 ∗
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  rw [memRegion_out32_cells, stackAt_serialize_some_pre]

private structure SerializeSomeGhost where
  self : BitVec 64
  out : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : LibsignalSessionApi.Session (List (BitVec 8))

private def serializeSomeSpec (A : RustAlloc) : Spec SerializeSomeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      (lenField 1 (encSessionMem x.G x.sess)).length < 2 ^ 32⌝ ∗
      ((x.self + 8#64) ↦₆₄ x.prevPtr) ∗ ((x.self + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A (x.self + 24#64) x.G x.sess ∗
      A.pool ∗ memRegion x.out 32 ∗ stackAt s.sp serializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((x.self + 8#64) ↦₆₄ x.prevPtr) ∗ ((x.self + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A (x.self + 24#64) x.G x.sess ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (lenField 1 (encSessionMem x.G x.sess)) ∗
      A.pool ∗ stackAt s0.sp serializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem allocFailedIn_of_trace_eq {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢
  rwa [htr] at h

private theorem allowPanic_frame_trace {s0 sm sf : State} {F R : SepProp}
    (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eq htr) h

private theorem allowPanic_entails_trace {s0 sm sf : State} {F : SepProp}
    (htr : sm.trace = s0.trace) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  apply Entails.pure_left; intro h
  exact Entails.pure_right (allocFailedIn_of_trace_eq htr h) (entails_anyHeap _)

open Lean Meta Elab Tactic in
private meta def wppElimSpatialContext (hEq : Ident) : TacticM Unit := do
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hEq:ident]))))
  for _ in [0:64] do
    let g ← getMainGoal
    let ty ← g.withContext (instantiateMVars (← g.getType))
    unless ty.isAppOf ``SepWPp do return
    let P := (ty.getArg! 3).consumeMData
    if P.isAppOfArity ``SepProp.sepExists 2 then
      let wId ← freshIdent `w
      evalTactic (← `(tactic| (apply SepWPp.exists_elim; intro $wId:ident)))
      betaReduceTarget
    else if P.isAppOfArity ``SepProp.sepConj 2 && (P.getArg! 0).isAppOfArity ``SepProp.pure 1 then
      let hId ← freshIdent `hpost
      evalTactic (← `(tactic| (apply SepWPp.pure_elim; intro $hId:ident)))
      wpNormAndSplitHyp hId
    else
      return

open Lean Meta Elab Tactic in
private meta def closeWppCallSiteSetupSubgoals : TacticM Unit := do
  let gs ← getGoals
  let gPc :: gRun :: gSp :: gLr :: rest := gs
    | throwError "wpp_call: unexpected subgoals after applying SepWPp.call"
  setGoals [gPc]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (first | wp_norm_goal | wp_norm_lhs))))) then
    let ty ← gPc.withContext (instantiateMVars (← gPc.getType))
    throwError "wpp_call: call target address does not match callee entry:{indentExpr ty}"
  setGoals [gRun]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close wp_norm_lhs)))) then
    let ty ← gRun.withContext (instantiateMVars (← gRun.getType))
    throwError "wpp_call: failed to prove machine status is `.Running`:{indentExpr ty}"
  setGoals [gSp]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal))))) then
    let ty ← gSp.withContext (instantiateMVars (← gSp.getType))
    throwError "wpp_call: failed to prove 16-byte stack pointer alignment (`s.spAligned = true`):{indentExpr ty}"
  setGoals [gLr]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal))))) then
    let ty ← gLr.withContext (instantiateMVars (← gLr.getType))
    throwError "wpp_call: failed to resolve link register (`s.readReg64 .lr = ret_pc`):{indentExpr ty}"
  setGoals (← rest.filterM fun m => not <$> m.isAssigned)

open Lean Meta Elab Tactic in
local elab "wpp_call " hcall:term:max arg?:(ppSpace colGt term:max)? : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let applyFrameStx ← match arg? with
    | some a => `(tactic| apply (SepWPp.call $hcall (x := $a)))
    | none => `(tactic| apply (SepWPp.call $hcall))
  evalTactic applyFrameStx
  closeWppCallSiteSetupSubgoals
  let gsAfterSetup ← getGoals
  let gPre :: gExit :: gPanic :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call: unexpected subgoals after `SepWPp.call`"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gExit :: gPanic :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he)
    wp_focus_close (wp_unfold_specs; intro _ _ _hp; exact allowPanic_frame_trace (by wp_norm_lhs) _hp)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wppElimSpatialContext hspId

/-! ## `Some` session branch -/

private theorem memRegion_split_init_byte (ptr : BitVec 64) {n : Nat}
    (hpos : 1 ≤ n) (hlt : n < 2 ^ 63) :
    memRegion ptr n =
      (∃∗ b0 : BitVec 8, (ptr ↦₈ b0) ∗ memRegion (ptr + 1#64) (n - 1)) := by
  have h1 : n = 1 + (n - 1) := by omega
  conv => lhs; rw [h1]
  rw [memRegion_split ptr 1 (n - 1) (by omega),
    memRegion_eq_exists_bytes ptr 1 (by decide)]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply ProofLib.sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; intro hlen
    rcases bs with _ | ⟨b0, _ | _⟩ <;> simp at hlen
    rw [pointsToBytes_singleton]
    exact Entails.sepExists_right b0 (Entails.refl _)
  · apply Entails.sepExists_elim; intro b0
    rw [← pointsToBytes_singleton]
    exact Entails.sepExists_right [b0] (Entails.pure_right rfl (Entails.refl _))

private theorem vecU8At_unpack_cells_432 (A : RustAlloc) (sp cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A (sp - 432#64) cap ptr bs =
      (((sp - 432#64) ↦₆₄ cap) ∗ ((sp - 424#64) ↦₆₄ ptr) ∗
        ((sp - 416#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs) := by
  unfold vecU8At RustHeap.vecU8Buf vecHeader
  have e1 : sp - 432#64 + 8#64 = sp - 424#64 := bv_sub_add_lit sp 432 8
  have e2 : sp - 432#64 + 16#64 = sp - 416#64 := bv_sub_add_lit sp 432 16
  rw [e1, e2]
  ac_rfl

private theorem lenField_one_bv_toNat {bs : List (BitVec 8)}
    (h : (lenField 1 bs).length < 2 ^ 32) :
    (BitVec.ofNat 64 (lenField 1 bs).length).toNat = (lenField 1 bs).length := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem cap_lt_not_noneCap {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro heq
  have h1 : (cap + 1#64).toNat = 0 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

@[local simp, local arm64_norm, local wp_norm]
private theorem bv64_ult_zero (x : BitVec 64) : BitVec.ult x 0#64 = false := by
  simp [BitVec.ult]

private theorem lenField_one_branch_conds {bs : List (BitVec 8)}
    (h : (lenField 1 bs).length < 2 ^ 32) :
    BitVec.ule (BitVec.ofNat 64 (lenField 1 bs).length)
      (BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length) = false ∧
    (BitVec.ofNat 64 (lenField 1 bs).length).getLsbD 63 = false ∧
    (BitVec.ofNat 64 (lenField 1 bs).length == 0#64) = false := by
  have hlen := lenField_one_length bs
  refine ⟨?_, ?_, ?_⟩
  · simp only [BitVec.ule, BitVec.toNat_ofNat]
    have h1 : (lenField 1 bs).length % 2 ^ 64 = (lenField 1 bs).length :=
      Nat.mod_eq_of_lt (by omega)
    have h2 : (encodeVarint (BitVec.ofNat 64 bs.length)).length % 2 ^ 64 =
        (encodeVarint (BitVec.ofNat 64 bs.length)).length :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    exact decide_eq_false (by omega)
  · rw [BitVec.getLsbD_ofNat]
    simp only [Nat.reduceLT, decide_true, Bool.true_and]
    exact Nat.testBit_lt_two_pow (by omega)
  · apply beq_false_of_ne
    intro heq
    have h1 : (BitVec.ofNat 64 (lenField 1 bs).length).toNat = 0 :=
      congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    omega

private theorem vecU8At_init_byte_432 (A : RustAlloc) (sp ptr : BitVec 64) (n : Nat) (b0 : BitVec 8)
    (hpos : 1 ≤ n) (hlt : n < 2 ^ 32) (hptr : ptr ≠ 0) :
    (((sp - 432#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      ((sp - 424#64) ↦₆₄ ptr) ∗
      ((sp - 416#64) ↦₆₄ 1#64) ∗
      A.live ptr n 1 ∗ (ptr ↦₈ b0) ∗ memRegion (ptr + 1#64) (n - 1)) ⊢
      vecU8At A (sp - 432#64) (BitVec.ofNat 64 n) ptr [b0] := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e1 : sp - 432#64 + 8#64 = sp - 424#64 := bv_sub_add_lit sp 432 8
  have e2 : sp - 432#64 + 16#64 = sp - 416#64 := bv_sub_add_lit sp 432 16
  have h := vecU8At_init_byte A (sp - 432#64) (BitVec.ofNat 64 n) ptr b0
    (htoNat.symm ▸ hpos) (by omega) hptr
  rwa [htoNat, e1, e2] at h

private theorem lenField_one_cons_eq {bs bs' : List (BitVec 8)} (h : bs = bs') :
    10#8 :: (encodeVarint (BitVec.ofNat 64 bs'.length) ++ bs) = lenField 1 bs' := by
  subst h
  exact (lenField_one_eq bs).symm

section SerializeSomeIrred
attribute [local irreducible] Program.fnOff reaches_pc sessionStateReprAt sessionStateAt

set_option maxHeartbeats 800000 in
private theorem serialize_some_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (hClone : OkAt b C ctl abs sessionCloneName (sessionCloneSpec A))
    (hVV : OkAt b C ctl abs vecVecCloneName vecVecCloneEmptySpec)
    (hLen : OkAt b C ctl abs sessionLenName (sessionLenSpec A))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hRaw : OkAt b C ctl abs encodeRawName (encodeRawSpec A))
    (hDrop : FromRecordCallees.DropSessionStructureLocal1Ok b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr serializeName)
      (serializeSomeSpec A) := by
  unfold serializeSomeSpec
  simp only [okTagVec, memRegion_out32_stack_some,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff serializeName = 0x1857c :=
    libsignalSessionCode_fnOff_serialize
  have hmemcpy := framelessMemcpy_ok_at (b := b) (C := C) (ctl := ctl) (abs := abs)
    (name := serializeName) (k := num% (ls_off% "memcpy" - 0x1857c))
  have hshim := noAllocShim_ok_at (b := b) (C := C) (ctl := ctl) (abs := abs)
    (name := serializeName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x1857c))
  have hpanic := panic_at_handle_error_norm (b := b) (C := C) (ctl := ctl) (abs := abs)
    (name := serializeName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x1857c))
  have hclone := sessionClone_sub_ok hClone
  have hvv := vecVecClone_sub_ok hVV
  have hlen := sessionLen_sub_ok hLen
  have hev := encodeVarint_sub_ok hEV
  have hraw := encodeRaw_sub_ok hRaw
  have hdrop := dropLocal1_sub_ok hDrop
  have halloc := alloc_sub_ok (b := b) (C := C) (ctl := ctl) hA
  clear hClone hVV hLen hEV hRaw hDrop
  code_fetches_range CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0 196
  code_fetches_range CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x10c 160
  code_fetches_range CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x1bc 4
  code_fetches_range CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x2b4 48
  code_fetches_range CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x310 8
  code_fetches_range CryptoVerification.libsignalSessionCode serializeBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x1857c 0x32c 32
  wpp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨self, out, prevPtr, G, sess⟩ := x
  dsimp only at *
  apply SepWPp.of_sepWP (mid := entry + 47988#64)
  refine SepWP.fold (sessionAt_unpack_head_tail A (self + 24#64) G sess) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro bs336_self
  apply sepWP_pure_left_sep; rintro ⟨hbs336_self, hcap_self, hinl_self⟩
  have hcmn_self : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCap hcap_self
  wp_steps
  refine SepWP.fold (sessionAt_pack_head_tail A (self + 24#64) G sess hinl_self) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpp_call hclone ⟨s0.sp - 800#64, self + 24#64, G, sess⟩
  have heq_enc : encSessionMem w sess = encSessionMem G sess := hpost
  clear hclone bs336_self hbs336_self hcap_self hinl_self hcmn_self
  apply SepWPp.of_sepWP (mid := entry + 320#64)
  refine SepWP.fold (sessionAt_unpack_800 A s0.sp w sess) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro bs336_clone
  apply sepWP_pure_left_sep; rintro ⟨hbs336_clone, hcap_clone, hinl_clone⟩
  have hcmn_clone : (w.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCap hcap_clone
  wp_steps
  rw [← hbs336_clone]
  wp_apply using hmemcpy
  refine SepWP.fold (repack_frame_368 s0.sp w.localIk.cap hbs336_clone) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro w_none
  wp_steps
  wp_apply using hvv
  wp_simp_pre [vecHeader, arm64_norm]
  wp_steps
  rw [← hbs336_clone]
  wp_apply using hmemcpy
  refine SepWP.fold (sessionAt_pack_776 A s0.sp w sess hinl_clone) (by sep_focus) ?_
  refine SepWP.fold (bytes336_to_w012 s0.sp hbs336_clone) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro w0
  apply sepWP_exists_left_sep; intro w1
  apply sepWP_exists_left_sep; intro w2
  wp_steps
  clear hvv hmemcpy bs336_clone hbs336_clone hcap_clone hinl_clone w_none
  have hlen_bounds_G : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32 := by
    assumption
  obtain ⟨hbs_lt_G, hlf_pos_G, hlf_lt63_G, hlayout_G, hv_lt62_G, hv_le_lf_G, hraw_lt_G⟩ :=
    lenField_one_bounds hlen_bounds_G
  obtain ⟨hbr_ls_G, hbr_tbz_G, hbr_cbz_G⟩ := lenField_one_branch_conds hlen_bounds_G
  have hcap_toNat_G := lenField_one_bv_toNat hlen_bounds_G
  have hex_pow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_apply using hlen with ⟨s0.sp - 776#64, w, sess⟩
  wp_steps
  wp_apply using hshim
  wp_steps
  wp_apply using halloc
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  clear hshim halloc hex_pow
  wp_clear_temps
  by_cases hp0 : sf_6.readReg64 .x0 = 0#64
  · conv => arg 4; simp only [hp0, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_fail => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x1857c))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hp0' : sf_6.readReg64 .x0 ≠ 0 := hp0
    have hp0_beq : (sf_6.readReg64 .x0 == 0#64) = false := beq_false_of_ne hp0
    conv => arg 4; simp only [hp0', ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨halign, htr_alloc⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 18446744073709464356#64)
    rw [memRegion_split_init_byte (sf_6.readReg64 .x0) hlf_pos_G hlf_lt63_G]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro b0
    wp_steps
    wp_apply using hlen with ⟨s0.sp - 776#64, w, sess⟩
    wp_steps
    refine SepWP.fold (vecU8At_init_byte_432 A s0.sp (sf_6.readReg64 .x0)
      (lenField 1 (encSessionMem G sess)).length 0x0a#8 hlf_pos_G hlen_bounds_G hp0')
      (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    wpp_call hev ⟨BitVec.ofNat 64 (encSessionMem G sess).length, s0.sp - 432#64,
      BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length,
      sf_6.readReg64 .x0, [0x0a#8]⟩
    clear hlen hev b0 hlf_pos_G hlf_lt63_G hlen_bounds_G
    apply SepWPp.of_sepWP (mid := entry + 18446744073709471676#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    wpp_call hraw ⟨s0.sp - 776#64, w, sess, s0.sp - 432#64, _, _,
      [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩
    clear hraw hpanic hA hfn hbs_lt_G hlayout_G hraw_lt_G
      hbr_ls_G hbr_tbz_G hbr_cbz_G hcap_toNat_G hp0_beq halign
    apply SepWPp.of_sepWP_ret
    rw [lenField_one_cons_eq heq_enc, vecU8At_unpack_cells_432]
    wp_steps
    refine SepWP.fold (sessionAt_entails_sessionStateAt A (s0.sp - 776#64) w sess) (by sep_focus) ?_
    wp_call hdrop (x := ⟨s0.sp - 776#64, w, sess.state⟩)
    wp_steps
    conv => arg 4; simp only [*]
    refine SepWP.fold (vecU8_from_out_cells A out _ _ (lenField 1 (encSessionMem G sess)))
      (by sep_focus) ?_
    refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (repack_stack_some_cells s0.sp _ _ _) (by sep_focus) ?_
    wp_done

end SerializeSomeIrred

private def prevVecFrame (A : RustAlloc) (r : BitVec 64) (g : RecordGhost) : SepProp :=
  (r ↦₆₄ g.prevCap) ∗ vecBuf A 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr []

private theorem vecAt_empty_split (A : RustAlloc) (r : BitVec 64) (g : RecordGhost) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) r g.prevCap g.prevPtr [] =
      ((r + 8#64) ↦₆₄ g.prevPtr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗ prevVecFrame A r g := by
  unfold vecAt vecHeader prevVecFrame
  simp only [List.length_nil]
  ac_rfl

/-- `SessionRecord::serialize` (`0x1857c`) satisfies `serializeSpec` given `AllocHooks` and its
callee contracts. -/
theorem serialize_ok_of_leaves (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (hClone : OkAt b C ctl abs sessionCloneName (sessionCloneSpec A))
    (hVV : OkAt b C ctl abs vecVecCloneName vecVecCloneEmptySpec)
    (hLen : OkAt b C ctl abs sessionLenName (sessionLenSpec A))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hRaw : OkAt b C ctl abs encodeRawName (encodeRawSpec A))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (hDrop : FromRecordCallees.DropSessionStructureLocal1Ok b C A ctl abs) :
    OkAt b C ctl abs serializeName (serializeSpec A) := by
  have _ := hDR
  have hnone := serialize_none_ok b C A ctl abs hVV
  have hsome := serialize_some_ok b C A ctl abs hA hClone hVV hLen hEV hRaw hDrop
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  rcases hcur_g : x.g.cur with _ | G <;> rcases hcur_r : x.r.currentSession with _ | sess
  ·
    have henc : encRecordMem x.g x.r = [] := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    let F := prevVecFrame A x.self x.g ∗ memRegion (x.self + 32#64) 336 ∗ A.pool
    have hpre' : s0.mem ⊨ (serializeNoneSpec A).pre (x.self, x.out, x.g.prevPtr) s0 ∗ (F ∗ R) := by
      simp only [serializeSpec, serializeNoneSpec, sessionRecordAt, hcur_g, hcur_r,
        vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨⟨hpre.1.1, hpre.1.2.1⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre.2
    refine hnone.mono_outcome (x.self, x.out, x.g.prevPtr) (F ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
    rcases hout with ⟨h1, h2, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_hoom_st, _hoom_post⟩
    rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
    · refine Or.inl ⟨h1, h2, ?_⟩
      simp only [serializeSpec, serializeNoneSpec, sessionRecordAt, hcur_g, hcur_r, henc,
        vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost.2
    · exact False.elim (not_satisfies_false_sepConj hpan)
    · exact False.elim (not_satisfies_false_sepConj hex)
  ·
    simp only [serializeSpec, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    simp only [serializeSpec, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    have henc : encRecordMem x.g x.r = lenField 1 (encSessionMem G sess) := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    let F := prevVecFrame A x.self x.g
    have hpre' : s0.mem ⊨ (serializeSomeSpec A).pre ⟨x.self, x.out, x.g.prevPtr, G, sess⟩ s0 ∗ (F ∗ R) := by
      simp only [serializeSpec, serializeSomeSpec, sessionRecordAt, hcur_g, hcur_r, henc,
        vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨hpre.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre.2
    refine hsome.mono_outcome ⟨x.self, x.out, x.g.prevPtr, G, sess⟩ (F ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
    rcases hout with ⟨h1, h2, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨_, _, hex⟩ | ⟨_hoom_st, _hoom_post⟩
    rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
    · refine Or.inl ⟨h1, h2, ?_⟩
      simp only [serializeSpec, serializeSomeSpec, sessionRecordAt, hcur_g, hcur_r, henc,
        vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost.2
    · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
      simp only [serializeSpec, serializeSomeSpec] at hpan ⊢
      rw [← sepConj_assoc] at hpan
      exact allowPanic_frame id hpan
    · exact False.elim (not_satisfies_false_sepConj hex)

/-! ## Relocatable `[LibsignalPlacement]` body proofs (block `52`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

private def withLsCodeLoadedLeft_ser {α : Type} (pl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜LibsignalCodeLoaded pl s0.mem⌝ ∗ spec.pre x s0 }

private theorem subroutine_ok_of_withLsCodeLoadedLeft_ser {α : Type} {prog : Program}
    {pl : MultiPlacement} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoadedLeft_ser pl spec)) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded, withLsCodeLoadedLeft_ser] at hpre ⊢
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre

private abbrev lhsOfNe_ser {α : Type} {a b : α} (_ : a ≠ b) : α := a

private theorem sepWPp_split_x0_ser {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hzero : s.readReg64 .x0 = 0#64 → SepWPp prog ret s P Q Qp)
    (hnez : s.readReg64 .x0 ≠ 0#64 → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  if hp0 : s.readReg64 .x0 = 0#64 then hzero hp0 else hnez hp0

private theorem serialize_none_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hvv0 : subroutine_ok (lsProg_52 H) (blkPl_117).base (withLsCl lsmpl vecVecCloneSubSpec))
    (hmemcpy : subroutine_ok (lsProg_52 H) (lsρ lsMemcpySym) framelessMemcpySpec) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeNoneSpec A)) := by
  have hvv : subroutine_ok (lsProg_52 H) (lsmpl.base 117) (withLsCl lsmpl vecVecCloneSubSpec) := hvv0
  clear hvv0
  apply subroutine_ok_of_withLsCodeLoadedLeft_ser
  unfold withLsCodeLoadedLeft_ser serializeNoneSpec
  simp only [noneCap, okTagVec, memRegion_out32_stack_none,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_init x s0
  obtain ⟨self, out, prevPtr⟩ := x
  dsimp only at *
  have hbs336 : (_ : List (BitVec 8)).length = 336 := ‹_›
  wp_steps_lscl (lsmpl.base 117)
  wp_apply
  wp_simp_pre [vecHeader, arm64_norm]
  wp_steps
  rw [← hbs336]
  wp_apply
  refine SepWP.fold (bytes336_to_w012 s0.sp hbs336) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro w0
  apply sepWP_exists_left_sep; intro w1
  apply sepWP_exists_left_sep; intro w2
  wp_steps
  refine SepWP.fold (vecU8_nil_from_out_cells A out) (by sep_focus) ?_
  refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (repack_stack_none_cells s0.sp _ _ _ _ hbs336) (by sep_focus) ?_
  wp_done

set_option maxHeartbeats 400000 in
private theorem serialize_some_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_52 H) (lsρ lsRustNoAllocShimSym)
      LibsignalTripleRatchet.sessionShimSpec)
    (halloc : subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym) (rustAllocSubSpec A))
    (hmemcpy : subroutine_ok (lsProg_52 H) (lsρ lsMemcpySym) framelessMemcpySpec)
    (hpanic : (lsProg_52 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (hclone0 : subroutine_ok (lsProg_52 H) (blkPl_80).base (withLsCl lsmpl (sessionCloneSubSpec A)))
    (hvv0 : subroutine_ok (lsProg_52 H) (blkPl_117).base (withLsCl lsmpl vecVecCloneSubSpec))
    (hlen0 : subroutine_ok (lsProg_52 H) (blkPl_86).base (withLsCl lsmpl (sessionLenSubSpec A)))
    (hev0 : subroutine_ok (lsProg_52 H) (blkPl_10).base (withLsCl lsmpl (encodeVarintSubSpec A)))
    (hraw0 : subroutine_ok (lsProg_52 H) (blkPl_14).base (withLsCl lsmpl (encodeRawSubSpec A)))
    (hdrop0 : subroutine_ok (lsProg_52 H) (blkPl_6).base (withLsCl lsmpl (dropLocal1SubSpec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeSomeSpec A)) := by
  have hclone : subroutine_ok (lsProg_52 H) (lsmpl.base 80) (withLsCl lsmpl (sessionCloneSubSpec A)) := hclone0
  have hvv : subroutine_ok (lsProg_52 H) (lsmpl.base 117) (withLsCl lsmpl vecVecCloneSubSpec) := hvv0
  have hlen : subroutine_ok (lsProg_52 H) (lsmpl.base 86) (withLsCl lsmpl (sessionLenSubSpec A)) := hlen0
  have hev : subroutine_ok (lsProg_52 H) (lsmpl.base 10) (withLsCl lsmpl (encodeVarintSubSpec A)) := hev0
  have hraw : subroutine_ok (lsProg_52 H) (lsmpl.base 14) (withLsCl lsmpl (encodeRawSubSpec A)) := hraw0
  have hdrop : subroutine_ok (lsProg_52 H) (lsmpl.base 6) (withLsCl lsmpl (dropLocal1SubSpec A)) := hdrop0
  clear hclone0 hvv0 hlen0 hev0 hraw0 hdrop0
  apply subroutine_ok_of_withLsCodeLoadedLeft_ser
  unfold withLsCodeLoadedLeft_ser serializeSomeSpec
  simp only [okTagVec, memRegion_out32_stack_some,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wpp_init x s0
  obtain ⟨self, out, prevPtr, G, sess⟩ := x
  dsimp only at *
  apply sepWPp_of_sepWP_lscl_ser ‹_› (mid := lsmpl.base 80)
  refine SepWP.fold (sessionAt_unpack_head_tail A (self + 24#64) G sess) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro bs336_self
  apply sepWP_pure_left_sep; rintro ⟨hbs336_self, hcap_self, hinl_self⟩
  have hcmn_self : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCap hcap_self
  wp_steps
  refine SepWP.fold (sessionAt_pack_head_tail A (self + 24#64) G sess hinl_self) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro _hcl_clone
  wpp_call hclone ⟨s0.sp - 800#64, self + 24#64, G, sess⟩
  have heq_enc : encSessionMem w sess = encSessionMem G sess := ‹_›
  apply sepWPp_of_sepWP_lscl_ser ‹_› (mid := (blkPl_52).base + 320#64)
  refine SepWP.fold (sessionAt_unpack_800 A s0.sp w sess) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro bs336_clone
  apply sepWP_pure_left_sep; rintro ⟨hbs336_clone, hcap_clone, hinl_clone⟩
  have hcmn_clone : (w.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCap hcap_clone
  apply sepWP_seq_lscl ‹_› (mid := lsmpl.base 117)
  wp_steps
  rw [← hbs336_clone]
  wp_apply
  refine SepWP.fold (repack_frame_368 s0.sp w.localIk.cap hbs336_clone) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro w_none
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro _hcl_vv
  wp_apply
  wp_simp_pre [vecHeader, arm64_norm]
  apply sepWP_seq_lscl ‹_› (mid := lsmpl.base 86)
  wp_steps
  rw [← hbs336_clone]
  wp_apply
  refine SepWP.fold (sessionAt_pack_776 A s0.sp w sess hinl_clone) (by sep_focus) ?_
  refine SepWP.fold (bytes336_to_w012 s0.sp hbs336_clone) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro w0
  apply sepWP_exists_left_sep; intro w1
  apply sepWP_exists_left_sep; intro w2
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro _hcl_len
  have hlen_bounds_G : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32 := by
    assumption
  obtain ⟨hbs_lt_G, hlf_pos_G, hlf_lt63_G, hlayout_G, hv_lt62_G, hv_le_lf_G, hraw_lt_G⟩ :=
    lenField_one_bounds hlen_bounds_G
  obtain ⟨hbr_ls_G, hbr_tbz_G, hbr_cbz_G⟩ := lenField_one_branch_conds hlen_bounds_G
  have hcap_toNat_G := lenField_one_bv_toNat hlen_bounds_G
  have hex_pow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro _hcl_alloc
  refine sepWPp_split_x0_ser (fun hp0 => ?_) (fun hp0 => ?_)
  · conv => arg 4; simp only [hp0, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_fail => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hp0' : lhsOfNe_ser hp0 ≠ 0 := hp0
    have hp0_beq : (lhsOfNe_ser hp0 == 0#64) = false := beq_false_of_ne hp0
    conv => arg 4; simp only [hp0', ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨halign, htr_alloc⟩ => ?_
    apply sepWPp_of_sepWP_lscl_ser ‹_› (mid := lsmpl.base 10)
    rw [memRegion_split_init_byte (lhsOfNe_ser hp0) hlf_pos_G hlf_lt63_G]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro b0
    wp_steps_lscl (lsmpl.base 86)
    wp_apply
    wp_steps
    refine SepWP.fold (vecU8At_init_byte_432 A s0.sp (lhsOfNe_ser hp0)
      (lenField 1 (encSessionMem G sess)).length 0x0a#8 hlf_pos_G hlen_bounds_G hp0')
      (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _hcl_ev
    wpp_call hev ⟨BitVec.ofNat 64 (encSessionMem G sess).length, s0.sp - 432#64,
      BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length,
      lhsOfNe_ser hp0, [0x0a#8]⟩
    apply sepWPp_of_sepWP_lscl_ser ‹_› (mid := lsmpl.base 14)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _hcl_er
    wpp_call hraw ⟨s0.sp - 776#64, w, sess, s0.sp - 432#64, _, _,
      [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩
    apply SepWPp.of_sepWP_ret
    rw [lenField_one_cons_eq heq_enc, vecU8At_unpack_cells_432]
    apply sepWP_seq_lscl ‹_› (mid := lsmpl.base 6)
    wp_steps
    refine SepWP.fold (sessionAt_entails_sessionStateAt A (s0.sp - 776#64) w sess) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro _hcl_drop
    wp_apply
    wp_steps
    conv => arg 4; simp only [*]
    refine SepWP.fold (vecU8_from_out_cells A out _ _ (lenField 1 (encSessionMem G sess)))
      (by sep_focus) ?_
    refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (repack_stack_some_cells s0.sp _ _ _) (by sep_focus) ?_
    wp_done

/-- Relocatable `SessionRecord::serialize` (block `52`) from caller-program (`lsProg_52 H`) callee contracts. -/
theorem serialize_placed_ok_of_caller_callees [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_52 H) (lsρ lsRustNoAllocShimSym)
      LibsignalTripleRatchet.sessionShimSpec)
    (halloc : subroutine_ok (lsProg_52 H) (lsρ lsRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_52 H) (lsρ lsMemcpySym) framelessMemcpySpec)
    (hpanic : (lsProg_52 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (hClone : subroutine_ok (lsProg_52 H) (blkPl_80).base
      (withLsCodeLoaded lsmpl (sessionCloneSpec A)))
    (hVV : subroutine_ok (lsProg_52 H) (blkPl_117).base
      (withLsCodeLoaded lsmpl vecVecCloneEmptySpec))
    (hLen : subroutine_ok (lsProg_52 H) (blkPl_86).base
      (withLsCodeLoaded lsmpl (sessionLenSpec A)))
    (hEV : subroutine_ok (lsProg_52 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (Prost.encodeVarintSpec A)))
    (hRaw : subroutine_ok (lsProg_52 H) (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSpec A)))
    (hDrop : subroutine_ok (lsProg_52 H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeSpec A)) := by
  have hvv_sub := vecVecClone_caller_sub_ok hVV
  have hnone := serialize_none_placed_ok A H hvv_sub hmemcpy
  have hsome := serialize_some_placed_ok A H hshim (alloc_caller_sub_ok halloc) hmemcpy hpanic
    (sessionClone_caller_sub_ok hClone) hvv_sub (sessionLen_caller_sub_ok hLen)
    (encodeVarint_caller_sub_ok hEV) (encodeRaw_caller_sub_ok hRaw) (dropLocal1_caller_sub_ok hDrop)
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre0 hsp
  obtain ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre0
  have hpre : s0.mem ⊨ (serializeSpec A).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded] at hpre0
    rw [sepConj_assoc, sepConj_left_comm ((serializeSpec A).pre x s0), satisfies_pure_sepConj] at hpre0
    exact hpre0.2
  rcases hcur_g : x.g.cur with _ | G <;> rcases hcur_r : x.r.currentSession with _ | sess
  ·
    have henc : encRecordMem x.g x.r = [] := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    let F := prevVecFrame A x.self x.g ∗ memRegion (x.self + 32#64) 336 ∗ A.pool
    have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (serializeNoneSpec A)).pre
        (x.self, x.out, x.g.prevPtr) s0 ∗ (F ∗ R) := by
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm ((serializeNoneSpec A).pre _ s0), satisfies_pure_sepConj]
      refine ⟨hcl0, ?_⟩
      simp only [serializeSpec, serializeNoneSpec, sessionRecordAt, hcur_g, hcur_r,
        vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨⟨hpre.1.1, hpre.1.2.1⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre.2
    refine hnone.mono_outcome (x.self, x.out, x.g.prevPtr) (F ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
    rcases hout with ⟨h1, h2, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_hoom_st, _hoom_post⟩
    rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
    · refine Or.inl ⟨h1, h2, ?_⟩
      simp only [serializeSpec, serializeNoneSpec, sessionRecordAt, hcur_g, hcur_r,
        henc, vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost.2
    · exact False.elim (not_satisfies_false_sepConj hpan)
    · exact False.elim (not_satisfies_false_sepConj hex)
  ·
    simp only [serializeSpec, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    simp only [serializeSpec, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    have henc : encRecordMem x.g x.r = lenField 1 (encSessionMem G sess) := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    let F := prevVecFrame A x.self x.g
    have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (serializeSomeSpec A)).pre
        ⟨x.self, x.out, x.g.prevPtr, G, sess⟩ s0 ∗ (F ∗ R) := by
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm ((serializeSomeSpec A).pre _ s0), satisfies_pure_sepConj]
      refine ⟨hcl0, ?_⟩
      simp only [serializeSpec, serializeSomeSpec, sessionRecordAt, hcur_g, hcur_r, henc,
        vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨hpre.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre.2
    refine hsome.mono_outcome ⟨x.self, x.out, x.g.prevPtr, G, sess⟩ (F ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
    rcases hout with ⟨h1, h2, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨_, _, hex⟩ | ⟨_hoom_st, _hoom_post⟩
    rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
    · refine Or.inl ⟨h1, h2, ?_⟩
      simp only [serializeSpec, serializeSomeSpec, sessionRecordAt, hcur_g, hcur_r,
        henc, vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost.2
    · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
      simp only [serializeSpec, serializeSomeSpec] at hpan ⊢
      rw [← sepConj_assoc] at hpan
      exact allowPanic_frame id hpan
    · exact False.elim (not_satisfies_false_sepConj hex)

/-- Relocatable `SessionRecord::serialize` (block `52`) from block-level callee contracts and external hooks. -/
theorem serialize_placed_ok_of_callees [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hClone : subroutine_ok (lsProg_80 H) (blkPl_80).base
      (withLsCodeLoaded lsmpl (sessionCloneSpec A)))
    (hVV : subroutine_ok (lsProg_117 H) (blkPl_117).base vecVecCloneEmptySpec)
    (hLen : subroutine_ok (lsProg_86 H) (blkPl_86).base
      (withLsCodeLoaded lsmpl (sessionLenSpec A)))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (Prost.encodeVarintSpec A)))
    (hRaw : subroutine_ok (lsProg_14 H) (blkPl_14).base
      (withLsCodeLoaded lsmpl (encodeRawSpec A)))
    (hDrop : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A))) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base (withLsCodeLoaded lsmpl (serializeSpec A)) :=
  serialize_placed_ok_of_caller_callees
    (ls_hook_ok_of_mem hshim)
    (ls_hook_ok_of_mem halloc)
    (ls_hook_ok_of_mem hmemcpy)
    (panic_at_handle_error_52_placed hpanic)
    (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hClone)
    (ls_subroutine_ok_of_block (callerProg := lsProg_52 H)
      (subroutine_ok_withLsCodeLoaded_of_plain hVV))
    (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hLen)
    (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hEV)
    (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hRaw)
    (ls_subroutine_ok_of_block (callerProg := lsProg_52 H) hDrop)

end Placed

end CryptoVerification.E2E.Record.Serialization

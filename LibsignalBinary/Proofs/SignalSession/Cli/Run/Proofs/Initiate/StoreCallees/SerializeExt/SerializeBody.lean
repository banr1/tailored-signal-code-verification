/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SerializeBodyAux.Helpers
public meta import ProofLib.SepLogic.WP.Apply -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.WPX
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionRecord::serialize`

Verifies `SessionRecord::serialize`: clones `current_session` (`SessionStructure::clone`) and
empty `previous_sessions` (`Vec<Vec<u8>>::clone`), allocates the exact encoded buffer via
`SessionStructure::encoded_len` + `__rust_alloc`, writes tag `0x0a` + `encode_varint` +
`SessionStructure::encode_raw`, drops the temporary clone (`drop_glue<SessionStructure>`), and
writes `Ok(v)` into the `sret` slot.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.SerializeBodyAux

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
  encSessionMem lenField encodeVarint
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  serialize_varintLen_eq serialize_varintLen_bvShift_eq lenField_one_bv_eq
attribute [local wp_norm] serialize_varintLen_eq serialize_varintLen_bvShift_eq lenField_one_bv_eq

def serializeNoneSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (self, out, prevPtr) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = out⌝ ∗
      ((self + 8#64) ↦₆₄ prevPtr) ∗ ((self + 16#64) ↦₆₄ 0#64) ∗
      ((self + 24#64) ↦₆₄ noneCap) ∗
      memRegion out 32 ∗ stackAt s.sp serializeStackX
  post := fun (self, out, prevPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((self + 8#64) ↦₆₄ prevPtr) ∗ ((self + 16#64) ↦₆₄ 0#64) ∗
      ((self + 24#64) ↦₆₄ noneCap) ∗
      (out ↦₆₄ okTagVec) ∗ vecU8 A (out + 8#64) [] ∗
      stackAt s0.sp serializeStackX

theorem memRegion_out32_cells (out : BitVec 64) :
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

theorem memRegion_out32_stack_none (out sp : BitVec 64) :
    memRegion out 32 ∗ stackAt sp serializeStackX =
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

theorem sepWP_exists_left_sep {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {post : State → SepProp → Prop}
    (h : ∀ x, SepWP prog pc s (P x ∗ F) post) :
    SepWP prog pc s ((∃∗ x, P x) ∗ F) post := by
  rw [sepExists_sepConj_left]
  exact SepWP.exists_left h

theorem sepWP_pure_left_sep {prog : Program} {pc : BitVec 64} {s : State}
    {φ : Prop} {P F : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog pc s (P ∗ F) post) :
    SepWP prog pc s ((⌜φ⌝ ∗ P) ∗ F) post := by
  rw [sepConj_assoc]
  exact SepWP.pure_elim h

theorem vecU8_nil_from_out_cells (A : RustAlloc) (out : BitVec 64) :
    (((out + 8#64) ↦₆₄ 0#64) ∗ ((out + 16#64) ↦₆₄ 1#64) ∗ ((out + 24#64) ↦₆₄ 0#64)) ⊢
      vecU8 A (out + 8#64) [] := by
  have hp := pointsTo64_pair_out out 0#64 1#64
  have hpull :
      (((out + 8#64) ↦₆₄ 0#64) ∗ ((out + 16#64) ↦₆₄ 1#64) ∗ ((out + 24#64) ↦₆₄ 0#64)) =
      ((((out + 8#64) ↦₆₄ 0#64) ∗ ((out + 16#64) ↦₆₄ 1#64)) ∗ ((out + 24#64) ↦₆₄ 0#64)) := by
    ac_rfl
  rw [hpull, ← hp]
  exact vecU8_nil_from_out_stores A out

theorem vecU8_from_out_cells (A : RustAlloc) (out cap ptr : BitVec 64)
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

theorem sessionAt_eq_head_tail (A : RustAlloc) (ss : BitVec 64)
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

theorem vecHeader_cells_800 (sp : BitVec 64) :
    (((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64)) =
      vecHeader (sp - 800#64) 0#64 8#64 0#64 := by
  unfold vecHeader
  have e1 : sp - 800#64 + 8#64 = sp - 792#64 := bv_sub_add_lit sp 800 8
  have e2 : sp - 800#64 + 16#64 = sp - 784#64 := bv_sub_add_lit sp 800 16
  rw [e1, e2]

theorem repack_stack_some_cells (sp w0 w1 w2 : BitVec 64) :
    (stackAt (sp - 800#64) serializeSubStack ∗
      ((sp - 800#64) ↦₆₄ 0#64) ∗ ((sp - 792#64) ↦₆₄ 8#64) ∗ ((sp - 784#64) ↦₆₄ 0#64) ∗
      memRegion (sp - 776#64) 344 ∗
      ((sp - 432#64) ↦₆₄ w0) ∗
      ((sp - 424#64) ↦₆₄ w1) ∗
      ((sp - 416#64) ↦₆₄ w2) ∗
      memRegion (sp - 408#64) 312 ∗
      cells (sp - 96#64) 12) ⊢
      stackAt sp serializeStackX := by
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

theorem repack_stack_none_cells (sp wn w0 w1 w2 : BitVec 64)
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
      stackAt sp serializeStackX := by
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

theorem serialize_none_ok (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hVV : OkAtX img ext vecVecCloneName vecVecCloneEmptySpecX) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr serializeName)
      ((serializeNoneSpec A).inImage img) := by
  apply subroutine_ok_inImage_iff_right
  unfold serializeNoneSpec
  simp only [noneCap, okTagVec, memRegion_out32_stack_none,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff serializeName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") :=
    libsignalSessionCode_fnOff_serialize
  have hmemcpy := memcpy_sub_ok hA
  have hvv := vecVecClone_sub_ok hVV
  dsimp only [framelessMemcpySubSpec, vecVecCloneSubSpec, withStack, framelessMemcpySpec]
    at hmemcpy hvv
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0 56
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x5c 48
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x10c 12
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x128 4
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x188 20
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x1a8 24
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x2b4 32
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x2dc 8
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x310 8
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x32c 32
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨self, out, prevPtr⟩ := x
  dsimp only at *
  wpx_steps
  wpx_call hvv
  wp_simp_pre [vecHeader, arm64_norm]
  wpx_steps
  rw [← ‹List.length _ = 336›]
  wpx_call hmemcpy
  refine SepWP.fold (bytes336_to_w012 s0.sp ‹List.length _ = 336›) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro w0
  apply sepWP_exists_left_sep; intro w1
  apply sepWP_exists_left_sep; intro w2
  wpx_steps
  conv => arg 4; simp only [*]
  refine SepWP.fold (vecU8_nil_from_out_cells A out) (by sep_focus) ?_
  refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (repack_stack_none_cells s0.sp _ _ _ _ ‹List.length _ = 336›) (by sep_focus) ?_
  wp_done

theorem sessionAt_pack_776 (A : RustAlloc) (sp : BitVec 64)
    (G : SessionGhost) (s : LibsignalSessionApi.Session (List (BitVec 8)))
    {bs336 : List (BitVec 8)}
    (hinl : SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)) :
    (((sp - 776#64) ↦₆₄ G.localIk.cap) ∗ ((sp - 768#64) ↦ₛ bs336) ∗ sessionAtHeap A G s) ⊢
      sessionStateReprAt A (sp - 776#64) G s := by
  have h := sessionAt_pack_head_tail A (sp - 776#64) G s hinl
  have e : sp - 776#64 + 8#64 = sp - 768#64 := bv_sub_add_lit sp 776 8
  rwa [e] at h

theorem sessionAt_unpack_800 (A : RustAlloc) (sp : BitVec 64)
    (G : SessionGhost) (s : LibsignalSessionApi.Session (List (BitVec 8))) :
    sessionStateReprAt A (sp - 800#64) G s ⊢
      ∃∗ bs336 : List (BitVec 8),
        ⌜bs336.length = 336 ∧ G.localIk.cap.toNat < 2 ^ 63 ∧
          SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)⌝ ∗
        ((sp - 800#64) ↦₆₄ G.localIk.cap) ∗ ((sp - 792#64) ↦ₛ bs336) ∗ sessionAtHeap A G s := by
  have h := sessionAt_unpack_head_tail A (sp - 800#64) G s
  have e : sp - 800#64 + 8#64 = sp - 792#64 := bv_sub_add_lit sp 800 8
  rwa [e] at h

theorem memRegion_out32_stack_some (out sp : BitVec 64) :
    memRegion out 32 ∗ stackAt sp serializeStackX =
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
      A.pool ∗ memRegion x.out 32 ∗ stackAt s.sp serializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((x.self + 8#64) ↦₆₄ x.prevPtr) ∗ ((x.self + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A (x.self + 24#64) x.G x.sess ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (lenField 1 (encSessionMem x.G x.sess)) ∗
      A.pool ∗ stackAt s0.sp serializeStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem allocFailedIn_of_trace_eq {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢
  rwa [htr] at h

theorem allowPanic_frame_trace {s0 sm sf : State} {F R : SepProp}
    (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eq htr) h

/-- Propagate callee `allocFailedIn` panic across an unchanged trace `sm.trace = s0.trace`. -/
theorem allowPanic_entails_trace {s0 sm sf : State} {F : SepProp}
    (htr : sm.trace = s0.trace) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  apply Entails.pure_left; intro h
  exact Entails.pure_right (allocFailedIn_of_trace_eq htr h) (entails_anyHeap _)

@[local wp_norm]
private theorem local_trace_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := by
  cases r <;> simp [State.writeReg64]

@[local wp_norm]
private theorem local_trace_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by
  cases r <;> simp [State.writeReg32]

@[local wp_norm]
private theorem local_trace_setPState (s : State) (p : PState) :
    (s.setPState p).trace = s.trace := rfl

@[local wp_norm]
private theorem local_trace_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := rfl

@[local wp_norm]
private theorem local_trace_setMem (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := rfl

@[local wp_norm]
private theorem local_trace_advancePC (s : State) :
    s.advancePC.trace = s.trace := rfl

open Lean Meta Elab Tactic in
private meta def wppElimSpatialContext (hEq : Ident) : TacticM Unit := do
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 5
      simp (config := { decide := true }) only [
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hEq:ident]))))
  for _ in [0:64] do
    let g ← getMainGoal
    let ty ← g.withContext (instantiateMVars (← g.getType))
    unless ty.isAppOf ``SepWPpX do return
    let P := (ty.getArg! 4).consumeMData
    if P.isAppOfArity ``SepProp.sepExists 2 then
      let wId ← freshIdent `w
      evalTactic (← `(tactic| (apply SepWPpX.exists_elim; intro $wId:ident)))
      betaReduceTarget
    else if P.isAppOfArity ``SepProp.sepConj 2 && (P.getArg! 0).isAppOfArity ``SepProp.pure 1 then
      let hId ← freshIdent `hpost
      evalTactic (← `(tactic| (apply SepWPpX.pure_elim; intro $hId:ident)))
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

private theorem sepWPpX_call_imgInv {α : Type} {img : Obj.Image} {prog : Program}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, ImgCallInv img s → (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpX img prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPpX img prog ret s P Q Qp :=
  fun hinv =>
    SepWPp.call_imgInv (x := x) (F := F) hcall hinv hpc hrun hsp hlr (fun R hm => hpre R hinv hm)
      hexit hpanic
      (fun sf h1 h2 h3 h4 hinv_sf => hnext sf h1 h2 h3 h4 hinv_sf)
      h_no_oom

open Lean Meta Elab Tactic in
local elab "wpp_call " hcall:term:max arg?:(ppSpace colGt term:max)? : tactic => do
  let g0 ← getMainGoal
  let inImg ← g0.withContext <| withoutModifyingState do
    let hcE ← Tactic.elabTerm hcall none
    let hcTy := (← whnfR (← instantiateMVars (← inferType hcE))).consumeMData
    if !hcTy.isAppOfArity ``Arm64.subroutine_ok 4 then
      throwError "wpp_call: `{hcall}` is not a `subroutine_ok` hypothesis:{indentExpr hcTy}"
    let specFull := (← instantiateMVars (hcTy.getArg! 3)).consumeMData
    return specFull.isAppOfArity ``Arm64.Spec.inImage 3
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let applyFrameStx ← match inImg, arg? with
    | true, some a => `(tactic| apply (SepWPpX.call $hcall (x := $a)))
    | true, none => `(tactic| apply (SepWPpX.call $hcall))
    | false, some a => `(tactic| apply (sepWPpX_call_imgInv $hcall (x := $a)))
    | false, none => `(tactic| apply (sepWPpX_call_imgInv $hcall))
  evalTactic applyFrameStx
  closeWppCallSiteSetupSubgoals
  let gsAfterSetup ← getGoals
  let gPre :: gExit :: gPanic :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call: unexpected subgoals after `SepWPp.call`"
  setGoals [gPre]
  if inImg then
    evalTactic (← `(tactic| intro _R' _hmR'))
  else
    evalTactic (← `(tactic| (
      intro _R' _hinv_pre _hmR'
      dsimp only
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨_hinv_pre, ?_⟩
      clear _hinv_pre)))
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
  let preLeft ← getGoals
  if !preLeft.isEmpty then
    throwError "wpp_call: unsolved precondition subgoals"
  setGoals [gExit]
  evalTactic (← `(tactic| (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he)))
  if !(← getGoals).isEmpty then
    throwError "wpp_call: unsolved exit subgoal"
  setGoals [gPanic]
  evalTactic (← `(tactic| (wp_unfold_specs; intro _ _ _hp; dsimp only [allocPanic] at _hp ⊢; exact allowPanic_frame_trace (by simp only [wp_norm, arm64_norm, *]) _hp)))
  if !(← getGoals).isEmpty then
    throwError "wpp_call: unsolved panic subgoal"
  for m in rest do
    if ← m.isAssigned then continue
    let m' ← m.withContext do
      let ty ← instantiateMVars (← m.getType)
      if ty.consumeMData.isAppOfArity ``autoParam 2 then
        m.replaceTargetDefEq (ty.consumeMData.getArg! 0)
      else
        pure m
    setGoals [m']
    evalTactic (← `(tactic| (wp_unfold_specs; wp_close_oom_default)))
    if !(← getGoals).isEmpty then
      throwError "wpp_call: unsolved oom subgoal"
  setGoals [gCont]
  evalTactic (← `(tactic| intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wppElimSpatialContext hspId

/-! ## `Some` branch of `SessionRecord::serialize` -/

theorem memRegion_split_init_byte (ptr : BitVec 64) {n : Nat}
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

theorem vecU8At_unpack_cells_432 (A : RustAlloc) (sp cap ptr : BitVec 64)
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

theorem lenField_one_bv_toNat {bs : List (BitVec 8)}
    (h : (lenField 1 bs).length < 2 ^ 32) :
    (BitVec.ofNat 64 (lenField 1 bs).length).toNat = (lenField 1 bs).length := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem cap_lt_not_noneCap {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro heq
  have h1 : (cap + 1#64).toNat = 0 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem bv64_ult_zero (x : BitVec 64) : BitVec.ult x 0#64 = false := by
  simp [BitVec.ult]

theorem lenField_one_branch_conds {bs : List (BitVec 8)}
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

theorem vecU8At_init_byte_432 (A : RustAlloc) (sp ptr : BitVec 64) (n : Nat) (b0 : BitVec 8)
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

theorem lenField_one_cons_eq {bs bs' : List (BitVec 8)} (h : bs = bs') :
    10#8 :: (encodeVarint (BitVec.ofNat 64 bs'.length) ++ bs) = lenField 1 bs' := by
  subst h
  exact (lenField_one_eq bs).symm

private structure SubCallees (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  hA : AllocContractsX img A ext
  hClone : OkAtX img ext sessionCloneName (sessionCloneSpecX A)
  hVV : OkAtX img ext vecVecCloneName vecVecCloneEmptySpecX
  hLen : OkAtX img ext sessionLenName (sessionLenSpec A)
  hEV : Prost.EncodeVarintOkExtX img A ext
  hRaw : OkAtX img ext encodeRawName (encodeRawSpecX A)
  hDrop : OkAtX img ext FromRecordCallees.dropSessionStructureLocal1Name (dropSessionStructureLocal1SpecX A)

set_option maxHeartbeats 1200000 in
private theorem serialize_some_body (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hSubs : SubCallees img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr serializeName)
      ((serializeSomeSpec A).inImage img) := by
  apply subroutine_ok_inImage_iff_right
  unfold serializeSomeSpec
  simp only [okTagVec, memRegion_out32_stack_some,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff serializeName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") :=
    libsignalSessionCode_fnOff_serialize
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0 196
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x10c 160
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x1bc 4
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x2b4 48
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x310 8
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") 0x32c 32
  wpp_init x s0
  refine sepWPp_of_sepWPpX ‹ImgCallInv img s0› ?_
  rcases hSubs with ⟨hA, hClone, hVV, hLen, hEV, hRaw, hDrop⟩
  have hmemcpy := memcpy_sub_ok hA
  have hshim := shim_sub_ok hA
  have hclone := sessionClone_sub_ok hClone
  have hvv := vecVecClone_sub_ok hVV
  have hlen := sessionLen_sub_ok hLen
  have hev := encodeVarint_sub_ok hEV
  have hraw := encodeRaw_sub_ok hRaw
  have hdrop := dropLocal1_sub_ok hDrop
  have halloc := alloc_sub_ok hA
  clear hA hClone hVV hLen hEV hRaw hDrop
  have hpanic : (tripleRatchetProgAtExt img.base ext).externAt? ((tripleRatchetProgAtExt img.base ext).fnAddr serializeName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) = some Rust.panicked := panic_at_panicSymbol libsignalSessionCode_fnOff_serialize (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) (by decide) (by decide) (ls_hook% "alloc::raw_vec::handle_error") (by simp [Rust.isPanicSymbol])
  dsimp only [framelessMemcpySubSpec, noAllocShimSubSpec, sessionCloneSubSpec,
    vecVecCloneSubSpec, sessionLenSubSpec, encodeVarintSubSpec, encodeRawSubSpec,
    dropLocal1SubSpec, rustAllocSubSpec, withStack, framelessMemcpySpec, noAllocShimSpec]
    at hmemcpy hshim hclone hvv hlen hev hraw hdrop halloc
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨self, out, prevPtr, G, sess⟩ := x
  dsimp only at *
  apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
  refine SepWP.fold (sessionAt_unpack_head_tail A (self + 24#64) G sess) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro bs336_self
  apply sepWP_pure_left_sep; rintro ⟨hbs336_self, hcap_self, hinl_self⟩
  have hcmn_self : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCap hcap_self
  wp_steps
  refine SepWP.fold (sessionAt_pack_head_tail A (self + 24#64) G sess hinl_self) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  wpp_call hclone ⟨s0.sp - 800#64, self + 24#64, G, sess⟩
  have heq_enc : encSessionMem w sess = encSessionMem G sess := by assumption
  wpx_of_sepWP (mid := entry + bv% (320))
  refine SepWP.fold (sessionAt_unpack_800 A s0.sp w sess) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro bs336_clone
  apply sepWP_pure_left_sep; rintro ⟨hbs336_clone, hcap_clone, hinl_clone⟩
  have hcmn_clone : (w.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCap hcap_clone
  wpx_steps
  rw [← hbs336_clone]
  wpx_call hmemcpy
  refine SepWP.fold (repack_frame_368 s0.sp w.localIk.cap hbs336_clone) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro w_none
  wpx_steps
  wpx_call hvv
  wp_simp_pre [vecHeader, arm64_norm]
  wpx_steps
  rw [← hbs336_clone]
  wpx_call hmemcpy
  refine SepWP.fold (sessionAt_pack_776 A s0.sp w sess hinl_clone) (by sep_focus) ?_
  refine SepWP.fold (bytes336_to_w012 s0.sp hbs336_clone) (by sep_focus) ?_
  apply sepWP_exists_left_sep; intro w0
  apply sepWP_exists_left_sep; intro w1
  apply sepWP_exists_left_sep; intro w2
  wpx_steps
  have hlen_bounds_G : (lenField 1 (encSessionMem G sess)).length < 2 ^ 32 := by
    assumption
  obtain ⟨hbs_lt_G, hlf_pos_G, hlf_lt63_G, hlayout_G, hv_lt62_G, hv_le_lf_G, hraw_lt_G⟩ :=
    lenField_one_bounds hlen_bounds_G
  have hbs_lt_w : (encSessionMem w sess).length < 2 ^ 32 := heq_enc.symm ▸ hbs_lt_G
  have hraw_lt_w : ([0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)).length +
      (encSessionMem w sess).length < 2 ^ 32 := heq_enc.symm ▸ hraw_lt_G
  obtain ⟨hbr_ls_G, hbr_tbz_G, hbr_cbz_G⟩ := lenField_one_branch_conds hlen_bounds_G
  have hcap_toNat_G := lenField_one_bv_toNat hlen_bounds_G
  have hex_pow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wpx_call hlen
  wpx_steps
  wpx_call hshim
  wpx_steps
  wpx_call halloc
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hp0 : sf_6.readReg64 .x0 = 0#64
  · conv => arg 5; simp only [hp0, sepConj_assoc]
    refine SepWPpX.pure_elim fun htr_fail => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPpX.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hp0' : sf_6.readReg64 .x0 ≠ 0 := hp0
    have hp0_beq : (sf_6.readReg64 .x0 == 0#64) = false := beq_false_of_ne hp0
    conv => arg 5; simp only [hp0', ↓reduceIte, sepConj_assoc]
    refine SepWPpX.pure_elim fun ⟨halign, htr_alloc⟩ => ?_
    wpx_of_sepWP (mid := entry + bv% (2 ^ 64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
    rw [memRegion_split_init_byte (sf_6.readReg64 .x0) hlf_pos_G hlf_lt63_G]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro b0
    wpx_steps
    wpx_call hlen
    wpx_steps
    refine SepWP.fold (vecU8At_init_byte_432 A s0.sp (sf_6.readReg64 .x0)
      (lenField 1 (encSessionMem G sess)).length 0x0a#8 hlf_pos_G hlen_bounds_G hp0')
      (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    wpp_call hev ⟨BitVec.ofNat 64 (encSessionMem G sess).length, s0.sp - 432#64,
      BitVec.ofNat 64 (lenField 1 (encSessionMem G sess)).length,
      sf_6.readReg64 .x0, [0x0a#8]⟩
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    wpp_call hraw ⟨s0.sp - 776#64, w, sess, s0.sp - 432#64, _, _,
      [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 (encSessionMem G sess).length)⟩
    wpx_of_sepWP_ret
    rw [lenField_one_cons_eq heq_enc, vecU8At_unpack_cells_432]
    wpx_steps
    refine SepWP.fold (sessionAt_entails_sessionStateAt A (s0.sp - 776#64) w sess) (by sep_focus) ?_
    wpx_call hdrop
    wpx_steps
    conv => arg 4; simp only [*]
    refine SepWP.fold (vecU8_from_out_cells A out _ _ (lenField 1 (encSessionMem G sess)))
      (by sep_focus) ?_
    refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (repack_stack_some_cells s0.sp _ _ _) (by sep_focus) ?_
    wp_done

private theorem serialize_some_ok (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hClone : OkAtX img ext sessionCloneName (sessionCloneSpecX A))
    (hVV : OkAtX img ext vecVecCloneName vecVecCloneEmptySpecX)
    (hLen : OkAtX img ext sessionLenName (sessionLenSpec A))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hRaw : OkAtX img ext encodeRawName (encodeRawSpecX A))
    (hDrop : OkAtX img ext FromRecordCallees.dropSessionStructureLocal1Name (dropSessionStructureLocal1SpecX A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr serializeName)
      ((serializeSomeSpec A).inImage img) :=
  serialize_some_body img A ext ⟨hA, hClone, hVV, hLen, hEV, hRaw, hDrop⟩

def prevVecFrame (A : RustAlloc) (r : BitVec 64) (g : RecordGhost) : SepProp :=
  (r ↦₆₄ g.prevCap) ∗ vecBuf A 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr []

theorem vecAt_empty_split (A : RustAlloc) (r : BitVec 64) (g : RecordGhost) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) r g.prevCap g.prevPtr [] =
      ((r + 8#64) ↦₆₄ g.prevPtr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗ prevVecFrame A r g := by
  unfold vecAt vecHeader prevVecFrame
  simp only [List.length_nil]
  ac_rfl

/-- `SessionRecord::serialize` meets `serializeSpecX` given its leaf callee contracts and `AllocContractsX`. -/
theorem serialize_ok_of_leaves (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hClone : OkAtX img ext sessionCloneName (sessionCloneSpecX A))
    (hVV : OkAtX img ext vecVecCloneName vecVecCloneEmptySpecX)
    (hLen : OkAtX img ext sessionLenName (sessionLenSpec A))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hRaw : OkAtX img ext encodeRawName (encodeRawSpecX A))
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (hDrop : OkAtX img ext FromRecordCallees.dropSessionStructureLocal1Name (dropSessionStructureLocal1SpecX A)) :
    OkAtX img ext serializeName (serializeSpecX A) := by
  have _ := hDR
  have hnone := serialize_none_ok img A ext hA hVV
  have hsome := serialize_some_ok img A ext hA hClone hVV hLen hEV hRaw hDrop
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (serializeSpecX A).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rcases hcur_g : x.g.cur with _ | G <;> rcases hcur_r : x.r.currentSession with _ | sess
  ·
    have henc : encRecordMem x.g x.r = [] := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    let F := prevVecFrame A x.self x.g ∗ memRegion (x.self + 32#64) 336 ∗ A.pool
    have hpre' : s0.mem ⊨ ((serializeNoneSpec A).inImage img).pre (x.self, x.out, x.g.prevPtr) s0 ∗ (F ∗ R) := by
      refine satisfies_inImage_pre hinv ?_
      simp only [serializeSpecX, serializeNoneSpec, sessionRecordAt, hcur_g, hcur_r,
        vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨⟨hpre.1.1, hpre.1.2.1⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre.2
    refine subroutine_ok.mono_outcome hnone (x.self, x.out, x.g.prevPtr) (F ∗ R)
      s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨h1, h2, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_hoom_st, _hoom_post⟩)
    rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
    · refine Or.inl ⟨h1, h2, ?_⟩
      simp only [Spec.inImage, serializeSpecX, serializeNoneSpec, sessionRecordAt, hcur_g, hcur_r, henc,
        vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost.2
    · exact False.elim (not_satisfies_false_sepConj hpan)
    · exact False.elim (not_satisfies_false_sepConj hex)
  ·
    simp only [serializeSpecX, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    simp only [serializeSpecX, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    have henc : encRecordMem x.g x.r = lenField 1 (encSessionMem G sess) := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    let F := prevVecFrame A x.self x.g
    have hpre' : s0.mem ⊨ ((serializeSomeSpec A).inImage img).pre ⟨x.self, x.out, x.g.prevPtr, G, sess⟩ s0 ∗ (F ∗ R) := by
      refine satisfies_inImage_pre hinv ?_
      simp only [serializeSpecX, serializeSomeSpec, sessionRecordAt, hcur_g, hcur_r, henc,
        vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨hpre.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre.2
    refine subroutine_ok.mono_outcome hsome ⟨x.self, x.out, x.g.prevPtr, G, sess⟩ (F ∗ R)
      s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨h1, h2, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨_, _, hex⟩ | ⟨_hoom_st, _hoom_post⟩)
    rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
    · refine Or.inl ⟨h1, h2, ?_⟩
      simp only [Spec.inImage, serializeSpecX, serializeSomeSpec, sessionRecordAt, hcur_g, hcur_r, henc,
        vecAt_empty_split, F, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost.2
    · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
      simp only [Spec.inImage, serializeSpecX, serializeSomeSpec] at hpan ⊢
      rw [← sepConj_assoc] at hpan
      exact allowPanic_frame id hpan
    · exact False.elim (not_satisfies_false_sepConj hex)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Shared Loop Frame & Call Wrappers for `spqr::decode_state` (`0x5349c`)

Defines the image-invariant-threading `SepWPpI` combinator, shared active-loop stack frame
helpers (`decodeStateLoopCommon` and error-frame folding), panic-aware call wrappers
(`decode_varint`, `skip_field`, `bytes::merge`, `ChainParams::merge`), and pure
`Proto.mergeMessage` bridge lemmas.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. `SepWPpI` (Image-Invariant-Threading `SepWPp`) & Stack Frame Helpers -/

theorem _root_.Arm64.Steps.imgCallInv {prog : Program} {img : Obj.Image} {s s' : State}
    (h : Steps prog s s') (hinv : ImgCallInv img s) : ImgCallInv img s' :=
  ⟨h.frozenLoaded hinv.1, h.symtab_eq.trans hinv.2⟩

/-- `SepWPp` enriched with `ImgCallInv img s`, automatically preserved across `Steps`
    (`SepWPpI.of_sepWP`) and available to `.inImage img` callee contracts. -/
def SepWPpI (img : Obj.Image) (prog : Program) (ret : BitVec 64) (s : State) (P : SepProp)
    (Q Q_err : State → SepProp → Prop) : Prop :=
  ImgCallInv img s → SepWPp prog ret s P Q Q_err

theorem SepWPpI.of_sepWPp {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Q_err) :
    SepWPpI img prog ret s P Q Q_err :=
  fun _ => h

theorem SepWPpI.of_sepWP {img : Obj.Image} {prog : Program} {ret mid : BitVec 64} {s : State}
    {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpI img prog ret sm Pm Q Q_err)) :
    SepWPpI img prog ret s P Q Q_err := by
  intro hinv R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ := hnext (hsteps.imgCallInv hinv) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPpI.exists_elim {α : Type} {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {P : α → SepProp} {Q Q_err : State → SepProp → Prop}
    (h : ∀ x, SepWPpI img prog ret s (P x) Q Q_err) :
    SepWPpI img prog ret s (∃∗ x, P x) Q Q_err :=
  fun hinv => SepWPp.exists_elim (fun x => h x hinv)

theorem SepWPp.mono_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWPp prog ret s P' Q Q_err) :
    SepWPp prog ret s P Q Q_err := by
  intro R hm hL
  exact hwp R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem SepWPpI.mono_pre {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWPpI img prog ret s P' Q Q_err) :
    SepWPpI img prog ret s P Q Q_err :=
  fun hinv => SepWPp.mono_pre h (hwp hinv)

/-- The `240`-byte upper frame `memRegion (sp - 336#64) 240` splits into:
    - `(sp - 336#64) ↦₆₄ bRef` (`[x29 - 0xf0]`),
    - `memRegion (sp - 328#64) 224` (`[x29 - 0xe8 .. x29 - 0x08)`),
    - `memRegion (sp - 104#64) 8` (`[x29 - 0x08 .. x29)`). -/
theorem upper_240_fold (sp bRef : BitVec 64) :
    ((sp - 336#64) ↦₆₄ bRef) ∗ memRegion (sp - 328#64) 224 ∗ memRegion (sp - 104#64) 8 ⊢
      memRegion (sp - 336#64) 240 := by
  have hb : ((sp - 336#64) ↦₆₄ bRef) ⊢ memRegion (sp - 336#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (sp - 336#64) bRef
  rw [ProofLib.memRegion_split' (b := sp - 336#64) (n := 8) (k := 232)
      (b' := sp - 328#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 328#64) (n := 224) (k := 8)
      (b' := sp - 104#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left hb

/-- The `352`-byte lower frame `memRegion (sp - 1392#64) 352` is formed from
    `memRegion (sp - 1392#64) 336` and `memRegion (sp - 1056#64) 16` (`[sp + 0x150 .. sp + 0x160)`). -/
theorem lower_352_fold (sp : BitVec 64) :
    memRegion (sp - 1392#64) 336 ∗ memRegion (sp - 1056#64) 16 ⊢
      memRegion (sp - 1392#64) 352 := by
  rw [ProofLib.memRegion_split' (b := sp - 1392#64) (n := 336) (k := 16)
      (b' := sp - 1056#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-- Fold `sliceCursorAt (sp - 1056#64) ptr bs` into `memRegion (sp - 1056#64) 16 ∗ (ptr ↦ₛ bs)`. -/
theorem sliceCursorAt_to_memRegion (sp ptr : BitVec 64) (bs : List (BitVec 8)) :
    sliceCursorAt (sp - 1056#64) ptr bs ⊢
      memRegion (sp - 1056#64) 16 ∗ (ptr ↦ₛ bs) := by
  unfold sliceCursorAt
  have h16 : ((sp - 1056#64) ↦₆₄ ptr) ∗ ((sp - 1056#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ⊢
      memRegion (sp - 1056#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 1056#64) (n := 8) (k := 8)
        (b' := sp - 1056#64 + 8#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono
      (ProofLib.pointsTo64_entails_memRegion _ ptr)
      (ProofLib.pointsTo64_entails_memRegion _ _)
  have hassoc :
      ((sp - 1056#64) ↦₆₄ ptr) ∗ ((sp - 1056#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) =
      (((sp - 1056#64) ↦₆₄ ptr) ∗ ((sp - 1056#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗ (ptr ↦ₛ bs) := by
    ac_rfl
  rw [hassoc]
  exact sepConj_mono_left h16

/-- Remainder of `st.at A` when `(st.ptr ↦ₛ st.bytes)` is split out on the non-empty path (`st.bytes ≠ []`). -/
def vecArgRestAt (A : RustAlloc) (st : VecArg) : SepProp :=
  (st.v ↦₆₄ st.cap) ∗ ((st.v + 8#64) ↦₆₄ st.ptr) ∗
    ((st.v + 16#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
    ⌜st.bytes.length ≤ st.cap.toNat ∧ st.cap.toNat < 2 ^ 63 ∧ st.ptr ≠ 0 ∧ st.cap ≠ 0⌝ ∗
    A.live st.ptr st.cap.toNat 1 ∗
    memRegion (st.ptr + BitVec.ofNat 64 st.bytes.length) (st.cap.toNat - st.bytes.length)

theorem vecArg_split_bytes (A : RustAlloc) (st : VecArg) (hne : st.bytes ≠ []) :
    st.at A ⊢ (st.ptr ↦ₛ st.bytes) ∗ vecArgRestAt A st := by
  simp only [VecArg.at, vecU8At, vecHeader, vecArgRestAt, sepConj_assoc, sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨hlen_cap, hcap_lt, hptr⟩ => ?_
  have hcap : st.cap ≠ 0 := by
    intro hc
    have h0 : st.cap.toNat = 0 := by rw [hc]; rfl
    have hpos : 0 < st.bytes.length := List.length_pos_of_ne_nil hne
    omega
  refine Entails.pure_right ⟨hlen_cap, hcap_lt, hptr, hcap⟩ ?_
  simp only [hcap, ↓reduceIte]
  exact Entails.of_eq (by ac_rfl)

theorem vecArg_join_bytes (A : RustAlloc) (st : VecArg) :
    (st.ptr ↦ₛ st.bytes) ∗ vecArgRestAt A st ⊢ st.at A := by
  simp only [VecArg.at, vecU8At, vecHeader, vecArgRestAt, sepConj_assoc, sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨hlen_cap, hcap_lt, hptr, hcap⟩ => ?_
  refine Entails.pure_right ⟨hlen_cap, hcap_lt, hptr⟩ ?_
  simp only [hcap, ↓reduceIte]
  exact Entails.of_eq (by ac_rfl)

/-- Shared stack & heap frame across the active loops of `spqr::decode_state`. -/
abbrev decodeStateLoopCommon (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (s0 : State) : SepProp :=
  v1StateJumpTablesAt b ∗
  vecArgRestAt A x.st ∗
  memRegion x.outPtr 352 ∗
  A.pool ∗
  stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
  memRegion (s0.sp - 1392#64) 336 ∗
  ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
  memRegion (s0.sp - 328#64) 224 ∗
  memRegion (s0.sp - 104#64) 8 ∗
  decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

/-- Fold `sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur` into
    `memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes)`. -/
theorem sliceCursorAfter_to_memRegion (sp ptr : BitVec 64) (bs cur : List (BitVec 8)) :
    sliceCursorAfter (sp - 1056#64) ptr bs cur ⊢
      memRegion (sp - 1056#64) 16 ∗ (ptr ↦ₛ bs) := by
  unfold sliceCursorAfter
  have h16 := pointsTo64_pair_entails_memRegion16 (sp - 1056#64)
    (ptr + BitVec.ofNat 64 (bs.length - cur.length)) (BitVec.ofNat 64 cur.length)
  have hassoc :
      ((sp - 1056#64) ↦₆₄ (ptr + BitVec.ofNat 64 (bs.length - cur.length))) ∗
        ((sp - 1056#64 + 8#64) ↦₆₄ BitVec.ofNat 64 cur.length) ∗ (ptr ↦ₛ bs) =
      (((sp - 1056#64) ↦₆₄ (ptr + BitVec.ofNat 64 (bs.length - cur.length))) ∗
        ((sp - 1056#64 + 8#64) ↦₆₄ BitVec.ofNat 64 cur.length)) ∗ (ptr ↦ₛ bs) := by ac_rfl
  rw [hassoc]
  exact sepConj_mono_left h16

/-- Fold `memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes) ∗ protoPqRatchetStateAt ... ∗
    memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗ decodeStateLoopCommon`
    into `decodeStateErrFrame`. -/
theorem loopCommon_to_errFrame (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      (x.st.ptr ↦ₛ x.st.bytes) ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0 ⊢
      decodeStateErrFrame H_inner b A x curSt s0 := by
  dsimp only [decodeStateLoopCommon, decodeStateErrFrame]
  have hst := vecArg_join_bytes A x.st
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        (v1StateJumpTablesAt b ∗ vecArgRestAt A x.st ∗ memRegion x.outPtr 352 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      v1StateJumpTablesAt b ∗
        ((x.st.ptr ↦ₛ x.st.bytes) ∗ vecArgRestAt A x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono hst (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono hlow (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

/-- Fold `sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur` + `protoPqRatchetStateCapOkAt`
    + `decodeStateLoopCommon` directly into `decodeStateErrFrame`. -/
theorem loopCommon_cursor_to_errFrame (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (cur : List (BitVec 8)) (remLen : Nat) (curSt : PqRatchetState) (s0 : State) :
    sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0 ⊢
      decodeStateErrFrame H_inner b A x curSt s0 := by
  have h1 := sliceCursorAfter_to_memRegion s0.sp x.st.ptr x.st.bytes cur
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remLen curSt
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  rw [sepConj_assoc]
  exact loopCommon_to_errFrame H_inner b A x curSt s0

/-- Fold callee error cursor output (`memRegion slot 16 ∗ ((ptr + ...) ↦ₛ cur) ∗ (ptr ↦ₛ take)`)
    + `protoPqRatchetStateCapOkAt` + `decodeStateLoopCommon` into `decodeStateErrFrame`. -/
theorem loopCommon_calleeErr_to_errFrame (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) {cur : List (BitVec 8)} (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur) (remLen : Nat) (curSt : PqRatchetState) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0 ⊢
      decodeStateErrFrame H_inner b A x curSt s0 := by
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remLen curSt
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 =
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
          ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))) ?_
  exact loopCommon_to_errFrame H_inner b A x curSt s0

/-- Fold callee error cursor output + `protoPqRatchetStateAt` + `decodeStateLoopCommon` into `decodeStateErrFrame`. -/
theorem loopCommon_calleeErr_proto_to_errFrame (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustAlloc) (x : DecodeStateGhost) {cur : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (curSt : PqRatchetState) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0 ⊢
      decodeStateErrFrame H_inner b A x curSt s0 := by
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 =
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
          ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h1)) ?_
  exact loopCommon_to_errFrame H_inner b A x curSt s0

/-! ## 2. Panic-Aware Call Wrappers (`decode_varint`, `skip_field`, `bytes::merge`, `ChainParams::merge`) -/

theorem SepWPpI.call_decodeVarint2 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {b : BitVec 64} {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (Varint.decodeVarint2Spec A))
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (v : BitVec 64) (rest : List (BitVec 8)),
      decodeVarint bs = some (v, rest) →
      rest.length < bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = v →
      SepWPpI img prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R))
    (herr : ∀ sf : State,
      decodeVarint bs = none →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 1#64 → sf.readReg64 .x1 ≠ 0#64 →
      SepWPpI img prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R)) :
    SepWPpI img prog ret s P Q (decodeStatePanicPost H_inner b A x_outer s0 R) := by
  intro hinv
  let sp_cur := s0.sp - 1392#64
  let x_dv : DecodeVarintSlowGhost := ⟨bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - Varint.decodeVarint2Stack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  refine ProofLib.SepWPp.call_wpp_frozen (x := x_dv) (F := F_ext) hcall hinv.1 hinv.2 hpc hrun halign hlr
    (fun R' hm => ?_) (fun sm _ _ _ hpost => ?_) (fun sm _ _ hm' => ?_)
    (fun sm hpcm hrunm hspm hcsm hfz hsym R' hpost hL => ?_)
    (fun sm _ _ hpost => False.elim (not_satisfies_false_sepConj hpost))
  · dsimp only [Varint.decodeVarint2Spec, x_dv]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur Varint.decodeVarint2Stack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  · dsimp only [Varint.decodeVarint2Spec] at hpost
    exact allowPanic_not_exited hpost
  · dsimp only [decodeStatePanicPost, decodeStateSpecX, Varint.decodeVarint2Spec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · rw [sepConj_assoc] at hpost
    dsimp only [Varint.decodeVarint2Spec, x_dv] at hpost
    rw [hsp] at hpost; rw [hsp] at hspm
    rcases hdv : decodeVarint bs with _ | ⟨v, rest⟩
    · simp only [hdv] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 1#64⌝ ∗ (⌜sm.readReg64 .x1 ≠ 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - Varint.decodeVarint2Stack) ∗
              stackAt sp_cur Varint.decodeVarint2Stack) ∗
            decodeErrorAtStackLen A (sm.readReg64 .x1) 0 ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_1, hx1_ne, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur Varint.decodeVarint2Stack (by decide))))))) hpost1
      exact herr sm hdv hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_1 hx1_ne ⟨hfz, hsym⟩ R' hpost2 hL
    · simp only [hdv] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64 ∧ sm.readReg64 .x1 = v⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - Varint.decodeVarint2Stack) ∗
              stackAt sp_cur Varint.decodeVarint2Stack) ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, ⟨hx0_0, hx1_v⟩, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur Varint.decodeVarint2Stack (by decide))))))) hpost1
      exact hok sm v rest hdv (decodeVarint_length hdv) (decodeVarint_suffix hdv)
        hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 hx1_v ⟨hfz, hsym⟩ R' hpost2 hL

theorem SepWPpI.call_skipField3 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {b : BitVec 64} {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (skipField3Spec A))
    (wt : WireType) (tag depth : Nat) (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 tag)
    (htag : tag < 2 ^ 32)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hx3 : (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 depth)
    (hdepth : depth ≤ 100)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (rest : List (BitVec 8)),
      skipField (2 * bs.length + 2) depth tag wt bs = some rest →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpI img prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R))
    (herr : ∀ sf : State,
      skipField (2 * bs.length + 2) depth tag wt bs = none →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpI img prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R)) :
    SepWPpI img prog ret s P Q (decodeStatePanicPost H_inner b A x_outer s0 R) := by
  intro hinv
  let sp_cur := s0.sp - 1392#64
  let x_sf : SkipFieldGhost := ⟨wt, tag, depth, bufRef, slot, ptr, bs⟩
  have hM : skipField3Stack depth ≤ v1StateMergeStack := by
    have h100 : skipField3Stack 100 ≤ v1StateMergeStack := by decide
    have hmono : skipField3Stack depth ≤ skipField3Stack 100 := by unfold skipField3Stack; omega
    omega
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - skipField3Stack depth) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  refine ProofLib.SepWPp.call_wpp_frozen (x := x_sf) (F := F_ext) hcall hinv.1 hinv.2 hpc hrun halign hlr
    (fun R' hm => ?_) (fun sm _ _ _ hpost => ?_) (fun sm _ _ hm' => ?_)
    (fun sm hpcm hrunm hspm hcsm hfz hsym R' hpost hL => ?_)
    (fun sm _ _ hpost => False.elim (not_satisfies_false_sepConj hpost))
  · dsimp only [skipField3Spec, x_sf]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, htag, hx2, hx3, by omega, hlen⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur (skipField3Stack depth) hM)))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  · dsimp only [skipField3Spec] at hpost
    exact allowPanic_not_exited hpost
  · dsimp only [decodeStatePanicPost, decodeStateSpecX, skipField3Spec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · rw [sepConj_assoc] at hpost
    dsimp only [skipField3Spec, x_sf] at hpost
    rw [hsp] at hpost; rw [hsp] at hspm
    rcases hsf : skipField (2 * bs.length + 2) depth tag wt bs with _ | rest
    · simp only [hsf] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - skipField3Stack depth) ∗
              stackAt sp_cur (skipField3Stack depth)) ∗
            decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_ne, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur (skipField3Stack depth) hM)))))) hpost1
      exact herr sm hsf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne ⟨hfz, hsym⟩ R' hpost2 hL
    · simp only [hsf] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - skipField3Stack depth) ∗
              stackAt sp_cur (skipField3Stack depth)) ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_0, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur (skipField3Stack depth) hM)))))) hpost1
      have hle := (skip_length (2 * bs.length + 2)).1 depth tag wt bs rest hsf
      have hsuf := (skip_suffix (2 * bs.length + 2)).1 depth tag wt bs rest hsf
      exact hok sm rest hsf hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 ⟨hfz, hsym⟩ R' hpost2 hL

theorem SepWPpI.call_bytesMerge3 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {b : BitVec 64} {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry ((bytesMerge3RawSpec A).inImage img))
    (wt : WireType) (valPtr : BitVec 64) (valBs : List (BitVec 8))
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = valPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = (vecU8CapOkAt A valPtr bs.length valBs ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (v rest : List (BitVec 8)),
      (Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption = some (v, rest) →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpI img prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          vecU8CapOkAt A valPtr rest.length v ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R))
    (herr : ∀ sf : State,
      (Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption = none →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPpI img prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          rustBytesVecAt A valPtr valBs ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R)) :
    SepWPpI img prog ret s P Q (decodeStatePanicPost H_inner b A x_outer s0 R) := by
  intro hinv
  rw [hP]
  unfold vecU8CapOkAt
  simp only [sepExists_sepConj_left]
  refine ProofLib.SepWPp.exists_elim fun valCap => ProofLib.SepWPp.exists_elim fun valBuf => ?_
  refine SepWPp.mono_pre (Entails.of_eq (show
      (((⌜BytesMergeCapOk valCap bs.length⌝ ∗ vecU8At A valPtr valCap valBuf valBs) ∗
        (bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr bs ∗ A.pool ∗
        stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F) =
      (⌜BytesMergeCapOk valCap bs.length⌝ ∗
        ((vecU8At A valPtr valCap valBuf valBs ∗ (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr bs ∗ A.pool ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)) by ac_rfl)) ?_
  refine ProofLib.SepWPp.pure_elim fun hcap_ok => ?_
  let sp_cur := s0.sp - 1392#64
  let x_bm : BytesMergeGhost := ⟨wt, valPtr, valCap, valBuf, valBs, bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - bytesMerge3Stack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  refine ProofLib.SepWPp.call_wpp_frozen (x := x_bm) (F := F_ext) hcall hinv.1 hinv.2 hpc hrun halign hlr
    (fun R' hm => ?_) (fun sm _ _ _ hpost => ?_) (fun sm _ _ hm' => ?_)
    (fun sm hpcm hrunm hspm hcsm hfz hsym R' hpost hL => ?_)
    (fun sm _ _ hpost => False.elim (not_satisfies_false_sepConj hpost))
  · change s.mem ⊨ (⌜ImgCallInv img s⌝ ∗ (bytesMerge3RawSpec A).pre x_bm s) ∗ (F_ext ∗ R')
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    dsimp only [bytesMerge3RawSpec, x_bm]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hcap_ok⟩, ?_⟩
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur bytesMerge3Stack (by decide)))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  · dsimp only [bytesMerge3RawSpec, Spec.inImage] at hpost
    exact allowPanic_not_exited hpost
  · dsimp only [decodeStatePanicPost, decodeStateSpecX, bytesMerge3RawSpec, Spec.inImage] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · rw [sepConj_assoc] at hpost
    change sm.mem ⊨ (bytesMerge3RawSpec A).post x_bm s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [bytesMerge3RawSpec, x_bm] at hpost
    have hmb_eq : mergeBytes wt bs = (Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption := by
      have h := proto_mergeBytes_toOption (codecWireTypeToProto wt) bs
      rw [protoWireTypeToCodec_codecWireTypeToProto] at h
      exact h.symm
    rw [hmb_eq, hsp] at hpost; rw [hsp] at hspm
    rcases hmb : (Proto.mergeBytes (codecWireTypeToProto wt) bs).toOption with _ | ⟨v, rest⟩
    · simp only [hmb] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗
          (vecU8At A valPtr valCap valBuf valBs ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool ∗
              (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
                (v1StateMergeStack - bytesMerge3Stack) ∗
                stackAt sp_cur bytesMerge3Stack) ∗
              decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗
              memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_ne, hpost1⟩
      have hvec : vecU8At A valPtr valCap valBuf valBs ⊢ rustBytesVecAt A valPtr valBs := by
        unfold rustBytesVecAt
        exact Entails.sepExists_right valCap (Entails.sepExists_right valBuf (Entails.refl _))
      have hpost1' := Satisfies.mono (sepConj_mono hvec (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur bytesMerge3Stack (by decide)))))))) hpost1
      have hpost2 : sm.mem ⊨
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt sp_cur v1StateMergeStack ∗
            decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗
            rustBytesVecAt A valPtr valBs ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R' :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost1'
      exact herr sm hmb hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne ⟨hfz, hsym⟩ R' hpost2 hL
    · simp only [hmb] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - bytesMerge3Stack) ∗
              stackAt sp_cur bytesMerge3Stack) ∗
            vecU8CapOkAt A valPtr rest.length v ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext, vecU8CapOkAt]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_0, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur bytesMerge3Stack (by decide))))))) hpost1
      have ⟨hle, hsuf⟩ := proto_mergeBytes_suffix hmb
      exact hok sm v rest hmb hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 ⟨hfz, hsym⟩ R' hpost2 hL

theorem SepWPpI.call_chainParamsMerge {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {b : BitVec 64} {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (chainParamsMergeSpec A))
    (wt : WireType) (msgPtr : BitVec 64) (msg : ChainParamsPB)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = (chainParamsPBAt msgPtr msg ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : ChainParamsPB) (rest : List (BitVec 8)),
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption = some (m', rest) →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpI img prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          chainParamsPBAt msgPtr m' ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R))
    (herr : ∀ (sf : State) (n : Nat) (m' : ChainParamsPB),
      (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption = none →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 1 →
      SepWPpI img prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A (sf.readReg64 .x0) n ∗
          chainParamsPBAt msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R)) :
    SepWPpI img prog ret s P Q (decodeStatePanicPost H_inner b A x_outer s0 R) := by
  intro hinv
  let sp_cur := s0.sp - 1392#64
  let x_cp : ChainParamsMergeGhost := ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - chainParamsMergeStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  refine ProofLib.SepWPp.call_wpp_frozen (x := x_cp) (F := F_ext) hcall hinv.1 hinv.2 hpc hrun halign hlr
    (fun R' hm => ?_) (fun sm _ _ _ hpost => ?_) (fun sm _ _ hm' => ?_)
    (fun sm hpcm hrunm hspm hcsm hfz hsym R' hpost hL => ?_)
    (fun sm _ _ hpost => False.elim (not_satisfies_false_sepConj hpost))
  · dsimp only [chainParamsMergeSpec, x_cp]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur chainParamsMergeStack (by decide)))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  · dsimp only [chainParamsMergeSpec] at hpost
    exact allowPanic_not_exited hpost
  · dsimp only [decodeStatePanicPost, decodeStateSpecX, chainParamsMergeSpec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · rw [sepConj_assoc] at hpost
    dsimp only [chainParamsMergeSpec, x_cp] at hpost
    rw [hsp] at hpost; rw [hsp] at hspm
    rcases hcp : (Proto.mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto wt) msg bs 99).toOption with _ | ⟨m', rest⟩
    · simp only [hcp, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨m', n, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗ (⌜n ≤ 1⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - chainParamsMergeStack) ∗
              stackAt sp_cur chainParamsMergeStack) ∗
            decodeErrorAtStackLen A (sm.readReg64 .x0) n ∗
            chainParamsPBAt msgPtr m' ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_ne, hn, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur chainParamsMergeStack (by decide))))))) hpost1
      exact herr sm n m' hcp hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne hn ⟨hfz, hsym⟩ R' hpost2 hL
    · simp only [hcp] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - chainParamsMergeStack) ∗
              stackAt sp_cur chainParamsMergeStack) ∗
            chainParamsPBAt msgPtr m' ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_0, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur chainParamsMergeStack (by decide))))))) hpost1
      have ⟨hle, hsuf⟩ := proto_mergeMessage_suffix hcp
      exact hok sm m' rest hcp hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 ⟨hfz, hsym⟩ R' hpost2 hL

/-! ## 3. Pure `Proto.mergeMessage` Bridge Lemmas -/

theorem mergeMessage_toOption_of_ne_lengthDelimited {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    {iwt : WireType} {m : M} {bs : List (BitVec 8)} {depth' : Nat}
    (hne : iwt ≠ .lengthDelimited) :
    (Proto.mergeMessage mergeField (codecWireTypeToProto iwt) m bs (depth' + 1)).toOption = none := by
  cases iwt <;> first | exact (hne rfl).elim | rfl

theorem mergeMessage_toOption_of_decodeVarint_none {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    {m : M} {bs : List (BitVec 8)} {depth' : Nat}
    (hd : decodeVarint bs = none) :
    (Proto.mergeMessage mergeField .lengthDelimited m bs (depth' + 1)).toOption = none := by
  have hd' : (Proto.decodeVarint bs).toOption = none := by rw [proto_decodeVarint_toOption, hd]
  rcases hdv : Proto.decodeVarint bs with e | ⟨len64, rest⟩
  · simp [Proto.mergeMessage, Proto.checkWireType, hdv, Bind.bind, Except.bind, Except.toOption]
  · simp [hdv, Except.toOption] at hd'

theorem mergeMessage_toOption_of_lt {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    {m : M} {bs rest : List (BitVec 8)} {len64 : BitVec 64} {depth' : Nat}
    (hd : decodeVarint bs = some (len64, rest)) (hlt : rest.length < len64.toNat) :
    (Proto.mergeMessage mergeField .lengthDelimited m bs (depth' + 1)).toOption = none := by
  have hd' : (Proto.decodeVarint bs).toOption = some (len64, rest) := by rw [proto_decodeVarint_toOption, hd]
  rcases hdv : Proto.decodeVarint bs with e | ⟨l', r'⟩
  · simp [hdv, Except.toOption] at hd'
  · simp only [hdv, Except.toOption, Option.some.injEq, Prod.mk.injEq] at hd'
    rcases hd' with ⟨hl, hr⟩
    subst l' r'
    simp only [Proto.mergeMessage, Proto.checkWireType, ↓reduceIte, hdv, Bind.bind, Except.bind,
      takeExact_eq_take_drop]
    have hnot : ¬ len64.toNat ≤ rest.length := by omega
    simp [hnot, Except.toOption]

theorem mergeMessage_toOption_of_ge {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {bs rest : List (BitVec 8)} {len64 : BitVec 64} {depth' : Nat}
    (hd : decodeVarint bs = some (len64, rest)) (hge : ¬ rest.length < len64.toNat) :
    (Proto.mergeMessage mergeField .lengthDelimited m bs (depth' + 1)).toOption =
      (mergeLoopBin mergeField (rest.length - (rest.length - len64.toNat)) m rest
        (rest.length - len64.toNat) depth').map (fun m' => (m', rest.drop len64.toNat)) := by
  have hd' : (Proto.decodeVarint bs).toOption = some (len64, rest) := by rw [proto_decodeVarint_toOption, hd]
  rcases hdv : Proto.decodeVarint bs with e | ⟨l', r'⟩
  · simp [hdv, Except.toOption] at hd'
  · simp only [hdv, Except.toOption, Option.some.injEq, Prod.mk.injEq] at hd'
    rcases hd' with ⟨hl, hr⟩
    subst l' r'
    have hle : len64.toNat ≤ rest.length := by omega
    have hlen_take : (rest.take len64.toNat).length = rest.length - (rest.length - len64.toNat) := by
      simp [hle]; omega
    have happ := mergeLoopBin_append_eq hmf (rest.length - (rest.length - len64.toNat))
      (rest.take len64.toNat) (rest.drop len64.toNat) (rest.take len64.toNat).length m depth'
      (by omega) (Nat.le_refl _)
    rw [List.take_append_drop, List.length_drop, hlen_take] at happ
    have hchk : Proto.checkWireType .lengthDelimited .lengthDelimited = .ok () := rfl
    simp only [Proto.mergeMessage, hchk, hdv, Bind.bind, Except.bind,
      takeExact_eq_take_drop, hle, ↓reduceIte, Pure.pure, Except.pure, hlen_take, happ]
    rcases Proto.mergeFieldsLoop mergeField (rest.length - (rest.length - len64.toNat))
      m (rest.take len64.toNat) depth' with e | m' <;> rfl

end CryptoVerification.SpqrV1.Top.DecodeState

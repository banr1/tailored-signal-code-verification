/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Defs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SpqrV1.Auth.New
public import LibsignalBinary.Proofs.SpqrV1.GF.IsNonZero
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk`: Shared Layout, Byte-Shift, and Framing Helpers

Panic entailments, `EkSentCt1Received` struct unpack/pack lemmas, `libcruxHmacSafeSpec`,
byte-shift combinators (`b0`, `b7`, `mid7At`, `low7At`), and stack framing helpers for `0x5ec2c`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.RecvCt2Chunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts SplitBytes NewFacts

section Part1Helpers
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## Offset and Panic Helpers -/

theorem onPanic_alloc_entails_recvCt2 {P : Prop} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  refine Entails.pure_left fun ⟨haf, hpref⟩ => ?_
  exact Entails.pure_right ⟨Or.inr haf, hpref⟩ (entails_anyHeap _)

theorem onPanic_hmac_entails_recvCt2 {P : Prop} {klen dlen : Nat} {s0 s sf : State} {F : SepProp}
    (hk : klen < 2 ^ 32) (hd : dlen < 2 ^ 32) (htr : s.trace = s0.trace) :
    (⌜(allocFailedIn s sf ∨ 2 ^ 32 ≤ klen ∨ 2 ^ 32 ≤ dlen) ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  refine Entails.pure_left fun ⟨hdisj, hpref⟩ => ?_
  rcases hdisj with haf | hk' | hd'
  · exact Entails.pure_right ⟨Or.inr haf, hpref⟩ (entails_anyHeap _)
  · omega
  · omega

theorem allowPanic_isPanic_recvCt2 {P : Prop} {s0 sf : State} {Q R : SepProp}
    (hP : P) (htr : sf.trace = s0.trace)
    (hm : (Rust.panicked sf).mem ⊨ Q ∗ R) :
    (Rust.panicked sf).mem ⊨
      (⌜(P ∨ allocFailedIn s0 (Rust.panicked sf)) ∧ s0.trace <+: (Rust.panicked sf).trace⌝ ∗ anyHeap) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have hpref : s0.trace <+: (Rust.panicked sf).trace := by
    simp only [Rust.panicked, htr]
    exact List.prefix_refl _
  exact ⟨⟨Or.inl hP, hpref⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap Q)) hm⟩

theorem allowPanic_oom_recvCt2 {P : Prop} {s0 sf : State} {Q R : SepProp}
    (haf : allocFailedIn s0 (Rust.panicked sf) ∧ s0.trace <+: (Rust.panicked sf).trace)
    (hm : (Rust.panicked sf).mem ⊨ Q ∗ R) :
    (Rust.panicked sf).mem ⊨
      (⌜(P ∨ allocFailedIn s0 (Rust.panicked sf)) ∧ s0.trace <+: (Rust.panicked sf).trace⌝ ∗ anyHeap) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨Or.inr haf.1, haf.2⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap Q)) hm⟩

theorem subroutine_ok_inImage_rodata3_keep {α : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {roAddr1 roAddr2 roAddr3 : BitVec 64}
    {roBytes1 roBytes2 roBytes3 : List (BitVec 8)}
    {spec : Spec α}
    (hro1 : ∀ {s : State} (_ : img.FrozenLoaded s) {P : SepProp},
      (s.mem ⊨ P) → (s.mem ⊨ (roAddr1 ↦ᵣ roBytes1) ∗ P))
    (hro2 : ∀ {s : State} (_ : img.FrozenLoaded s) {P : SepProp},
      (s.mem ⊨ P) → (s.mem ⊨ (roAddr2 ↦ᵣ roBytes2) ∗ P))
    (hro3 : ∀ {s : State} (_ : img.FrozenLoaded s) {P : SepProp},
      (s.mem ⊨ P) → (s.mem ⊨ (roAddr3 ↦ᵣ roBytes3) ∗ P))
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
          (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗ (roAddr3 ↦ᵣ roBytes3) ∗ spec.pre x s
        post := fun x s0 sf =>
          (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗ (roAddr3 ↦ᵣ roBytes3) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hL, hpre⟩
  have hpre' : s0.mem ⊨
      (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (roAddr1 ↦ᵣ roBytes1) ∗ (roAddr2 ↦ᵣ roBytes2) ∗ (roAddr3 ↦ᵣ roBytes3) ∗ spec.pre x s0) ∗ R := by
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hL, hro1 hL.1 (hro2 hL.1 (hro3 hL.1 hpre))⟩
  refine (h.to_outcome x R s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hq
    exact Satisfies.of_sep_right (Satisfies.of_sep_right (Satisfies.of_sep_right hq))
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

abbrev assertFailedU64Name : String := "core::panicking::assert_failed::<u64, u64>"
abbrev sliceIndexFailName : String := "core::slice::index::slice_index_fail"
abbrev unwrapFailedName : String := "core::result::unwrap_failed"
abbrev panicBoundsCheckName : String := "core::panicking::panic_bounds_check"
abbrev panicConstAddOverflowName : String := "core::panicking::panic_const::panic_const_add_overflow"

@[simp, arm64_norm] theorem assertFailedU64_fnOff :
    libsignalSessionCode.fnOff assertFailedU64Name =
      ls_off% "core::panicking::assert_failed::<u64, u64>" :=
  ls_stub% "core::panicking::assert_failed::<u64, u64>"

@[simp, arm64_norm] theorem sliceIndexFail_fnOff :
    libsignalSessionCode.fnOff sliceIndexFailName =
      ls_off% "core::slice::index::slice_index_fail" :=
  ls_stub% "core::slice::index::slice_index_fail"

@[simp, arm64_norm] theorem unwrapFailed_fnOff :
    libsignalSessionCode.fnOff unwrapFailedName =
      ls_off% "core::result::unwrap_failed" :=
  ls_stub% "core::result::unwrap_failed"

@[simp, arm64_norm] theorem panicBoundsCheck_fnOff :
    libsignalSessionCode.fnOff panicBoundsCheckName =
      ls_off% "core::panicking::panic_bounds_check" :=
  ls_stub% "core::panicking::panic_bounds_check"

@[simp, arm64_norm] theorem panicConstAddOverflow_fnOff :
    libsignalSessionCode.fnOff panicConstAddOverflowName =
      ls_off% "core::panicking::panic_const::panic_const_add_overflow" :=
  ls_stub% "core::panicking::panic_const::panic_const_add_overflow"

@[simp, arm64_norm] theorem memcpy_fnOff :
    libsignalSessionCode.fnOff memcpyName = ls_off% "memcpy" :=
  ls_stub% "memcpy"

@[simp, arm64_norm] theorem gf16IsNonZero_fnOff :
    libsignalSessionCode.fnOff isNonZeroName = 0x5e5f0 :=
  libsignalSessionCode_fnOff_0x5e5f0

open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts SplitBytes

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  recvCt2Chunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff mlkemDecaps_fnOff
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x67028
  libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x58ac4
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x46920
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5e5f0
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::result::unwrap_failed") (ls_hook% "core::result::unwrap_failed")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")

open Lean Elab Tactic Meta in
elab "wpp_call_inImage_recvCt2 " hcall:term:max a:term:max hF:term:max : tactic => do
  let hcallCopyId ← freshIdent `hcall_copy
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    have $hcallCopyId := $hcall
    apply (MacHdrFacts.SepWPp.call_allowPanic_inImage_mid $hcallCopyId (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_inImage_recvCt2: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR'
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm, *]
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcallCopyId)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; first
      | exact onPanic_alloc_entails_recvCt2 (by wp_norm_lhs)
      | exact NextKeyInternalFacts.onPanic_entails_of_trace_eq (by wp_norm_lhs)
      | exact Entails.pure_left False.elim)
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    try clear $hcallCopyId
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  for _ in [:2] do
    let mvarId ← getMainGoal
    let ref ← IO.mkRef #[]
    mvarId.withContext do
      let ty ← instantiateMVars (← mvarId.getType)
      ty.forEach fun sub => do
        if sub.isConst then
          let nm := sub.constName!
          if nm != ``Arm64.Spec.mk && nm != ``Arm64.Spec.inImage then
            let subTy ← inferType sub
            if subTy.getForallBody.isAppOf ``Arm64.Spec then
              let arr ← ref.get
              if !arr.any (fun i => i.getId == nm) then
                ref.set (arr.push (mkIdent nm))
    let ids ← ref.get
    for id in ids do
      let _ ← tryTactic (evalTactic (← `(tactic| dsimp only [$id:ident])))
  let _ ← tryTactic (evalTactic (← `(tactic| dsimp only)))
  for hId in [hspId, hcsId] do
    let _ ← tryTactic (evalTactic (← `(tactic| dsimp only at $hId:ident)))
    let _ ← tryTactic (evalTactic (← `(tactic|
      simp (config := { decide := true }) only [
        ← disjointRegions_iff_disjoint64,
        ← disjointRegions_iff_disjoint128,
        Arm64.CalleeSavedPreserved,
        wp_norm, arm64_norm] at $hId:ident)))
  let mut worklist : List Ident := [hspId, hcsId]
  while !worklist.isEmpty do
    let currId :: rest := worklist | break
    worklist := rest
    let mvarId ← getMainGoal
    let lctx ← mvarId.withContext getLCtx
    if let some decl := lctx.findFromUserName? currId.getId then
      let ty ← mvarId.withContext (instantiateMVars decl.type)
      if ty.isAppOfArity ``And 2 then
        let h1 ← freshIdent `h
        if ← tryTactic (evalTactic (← `(tactic| rcases $currId:ident with ⟨$h1:ident, $currId:ident⟩))) then
          worklist := h1 :: currId :: worklist
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hspId:ident]))))

/-! ## Structural Expose and Fold Helpers for `EkSentCt1Received` -/

open NewFacts

theorem polyDecoderAt_pts_length (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a dec ⊢ ⌜dec.pts.length = 16⌝ ∗ polyDecoderAt A a dec := by
  unfold polyDecoderAt
  refine Entails.pure_left fun ⟨hlen, hneed⟩ => ?_
  exact Entails.pure_right hlen (Entails.pure_right ⟨hlen, hneed⟩ (Entails.refl _))

/-- Heap portion of `vecU8At A v cap ptr bs` (independent of header address `v`). -/
def vecU8HeapAt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_cells_heap (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8HeapAt A cap ptr bs := by
  unfold vecU8At vecHeader vecU8HeapAt
  ac_rfl

theorem vecU8_expose_cells_heap (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  unfold vecU8
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  exact Entails.sepExists_right cap
    (Entails.sepExists_right ptr (Entails.of_eq (vecU8At_eq_cells_heap A v cap ptr bs)))

theorem vecU8_of_cells_heap (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8HeapAt A cap ptr bs ⊢
      vecU8 A v bs := by
  unfold vecU8
  exact Entails.sepExists_right cap
    (Entails.sepExists_right ptr (Entails.of_eq (vecU8At_eq_cells_heap A v cap ptr bs).symm))

theorem ekSentCt1ReceivedUcAt_expose_entails (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    ekSentCt1ReceivedUcAt A a uc ⊢
      ∃∗ g_auth : AuthenticatorGhost,
      ∃∗ cap_dk : BitVec 64, ∃∗ ptr_dk : BitVec 64,
      ∃∗ cap_ct1 : BitVec 64, ∃∗ ptr_ct1 : BitVec 64,
        (a ↦₆₄ g_auth.rootKey.cap) ∗
        ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
        ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
        ((a + 48#64) ↦₆₄ cap_dk) ∗
        ((a + 56#64) ↦₆₄ ptr_dk) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 uc.dk.length) ∗
        ((a + 72#64) ↦₆₄ cap_ct1) ∗
        ((a + 80#64) ↦₆₄ ptr_ct1) ∗
        ((a + 88#64) ↦₆₄ BitVec.ofNat 64 uc.ct1.length) ∗
        ((a + 96#64) ↦₆₄ uc.epoch) ∗
        authenticatorHeapAt A g_auth uc.auth ∗
        vecU8HeapAt A cap_dk ptr_dk uc.dk ∗
        vecU8HeapAt A cap_ct1 ptr_ct1 uc.ct1 := by
  unfold ekSentCt1ReceivedUcAt
  rw [authenticatorAt_eq_exists_pinned A a uc.auth]
  refine Entails.trans (sepConj_mono_left (Entails.sepExists_elim fun g_auth =>
    Entails.sepExists_right g_auth (Entails.of_eq (authenticatorPinAt_eq_cells_heap A g_auth a uc.auth)))) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g_auth => Entails.sepExists_right g_auth ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (vecU8_expose_cells_heap A (a + 48#64) uc.dk))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun cap_dk => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ptr_dk => ?_
  refine Entails.sepExists_right cap_dk (Entails.sepExists_right ptr_dk ?_)
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (vecU8_expose_cells_heap A (a + 72#64) uc.ct1)))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun cap_ct1 => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ptr_ct1 => ?_
  refine Entails.sepExists_right cap_ct1 (Entails.sepExists_right ptr_ct1 ?_)
  have h56 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have h64 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  have h80 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have h88 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  rw [h56, h64, h80, h88]
  exact Entails.of_eq (by ac_rfl)

theorem ekSentCt1ReceivedUcAt_fold_entails (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (g_auth : AuthenticatorGhost) (cap_dk ptr_dk cap_ct1 ptr_ct1 : BitVec 64) :
    (a ↦₆₄ g_auth.rootKey.cap) ∗
      ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
      ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
      ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
      ((a + 48#64) ↦₆₄ cap_dk) ∗
      ((a + 56#64) ↦₆₄ ptr_dk) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 uc.dk.length) ∗
      ((a + 72#64) ↦₆₄ cap_ct1) ∗
      ((a + 80#64) ↦₆₄ ptr_ct1) ∗
      ((a + 88#64) ↦₆₄ BitVec.ofNat 64 uc.ct1.length) ∗
      ((a + 96#64) ↦₆₄ uc.epoch) ∗
      authenticatorHeapAt A g_auth uc.auth ∗
      vecU8HeapAt A cap_dk ptr_dk uc.dk ∗
      vecU8HeapAt A cap_ct1 ptr_ct1 uc.ct1 ⊢
      ekSentCt1ReceivedUcAt A a uc := by
  unfold ekSentCt1ReceivedUcAt
  have h56 : a + 56#64 = (a + 48#64) + 8#64 := by bv_omega
  have h64 : a + 64#64 = (a + 48#64) + 16#64 := by bv_omega
  have h80 : a + 80#64 = (a + 72#64) + 8#64 := by bv_omega
  have h88 : a + 88#64 = (a + 72#64) + 16#64 := by bv_omega
  rw [h56, h64, h80, h88]
  have harrange :
      (a ↦₆₄ g_auth.rootKey.cap) ∗
        ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
        ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
        ((a + 48#64) ↦₆₄ cap_dk) ∗
        (((a + 48#64) + 8#64) ↦₆₄ ptr_dk) ∗
        (((a + 48#64) + 16#64) ↦₆₄ BitVec.ofNat 64 uc.dk.length) ∗
        ((a + 72#64) ↦₆₄ cap_ct1) ∗
        (((a + 72#64) + 8#64) ↦₆₄ ptr_ct1) ∗
        (((a + 72#64) + 16#64) ↦₆₄ BitVec.ofNat 64 uc.ct1.length) ∗
        ((a + 96#64) ↦₆₄ uc.epoch) ∗
        authenticatorHeapAt A g_auth uc.auth ∗
        vecU8HeapAt A cap_dk ptr_dk uc.dk ∗
        vecU8HeapAt A cap_ct1 ptr_ct1 uc.ct1 =
      ((a ↦₆₄ g_auth.rootKey.cap) ∗
        ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
        ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
        authenticatorHeapAt A g_auth uc.auth) ∗
      (((a + 48#64) ↦₆₄ cap_dk) ∗
        (((a + 48#64) + 8#64) ↦₆₄ ptr_dk) ∗
        (((a + 48#64) + 16#64) ↦₆₄ BitVec.ofNat 64 uc.dk.length) ∗
        vecU8HeapAt A cap_dk ptr_dk uc.dk) ∗
      (((a + 72#64) ↦₆₄ cap_ct1) ∗
        (((a + 72#64) + 8#64) ↦₆₄ ptr_ct1) ∗
        (((a + 72#64) + 16#64) ↦₆₄ BitVec.ofNat 64 uc.ct1.length) ∗
        vecU8HeapAt A cap_ct1 ptr_ct1 uc.ct1) ∗
      ((a + 96#64) ↦₆₄ uc.epoch) := by ac_rfl
  rw [harrange, ← authenticatorPinAt_eq_cells_heap A g_auth a uc.auth]
  exact sepConj_mono
    (authenticatorPinAt_entails_authenticatorAt A g_auth a uc.auth)
    (sepConj_mono (vecU8_of_cells_heap A (a + 48#64) cap_dk ptr_dk uc.dk)
      (sepConj_mono_left (vecU8_of_cells_heap A (a + 72#64) cap_ct1 ptr_ct1 uc.ct1)))

theorem ekSentCt1ReceivedCells_entails_memRegion_504
    (a c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : BitVec 64) :
    (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
      ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
      ((a + 48#64) ↦₆₄ c6) ∗ ((a + 56#64) ↦₆₄ c7) ∗ ((a + 64#64) ↦₆₄ c8) ∗
      ((a + 72#64) ↦₆₄ c9) ∗ ((a + 80#64) ↦₆₄ c10) ∗ ((a + 88#64) ↦₆₄ c11) ∗
      ((a + 96#64) ↦₆₄ c12) ∗ memRegion (a + 104#64) 400 ⊢
      memRegion a chunkedEkSentCt1ReceivedSize := by
  change _ ⊢ memRegion a 504
  rw [ProofLib.memRegion_split' (b := a) (n := 104) (k := 400)
        (b' := a + 104#64) rfl rfl (by decide),
      ProofLib.memRegion_cells a 13 (by decide)]
  have hc13 :
      (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
        ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
        ((a + 48#64) ↦₆₄ c6) ∗ ((a + 56#64) ↦₆₄ c7) ∗ ((a + 64#64) ↦₆₄ c8) ∗
        ((a + 72#64) ↦₆₄ c9) ∗ ((a + 80#64) ↦₆₄ c10) ∗ ((a + 88#64) ↦₆₄ c11) ∗
        ((a + 96#64) ↦₆₄ c12) ⊢ cells a 13 := by
    dsimp only [cells]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      emp_sepConj, sepConj_emp]
    exact Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
      (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
        (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
          (Entails.sepExists_right c9 (Entails.sepExists_right c10 (Entails.sepExists_right c11
            (Entails.sepExists_right c12 (Entails.refl _)))))))))))))
  have hgroup :
      (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
        ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
        ((a + 48#64) ↦₆₄ c6) ∗ ((a + 56#64) ↦₆₄ c7) ∗ ((a + 64#64) ↦₆₄ c8) ∗
        ((a + 72#64) ↦₆₄ c9) ∗ ((a + 80#64) ↦₆₄ c10) ∗ ((a + 88#64) ↦₆₄ c11) ∗
        ((a + 96#64) ↦₆₄ c12) ∗ memRegion (a + 104#64) 400 =
      ((a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
        ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
        ((a + 48#64) ↦₆₄ c6) ∗ ((a + 56#64) ↦₆₄ c7) ∗ ((a + 64#64) ↦₆₄ c8) ∗
        ((a + 72#64) ↦₆₄ c9) ∗ ((a + 80#64) ↦₆₄ c10) ∗ ((a + 88#64) ↦₆₄ c11) ∗
        ((a + 96#64) ↦₆₄ c12)) ∗ memRegion (a + 104#64) 400 := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_left hc13

theorem memRegion_504_at_fsp_280_split (fsp : BitVec 64) :
    memRegion (fsp + 0x280#64) 504 =
      (∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
       ∃∗ d4 : BitVec 64, ∃∗ d5 : BitVec 64, ∃∗ d6 : BitVec 64, ∃∗ d7 : BitVec 64,
       ∃∗ d8 : BitVec 64, ∃∗ d9 : BitVec 64, ∃∗ d10 : BitVec 64, ∃∗ d11 : BitVec 64,
       ∃∗ d12 : BitVec 64,
        ((fsp + 0x280#64) ↦₆₄ d0) ∗ ((fsp + 0x288#64) ↦₆₄ d1) ∗
        ((fsp + 0x290#64) ↦₆₄ d2) ∗ ((fsp + 0x298#64) ↦₆₄ d3) ∗
        ((fsp + 0x2a0#64) ↦₆₄ d4) ∗ ((fsp + 0x2a8#64) ↦₆₄ d5) ∗
        ((fsp + 0x2b0#64) ↦₆₄ d6) ∗ ((fsp + 0x2b8#64) ↦₆₄ d7) ∗
        ((fsp + 0x2c0#64) ↦₆₄ d8) ∗ ((fsp + 0x2c8#64) ↦₆₄ d9) ∗
        ((fsp + 0x2d0#64) ↦₆₄ d10) ∗ ((fsp + 0x2d8#64) ↦₆₄ d11) ∗
        ((fsp + 0x2e0#64) ↦₆₄ d12)) ∗
      memRegion (fsp + 0x2e8#64) 400 := by
  rw [ProofLib.memRegion_split' (b := fsp + 0x280#64) (n := 104) (k := 400)
        (b' := fsp + 0x2e8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (fsp + 0x280#64) 13 (by decide)]
  congr 1
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem ekSentCt1ReceivedAt_fsp_280_entails (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64) (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (receivingCt2 : PolyDecoder)
    (g_auth : AuthenticatorGhost) (cap_dk ptr_dk cap_ct1 ptr_ct1 : BitVec 64) :
    ((sp - 1856#64) ↦₆₄ g_auth.rootKey.cap) ∗
      ((sp - 1848#64) ↦₆₄ g_auth.rootKey.ptr) ∗
      ((sp - 1840#64) ↦₆₄ BitVec.ofNat 64 (uc.auth : Authenticator).rootKey.length) ∗
      ((sp - 1832#64) ↦₆₄ g_auth.macKey.cap) ∗
      ((sp - 1824#64) ↦₆₄ g_auth.macKey.ptr) ∗
      ((sp - 1816#64) ↦₆₄ BitVec.ofNat 64 (uc.auth : Authenticator).macKey.length) ∗
      ((sp - 1808#64) ↦₆₄ cap_dk) ∗
      ((sp - 1800#64) ↦₆₄ ptr_dk) ∗
      ((sp - 1792#64) ↦₆₄ BitVec.ofNat 64 uc.dk.length) ∗
      ((sp - 1784#64) ↦₆₄ cap_ct1) ∗
      ((sp - 1776#64) ↦₆₄ ptr_ct1) ∗
      ((sp - 1768#64) ↦₆₄ BitVec.ofNat 64 uc.ct1.length) ∗
      ((sp - 1760#64) ↦₆₄ uc.epoch) ∗
      authenticatorHeapAt A g_auth uc.auth ∗
      vecU8HeapAt A cap_dk ptr_dk uc.dk ∗
      vecU8HeapAt A cap_ct1 ptr_ct1 uc.ct1 ∗
      polyDecoderAt A (sp - 1752#64) receivingCt2 ⊢
      ekSentCt1ReceivedAt A (sp - 1856#64) { uc := uc, receiving_ct2 := receivingCt2 } := by
  unfold ekSentCt1ReceivedAt ekSentCt1ReceivedUcAt
  have h104 : (sp - 1856#64) + 104#64 = sp - 1752#64 := by bv_omega
  have h8 : (sp - 1856#64) + 8#64 = sp - 1848#64 := by bv_omega
  have h16 : (sp - 1856#64) + 16#64 = sp - 1840#64 := by bv_omega
  have h24 : (sp - 1856#64) + 24#64 = sp - 1832#64 := by bv_omega
  have h32 : (sp - 1856#64) + 32#64 = sp - 1824#64 := by bv_omega
  have h40 : (sp - 1856#64) + 40#64 = sp - 1816#64 := by bv_omega
  have h48 : (sp - 1856#64) + 48#64 = sp - 1808#64 := by bv_omega
  have h48_8 : (sp - 1808#64) + 8#64 = sp - 1800#64 := by bv_omega
  have h48_16 : (sp - 1808#64) + 16#64 = sp - 1792#64 := by bv_omega
  have h72 : (sp - 1856#64) + 72#64 = sp - 1784#64 := by bv_omega
  have h72_8 : (sp - 1784#64) + 8#64 = sp - 1776#64 := by bv_omega
  have h72_16 : (sp - 1784#64) + 16#64 = sp - 1768#64 := by bv_omega
  have h96 : (sp - 1856#64) + 96#64 = sp - 1760#64 := by bv_omega
  rw [h104, h48, h72, h96]
  have hauth := authenticatorPinAt_entails_authenticatorAt A g_auth (sp - 1856#64) uc.auth
  rw [authenticatorPinAt_eq_cells_heap A g_auth (sp - 1856#64) uc.auth, h8, h16, h24, h32, h40] at hauth
  have hdk := vecU8_of_cells_heap A (sp - 1808#64) cap_dk ptr_dk uc.dk
  rw [h48_8, h48_16] at hdk
  have hct1 := vecU8_of_cells_heap A (sp - 1784#64) cap_ct1 ptr_ct1 uc.ct1
  rw [h72_8, h72_16] at hct1
  have hgroup :
      ((sp - 1856#64) ↦₆₄ g_auth.rootKey.cap) ∗
        ((sp - 1848#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((sp - 1840#64) ↦₆₄ BitVec.ofNat 64 (uc.auth : Authenticator).rootKey.length) ∗
        ((sp - 1832#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((sp - 1824#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((sp - 1816#64) ↦₆₄ BitVec.ofNat 64 (uc.auth : Authenticator).macKey.length) ∗
        ((sp - 1808#64) ↦₆₄ cap_dk) ∗
        ((sp - 1800#64) ↦₆₄ ptr_dk) ∗
        ((sp - 1792#64) ↦₆₄ BitVec.ofNat 64 uc.dk.length) ∗
        ((sp - 1784#64) ↦₆₄ cap_ct1) ∗
        ((sp - 1776#64) ↦₆₄ ptr_ct1) ∗
        ((sp - 1768#64) ↦₆₄ BitVec.ofNat 64 uc.ct1.length) ∗
        ((sp - 1760#64) ↦₆₄ uc.epoch) ∗
        authenticatorHeapAt A g_auth uc.auth ∗
        vecU8HeapAt A cap_dk ptr_dk uc.dk ∗
        vecU8HeapAt A cap_ct1 ptr_ct1 uc.ct1 ∗
        polyDecoderAt A (sp - 1752#64) receivingCt2 =
      ((((sp - 1856#64) ↦₆₄ g_auth.rootKey.cap) ∗
          ((sp - 1848#64) ↦₆₄ g_auth.rootKey.ptr) ∗
          ((sp - 1840#64) ↦₆₄ BitVec.ofNat 64 (uc.auth : Authenticator).rootKey.length) ∗
          ((sp - 1832#64) ↦₆₄ g_auth.macKey.cap) ∗
          ((sp - 1824#64) ↦₆₄ g_auth.macKey.ptr) ∗
          ((sp - 1816#64) ↦₆₄ BitVec.ofNat 64 (uc.auth : Authenticator).macKey.length) ∗
          authenticatorHeapAt A g_auth uc.auth) ∗
        (((sp - 1808#64) ↦₆₄ cap_dk) ∗
          ((sp - 1800#64) ↦₆₄ ptr_dk) ∗
          ((sp - 1792#64) ↦₆₄ BitVec.ofNat 64 uc.dk.length) ∗
          vecU8HeapAt A cap_dk ptr_dk uc.dk) ∗
        (((sp - 1784#64) ↦₆₄ cap_ct1) ∗
          ((sp - 1776#64) ↦₆₄ ptr_ct1) ∗
          ((sp - 1768#64) ↦₆₄ BitVec.ofNat 64 uc.ct1.length) ∗
          vecU8HeapAt A cap_ct1 ptr_ct1 uc.ct1) ∗
        ((sp - 1760#64) ↦₆₄ uc.epoch)) ∗
      polyDecoderAt A (sp - 1752#64) receivingCt2 := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_left (sepConj_mono hauth (sepConj_mono hdk (sepConj_mono_left hct1)))

theorem optKeyBytesAt_none_entails_memRegion_24 (A : RustAlloc) (a : BitVec 64) :
    optKeyBytesAt A a none ⊢ memRegion a 24 := by
  unfold optKeyBytesAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion a noneCap)

theorem memRegion_128_cells (a : BitVec 64) :
    memRegion a 128 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
        ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ∗
        ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ∗
        ((a + 96#64) ↦₆₄ v12) ∗ ((a + 104#64) ↦₆₄ v13) ∗ ((a + 112#64) ↦₆₄ v14) ∗ ((a + 120#64) ↦₆₄ v15)) := by
  rw [ProofLib.memRegion_cells a 16 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem exists_unpack64_of_length_128 {bs : List (BitVec 8)} (h : bs.length = 128) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
          ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
          ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15) := by
  have h1 : (bs.take 64).length = 64 := by rw [List.length_take]; omega
  have h2 : (bs.drop 64).length = 64 := by rw [List.length_drop]; omega
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, ha1, _, _⟩ := exists_unpack64_of_length_64_split h1
  obtain ⟨w8, w9, w10, w11, w12, w13, w14, w15, ha2, _, _⟩ := exists_unpack64_of_length_64_split h2
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, fun a => ?_⟩
  conv_lhs => rw [← List.take_append_drop 64 bs, pointsToBytes_append, h1]
  rw [ha1 a, ha2 (a + BitVec.ofNat 64 64)]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## Fetch Macro, Postcondition Abbreviations, and `None` (`StillReceiving`) Branch -/

/-- Add instruction-fetch hypotheses for a byte range `[k0, k0 + len)` inside `0x59750`. -/
macro "recv_ct2_chunk_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode recvCt2ChunkBin $b $H recvCt2Chunk_fnOff 0x59834 $k0 $len)

abbrev recvCt2ChunkRoAt (img : Obj.Image) : SepProp :=
  ((img.base + bv% (ls_xref% 0x59a38 0x59a3c)) ↦ᵣ sckaKeyInfoPrefix) ∗
    ((img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964")) ↦ᵣ List.replicate 32 0#8) ∗
    ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)

abbrev recvCt2ChunkPostQ (img : Obj.Image) (K : MlKem) (F : ShaCompress) (A : RustAlloc)
    (x : RecvCt2ChunkGhost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (((img.base + bv% (ls_xref% 0x59a38 0x59a3c)) ↦ᵣ sckaKeyInfoPrefix) ∗
          ((img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964")) ↦ᵣ List.replicate 32 0#8) ∗
          ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
          (recvCt2ChunkSpec K F A img.base).post x s0 sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev recvCt2ChunkPostQp (K : MlKem) (F : ShaCompress) (A : RustAlloc) (b : BitVec 64)
    (x : RecvCt2ChunkGhost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (recvCt2ChunkSpec K F A b).onPanic x s0 sf ∗ R)

theorem SplitBytes.memcpy_withStack_inImage_ok {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) (hn : n < 2 ^ 64) (hookStack : Nat)
    (hmc : subroutine_ok prog entry ((withStack sessionMemcpyRegionSpec hookStack).inImage img)) :
    subroutine_ok prog entry ((withStack S.memcpySpec hookStack).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨dst, src⟩ R0 s_c hpc_c hrun_c hpre_c hsp_c => ?_
  dsimp only [Spec.inImage, withStack, SplitBytes.memcpySpec] at hpre_c
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_c
  rcases hpre_c with ⟨hinv_c, hpre_c⟩
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre_c
  rcases hpre_c with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (S.to_bytes src))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  rcases h2 with ⟨bs, h3⟩
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  rcases h3 with ⟨hlen, h4⟩
  have hpre_mc : s_c.mem ⊨ ((withStack sessionMemcpyRegionSpec hookStack).inImage img).pre (dst, src, bs) s_c ∗
      (S.heap bs ∗ R0) := by
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv_c, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]⟩, ?_⟩
    rw [hlen]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h4
  refine (hmc.to_outcome (dst, src, bs) (S.heap bs ∗ R0) s_c hpc_c hrun_c hpre_mc hsp_c).mono_outcome
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_sf, htr_sf⟩, hpost_mem⟩
    dsimp only [Spec.inImage, withStack, SplitBytes.memcpySpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr_sf, hx0_sf⟩, ?_⟩
    have harrange :
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt s_c.sp hookStack ∗ (S.heap bs ∗ R0) =
        (((dst ↦ₛ bs) ∗ S.heap bs) ∗ (src ↦ₛ bs)) ∗ stackAt s_c.sp hookStack ∗ R0 := by ac_rfl
    rw [harrange] at hpost_mem
    have hsrc_mr : (src ↦ₛ bs) ⊢ memRegion src n := hlen ▸ pointsToBytes_entails_memRegion src bs
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono (S.of_bytes dst bs hlen) hsrc_mr)) hpost_mem
  · right; left
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; left
    refine ⟨code, hex, ?_⟩
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; right
    refine ⟨hoom, ?_⟩
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro heq
  have h1 : (cap + 1#64).toNat = 0 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  omega

theorem ofNat_ult_128_of_lt {n : Nat} (h : n < 128) :
    (BitVec.ofNat 64 n).ult 128#64 = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by decide : 128 < 2 ^ 64), decide_eq_true_eq]
  exact h

theorem ofNat_ult_128_of_ge {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).ult 128#64 = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by decide : 128 < 2 ^ 64), decide_eq_false_iff_not]
  omega

theorem ofNat_sub_128_eq {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 63) :
    BitVec.ofNat 64 n - 128#64 = BitVec.ofNat 64 (n - 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : n - 128 < 2 ^ 64)]
  · rw [BitVec.le_def]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    exact hge

theorem ofNat_getLsbD_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow h

theorem ofNat_getElem_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false :=
  ofNat_getLsbD_63_false h

theorem optKeyBytesAt_some_expose (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    optKeyBytesAt A a (some bs) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ cap) ∗
        ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  dsimp only [optKeyBytesAt]
  refine Entails.trans (vecU8_expose_cells_heap A a bs) ?_
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hpull :
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8HeapAt A cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
    dsimp only [vecU8HeapAt]; ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hpure
  exact Entails.pure_right hpure (Entails.pure_right hpure (Entails.refl _))

theorem vecBufAt_zero_one (A : RustAlloc) (bs : List (BitVec 8)) (h0 : bs.length = 0) :
    emp ⊢ vecBufAt A 0#64 1#64 bs := by
  have hnil : bs = [] := List.eq_nil_of_length_eq_zero h0
  subst hnil
  have h0z : (0#64 : BitVec 64) = 0 := rfl
  dsimp only [vecBufAt]
  simp only [h0z, ↓reduceIte, pointsToBytes_nil, sepConj_emp]
  exact Entails.refl emp

theorem vecU8HeapAt_split_128 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hge : 128 ≤ bs.length) :
    vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
      (ptr ↦ₛ bs.take 128) ∗
      ((ptr + 128#64) ↦ₛ bs.drop 128) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 := by
  dsimp only [vecU8HeapAt]
  apply Entails.pure_left; rintro ⟨hle, hmax, hptr_ne⟩
  have hcap_ne : cap ≠ 0 := by
    intro h0; subst h0
    have hle0 : bs.length ≤ 0 := hle
    omega
  simp only [hcap_ne, ↓reduceIte]
  have htake_len : (bs.take 128).length = 128 := by rw [List.length_take]; omega
  have happ : bs.take 128 ++ bs.drop 128 = bs := List.take_append_drop 128 bs
  conv_lhs => arg 2; arg 1; rw [← happ, pointsToBytes_append, htake_len]
  refine Entails.pure_right ⟨hle, hmax, hptr_ne, hcap_ne⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem vecBufAt_of_bytes_live (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hne0 : bs.length ≠ 0) (hle : bs.length < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ A.live ptr bs.length 1 ⊢
      vecBufAt A (BitVec.ofNat 64 bs.length) ptr bs := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [htoNat] at h1
    change bs.length = 0 at h1
    omega
  dsimp only [vecBufAt]
  simp only [hcap_ne, ↓reduceIte, htoNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.refl _

def ct2DeallocAt (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  ⌜cap ≠ 0#64 ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    memRegion ptr cap.toNat ∗ A.live ptr cap.toNat 1

theorem ct2DeallocAt_of_cells_drop (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64)
    (hge : 128 ≤ bs.length) (hle : bs.length ≤ cap.toNat)
    (hmax : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    ((ptr ↦₆₄ w0) ∗ ((ptr + 8#64) ↦₆₄ w1) ∗
      ((ptr + 16#64) ↦₆₄ w2) ∗ ((ptr + 24#64) ↦₆₄ w3) ∗
      ((ptr + 32#64) ↦₆₄ w4) ∗ ((ptr + 40#64) ↦₆₄ w5) ∗
      ((ptr + 48#64) ↦₆₄ w6) ∗ ((ptr + 56#64) ↦₆₄ w7) ∗
      ((ptr + 64#64) ↦₆₄ w8) ∗ ((ptr + 72#64) ↦₆₄ w9) ∗
      ((ptr + 80#64) ↦₆₄ w10) ∗ ((ptr + 88#64) ↦₆₄ w11) ∗
      ((ptr + 96#64) ↦₆₄ w12) ∗ ((ptr + 104#64) ↦₆₄ w13) ∗
      ((ptr + 112#64) ↦₆₄ w14) ∗ ((ptr + 120#64) ↦₆₄ w15)) ∗
      ((ptr + 128#64) ↦ₛ bs.drop 128) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 ⊢
    ct2DeallocAt A cap ptr := by
  have h128 :
      ((ptr ↦₆₄ w0) ∗ ((ptr + 8#64) ↦₆₄ w1) ∗
        ((ptr + 16#64) ↦₆₄ w2) ∗ ((ptr + 24#64) ↦₆₄ w3) ∗
        ((ptr + 32#64) ↦₆₄ w4) ∗ ((ptr + 40#64) ↦₆₄ w5) ∗
        ((ptr + 48#64) ↦₆₄ w6) ∗ ((ptr + 56#64) ↦₆₄ w7) ∗
        ((ptr + 64#64) ↦₆₄ w8) ∗ ((ptr + 72#64) ↦₆₄ w9) ∗
        ((ptr + 80#64) ↦₆₄ w10) ∗ ((ptr + 88#64) ↦₆₄ w11) ∗
        ((ptr + 96#64) ↦₆₄ w12) ∗ ((ptr + 104#64) ↦₆₄ w13) ∗
        ((ptr + 112#64) ↦₆₄ w14) ∗ ((ptr + 120#64) ↦₆₄ w15)) ⊢
      memRegion ptr 128 := by
    rw [memRegion_128_cells ptr]
    exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
      (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5
        (Entails.sepExists_right w6 (Entails.sepExists_right w7 (Entails.sepExists_right w8
          (Entails.sepExists_right w9 (Entails.sepExists_right w10 (Entails.sepExists_right w11
            (Entails.sepExists_right w12 (Entails.sepExists_right w13 (Entails.sepExists_right w14
              (Entails.sepExists_right w15 (Entails.refl _))))))))))))))))
  have hdrop : ((ptr + 128#64) ↦ₛ bs.drop 128) ⊢ memRegion (ptr + 128#64) (bs.length - 128) := by
    have hlen : (bs.drop 128).length = bs.length - 128 := List.length_drop
    rw [← hlen]
    exact pointsToBytes_entails_memRegion (ptr + 128#64) (bs.drop 128)
  refine Entails.trans (sepConj_mono h128 (sepConj_mono_left hdrop)) ?_
  dsimp only [ct2DeallocAt]
  refine Entails.pure_right ⟨hcap, hmax, hptr⟩ ?_
  have hsplit1 : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) :=
    ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
      (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)
  have hsplit2 : memRegion ptr bs.length =
      memRegion ptr 128 ∗ memRegion (ptr + 128#64) (bs.length - 128) :=
    ProofLib.memRegion_split' (b := ptr) (n := 128) (k := bs.length - 128)
      (b' := ptr + 128#64) (by omega) rfl (by omega)
  rw [hsplit1, hsplit2]
  exact Entails.of_eq (by ac_rfl)

theorem cells9_fsp_split (fsp : BitVec 64) :
    cells fsp 9 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64,
        (fsp ↦₆₄ c0) ∗ ((fsp + 0x08#64) ↦₆₄ c1) ∗ ((fsp + 0x10#64) ↦₆₄ c2) ∗
        ((fsp + 0x18#64) ↦₆₄ c3) ∗ ((fsp + 0x20#64) ↦₆₄ c4) ∗ ((fsp + 0x28#64) ↦₆₄ c5) ∗
        ((fsp + 0x30#64) ↦₆₄ c6) ∗ ((fsp + 0x38#64) ↦₆₄ c7) ∗ ((fsp + 0x40#64) ↦₆₄ c8)) := by
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

/-! ## `Some(ct2Full)` Allocation and `decapsulate_compressed_key` (`0x5ed0c .. 0x5ee0c`) -/

theorem sub_128_eq_drop_length (bs : List (BitVec 8)) :
    bs.length - 128 = (bs.drop 128).length :=
  List.length_drop.symm

theorem sub_128_lt_max {n : Nat} (h : n ≤ 0x7fff_ffff_ffff_ffff) :
    n - 128 ≤ 0x7fff_ffff_ffff_ffff := by omega

theorem ofNat_sub_128_eq_zero_iff {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 (n - 128) == 0#64) = decide (n = 128) := by
  by_cases h : n = 128
  · subst h; decide
  · rw [decide_eq_false h]
    apply beq_false_of_ne
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    change n - 128 = 0 at h1
    omega

@[simp] theorem ofNat_128_eq : BitVec.ofNat 64 128 = 128#64 := rfl

@[simp, arm64_norm] theorem doReserve7_fnOff_eq :
    libsignalSessionCode.fnOff doReserve7Name = 0x4dca8 :=
  libsignalSessionCode_fnOff_0x4dca8

@[simp] theorem ofNat_32_eq : BitVec.ofNat 64 32 = 32#64 := rfl

@[simp] theorem ofNat_128_toNat : (128#64 : BitVec 64).toNat = 128 := rfl
@[simp] theorem ofNat_1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
@[simp] theorem ofNat_960_eq : BitVec.ofNat 64 960 = 960#64 := rfl
@[simp] theorem ofNat_2400_eq : BitVec.ofNat 64 2400 = 2400#64 := rfl
@[simp] theorem ofNat_400_eq : BitVec.ofNat 64 400 = 400#64 := rfl
@[simp] theorem ofNat_504_eq : BitVec.ofNat 64 504 = 504#64 := rfl

theorem shim_ok_at_recvCt2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (session2ShimSpecX.inImage img) :=
  shim_ok_at2_ext_x hA

theorem memcpy_ok_at_recvCt2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "memcpy"))
      (session2MemcpySpecX.inImage img) :=
  memcpy_ok_at2_ext_x hA

theorem alloc_ok_at_recvCt2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_alloc"))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  alloc_ok_at_norm_ext_x hA

theorem dealloc_ok_at_recvCt2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hA

theorem panic_at_handle_error_recvCt2 (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "alloc::raw_vec::handle_error")) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext recvCt2ChunkName
    (num% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "alloc::raw_vec::handle_error"))

theorem panic_at_assert_failed_u64_recvCt2 (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "core::panicking::assert_failed::<u64, u64>")) =
      some Rust.panicked :=
  panic_at_sym_ext b ext recvCt2ChunkName assertFailedU64Name
    (num% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "core::panicking::assert_failed::<u64, u64>"))
    (by simp only [arm64_norm]) (hp := by decide +kernel)

theorem panic_at_slice_index_fail_recvCt2 (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "core::slice::index::slice_index_fail")) =
      some Rust.panicked :=
  panic_at_sym_ext b ext recvCt2ChunkName sliceIndexFailName
    (num% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "core::slice::index::slice_index_fail"))
    (by simp only [arm64_norm]) (hp := by decide +kernel)

theorem panic_at_unwrap_failed_recvCt2 (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "core::result::unwrap_failed")) =
      some Rust.panicked :=
  panic_at_sym_ext b ext recvCt2ChunkName unwrapFailedName
    (num% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "core::result::unwrap_failed"))
    (by simp only [arm64_norm]) (hp := by decide +kernel)

theorem panic_at_bounds_check_recvCt2 (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "core::panicking::panic_bounds_check")) =
      some Rust.panicked :=
  panic_at_sym_ext b ext recvCt2ChunkName panicBoundsCheckName
    (num% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "core::panicking::panic_bounds_check"))
    (by simp only [arm64_norm]) (hp := by decide +kernel)

theorem panic_at_add_overflow_recvCt2 (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "core::panicking::panic_const::panic_const_add_overflow")) =
      some Rust.panicked :=
  panic_at_sym_ext b ext recvCt2ChunkName panicConstAddOverflowName
    (num% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "core::panicking::panic_const::panic_const_add_overflow"))
    (by simp only [arm64_norm]) (hp := by decide +kernel)

end Part1Helpers

section Part1bHelpers
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  recvCt2Chunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff mlkemDecaps_fnOff
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff doReserve7_fnOff_eq
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x67028
  libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x58ac4
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x46920
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5e5f0
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::result::unwrap_failed") (ls_hook% "core::result::unwrap_failed")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")

/-! ## Stack Frame & Heap Splitting Helpers for `Some(ct2Full)` -/

theorem ofNat_beq_960_iff {n : Nat} (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n == 960#64) = decide (n = 960) := by
  by_cases h : n = 960
  · subst h; decide
  · rw [decide_eq_false h]
    apply beq_false_of_ne
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    change n = 960 at h1
    exact h h1

theorem ofNat_beq_2400_iff {n : Nat} (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n == 2400#64) = decide (n = 2400) := by
  by_cases h : n = 2400
  · subst h; decide
  · rw [decide_eq_false h]
    apply beq_false_of_ne
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    change n = 2400 at h1
    exact h h1

theorem vecU8HeapAt_expose_nonempty (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
      (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 := by
  dsimp only [vecU8HeapAt]
  apply Entails.pure_left; rintro ⟨hle, hmax, hptr_ne⟩
  have hcap_ne : cap ≠ 0 := by
    intro h0; subst h0
    have hle0 : bs.length ≤ 0 := hle
    omega
  simp only [hcap_ne, ↓reduceIte]
  refine Entails.pure_right ⟨hle, hmax, hptr_ne, hcap_ne⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem vecU8HeapAt_pure_bounds (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      vecU8HeapAt A cap ptr bs := by
  dsimp only [vecU8HeapAt]
  apply Entails.pure_left; intro hp
  exact Entails.pure_right hp (Entails.pure_right hp (Entails.refl _))

def heapDeallocAt (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if cap = 0#64 then emp
  else ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗ memRegion ptr cap.toNat ∗ A.live ptr cap.toNat 1

theorem vecU8HeapAt_entails_heapDeallocAt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8HeapAt A cap ptr bs ⊢ heapDeallocAt A cap ptr := by
  dsimp only [vecU8HeapAt, heapDeallocAt]
  apply Entails.pure_left; rintro ⟨hle, hmax, hptr⟩
  by_cases hcap : cap = 0#64
  · subst hcap
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl emp
  · have hcap' : cap ≠ 0 := hcap
    simp only [hcap, hcap', ↓reduceIte]
    refine Entails.pure_right ⟨hmax, hptr⟩ ?_
    have h1 : (ptr ↦ₛ bs) ⊢ memRegion ptr bs.length := pointsToBytes_entails_memRegion ptr bs
    have hsplit : memRegion ptr cap.toNat =
        memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) :=
      ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)
    rw [hsplit]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left h1)) ?_
    exact Entails.of_eq (by ac_rfl)

theorem bytes_rem_entails_heapDeallocAt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hmax : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 ⊢
    heapDeallocAt A cap ptr := by
  dsimp only [heapDeallocAt]
  simp only [hcap, ↓reduceIte]
  refine Entails.pure_right ⟨hmax, hptr⟩ ?_
  have h1 : (ptr ↦ₛ bs) ⊢ memRegion ptr bs.length := pointsToBytes_entails_memRegion ptr bs
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) :=
    ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
      (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)
  rw [hsplit, sepConj_assoc]
  exact sepConj_mono_left h1

theorem memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5)) := by
  rw [ProofLib.memRegion_cells a 6 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2)) := by
  rw [ProofLib.memRegion_cells a 3 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem mlkem_decaps_ok_at_recvCt2 {img : Obj.Image} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdecaps : HookSat ext mlkemDecapsName (mlkemDecapsSpec K)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key"))
      ((mlkemDecapsSpec K).inImage img) := by
  apply Alloc.subroutine_ok_inImage img
  exact hook_ok_at (hname := "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
    recvCt2Chunk_fnOff (by fnoff_eq) (by decide)
    (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
    (by decide +kernel) hdecaps

theorem libcrux_hmac_ok_at_recvCt2 {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "libcrux_hmac::hmac"))
      ((libcruxHmacSpec F A).inImage img) :=
  Alloc.subroutine_ok_inImage img <|
    libcrux_hmac_ok_at_ext img.base F A ext hhmac recvCt2ChunkName
      (num% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "libcrux_hmac::hmac"))
      (by simp only [arm64_norm])

theorem sub_ok_at_recvCt2 {α : Type} {img : Obj.Image}
    {ext : String → Option (State → State)} {callee : String} {off : BitVec 64} {spec : Spec α}
    (hoff : BitVec.ofNat 64 (libsignalSessionCode.fnOff recvCt2ChunkName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff callee))
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr callee) spec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + off) spec := by
  have haddr :
      (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + off =
        (tripleRatchetProgAtExt img.base ext).fnAddr callee := by
    unfold tripleRatchetProgAtExt
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, BitVec.add_assoc, hoff]
  rwa [haddr]

theorem addChunk_ok_at_recvCt2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : AddChunkOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x67028 - 0x59834))
      ((addChunkSpecX A).inImage img) := by
  unfold AddChunkOkX at h
  exact sub_ok_at_recvCt2 (callee := addChunkName) (by rw [recvCt2Chunk_fnOff, addChunk_fnOff]; rfl) h

theorem polyDecodedMessage_ok_at_recvCt2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : PolyDecodedMessageOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x66788 - 0x59834))
      ((polyDecodedMessageSpec A img.base).inImage img) :=
  sub_ok_at_recvCt2 (callee := polyDecodedMessageName)
    (by rw [recvCt2Chunk_fnOff, polyDecodedMessage_fnOff]; rfl) h

theorem bytes_rem_entails_ct2DeallocAt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hmax : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 ⊢
    ct2DeallocAt A cap ptr := by
  dsimp only [ct2DeallocAt]
  refine Entails.pure_right ⟨hcap, hmax, hptr⟩ ?_
  have h1 : (ptr ↦ₛ bs) ⊢ memRegion ptr bs.length := pointsToBytes_entails_memRegion ptr bs
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) :=
    ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
      (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)
  rw [hsplit, sepConj_assoc]
  exact sepConj_mono_left h1

theorem someBranchFrameAt_expose_decaps (sp : BitVec 64) :
    someBranchFrameAt (sp - 2496#64) =
      memRegion (sp - 2000#64) 144 ∗
      memRegion (sp - 1344#64) 16 ∗
      memRegion (sp - 1328#64) 48 ∗
      memRegion (sp - 1280#64) 24 ∗
      memRegion (sp - 1248#64) 960 ∗
      memRegion (sp - 288#64) 128 ∗
      memRegion (sp - 152#64) 32 ∗
      unusedFrameAt (sp - 2496#64) := by
  unfold someBranchFrameAt
  have h1 : (sp - 2496#64) + 0x1f0#64 = sp - 2000#64 := by bv_omega
  have h2 : (sp - 2496#64) + 0x480#64 = sp - 1344#64 := by bv_omega
  have h3 : (sp - 2496#64) + 0x490#64 = sp - 1328#64 := by bv_omega
  have h4 : (sp - 2496#64) + 0x4c0#64 = sp - 1280#64 := by bv_omega
  have h5 : (sp - 2496#64) + 0x4e0#64 = sp - 1248#64 := by bv_omega
  have h6 : (sp - 2496#64) + 0x8a0#64 = sp - 288#64 := by bv_omega
  have h7 : (sp - 2496#64) + 0x928#64 = sp - 152#64 := by bv_omega
  rw [h1, h2, h3, h4, h5, h6, h7]

theorem authenticatorPinAt_of_sp_1328 (A : RustAlloc) (sp : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator) :
    ((sp - 1328#64) ↦₆₄ g.rootKey.cap) ∗
      ((sp - 1320#64) ↦₆₄ g.rootKey.ptr) ∗
      ((sp - 1312#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((sp - 1304#64) ↦₆₄ g.macKey.cap) ∗
      ((sp - 1296#64) ↦₆₄ g.macKey.ptr) ∗
      ((sp - 1288#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      authenticatorHeapAt A g auth ⊢
    authenticatorPinAt A g (sp - 1328#64) auth := by
  rw [authenticatorPinAt_eq_cells_heap A g (sp - 1328#64) auth]
  have h1 : (sp - 1328#64) + 8#64 = sp - 1320#64 := by bv_omega
  have h2 : (sp - 1328#64) + 16#64 = sp - 1312#64 := by bv_omega
  have h3 : (sp - 1328#64) + 24#64 = sp - 1304#64 := by bv_omega
  have h4 : (sp - 1328#64) + 32#64 = sp - 1296#64 := by bv_omega
  have h5 : (sp - 1328#64) + 40#64 = sp - 1288#64 := by bv_omega
  rw [h1, h2, h3, h4, h5]
  exact Entails.refl _

theorem vecU8At_of_sp_1280 (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hmax : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    ((sp - 1280#64) ↦₆₄ cap) ∗
      ((sp - 1272#64) ↦₆₄ ptr) ∗
      ((sp - 1264#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 ⊢
    vecU8At A (sp - 1280#64) cap ptr bs := by
  rw [vecU8At_eq_cells_heap A (sp - 1280#64) cap ptr bs]
  have h1 : (sp - 1280#64) + 8#64 = sp - 1272#64 := by bv_kernel
  have h2 : (sp - 1280#64) + 16#64 = sp - 1264#64 := by bv_kernel
  rw [h1, h2]
  have hheap :
      (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 ⊢
      vecU8HeapAt A cap ptr bs := by
    dsimp only [vecU8HeapAt]
    have hne : ¬ (cap = 0) := hcap
    simp only [hne, ↓reduceIte]
    exact Entails.pure_right ⟨hle, hmax, hptr⟩ (Entails.of_eq (by ac_rfl))
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hheap))

theorem pointsToBytes_128_of_sp_288 (sp : BitVec 64) (bs : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64)
    (ha : ∀ a : BitVec 64,
      (a ↦ₛ bs) =
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
        ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
        ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15)) :
    ((sp - 288#64) ↦₆₄ w0) ∗ ((sp - 280#64) ↦₆₄ w1) ∗ ((sp - 272#64) ↦₆₄ w2) ∗ ((sp - 264#64) ↦₆₄ w3) ∗
      ((sp - 256#64) ↦₆₄ w4) ∗ ((sp - 248#64) ↦₆₄ w5) ∗ ((sp - 240#64) ↦₆₄ w6) ∗ ((sp - 232#64) ↦₆₄ w7) ∗
      ((sp - 224#64) ↦₆₄ w8) ∗ ((sp - 216#64) ↦₆₄ w9) ∗ ((sp - 208#64) ↦₆₄ w10) ∗ ((sp - 200#64) ↦₆₄ w11) ∗
      ((sp - 192#64) ↦₆₄ w12) ∗ ((sp - 184#64) ↦₆₄ w13) ∗ ((sp - 176#64) ↦₆₄ w14) ∗ ((sp - 168#64) ↦₆₄ w15) ⊢
    ((sp - 288#64) ↦ₛ bs) := by
  rw [ha (sp - 288#64)]
  have h1 : (sp - 288#64) + 8#64 = sp - 280#64 := by bv_kernel
  have h2 : (sp - 288#64) + 16#64 = sp - 272#64 := by bv_kernel
  have h3 : (sp - 288#64) + 24#64 = sp - 264#64 := by bv_kernel
  have h4 : (sp - 288#64) + 32#64 = sp - 256#64 := by bv_kernel
  have h5 : (sp - 288#64) + 40#64 = sp - 248#64 := by bv_kernel
  have h6 : (sp - 288#64) + 48#64 = sp - 240#64 := by bv_kernel
  have h7 : (sp - 288#64) + 56#64 = sp - 232#64 := by bv_kernel
  have h8 : (sp - 288#64) + 64#64 = sp - 224#64 := by bv_kernel
  have h9 : (sp - 288#64) + 72#64 = sp - 216#64 := by bv_kernel
  have h10 : (sp - 288#64) + 80#64 = sp - 208#64 := by bv_kernel
  have h11 : (sp - 288#64) + 88#64 = sp - 200#64 := by bv_kernel
  have h12 : (sp - 288#64) + 96#64 = sp - 192#64 := by bv_kernel
  have h13 : (sp - 288#64) + 104#64 = sp - 184#64 := by bv_kernel
  have h14 : (sp - 288#64) + 112#64 = sp - 176#64 := by bv_kernel
  have h15 : (sp - 288#64) + 120#64 = sp - 168#64 := by bv_kernel
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  exact Entails.refl _

theorem memRegion_48_sp_1328 (sp : BitVec 64) :
    memRegion (sp - 1328#64) 48 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 1328#64) ↦₆₄ v0) ∗ ((sp - 1320#64) ↦₆₄ v1) ∗ ((sp - 1312#64) ↦₆₄ v2) ∗
        ((sp - 1304#64) ↦₆₄ v3) ∗ ((sp - 1296#64) ↦₆₄ v4) ∗ ((sp - 1288#64) ↦₆₄ v5)) := by
  rw [memRegion_48_cells (sp - 1328#64)]
  simp only [wp_norm, arm64_norm]

theorem memRegion_24_sp_1280 (sp : BitVec 64) :
    memRegion (sp - 1280#64) 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ((sp - 1280#64) ↦₆₄ v0) ∗ ((sp - 1272#64) ↦₆₄ v1) ∗ ((sp - 1264#64) ↦₆₄ v2)) := by
  rw [memRegion_24_cells (sp - 1280#64)]
  simp only [wp_norm, arm64_norm]

theorem memRegion_128_sp_288 (sp : BitVec 64) :
    memRegion (sp - 288#64) 128 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        ((sp - 288#64) ↦₆₄ v0) ∗ ((sp - 280#64) ↦₆₄ v1) ∗ ((sp - 272#64) ↦₆₄ v2) ∗ ((sp - 264#64) ↦₆₄ v3) ∗
        ((sp - 256#64) ↦₆₄ v4) ∗ ((sp - 248#64) ↦₆₄ v5) ∗ ((sp - 240#64) ↦₆₄ v6) ∗ ((sp - 232#64) ↦₆₄ v7) ∗
        ((sp - 224#64) ↦₆₄ v8) ∗ ((sp - 216#64) ↦₆₄ v9) ∗ ((sp - 208#64) ↦₆₄ v10) ∗ ((sp - 200#64) ↦₆₄ v11) ∗
        ((sp - 192#64) ↦₆₄ v12) ∗ ((sp - 184#64) ↦₆₄ v13) ∗ ((sp - 176#64) ↦₆₄ v14) ∗ ((sp - 168#64) ↦₆₄ v15)) := by
  rw [memRegion_128_cells (sp - 288#64)]
  simp only [wp_norm, arm64_norm]

end Part1bHelpers

section Part1cHelpers
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  recvCt2Chunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff mlkemDecaps_fnOff
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff doReserve7_fnOff_eq
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x67028
  libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x58ac4
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x46920
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5e5f0
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::result::unwrap_failed") (ls_hook% "core::result::unwrap_failed")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")

theorem savedRegsAt_of_cells12 (s0 : State) :
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
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢ savedRegsAt s0 :=
  Entails.refl _

theorem cells12_sp_96_expand (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64, ∃∗ r3 : BitVec 64,
       ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r6 : BitVec 64, ∃∗ r7 : BitVec 64,
       ∃∗ r8 : BitVec 64, ∃∗ r9 : BitVec 64, ∃∗ r10 : BitVec 64, ∃∗ r11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ r0) ∗ ((sp - 88#64) ↦₆₄ r1) ∗
        ((sp - 80#64) ↦₆₄ r2) ∗ ((sp - 72#64) ↦₆₄ r3) ∗
        ((sp - 64#64) ↦₆₄ r4) ∗ ((sp - 56#64) ↦₆₄ r5) ∗
        ((sp - 48#64) ↦₆₄ r6) ∗ ((sp - 40#64) ↦₆₄ r7) ∗
        ((sp - 32#64) ↦₆₄ r8) ∗ ((sp - 24#64) ↦₆₄ r9) ∗
        ((sp - 16#64) ↦₆₄ r10) ∗ ((sp - 8#64) ↦₆₄ r11)) := by
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    emp_sepConj, sepConj_emp, wp_norm, arm64_norm]

theorem cells9_sp_2496_expand (sp : BitVec 64) :
    cells (sp - 2496#64) 9 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64,
        ((sp - 2496#64) ↦₆₄ c0) ∗ ((sp - 2488#64) ↦₆₄ c1) ∗
        ((sp - 2480#64) ↦₆₄ c2) ∗ ((sp - 2472#64) ↦₆₄ c3) ∗
        ((sp - 2464#64) ↦₆₄ c4) ∗ ((sp - 2456#64) ↦₆₄ c5) ∗
        ((sp - 2448#64) ↦₆₄ c6) ∗ ((sp - 2440#64) ↦₆₄ c7) ∗
        ((sp - 2432#64) ↦₆₄ c8)) := by
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    emp_sepConj, sepConj_emp, wp_norm, arm64_norm]

theorem cells9_sp_2496_fold (sp c0 c1 c2 c3 c4 c5 c6 c7 c8 : BitVec 64) :
    ((sp - 2496#64) ↦₆₄ c0) ∗ ((sp - 2488#64) ↦₆₄ c1) ∗
      ((sp - 2480#64) ↦₆₄ c2) ∗ ((sp - 2472#64) ↦₆₄ c3) ∗
      ((sp - 2464#64) ↦₆₄ c4) ∗ ((sp - 2456#64) ↦₆₄ c5) ∗
      ((sp - 2448#64) ↦₆₄ c6) ∗ ((sp - 2440#64) ↦₆₄ c7) ∗
      ((sp - 2432#64) ↦₆₄ c8) ⊢ cells (sp - 2496#64) 9 := by
  rw [cells9_sp_2496_expand sp]
  exact Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
      (Entails.sepExists_right c6 (Entails.sepExists_right c7
        (Entails.sepExists_right c8 (Entails.refl _)))))))))

theorem optKeyBytesAt_none_sp_2024 (A : RustAlloc) (sp : BitVec 64) :
    optKeyBytesAt A (sp - 2024#64) none =
      ((sp - 2024#64) ↦₆₄ noneCap) ∗ memRegion (sp - 2016#64) 16 := by
  unfold optKeyBytesAt
  have h2 : (sp - 2024#64) + 8#64 = sp - 2016#64 := by bv_omega
  rw [h2]

theorem optKeyBytesAt_some_sp_2024 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    optKeyBytesAt A (sp - 2024#64) (some bs) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 2024#64) ↦₆₄ cap) ∗
        ((sp - 2016#64) ↦₆₄ ptr) ∗
        ((sp - 2008#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  have h2 : (sp - 2024#64) + 8#64 = sp - 2016#64 := by bv_omega
  have h3 : (sp - 2024#64) + 16#64 = sp - 2008#64 := by bv_omega
  have hexp := optKeyBytesAt_some_expose A (sp - 2024#64) bs
  rw [h2, h3] at hexp
  exact hexp

theorem memRegion_24_of_sp_2024 (sp v0 v1 v2 : BitVec 64) :
    ((sp - 2024#64) ↦₆₄ v0) ∗ ((sp - 2016#64) ↦₆₄ v1) ∗ ((sp - 2008#64) ↦₆₄ v2) ⊢
      memRegion (sp - 2024#64) 24 := by
  have h2 : (sp - 2024#64) + 8#64 = sp - 2016#64 := by bv_omega
  have h3 : (sp - 2024#64) + 16#64 = sp - 2008#64 := by bv_omega
  rw [memRegion_24_cells (sp - 2024#64), h2, h3]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.refl _)))

theorem fold_none_addrs_sp (A : RustAlloc) (sp : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A (sp - 2424#64) dec ∗
      ((sp - 2024#64) ↦₆₄ noneCap) ∗ memRegion (sp - 2016#64) 16 ∗
      memRegion (sp - 1856#64) 504 ⊢
    polyDecoderAt A ((sp - 2496#64) + 0x48#64) dec ∗
      optKeyBytesAt A ((sp - 2496#64) + 0x1d8#64) none ∗
      memRegion ((sp - 2496#64) + 0x280#64) 504 := by
  dsimp only [optKeyBytesAt]
  have h1 : (sp - 2496#64) + 0x48#64 = sp - 2424#64 := by bv_omega
  have h2 : (sp - 2496#64) + 0x1d8#64 = sp - 2024#64 := by bv_omega
  have h3 : (sp - 2024#64) + 8#64 = sp - 2016#64 := by bv_omega
  have h4 : (sp - 2496#64) + 0x280#64 = sp - 1856#64 := by bv_omega
  rw [h1, h2, h3, h4]
  exact Entails.of_eq (by ac_rfl)

theorem SepWPp.frame_call {prog : Program} {ret : BitVec 64} {s : State}
    {P F_frame P' : SepProp} {Q Qp : State → SepProp → Prop}
    (T : SepProp)
    (hf : P = T ∗ F_frame)
    (heq : T ∗ F_frame = P')
    (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hf, heq]
  exact h

theorem addWithCarry64_sub_128_n (a : BitVec 64) :
    (AddWithCarry64 a 18446744073709551487#64 true).2.n = (a - 128#64).getLsbD 63 := by
  dsimp [AddWithCarry64]
  have htrunc :
      BitVec.setWidth 64 (1#65 + (18446744073709551487#65 + BitVec.setWidth 65 a)) =
        a - 128#64 := by
    bv_kernel
  rw [htrunc, BitVec.msb_eq_getLsbD_last]

end Part1cHelpers

section Part2Helpers
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  spqrHkdfWith Authenticator.update Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length replicate_32_zero_length
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  recvCt2Chunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff mlkemDecaps_fnOff
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff doReserve7_fnOff_eq
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x67028
  libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x58ac4
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x46920
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5e5f0
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::result::unwrap_failed") (ls_hook% "core::result::unwrap_failed")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")

theorem allocZeroed_ok_at_recvCt2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : AllocZeroedWithStackOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_alloc_zeroed"))
      ((rustAllocZeroedSpecWithStack A extHookStack).inImage img) :=
  sub_ok_at_recvCt2 (callee := allocZeroedName)
    (by rw [recvCt2Chunk_fnOff, allocZeroed_fnOff]; rfl) h

theorem sliceConcat2_ok_at_recvCt2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : SliceConcat2OkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x5eab8 - 0x59834))
      ((sliceConcat2Spec A).inImage img) :=
  sub_ok_at_recvCt2 (callee := sliceConcatName)
    (by rw [recvCt2Chunk_fnOff, sliceConcat_fnOff]; rfl) h

theorem sliceConcat3_ok_at_recvCt2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : SliceConcat3OkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x5eab8 - 0x59834))
      ((sliceConcat3Spec A).inImage img) :=
  sub_ok_at_recvCt2 (callee := sliceConcatName)
    (by rw [recvCt2Chunk_fnOff, sliceConcat_fnOff]; rfl) h

theorem hkdfToSlice_ok_at_recvCt2 {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} (h : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x5de8c - 0x59834))
      ((hkdfToSliceSpqrSpec (spqrHkdfWith F)).inImage img) :=
  sub_ok_at_recvCt2 (callee := Kdf.hkdfToSliceName)
    (by rw [recvCt2Chunk_fnOff, hkdfToSlice_fnOff]; rfl) h

theorem authUpdate_ok_at_recvCt2 {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : AuthUpdateOkX img F A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + (0x58ac4#64 - 0x59834#64))
      ((authUpdateSpec F A).inImage img) :=
  sub_ok_at_recvCt2 (callee := authUpdateName)
    (by rw [recvCt2Chunk_fnOff, authUpdate_fnOff]; rfl) h

theorem isNonZero_ok_at_recvCt2 (img : Obj.Image) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x5e5f0 - 0x59834))
      (isNonZeroSpec.inImage img) :=
  sub_ok_at_recvCt2 (callee := isNonZeroName)
    (by rw [recvCt2Chunk_fnOff, gf16IsNonZero_fnOff]; rfl)
    (Alloc.subroutine_ok_inImage img (isNonZero_ok img.base ext))

/-! ## Callee Contract Wrappers & Segment 2a (`0x5ee0c .. 0x5eec4`) -/

theorem pointsToBytes_replicate_32_entails_memRegion (p : BitVec 64) :
    (p ↦ₛ List.replicate 32 (0#8 : BitVec 8)) ⊢ memRegion p 32 := by
  have hlen : (List.replicate 32 (0#8 : BitVec 8)).length = 32 := by decide
  exact hlen ▸ pointsToBytes_entails_memRegion p (List.replicate 32 0#8)

theorem stackAt_extHook_eq_authUpdate (sp : BitVec 64) :
    memRegion (sp - 19552#64) 672 ∗ stackAt (sp - 2496#64) extHookStack =
      memRegion (sp - 19552#64) 512 ∗ stackAt (sp - 2496#64) authUpdateStackX := by
  have h1 := stackAt_polyDecodedMessage_eq_extHook (sp - 2496#64)
  have h2 := stackAt_polyDecodedMessage_eq_authUpdate (sp - 2496#64)
  have hsub : sp - 2496#64 - 17056#64 = sp - 19552#64 := by bv_kernel
  rw [hsub] at h1 h2
  exact h1.symm.trans h2

theorem stackAt_extHook_eq_doReserve (sp : BitVec 64) :
    memRegion (sp - 19552#64) 672 ∗ stackAt (sp - 2496#64) extHookStack =
      memRegion (sp - 19552#64) 12848 ∗ stackAt (sp - 2496#64) doReserveStack := by
  have h1 := stackAt_polyDecodedMessage_eq_extHook (sp - 2496#64)
  have h2 := stackAt_polyDecodedMessage_eq_doReserve (sp - 2496#64)
  have hsub : sp - 2496#64 - 17056#64 = sp - 19552#64 := by bv_kernel
  rw [hsub] at h1 h2
  exact h1.symm.trans h2

theorem memRegion_128_split_8_120 (sp : BitVec 64) :
    memRegion (sp - 288#64) 128 =
      (∃∗ v0 : BitVec 64, ((sp - 288#64) ↦₆₄ v0)) ∗ memRegion (sp - 280#64) 120 := by
  rw [ProofLib.memRegion_split' (b := sp - 288#64) (n := 8) (k := 120)
        (b' := sp - 280#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 288#64)]

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) := by
  rw [ProofLib.memRegion_cells a 4 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem memRegion_960_split_32_928 (sp : BitVec 64) :
    memRegion (sp - 1248#64) 960 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 1248#64) ↦₆₄ v0) ∗ ((sp - 1240#64) ↦₆₄ v1) ∗
        ((sp - 1232#64) ↦₆₄ v2) ∗ ((sp - 1224#64) ↦₆₄ v3)) ∗
      memRegion (sp - 1216#64) 928 := by
  have h1 : (sp - 1248#64) + 8#64 = sp - 1240#64 := by bv_omega
  have h2 : (sp - 1248#64) + 16#64 = sp - 1232#64 := by bv_omega
  have h3 : (sp - 1248#64) + 24#64 = sp - 1224#64 := by bv_omega
  rw [ProofLib.memRegion_split' (b := sp - 1248#64) (n := 32) (k := 928)
        (b' := sp - 1216#64) rfl (by bv_omega) (by decide),
      memRegion_32_cells (sp - 1248#64), h1, h2, h3]

theorem fold_sp_152_24_8 (sp : BitVec 64) (u0 u1 u2 u3 : BitVec 64) :
    ((sp - 152#64) ↦₆₄ u0) ∗ ((sp - 144#64) ↦₆₄ u1) ∗
      ((sp - 136#64) ↦₆₄ u2) ∗ ((sp - 128#64) ↦₆₄ u3) ⊢
      memRegion (sp - 152#64) 24 ∗ memRegion (sp - 128#64) 8 := by
  have h1 : (sp - 152#64) + 8#64 = sp - 144#64 := by bv_omega
  have h2 : (sp - 152#64) + 16#64 = sp - 136#64 := by bv_omega
  have h24 : ((sp - 152#64) ↦₆₄ u0) ∗ ((sp - 144#64) ↦₆₄ u1) ∗ ((sp - 136#64) ↦₆₄ u2) ⊢
      memRegion (sp - 152#64) 24 := by
    rw [memRegion_24_cells (sp - 152#64), h1, h2]
    exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2 (Entails.refl _)))
  have h8 : ((sp - 128#64) ↦₆₄ u3) ⊢ memRegion (sp - 128#64) 8 := by
    rw [ProofLib.memRegion_eight (sp - 128#64)]
    exact Entails.sepExists_right u3 (Entails.refl _)
  have hassoc :
      ((sp - 152#64) ↦₆₄ u0) ∗ ((sp - 144#64) ↦₆₄ u1) ∗
        ((sp - 136#64) ↦₆₄ u2) ∗ ((sp - 128#64) ↦₆₄ u3) =
      (((sp - 152#64) ↦₆₄ u0) ∗ ((sp - 144#64) ↦₆₄ u1) ∗ ((sp - 136#64) ↦₆₄ u2)) ∗
        ((sp - 128#64) ↦₆₄ u3) := by ac_rfl
  rw [hassoc]
  exact sepConj_mono h24 h8

theorem page_align_mask {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    b &&& 18446744073709547520#64 = b := by
  have hb : (b &&& 18446744073709547520#64) + (b &&& 4095#64) = b := by bv_kernel
  rw [halign, BitVec.add_zero] at hb
  exact hb

theorem adrp_sckaKeyInfoPrefix {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    ((b + 0x59834#64) + 516#64 &&& 18446744073709547520#64) + bv% (ls_xref% 0x59a38 0x59a3c - 0x59000) =
      b + bv% (ls_xref% 0x59a38 0x59a3c) := by
  rw [← page_align_mask halign]; bv_kernel

theorem sckaKeyInfo_length (ep : Epoch) :
    (sckaKeyInfoPrefix ++ toBEBytes 8 ep).length = 41 := by
  simp [sckaKeyInfoPrefix, asciiBytes]

theorem adrp_zero32 {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    ((b + 0x59834#64) + 600#64 &&& 18446744073709547520#64) + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" - 0x59000) =
      b + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964") := by
  rw [← page_align_mask halign]; bv_kernel

theorem adrp_ctLabel {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    ((b + 0x59834#64) + 756#64 &&& 18446744073709547520#64) + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext" - 0x59000) =
      b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext") := by
  rw [← page_align_mask halign]; bv_kernel

@[simp, arm64_norm, wp_norm, arm64_norm ↓, wp_norm ↓]
theorem sckaKeyInfoPrefix_length : sckaKeyInfoPrefix.length = 33 := rfl

@[simp, arm64_norm, wp_norm, arm64_norm ↓, wp_norm ↓]
theorem ctLabel_length : Authenticator.ctLabel.length = 35 := rfl

theorem fold_ptr_ss_raw (ptr : BitVec 64) (bs : List (BitVec 8))
    (u0 u1 u2 u3 : BitVec 64)
    (ha : ∀ a : BitVec 64,
      (a ↦ₛ bs) = (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3)) :
    (ptr ↦₆₄ u0) ∗ ((ptr + 8#64) ↦₆₄ u1) ∗ ((ptr + 16#64) ↦₆₄ u2) ∗ ((ptr + 24#64) ↦₆₄ u3) ⊢
      (ptr ↦ₛ bs) :=
  Entails.of_eq (ha ptr).symm

theorem rejoin_memRegion_128_8_120 (sp : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length = 8) :
    ((sp - 288#64) ↦ₛ bs) ∗ memRegion (sp - 280#64) 120 ⊢
      memRegion (sp - 288#64) 128 := by
  have h1 : ((sp - 288#64) ↦ₛ bs) ⊢ memRegion (sp - 288#64) 8 :=
    hlen ▸ pointsToBytes_entails_memRegion (sp - 288#64) bs
  rw [ProofLib.memRegion_split' (b := sp - 288#64) (n := 8) (k := 120)
        (b' := sp - 280#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left h1

theorem rejoin_memRegion_960_32_928 (sp : BitVec 64) (v0 v1 v2 v3 : BitVec 64) :
    ((sp - 1248#64) ↦₆₄ v0) ∗ ((sp - 1240#64) ↦₆₄ v1) ∗
      ((sp - 1232#64) ↦₆₄ v2) ∗ ((sp - 1224#64) ↦₆₄ v3) ∗
      memRegion (sp - 1216#64) 928 ⊢
      memRegion (sp - 1248#64) 960 := by
  have hassoc :
      ((sp - 1248#64) ↦₆₄ v0) ∗ ((sp - 1240#64) ↦₆₄ v1) ∗
        ((sp - 1232#64) ↦₆₄ v2) ∗ ((sp - 1224#64) ↦₆₄ v3) ∗
        memRegion (sp - 1216#64) 928 =
      (((sp - 1248#64) ↦₆₄ v0) ∗ ((sp - 1240#64) ↦₆₄ v1) ∗
        ((sp - 1232#64) ↦₆₄ v2) ∗ ((sp - 1224#64) ↦₆₄ v3)) ∗
        memRegion (sp - 1216#64) 928 := by ac_rfl
  rw [memRegion_960_split_32_928 sp, hassoc]
  exact sepConj_mono_left
    (Entails.sepExists_right v0
      (Entails.sepExists_right v1
        (Entails.sepExists_right v2
          (Entails.sepExists_right v3 (Entails.refl _)))))

theorem vecU8_expose_nonempty_152 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8 A (sp - 152#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap ≠ 0#64 ∧ LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧ bs.length ≤ cap.toNat⌝ ∗
          ((sp - 152#64) ↦₆₄ cap) ∗
          ((sp - 144#64) ↦₆₄ ptr) ∗
          ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live ptr cap.toNat 1 ∗
          (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
  dsimp only [vecU8]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A (sp - 152#64) cap ptr bs]
  have h8 : (sp - 152#64) + 8#64 = sp - 144#64 := by bv_omega
  have h16 : (sp - 152#64) + 16#64 = sp - 136#64 := by bv_omega
  rw [h8, h16]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_nonempty A cap ptr bs hpos)))) ?_
  have hcomm :
      ((sp - 152#64) ↦₆₄ cap) ∗ ((sp - 144#64) ↦₆₄ ptr) ∗
        ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
          (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 152#64) ↦₆₄ cap) ∗ ((sp - 144#64) ↦₆₄ ptr) ∗
        ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun ⟨hle, hmax, hptr, hcap⟩ => ?_
  have hpos_cap : 0 < cap.toNat := by
    have : cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos_cap, ⟨0, rfl⟩, by omega⟩
  exact Entails.pure_right ⟨hcap, hlay, hptr, hle⟩ (Entails.refl _)

end Part2Helpers

section Part2bHelpers
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  spqrHkdfWith Authenticator.update Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length replicate_32_zero_length ctLabel_length
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  recvCt2Chunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff mlkemDecaps_fnOff
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff doReserve7_fnOff_eq
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x67028
  libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x58ac4
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x46920
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5e5f0
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::result::unwrap_failed") (ls_hook% "core::result::unwrap_failed")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")

/-! ## Callee Wrappers and Stack/Memory Helpers for Segment 2b (`0x5eec4..0x5ef88`) -/

def DoReserve7OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name)
    ((doReserveSpecX A).inImage img)

theorem doReserve7_ok_at_recvCt2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : DoReserve7OkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + (0x4dca8#64 - 0x59834#64))
      ((doReserveSpecX A).inImage img) :=
  sub_ok_at_recvCt2 (callee := doReserve7Name)
    (by rw [recvCt2Chunk_fnOff, doReserve7_fnOff_eq]; rfl) h

/-- Specialized `libcrux_hmac::hmac` contract when `key.length < 2^32` and `data.length < 2^32`
are already known at the call site, reducing `onPanic` to `allocFailedIn`. -/
def libcruxHmacSafeSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec LibcruxHmacCall where
  pre x s :=
    ⌜s.readReg64 .x8 = x.ret ∧ (s.readReg64 .x0).setWidth 32 = 0#32 ∧
      s.readReg64 .x1 = x.keyA ∧ (s.readReg64 .x2).toNat = x.key.length ∧
      s.readReg64 .x3 = x.dataA ∧ (s.readReg64 .x4).toNat = x.data.length ∧
      (s.readReg64 .x5).setWidth 32 = 1#32 ∧ s.readReg64 .x6 = 32#64 ∧
      x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp extHookStack
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      vecU8 A x.ret (hmacWith F x.key x.data) ∗ A.pool ∗ stackAt s0.sp extHookStack
  onPanic _ s0 sf :=
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem libcrux_hmac_safe_ok_at_recvCt2 {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "libcrux_hmac::hmac"))
      ((libcruxHmacSafeSpec F A).inImage img) := by
  have hraw := libcrux_hmac_ok_at_recvCt2 (img := img) hhmac
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, libcruxHmacSafeSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hk_lt, hd_lt⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((libcruxHmacSpec F A).inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, libcruxHmacSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hmem⟩
  refine (hraw.to_outcome x R s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, libcruxHmacSpec, libcruxHmacSafeSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.2.2, hpost.2⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, libcruxHmacSpec, libcruxHmacSafeSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨haf | hk_ge | hd_ge, hpref⟩, hmem'⟩
    · exact ⟨⟨haf, hpref⟩, hmem'⟩
    · omega
    · omega
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

theorem stackAt_extHook_eq_doReserveX (sp : BitVec 64) :
    memRegion (sp - 19552#64) 672 ∗ stackAt (sp - 2496#64) extHookStack =
      memRegion (sp - 19552#64) 560 ∗ stackAt (sp - 2496#64) doReserveStackX := by
  have heq : extHookStack + 112 = doReserveStackX := by decide
  have hbv : BitVec.ofNat 64 (extHookStack + 112) = 16496#64 := by decide
  have hsplit := stackAt_split_bottom (sp - 2496#64) extHookStack 112 (by decide)
  rw [heq, hbv] at hsplit
  have h2 : (sp - 2496#64) - 16496#64 = sp - 18992#64 := by bv_omega
  rw [h2] at hsplit
  rw [hsplit,
    ProofLib.memRegion_split' (b := sp - 19552#64) (n := 560) (k := 112)
      (b' := sp - 18992#64) rfl (by bv_omega) (by decide),
    sepConj_assoc]

theorem memRegion_128_split_24_104 (sp : BitVec 64) :
    memRegion (sp - 288#64) 128 =
      memRegion (sp - 288#64) 24 ∗ memRegion (sp - 264#64) 104 := by
  rw [ProofLib.memRegion_split' (b := sp - 288#64) (n := 24) (k := 104)
        (b' := sp - 264#64) rfl (by bv_omega) (by decide)]

theorem memRegion_960_split_48_912 (sp : BitVec 64) :
    memRegion (sp - 1248#64) 960 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 1248#64) ↦₆₄ v0) ∗ ((sp - 1240#64) ↦₆₄ v1) ∗
        ((sp - 1232#64) ↦₆₄ v2) ∗ ((sp - 1224#64) ↦₆₄ v3) ∗
        ((sp - 1216#64) ↦₆₄ v4) ∗ ((sp - 1208#64) ↦₆₄ v5)) ∗
      memRegion (sp - 1200#64) 912 := by
  have h1 : (sp - 1248#64) + 8#64 = sp - 1240#64 := by bv_omega
  have h2 : (sp - 1248#64) + 16#64 = sp - 1232#64 := by bv_omega
  have h3 : (sp - 1248#64) + 24#64 = sp - 1224#64 := by bv_omega
  have h4 : (sp - 1248#64) + 32#64 = sp - 1216#64 := by bv_omega
  have h5 : (sp - 1248#64) + 40#64 = sp - 1208#64 := by bv_omega
  rw [ProofLib.memRegion_split' (b := sp - 1248#64) (n := 48) (k := 912)
        (b' := sp - 1200#64) rfl (by bv_omega) (by decide),
      memRegion_48_cells (sp - 1248#64), h1, h2, h3, h4, h5]

theorem fold_sp_1248_24_24 (sp : BitVec 64) (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((sp - 1248#64) ↦₆₄ v0) ∗ ((sp - 1240#64) ↦₆₄ v1) ∗
      ((sp - 1232#64) ↦₆₄ v2) ∗ ((sp - 1224#64) ↦₆₄ v3) ∗
      ((sp - 1216#64) ↦₆₄ v4) ∗ ((sp - 1208#64) ↦₆₄ v5) ⊢
      memRegion (sp - 1248#64) 24 ∗ memRegion (sp - 1224#64) 24 := by
  have h1 : (sp - 1248#64) + 8#64 = sp - 1240#64 := by bv_omega
  have h2 : (sp - 1248#64) + 16#64 = sp - 1232#64 := by bv_omega
  have h3 : (sp - 1224#64) + 8#64 = sp - 1216#64 := by bv_omega
  have h4 : (sp - 1224#64) + 16#64 = sp - 1208#64 := by bv_omega
  have ha :
      ((sp - 1248#64) ↦₆₄ v0) ∗ ((sp - 1240#64) ↦₆₄ v1) ∗ ((sp - 1232#64) ↦₆₄ v2) ⊢
        memRegion (sp - 1248#64) 24 := by
    rw [memRegion_24_cells (sp - 1248#64), h1, h2]
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2 (Entails.refl _)))
  have hb :
      ((sp - 1224#64) ↦₆₄ v3) ∗ ((sp - 1216#64) ↦₆₄ v4) ∗ ((sp - 1208#64) ↦₆₄ v5) ⊢
        memRegion (sp - 1224#64) 24 := by
    rw [memRegion_24_cells (sp - 1224#64), h3, h4]
    exact Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5 (Entails.refl _)))
  have hassoc :
      ((sp - 1248#64) ↦₆₄ v0) ∗ ((sp - 1240#64) ↦₆₄ v1) ∗
        ((sp - 1232#64) ↦₆₄ v2) ∗ ((sp - 1224#64) ↦₆₄ v3) ∗
        ((sp - 1216#64) ↦₆₄ v4) ∗ ((sp - 1208#64) ↦₆₄ v5) =
      (((sp - 1248#64) ↦₆₄ v0) ∗ ((sp - 1240#64) ↦₆₄ v1) ∗ ((sp - 1232#64) ↦₆₄ v2)) ∗
        (((sp - 1224#64) ↦₆₄ v3) ∗ ((sp - 1216#64) ↦₆₄ v4) ∗ ((sp - 1208#64) ↦₆₄ v5)) := by ac_rfl
  rw [hassoc]
  exact sepConj_mono ha hb

theorem rejoin_memRegion_128_24_104 (sp : BitVec 64) (u0 u1 u2 : BitVec 64) :
    ((sp - 288#64) ↦₆₄ u0) ∗ ((sp - 280#64) ↦₆₄ u1) ∗ ((sp - 272#64) ↦₆₄ u2) ∗
      memRegion (sp - 264#64) 104 ⊢
      memRegion (sp - 288#64) 128 := by
  have h1 : (sp - 288#64) + 8#64 = sp - 280#64 := by bv_omega
  have h2 : (sp - 288#64) + 16#64 = sp - 272#64 := by bv_omega
  have h24 :
      ((sp - 288#64) ↦₆₄ u0) ∗ ((sp - 280#64) ↦₆₄ u1) ∗ ((sp - 272#64) ↦₆₄ u2) ⊢
        memRegion (sp - 288#64) 24 := by
    rw [memRegion_24_cells (sp - 288#64), h1, h2]
    exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2 (Entails.refl _)))
  rw [memRegion_128_split_24_104 sp]
  have hassoc :
      ((sp - 288#64) ↦₆₄ u0) ∗ ((sp - 280#64) ↦₆₄ u1) ∗ ((sp - 272#64) ↦₆₄ u2) ∗
        memRegion (sp - 264#64) 104 =
      (((sp - 288#64) ↦₆₄ u0) ∗ ((sp - 280#64) ↦₆₄ u1) ∗ ((sp - 272#64) ↦₆₄ u2)) ∗
        memRegion (sp - 264#64) 104 := by ac_rfl
  rw [hassoc]
  exact sepConj_mono_left h24

theorem memRegion_144_split_80_8_56 (sp : BitVec 64) :
    memRegion (sp - 2000#64) 144 =
      memRegion (sp - 2000#64) 80 ∗
        (∃∗ v : BitVec 64, (sp - 1920#64) ↦₆₄ v) ∗
        memRegion (sp - 1912#64) 56 := by
  rw [ProofLib.memRegion_split' (b := sp - 2000#64) (n := 80) (k := 64)
        (b' := sp - 1920#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1920#64) (n := 8) (k := 56)
        (b' := sp - 1912#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 1920#64)]

theorem rejoin_memRegion_144_80_8_56 (sp : BitVec 64) {bs : List (BitVec 8)} (hbs : bs.length = 8) :
    memRegion (sp - 2000#64) 80 ∗ ((sp - 1920#64) ↦ₛ bs) ∗ memRegion (sp - 1912#64) 56 ⊢
      memRegion (sp - 2000#64) 144 := by
  rw [ProofLib.memRegion_split' (b := sp - 2000#64) (n := 80) (k := 64)
        (b' := sp - 1920#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1920#64) (n := 8) (k := 56)
        (b' := sp - 1912#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_left (hbs ▸ pointsToBytes_entails_memRegion (sp - 1920#64) bs))

theorem le_of_not_ule_sub_960 {cap : BitVec 64}
    (hle : 960 ≤ cap.toNat)
    (h : ¬ (cap - 960#64).ule 127#64 = true) :
    1088 ≤ cap.toNat := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le] at h
  · change ¬ (cap.toNat - 960 ≤ 127) at h; omega
  · rw [BitVec.le_def]; exact hle

theorem reserveCap_bound_of_ule_sub_960 {cap : BitVec 64}
    (hle : 960 ≤ cap.toNat)
    (h : (cap - 960#64).ule 127#64 = true) :
    reserveCap cap.toNat 960 128 + 1 ≤ 2 ^ 63 := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le] at h
  · change cap.toNat - 960 ≤ 127 at h
    dsimp only [reserveCap]
    omega
  · rw [BitVec.le_def]; exact hle

theorem reserveCap_ge_1088 {cap : BitVec 64}
    (hbound : reserveCap cap.toNat 960 128 + 1 ≤ 2 ^ 63) :
    1088 ≤ (BitVec.ofNat 64 (reserveCap cap.toNat 960 128)).toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  dsimp only [reserveCap]
  omega

theorem reserveCap_ne_zero {cap : Nat}
    (hbound : reserveCap cap 960 128 + 1 ≤ 2 ^ 63) :
    BitVec.ofNat 64 (reserveCap cap 960 128) ≠ 0#64 := by
  intro h0
  have h1 := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  change reserveCap cap 960 128 = 0 at h1
  dsimp only [reserveCap] at h1
  omega

theorem vecU8At_expose_sp_1280 (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8At A (sp - 1280#64) cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 1280#64) ↦₆₄ cap) ∗
        ((sp - 1272#64) ↦₆₄ ptr) ∗
        ((sp - 1264#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 := by
  rw [vecU8At_eq_cells_heap A (sp - 1280#64) cap ptr bs]
  have h1 : (sp - 1280#64) + 8#64 = sp - 1272#64 := by bv_omega
  have h2 : (sp - 1280#64) + 16#64 = sp - 1264#64 := by bv_omega
  rw [h1, h2]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_nonempty A cap ptr bs hpos)))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem bytes_rem_entails_memRegion (ptr cap : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hmax : cap.toNat + 1 ≤ 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      memRegion ptr cap.toNat := by
  rw [ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

theorem memRegion_ct1_split_128 (ptr_ct1' : BitVec 64) {cap : Nat}
    (hge : 1088 ≤ cap) (hlt : cap < 2 ^ 63) :
    memRegion (ptr_ct1' + 960#64) (cap - 960) =
      memRegion (ptr_ct1' + 960#64) 128 ∗
        memRegion (ptr_ct1' + 1088#64) (cap - 1088) := by
  rw [ProofLib.memRegion_split' (b := ptr_ct1' + 960#64) (n := 128) (k := cap - 1088)
        (b' := ptr_ct1' + 1088#64) (by omega) (by bv_omega) (by omega)]

theorem vecU8At_expose_sp_1304 (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8At A (sp - 1328#64 + 0x18#64) cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 1304#64) ↦₆₄ cap) ∗
        ((sp - 1296#64) ↦₆₄ ptr) ∗
        ((sp - 1288#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 := by
  have h0 : sp - 1328#64 + 0x18#64 = sp - 1304#64 := by bv_omega
  have h1 : (sp - 1304#64) + 8#64 = sp - 1296#64 := by bv_omega
  have h2 : (sp - 1304#64) + 16#64 = sp - 1288#64 := by bv_omega
  rw [h0, vecU8At_eq_cells_heap A (sp - 1304#64) cap ptr bs, h1, h2]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_nonempty A cap ptr bs hpos)))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem vecU8_expose_nonempty_288 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8 A (sp - 288#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap ≠ 0#64 ∧ LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧ bs.length ≤ cap.toNat⌝ ∗
          ((sp - 288#64) ↦₆₄ cap) ∗
          ((sp - 280#64) ↦₆₄ ptr) ∗
          ((sp - 272#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1 := by
  dsimp only [vecU8]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A (sp - 288#64) cap ptr bs]
  have h8 : (sp - 288#64) + 8#64 = sp - 280#64 := by bv_omega
  have h16 : (sp - 288#64) + 16#64 = sp - 272#64 := by bv_omega
  rw [h8, h16]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_nonempty A cap ptr bs hpos)))) ?_
  have hcomm :
      ((sp - 288#64) ↦₆₄ cap) ∗ ((sp - 280#64) ↦₆₄ ptr) ∗
        ((sp - 272#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
          (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 288#64) ↦₆₄ cap) ∗ ((sp - 280#64) ↦₆₄ ptr) ∗
        ((sp - 272#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 := by ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun ⟨hle, hmax, hptr, hcap⟩ => ?_
  have hpos_cap : 0 < cap.toNat := by
    have : cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos_cap, ⟨0, rfl⟩, by omega⟩
  exact Entails.pure_right ⟨hcap, hlay, hptr, hle⟩ (Entails.refl _)

theorem pointsToBytes_append_960_128 (ptr : BitVec 64) (bs1 bs2 : List (BitVec 8))
    (h1 : bs1.length = 960) :
    (ptr ↦ₛ bs1) ∗ ((ptr + 960#64) ↦ₛ bs2) ⊢ (ptr ↦ₛ (bs1 ++ bs2)) := by
  rw [pointsToBytes_append ptr bs1 bs2, h1]
  exact Entails.refl _

end Part2bHelpers

section Part2cHelpers
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  recvCt2Chunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff mlkemDecaps_fnOff
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff doReserve7_fnOff_eq
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x67028
  libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x58ac4
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x46920
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5e5f0
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::result::unwrap_failed") (ls_hook% "core::result::unwrap_failed")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")

/-! ## Pure & Stack Helpers for MAC Comparison -/

theorem vecU8_expose_nonempty_1248 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8 A (sp - 1248#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap ≠ 0#64 ∧ LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧ bs.length ≤ cap.toNat⌝ ∗
          ((sp - 1248#64) ↦₆₄ cap) ∗
          ((sp - 1240#64) ↦₆₄ ptr) ∗
          ((sp - 1232#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1 := by
  dsimp only [vecU8]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A (sp - 1248#64) cap ptr bs]
  have h8 : (sp - 1248#64) + 8#64 = sp - 1240#64 := by bv_omega
  have h16 : (sp - 1248#64) + 16#64 = sp - 1232#64 := by bv_omega
  rw [h8, h16]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_nonempty A cap ptr bs hpos)))) ?_
  have hcomm :
      ((sp - 1248#64) ↦₆₄ cap) ∗ ((sp - 1240#64) ↦₆₄ ptr) ∗
        ((sp - 1232#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
          (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 1248#64) ↦₆₄ cap) ∗ ((sp - 1240#64) ↦₆₄ ptr) ∗
        ((sp - 1232#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 := by ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun ⟨hle, hmax, hptr, hcap⟩ => ?_
  have hpos_cap : 0 < cap.toNat := by
    have : cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos_cap, ⟨0, rfl⟩, by omega⟩
  exact Entails.pure_right ⟨hcap, hlay, hptr, hle⟩ (Entails.refl _)

theorem rejoin_memRegion_960_24_24_912 (sp : BitVec 64) (u0 u1 u2 : BitVec 64) :
    ((sp - 1248#64) ↦₆₄ u0) ∗ ((sp - 1240#64) ↦₆₄ u1) ∗ ((sp - 1232#64) ↦₆₄ u2) ∗
      memRegion (sp - 1224#64) 24 ∗ memRegion (sp - 1200#64) 912 ⊢
      memRegion (sp - 1248#64) 960 := by
  have h1 : (sp - 1248#64) + 8#64 = sp - 1240#64 := by bv_omega
  have h2 : (sp - 1248#64) + 16#64 = sp - 1232#64 := by bv_omega
  have h24 :
      ((sp - 1248#64) ↦₆₄ u0) ∗ ((sp - 1240#64) ↦₆₄ u1) ∗ ((sp - 1232#64) ↦₆₄ u2) ⊢
        memRegion (sp - 1248#64) 24 := by
    rw [memRegion_24_cells (sp - 1248#64), h1, h2]
    exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2 (Entails.refl _)))
  rw [ProofLib.memRegion_split' (b := sp - 1248#64) (n := 24) (k := 936)
        (b' := sp - 1224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1224#64) (n := 24) (k := 912)
        (b' := sp - 1200#64) rfl (by bv_omega) (by decide)]
  have hassoc :
      ((sp - 1248#64) ↦₆₄ u0) ∗ ((sp - 1240#64) ↦₆₄ u1) ∗ ((sp - 1232#64) ↦₆₄ u2) ∗
        memRegion (sp - 1224#64) 24 ∗ memRegion (sp - 1200#64) 912 =
      (((sp - 1248#64) ↦₆₄ u0) ∗ ((sp - 1240#64) ↦₆₄ u1) ∗ ((sp - 1232#64) ↦₆₄ u2)) ∗
        (memRegion (sp - 1224#64) 24 ∗ memRegion (sp - 1200#64) 912) := by ac_rfl
  rw [hassoc]
  exact sepConj_mono_left h24

theorem sub_one_ofNat_succ (n : Nat) (hn : n < 32) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h3 : (1#64 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_sub_of_le]
  · omega
  · rw [BitVec.le_def]; omega

theorem bne_zero_ofNat_succ (n : Nat) (hn : n < 32) :
    ((BitVec.ofNat 64 (n + 1) == 0#64) == false) = true := by
  have hne : BitVec.ofNat 64 (n + 1) ≠ 0#64 := by
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    change n + 1 = 0 at h1
    omega
  rw [beq_false_of_ne hne]
  rfl

theorem bne_one_ofNat_cons2 (a a2 : BitVec 8) (lhs'' : List (BitVec 8))
    (hle : (a :: a2 :: lhs'').length ≤ 32) :
    (BitVec.ofNat 64 (a :: a2 :: lhs'').length != 1#64) = true := by
  simp only [bne_iff_ne]
  intro h1
  have h2 := congrArg BitVec.toNat h1
  simp only [List.length_cons] at hle h2
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
  change lhs''.length + 1 + 1 = 1 at h2
  omega

theorem sub_one_ofNat_cons2 (a a2 : BitVec 8) (lhs'' : List (BitVec 8))
    (hle : (a :: a2 :: lhs'').length ≤ 32) :
    BitVec.ofNat 64 (a :: a2 :: lhs'').length - 1#64 =
      BitVec.ofNat 64 (a2 :: lhs'').length := by
  simp only [List.length_cons] at hle ⊢
  exact sub_one_ofNat_succ (lhs''.length + 1) (by omega)

theorem xor_orr_loop_step (acc a b : BitVec 8) :
    BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 b ^^^ BitVec.zeroExtend 64 a)) |||
          BitVec.zeroExtend 64 acc)) =
      BitVec.zeroExtend 64 (acc ||| (a ^^^ b)) := by
  ext i hi
  by_cases h32 : i < 32 <;> simp [h32, Bool.or_comm, Bool.xor_comm]

theorem stackAt_extHook_eq_16 (sp : BitVec 64) :
    stackAt (sp - 2496#64) extHookStack =
      memRegion (sp - 18880#64) 16368 ∗ stackAt (sp - 2496#64) 16 := by
  have h := stackAt_split_bottom (sp - 2496#64) 16 16368 (by decide)
  have h2 : (sp - 2496#64) - BitVec.ofNat 64 (16 + 16368) = sp - 18880#64 := by
    change (sp - 2496#64) - 16384#64 = sp - 18880#64
    bv_omega
  rw [h2] at h
  exact h

theorem ule_32_sub_129_iff {n : Nat} (hge : 129 ≤ n) (hlt : n < 2 ^ 63) :
    (32#64 : BitVec 64).ule (BitVec.ofNat 64 n - 129#64) = true ↔ ¬ (n - 128 ≤ 32) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h129 : (129#64 : BitVec 64).toNat = 129 := rfl
  have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le]
  · omega
  · rw [BitVec.le_def]; omega

theorem recv_ct2_chunk_isPanic_of_mac_gt_32 {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_ct2 chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge : ¬ ct2Full.length < 128)
    (hct1 : self.uc.ct1.length = 960)
    (hdk : self.uc.dk.length = 2400)
    (hm : ¬ (ct2Full.drop 128).length ≤ 32) :
    (self.recv_ct2_chunk K epoch chunk).isPanic = true := by
  have hafter := recv_ct2_chunk_after_decaps (K := K) self epoch chunk receivingCt2 ct2Full
    hepoch hadd hdec hge hct1 hdk
  dsimp only at hafter
  let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
  let ss_raw := (K.decaps ⟨self.uc.dk, hdk⟩ ⟨self.uc.ct1, hct1⟩ ⟨ct2Full.take 128, hct2⟩).toList
  let info := sckaKeyInfoPrefix ++ toBEBytes 8 self.uc.epoch
  let ss := spqrHkdfWith F (List.replicate 32 0#8) ss_raw info 32
  let auth' := self.uc.auth.update F self.uc.epoch ss
  have hk_lt : auth'.macKey.length < 2 ^ 32 := by
    rw [auth_update_macKey_length_32]; decide
  have hd_lt : (Authenticator.ctLabel ++ toBEBytes 8 self.uc.epoch ++ (self.uc.ct1 ++ ct2Full.take 128)).length < 2 ^ 32 := by
    simp [List.length_append, ctLabel_length, hct1, hct2]
  have herr := verifyCtError_of_mac_gt_32 F auth' self.uc.epoch
    (self.uc.ct1 ++ ct2Full.take 128) (ct2Full.drop 128) hk_lt hd_lt hm
  rw [hafter, herr]
  rfl

theorem vecBufAt_expose_of_bytes_live (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hne0 : bs.length ≠ 0) (hle : bs.length < 2 ^ 63) :
    vecBufAt A (BitVec.ofNat 64 bs.length) ptr bs ⊢
      (ptr ↦ₛ bs) ∗ A.live ptr bs.length 1 := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [htoNat] at h1
    change bs.length = 0 at h1
    omega
  dsimp only [vecBufAt]
  simp only [hcap_ne, ↓reduceIte, htoNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.refl _

theorem isNonZero_foldl_eq_compare_prefix (lhs rhs : List (BitVec 8)) :
    isNonZero (List.foldl (fun r x => r ||| x.1 ^^^ x.2) 0#8 (lhs.zip rhs)) =
      compare_prefix lhs rhs := rfl

theorem tst_ff_zeroExtend_64_false_of_bne {v : BitVec 8} (h : (v != 0#8) = true) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 v &&& 1095216660735#64) == 0#32) = false := by
  revert v h; decide

theorem tst_ff_zeroExtend_64_true_of_bne_false {v : BitVec 8} (h : (v != 0#8) = false) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 v &&& 1095216660735#64) == 0#32) = true := by
  revert v h; decide

end Part2cHelpers

section Part3Helpers
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem stackAt_extHook_eq_dropGluePoly16 (sp : BitVec 64) :
    stackAt (sp - 2496#64) extHookStack =
      memRegion (sp - 18880#64) 12256 ∗ stackAt (sp - 2496#64) dropGluePoly16Stack := by
  have h := stackAt_split_bottom (sp - 2496#64) dropGluePoly16Stack 12256 (by decide)
  have h1 : dropGluePoly16Stack + 12256 = extHookStack := rfl
  have h2 : sp - 2496#64 - BitVec.ofNat 64 (dropGluePoly16Stack + 12256) = sp - 18880#64 := by
    change sp - 2496#64 - 16384#64 = sp - 18880#64
    bv_omega
  rw [h2, h1] at h
  exact h

theorem recv_ct2_chunk_eq_err_macVerifyFailed {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_ct2 chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge : ¬ ct2Full.length < 128)
    (hct1 : self.uc.ct1.length = 960)
    (hdk : self.uc.dk.length = 2400)
    (hm : (ct2Full.drop 128).length ≤ 32)
    (hcmp :
      (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
       let ss_raw := (K.decaps ⟨self.uc.dk, hdk⟩ ⟨self.uc.ct1, hct1⟩ ⟨ct2Full.take 128, hct2⟩).toList
       let info := sckaKeyInfoPrefix ++ toBEBytes 8 self.uc.epoch
       let ss := spqrHkdfWith F (List.replicate 32 0#8) ss_raw info 32
       let auth' := self.uc.auth.update F self.uc.epoch ss
       let ct1Full := self.uc.ct1 ++ ct2Full.take 128
       let tag := hmacWith F auth'.macKey (Authenticator.ctLabel ++ toBEBytes 8 self.uc.epoch ++ ct1Full)
       compare_prefix (ct2Full.drop 128) tag != 0#8) = true) :
    self.recv_ct2_chunk K epoch chunk = .error (.err .macVerifyFailed) := by
  have hafter := recv_ct2_chunk_after_decaps (K := K) self epoch chunk receivingCt2 ct2Full
    hepoch hadd hdec hge hct1 hdk
  dsimp only at hafter hcmp
  rw [hafter]
  let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
  let ss_raw := (K.decaps ⟨self.uc.dk, hdk⟩ ⟨self.uc.ct1, hct1⟩ ⟨ct2Full.take 128, hct2⟩).toList
  let info := sckaKeyInfoPrefix ++ toBEBytes 8 self.uc.epoch
  let ss := spqrHkdfWith F (List.replicate 32 0#8) ss_raw info 32
  let auth' := self.uc.auth.update F self.uc.epoch ss
  let ct1Full := self.uc.ct1 ++ ct2Full.take 128
  have hk : auth'.macKey.length < 2 ^ 32 := by
    rw [auth_update_macKey_length_32]; decide
  have hd : (Authenticator.ctLabel ++ toBEBytes 8 self.uc.epoch ++ ct1Full).length < 2 ^ 32 := by
    rw [List.length_append, List.length_append, List.length_append, hct1, hct2]
    have h1 : Authenticator.ctLabel.length = 35 := rfl
    have h2 : (toBEBytes 8 self.uc.epoch).length = 8 := by simp [CryptoGames.HMAC.toBEBytes]
    omega
  have hver := verifyCtError_of_mac_le_32 F auth' self.uc.epoch ct1Full (ct2Full.drop 128) hk hd hm
  rw [macCtUnchecked_eq_hmacWith] at hver
  rw [hver, hcmp]
  rfl

theorem recv_ct2_chunk_isPanic_of_epoch_allOnes {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_ct2 chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge : ¬ ct2Full.length < 128)
    (hct1 : self.uc.ct1.length = 960)
    (hdk : self.uc.dk.length = 2400)
    (hm : (ct2Full.drop 128).length ≤ 32)
    (hcmp :
      (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
       let ss_raw := (K.decaps ⟨self.uc.dk, hdk⟩ ⟨self.uc.ct1, hct1⟩ ⟨ct2Full.take 128, hct2⟩).toList
       let info := sckaKeyInfoPrefix ++ toBEBytes 8 self.uc.epoch
       let ss := spqrHkdfWith F (List.replicate 32 0#8) ss_raw info 32
       let auth' := self.uc.auth.update F self.uc.epoch ss
       let ct1Full := self.uc.ct1 ++ ct2Full.take 128
       let tag := hmacWith F auth'.macKey (Authenticator.ctLabel ++ toBEBytes 8 self.uc.epoch ++ ct1Full)
       compare_prefix (ct2Full.drop 128) tag != 0#8) = false)
    (hall : (self.uc.epoch == BitVec.allOnes 64) = true) :
    (self.recv_ct2_chunk K epoch chunk).isPanic = true := by
  have hafter := recv_ct2_chunk_after_decaps (K := K) self epoch chunk receivingCt2 ct2Full
    hepoch hadd hdec hge hct1 hdk
  dsimp only at hafter hcmp
  refine (congrArg StatesResult.isPanic hafter).trans ?_
  let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
  let ss_raw := (K.decaps ⟨self.uc.dk, hdk⟩ ⟨self.uc.ct1, hct1⟩ ⟨ct2Full.take 128, hct2⟩).toList
  let info := sckaKeyInfoPrefix ++ toBEBytes 8 self.uc.epoch
  let ss := spqrHkdfWith F (List.replicate 32 0#8) ss_raw info 32
  let auth' := self.uc.auth.update F self.uc.epoch ss
  let ct1Full := self.uc.ct1 ++ ct2Full.take 128
  have hk : auth'.macKey.length < 2 ^ 32 := by
    rw [auth_update_macKey_length_32]; decide
  have hd : (Authenticator.ctLabel ++ toBEBytes 8 self.uc.epoch ++ ct1Full).length < 2 ^ 32 := by
    rw [List.length_append, List.length_append, List.length_append, hct1, hct2]
    have h1 : Authenticator.ctLabel.length = 35 := rfl
    have h2 : (toBEBytes 8 self.uc.epoch).length = 8 := by simp [CryptoGames.HMAC.toBEBytes]
    omega
  have hver := verifyCtError_of_mac_le_32 F auth' self.uc.epoch ct1Full (ct2Full.drop 128) hk hd hm
  rw [macCtUnchecked_eq_hmacWith] at hver
  have hcmp' : ¬ (compare_prefix (ct2Full.drop 128)
      (hmacWith F auth'.macKey (Authenticator.ctLabel ++ toBEBytes 8 self.uc.epoch ++ ct1Full)) != 0#8) = true := by
    rw [hcmp]; decide
  rw [hver, ite_eq_right_iff.mpr (fun h => False.elim (hcmp' h)), hall]
  rfl

theorem recv_ct2_chunk_eq_done {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_ct2 chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge : ¬ ct2Full.length < 128)
    (hct1 : self.uc.ct1.length = 960)
    (hdk : self.uc.dk.length = 2400)
    (hm : (ct2Full.drop 128).length ≤ 32)
    (hcmp :
      (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
       let ss_raw := (K.decaps ⟨self.uc.dk, hdk⟩ ⟨self.uc.ct1, hct1⟩ ⟨ct2Full.take 128, hct2⟩).toList
       let info := sckaKeyInfoPrefix ++ toBEBytes 8 self.uc.epoch
       let ss := spqrHkdfWith F (List.replicate 32 0#8) ss_raw info 32
       let auth' := self.uc.auth.update F self.uc.epoch ss
       let ct1Full := self.uc.ct1 ++ ct2Full.take 128
       let tag := hmacWith F auth'.macKey (Authenticator.ctLabel ++ toBEBytes 8 self.uc.epoch ++ ct1Full)
       compare_prefix (ct2Full.drop 128) tag != 0#8) = false)
    (hall : (self.uc.epoch == BitVec.allOnes 64) = false) :
    let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
    let ss_raw := (K.decaps ⟨self.uc.dk, hdk⟩ ⟨self.uc.ct1, hct1⟩ ⟨ct2Full.take 128, hct2⟩).toList
    let info := sckaKeyInfoPrefix ++ toBEBytes 8 self.uc.epoch
    let ss := spqrHkdfWith F (List.replicate 32 0#8) ss_raw info 32
    let auth' := self.uc.auth.update F self.uc.epoch ss
    self.recv_ct2_chunk K epoch chunk =
      .ok (.done ({ uc := { epoch := self.uc.epoch + 1#64, auth := auth' },
                    receiving_hdr := polyDecoderNew96 },
                  { epoch := self.uc.epoch, secret := ss })) := by
  intro hct2 ss_raw info ss auth'
  have hafter := recv_ct2_chunk_after_decaps (K := K) self epoch chunk receivingCt2 ct2Full
    hepoch hadd hdec hge hct1 hdk
  dsimp only at hafter hcmp
  rw [hafter]
  let ct1Full := self.uc.ct1 ++ ct2Full.take 128
  have hk : auth'.macKey.length < 2 ^ 32 := by
    rw [auth_update_macKey_length_32]; decide
  have hd : (Authenticator.ctLabel ++ toBEBytes 8 self.uc.epoch ++ ct1Full).length < 2 ^ 32 := by
    rw [List.length_append, List.length_append, List.length_append, hct1, hct2]
    have h1 : Authenticator.ctLabel.length = 35 := rfl
    have h2 : (toBEBytes 8 self.uc.epoch).length = 8 := by simp [CryptoGames.HMAC.toBEBytes]
    omega
  have hver := verifyCtError_of_mac_le_32 F auth' self.uc.epoch ct1Full (ct2Full.drop 128) hk hd hm
  rw [macCtUnchecked_eq_hmacWith] at hver
  have hcmp' : ¬ (compare_prefix (ct2Full.drop 128)
      (hmacWith F auth'.macKey (Authenticator.ctLabel ++ toBEBytes 8 self.uc.epoch ++ ct1Full)) != 0#8) = true := by
    rw [hcmp]; decide
  rw [hver, ite_eq_right_iff.mpr (fun h => False.elim (hcmp' h)), hall]
  rfl

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  recvCt2Chunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff mlkemDecaps_fnOff
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff doReserve7_fnOff_eq
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x67028
  libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x58ac4
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x46920
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5e5f0
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::result::unwrap_failed") (ls_hook% "core::result::unwrap_failed")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")

def b0 (w : BitVec 64) : BitVec 8 :=
  w.extractLsb' 0 8

/-- Bytes 1..8 (the high 7 bytes) of a 64-bit word `w`, placed at `a .. a + 7`. -/
def mid7At (a : BitVec 64) (w : BitVec 64) : SepProp :=
  ((a + 0#64) ↦₈ (w.extractLsb' 8 8)) ∗
  ((a + 1#64) ↦₈ (w.extractLsb' 16 8)) ∗
  ((a + 2#64) ↦₈ (w.extractLsb' 24 8)) ∗
  ((a + 3#64) ↦₈ (w.extractLsb' 32 8)) ∗
  ((a + 4#64) ↦₈ (w.extractLsb' 40 8)) ∗
  ((a + 5#64) ↦₈ (w.extractLsb' 48 8)) ∗
  ((a + 6#64) ↦₈ (w.extractLsb' 56 8))

/-- 64-bit word formed by taking the high 7 bytes of `w1` (low 56 bits) followed by byte 0 of `w2` (high 8 bits). -/
def shiftWord8 (w1 w2 : BitVec 64) : BitVec 64 :=
  (w2.extractLsb' 0 8).zeroExtend 64 <<< 56 ||| (w1 >>> 8)

theorem pointsTo64_eq_b0_mid7 (a w : BitVec 64) :
    (a ↦₆₄ w) = (a ↦₈ b0 w) ∗ mid7At (a + 1#64) w := by
  unfold Arm64.pointsTo64 b0 mid7At
  have h0 : a + 0#64 = a := by bv_omega
  have h1 : (a + 1#64) + 0#64 = a + 1#64 := by bv_omega
  have h2 : (a + 1#64) + 1#64 = a + 2#64 := by bv_omega
  have h3 : (a + 1#64) + 2#64 = a + 3#64 := by bv_omega
  have h4 : (a + 1#64) + 3#64 = a + 4#64 := by bv_omega
  have h5 : (a + 1#64) + 4#64 = a + 5#64 := by bv_omega
  have h6 : (a + 1#64) + 5#64 = a + 6#64 := by bv_omega
  have h7 : (a + 1#64) + 6#64 = a + 7#64 := by bv_omega
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

theorem mid7_b0_eq_pointsTo64_shiftWord8 (a w1 w2 : BitVec 64) :
    mid7At a w1 ∗ ((a + 7#64) ↦₈ b0 w2) = (a ↦₆₄ shiftWord8 w1 w2) := by
  unfold mid7At Arm64.pointsTo64 b0 shiftWord8
  have hb0 : ((w2.extractLsb' 0 8).zeroExtend 64 <<< 56 ||| (w1 >>> 8)).extractLsb' 0 8 =
      w1.extractLsb' 8 8 := by bv_bits
  have hb1 : ((w2.extractLsb' 0 8).zeroExtend 64 <<< 56 ||| (w1 >>> 8)).extractLsb' 8 8 =
      w1.extractLsb' 16 8 := by bv_bits
  have hb2 : ((w2.extractLsb' 0 8).zeroExtend 64 <<< 56 ||| (w1 >>> 8)).extractLsb' 16 8 =
      w1.extractLsb' 24 8 := by bv_bits
  have hb3 : ((w2.extractLsb' 0 8).zeroExtend 64 <<< 56 ||| (w1 >>> 8)).extractLsb' 24 8 =
      w1.extractLsb' 32 8 := by bv_bits
  have hb4 : ((w2.extractLsb' 0 8).zeroExtend 64 <<< 56 ||| (w1 >>> 8)).extractLsb' 32 8 =
      w1.extractLsb' 40 8 := by bv_bits
  have hb5 : ((w2.extractLsb' 0 8).zeroExtend 64 <<< 56 ||| (w1 >>> 8)).extractLsb' 40 8 =
      w1.extractLsb' 48 8 := by bv_bits
  have hb6 : ((w2.extractLsb' 0 8).zeroExtend 64 <<< 56 ||| (w1 >>> 8)).extractLsb' 48 8 =
      w1.extractLsb' 56 8 := by bv_bits
  have hb7 : ((w2.extractLsb' 0 8).zeroExtend 64 <<< 56 ||| (w1 >>> 8)).extractLsb' 56 8 =
      w2.extractLsb' 0 8 := by bv_bits
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  ac_rfl

theorem window15_left_eq_right (a8 a15 a16 w2 w3 : BitVec 64)
    (h15 : a15 = a8 + 7#64) (h16 : a16 = a8 + 8#64) :
    ((a8 ↦₆₄ shiftWord8 w2 w3) ∗ mid7At a16 w3) =
      (mid7At a8 w2 ∗ (a15 ↦₆₄ w3)) := by
  have h16' : a15 + 1#64 = a16 := by subst h15 h16; bv_omega
  rw [← h16', ← mid7_b0_eq_pointsTo64_shiftWord8 a8 w2 w3, ← h15,
      sepConj_assoc, ← pointsTo64_eq_b0_mid7 a15 w3]

def b7 (w : BitVec 64) : BitVec 8 :=
  w.extractLsb' 56 8

/-- Bytes 0..7 (the low 7 bytes) of a 64-bit word `w`, placed at `a .. a + 7`. -/
def low7At (a : BitVec 64) (w : BitVec 64) : SepProp :=
  ((a + 0#64) ↦₈ (w.extractLsb' 0 8)) ∗
  ((a + 1#64) ↦₈ (w.extractLsb' 8 8)) ∗
  ((a + 2#64) ↦₈ (w.extractLsb' 16 8)) ∗
  ((a + 3#64) ↦₈ (w.extractLsb' 24 8)) ∗
  ((a + 4#64) ↦₈ (w.extractLsb' 32 8)) ∗
  ((a + 5#64) ↦₈ (w.extractLsb' 40 8)) ∗
  ((a + 6#64) ↦₈ (w.extractLsb' 48 8))

/-- 64-bit word formed by byte 7 of `w1` (low 8 bits) followed by the low 7 bytes of `w2` (high 56 bits). -/
def unshiftWord8 (w1 w2 : BitVec 64) : BitVec 64 :=
  (w2 <<< 8) ||| (w1.extractLsb' 56 8).zeroExtend 64

/-- Replace byte 7 (highest 8 bits) of `w1` with byte 0 of `w2`. -/
def setByte7 (w1 w2 : BitVec 64) : BitVec 64 :=
  ((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 &&& 0x00ff_ffff_ffff_ffff#64)

theorem pointsTo64_eq_low7_b7 (a w : BitVec 64) :
    (a ↦₆₄ w) = low7At a w ∗ ((a + 7#64) ↦₈ b7 w) := by
  unfold Arm64.pointsTo64 low7At b7
  ac_rfl

theorem b7_low7_eq_pointsTo64_unshiftWord8 (a w1 w2 : BitVec 64) :
    (a ↦₈ b7 w1) ∗ low7At (a + 1#64) w2 = (a ↦₆₄ unshiftWord8 w1 w2) := by
  unfold Arm64.pointsTo64 low7At b7 unshiftWord8
  have h0 : a + 0#64 = a := by bv_omega
  have h1 : (a + 1#64) + 0#64 = a + 1#64 := by bv_omega
  have h2 : (a + 1#64) + 1#64 = a + 2#64 := by bv_omega
  have h3 : (a + 1#64) + 2#64 = a + 3#64 := by bv_omega
  have h4 : (a + 1#64) + 3#64 = a + 4#64 := by bv_omega
  have h5 : (a + 1#64) + 4#64 = a + 5#64 := by bv_omega
  have h6 : (a + 1#64) + 5#64 = a + 6#64 := by bv_omega
  have h7 : (a + 1#64) + 6#64 = a + 7#64 := by bv_omega
  have hb0 : ((w2 <<< 8) ||| (w1.extractLsb' 56 8).zeroExtend 64).extractLsb' 0 8 =
      w1.extractLsb' 56 8 := by bv_bits
  have hb1 : ((w2 <<< 8) ||| (w1.extractLsb' 56 8).zeroExtend 64).extractLsb' 8 8 =
      w2.extractLsb' 0 8 := by bv_bits
  have hb2 : ((w2 <<< 8) ||| (w1.extractLsb' 56 8).zeroExtend 64).extractLsb' 16 8 =
      w2.extractLsb' 8 8 := by bv_bits
  have hb3 : ((w2 <<< 8) ||| (w1.extractLsb' 56 8).zeroExtend 64).extractLsb' 24 8 =
      w2.extractLsb' 16 8 := by bv_bits
  have hb4 : ((w2 <<< 8) ||| (w1.extractLsb' 56 8).zeroExtend 64).extractLsb' 32 8 =
      w2.extractLsb' 24 8 := by bv_bits
  have hb5 : ((w2 <<< 8) ||| (w1.extractLsb' 56 8).zeroExtend 64).extractLsb' 40 8 =
      w2.extractLsb' 32 8 := by bv_bits
  have hb6 : ((w2 <<< 8) ||| (w1.extractLsb' 56 8).zeroExtend 64).extractLsb' 48 8 =
      w2.extractLsb' 40 8 := by bv_bits
  have hb7 : ((w2 <<< 8) ||| (w1.extractLsb' 56 8).zeroExtend 64).extractLsb' 56 8 =
      w2.extractLsb' 48 8 := by bv_bits
  rw [h0, h1, h2, h3, h4, h5, h6, h7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]

theorem low7_b0_eq_pointsTo64_setByte7 (a w1 w2 : BitVec 64) :
    low7At a w1 ∗ ((a + 7#64) ↦₈ b0 w2) = (a ↦₆₄ setByte7 w1 w2) := by
  unfold Arm64.pointsTo64 low7At b0 setByte7
  have hb0 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 &&& 0x00ff_ffff_ffff_ffff#64)).extractLsb' 0 8 =
      w1.extractLsb' 0 8 := by bv_bits
  have hb1 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 &&& 0x00ff_ffff_ffff_ffff#64)).extractLsb' 8 8 =
      w1.extractLsb' 8 8 := by bv_bits
  have hb2 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 &&& 0x00ff_ffff_ffff_ffff#64)).extractLsb' 16 8 =
      w1.extractLsb' 16 8 := by bv_bits
  have hb3 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 &&& 0x00ff_ffff_ffff_ffff#64)).extractLsb' 24 8 =
      w1.extractLsb' 24 8 := by bv_bits
  have hb4 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 &&& 0x00ff_ffff_ffff_ffff#64)).extractLsb' 32 8 =
      w1.extractLsb' 32 8 := by bv_bits
  have hb5 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 &&& 0x00ff_ffff_ffff_ffff#64)).extractLsb' 40 8 =
      w1.extractLsb' 40 8 := by bv_bits
  have hb6 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 &&& 0x00ff_ffff_ffff_ffff#64)).extractLsb' 48 8 =
      w1.extractLsb' 48 8 := by bv_bits
  have hb7 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 &&& 0x00ff_ffff_ffff_ffff#64)).extractLsb' 56 8 =
      w2.extractLsb' 0 8 := by bv_bits
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  ac_rfl

theorem mid7At_eq_low7At (a w : BitVec 64) :
    mid7At a w = low7At a (w >>> 8) := by
  unfold mid7At low7At
  have h0 : w.extractLsb' 8 8 = (w >>> 8).extractLsb' 0 8 := by bv_bits
  have h1 : w.extractLsb' 16 8 = (w >>> 8).extractLsb' 8 8 := by bv_bits
  have h2 : w.extractLsb' 24 8 = (w >>> 8).extractLsb' 16 8 := by bv_bits
  have h3 : w.extractLsb' 32 8 = (w >>> 8).extractLsb' 24 8 := by bv_bits
  have h4 : w.extractLsb' 40 8 = (w >>> 8).extractLsb' 32 8 := by bv_bits
  have h5 : w.extractLsb' 48 8 = (w >>> 8).extractLsb' 40 8 := by bv_bits
  have h6 : w.extractLsb' 56 8 = (w >>> 8).extractLsb' 48 8 := by bv_bits
  rw [h0, h1, h2, h3, h4, h5, h6]

theorem left_and_low7_to_mid_at_7 (a8 a15 a16 w1 w2 : BitVec 64)
    (h15 : a15 = a8 + 7#64) (h16 : a16 = a8 + 8#64) :
    (a8 ↦₆₄ w1) ∗ low7At a16 w2 = low7At a8 w1 ∗ (a15 ↦₆₄ unshiftWord8 w1 w2) := by
  have h16' : a15 + 1#64 = a16 := by subst h15 h16; bv_omega
  rw [pointsTo64_eq_low7_b7 a8 w1, ← h15, sepConj_assoc, ← h16',
      b7_low7_eq_pointsTo64_unshiftWord8 a15 w1 w2]

theorem pair_to_mid_at_7 (a8 a15 a16 a23 w1 w2 : BitVec 64)
    (h15 : a15 = a8 + 7#64) (h16 : a16 = a8 + 8#64) (h23 : a23 = a8 + 15#64) :
    (a8 ↦₆₄ w1) ∗ (a16 ↦₆₄ w2) =
      low7At a8 w1 ∗ (a15 ↦₆₄ unshiftWord8 w1 w2) ∗ (a23 ↦₈ b7 w2) := by
  have h23' : a16 + 7#64 = a23 := by subst h16 h23; bv_omega
  rw [pointsTo64_eq_low7_b7 a16 w2, h23', ← sepConj_assoc,
      left_and_low7_to_mid_at_7 a8 a15 a16 w1 w2 h15 h16, sepConj_assoc]

theorem mid_at_7_to_left (a8 a15 a16 w1 w2 : BitVec 64)
    (h15 : a15 = a8 + 7#64) (h16 : a16 = a8 + 8#64) :
    low7At a8 w1 ∗ (a15 ↦₆₄ w2) = (a8 ↦₆₄ setByte7 w1 w2) ∗ mid7At a16 w2 := by
  have h16' : a15 + 1#64 = a16 := by subst h15 h16; bv_omega
  rw [pointsTo64_eq_b0_mid7 a15 w2, h16', ← sepConj_assoc, h15,
      low7_b0_eq_pointsTo64_setByte7 a8 w1 w2]

theorem low7At_entails_memRegion_7 (a w : BitVec 64) :
    low7At a w ⊢ memRegion a 7 := by
  have hb : IsBlock (low7At a w) a 7 _ :=
    ((IsBlock.pointsTo8 _ _).sepConj ((IsBlock.pointsTo8 _ _).sepConj ((IsBlock.pointsTo8 _ _).sepConj
      ((IsBlock.pointsTo8 _ _).sepConj ((IsBlock.pointsTo8 _ _).sepConj ((IsBlock.pointsTo8 _ _).sepConj
        (IsBlock.pointsTo8 _ _) (by bv_omega) (by decide)) (by bv_omega) (by decide))
        (by bv_omega) (by decide)) (by bv_omega) (by decide)) (by bv_omega) (by decide))
        (by bv_omega) (by decide)).cast (by bv_omega) (fun _ => Iff.rfl)
  exact hb.entails (IsBlock.memRegion a 7) (fun _ _ => trivial)

theorem pointsTo8_entails_memRegion_1 (a : BitVec 64) (v : BitVec 8) :
    (a ↦₈ v) ⊢ memRegion a 1 :=
  (IsBlock.pointsTo8 a v).entails (IsBlock.memRegion a 1) (fun _ _ => trivial)

theorem pointsTo64_entails_memRegion_8 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ⊢ memRegion a 8 :=
  (IsBlock.pointsTo64 a w).entails (IsBlock.memRegion a 8) (fun _ _ => trivial)

theorem mid7At_entails_memRegion_7 (a w : BitVec 64) :
    mid7At a w ⊢ memRegion a 7 := by
  have hb : IsBlock (mid7At a w) a 7 _ :=
    ((IsBlock.pointsTo8 _ _).sepConj ((IsBlock.pointsTo8 _ _).sepConj ((IsBlock.pointsTo8 _ _).sepConj
      ((IsBlock.pointsTo8 _ _).sepConj ((IsBlock.pointsTo8 _ _).sepConj ((IsBlock.pointsTo8 _ _).sepConj
        (IsBlock.pointsTo8 _ _) (by bv_omega) (by decide)) (by bv_omega) (by decide))
        (by bv_omega) (by decide)) (by bv_omega) (by decide)) (by bv_omega) (by decide))
        (by bv_omega) (by decide)).cast (by bv_omega) (fun _ => Iff.rfl)
  exact hb.entails (IsBlock.memRegion a 7) (fun _ _ => trivial)

theorem memRegion_outA_err_split (outA : BitVec 64) :
    memRegion outA chunkedEkSentCt1ReceivedSize ⊢
      ∃∗ o0 : BitVec 64, ∃∗ ob8 : BitVec 8, ∃∗ o9 : BitVec 64, ∃∗ o17 : BitVec 64, ∃∗ o25 : BitVec 64,
        (outA ↦₆₄ o0) ∗ ((outA + 8#64) ↦₈ ob8) ∗
        ((outA + 9#64) ↦₆₄ o9) ∗ ((outA + 17#64) ↦₆₄ o17) ∗
        low7At (outA + 25#64) o25 ∗ memRegion (outA + 32#64) 472 := by
  rw [ProofLib.memRegion_split' (b := outA) (n := 32) (k := 472) (b' := outA + 32#64)
      rfl (by bv_omega) (by decide)]
  rw [show (32 : Nat) = 8 * 4 by rfl, ProofLib.memRegion_cells outA 4 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]
  refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
    Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 => ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right (b0 w1)
    (Entails.sepExists_right (shiftWord8 w1 w2) (Entails.sepExists_right (shiftWord8 w2 w3)
      (Entails.sepExists_right (w3 >>> 8) ?_))))
  have ha9 : (outA + 8#64) + 1#64 = outA + 9#64 := by bv_omega
  have ha16 : (outA + 9#64) + 7#64 = outA + 16#64 := by bv_omega
  have ha17 : (outA + 16#64) + 1#64 = outA + 17#64 := by bv_omega
  have ha24 : (outA + 17#64) + 7#64 = outA + 24#64 := by bv_omega
  have ha25 : (outA + 24#64) + 1#64 = outA + 25#64 := by bv_omega
  rw [pointsTo64_eq_b0_mid7 (outA + 8#64) w1, ha9,
      pointsTo64_eq_b0_mid7 (outA + 16#64) w2, ha17,
      pointsTo64_eq_b0_mid7 (outA + 24#64) w3, ha25,
      ← mid7_b0_eq_pointsTo64_shiftWord8 (outA + 9#64) w1 w2, ha16,
      ← mid7_b0_eq_pointsTo64_shiftWord8 (outA + 17#64) w2 w3, ha24,
      ← mid7At_eq_low7At (outA + 25#64) w3]
  exact Entails.of_eq (by ac_rfl)

theorem rejoin_outA_err (A : RustAlloc) {F : ShaCompress} (outA : BitVec 64)
    (o9 o17 o24 : BitVec 64) :
    (outA ↦₆₄ 0xffff_ffff_ffff_fffe#64) ∗
      ((outA + 8#64) ↦₈ 3#8) ∗
      ((outA + 9#64) ↦₆₄ o9) ∗
      low7At (outA + 17#64) o17 ∗
      ((outA + 24#64) ↦₆₄ o24) ∗
      memRegion (outA + 32#64) 472 ⊢
    ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (.error (.err .macVerifyFailed)) := by
  change (outA ↦₆₄ 0xffff_ffff_ffff_fffe#64) ∗
      ((outA + 8#64) ↦₈ 3#8) ∗
      ((outA + 9#64) ↦₆₄ o9) ∗
      low7At (outA + 17#64) o17 ∗
      ((outA + 24#64) ↦₆₄ o24) ∗
      memRegion (outA + 32#64) 472 ⊢
    (outA ↦₆₄ 0xffff_ffff_ffff_fffe#64) ∗
      ((outA + 8#64) ↦₈ 3#8) ∗
      memRegion (outA + 9#64) 495
  have h9 := pointsTo64_entails_memRegion_8 (outA + 9#64) o9
  have h17 := low7At_entails_memRegion_7 (outA + 17#64) o17
  have h24 := pointsTo64_entails_memRegion_8 (outA + 24#64) o24
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono h9 (sepConj_mono h17 (sepConj_mono_left h24))) ?_
  rw [← sepConj_assoc, ← sepConj_assoc]
  rw [← ProofLib.memRegion_split' (b := outA + 9#64) (n := 8) (k := 7) (b' := outA + 17#64)
      rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := outA + 9#64) (n := 15) (k := 8) (b' := outA + 24#64)
      rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := outA + 9#64) (n := 23) (k := 472) (b' := outA + 32#64)
      rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem dropSortedSetPt16_ok_at_recvCt2 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + (0x46920#64 - 0x59834#64))
      ((dropGlueSortedSetPt16Spec A).inImage img) := by
  have hok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropSortedSetPt16Name)
      ((dropGlueSortedSetPt16Spec A).inImage img) :=
    Alloc.subroutine_ok_inImage img (drop_glue_sorted_set_pt16_ok_ext hdealloc)
  have hrel : (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName =
      (tripleRatchetProgAtExt img.base ext).fnAddr dropSortedSetPt16Name + BitVec.ofNat 64 77588 :=
    Program.fnAddr_rel (k := 77588) (b := img.base) (X := Rust.withPanics ext)
      libsignalSessionCode_fnOff_0x46920 recvCt2Chunk_fnOff (by decide)
  refine sub_ok_of_addr_eq ?_ hok
  rw [hrel, BitVec.add_assoc]; simp

theorem rejoin_stack_polyDecodedMessage_from_extHook (sp : BitVec 64) :
    memRegion (sp - 19552#64) 672 ∗ stackAt (sp - 2496#64) extHookStack ⊢
      stackAt (sp - 2496#64) polyDecodedMessageStackX := by
  rw [stackAt_polyDecodedMessage_eq_extHook (sp - 2496#64)]
  have h : (sp - 2496#64) - 17056#64 = sp - 19552#64 := by bv_omega
  rw [h]
  exact Entails.refl _

theorem rejoin_activeFrameRegionsAt_epilogue (sp : BitVec 64) :
    cells (sp - 2496#64) 9 ∗
      memRegion (sp - 2424#64) 400 ∗
      memRegion (sp - 2024#64) 24 ∗
      memRegion (sp - 1856#64) 504 ∗
      someBranchFrameAt (sp - 2496#64) ⊢
    activeFrameRegionsAt (sp - 2496#64) := by
  unfold activeFrameRegionsAt
  have ha1 : (sp - 2496#64) + 0x48#64 = sp - 2424#64 := by bv_omega
  have ha2 : (sp - 2496#64) + 0x1d8#64 = sp - 2024#64 := by bv_omega
  have ha3 : (sp - 2496#64) + 0x280#64 = sp - 1856#64 := by bv_omega
  rw [ha1, ha2, ha3]
  exact Entails.refl _

theorem memRegion_24_split_23_1 (a : BitVec 64) :
    memRegion a 24 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        low7At (a + 16#64) w2 ∗ ((a + 23#64) ↦₈ b7 w2) := by
  rw [show (24 : Nat) = 8 * 3 by rfl, ProofLib.memRegion_cells a 3 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]
  refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w2 => ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 ?_))
  have h23 : (a + 16#64) + 7#64 = a + 23#64 := by bv_omega
  rw [pointsTo64_eq_low7_b7 (a + 16#64) w2, h23]
  exact Entails.of_eq (by ac_rfl)

theorem rejoin_memRegion_24_mid (a w0 w1 w15 : BitVec 64) (b23 : BitVec 8) :
    (a ↦₆₄ w0) ∗ low7At (a + 8#64) w1 ∗ ((a + 15#64) ↦₆₄ w15) ∗ ((a + 23#64) ↦₈ b23) ⊢
      memRegion a 24 := by
  have h0 := pointsTo64_entails_memRegion_8 a w0
  have h8 := low7At_entails_memRegion_7 (a + 8#64) w1
  have h15 := pointsTo64_entails_memRegion_8 (a + 15#64) w15
  have h23 := pointsTo8_entails_memRegion_1 (a + 23#64) b23
  refine Entails.trans (sepConj_mono h0 (sepConj_mono h8 (sepConj_mono h15 h23))) ?_
  rw [← sepConj_assoc, ← sepConj_assoc]
  rw [← ProofLib.memRegion_split' (b := a) (n := 8) (k := 7) (b' := a + 8#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := a) (n := 15) (k := 8) (b' := a + 15#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := a) (n := 23) (k := 1) (b' := a + 23#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem rejoin_memRegion_24_left (a w0 w8 w16 : BitVec 64) (b23 : BitVec 8) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ mid7At (a + 16#64) w16 ∗ ((a + 23#64) ↦₈ b23) ⊢
      memRegion a 24 := by
  have h0 := pointsTo64_entails_memRegion_8 a w0
  have h8 := pointsTo64_entails_memRegion_8 (a + 8#64) w8
  have h16 := mid7At_entails_memRegion_7 (a + 16#64) w16
  have h23 := pointsTo8_entails_memRegion_1 (a + 23#64) b23
  refine Entails.trans (sepConj_mono h0 (sepConj_mono h8 (sepConj_mono h16 h23))) ?_
  rw [← sepConj_assoc, ← sepConj_assoc]
  rw [← ProofLib.memRegion_split' (b := a) (n := 8) (k := 8) (b' := a + 8#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := a) (n := 16) (k := 7) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := a) (n := 23) (k := 1) (b' := a + 23#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem memRegion_144_x20_split (sp : BitVec 64) :
    memRegion (sp - 2000#64) 144 =
      memRegion (sp - 2000#64) 24 ∗ memRegion (sp - 1976#64) 8 ∗
      memRegion (sp - 1968#64) 24 ∗ memRegion (sp - 1944#64) 88 := by
  rw [ProofLib.memRegion_split' (b := sp - 2000#64) (n := 24) (k := 120) (b' := sp - 1976#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_split' (b := sp - 1976#64) (n := 8) (k := 112) (b' := sp - 1968#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_split' (b := sp - 1968#64) (n := 24) (k := 88) (b' := sp - 1944#64) rfl (by bv_omega) (by decide)]

theorem rejoin_someBranchFrameAt (sp : BitVec 64) :
    memRegion (sp - 2000#64) 144 ∗ memRegion (sp - 1344#64) 16 ∗
      memRegion (sp - 1328#64) 48 ∗ memRegion (sp - 1280#64) 24 ∗
      memRegion (sp - 1248#64) 960 ∗ memRegion (sp - 288#64) 128 ∗
      memRegion (sp - 152#64) 32 ∗ unusedFrameAt (sp - 2496#64) ⊢
    someBranchFrameAt (sp - 2496#64) := by
  unfold someBranchFrameAt
  have h1 : (sp - 2496#64) + 0x1f0#64 = sp - 2000#64 := by bv_omega
  have h2 : (sp - 2496#64) + 0x480#64 = sp - 1344#64 := by bv_omega
  have h3 : (sp - 2496#64) + 0x490#64 = sp - 1328#64 := by bv_omega
  have h4 : (sp - 2496#64) + 0x4c0#64 = sp - 1280#64 := by bv_omega
  have h5 : (sp - 2496#64) + 0x4e0#64 = sp - 1248#64 := by bv_omega
  have h6 : (sp - 2496#64) + 0x8a0#64 = sp - 288#64 := by bv_omega
  have h7 : (sp - 2496#64) + 0x928#64 = sp - 152#64 := by bv_omega
  rw [h1, h2, h3, h4, h5, h6, h7]; exact Entails.refl _

theorem vecU8At_expose_sp_1328 (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8At A (sp - 1328#64) cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 1328#64) ↦₆₄ cap) ∗ ((sp - 1320#64) ↦₆₄ ptr) ∗
        ((sp - 1312#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ct2DeallocAt A cap ptr := by
  have h1 : (sp - 1328#64) + 8#64 = sp - 1320#64 := by bv_omega
  have h2 : (sp - 1328#64) + 16#64 = sp - 1312#64 := by bv_omega
  rw [vecU8At_eq_cells_heap A (sp - 1328#64) cap ptr bs, h1, h2]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_nonempty A cap ptr bs hpos)))) ?_
  have hcomm :
      ((sp - 1328#64) ↦₆₄ cap) ∗ ((sp - 1320#64) ↦₆₄ ptr) ∗
        ((sp - 1312#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
          (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 1328#64) ↦₆₄ cap) ∗ ((sp - 1320#64) ↦₆₄ ptr) ∗
        ((sp - 1312#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1) := by ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun ⟨hle, hmax, hptr, hcap⟩ =>
    Entails.pure_right ⟨hle, hmax, hptr, hcap⟩ (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (bytes_rem_entails_ct2DeallocAt A cap ptr bs hle hmax hptr hcap))))

theorem rejoin_memRegion_48_sp_1328 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp - 1328#64) ↦₆₄ w0) ∗ ((sp - 1320#64) ↦₆₄ w1) ∗ ((sp - 1312#64) ↦₆₄ w2) ∗
      ((sp - 1304#64) ↦₆₄ w3) ∗ ((sp - 1296#64) ↦₆₄ w4) ∗ ((sp - 1288#64) ↦₆₄ w5) ⊢
      memRegion (sp - 1328#64) 48 := by
  have hb : IsBlock
      (((sp - 1328#64) ↦₆₄ w0) ∗ ((sp - 1320#64) ↦₆₄ w1) ∗ ((sp - 1312#64) ↦₆₄ w2) ∗
        ((sp - 1304#64) ↦₆₄ w3) ∗ ((sp - 1296#64) ↦₆₄ w4) ∗ ((sp - 1288#64) ↦₆₄ w5))
      (sp - 1328#64) 48 _ :=
    ((IsBlock.pointsTo64 _ _).sepConj ((IsBlock.pointsTo64 _ _).sepConj
      ((IsBlock.pointsTo64 _ _).sepConj ((IsBlock.pointsTo64 _ _).sepConj
        ((IsBlock.pointsTo64 _ _).sepConj (IsBlock.pointsTo64 _ _)
          (by bv_omega) (by decide)) (by bv_omega) (by decide))
        (by bv_omega) (by decide)) (by bv_omega) (by decide))
      (by bv_omega) (by decide)).cast (by bv_omega) (fun _ => Iff.rfl)
  exact hb.entails (IsBlock.memRegion (sp - 1328#64) 48) (fun _ _ => trivial)

theorem rejoin_memRegion_24_sp_1280 (sp w0 w1 w2 : BitVec 64) :
    ((sp - 1280#64) ↦₆₄ w0) ∗ ((sp - 1272#64) ↦₆₄ w1) ∗ ((sp - 1264#64) ↦₆₄ w2) ⊢
      memRegion (sp - 1280#64) 24 := by
  have hb : IsBlock
      (((sp - 1280#64) ↦₆₄ w0) ∗ ((sp - 1272#64) ↦₆₄ w1) ∗ ((sp - 1264#64) ↦₆₄ w2))
      (sp - 1280#64) 24 _ :=
    ((IsBlock.pointsTo64 _ _).sepConj ((IsBlock.pointsTo64 _ _).sepConj
      (IsBlock.pointsTo64 _ _) (by bv_omega) (by decide))
      (by bv_omega) (by decide)).cast (by bv_omega) (fun _ => Iff.rfl)
  exact hb.entails (IsBlock.memRegion (sp - 1280#64) 24) (fun _ _ => trivial)

theorem rejoin_memRegion_32_sp_152 (sp w0 w1 w2 : BitVec 64) :
    ((sp - 152#64) ↦₆₄ w0) ∗ ((sp - 144#64) ↦₆₄ w1) ∗ ((sp - 136#64) ↦₆₄ w2) ∗
      memRegion (sp - 128#64) 8 ⊢
      memRegion (sp - 152#64) 32 := by
  have hb : IsBlock
      (((sp - 152#64) ↦₆₄ w0) ∗ ((sp - 144#64) ↦₆₄ w1) ∗ ((sp - 136#64) ↦₆₄ w2))
      (sp - 152#64) 24 _ :=
    ((IsBlock.pointsTo64 _ _).sepConj ((IsBlock.pointsTo64 _ _).sepConj
      (IsBlock.pointsTo64 _ _) (by bv_omega) (by decide))
      (by bv_omega) (by decide)).cast (by bv_omega) (fun _ => Iff.rfl)
  have h24 := hb.entails (IsBlock.memRegion (sp - 152#64) 24) (fun _ _ => trivial)
  have hcomm :
      ((sp - 152#64) ↦₆₄ w0) ∗ ((sp - 144#64) ↦₆₄ w1) ∗ ((sp - 136#64) ↦₆₄ w2) ∗
        memRegion (sp - 128#64) 8 =
      (((sp - 152#64) ↦₆₄ w0) ∗ ((sp - 144#64) ↦₆₄ w1) ∗ ((sp - 136#64) ↦₆₄ w2)) ∗
        memRegion (sp - 128#64) 8 := by ac_rfl
  rw [hcomm]
  refine Entails.trans (sepConj_mono_left h24) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 152#64) (n := 24) (k := 8) (b' := sp - 128#64)
      rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem gt_128_of_compare_prefix_bne {ct2Full tag : Bytes}
    (hcmp : (compare_prefix (ct2Full.drop 128) tag != 0#8) = true) :
    128 < ct2Full.length := by
  by_contra hle
  have hnil : ct2Full.drop 128 = [] := List.drop_eq_nil_of_le (by omega)
  simp [hnil, compare_prefix] at hcmp
  exact hcmp rfl

abbrev Ct2DeallocProp (cap ptr : BitVec 64) : Prop :=
  (cap == 0#64) = false ∧ 0 < cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64

theorem ct2DeallocAt_expose (A : RustAlloc) (cap ptr : BitVec 64) :
    ct2DeallocAt A cap ptr ⊢
      ⌜Ct2DeallocProp cap ptr⌝ ∗ memRegion ptr cap.toNat ∗ A.live ptr cap.toNat 1 := by
  dsimp only [ct2DeallocAt, Ct2DeallocProp]
  refine Entails.pure_left fun ⟨hne, hmax, hptr⟩ => ?_
  have hpos : 0 < cap.toNat := by
    apply Nat.pos_of_ne_zero; intro h0; exact hne (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  exact Entails.pure_right ⟨beq_false_of_ne hne, hpos, hmax, hptr⟩ (Entails.refl _)

theorem vecBufAt_entails_memRegion_live (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) :
    vecBufAt A (BitVec.ofNat 64 bs.length) ptr bs ⊢
      memRegion ptr (BitVec.ofNat 64 bs.length).toNat ∗
        A.live ptr (BitVec.ofNat 64 bs.length).toNat 1 := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [htoNat]
  refine Entails.trans (vecBufAt_expose_of_bytes_live A ptr bs (by omega) hlt) ?_
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

end Part3Helpers

section Part3bHelpers
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  recvCt2Chunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff mlkemDecaps_fnOff
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff doReserve7_fnOff_eq
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x67028
  libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x58ac4
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x46920
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5e5f0
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::result::unwrap_failed") (ls_hook% "core::result::unwrap_failed")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")

/-! ## Byte-Shift & `polyDecoderNew96` Construction Helpers -/

theorem unshift_shift_eq (a b c : BitVec 64) :
    unshiftWord8 (shiftWord8 a b) (shiftWord8 b c) = b := by
  unfold unshiftWord8 shiftWord8; bv_bits

theorem unshift_shift_shr8_eq (a b : BitVec 64) :
    unshiftWord8 (shiftWord8 a b) (b >>> 8) = b := by
  unfold unshiftWord8 shiftWord8; bv_bits

theorem setByte7_shift_eq (a b : BitVec 64) :
    setByte7 (shiftWord8 a b) b = shiftWord8 a b := by
  unfold setByte7 shiftWord8; bv_bits

theorem low7At_shiftWord8_eq_mid7At (a w1 w2 : BitVec 64) :
    low7At a (shiftWord8 w1 w2) = mid7At a w1 := by
  unfold low7At mid7At shiftWord8
  have h0 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 >>> 8)).extractLsb' 0 8 =
      w1.extractLsb' 8 8 := by bv_bits
  have h1 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 >>> 8)).extractLsb' 8 8 =
      w1.extractLsb' 16 8 := by bv_bits
  have h2 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 >>> 8)).extractLsb' 16 8 =
      w1.extractLsb' 24 8 := by bv_bits
  have h3 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 >>> 8)).extractLsb' 24 8 =
      w1.extractLsb' 32 8 := by bv_bits
  have h4 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 >>> 8)).extractLsb' 32 8 =
      w1.extractLsb' 40 8 := by bv_bits
  have h5 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 >>> 8)).extractLsb' 40 8 =
      w1.extractLsb' 48 8 := by bv_bits
  have h6 : (((w2.extractLsb' 0 8).zeroExtend 64 <<< 56) ||| (w1 >>> 8)).extractLsb' 48 8 =
      w1.extractLsb' 56 8 := by bv_bits
  rw [h0, h1, h2, h3, h4, h5, h6]

theorem rejoin_2words_from_shifted (a a1 a8 a9 w1 w2 w3 : BitVec 64)
    (h1 : a + 1#64 = a1) (h8 : a + 8#64 = a8) (h9 : a + 9#64 = a9) (h18 : a1 + 7#64 = a8) :
    (a ↦₈ b0 w1) ∗ (a1 ↦₆₄ shiftWord8 w1 w2) ∗ low7At a9 (shiftWord8 w2 w3) ⊢
      (a ↦₆₄ w1) ∗ (a8 ↦₆₄ w2) := by
  subst h1 h8 h9
  have hmid :
      (a + 1#64) ↦₆₄ shiftWord8 w1 w2 =
        mid7At (a + 1#64) w1 ∗ ((a + 8#64) ↦₈ b0 w2) := by
    rw [← mid7_b0_eq_pointsTo64_shiftWord8 (a + 1#64) w1 w2, h18]
  have hlow : low7At (a + 9#64) (shiftWord8 w2 w3) = mid7At (a + 9#64) w2 :=
    low7At_shiftWord8_eq_mid7At (a + 9#64) w2 w3
  have h9' : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have hw1 : (a ↦₈ b0 w1) ∗ mid7At (a + 1#64) w1 = a ↦₆₄ w1 :=
    (pointsTo64_eq_b0_mid7 a w1).symm
  have hw2 : ((a + 8#64) ↦₈ b0 w2) ∗ mid7At (a + 9#64) w2 = (a + 8#64) ↦₆₄ w2 := by
    rw [← h9', ← pointsTo64_eq_b0_mid7 (a + 8#64) w2]
  rw [hmid, hlow]
  refine Entails.trans (Entails.of_eq (show
    (a ↦₈ b0 w1) ∗ (mid7At (a + 1#64) w1 ∗ ((a + 8#64) ↦₈ b0 w2)) ∗ mid7At (a + 9#64) w2 =
      ((a ↦₈ b0 w1) ∗ mid7At (a + 1#64) w1) ∗ (((a + 8#64) ↦₈ b0 w2) ∗ mid7At (a + 9#64) w2)
    by ac_rfl)) ?_
  rw [hw1, hw2]
  exact Entails.refl _

theorem sortedSetPtOf_new_of_words (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 2#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      sortedSetPtOf A v SortedSetPt.new := by
  dsimp only [sortedSetPtOf, SortedSetPt.new, vecOf, vecAt, vecHeader, vecBuf]
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 2#64 ?_)
  have h0z : ((0#64 : BitVec 64) = 0) = True := propext ⟨fun _ => trivial, fun _ => rfl⟩
  have hp : ([] : List Pt).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * ptStride < 2 ^ 63 ∧ (2#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  simp only [h0z, ↓reduceIte, sepConj_emp, List.length_nil, BitVec.ofNat_eq_ofNat]
  rw [sepConj_comm _ ⌜_⌝]
  exact Entails.pure_right hp (Entails.refl _)

theorem sortedSetPtOf_new_at (A : RustAlloc) (outA off0 off8 off16 : BitVec 64)
    (h8 : (outA + off0) + 8#64 = outA + off8)
    (h16 : (outA + off0) + 16#64 = outA + off16) :
    ((outA + off0) ↦₆₄ 0#64) ∗ ((outA + off8) ↦₆₄ 2#64) ∗ ((outA + off16) ↦₆₄ 0#64) ⊢
      sortedSetPtOf A (outA + off0) SortedSetPt.new := by
  rw [← h8, ← h16]; exact sortedSetPtOf_new_of_words A (outA + off0)

theorem polyDecoderNew96_of_slots (A : RustAlloc) (outA : BitVec 64) :
    sortedSetPtOf A (outA + 64#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 88#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 112#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 136#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 160#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 184#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 208#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 232#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 256#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 280#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 304#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 328#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 352#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 376#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 400#64) SortedSetPt.new ∗
      sortedSetPtOf A (outA + 424#64) SortedSetPt.new ∗
      ((outA + 448#64) ↦₆₄ 48#64) ∗ ((outA + 456#64) ↦₈ 0#8) ∗ memRegion (outA + 457#64) 7 ⊢
    polyDecoderAt A (outA + 64#64) polyDecoderNew96 := by
  unfold polyDecoderAt polyDecoderNew96 sortedSetPtListOf NUM_POLYS CHUNK_SIZE
  have h32 : (32 / 2 : Nat) = 16 := rfl
  rw [h32]
  dsimp only [List.replicate, arrayAt, Poly.vecHeaderBytes, polyDecoderPtsNeededOff,
    polyDecoderIsCompleteOff, polyDecoderPadOff, polyDecoderPadSize, boolByte]
  simp only [↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, emp_sepConj, sepConj_emp]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.of_eq (by ac_rfl))

theorem vecU8_of_cells_heap_32 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 32) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗ vecU8HeapAt A cap ptr bs ⊢
      vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hlen64 : BitVec.ofNat 64 bs.length = 32#64 := congrArg (BitVec.ofNat 64) hlen
  rw [vecU8At_eq_cells_heap A a cap ptr bs, hlen64]
  exact Entails.refl _

theorem vecU8_of_cells_bytes_live_32 (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 32) (hptr : ptr ≠ 0#64) :
    (a ↦₆₄ 32#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
      (ptr ↦ₛ bs) ∗ A.live ptr 32 1 ⊢
      vecU8 A a bs := by
  refine Entails.trans ?_ (vecU8_of_cells_heap_32 A a 32#64 ptr bs hlen)
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  dsimp only [vecU8HeapAt]
  have hne : (32#64 : BitVec 64) ≠ 0 := by decide
  have htoNat : (32#64 : BitVec 64).toNat = 32 := rfl
  simp only [hne, ↓reduceIte, htoNat, hlen, Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.pure_right ⟨by decide, by decide, hptr⟩ (Entails.of_eq (by ac_rfl))

theorem rejoin_outA_ok_done (A : RustAlloc) {F : ShaCompress} (outA ep : BitVec 64)
    (auth' : Authenticator) (g_auth' : AuthenticatorGhost) (ss : Bytes) (ptr_sec : BitVec 64)
    (hrk_len : auth'.rootKey.length = 32) (hmk_len : auth'.macKey.length = 32)
    (hss_len : ss.length = 32) (hptr_sec_ne : ptr_sec ≠ 0#64) :
    (outA ↦₆₄ 0xffff_ffff_ffff_ffff#64) ∗
      ((outA + 8#64) ↦₆₄ g_auth'.rootKey.cap) ∗
      ((outA + 16#64) ↦₆₄ g_auth'.rootKey.ptr) ∗
      ((outA + 24#64) ↦₆₄ 32#64) ∗
      vecU8HeapAt A g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
      ((outA + 32#64) ↦₆₄ g_auth'.macKey.cap) ∗
      ((outA + 40#64) ↦₆₄ g_auth'.macKey.ptr) ∗
      ((outA + 48#64) ↦₆₄ 32#64) ∗
      vecU8HeapAt A g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey ∗
      ((outA + 56#64) ↦₆₄ (ep + 1#64)) ∗
      polyDecoderAt A (outA + 64#64) polyDecoderNew96 ∗
      ((outA + 464#64) ↦₆₄ 32#64) ∗
      ((outA + 472#64) ↦₆₄ ptr_sec) ∗
      ((outA + 480#64) ↦₆₄ 32#64) ∗
      (ptr_sec ↦ₛ ss) ∗ A.live ptr_sec 32 1 ∗
      ((outA + 488#64) ↦₆₄ ep) ∗
      memRegion (outA + 496#64) 8 ⊢
    ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA
      (.ok (.done ({ uc := { epoch := ep + 1#64, auth := auth' },
                     receiving_hdr := polyDecoderNew96 },
                   { epoch := ep, secret := ss }))) := by
  have hrk :
      ((outA + 8#64) ↦₆₄ g_auth'.rootKey.cap) ∗
        ((outA + 16#64) ↦₆₄ g_auth'.rootKey.ptr) ∗
        ((outA + 24#64) ↦₆₄ 32#64) ∗
        vecU8HeapAt A g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ⊢
      vecU8 A (outA + 8#64) auth'.rootKey := by
    have h := vecU8_of_cells_heap_32 A (outA + 8#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey hrk_len
    have h16 : (outA + 8#64) + 8#64 = outA + 16#64 := by bv_omega
    have h24 : (outA + 8#64) + 16#64 = outA + 24#64 := by bv_omega
    rwa [h16, h24] at h
  have hmk :
      ((outA + 32#64) ↦₆₄ g_auth'.macKey.cap) ∗
        ((outA + 40#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((outA + 48#64) ↦₆₄ 32#64) ∗
        vecU8HeapAt A g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey ⊢
      vecU8 A (outA + 32#64) auth'.macKey := by
    have h := vecU8_of_cells_heap_32 A (outA + 32#64) g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey hmk_len
    have h40 : (outA + 32#64) + 8#64 = outA + 40#64 := by bv_omega
    have h48 : (outA + 32#64) + 16#64 = outA + 48#64 := by bv_omega
    rwa [h40, h48] at h
  have hsec :
      ((outA + 464#64) ↦₆₄ 32#64) ∗
        ((outA + 472#64) ↦₆₄ ptr_sec) ∗
        ((outA + 480#64) ↦₆₄ 32#64) ∗
        (ptr_sec ↦ₛ ss) ∗ A.live ptr_sec 32 1 ⊢
      vecU8 A (outA + 464#64) ss := by
    have h := vecU8_of_cells_bytes_live_32 A (outA + 464#64) ptr_sec ss hss_len hptr_sec_ne
    have h472 : (outA + 464#64) + 8#64 = outA + 472#64 := by bv_omega
    have h480 : (outA + 464#64) + 16#64 = outA + 480#64 := by bv_omega
    rwa [h472, h480] at h
  dsimp only [ekSentCt1ReceivedRecvChunkResultAt, ekSentCt1ReceivedRecvChunkAt,
    chunkedNoHeaderReceivedAt, unchunkedNoHeaderReceivedAt, authenticatorAt, epochSecretAt]
  have ha32 : (outA + 8#64) + 24#64 = outA + 32#64 := by bv_omega
  have ha56 : (outA + 8#64) + 48#64 = outA + 56#64 := by bv_omega
  have ha64 : (outA + 8#64) + 56#64 = outA + 64#64 := by bv_omega
  have ha488 : (outA + 464#64) + 24#64 = outA + 488#64 := by bv_omega
  rw [ha32, ha56, ha64, ha488]
  refine Entails.pure_right polyDecoderStrictSorted_new96 ?_
  have hgroup :
      (outA ↦₆₄ 0xffff_ffff_ffff_ffff#64) ∗
        ((outA + 8#64) ↦₆₄ g_auth'.rootKey.cap) ∗
        ((outA + 16#64) ↦₆₄ g_auth'.rootKey.ptr) ∗
        ((outA + 24#64) ↦₆₄ 32#64) ∗
        vecU8HeapAt A g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
        ((outA + 32#64) ↦₆₄ g_auth'.macKey.cap) ∗
        ((outA + 40#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((outA + 48#64) ↦₆₄ 32#64) ∗
        vecU8HeapAt A g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey ∗
        ((outA + 56#64) ↦₆₄ (ep + 1#64)) ∗
        polyDecoderAt A (outA + 64#64) polyDecoderNew96 ∗
        ((outA + 464#64) ↦₆₄ 32#64) ∗
        ((outA + 472#64) ↦₆₄ ptr_sec) ∗
        ((outA + 480#64) ↦₆₄ 32#64) ∗
        (ptr_sec ↦ₛ ss) ∗ A.live ptr_sec 32 1 ∗
        ((outA + 488#64) ↦₆₄ ep) ∗
        memRegion (outA + 496#64) 8 =
      (outA ↦₆₄ noneCap) ∗
        (((outA + 8#64) ↦₆₄ g_auth'.rootKey.cap) ∗
          ((outA + 16#64) ↦₆₄ g_auth'.rootKey.ptr) ∗
          ((outA + 24#64) ↦₆₄ 32#64) ∗
          vecU8HeapAt A g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey) ∗
        (((outA + 32#64) ↦₆₄ g_auth'.macKey.cap) ∗
          ((outA + 40#64) ↦₆₄ g_auth'.macKey.ptr) ∗
          ((outA + 48#64) ↦₆₄ 32#64) ∗
          vecU8HeapAt A g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey) ∗
        ((outA + 56#64) ↦₆₄ (ep + 1#64)) ∗
        polyDecoderAt A (outA + 64#64) polyDecoderNew96 ∗
        (((outA + 464#64) ↦₆₄ 32#64) ∗
          ((outA + 472#64) ↦₆₄ ptr_sec) ∗
          ((outA + 480#64) ↦₆₄ 32#64) ∗
          (ptr_sec ↦ₛ ss) ∗ A.live ptr_sec 32 1) ∗
        ((outA + 488#64) ↦₆₄ ep) ∗
        memRegion (outA + 496#64) 8 := by
    change _ = (outA ↦₆₄ 0xffff_ffff_ffff_ffff#64) ∗ _; ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_right (sepConj_mono hrk (sepConj_mono hmk
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsec)))))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_split_2cells (a a8 b : BitVec 64) (n k : Nat)
    (hn : n = 16 + k) (h8 : a + 8#64 = a8) (h16 : a + 16#64 = b) (hk : 16 + k ≤ 2 ^ 64) :
    memRegion a n ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (a ↦₆₄ w0) ∗ (a8 ↦₆₄ w1) ∗ memRegion b k := by
  subst hn
  have hc : memRegion a 16 = cells a 2 := ProofLib.memRegion_cells a 2 (by decide)
  rw [ProofLib.memRegion_split' (b := a) (n := 16) (k := k) (b' := b) rfl h16.symm hk, hc]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, h8, emp_sepConj, sepConj_emp, sepConj_assoc]
  exact Entails.refl _

theorem rejoin_2cells_memRegion (a a8 b w0 w1 : BitVec 64) (n k : Nat)
    (hn : n = 16 + k) (h8 : a + 8#64 = a8) (h16 : a + 16#64 = b) (hk : 16 + k ≤ 2 ^ 64) :
    (a ↦₆₄ w0) ∗ (a8 ↦₆₄ w1) ∗ memRegion b k ⊢ memRegion a n := by
  subst hn h8
  have h0 := pointsTo64_entails_memRegion_8 a w0
  have h1 := pointsTo64_entails_memRegion_8 (a + 8#64) w1
  refine Entails.trans (sepConj_mono h0 (sepConj_mono_left h1)) ?_
  rw [← sepConj_assoc,
      ← ProofLib.memRegion_split' (b := a) (n := 8) (k := 8) (b' := a + 8#64) rfl rfl (by decide),
      ← ProofLib.memRegion_split' (b := a) (n := 16) (k := k) (b' := b) rfl h16.symm hk]
  exact Entails.refl _

theorem rejoin_memRegion_40_x20_20 (sp w0 w8 w16 w23 w31 : BitVec 64) (b39 : BitVec 8) :
    ((sp - 1968#64) ↦₆₄ w0) ∗ ((sp - 1960#64) ↦₆₄ w8) ∗
      mid7At (sp - 1952#64) w16 ∗ ((sp - 1945#64) ↦₆₄ w23) ∗
      ((sp - 1937#64) ↦₆₄ w31) ∗ ((sp - 1929#64) ↦₈ b39) ⊢
      memRegion (sp - 1968#64) 40 := by
  have h0 := pointsTo64_entails_memRegion_8 (sp - 1968#64) w0
  have h8 := pointsTo64_entails_memRegion_8 (sp - 1960#64) w8
  have h16 := mid7At_entails_memRegion_7 (sp - 1952#64) w16
  have h23 := pointsTo64_entails_memRegion_8 (sp - 1945#64) w23
  have h31 := pointsTo64_entails_memRegion_8 (sp - 1937#64) w31
  have h39 := pointsTo8_entails_memRegion_1 (sp - 1929#64) b39
  refine Entails.trans (sepConj_mono h0 (sepConj_mono h8 (sepConj_mono h16
    (sepConj_mono h23 (sepConj_mono h31 h39))))) ?_
  rw [← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
  rw [← ProofLib.memRegion_split' (b := sp - 1968#64) (n := 8) (k := 8) (b' := sp - 1960#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 1968#64) (n := 16) (k := 7) (b' := sp - 1952#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 1968#64) (n := 23) (k := 8) (b' := sp - 1945#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 1968#64) (n := 31) (k := 8) (b' := sp - 1937#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 1968#64) (n := 39) (k := 1) (b' := sp - 1929#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem rejoin_memRegion_104_x20_tail (sp w40_0 w40_1 w50_0 w50_1 : BitVec 64) :
    memRegion (sp - 2000#64) 24 ∗ memRegion (sp - 1976#64) 8 ∗
      memRegion (sp - 1968#64) 40 ∗ memRegion (sp - 1928#64) 8 ∗
      ((sp - 1920#64) ↦₆₄ w40_0) ∗ ((sp - 1912#64) ↦₆₄ w40_1) ∗
      ((sp - 1904#64) ↦₆₄ w50_0) ∗ ((sp - 1896#64) ↦₆₄ w50_1) ∗
      memRegion (sp - 1888#64) 24 ∗ memRegion (sp - 1864#64) 8 ⊢
      memRegion (sp - 2000#64) 144 := by
  have h40_0 := pointsTo64_entails_memRegion_8 (sp - 1920#64) w40_0
  have h40_1 := pointsTo64_entails_memRegion_8 (sp - 1912#64) w40_1
  have h50_0 := pointsTo64_entails_memRegion_8 (sp - 1904#64) w50_0
  have h50_1 := pointsTo64_entails_memRegion_8 (sp - 1896#64) w50_1
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono h40_0 (sepConj_mono h40_1
      (sepConj_mono h50_0 (sepConj_mono_left h50_1)))))))) ?_
  rw [← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc,
      ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
  rw [← ProofLib.memRegion_split' (b := sp - 2000#64) (n := 24) (k := 8) (b' := sp - 1976#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 2000#64) (n := 32) (k := 40) (b' := sp - 1968#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 2000#64) (n := 72) (k := 8) (b' := sp - 1928#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 2000#64) (n := 80) (k := 8) (b' := sp - 1920#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 2000#64) (n := 88) (k := 8) (b' := sp - 1912#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 2000#64) (n := 96) (k := 8) (b' := sp - 1904#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 2000#64) (n := 104) (k := 8) (b' := sp - 1896#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 2000#64) (n := 112) (k := 24) (b' := sp - 1888#64) rfl (by bv_omega) (by decide)]
  rw [← ProofLib.memRegion_split' (b := sp - 2000#64) (n := 136) (k := 8) (b' := sp - 1864#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem memRegion_104_x20_eq (sp : BitVec 64) :
    memRegion (sp - 2000#64) 32 ∗ memRegion (sp - 1928#64) 72 =
      memRegion (sp - 2000#64) 24 ∗ memRegion (sp - 1976#64) 8 ∗
      memRegion (sp - 1928#64) 8 ∗ memRegion (sp - 1920#64) 16 ∗
      memRegion (sp - 1904#64) 16 ∗ memRegion (sp - 1888#64) 24 ∗
      memRegion (sp - 1864#64) 8 := by
  rw [ProofLib.memRegion_split' (b := sp - 2000#64) (n := 24) (k := 8) (b' := sp - 1976#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_split' (b := sp - 1928#64) (n := 8) (k := 64) (b' := sp - 1920#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_split' (b := sp - 1920#64) (n := 16) (k := 48) (b' := sp - 1904#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_split' (b := sp - 1904#64) (n := 16) (k := 32) (b' := sp - 1888#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_split' (b := sp - 1888#64) (n := 24) (k := 8) (b' := sp - 1864#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem memRegion_24_split_1_16_7 (a : BitVec 64) :
    memRegion a 24 ⊢
      ∃∗ b0_val : BitVec 8, ∃∗ w1 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w16 : BitVec 64,
        (a ↦₈ b0_val) ∗ ((a + 1#64) ↦₆₄ w1) ∗ ((a + 9#64) ↦₆₄ w9) ∗ mid7At (a + 17#64) w16 := by
  have hc : memRegion a 24 = cells a 3 := ProofLib.memRegion_cells a 3 (by decide)
  rw [hc]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]
  refine Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 => Entails.sepExists_elim fun u2 => ?_
  refine Entails.sepExists_right (b0 u0) (Entails.sepExists_right (shiftWord8 u0 u1)
    (Entails.sepExists_right (shiftWord8 u1 u2) (Entails.sepExists_right u2 ?_)))
  have h9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have h17 : (a + 16#64) + 1#64 = a + 17#64 := by bv_omega
  have h8 : (a + 1#64) + 7#64 = a + 8#64 := by bv_omega
  have h16 : (a + 9#64) + 7#64 = a + 16#64 := by bv_omega
  rw [pointsTo64_eq_b0_mid7 a u0, pointsTo64_eq_b0_mid7 (a + 8#64) u1, h9,
      pointsTo64_eq_b0_mid7 (a + 16#64) u2, h17,
      ← mid7_b0_eq_pointsTo64_shiftWord8 (a + 1#64) u0 u1, h8,
      ← mid7_b0_eq_pointsTo64_shiftWord8 (a + 9#64) u1 u2, h16]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_split_4cells (a a8 a16 a24 b : BitVec 64) (n k : Nat)
    (hn : n = 32 + k) (h8 : a + 8#64 = a8) (h16 : a8 + 8#64 = a16) (h24 : a16 + 8#64 = a24)
    (h32 : a + 32#64 = b) (hk : 32 + k ≤ 2 ^ 64) :
    memRegion a n ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (a ↦₆₄ w0) ∗ (a8 ↦₆₄ w1) ∗ (a16 ↦₆₄ w2) ∗ (a24 ↦₆₄ w3) ∗ memRegion b k := by
  subst hn
  have hc : memRegion a 32 = cells a 4 := ProofLib.memRegion_cells a 4 (by decide)
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := k) (b' := b) rfl h32.symm hk, hc]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, h8, h16, h24, emp_sepConj, sepConj_emp, sepConj_assoc]
  exact Entails.refl _

theorem memRegion_split_8cells (a a8 a16 a24 a32 a40 a48 a56 b : BitVec 64) (n k : Nat)
    (hn : n = 64 + k) (h8 : a + 8#64 = a8) (h16 : a8 + 8#64 = a16) (h24 : a16 + 8#64 = a24)
    (h32 : a24 + 8#64 = a32) (h40 : a32 + 8#64 = a40) (h48 : a40 + 8#64 = a48)
    (h56 : a48 + 8#64 = a56) (h64 : a + 64#64 = b) (hk : 64 + k ≤ 2 ^ 64) :
    memRegion a n ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        (a ↦₆₄ w0) ∗ (a8 ↦₆₄ w1) ∗ (a16 ↦₆₄ w2) ∗ (a24 ↦₆₄ w3) ∗
        (a32 ↦₆₄ w4) ∗ (a40 ↦₆₄ w5) ∗ (a48 ↦₆₄ w6) ∗ (a56 ↦₆₄ w7) ∗ memRegion b k := by
  subst hn
  have hc : memRegion a 64 = cells a 8 := ProofLib.memRegion_cells a 8 (by decide)
  rw [ProofLib.memRegion_split' (b := a) (n := 64) (k := k) (b' := b) rfl h64.symm hk, hc]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, h8, h16, h24, h32, h40, h48, h56,
    emp_sepConj, sepConj_emp, sepConj_assoc]
  exact Entails.refl _

@[simp] theorem extractLsb8_zeroExtend32_zeroExtend64 (b : BitVec 8) :
    BitVec.extractLsb' 0 8 (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 b))) = b := by
  bv_bits

@[simp] theorem truncate8_zeroExtend32_zeroExtend64 (b : BitVec 8) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 b))) = b := by
  bv_bits

@[simp] theorem q0_zero_combine :
    (BitVec.zeroExtend 128 0#64 ||| BitVec.zeroExtend 128 0#64 <<< 64) = 0#128 := rfl

@[simp] theorem extractLsb_low64_zero128 :
    BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[simp] theorem extractLsb_high64_zero128 :
    BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

theorem rejoin_someBranchFrameAt_part2a (sp w40_0 w40_1 w4c0_0 w4c0_1 : BitVec 64) :
    memRegion (sp - 2000#64) 80 ∗ ((sp - 1920#64) ↦₆₄ w40_0) ∗ ((sp - 1912#64) ↦₆₄ w40_1) ∗
      memRegion (sp - 1904#64) 48 ∗
      memRegion (sp - 1344#64) 16 ∗
      memRegion (sp - 1328#64) 48 ∗
      ((sp - 1280#64) ↦₆₄ w4c0_0) ∗ ((sp - 1272#64) ↦₆₄ w4c0_1) ∗
      memRegion (sp - 1264#64) 8 ∗
      memRegion (sp - 1248#64) 960 ∗
      memRegion (sp - 288#64) 128 ∗
      memRegion (sp - 152#64) 32 ∗
      unusedFrameAt (sp - 2496#64) ⊢
      someBranchFrameAt (sp - 2496#64) := by
  have h1 :
      ((sp - 1920#64) ↦₆₄ w40_0) ∗ ((sp - 1912#64) ↦₆₄ w40_1) ∗ memRegion (sp - 1904#64) 48 ⊢
        memRegion (sp - 1920#64) 64 :=
    rejoin_2cells_memRegion (sp - 1920#64) (sp - 1912#64) (sp - 1904#64) w40_0 w40_1 64 48
      rfl (by bv_omega) (by bv_omega) (by decide)
  have h2 :
      ((sp - 1280#64) ↦₆₄ w4c0_0) ∗ ((sp - 1272#64) ↦₆₄ w4c0_1) ∗ memRegion (sp - 1264#64) 8 ⊢
        memRegion (sp - 1280#64) 24 :=
    rejoin_2cells_memRegion (sp - 1280#64) (sp - 1272#64) (sp - 1264#64) w4c0_0 w4c0_1 24 8
      rfl (by bv_omega) (by bv_omega) (by decide)
  have hgroup :
      memRegion (sp - 2000#64) 80 ∗ ((sp - 1920#64) ↦₆₄ w40_0) ∗ ((sp - 1912#64) ↦₆₄ w40_1) ∗
        memRegion (sp - 1904#64) 48 ∗
        memRegion (sp - 1344#64) 16 ∗
        memRegion (sp - 1328#64) 48 ∗
        ((sp - 1280#64) ↦₆₄ w4c0_0) ∗ ((sp - 1272#64) ↦₆₄ w4c0_1) ∗
        memRegion (sp - 1264#64) 8 ∗
        memRegion (sp - 1248#64) 960 ∗
        memRegion (sp - 288#64) 128 ∗
        memRegion (sp - 152#64) 32 ∗
        unusedFrameAt (sp - 2496#64) =
      memRegion (sp - 2000#64) 80 ∗
        (((sp - 1920#64) ↦₆₄ w40_0) ∗ ((sp - 1912#64) ↦₆₄ w40_1) ∗ memRegion (sp - 1904#64) 48) ∗
        memRegion (sp - 1344#64) 16 ∗
        memRegion (sp - 1328#64) 48 ∗
        (((sp - 1280#64) ↦₆₄ w4c0_0) ∗ ((sp - 1272#64) ↦₆₄ w4c0_1) ∗ memRegion (sp - 1264#64) 8) ∗
        memRegion (sp - 1248#64) 960 ∗
        memRegion (sp - 288#64) 128 ∗
        memRegion (sp - 152#64) 32 ∗
        unusedFrameAt (sp - 2496#64) := by ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h2))))) ?_
  unfold someBranchFrameAt
  have ha1 : (sp - 2496#64) + 496#64 = sp - 2000#64 := by bv_omega
  have ha2 : (sp - 2496#64) + 1152#64 = sp - 1344#64 := by bv_omega
  have ha3 : (sp - 2496#64) + 1168#64 = sp - 1328#64 := by bv_omega
  have ha4 : (sp - 2496#64) + 1216#64 = sp - 1280#64 := by bv_omega
  have ha5 : (sp - 2496#64) + 1248#64 = sp - 1248#64 := by bv_omega
  have ha6 : (sp - 2496#64) + 2208#64 = sp - 288#64 := by bv_omega
  have ha7 : (sp - 2496#64) + 2344#64 = sp - 152#64 := by bv_omega
  rw [ha1, ha2, ha3, ha4, ha5, ha6, ha7]
  rw [ProofLib.memRegion_split' (b := sp - 2000#64) (n := 80) (k := 64) (b' := sp - 1920#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_8_eq_cell (a : BitVec 64) :
    memRegion a 8 ⊢ ∃∗ w0 : BitVec 64, a ↦₆₄ w0 := by
  have hc : memRegion a 8 = cells a 1 := ProofLib.memRegion_cells a 1 (by decide)
  rw [hc]; dsimp only [cells]; simp only [sepConj_emp]; exact Entails.refl _

theorem memRegion_8_split_1_7 (a a1 : BitVec 64) (h1 : a + 1#64 = a1) :
    memRegion a 8 ⊢ ∃∗ b0_val : BitVec 8, (a ↦₈ b0_val) ∗ memRegion a1 7 := by
  subst h1
  refine Entails.trans (memRegion_8_eq_cell a) ?_
  refine Entails.sepExists_elim fun w0 => Entails.sepExists_right (b0 w0) ?_
  rw [pointsTo64_eq_b0_mid7 a w0]
  exact sepConj_mono_right (mid7At_entails_memRegion_7 (a + 1#64) w0)

theorem rejoin_2cells_16 (a a8 w0 w1 : BitVec 64) (h8 : a + 8#64 = a8) :
    (a ↦₆₄ w0) ∗ (a8 ↦₆₄ w1) ⊢ memRegion a 16 := by
  subst h8
  have h0 := pointsTo64_entails_memRegion_8 a w0
  have h1 := pointsTo64_entails_memRegion_8 (a + 8#64) w1
  refine Entails.trans (sepConj_mono h0 h1) ?_
  rw [← ProofLib.memRegion_split' (b := a) (n := 8) (k := 8) (b' := a + 8#64) rfl rfl (by decide)]
  exact Entails.refl _

theorem rejoin_cells_9 (sp w0 w1 w2 w3 : BitVec 64) :
    ((sp - 2496#64) ↦₆₄ w0) ∗ ((sp - 2488#64) ↦₆₄ w1) ∗
      ((sp - 2480#64) ↦₆₄ w2) ∗ ((sp - 2472#64) ↦₆₄ w3) ∗
      cells (sp - 2464#64) 5 ⊢
    cells (sp - 2496#64) 9 := by
  have h8 : (sp - 2496#64) + 8#64 = sp - 2488#64 := by bv_omega
  have h16 : (sp - 2488#64) + 8#64 = sp - 2480#64 := by bv_omega
  have h24 : (sp - 2480#64) + 8#64 = sp - 2472#64 := by bv_omega
  have h32 : (sp - 2472#64) + 8#64 = sp - 2464#64 := by bv_omega
  dsimp only [cells]
  refine Entails.sepExists_right w0 (sepConj_mono_right ?_)
  rw [h8]
  refine Entails.sepExists_right w1 (sepConj_mono_right ?_)
  rw [h16]
  refine Entails.sepExists_right w2 (sepConj_mono_right ?_)
  rw [h24]
  refine Entails.sepExists_right w3 (sepConj_mono_right ?_)
  rw [h32]
  exact Entails.refl _

theorem memRegion_24_eq_3cells (a a8 a16 : BitVec 64)
    (h8 : a + 8#64 = a8) (h16 : a8 + 8#64 = a16) :
    memRegion a 24 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (a ↦₆₄ w0) ∗ (a8 ↦₆₄ w1) ∗ (a16 ↦₆₄ w2) := by
  have hc : memRegion a 24 = cells a 3 := ProofLib.memRegion_cells a 3 (by decide)
  rw [hc]; dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, h8, h16,
    emp_sepConj, sepConj_emp, sepConj_assoc]
  exact Entails.refl _

@[simp] theorem extractLsb_low64_qpair (lo hi : BitVec 64) :
    BitVec.extractLsb' 0 64 (BitVec.zeroExtend 128 lo ||| BitVec.zeroExtend 128 hi <<< 64) = lo := by
  bv_bits

@[simp] theorem extractLsb_high64_qpair (lo hi : BitVec 64) :
    BitVec.extractLsb' 64 64 (BitVec.zeroExtend 128 lo ||| BitVec.zeroExtend 128 hi <<< 64) = hi := by
  bv_bits

theorem left_and_mid7_to_mid_at_7_shift (a8 a15 a16 w2 w3 : BitVec 64)
    (h15 : a8 + 7#64 = a15) (h16 : a8 + 8#64 = a16) :
    (a8 ↦₆₄ shiftWord8 w2 w3) ∗ mid7At a16 w3 =
      low7At a8 (shiftWord8 w2 w3) ∗ (a15 ↦₆₄ w3) := by
  rw [mid7At_eq_low7At a16 w3,
      left_and_low7_to_mid_at_7 a8 a15 a16 (shiftWord8 w2 w3) (w3 >>> 8) h15.symm h16.symm,
      unshift_shift_shr8_eq w2 w3]

theorem mid_at_7_to_left_shift (a8 a15 a16 w2 w3 : BitVec 64)
    (h15 : a8 + 7#64 = a15) (h16 : a8 + 8#64 = a16) :
    low7At a8 (shiftWord8 w2 w3) ∗ (a15 ↦₆₄ w3) =
      (a8 ↦₆₄ shiftWord8 w2 w3) ∗ mid7At a16 w3 :=
  (left_and_mid7_to_mid_at_7_shift a8 a15 a16 w2 w3 h15 h16).symm

theorem left_and_mid7_to_mid_at_7_any (a8 a15 a16 w1 w2 : BitVec 64)
    (h15 : a8 + 7#64 = a15) (h16 : a8 + 8#64 = a16) :
    (a8 ↦₆₄ w1) ∗ mid7At a16 w2 =
      low7At a8 w1 ∗ (a15 ↦₆₄ unshiftWord8 w1 (w2 >>> 8)) := by
  rw [mid7At_eq_low7At a16 w2, left_and_low7_to_mid_at_7 a8 a15 a16 w1 (w2 >>> 8) h15.symm h16.symm]

end Part3bHelpers

section Part3cHelpers
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  recvCt2Chunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff mlkemDecaps_fnOff
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff doReserve7_fnOff_eq
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x67028
  libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x58ac4
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x46920
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5e5f0
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::result::unwrap_failed") (ls_hook% "core::result::unwrap_failed")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")

/-! ## Helper Lemmas for `Ok(Done)` Header Staging and Deallocations -/

theorem add_one_ult_self_eq_beq_allOnes (ep : BitVec 64) :
    (ep + 1#64).ult ep = (ep == BitVec.allOnes 64) := by
  by_cases h : ep = BitVec.allOnes 64
  · subst h; decide
  · have hbeq : (ep == BitVec.allOnes 64) = false := beq_false_of_ne h
    have hlt : ep.toNat < 0xffff_ffff_ffff_ffff := by
      have hne : ep.toNat ≠ 0xffff_ffff_ffff_ffff := fun heq => h (BitVec.eq_of_toNat_eq heq)
      have hbound := ep.isLt
      omega
    have hult : (ep + 1#64).ult ep = false := by
      rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
      have h1 : (ep + 1#64).toNat = ep.toNat + 1 := by
        rw [BitVec.toNat_add]
        have : (1#64 : BitVec 64).toNat = 1 := rfl
        rw [this, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hult, hbeq]

theorem bytes_rem_entails_vecU8HeapAt_32 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 32) (hcap_ne : cap ≠ 0#64) (hle : 32 ≤ cap.toNat)
    (hmax : cap.toNat < 2 ^ 63) (hptr_ne : ptr ≠ 0#64) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + 32#64) (cap.toNat - 32) ∗ A.live ptr cap.toNat 1 ⊢
      vecU8HeapAt A cap ptr bs := by
  dsimp only [vecU8HeapAt]
  have hcap_ne' : cap ≠ 0 := hcap_ne
  have hlen64 : BitVec.ofNat 64 bs.length = 32#64 := congrArg (BitVec.ofNat 64) hlen
  simp only [hcap_ne', ↓reduceIte, hlen64, hlen]
  exact Entails.pure_right ⟨hle, hmax, hptr_ne⟩ (Entails.of_eq (by ac_rfl))

theorem vecU8At_expose_cells_heap_sp_1328 (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 32) :
    vecU8At A (sp - 1328#64) cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      ((sp - 1328#64) ↦₆₄ cap) ∗ ((sp - 1320#64) ↦₆₄ ptr) ∗ ((sp - 1312#64) ↦₆₄ 32#64) ∗
      vecU8HeapAt A cap ptr bs := by
  rw [vecU8At_eq_cells_heap A (sp - 1328#64) cap ptr bs]
  have hlen64 : BitVec.ofNat 64 bs.length = 32#64 := congrArg (BitVec.ofNat 64) hlen
  have ha8 : (sp - 1328#64) + 8#64 = sp - 1320#64 := by bv_omega
  have ha16 : (sp - 1328#64) + 16#64 = sp - 1312#64 := by bv_omega
  rw [hlen64, ha8, ha16]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_pure_bounds A cap ptr bs)))) ?_
  have hcomm :
      ((sp - 1328#64) ↦₆₄ cap) ∗ ((sp - 1320#64) ↦₆₄ ptr) ∗ ((sp - 1312#64) ↦₆₄ 32#64) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗ vecU8HeapAt A cap ptr bs) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (((sp - 1328#64) ↦₆₄ cap) ∗ ((sp - 1320#64) ↦₆₄ ptr) ∗ ((sp - 1312#64) ↦₆₄ 32#64) ∗
          vecU8HeapAt A cap ptr bs) := by ac_rfl
  rw [hcomm]
  apply Entails.pure_left; rintro ⟨_, hmax, _⟩
  exact Entails.pure_right hmax (Entails.refl _)

theorem shift_5words_1320 (sp w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp - 1320#64) ↦₆₄ w1) ∗ ((sp - 1312#64) ↦₆₄ w2) ∗
      ((sp - 1304#64) ↦₆₄ w3) ∗ ((sp - 1296#64) ↦₆₄ w4) ∗
      ((sp - 1288#64) ↦₆₄ w5) =
    ((sp - 1320#64) ↦₈ b0 w1) ∗
      ((sp - 1319#64) ↦₆₄ shiftWord8 w1 w2) ∗
      ((sp - 1311#64) ↦₆₄ shiftWord8 w2 w3) ∗
      ((sp - 1303#64) ↦₆₄ shiftWord8 w3 w4) ∗
      ((sp - 1295#64) ↦₆₄ shiftWord8 w4 w5) ∗
      mid7At (sp - 1287#64) w5 := by
  have ha1 : (sp - 1320#64) + 1#64 = sp - 1319#64 := by bv_omega
  have hb1 : (sp - 1319#64) + 7#64 = sp - 1312#64 := by bv_omega
  have ha2 : (sp - 1312#64) + 1#64 = sp - 1311#64 := by bv_omega
  have hb2 : (sp - 1311#64) + 7#64 = sp - 1304#64 := by bv_omega
  have ha3 : (sp - 1304#64) + 1#64 = sp - 1303#64 := by bv_omega
  have hb3 : (sp - 1303#64) + 7#64 = sp - 1296#64 := by bv_omega
  have ha4 : (sp - 1296#64) + 1#64 = sp - 1295#64 := by bv_omega
  have hb4 : (sp - 1295#64) + 7#64 = sp - 1288#64 := by bv_omega
  have ha5 : (sp - 1288#64) + 1#64 = sp - 1287#64 := by bv_omega
  rw [pointsTo64_eq_b0_mid7 (sp - 1320#64) w1, ha1,
      pointsTo64_eq_b0_mid7 (sp - 1312#64) w2, ha2,
      pointsTo64_eq_b0_mid7 (sp - 1304#64) w3, ha3,
      pointsTo64_eq_b0_mid7 (sp - 1296#64) w4, ha4,
      pointsTo64_eq_b0_mid7 (sp - 1288#64) w5, ha5,
      ← mid7_b0_eq_pointsTo64_shiftWord8 (sp - 1319#64) w1 w2, hb1,
      ← mid7_b0_eq_pointsTo64_shiftWord8 (sp - 1311#64) w2 w3, hb2,
      ← mid7_b0_eq_pointsTo64_shiftWord8 (sp - 1303#64) w3 w4, hb3,
      ← mid7_b0_eq_pointsTo64_shiftWord8 (sp - 1295#64) w4 w5, hb4]
  ac_rfl

theorem reshape_x20_1960_to_1929 (sp a b c d z4 : BitVec 64) :
    ((sp - 1960#64) ↦₆₄ shiftWord8 a b) ∗
      ((sp - 1952#64) ↦₆₄ shiftWord8 b c) ∗
      ((sp - 1944#64) ↦₆₄ shiftWord8 c d) ∗
      ((sp - 1936#64) ↦₆₄ z4) =
    low7At (sp - 1960#64) (shiftWord8 a b) ∗
      ((sp - 1953#64) ↦₆₄ b) ∗
      ((sp - 1945#64) ↦₆₄ c) ∗
      ((sp - 1937#64) ↦₆₄ unshiftWord8 (shiftWord8 c d) z4) ∗
      ((sp - 1929#64) ↦₈ b7 z4) := by
  have h29 : (sp - 1936#64) + 7#64 = sp - 1929#64 := by bv_omega
  rw [pointsTo64_eq_low7_b7 (sp - 1936#64) z4, h29]
  have h1 := left_and_low7_to_mid_at_7 (sp - 1944#64) (sp - 1937#64) (sp - 1936#64)
    (shiftWord8 c d) z4 (by bv_omega) (by bv_omega)
  have h2 := left_and_low7_to_mid_at_7 (sp - 1952#64) (sp - 1945#64) (sp - 1944#64)
    (shiftWord8 b c) (shiftWord8 c d) (by bv_omega) (by bv_omega)
  have h3 := left_and_low7_to_mid_at_7 (sp - 1960#64) (sp - 1953#64) (sp - 1952#64)
    (shiftWord8 a b) (shiftWord8 b c) (by bv_omega) (by bv_omega)
  rw [unshift_shift_eq b c d] at h2
  rw [unshift_shift_eq a b c] at h3
  have hassoc1 :
      ((sp - 1960#64) ↦₆₄ shiftWord8 a b) ∗
        ((sp - 1952#64) ↦₆₄ shiftWord8 b c) ∗
        ((sp - 1944#64) ↦₆₄ shiftWord8 c d) ∗
        (low7At (sp - 1936#64) z4 ∗ ((sp - 1929#64) ↦₈ b7 z4)) =
      ((sp - 1960#64) ↦₆₄ shiftWord8 a b) ∗
        ((sp - 1952#64) ↦₆₄ shiftWord8 b c) ∗
        (((sp - 1944#64) ↦₆₄ shiftWord8 c d) ∗ low7At (sp - 1936#64) z4) ∗
        ((sp - 1929#64) ↦₈ b7 z4) := by ac_rfl
  rw [hassoc1, h1]
  have hassoc2 :
      ((sp - 1960#64) ↦₆₄ shiftWord8 a b) ∗
        ((sp - 1952#64) ↦₆₄ shiftWord8 b c) ∗
        (low7At (sp - 1944#64) (shiftWord8 c d) ∗ ((sp - 1937#64) ↦₆₄ unshiftWord8 (shiftWord8 c d) z4)) ∗
        ((sp - 1929#64) ↦₈ b7 z4) =
      ((sp - 1960#64) ↦₆₄ shiftWord8 a b) ∗
        (((sp - 1952#64) ↦₆₄ shiftWord8 b c) ∗ low7At (sp - 1944#64) (shiftWord8 c d)) ∗
        ((sp - 1937#64) ↦₆₄ unshiftWord8 (shiftWord8 c d) z4) ∗
        ((sp - 1929#64) ↦₈ b7 z4) := by ac_rfl
  rw [hassoc2, h2]
  have hassoc3 :
      ((sp - 1960#64) ↦₆₄ shiftWord8 a b) ∗
        (low7At (sp - 1952#64) (shiftWord8 b c) ∗ ((sp - 1945#64) ↦₆₄ c)) ∗
        ((sp - 1937#64) ↦₆₄ unshiftWord8 (shiftWord8 c d) z4) ∗
        ((sp - 1929#64) ↦₈ b7 z4) =
      (((sp - 1960#64) ↦₆₄ shiftWord8 a b) ∗ low7At (sp - 1952#64) (shiftWord8 b c)) ∗
        ((sp - 1945#64) ↦₆₄ c) ∗
        ((sp - 1937#64) ↦₆₄ unshiftWord8 (shiftWord8 c d) z4) ∗
        ((sp - 1929#64) ↦₈ b7 z4) := by ac_rfl
  rw [hassoc3, h3]
  ac_rfl

theorem fold_4cells_memRegion_32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [memRegion_32_cells a]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))

theorem rejoin_cells_5_sp_2464 (sp w4 w5 w6 w7 w8 : BitVec 64) :
    ((sp - 2464#64) ↦₆₄ w4) ∗ ((sp - 2456#64) ↦₆₄ w5) ∗
      ((sp - 2448#64) ↦₆₄ w6) ∗ ((sp - 2440#64) ↦₆₄ w7) ∗
      ((sp - 2432#64) ↦₆₄ w8) ⊢
      cells (sp - 2464#64) 5 := by
  dsimp only [cells]
  have ha1 : (sp - 2464#64) + 8#64 = sp - 2456#64 := by bv_omega
  have ha2 : (sp - 2456#64) + 8#64 = sp - 2448#64 := by bv_omega
  have ha3 : (sp - 2448#64) + 8#64 = sp - 2440#64 := by bv_omega
  have ha4 : (sp - 2440#64) + 8#64 = sp - 2432#64 := by bv_omega
  simp only [ha1, ha2, ha3, ha4, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp]
  exact Entails.sepExists_right w4 (Entails.sepExists_right w5
    (Entails.sepExists_right w6 (Entails.sepExists_right w7
      (Entails.sepExists_right w8 (Entails.refl _)))))

theorem vecBufAt_zero_entails_emp (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (h0 : bs = []) :
    vecBufAt A 0#64 ptr bs ⊢ emp := by
  subst h0
  dsimp only [vecBufAt]
  have h0z : ((0#64 : BitVec 64) = 0) = True := propext ⟨fun _ => trivial, fun _ => rfl⟩
  simp only [h0z, ↓reduceIte, pointsToBytes_nil, sepConj_emp]
  exact Entails.refl emp

/-! ## `Ok(Done)` Epoch Check, `secret` Alloc, Header Staging & 7-Buffer Dealloc (`0x5f148 .. 0x5f21c`) -/

end Part3cHelpers

end CryptoVerification.SpqrV1.States.RecvCt2Chunk

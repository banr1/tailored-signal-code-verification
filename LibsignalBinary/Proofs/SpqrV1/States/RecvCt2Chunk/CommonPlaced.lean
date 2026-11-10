/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Common
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVec
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Common
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Relocatable Shared Helpers

Defines `lsProg_350` (`blockProgram lsmpl 350`), fetch macros, and relocatable framing
and callee bridges for `<EkSentCt1Received>::recv_ct2_chunk` (`514` instructions).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.RecvCt2Chunk

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Kdf
open NextKeyInternalFacts

/-! ## `.rodata` Bundle and Postcondition Abbreviations -/

/-- The three `.rodata` slices accessed by `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`). -/
abbrev recvCt2RoPlacedAt [LibsignalPlacement] : SepProp :=
  ((lsρ sckaKeyInfoPrefixSym) ↦ᵣ sckaKeyInfoPrefix) ∗
    ((lsρ zeros32Sym) ↦ᵣ List.replicate 32 0#8) ∗
    ((lsρ ctLabelSym) ↦ᵣ Authenticator.ctLabel)

/-- Normal-return `SepWPp` postcondition predicate for Block `350` segments. -/
abbrev recvCt2PlacedPostQ [LibsignalPlacement] (K : MlKem) (F : ShaCompress) (A : RustAlloc)
    (x : RecvCt2ChunkGhost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (((lsρ sckaKeyInfoPrefixSym) ↦ᵣ sckaKeyInfoPrefix) ∗
          ((lsρ zeros32Sym) ↦ᵣ List.replicate 32 0#8) ∗
          ((lsρ ctLabelSym) ↦ᵣ Authenticator.ctLabel) ∗
          (recvCt2ChunkPlacedSpec K F A).post x s0 sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Panic `SepWPp` postcondition predicate for Block `350` segments. -/
abbrev recvCt2PlacedPostQp [LibsignalPlacement] (K : MlKem) (F : ShaCompress) (A : RustAlloc)
    (x : RecvCt2ChunkGhost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (recvCt2ChunkPlacedSpec K F A).onPanic x s0 sf ∗ R)

/-! ## `LibsignalCodeRoLoaded`-Preserving `SepWPp` Sequencing and Call Tactic -/

theorem SepWPp.of_sepWP_lscro {prog : Program} {pl : Arm64.Obj.MultiPlacement}
    {mid target_pc : BitVec 64} {s : State} {P : SepProp}
    {post postPanic : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded pl sm.mem → SepWPp prog target_pc sm Pm post postPanic)) :
    SepWPp prog target_pc s P post postPanic :=
  Leaves.of_sepWP_lscro hinv h

/-- Absorb a spatial frame `F_frame` into a panic postcondition ending in `∗ anyHeap`. -/
theorem anyHeap_absorb_right (P F_frame : SepProp) :
    (P ∗ anyHeap) ∗ F_frame ⊢ P ∗ anyHeap := by
  rw [sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap (anyHeap ∗ F_frame))

/-- Mid-function `SepWPp` call rule for `withLsCodeRoLoaded pl spec` when the outer panic
    postcondition has the shape `⌜φ sf⌝ ∗ anyHeap` (such as `(recvCt2ChunkPlacedSpec K F A).onPanic`). -/
theorem SepWPp.call_allowPanic_lscro_recvCt2 {α : Type} {prog : Program}
    {pl : Arm64.Obj.MultiPlacement} {entry ret_pc target_pc : BitVec 64}
    {spec : Spec α} {x : α} {F_frame R : SepProp}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {φ : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hinv : LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F_frame ∗ R')))
    (hpanic : ∀ sf, spec.onPanic x s sf ∗ F_frame ⊢ ⌜φ sf⌝ ∗ anyHeap)
    (herr : (∀ sf code, spec.onExit x code s sf = ⌜False⌝) ∧
            (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F_frame) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜φ sf⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜φ sf⌝ ∗ anyHeap) ∗ R)) := by
  refine Leaves.sepWPp_call_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hinv hcall
    (x := x) (F := F_frame) hpc hrun hsp hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm (spec.pre x s), satisfies_pure_sepConj]
    exact ⟨hinv, hpre R' hm⟩
  · intro sf code R' _ hex
    dsimp only [withLsCodeRoLoaded] at hex
    rw [herr.1 sf code, satisfies_pure_sepConj] at hex
    exact hex.1
  · intro sf _ hmem
    dsimp only [withLsCodeRoLoaded] at hmem
    exact Satisfies.mono (sepConj_mono_left (hpanic sf)) hmem
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf
    exact hnext sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf
  · intro sf R' _ hoom_m
    dsimp only [withLsCodeRoLoaded] at hoom_m
    rw [herr.2 sf, satisfies_pure_sepConj] at hoom_m
    exact False.elim hoom_m.1

open Lean Elab Tactic Meta in
/-- Relocatable counterpart of `wpp_call_inImage_recvCt2`: discharges a mid-function call
    to `hcall : subroutine_ok _ _ (withLsCodeRoLoaded lsmpl spec)` with ghost argument `a`
    and `hinv : LibsignalCodeRoLoaded lsmpl s.mem`, handling pure-false, alloc-fail, and
    HMAC panic specs uniformly. -/
elab "wpp_call_lscro_recvCt2 " hcall:term:max a:term:max hinv:term:max : tactic => do
  let hcallCopyId ← freshIdent `hcall_copy
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    have $hcallCopyId := $hcall
    apply (SepWPp.call_allowPanic_lscro_recvCt2 $hcallCopyId (x := $a) $hinv)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_lscro_recvCt2: unexpected subgoals"
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
      | exact Entails.pure_left False.elim
      | (repeat rw [sepConj_assoc]; exact Entails.pure_left False.elim)
      | (repeat rw [← sepConj_assoc]; exact Entails.pure_left False.elim))
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
          if nm != ``Arm64.Spec.mk && nm != ``Arm64.Spec.inImage &&
              nm != ``withLsCodeRoLoaded then
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

/-! ## `SplitBytes` Memcpy Bridge for `withLsCodeRoLoaded` -/

theorem SplitBytes.memcpy_withStack_ok {prog : Program} {entry : BitVec 64}
    {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) (hn : n < 2 ^ 64) (hookStack : Nat)
    (hmc : subroutine_ok prog entry (withStack sessionMemcpyRegionSpec hookStack)) :
    subroutine_ok prog entry (withStack S.memcpySpec hookStack) := by
  apply subroutine_ok_outcome_intro
  intro ⟨dst, src⟩ R0 s_c hpc_c hrun_c hpre_c hsp_c
  dsimp only [withStack, SplitBytes.memcpySpec] at hpre_c
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre_c
  rcases hpre_c with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (S.to_bytes src))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  rcases h2 with ⟨bs, h3⟩
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  rcases h3 with ⟨hlen, h4⟩
  have hpre_mc : s_c.mem ⊨ (withStack sessionMemcpyRegionSpec hookStack).pre (dst, src, bs) s_c ∗
      (S.heap bs ∗ R0) := by
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]⟩, ?_⟩
    rw [hlen]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h4
  refine subroutine_ok.mono_outcome hmc (dst, src, bs) (S.heap bs ∗ R0) s_c hpc_c hrun_c hpre_mc hsp_c ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_sf, htr_sf⟩, hpost_mem⟩
    dsimp only [withStack, SplitBytes.memcpySpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr_sf, hx0_sf⟩, ?_⟩
    have harrange :
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt s_c.sp hookStack ∗ (S.heap bs ∗ R0) =
        (((dst ↦ₛ bs) ∗ S.heap bs) ∗ (src ↦ₛ bs)) ∗ stackAt s_c.sp hookStack ∗ R0 := by ac_rfl
    rw [harrange] at hpost_mem
    have hsrc_mr : (src ↦ₛ bs) ⊢ memRegion src n := hlen ▸ pointsToBytes_entails_memRegion src bs
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono (S.of_bytes dst bs hlen) hsrc_mr)) hpost_mem
  · right; left
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; left
    refine ⟨code, hex, ?_⟩
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; right
    refine ⟨hoom, ?_⟩
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

theorem SplitBytes.memcpy_withStack_lscro_ok {pl : Arm64.Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) (hn : n < 2 ^ 64) (hookStack : Nat)
    (hmc : subroutine_ok prog entry (withStack sessionMemcpyRegionSpec hookStack)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl (withStack S.memcpySpec hookStack)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_plain (S.memcpy_withStack_ok hn hookStack hmc)

/-! ## Extern Symbol Names, Hook Bundle, Panic Symbols, and Cross-Block Callee Bridges -/

abbrev spqrRustDeallocSym' : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

abbrev spqrMlkemDecapsSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key"

abbrev spqrLibcruxHmacSym' : String :=
  "_RNvCs65XVORQObL2_12libcrux_hmac4hmac"

abbrev spqrAssertFailedU64Sym : String :=
  "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_"

abbrev spqrSliceIndexFailSym : String :=
  "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail"

abbrev spqrUnwrapFailedSym : String :=
  "_RNvNtCskxtBwYRO61I_4core6result13unwrap_failed"

abbrev spqrPanicBoundsCheckSym : String :=
  "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check"

/-- Standard allocator, `memcpy`, and panic hypotheses on `Rust.withPanics ext` for Block `350`. -/
structure RecvCt2PlacedAlloc [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  handleError : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked
  assertFailedU64 : Rust.withPanics ext spqrAssertFailedU64Sym = some Rust.panicked
  sliceIndexFail : Rust.withPanics ext spqrSliceIndexFailSym = some Rust.panicked
  unwrapFailed : Rust.withPanics ext spqrUnwrapFailedSym = some Rust.panicked
  panicBoundsCheck : Rust.withPanics ext spqrPanicBoundsCheckSym = some Rust.panicked
  panicConstAddOverflow : Rust.withPanics ext spqrPanicConstAddOverflowSym = some Rust.panicked
  shim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec
  alloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A)
  allocZeroed : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedSpec A)
  dealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym' (rustDeallocSpec A)
  realloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A)
  memcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec
  memcpyRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec

theorem withStack_sessionShim_of_noAllocShim {prog : Program} {entry : BitVec 64}
    (hookStack : Nat) (h : subroutine_ok prog entry noAllocShimSpec) :
    subroutine_ok prog entry (withStack sessionShimSpec hookStack) := by
  apply subroutine_ok_outcome_intro
  intro u R s0 hpc hrun hpre hal
  dsimp only [withStack, sessionShimSpec] at hpre
  rw [emp_sepConj] at hpre
  have hpre' : s0.mem ⊨ noAllocShimSpec.pre u s0 ∗ (stackAt s0.sp hookStack ∗ R) := by
    dsimp only [noAllocShimSpec]
    rw [emp_sepConj]
    exact hpre
  refine subroutine_ok.mono_outcome h u (stackAt s0.sp hookStack ∗ R) s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [noAllocShimSpec] at hpost
    dsimp only [withStack, sessionShimSpec]
    ac_nf at hpost ⊢
  · dsimp only [noAllocShimSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [noAllocShimSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [noAllocShimSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem withStack_sessionMemcpyRegion_of_frameless {prog : Program} {entry : BitVec 64}
    (hookStack : Nat) (h : subroutine_ok prog entry framelessMemcpySpec) :
    subroutine_ok prog entry (withStack sessionMemcpyRegionSpec hookStack) := by
  apply subroutine_ok_outcome_intro
  intro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal
  dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hpre' : s0.mem ⊨ framelessMemcpySpec.pre (dst, src, bs) s0 ∗ (stackAt s0.sp hookStack ∗ R) := by
    dsimp only [framelessMemcpySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    ac_nf at hmem ⊢
  refine subroutine_ok.mono_outcome h (dst, src, bs) (stackAt s0.sp hookStack ∗ R) s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [framelessMemcpySpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_sf, htr_sf⟩, hmem_sf⟩
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_sf, htr_sf⟩, ?_⟩
    ac_nf at hmem_sf ⊢
  · dsimp only [framelessMemcpySpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [framelessMemcpySpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [framelessMemcpySpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem RecvCt2PlacedAlloc.panic_handle_error [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem (hi := hi) (hunmut := hunmut)).trans hA.handleError

theorem RecvCt2PlacedAlloc.panic_assert_failed_u64 [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    (lsProg_350 (Rust.withPanics ext)).externAt? (lsρ spqrAssertFailedU64Sym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.assertFailedU64

theorem RecvCt2PlacedAlloc.panic_slice_index_fail [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    (lsProg_350 (Rust.withPanics ext)).externAt? (lsρ spqrSliceIndexFailSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.sliceIndexFail

theorem RecvCt2PlacedAlloc.panic_unwrap_failed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    (lsProg_350 (Rust.withPanics ext)).externAt? (lsρ spqrUnwrapFailedSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.unwrapFailed

theorem RecvCt2PlacedAlloc.panic_bounds_check [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    (lsProg_350 (Rust.withPanics ext)).externAt? (lsρ spqrPanicBoundsCheckSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.panicBoundsCheck

theorem RecvCt2PlacedAlloc.panic_add_overflow [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    (lsProg_350 (Rust.withPanics ext)).externAt? (lsρ spqrPanicConstAddOverflowSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.panicConstAddOverflow

theorem RecvCt2PlacedAlloc.shim_at_block [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)] (hookStack : Nat)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrRustNoAllocShimSym) (withStack sessionShimSpec hookStack) :=
  withStack_sessionShim_of_noAllocShim hookStack
    (spqr_hook_ok_of_mem hA.shim (hi := hi) (hunmut := hunmut))

theorem RecvCt2PlacedAlloc.shim_lscro [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustNoAllocShimSym)
      (withLsCodeRoLoaded lsmpl (withStack sessionShimSpec extHookStack)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_plain (hA.shim_at_block extHookStack)

theorem RecvCt2PlacedAlloc.memcpy_region_at_block [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)] (hookStack : Nat)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrMemcpySym) (withStack sessionMemcpyRegionSpec hookStack) :=
  withStack_sessionMemcpyRegion_of_frameless hookStack
    (spqr_hook_ok_of_mem hA.memcpy (hi := hi) (hunmut := hunmut))

theorem RecvCt2PlacedAlloc.memcpy_lscro [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrMemcpySym)
      (withLsCodeRoLoaded lsmpl session2MemcpySpecX) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_plain
    (session2MemcpyWithStack_of_framelessMemcpy extHookStack
      (spqr_hook_ok_of_mem hA.memcpy))

theorem RecvCt2PlacedAlloc.alloc_at_block [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A extHookStack) :=
  rustAllocWithStack_of_rustAlloc
    (spqr_hook_ok_of_mem hA.alloc (hi := hi) (hunmut := hunmut))

theorem RecvCt2PlacedAlloc.alloc_lscro [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustAllocSym)
      (withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_plain hA.alloc_at_block

theorem RecvCt2PlacedAlloc.allocZeroed_at_block [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrRustAllocZeroedSym) (rustAllocZeroedSpecWithStack A extHookStack) :=
  rustAllocZeroedWithStack_of_rustAllocZeroed
    (spqr_hook_ok_of_mem hA.allocZeroed (hi := hi) (hunmut := hunmut))

theorem RecvCt2PlacedAlloc.allocZeroed_lscro [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustAllocZeroedSym)
      (withLsCodeRoLoaded lsmpl (rustAllocZeroedSpecWithStack A extHookStack)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_plain hA.allocZeroed_at_block

theorem RecvCt2PlacedAlloc.dealloc_at_block [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrRustDeallocSym') (rustDeallocExternSpecWithStack A extHookStack) :=
  rustDeallocExternWithStack_of_rustDealloc
    (spqr_hook_ok_of_mem hA.dealloc (hi := hi) (hunmut := hunmut))

theorem RecvCt2PlacedAlloc.dealloc_lscro [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustDeallocSym')
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_plain hA.dealloc_at_block

theorem mlkem_decaps_placed_lscro [LibsignalPlacement] {K : MlKem}
    {ext : String → Option (State → State)}
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym (mlkemDecapsSpec K)) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrMlkemDecapsSym)
      (withLsCodeRoLoaded lsmpl (mlkemDecapsSpec K)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_plain (spqr_hook_ok_of_mem hdecaps)

theorem libcrux_hmac_safe_placed_lscro [LibsignalPlacement] {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym' (libcruxHmacSpec F A)) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrLibcruxHmacSym')
      (withLsCodeRoLoaded lsmpl (libcruxHmacSafeSpec F A)) := by
  apply Leaves.subroutine_ok_withLsCodeRoLoaded_of_plain
  have hraw : subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrLibcruxHmacSym')
      (libcruxHmacSpec F A) :=
    spqr_hook_ok_of_mem hhmac
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  dsimp only [libcruxHmacSafeSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hk_lt, hd_lt⟩, hmem⟩
  have hpre' : s0.mem ⊨ (libcruxHmacSpec F A).pre x s0 ∗ R := by
    dsimp only [libcruxHmacSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hmem⟩
  refine subroutine_ok.mono_outcome hraw x R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [libcruxHmacSpec, libcruxHmacSafeSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.2.2, hpost.2⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [libcruxHmacSpec, libcruxHmacSafeSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨haf | hk_ge | hd_ge, hpref⟩, hmem'⟩
    · exact ⟨⟨haf, hpref⟩, hmem'⟩
    · omega
    · omega
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

theorem addChunk_placed_lscro [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hadd : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX A))) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 419)
      (withLsCodeRoLoaded lsmpl (addChunkSpecX A)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 419) hadd)

theorem polyDecodedMessage_placed_lscro [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdec : PolyDecodedMessagePlacedOkX A ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl (polyDecodedMessagePlacedSpec A)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 350) (j := 418) hdec

theorem RecvCt2PlacedAlloc.sliceConcat2_lscro [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 386)
      (withLsCodeRoLoaded lsmpl (sliceConcat2Spec A)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 386)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (slice_concat_2_placed_ok hA.handleError
          hA.shim hA.alloc hA.memcpy hA.memcpyRO)))

theorem RecvCt2PlacedAlloc.sliceConcat3_lscro [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 386)
      (withLsCodeRoLoaded lsmpl (sliceConcat3Spec A)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 386)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (slice_concat_3_placed_ok hA.handleError
          hA.shim hA.alloc hA.memcpy hA.memcpyRO)))

theorem hkdfToSlice_placed_lscro [LibsignalPlacement] {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base (withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith F)))) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith F))) :=
  keys_ls_subroutine_ok_of_block_cro (i := 350) (j := 379) hhkdf

/-- Pure `Crypto` bundle carrying `F : ShaCompress` so `hkdf_to_slice_spqr_placed_ok`
    instantiates without requiring AES or X25519 parameters. -/
abbrev cryptoOfShaCompress (F : ShaCompress) : Crypto where
  F := F
  E := fun _ b => b
  D := fun _ b => b
  X := fun _ k => k
  pubKey := fun k => k

theorem hkdfToSlice_placed_ok_of_hooks [LibsignalPlacement] (F : ShaCompress)
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)] :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base (withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith F))) :=
  HkdfToSliceProof.hkdf_to_slice_spqr_placed_ok (cryptoOfShaCompress F)

theorem RecvCt2PlacedAlloc.authUpdate_lscro [LibsignalPlacement] {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext)
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base (withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith F)))) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 341)
      (withLsCodeRoLoaded lsmpl (authUpdateSpec F A)) := by
  have hconcat_341 : subroutine_ok ((blkPC_341).rebase (blkPl_341).base (Rust.withPanics ext))
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat2Spec A)) :=
    Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (ls_subroutine_ok_of_block (i := 341) (j := 386)
          (subroutine_ok_withLsCodeLoaded_of_plain
            (slice_concat_2_placed_ok hA.handleError
              hA.shim hA.alloc hA.memcpy hA.memcpyRO))))
  have hhkdf_341 : subroutine_ok ((blkPC_341).rebase (blkPl_341).base (Rust.withPanics ext))
      (lsmpl.base 379) (withLsCallInv lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith F))) :=
    Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (keys_ls_subroutine_ok_of_block_cro (i := 341) (j := 379) hhkdf)
  have hupd_341 :=
    authUpdate_placed_ok hconcat_341 hhkdf_341
      (hA.shim_at_block extHookStack)
      hA.alloc_at_block
      hA.allocZeroed_at_block
      hA.dealloc_at_block
      hA.panic_handle_error
  exact keys_ls_subroutine_ok_of_block_cro (i := 350) (j := 341)
    (Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv hupd_341)

theorem RecvCt2PlacedAlloc.doReserve7_lscro [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 320)
      (withLsCodeRoLoaded lsmpl (doReserveSpecX A)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 320)
      (do_reserve_7_placed_ok_x hA.handleError
        hA.shim hA.alloc hA.realloc))

theorem isNonZero_placed_lscro [LibsignalPlacement] (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 380)
      (withLsCodeRoLoaded lsmpl isNonZeroSpec) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 380)
      (subroutine_ok_withLsCodeLoaded_of_plain (isNonZero_placed_ok (Rust.withPanics ext))))

theorem RecvCt2PlacedAlloc.dropSortedSetPt16_lscro [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc A ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeRoLoaded lsmpl (dropGlueSortedSetPt16Spec A)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 264)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_sorted_set_pt16_placed_ok
          (spqr_hook_ok_of_mem hA.dealloc))))

end CryptoVerification.SpqrV1.States.RecvCt2Chunk

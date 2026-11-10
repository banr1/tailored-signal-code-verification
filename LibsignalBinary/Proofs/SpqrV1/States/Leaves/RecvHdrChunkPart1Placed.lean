/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SpqrV1.GF.IsNonZero
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) — Relocatable Part 1

Relocatable `[LibsignalPlacement]` proofs on `lsProg_369 (Rust.withPanics ext)` for
`withLsCodeRoLoaded` call combinators, the `None` (`StillReceiving`) branch
(`recv_hdr_chunk_none_placed_wpp`), and `Some(hdrFull)` `mac`/`hdr` allocations
(`recv_hdr_chunk_alloc_mac_hdr_placed_wpp`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

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
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Postcondition Abbreviations, Call Tactic, and Callee Wrappers -/

/-- Mangled `__rust_dealloc` extern symbol in `libsignalSessionExterns`. -/
abbrev spqrRustDeallocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

/-- Mangled `assert_failed::<u64, u64>` extern symbol in `libsignalSessionExterns`. -/
abbrev assertFailedRecvHdrSym : String :=
  "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_"

/-- Mangled `slice_index_fail` extern symbol in `libsignalSessionExterns`. -/
abbrev sliceIndexFailRecvHdrSym : String :=
  "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail"

/-- Mangled `panic_bounds_check` extern symbol in `libsignalSessionExterns`. -/
abbrev panicBoundsCheckRecvHdrSym : String :=
  "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check"

abbrev recvHdrChunkPlacedRoAt [LibsignalPlacement] : SepProp :=
  (lsρ hdrLabelSym) ↦ᵣ Authenticator.hdrLabel

abbrev recvHdrChunkPlacedPostQ [LibsignalPlacement] (F : ShaCompress) (A : RustAlloc)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (recvHdrChunkPlacedRoAt ∗
          (noHeaderReceivedRecvHdrChunkPlacedSpec F A).post x s0 sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev recvHdrChunkPlacedPostQp (F : ShaCompress) (_A : RustAlloc)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (⌜((x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true ∨ allocFailedIn s0 sf) ∧
            s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

/-- Hook and panic contract bundle for `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`). -/
structure RecvHdrChunkContractsPlaced (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  shim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec
  alloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A)
  dealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)
  memcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec
  memcpyRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec
  handle_error : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked
  assert_failed : (Rust.withPanics ext) assertFailedRecvHdrSym = some Rust.panicked
  slice_index_fail : (Rust.withPanics ext) sliceIndexFailRecvHdrSym = some Rust.panicked
  panic_bounds_check : (Rust.withPanics ext) panicBoundsCheckRecvHdrSym = some Rust.panicked

/-- Panic-aware mid-function call combinator preserving `LibsignalCodeRoLoaded pl`. -/
theorem call_allowPanic_lscro_mid {α : Type} {prog : Program} {pl : Arm64.Obj.MultiPlacement}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : (∀ code sf, spec.onExit x code s sf = ⌜False⌝) ∧
      (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine sepWPp_call_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hF hcall
    (x := x) (F := F) hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm (spec.pre x s), satisfies_pure_sepConj]
    exact ⟨hF, hpre R' hm⟩
  · intro sf code R' _ hex
    dsimp only [withLsCodeRoLoaded] at hex
    rw [hexit_eq.1 code sf, satisfies_pure_sepConj] at hex
    exact hex.1
  · intro sf _ hmem
    dsimp only [withLsCodeRoLoaded] at hmem
    exact Satisfies.mono (sepConj_mono_left (hpan sf)) hmem
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf hF_sf
    exact hnext sf hpc_sf hrun_sf hsp_sf hcs_sf hF_sf
  · intro sf R' _ hoom_m
    dsimp only [withLsCodeRoLoaded] at hoom_m
    rw [hexit_eq.2 sf, satisfies_pure_sepConj] at hoom_m
    exact False.elim hoom_m.1

open Lean Elab Tactic Meta in
elab "wpp_call_lscro_recvHdr " hcall:term:max a:term:max hF:term:max : tactic => do
  let hcallCopyId ← freshIdent `hcall_copy
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    have $hcallCopyId := $hcall
    apply (call_allowPanic_lscro_mid $hcallCopyId (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_lscro_recvHdr: unexpected subgoals"
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
      | exact onPanic_hmac_entails_recvCt2 (by wp_norm_lhs)
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
          if nm != ``Arm64.Spec.mk && nm != ``Arm64.Spec.inImage &&
              nm != ``withLsCodeRoLoaded &&
              nm != ``withLsCodeLoaded then
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

private theorem session2ShimSpecX_of_noAllocShim {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry noAllocShimSpec) :
    subroutine_ok prog entry session2ShimSpecX :=
  subroutine_ok_mono (subroutine_ok_withStack_of_subroutine_ok h extHookStack)
    (fun _ s R hp => by
      dsimp only [session2ShimSpecX, withStack, noAllocShimSpec] at hp ⊢
      rwa [emp_sepConj])
    (fun _ _ _ _ hq => hq)

private theorem session2MemcpySpecX_of_framelessMemcpy {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry framelessMemcpySpec) :
    subroutine_ok prog entry session2MemcpySpecX :=
  subroutine_ok_mono (subroutine_ok_withStack_of_subroutine_ok h extHookStack)
    (fun _ _ _ hp => by
      dsimp only [session2MemcpySpecX, withStack, framelessMemcpySpec] at hp ⊢
      ac_nf at hp ⊢)
    (fun _ _ _ _ hq => by
      dsimp only [session2MemcpySpecX, withStack, framelessMemcpySpec] at hq ⊢
      ac_nf at hq ⊢)

/-- Plain `SplitBytes` `memcpy` wrapper lifted to `withLsCodeRoLoaded lsmpl`. -/
theorem memcpy_withStack_lscro_ok [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) (hn : n < 2 ^ 64) (hookStack : Nat)
    (hmc : subroutine_ok prog entry (withStack framelessMemcpySpec hookStack)) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (withStack S.memcpySpec hookStack)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_plain
  refine subroutine_ok_outcome_intro fun ⟨dst, src⟩ R0 s_c hpc_c hrun_c hpre_c hsp_c => ?_
  dsimp only [withStack, SplitBytes.memcpySpec] at hpre_c
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre_c
  rcases hpre_c with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (S.to_bytes src))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  rcases h2 with ⟨bs, h3⟩
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  rcases h3 with ⟨hlen, h4⟩
  have hpre_mc : s_c.mem ⊨
      (withStack framelessMemcpySpec hookStack).pre (dst, src, bs) s_c ∗ (S.heap bs ∗ R0) := by
    dsimp only [withStack, framelessMemcpySpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, ?_⟩, ?_⟩
    · rw [hx2, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    · rw [hlen]
      ac_nf at h4 ⊢
  refine hmc.mono_outcome (dst, src, bs) (S.heap bs ∗ R0) s_c hpc_c hrun_c hpre_mc hsp_c fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withStack, framelessMemcpySpec] at hpost
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
  · dsimp only [withStack, framelessMemcpySpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [withStack, framelessMemcpySpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [withStack, framelessMemcpySpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

theorem shim_placed_ok_at_recvHdr [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced A ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym)
      (withLsCodeRoLoaded lsmpl session2ShimSpecX) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (session2ShimSpecX_of_noAllocShim
      (spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hC.shim))

theorem memcpy_placed_ok_at_recvHdr [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced A ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym)
      (withLsCodeRoLoaded lsmpl session2MemcpySpecX) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (session2MemcpySpecX_of_framelessMemcpy
      (spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hC.memcpy))

theorem memcpy_withStack_placed_at_recvHdr [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced A ext)
    (hookStack : Nat) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym)
      (withStack framelessMemcpySpec hookStack) :=
  subroutine_ok_withStack_of_subroutine_ok
    (spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hC.memcpy)
    hookStack

theorem alloc_placed_ok_at_recvHdr [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced A ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym)
      (withLsCodeRoLoaded lsmpl (rustAllocSpecWithStack A extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (rustAllocWithStack_of_rustAlloc
      (spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hC.alloc))

theorem dealloc_placed_ok_at_recvHdr [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced A ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (rustDeallocExternWithStack_of_rustDealloc
      (spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hC.dealloc))

theorem sliceConcat3_placed_ok_at_recvHdr [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced A ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsmpl.base 386)
      (withLsCodeRoLoaded lsmpl (sliceConcat3Spec A)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := lsProg_369 (Rust.withPanics ext)) (i := 369) (j := 386)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (slice_concat_3_placed_ok hC.handle_error hC.shim hC.alloc hC.memcpy hC.memcpyRO)))

theorem isNonZero_placed_ok_at_recvHdr [LibsignalPlacement]
    (ext : String → Option (State → State)) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsmpl.base 380)
      (withLsCodeRoLoaded lsmpl isNonZeroSpec) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := lsProg_369 (Rust.withPanics ext)) (i := 369) (j := 380)
      (subroutine_ok_withLsCodeLoaded_of_plain (isNonZero_placed_ok (Rust.withPanics ext))))

theorem dropSortedSet16_placed_ok_at_recvHdr [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced A ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsmpl.base 264)
      (withLsCodeRoLoaded lsmpl (dropGlueSortedSetPt16Spec A)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := lsProg_369 (Rust.withPanics ext)) (i := 369) (j := 264)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_sorted_set_pt16_placed_ok
          (spqr_hook_ok_of_mem (prog := (blkPC_264).rebase (blkPl_264).base (Rust.withPanics ext))
            hC.dealloc))))

theorem panic_at_handle_error_placed_recvHdr [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced A ext) :
    ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem (prog := lsProg_369 (Rust.withPanics ext))).trans hC.handle_error

theorem panic_at_assert_failed_u64_placed_recvHdr [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced A ext) :
    ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)).externAt?
      (lsρ assertFailedRecvHdrSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem (prog := lsProg_369 (Rust.withPanics ext))).trans hC.assert_failed

theorem panic_at_slice_index_fail_placed_recvHdr [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced A ext) :
    ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)).externAt?
      (lsρ sliceIndexFailRecvHdrSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem (prog := lsProg_369 (Rust.withPanics ext))).trans hC.slice_index_fail

theorem panic_at_bounds_check_placed_recvHdr [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced A ext) :
    ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)).externAt?
      (lsρ panicBoundsCheckRecvHdrSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem (prog := lsProg_369 (Rust.withPanics ext))).trans hC.panic_bounds_check

/-! ## 2. `None` (`StillReceiving`) Branch (offsets `180 .. 252` + `968 .. 1000`) -/

set_option maxHeartbeats 800000 in
theorem recv_hdr_chunk_none_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder)
    (s0 st : State) (R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
    (hsort : PolyDecoderStrictSorted receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok none)
    (hpc : st.pc = (blkPl_369).base + 180#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx21 : st.readReg64 .x21 = x.selfA)
    (hx22 : st.readReg64 .x22 = s0.sp - 736#64) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvHdrChunkPlacedRoAt ∗
        memRegion x.outA chunkedHeaderReceivedSize ∗
        unchunkedNoHeaderReceivedAt A x.selfA x.self.uc ∗
        memRegion (x.selfA + 56#64) 400 ∗
        cells (s0.sp - 1648#64) 11 ∗
        polyDecoderAt A ((s0.sp - 1648#64) + 0x58#64) receivingHdr ∗
        optKeyBytesAt A ((s0.sp - 1648#64) + 0x1e8#64) none ∗
        memRegion ((s0.sp - 1648#64) + 0x3e0#64) 456 ∗
        hdrSomeBranchFrameAt (s0.sp - 1648#64) ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) polyDecodedMessageStackX ∗
        savedRegsAt s0)
      (recvHdrChunkPlacedPostQ F A x s0 R)
      (recvHdrChunkPlacedPostQp F A x s0 R) := by
  have hmc_raw := memcpy_withStack_placed_at_recvHdr hC polyDecodedMessageStackX
  have h_mc_dec := memcpy_withStack_lscro_ok (polyDecoderSplit A receivingHdr)
    (by decide) polyDecodedMessageStackX hmc_raw
  have h_mc_st := memcpy_withStack_lscro_ok
    (chunkedNoHeaderReceivedSplit A { uc := x.self.uc, receiving_hdr := receivingHdr })
    (by decide) polyDecodedMessageStackX hmc_raw
  clear hC hmc_raw
  refine SepWPp.rw_pre (by
    rw [memRegion_456_at_fsp_3e0_split (s0.sp - 1648#64),
        memRegion_480_outA_split x.outA]) ?_
  sep_elim_exists
  refine of_sepWP_lscro (mid := lsρ spqrMemcpySym) hinv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr h_mc_dec
    ((s0.sp - 1648#64) + 0x418#64, (s0.sp - 1648#64) + 0x58#64) hinv1
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost1 => ?_
  rcases hpost1 with ⟨htr1, _⟩
  refine of_sepWP_lscro (mid := lsρ spqrMemcpySym) hF_sf ?_
  refine SepWP.fold (noHeaderReceivedUcAt_expose_entails A x.selfA x.self.uc) (by sep_focus) ?_
  sep_elim_exists
  wp_steps
  refine SepWP.fold
    (chunkedNoHeaderReceivedAt_fsp_3e0_entails A s0.sp x.self.uc receivingHdr _)
    (by sep_focus) ?_
  refine SepWP.fold
    (noHeaderReceivedCells_entails_memRegion_456 x.selfA _ _ _ _ _ _ _)
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_lscro_recvHdr h_mc_st (x.outA + 8#64, s0.sp - 656#64) hinv2
  refine SepWPp.pure_left_focus _ (by sep_focus) fun hpost2 => ?_
  rcases hpost2 with ⟨htr2, _⟩
  apply SepWPp.of_sepWP_ret
  refine SepWP.fold
    (optKeyBytesAt_none_entails_memRegion_24 A (s0.sp - 1160#64))
    (by sep_focus) ?_
  unfold savedRegsAt
  wp_steps
  have hfold_saved :
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
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢ savedRegsAt s0 := Entails.refl _
  refine SepWP.fold hfold_saved (by sep_focus) ?_
  have hfold_active :
      cells (s0.sp - 1648#64) 11 ∗
        memRegion (s0.sp - 1560#64) 400 ∗
        memRegion (s0.sp - 1160#64) 24 ∗
        memRegion (s0.sp - 656#64) 456 ∗
        hdrSomeBranchFrameAt (s0.sp - 1648#64) ⊢
      hdrActiveFrameRegionsAt (s0.sp - 1648#64) := by
    unfold hdrActiveFrameRegionsAt
    have ha1 : (s0.sp - 1648#64) + 0x58#64 = s0.sp - 1560#64 := by bv_omega
    have ha2 : (s0.sp - 1648#64) + 0x1e8#64 = s0.sp - 1160#64 := by bv_omega
    have ha3 : (s0.sp - 1648#64) + 0x3e0#64 = s0.sp - 656#64 := by bv_omega
    rw [ha1, ha2, ha3]
    exact Entails.refl _
  refine SepWP.fold hfold_active (by sep_focus) ?_
  have hstack_eq : stackAt sf.sp polyDecodedMessageStackX ⊢ stackAt (s0.sp - 1648#64) polyDecodedMessageStackX := by
    rw [hsp_sf, hsp]; exact Entails.refl _
  refine SepWP.fold hstack_eq (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_recvHdrChunk s0) (by sep_focus) ?_
  have hres := recv_hdr_chunk_eq_stillReceiving x.self x.epoch x.chunk receivingHdr hepoch hadd hdec
  unfold recvHdrChunkPlacedPostQ
  dsimp only [noHeaderReceivedRecvHdrChunkPlacedSpec]
  rw [hres]
  dsimp only [noHeaderReceivedRecvChunkResultAt, noHeaderReceivedRecvChunkAt]
  wp_done

/-! ## 3. `Some(hdrFull)` Length Check & `mac` / `hdr` Allocations (offsets `252 .. 320`) -/

set_option maxHeartbeats 1200000 in
theorem recv_hdr_chunk_alloc_mac_hdr_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced A ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hge64 : 64 ≤ hdrFull.length)
    (hlt_max : hdrFull.length < 2 ^ 63)
    (hpc : st.pc = (blkPl_369).base + 252#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (ptr_mac ptr_hdr : BitVec 64),
      ptr_hdr ≠ 0#64 →
      st'.pc = (blkPl_369).base + 320#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x0 = ptr_hdr →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = cap_hdrFull →
      st'.readReg64 .x21 = ptr_hdrFull →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = ptr_mac →
      st'.readReg64 .x24 = x.epoch →
      st'.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
          vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion ptr_hdr 64 ∗
          A.live ptr_hdr 64 1 ∗
          ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
          A.pool ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQ F A x s0 R)
        (recvHdrChunkPlacedPostQp F A x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
        ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPlacedPostQ F A x s0 R)
      (recvHdrChunkPlacedPostQp F A x s0 R) := by
  have h_shim := shim_placed_ok_at_recvHdr hC
  have h_alloc := alloc_placed_ok_at_recvHdr hC
  have h_mc := memcpy_placed_ok_at_recvHdr hC
  have h_pan_oom := panic_at_handle_error_placed_recvHdr hC
  clear hC
  have hzero_iff := ofNat_sub_64_eq_zero_iff hge64 hlt_max
  have hlay64 : LayoutOk 64 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  by_cases hlen64 : hdrFull.length = 64
  · have hzero : (BitVec.ofNat 64 (hdrFull.length - 64) == 0#64) = true := by
      rw [hzero_iff, decide_eq_true hlen64]
    refine of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr h_shim () hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
    refine of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf ?_
    wp_steps
    have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf]
    refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvHdr h_alloc (64, 1) hinv2
    by_cases hoom64 : sf_1.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      exact allowPanic_oom_recvCt2
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom64_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom64
      conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr2⟩
      refine of_sepWP_lscro (mid := (blkPl_369).base + 320#64) hF_sf_1 ?_
      wp_steps
      have hdrop0 : (hdrFull.drop 64).length = 0 := by rw [List.length_drop, hlen64]
      have hsub0 : BitVec.ofNat 64 (hdrFull.length - 64) = 0#64 := by rw [hlen64]
      have hvb0 : ((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ⊢
          ((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
            vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64)) 1#64 (hdrFull.drop 64) := by
        rw [hsub0]
        refine Entails.trans (Entails.of_eq (sepConj_emp _).symm) ?_
        exact sepConj_mono_right (vecBufAt_zero_one A (hdrFull.drop 64) hdrop0)
      refine SepWP.fold hvb0 (by sep_focus) ?_
      have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
        rw [← hstack_sf, hsp]
      refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv_end
      refine SepWPp.rw_pre (by ac_rfl)
        (hcont _ 1#64 (sf_1.readReg64 Reg.x0) hoom64
          (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hinv_end
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
  · have hzero : (BitVec.ofNat 64 (hdrFull.length - 64) == 0#64) = false := by
      rw [hzero_iff, decide_eq_false hlen64]
    have hlay_mac : LayoutOk (hdrFull.length - 64) 1 := ⟨by omega, ⟨0, rfl⟩, by omega⟩
    have hsub_toNat : (BitVec.ofNat 64 (hdrFull.length - 64)).toNat = hdrFull.length - 64 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hdrop_len : (hdrFull.drop 64).length = hdrFull.length - 64 := List.length_drop
    refine of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hinv ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr h_shim () hinv1
    refine SepWPp.pure_left_focus _ (by sep_focus) fun htr1 => ?_
    refine of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf ?_
    wp_steps
    have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf]
    refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvHdr h_alloc (hdrFull.length - 64, 1) hinv2
    by_cases hoom_mac : sf_1.readReg64 Reg.x0 = 0#64
    · conv => arg 4; simp only [hoom_mac, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      exact allowPanic_oom_recvCt2
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom_mac_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom_mac
      conv => arg 4; simp only [hoom_mac, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr2⟩
      refine of_sepWP_lscro (mid := lsρ spqrMemcpySym) hF_sf_1 ?_
      wp_steps
      have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
        rw [hsp_sf_1]
      refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv3
      wpp_call_lscro_recvHdr h_mc (sf_1.readReg64 Reg.x0, ptr_hdrFull + 64#64, hdrFull.drop 64) hinv3
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨_, htr3⟩
      have hfold_mac :
          ((sf_1.readReg64 Reg.x0) ↦ₛ hdrFull.drop 64) ∗
            A.live (sf_1.readReg64 Reg.x0) (hdrFull.length - 64) 1 ⊢
          vecBufAt A (BitVec.ofNat 64 (hdrFull.length - 64))
            (sf_1.readReg64 Reg.x0) (hdrFull.drop 64) := by
        rw [← hdrop_len]
        exact vecBufAt_of_bytes_live A (sf_1.readReg64 Reg.x0) (hdrFull.drop 64)
          (by omega) (by omega)
      refine of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hF_sf_2 ?_
      refine SepWP.fold hfold_mac (by sep_focus) ?_
      wp_steps
      have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
        rw [hsp_sf_2]
      refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv4
      wpp_call_lscro_recvHdr h_shim () hinv4
      refine SepWPp.pure_left_focus _ (by sep_focus) fun htr4 => ?_
      refine of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf_3 ?_
      wp_steps
      have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by
        rw [hsp_sf_3]
      refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv5
      wpp_call_lscro_recvHdr h_alloc (64, 1) hinv5
      by_cases hoom64 : sf_4.readReg64 Reg.x0 = 0#64
      · conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) fun htr5 => ?_
        apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
        exact allowPanic_oom_recvCt2
          (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
      · have hoom64_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom64
        conv => arg 4; simp only [hoom64, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
        refine SepWPp.pure_left_focus _ (by sep_focus) ?_
        rintro ⟨_, htr5⟩
        refine of_sepWP_lscro (mid := (blkPl_369).base + 320#64) hF_sf_4 ?_
        wp_steps
        have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
          rw [← hstack_sf3, ← hstack_sf2, ← hstack_sf1, ← hstack_sf, hsp]
        refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv_end
        refine SepWPp.rw_pre (by ac_rfl)
          (hcont _ (sf_1.readReg64 Reg.x0) (sf_4.readReg64 Reg.x0) hoom64
            (by wp_norm_goal) (by wp_norm_goal)
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            hinv_end
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

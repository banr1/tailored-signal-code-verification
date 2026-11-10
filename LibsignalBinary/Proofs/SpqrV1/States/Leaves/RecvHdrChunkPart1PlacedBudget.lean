/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
public import LibsignalBinary.Proofs.SpqrV1.GF.IsNonZero
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) — Budget-Threaded Part 1

Budget-threaded `[LibsignalPlacement]` proofs on `lsProg_369 (Rust.withPanics ext)` for
Block `369` callee/panic wrappers, the `None` (`StillReceiving`) branch, and `Some(hdrFull)`
`mac`/`hdr` heap allocations with OOM eliminated under `FitsEvents`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPC_264 blkPC_369 blkPC_380 blkPl_264 blkPl_369 blkPl_380
   lsProg_369 ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain
   withLsCodeLoaded)
open CryptoVerification.RustHeap
  (LayoutOk RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extHookStack subroutine_ok_withStack_of_subroutine_ok
   withLsCodeRoLoaded withStack)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (SepWPp.rw_pre)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes PolyDecoder isNonZero optKeyBytesAt spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym
   spqrRustNoAllocShimSym spqr_externAt?_of_mem spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Auth
  (vecBufAt)
open CryptoVerification.SpqrV1.ChainProofs
  (bytesAt_false bytesAt_true)
open CryptoVerification.SpqrV1.Drop
  (unchunkedNoHeaderReceivedAt)
open CryptoVerification.SpqrV1.GF.IsNonZero
  (isNonZeroSpec isNonZero_asm_eq stackAt_16_merge_byte12 stackAt_16_split_byte12)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt polyDecoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (PolyDecoderStrictSorted)
open CryptoVerification.SpqrV1.States.Leaves
  (of_sepWP_lscro subroutine_ok_withLsCodeRoLoaded_of_plain
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
  (NoHeaderReceivedRecvHdrChunkGhost chunkedHeaderReceivedSize chunkedNoHeaderReceivedSize
   chunkedNoHeaderReceivedSplit chunkedNoHeaderReceivedAt_fsp_3e0_entails
   hdrActiveFrameRegionsAt hdrLabelSym hdrSomeBranchFrameAt memRegion_456_at_fsp_3e0_split
   memRegion_480_outA_split noHeaderReceivedCells_entails_memRegion_456
   noHeaderReceivedRecvChunkAt noHeaderReceivedRecvChunkResultAt noHeaderReceivedRecvHdrChunkStackX
   noHeaderReceivedUcAt_expose_entails ofNat_sub_64_eq_zero_iff recv_hdr_chunk_eq_stillReceiving
   rejoin_stack_recvHdrChunk)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
  (SplitBytes optKeyBytesAt_none_entails_memRegion_24 polyDecodedMessageStackX savedRegsAt
   vecBufAt_of_bytes_live vecBufAt_zero_one)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk.SplitBytes
  (polyDecoderSplit)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget
   RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
   rustCliDeallocBudgetSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocBudgetExternSpecWithStack rustCliAllocNoOomExternSpecWithStack
   rustCliDeallocBudgetExternSpecWithStack subroutine_ok_rustCliAllocBudget_externWithStack
   subroutine_ok_rustCliAllocNoOom_externWithStack
   subroutine_ok_rustCliDeallocBudget_externWithStack)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget
  (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
  (framelessMemcpyAcpSpec session2MemcpyAcpSpecWithStack session2ShimAcpSpecWithStack
   sessionMemcpyRegionROSpec sliceConcat3Spec slice_concat_3_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
  (session2MemcpyAcpWithStack_of_frameless session2ShimAcpWithStack_of_rustAllocShimVm)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
  (dropGlueSortedSetPt16Spec drop_glue_sorted_set_pt16_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
  (NoHeaderReceivedRecvHdrChunkEnv noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv
   recvHdrChunkAllocMacHdrEvents)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] isNonZero_asm_eq
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Postcondition Abbreviations, Panic Helpers, Call Tactic, and Callee Wrappers -/

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

abbrev recvHdrChunkPlacedPostQOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (st0 : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (recvHdrChunkPlacedRoAt ∗
          (noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv M A lim F PreEnv PostEnv).post
            (x, st0) s0 sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev recvHdrChunkPlacedPostQOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (st0 : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  recvHdrChunkPlacedPostQOfPrePostEnv M A lim F Env Env x st0 s0 R

abbrev recvHdrChunkPlacedPostQ [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (st0 : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  recvHdrChunkPlacedPostQOfEnv M A lim F NoHeaderReceivedRecvHdrChunkEnv x st0 s0 R

abbrev recvHdrChunkPlacedPostQp (F : ShaCompress)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (⌜(x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true ∧
            s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem recvHdrChunkPlacedPostQOfPrePostEnv_intro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {x : NoHeaderReceivedRecvHdrChunkGhost F} {st0 : M.σ} {s0 sf : State} {R P_f : SepProp}
    (evs : List AllocEvent) (hevs : PostEnv x evs) (htr : sf.trace = s0.trace)
    (hsp : sf.sp = s0.sp) (hcs : CalleeSavedPreserved s0 sf)
    (hmem : (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (recvHdrChunkPlacedRoAt ∗
          noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
            (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
          memRegion x.selfA chunkedNoHeaderReceivedSize ∗
          chunkAt x.chunkA x.chunk ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX) ∗ R)) :
    recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R sf P_f := by
  refine ⟨fun hm => ?_, hsp, hcs⟩
  have hm' := hmem hm
  dsimp only [noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv]
  refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hm'
  refine Entails.trans ?_ (Entails.sepExists_intro evs)
  exact Entails.pure_right ⟨htr, hevs⟩ (Entails.refl _)

theorem onPanic_same_entails_recvHdr {P : Prop} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜P ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜P ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [htr, sepConj_assoc]
  exact Entails.pure_left fun hp => Entails.pure_right hp (entails_anyHeap _)

theorem onPanic_hmac_budget_entails_recvHdr {P : Prop} {msgLen : Nat} {s0 s sf : State}
    {F : SepProp} (hlt : msgLen < 2 ^ 32) (_htr : s.trace = s0.trace) :
    (⌜2 ^ 32 ≤ msgLen ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜P ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  exact Entails.pure_left fun ⟨hge, _⟩ => absurd hlt (Nat.not_lt.mpr hge)

theorem allowPanic_isPanic_recvHdr_budget {P : Prop} {s0 sf : State} {Q R : SepProp}
    (hP : P) (htr : sf.trace = s0.trace)
    (hm : (Rust.panicked sf).mem ⊨ Q ∗ R) :
    (Rust.panicked sf).mem ⊨
      (⌜P ∧ s0.trace <+: (Rust.panicked sf).trace⌝ ∗ anyHeap) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have hpref : s0.trace <+: (Rust.panicked sf).trace := by
    simp only [Rust.panicked, htr]
    exact List.prefix_refl _
  exact ⟨⟨hP, hpref⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap Q)) hm⟩

/-- Budget-threaded hook and panic contract bundle for `<NoHeaderReceived>::recv_hdr_chunk`
    (Block `369`). -/
structure RecvHdrChunkContractsPlaced [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop where
  shim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec
  alloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  memcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec
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
  refine CryptoVerification.SpqrV1.States.Leaves.sepWPp_call_frozen
    (fun _ _ h hkf => h.of_keepsFrozen hkf) hF hcall
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
elab "wpp_call_lscro_recvHdr_budget " hcall:term:max a:term:max hF:term:max : tactic => do
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
    | throwError "wpp_call_lscro_recvHdr_budget: unexpected subgoals"
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
      | exact onPanic_same_entails_recvHdr (by wp_norm_lhs)
      | exact onPanic_hmac_budget_entails_recvHdr (by decide) (by wp_norm_lhs)
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

/-- `SplitBytes` `memcpy` wrapper preserving `VmPreserved` and `LibsignalCodeRoLoaded lsmpl`. -/
theorem memcpy_withStack_lscro_ok [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) (hn : n < 2 ^ 64) (hookStack : Nat)
    (hmc : subroutine_ok prog entry (withStack framelessMemcpyAcpSpec hookStack)) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (withVmPreserved (withStack S.memcpySpec hookStack))) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_plain
  refine subroutine_ok_outcome_intro fun ⟨dst, src⟩ R0 s_c hpc_c hrun_c hpre_c hsp_c => ?_
  dsimp only [withVmPreserved, withStack, SplitBytes.memcpySpec] at hpre_c
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre_c
  rcases hpre_c with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (S.to_bytes src))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  rcases h2 with ⟨bs, h3⟩
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  rcases h3 with ⟨hlen, h4⟩
  have hpre_mc : s_c.mem ⊨
      (withStack framelessMemcpyAcpSpec hookStack).pre (dst, src, bs) s_c ∗ (S.heap bs ∗ R0) := by
    dsimp only [withStack, framelessMemcpyAcpSpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, ?_⟩, ?_⟩
    · rw [hx2, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    · rw [hlen]
      ac_nf at h4 ⊢
  refine hmc.mono_outcome (dst, src, bs) (S.heap bs ∗ R0) s_c hpc_c hrun_c hpre_mc hsp_c
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withStack, framelessMemcpyAcpSpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_sf, hacp_sf, hvm_sf⟩, hpost_mem⟩
    dsimp only [withVmPreserved, withStack, SplitBytes.memcpySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm_sf, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hacp_sf.2.1, hx0_sf⟩, ?_⟩
    have harrange :
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt s_c.sp hookStack ∗ (S.heap bs ∗ R0) =
        (((dst ↦ₛ bs) ∗ S.heap bs) ∗ (src ↦ₛ bs)) ∗ stackAt s_c.sp hookStack ∗ R0 := by
      sep_ac_rfl
    rw [harrange] at hpost_mem
    have hsrc_mr : (src ↦ₛ bs) ⊢ memRegion src n := hlen ▸ pointsToBytes_entails_memRegion src bs
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono (S.of_bytes dst bs hlen) hsrc_mr))
      hpost_mem
  · dsimp only [withStack, framelessMemcpyAcpSpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [withStack, framelessMemcpyAcpSpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · dsimp only [withStack, framelessMemcpyAcpSpec,
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.framelessMemcpyAcpSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

theorem shim_placed_ok_at_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym)
      (withLsCodeRoLoaded lsmpl (session2ShimAcpSpecWithStack extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (session2ShimAcpWithStack_of_rustAllocShimVm extHookStack
      (spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hC.shim))

theorem memcpy_placed_ok_at_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym)
      (withLsCodeRoLoaded lsmpl (session2MemcpyAcpSpecWithStack extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (session2MemcpyAcpWithStack_of_frameless extHookStack
      (spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hC.memcpy))

theorem memcpy_withStack_placed_at_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (hookStack : Nat) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym)
      (withStack framelessMemcpyAcpSpec hookStack) :=
  subroutine_ok_withStack_of_subroutine_ok
    (spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hC.memcpy)
    hookStack

theorem alloc_placed_ok_at_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym)
      (withLsCodeRoLoaded lsmpl
        (rustCliAllocBudgetExternSpecWithStack M A lim false extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (subroutine_ok_rustCliAllocBudget_externWithStack (by decide) (by decide)
      (spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hC.alloc))

theorem allocNoOom_placed_ok_at_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym)
      (withLsCodeRoLoaded lsmpl
        (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget
        (spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hC.alloc)))

theorem dealloc_placed_ok_at_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym)
      (withLsCodeRoLoaded lsmpl
        (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (subroutine_ok_rustCliDeallocBudget_externWithStack (by decide) (by decide)
      (spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hC.dealloc))

theorem sliceConcat3_placed_ok_at_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsmpl.base 386)
      (withLsCodeRoLoaded lsmpl (sliceConcat3Spec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := lsProg_369 (Rust.withPanics ext)) (i := 369) (j := 386)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (slice_concat_3_placed_ok hC.shim hC.alloc hC.memcpy hC.memcpyRO)))

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

@[local arm64_norm, local wp_norm]
private theorem isNonZero_asm_eq' (v : BitVec 8) :
    BitVec.setWidth 64 (BitVec.truncate 8 ((0#32 - BitVec.zeroExtend 32 v) >>> 31)) =
    BitVec.zeroExtend 64 (isNonZero v) := by
  revert v
  decide +kernel

/-- Relocatable `spqr::util::is_non_zero` (Block `380`) meets `withVmPreserved isNonZeroSpec`. -/
theorem isNonZero_vm_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_380).rebase (blkPl_380).base H) (blkPl_380).base
      (withVmPreserved isNonZeroSpec) := by
  simp only [withVmPreserved, isNonZeroSpec]
  wp_init v s0
  wp_simp_pre [stackAt_16_split_byte12]
  wp_pull_exists
  refine seq_vm_clean (mid := s0.readReg64 .lr)
    (P_mid := stackAt s0.sp 0x10)
    (Q := fun sm =>
      sm.readReg64 .x0 = BitVec.zeroExtend 64 (isNonZero v) ∧
      sm.trace = s0.trace ∧
      sm.sp = s0.sp ∧
      CalleeSavedPreserved s0 sm)
    ?_ ?_
  · by_vm_steps (
      wp_steps
      apply SepWP.fold
        (stackAt_16_merge_byte12 s0.sp
          (BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (0#32 - BitVec.zeroExtend 32 v) >>> 31)))
        (by sep_focus)
      wp_done
    )
  · intro sm hpc_m hrun_m hvm ⟨hx0_m, htr_m, hsp_m, hcs_m⟩
    refine SepWP.done hpc_m hrun_m ⟨fun hPR => ?_, hsp_m, hcs_m⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hPR ⊢
    exact ⟨hvm, ⟨hx0_m, htr_m⟩, hPR⟩

theorem isNonZero_placed_ok_at_recvHdr [LibsignalPlacement]
    (ext : String → Option (State → State)) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsmpl.base 380)
      (withLsCodeRoLoaded lsmpl (withVmPreserved isNonZeroSpec)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := lsProg_369 (Rust.withPanics ext)) (i := 369) (j := 380)
      (subroutine_ok_withLsCodeLoaded_of_plain (isNonZero_vm_placed_ok (Rust.withPanics ext))))

theorem dropSortedSet16_placed_ok_at_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsmpl.base 264)
      (withLsCodeRoLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := lsProg_369 (Rust.withPanics ext)) (i := 369) (j := 264)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_sorted_set_pt16_placed_ok
          (spqr_hook_ok_of_mem (prog := (blkPC_264).rebase (blkPl_264).base (Rust.withPanics ext))
            hC.dealloc))))

theorem panic_at_handle_error_placed_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext) :
    ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem (prog := lsProg_369 (Rust.withPanics ext))).trans hC.handle_error

theorem panic_at_assert_failed_u64_placed_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext) :
    ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)).externAt?
      (lsρ assertFailedRecvHdrSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem (prog := lsProg_369 (Rust.withPanics ext))).trans hC.assert_failed

theorem panic_at_slice_index_fail_placed_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext) :
    ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)).externAt?
      (lsρ sliceIndexFailRecvHdrSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem (prog := lsProg_369 (Rust.withPanics ext))).trans hC.slice_index_fail

theorem panic_at_bounds_check_placed_recvHdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext) :
    ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)).externAt?
      (lsρ panicBoundsCheckRecvHdrSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem (prog := lsProg_369 (Rust.withPanics ext))).trans hC.panic_bounds_check

/-! ## 2. `None` (`StillReceiving`) Branch (offsets `180 .. 252` + `968 .. 1000`) -/

set_option maxHeartbeats 800000 in
theorem recv_hdr_chunk_none_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder)
    (st0 st_cur : M.σ) (evs_so_far : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_so_far st0)
    (hpost_env : PostEnv x evs_so_far)
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
        unchunkedNoHeaderReceivedAt A.repAlloc x.selfA x.self.uc ∗
        memRegion (x.selfA + 56#64) 400 ∗
        cells (s0.sp - 1648#64) 11 ∗
        polyDecoderAt A.repAlloc ((s0.sp - 1648#64) + 0x58#64) receivingHdr ∗
        optKeyBytesAt A.repAlloc ((s0.sp - 1648#64) + 0x1e8#64) none ∗
        memRegion ((s0.sp - 1648#64) + 0x3e0#64) 456 ∗
        hdrSomeBranchFrameAt (s0.sp - 1648#64) ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) polyDecodedMessageStackX ∗
        savedRegsAt s0)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  have hmc_raw := memcpy_withStack_placed_at_recvHdr hC polyDecodedMessageStackX
  have h_mc_dec := memcpy_withStack_lscro_ok (polyDecoderSplit A.repAlloc receivingHdr)
    (by decide) polyDecodedMessageStackX hmc_raw
  have h_mc_st := memcpy_withStack_lscro_ok
    (chunkedNoHeaderReceivedSplit A.repAlloc { uc := x.self.uc, receiving_hdr := receivingHdr })
    (by decide) polyDecodedMessageStackX hmc_raw
  clear hC hmc_raw
  refine SepWPp.rw_pre (by
    rw [memRegion_456_at_fsp_3e0_split (s0.sp - 1648#64),
        memRegion_480_outA_split x.outA]) ?_
  sep_elim_exists
  refine of_sepWP_lscro (mid := lsρ spqrMemcpySym) hinv ?_
  wp_steps_sync_pool (lsρ spqrMemcpySym)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr_budget h_mc_dec
    ((s0.sp - 1648#64) + 0x418#64, (s0.sp - 1648#64) + 0x58#64) hinv1
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hpost1 => ?_
  rcases hpost1 with ⟨hvm1, htr1, _⟩
  refine SepWPp.rw_pre (by rw [← A.pool_of_vmPreserved hvm1]) ?_
  refine of_sepWP_lscro (mid := lsρ spqrMemcpySym) hF_sf ?_
  refine SepWP.fold (noHeaderReceivedUcAt_expose_entails A.repAlloc x.selfA x.self.uc)
    (by sep_focus) ?_
  sep_elim_exists
  wp_steps_sync_pool (lsρ spqrMemcpySym)
  simp only [State.setMem_setMem]
  refine SepWP.fold
    (chunkedNoHeaderReceivedAt_fsp_3e0_entails A.repAlloc s0.sp x.self.uc receivingHdr _)
    (by sep_focus) ?_
  refine SepWP.fold
    (noHeaderReceivedCells_entails_memRegion_456 x.selfA _ _ _ _ _ _ _)
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  wpp_call_lscro_recvHdr_budget h_mc_st (x.outA + 8#64, s0.sp - 656#64) hinv2
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hpost2 => ?_
  rcases hpost2 with ⟨hvm2, htr2, _⟩
  refine SepWPp.rw_pre (by rw [← A.pool_of_vmPreserved hvm2]) ?_
  apply SepWPp.of_sepWP_ret
  refine SepWP.fold
    (optKeyBytesAt_none_entails_memRegion_24 A.repAlloc (s0.sp - 1160#64))
    (by sep_focus) ?_
  unfold savedRegsAt
  wp_steps_sync_pool (s0.readReg64 .x30)
  simp only [State.setMem_setMem]
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
  have hstack_eq :
      stackAt sf_1.sp polyDecodedMessageStackX ⊢
        stackAt (s0.sp - 1648#64) polyDecodedMessageStackX := by
    rw [hsp_sf_1, hsp_sf, hsp]; exact Entails.refl _
  refine SepWP.fold hstack_eq (by sep_focus) ?_
  refine SepWP.fold (rejoin_stack_recvHdrChunk s0) (by sep_focus) ?_
  have hres := recv_hdr_chunk_eq_stillReceiving x.self x.epoch x.chunk receivingHdr hepoch hadd hdec
  refine SepWP.mono
    (post := fun sf_ret P_ret =>
      ((sf_ret.mem ⊨ P_ret ∗ R) →
        (sf_ret.mem ⊨
          (⌜sf_ret.trace = s0.trace⌝ ∗
            (recvHdrChunkPlacedRoAt ∗
              noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
                (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
              memRegion x.selfA chunkedNoHeaderReceivedSize ∗
              chunkAt x.chunkA x.chunk ∗
              tokenInitPlacedAt ∗
              reduceTablePlacedAt ∗
              A.pool lim st_cur sf_ret ∗
              stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX)) ∗ R)) ∧
        sf_ret.sp = s0.sp ∧ CalleeSavedPreserved s0 sf_ret)
    ?_ ?_
  · rw [hres]
    dsimp only [noHeaderReceivedRecvChunkResultAt, noHeaderReceivedRecvChunkAt]
    wp_done
  · rintro sf_ret P_ret _ _ ⟨hmem_ret, hsp_ret, hcs_ret⟩
    refine ⟨fun hm => ?_, hsp_ret, hcs_ret⟩
    have hm1 := hmem_ret hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1
    rcases hm1 with ⟨htr_ret, hm2⟩
    rw [hst_cur] at hm2
    exact (recvHdrChunkPlacedPostQOfPrePostEnv_intro (P_f := P_ret)
      evs_so_far hpost_env htr_ret hsp_ret hcs_ret (fun _ => hm2)).1 hm

theorem recv_hdr_chunk_none_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder)
    (st0 st_cur : M.σ) (evs_so_far : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_so_far st0)
    (hpost_env : Env x evs_so_far)
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
        unchunkedNoHeaderReceivedAt A.repAlloc x.selfA x.self.uc ∗
        memRegion (x.selfA + 56#64) 400 ∗
        cells (s0.sp - 1648#64) 11 ∗
        polyDecoderAt A.repAlloc ((s0.sp - 1648#64) + 0x58#64) receivingHdr ∗
        optKeyBytesAt A.repAlloc ((s0.sp - 1648#64) + 0x1e8#64) none ∗
        memRegion ((s0.sp - 1648#64) + 0x3e0#64) 456 ∗
        hdrSomeBranchFrameAt (s0.sp - 1648#64) ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) polyDecodedMessageStackX ∗
        savedRegsAt s0)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_none_placed_wpp_ofPrePostEnv hC x receivingHdr st0 st_cur evs_so_far s0 st R
    hst_cur hpost_env hepoch hadd hsort hdec hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx21 hx22

theorem recv_hdr_chunk_none_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (receivingHdr : PolyDecoder)
    (st0 st_cur : M.σ) (evs_so_far : List AllocEvent)
    (s0 st : State) (R : SepProp)
    (hst_cur : st_cur = M.stepEvents evs_so_far st0)
    (hpost_env : NoHeaderReceivedRecvHdrChunkEnv x evs_so_far)
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
        unchunkedNoHeaderReceivedAt A.repAlloc x.selfA x.self.uc ∗
        memRegion (x.selfA + 56#64) 400 ∗
        cells (s0.sp - 1648#64) 11 ∗
        polyDecoderAt A.repAlloc ((s0.sp - 1648#64) + 0x58#64) receivingHdr ∗
        optKeyBytesAt A.repAlloc ((s0.sp - 1648#64) + 0x1e8#64) none ∗
        memRegion ((s0.sp - 1648#64) + 0x3e0#64) 456 ∗
        hdrSomeBranchFrameAt (s0.sp - 1648#64) ∗
        chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) polyDecodedMessageStackX ∗
        savedRegsAt s0)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_none_placed_wpp_ofEnv hC x receivingHdr st0 st_cur evs_so_far s0 st R
    hst_cur hpost_env hepoch hadd hsort hdec hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx21 hx22

/-! ## 3. `Some(hdrFull)` `mac` / `hdr` Allocations (offsets `252 .. 320`, OOM Eliminated) -/

set_option maxHeartbeats 1200000 in
theorem recv_hdr_chunk_alloc_mac_hdr_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hge64 : 64 ≤ hdrFull.length)
    (hlt_max : hdrFull.length < 2 ^ 63)
    (hfits : FitsEvents M lim st_cur (recvHdrChunkAllocMacHdrEvents hdrFull.length))
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
          vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion ptr_hdr 64 ∗
          A.live ptr_hdr 64 1 ∗
          ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
          A.pool lim (M.stepEvents (recvHdrChunkAllocMacHdrEvents hdrFull.length) st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
        ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  have h_shim := shim_placed_ok_at_recvHdr hC
  have h_alloc := allocNoOom_placed_ok_at_recvHdr hC
  have h_mc := memcpy_placed_ok_at_recvHdr hC
  clear hC
  have hzero_iff := ofNat_sub_64_eq_zero_iff hge64 hlt_max
  have hlay64 : RustLayoutOk 64 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  by_cases hlen64 : hdrFull.length = 64
  · have hzero : (BitVec.ofNat 64 (hdrFull.length - 64) == 0#64) = true := by
      rw [hzero_iff, decide_eq_true hlen64]
    have hfits64 : FitsEvents M lim st_cur (rustAllocEvents 64 1) := by
      simpa only [recvHdrChunkAllocMacHdrEvents, hlen64, ↓reduceIte, List.nil_append] using hfits
    have hstep_eq :
        M.stepEvents (rustAllocEvents 64 1) st_cur =
          M.stepEvents (recvHdrChunkAllocMacHdrEvents hdrFull.length) st_cur := by
      simp only [recvHdrChunkAllocMacHdrEvents, hlen64, ↓reduceIte, List.nil_append]
    refine of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hinv ?_
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr_budget h_shim () hinv1
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hpost1 => ?_
    rcases hpost1 with ⟨hacp1, hvm1⟩
    have htr1 : sf.trace = s0.trace := hacp1.2.1.trans (by wp_norm_goal)
    refine SepWPp.rw_pre (by rw [← A.pool_of_vmPreserved hvm1]) ?_
    refine of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf ?_
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf]
    refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvHdr_budget h_alloc (64, 1, st_cur) hinv2
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨htr2, hoom64, _⟩
    have hoom64_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom64
    refine of_sepWP_lscro (mid := (blkPl_369).base + 320#64) hF_sf_1 ?_
    wp_steps_sync_pool ((blkPl_369).base + 320#64)
    simp only [State.setMem_setMem]
    have hdrop0 : (hdrFull.drop 64).length = 0 := by rw [List.length_drop, hlen64]
    have hsub0 : BitVec.ofNat 64 (hdrFull.length - 64) = 0#64 := by rw [hlen64]
    have hvb0 : ((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ⊢
        ((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) 1#64 (hdrFull.drop 64) := by
      rw [hsub0]
      refine Entails.trans (Entails.of_eq (sepConj_emp _).symm) ?_
      exact sepConj_mono_right (vecBufAt_zero_one A.repAlloc (hdrFull.drop 64) hdrop0)
    refine SepWP.fold hvb0 (by sep_focus) ?_
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
      rw [← hstack_sf, hsp]
    refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv_end
    refine SepWPp.rw_pre (by rw [hstep_eq]; sep_ac_rfl)
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
    have hlay_mac : RustLayoutOk (hdrFull.length - 64) 1 :=
      ⟨⟨by omega, ⟨0, rfl⟩, by omega⟩, by decide⟩
    have hsub_toNat : (BitVec.ofNat 64 (hdrFull.length - 64)).toNat = hdrFull.length - 64 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hdrop_len : (hdrFull.drop 64).length = hdrFull.length - 64 := List.length_drop
    have hfits_both :
        FitsEvents M lim st_cur
          (rustAllocEvents (hdrFull.length - 64) 1 ++ rustAllocEvents 64 1) := by
      simpa only [recvHdrChunkAllocMacHdrEvents, hlen64, ↓reduceIte] using hfits
    rcases (fitsEvents_append M lim
        (rustAllocEvents (hdrFull.length - 64) 1) (rustAllocEvents 64 1) st_cur).mp hfits_both with
      ⟨hfits_mac, hfits_hdr⟩
    have hstep_eq :
        M.stepEvents (rustAllocEvents 64 1)
          (M.stepEvents (rustAllocEvents (hdrFull.length - 64) 1) st_cur) =
        M.stepEvents (recvHdrChunkAllocMacHdrEvents hdrFull.length) st_cur := by
      simp only [recvHdrChunkAllocMacHdrEvents, hlen64, ↓reduceIte,
        AllocCostModel.stepEvents_append]
    refine of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hinv ?_
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr_budget h_shim () hinv1
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hpost1 => ?_
    rcases hpost1 with ⟨hacp1, hvm1⟩
    have htr1 : sf.trace = s0.trace := hacp1.2.1.trans (by wp_norm_goal)
    refine SepWPp.rw_pre (by rw [← A.pool_of_vmPreserved hvm1]) ?_
    refine of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf ?_
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
      rw [hsp_sf]
    refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvHdr_budget h_alloc (hdrFull.length - 64, 1, st_cur) hinv2
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨htr2, hoom_mac, _⟩
    have hoom_mac_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom_mac
    refine of_sepWP_lscro (mid := lsρ spqrMemcpySym) hF_sf_1 ?_
    wp_steps_sync_pool (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
      rw [hsp_sf_1]
    refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv3
    wpp_call_lscro_recvHdr_budget h_mc
      (sf_1.readReg64 Reg.x0, ptr_hdrFull + 64#64, hdrFull.drop 64) hinv3
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, hacp3, hvm3⟩
    have htr3 : sf_2.trace = s0.trace := hacp3.2.1.trans (by wp_norm_goal)
    refine SepWPp.rw_pre (by rw [← A.pool_of_vmPreserved hvm3]) ?_
    have hfold_mac :
        ((sf_1.readReg64 Reg.x0) ↦ₛ hdrFull.drop 64) ∗
          A.live (sf_1.readReg64 Reg.x0) (hdrFull.length - 64) 1 ⊢
        vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64))
          (sf_1.readReg64 Reg.x0) (hdrFull.drop 64) := by
      rw [← hdrop_len]
      exact vecBufAt_of_bytes_live A.repAlloc (sf_1.readReg64 Reg.x0) (hdrFull.drop 64)
        (by omega) (by omega)
    refine of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hF_sf_2 ?_
    refine SepWP.fold hfold_mac (by sep_focus) ?_
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
      rw [hsp_sf_2]
    refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv4
    wpp_call_lscro_recvHdr_budget h_shim () hinv4
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun hpost4 => ?_
    rcases hpost4 with ⟨hacp4, hvm4⟩
    have htr4 : sf_3.trace = s0.trace := hacp4.2.1.trans (by wp_norm_goal)
    refine SepWPp.rw_pre (by rw [← A.pool_of_vmPreserved hvm4]) ?_
    refine of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf_3 ?_
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    have hstack_sf3 : stackAt sf_2.sp extHookStack = stackAt sf_3.sp extHookStack := by
      rw [hsp_sf_3]
    refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv5
    wpp_call_lscro_recvHdr_budget h_alloc
      (64, 1, M.stepEvents (rustAllocEvents (hdrFull.length - 64) 1) st_cur) hinv5
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨htr5, hoom64, _⟩
    have hoom64_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom64
    refine of_sepWP_lscro (mid := (blkPl_369).base + 320#64) hF_sf_4 ?_
    wp_steps_sync_pool ((blkPl_369).base + 320#64)
    simp only [State.setMem_setMem]
    have hstack_sf4 : stackAt sf_3.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
      rw [← hstack_sf3, ← hstack_sf2, ← hstack_sf1, ← hstack_sf, hsp]
    refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv_end
    refine SepWPp.rw_pre (by rw [hstep_eq]; sep_ac_rfl)
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

theorem recv_hdr_chunk_alloc_mac_hdr_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull : BitVec 64) (st0 st_cur : M.σ) (s0 st : State) (F_frame R : SepProp)
    (hge64 : 64 ≤ hdrFull.length) (hlt_max : hdrFull.length < 2 ^ 63)
    (hfits : FitsEvents M lim st_cur (recvHdrChunkAllocMacHdrEvents hdrFull.length))
    (hpc : st.pc = (blkPl_369).base + 252#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (ptr_mac ptr_hdr : BitVec 64), ptr_hdr ≠ 0#64 →
      st'.pc = (blkPl_369).base + 320#64 → st'.status = .Running → st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace → calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem → st'.readReg64 .x0 = ptr_hdr →
      st'.readReg64 .x19 = x.outA → st'.readReg64 .x20 = cap_hdrFull →
      st'.readReg64 .x21 = ptr_hdrFull →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = ptr_mac → st'.readReg64 .x24 = x.epoch →
      st'.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length → st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion ptr_hdr 64 ∗ A.live ptr_hdr 64 1 ∗ ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
          A.pool lim (M.stepEvents (recvHdrChunkAllocMacHdrEvents hdrFull.length) st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗ F_frame)
        (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗ ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack ∗ F_frame)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_alloc_mac_hdr_placed_wpp_ofPrePostEnv hC x hdrFull cap_hdrFull ptr_hdrFull
    st0 st_cur s0 st F_frame R hge64 hlt_max hfits hpc hrun hsp hsp_s0 htr hvregs hinv
    hx19 hx20 hx22 hx24 hx26 hx29 hcont

theorem recv_hdr_chunk_alloc_mac_hdr_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull : BitVec 64) (st0 st_cur : M.σ) (s0 st : State) (F_frame R : SepProp)
    (hge64 : 64 ≤ hdrFull.length) (hlt_max : hdrFull.length < 2 ^ 63)
    (hfits : FitsEvents M lim st_cur (recvHdrChunkAllocMacHdrEvents hdrFull.length))
    (hpc : st.pc = (blkPl_369).base + 252#64) (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64) (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (ptr_mac ptr_hdr : BitVec 64), ptr_hdr ≠ 0#64 →
      st'.pc = (blkPl_369).base + 320#64 → st'.status = .Running → st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace → calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem → st'.readReg64 .x0 = ptr_hdr →
      st'.readReg64 .x19 = x.outA → st'.readReg64 .x20 = cap_hdrFull →
      st'.readReg64 .x21 = ptr_hdrFull →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = ptr_mac → st'.readReg64 .x24 = x.epoch →
      st'.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length → st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗
          vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion ptr_hdr 64 ∗ A.live ptr_hdr 64 1 ∗ ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
          A.pool lim (M.stepEvents (recvHdrChunkAllocMacHdrEvents hdrFull.length) st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗ F_frame)
        (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (((s0.sp - 1152#64) ↦₆₄ ptr_hdrFull) ∗ ((ptr_hdrFull + 64#64) ↦ₛ hdrFull.drop 64) ∗
        A.pool lim st_cur st ∗ stackAt (s0.sp - 1648#64) extHookStack ∗ F_frame)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_alloc_mac_hdr_placed_wpp_ofEnv hC x hdrFull cap_hdrFull ptr_hdrFull
    st0 st_cur s0 st F_frame R hge64 hlt_max hfits hpc hrun hsp hsp_s0 htr hvregs hinv
    hx19 hx20 hx22 hx24 hx26 hx29 hcont

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget

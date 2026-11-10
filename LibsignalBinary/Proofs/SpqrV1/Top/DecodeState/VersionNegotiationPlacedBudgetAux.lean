/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `VersionNegotiationPB` Tag 1..3 Helpers (Block `325`)

Proves budget-threaded relocatable `VersionNegotiationPB` body lemmas for Tag 1 (`auth_key`,
`+1412`), Tag 2 (`direction`, `+1328`), and Tag 3 (`min_version`, `+1432`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkLib_eq_325 blkPC_325 blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAfter_join)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto)
open CryptoVerification.LibsignalSpqrV1 (ChainPB PqRatchetState VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeBytes)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg
   errFrame_parts_fold optChainPBCapOkAt_entails_optChainPBAt optChainPBCapOkAt_mono
   optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt
   optProtoPqRatchetInnerCapOkAt_mono protoPqRatchetStateAt_some_vn_eq protoPqRatchetStateCapOkAt
   protoPqRatchetStateCapOkAt_some_vn_eq sp_sub_1392_aligned vecU8CapOkAt_entails_rustBytesVecAt
   vecU8CapOkAt_mono wireType_ofNat64_ne_zero_of_ne_varint)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (BytesMergeEnv bytesMergeEventsCore)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced
   decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget
  (SepWPpIPlaced bytesMerge3DetBudgetSpec bytesMerge3RawBudgetSpecOfEnv
   decodeStateLoopCommonPlaced loopCommon_cursor_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationErrPlacedBudget
  (decodeState_err_53d2c_placed_ofEnv decodeState_err_53d68_placed_ofEnv
   decodeState_err_push_53d08_placed_ofEnv decodeState_err_push_53d44_placed_ofEnv
   decodeState_err_push_53d80_placed_ofEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Envelope-parameterized Tag 1 (`auth_key`, `0x53a20`, `+1412`): calls `bytes::merge` on
`vn.authKey` (`sp + 0x160`), then either jumps to `0x53d08` on error or returns via `0x53978..0x5397c`
to `0x53980` (`+1252`). -/
theorem decodeState_vn_tag1_53a20_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {BmPreEnv BmPostEnv : BytesMergeGhost → List AllocEvent → Prop}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (hbm : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpecOfEnv A lim BmPreEnv BmPostEnv)))
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : (mergeBytes (codecWireTypeToProto iwt) rest1).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits_bm : ∀ valCap valBuf : BitVec 64, BytesMergeCapOk valCap rest1.length →
      FitsEnv M lim st (BmPreEnv ⟨iwt, s0.sp - 1040#64, valCap, valBuf, vn.authKey,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩))
    (hfits_err1 : ∀ valCap valBuf evs_bm,
      (mergeBytes (codecWireTypeToProto iwt) rest1).toOption = none →
      BytesMergeCapOk valCap rest1.length →
      BmPostEnv ⟨iwt, s0.sp - 1040#64, valCap, valBuf, vn.authKey,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_bm →
      FitsEnv M lim (M.stepEvents evs_bm st) (DecodeErrorPushEnv 0))
    (hfits_err2 : ∀ valCap valBuf evs_bm evs_p1,
      (mergeBytes (codecWireTypeToProto iwt) rest1).toOption = none →
      BytesMergeCapOk valCap rest1.length →
      BmPostEnv ⟨iwt, s0.sp - 1040#64, valCap, valBuf, vn.authKey,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_bm →
      DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_bm st)) (DecodeErrorPushEnv 1))
    (henv_err : ∀ valCap valBuf evs_bm evs_p1 evs_p2 evs_f,
      (mergeBytes (codecWireTypeToProto iwt) rest1).toOption = none →
      BytesMergeCapOk valCap rest1.length →
      BmPostEnv ⟨iwt, s0.sp - 1040#64, valCap, valBuf, vn.authKey,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_bm →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_bm st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1412#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (bs' rest2 : List (BitVec 8)) (valCap valBuf : BitVec 64)
        (evs_bm : List AllocEvent) (sf : State) (P' : SepProp),
      (mergeBytes (codecWireTypeToProto iwt) rest1).toOption = some (bs', rest2) →
      BytesMergeCapOk valCap rest1.length →
      BmPostEnv ⟨iwt, s0.sp - 1040#64, valCap, valBuf, vn.authKey,
        s0.sp - 336#64, s0.sp - 1056#64,
        x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length), rest1⟩ evs_bm →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some { vn with authKey := bs' }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_bm st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
    protoPqRatchetStateCapOkAt_some_vn_eq]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc hbm ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 290)
  wp_steps_sync_pool (lsmpl.base 290)
  try simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  have hsp160 : s0.sp - 1392#64 + 352#64 = s0.sp - 1040#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_bytesMerge3_ofEnv hbm iwt (s0.sp - 1040#64) vn.authKey
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
    (ret_pc := (blkPl_325).base + 1424#64)
    (hpc := by simp only [wp_norm, arm64_norm])
    (hrun := by simp only [wp_norm, arm64_norm, hrun])
    (hsp := by simp only [wp_norm, arm64_norm, hsp])
    (hs0A := hs0A)
    (hlr := by simp only [wp_norm, arm64_norm])
    (htr := by simp only [wp_norm, arm64_norm, htr])
    (hx0 := by simp only [wp_norm, arm64_norm, hx0])
    (hx1 := by simp only [wp_norm, arm64_norm, hsp, hsp160])
    (hx2 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hfits := hfits_bm)
    (hP := by sep_focus) ?_ ?_
  · intro s1 bs' rest2 valCap valBuf evs_bm hmb hcap hevs_bm hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1252#64)
    wp_steps_sync_pool ((blkPl_325).base + 1252#64)
    try simp only [State.setMem_setMem]
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (optChainPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 992#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optCh) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
      (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    exact hloop bs' rest2 valCap valBuf evs_bm _ _ hmb hcap hevs_bm hle2 hsuf2
      (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
      (by simp only [wp_norm, arm64_norm, htr1])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by rw [protoPqRatchetStateCapOkAt_some_vn_eq]; dsimp only [decodeStateLoopCommonPlaced]; sep_ac_rfl)
  · intro s1 valCap valBuf evs_bm hmb hcap hevs_bm hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
      hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2156#64)
    wp_steps 1
    wp_if hcbz
    · exact absurd hcbz hx0_ne
    · wp_steps 1
      refine SepWP.fold (errFrame_parts_fold A.repAlloc x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
      refine SepWP.fold (optChainPBCapOkAt_entails_optChainPBAt A.repAlloc (s0.sp - 992#64)
        rest1.length optCh) (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner
        A.repAlloc (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_push_53d08_placed_ofEnv hc x st0
        (M.stepEvents evs_bm st) ⟨some vn, optCh, inner⟩ w0 0 s0 _ _ R post hpost
        (herr_of_none hmb) (by decide)
        (hfits_err1 valCap valBuf evs_bm hmb hcap hevs_bm)
        (fun evs_p1 hp1 => hfits_err2 valCap valBuf evs_bm evs_p1 hmb hcap hevs_bm hp1)
        (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree =>
          henv_err valCap valBuf evs_bm evs_p1 evs_p2 evs_f hmb hcap hevs_bm hp1 hp2 hfree)
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun1])
        (by simp only [wp_norm, arm64_norm, hsp1]) hs0A
        (by simp only [wp_norm, arm64_norm, htr1])
        (by simp only [wp_norm, arm64_norm, *])
        (by
          unfold decodeStateErrFramePlaced
          rw [protoPqRatchetStateAt_some_vn_eq]
          dsimp only [Reg.x0, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
            Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]
          sep_ac_rfl))

/-- Deterministic-envelope (`bytesMerge3DetBudgetSpec` / `BytesMergeEnv` + `DecodeStateEnv`)
Tag 1 (`auth_key`, `0x53a20`, `+1412`), matching `DecodeStateIterEnv.of_bytesMergeEnv`. -/
theorem decodeState_vn_tag1_53a20_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (hbm : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3DetBudgetSpec A lim)))
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : (mergeBytes (codecWireTypeToProto iwt) rest1).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits_bm : ∀ valCap : BitVec 64, BytesMergeCapOk valCap rest1.length →
      FitsEnv M lim st (fun evs => evs = bytesMergeEventsCore iwt valCap rest1))
    (hfits_err1 : ∀ valCap : BitVec 64,
      (mergeBytes (codecWireTypeToProto iwt) rest1).toOption = none →
      BytesMergeCapOk valCap rest1.length →
      FitsEnv M lim (M.stepEvents (bytesMergeEventsCore iwt valCap rest1) st)
        (DecodeErrorPushEnv 0))
    (hfits_err2 : ∀ (valCap : BitVec 64) evs_p1,
      (mergeBytes (codecWireTypeToProto iwt) rest1).toOption = none →
      BytesMergeCapOk valCap rest1.length →
      DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim
        (M.stepEvents evs_p1 (M.stepEvents (bytesMergeEventsCore iwt valCap rest1) st))
        (DecodeErrorPushEnv 1))
    (henv_err : ∀ (valCap : BitVec 64) evs_p1 evs_p2 evs_f,
      (mergeBytes (codecWireTypeToProto iwt) rest1).toOption = none →
      BytesMergeCapOk valCap rest1.length →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2
            (M.stepEvents evs_p1 (M.stepEvents (bytesMergeEventsCore iwt valCap rest1) st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1412#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (bs' rest2 : List (BitVec 8)) (valCap : BitVec 64)
        (sf : State) (P' : SepProp),
      (mergeBytes (codecWireTypeToProto iwt) rest1).toOption = some (bs', rest2) →
      BytesMergeCapOk valCap rest1.length →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some { vn with authKey := bs' }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim
          (M.stepEvents (bytesMergeEventsCore iwt valCap rest1) st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_vn_tag1_53a20_placed_ofEnv
    (BmPreEnv := BytesMergeEnv) (BmPostEnv := BytesMergeEnv)
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc hbm x st0 st w0 vn optCh inner rest1 limit iwt
    hrest1_le hrest1_suf hlen_bound herr_of_none s0 s P R post hpost
    (fun valCap _ hcap => hfits_bm valCap hcap)
    (fun valCap _ evs_bm hmb hcap hevs => by subst hevs; exact hfits_err1 valCap hmb hcap)
    (fun valCap _ evs_bm evs_p1 hmb hcap hevs hp1 => by
      subst hevs; exact hfits_err2 valCap evs_p1 hmb hcap hp1)
    (fun valCap _ evs_bm evs_p1 evs_p2 evs_f hmb hcap hevs hp1 hp2 hfree => by
      subst hevs; exact henv_err valCap evs_p1 evs_p2 evs_f hmb hcap hp1 hp2 hfree)
    hs0A hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP
    (fun bs' rest2 valCap _ evs_bm sf P' hmb hcap hevs => by
      subst hevs; exact hloop bs' rest2 valCap sf P' hmb hcap)

/-- Envelope-parameterized Tag 2 (`direction: i32`) in `VersionNegotiation` at
`0x539cc..0x539e4`, `0x53a50..0x53a58`, `0x5397c` (`+1328..+1352`, `+1460..+1468`, `+1248`). -/
theorem decodeState_vn_tag2_539cc_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_ne : iwt ≠ .varint → spqrDecodeState x.st.bytes = .error .stateDecode)
    (herr_of_none : iwt = .varint → decodeVarint rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits_dv : iwt = .varint → FitsEnv M lim st (DecodeVarint2Env rest1))
    (hfits_dv_err1 : ∀ evs_dv, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv →
      FitsEnv M lim (M.stepEvents evs_dv st) (DecodeErrorPushEnv 0))
    (hfits_dv_err2 : ∀ evs_dv evs_p1, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_dv st)) (DecodeErrorPushEnv 1))
    (henv_dv_err : ∀ evs_dv evs_p1 evs_p2 evs_f, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_dv st))))
    (hfits_ne1 : iwt ≠ .varint → FitsEnv M lim st DecodeErrorFromEnv)
    (hfits_ne2 : iwt ≠ .varint → ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (hfits_ne3 : iwt ≠ .varint → ∀ evs_fr evs_p1, DecodeErrorFromEnv evs_fr →
      DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 1))
    (henv_ne : iwt ≠ .varint → ∀ evs_fr evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1328#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (evs_dv : List AllocEvent)
        (sf : State) (P' : SepProp),
      iwt = .varint →
      decodeVarint rest1 = some (v, rest2) →
      DecodeVarint2Env rest1 evs_dv →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some { vn with direction := v.truncate 32 }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_dv st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hwt : iwt = .varint
  · subst hwt
    have hdv_call := hc.decodeVarint2
    subst hP
    rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
      protoPqRatchetStateCapOkAt_some_vn_eq]
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
      WireType.toNat] at hpc hdv_call hx0 ⊢
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
    wp_steps_sync_pool (lsmpl.base 291)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    refine SepWPpIPlaced.call_decodeVarint2 hdv_call
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
      (ret_pc := (blkPl_325).base + 1340#64)
      (hpc := by simp only [wp_norm, arm64_norm])
      (hrun := by simp only [wp_norm, arm64_norm, hrun])
      (hsp := by simp only [wp_norm, arm64_norm, hsp])
      (hs0A := hs0A)
      (hlr := by simp only [wp_norm, arm64_norm])
      (htr := by simp only [wp_norm, arm64_norm, htr])
      (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
      (hlen := by omega)
      (hfits := hfits_dv rfl)
      (hP := by sep_focus) ?_ ?_
    · intro s1 v rest2 evs_dv hdv hevs_dv hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
      have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
        hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_0 hx1_v hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      have hsp1_a : s1.spAligned = true := by
        rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1252#64)
      wp_steps_sync_pool ((blkPl_325).base + 1252#64)
      try simp only [State.setMem_setMem]
      refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
        hrest1_le hrest1_suf hle2) (by sep_focus) ?_
      refine SepWP.fold (vecU8CapOkAt_mono (A := A.repAlloc) (v := s0.sp - 1040#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (bs := vn.authKey) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (optChainPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 992#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (opt := optCh) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
        (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
      exact hloop v rest2 evs_dv _ _ rfl hdv hevs_dv hle2 hsuf2
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
        (by simp only [wp_norm, arm64_norm, htr1])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by
          rw [protoPqRatchetStateCapOkAt_some_vn_eq]
          dsimp only [decodeStateLoopCommonPlaced, BitVec.truncate]
          sep_ac_rfl)
    · intro s1 evs_dv hdv hevs_dv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
        hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2216#64)
      wp_steps 3
      wp_if hcbz
      · exact absurd hcbz hx1_ne
      · wp_steps 1
        refine SepWP.fold (errFrame_parts_fold A.repAlloc x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
        refine SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A.repAlloc (s0.sp - 1040#64)
          rest1.length vn.authKey) (by sep_focus) ?_
        refine SepWP.fold (optChainPBCapOkAt_entails_optChainPBAt A.repAlloc (s0.sp - 992#64)
          rest1.length optCh) (by sep_focus) ?_
        refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner
          A.repAlloc (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
        apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
        exact SepWPpIPlaced.of_sepWPp (decodeState_err_push_53d44_placed_ofEnv hc x st0
          (M.stepEvents evs_dv st) ⟨some vn, optCh, inner⟩ w0 0 s0 _ _ R post hpost
          (herr_of_none rfl hdv) (by decide)
          (hfits_dv_err1 evs_dv rfl hdv hevs_dv)
          (fun evs_p1 hp1 => hfits_dv_err2 evs_dv evs_p1 rfl hdv hevs_dv hp1)
          (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree =>
            henv_dv_err evs_dv evs_p1 evs_p2 evs_f rfl hdv hevs_dv hp1 hp2 hfree)
          (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun1])
          (by simp only [wp_norm, arm64_norm, hsp1]) hs0A
          (by simp only [wp_norm, arm64_norm, htr1])
          (by simp only [wp_norm, arm64_norm, *])
          (by
            unfold decodeStateErrFramePlaced
            rw [protoPqRatchetStateAt_some_vn_eq]
            dsimp only [Reg.x1, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
              Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            simp only [wp_norm, arm64_norm]
            sep_ac_rfl))
  · subst hP
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2192#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold
        (loopCommon_cursor_to_errFrame_placed H_inner A lim st x rest1 rest1.length
          ⟨some vn, optCh, inner⟩ s0 s)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_53d2c_placed_ofEnv hc x st0 st
        ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost (herr_of_ne hwt)
        (hfits_ne1 hwt)
        (fun evs_fr hfr => hfits_ne2 hwt evs_fr hfr)
        (fun evs_fr evs_p1 hfr hp1 => hfits_ne3 hwt evs_fr evs_p1 hfr hp1)
        (fun evs_fr evs_p1 evs_p2 evs_f hfr hp1 hp2 hfree =>
          henv_ne hwt evs_fr evs_p1 evs_p2 evs_f hfr hp1 hp2 hfree)
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        (by simp only [wp_norm, arm64_norm, hsp]) hs0A
        (by simp only [wp_norm, arm64_norm, htr])
        (by simp only [wp_norm, arm64_norm, hx19])
        (by simp only [wp_norm, arm64_norm, hx21])
        (by
          unfold decodeStateErrFramePlaced
          dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
            Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]
          sep_ac_rfl))
    · exact absurd hcbnz (wireType_ofNat64_ne_zero_of_ne_varint hwt)

theorem decodeState_vn_tag2_539cc_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_ne : iwt ≠ .varint → spqrDecodeState x.st.bytes = .error .stateDecode)
    (herr_of_none : iwt = .varint → decodeVarint rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits_dv : iwt = .varint → FitsEnv M lim st (DecodeVarint2Env rest1))
    (hfits_dv_err1 : ∀ evs_dv, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv →
      FitsEnv M lim (M.stepEvents evs_dv st) (DecodeErrorPushEnv 0))
    (hfits_dv_err2 : ∀ evs_dv evs_p1, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_dv st)) (DecodeErrorPushEnv 1))
    (henv_dv_err : ∀ evs_dv evs_p1 evs_p2 evs_f, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_dv st))))
    (hfits_ne1 : iwt ≠ .varint → FitsEnv M lim st DecodeErrorFromEnv)
    (hfits_ne2 : iwt ≠ .varint → ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (hfits_ne3 : iwt ≠ .varint → ∀ evs_fr evs_p1, DecodeErrorFromEnv evs_fr →
      DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 1))
    (henv_ne : iwt ≠ .varint → ∀ evs_fr evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1328#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (evs_dv : List AllocEvent)
        (sf : State) (P' : SepProp),
      iwt = .varint →
      decodeVarint rest1 = some (v, rest2) →
      DecodeVarint2Env rest1 evs_dv →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some { vn with direction := v.truncate 32 }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_dv st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_vn_tag2_539cc_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st w0 vn optCh inner rest1 limit iwt hrest1_le hrest1_suf hlen_bound
    herr_of_ne herr_of_none s0 s P R post hpost
    hfits_dv hfits_dv_err1 hfits_dv_err2 henv_dv_err
    hfits_ne1 hfits_ne2 hfits_ne3 henv_ne hs0A hpc hrun hsp htr
    hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hloop

/-- Envelope-parameterized Tag 3 (`min_version: i32`) in `VersionNegotiation` at
`0x53a34..0x53a4c`, `0x53a5c..0x53a64`, `0x5397c` (`+1432..+1456`, `+1472..+1480`, `+1248`). -/
theorem decodeState_vn_tag3_53a34_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_ne : iwt ≠ .varint → spqrDecodeState x.st.bytes = .error .stateDecode)
    (herr_of_none : iwt = .varint → decodeVarint rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)
    (hfits_dv : iwt = .varint → FitsEnv M lim st (DecodeVarint2Env rest1))
    (hfits_dv_err1 : ∀ evs_dv, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv →
      FitsEnv M lim (M.stepEvents evs_dv st) (DecodeErrorPushEnv 0))
    (hfits_dv_err2 : ∀ evs_dv evs_p1, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_dv st)) (DecodeErrorPushEnv 1))
    (henv_dv_err : ∀ evs_dv evs_p1 evs_p2 evs_f, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_dv st))))
    (hfits_ne1 : iwt ≠ .varint → FitsEnv M lim st DecodeErrorFromEnv)
    (hfits_ne2 : iwt ≠ .varint → ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (hfits_ne3 : iwt ≠ .varint → ∀ evs_fr evs_p1, DecodeErrorFromEnv evs_fr →
      DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 1))
    (henv_ne : iwt ≠ .varint → ∀ evs_fr evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, PostEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1432#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (evs_dv : List AllocEvent)
        (sf : State) (P' : SepProp),
      iwt = .varint →
      decodeVarint rest1 = some (v, rest2) →
      DecodeVarint2Env rest1 evs_dv →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some { vn with minVersion := v.truncate 32 }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_dv st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R) := by
  by_cases hwt : iwt = .varint
  · subst hwt
    have hdv_call := hc.decodeVarint2
    subst hP
    rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf,
      protoPqRatchetStateCapOkAt_some_vn_eq]
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced,
      WireType.toNat] at hpc hdv_call hx0 ⊢
    have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
    apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 291)
    wp_steps_sync_pool (lsmpl.base 291)
    try simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
    refine SepWPpIPlaced.call_decodeVarint2 hdv_call
      (s0.sp - 336#64) (s0.sp - 1056#64)
      (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1 st
      (ret_pc := (blkPl_325).base + 1444#64)
      (hpc := by simp only [wp_norm, arm64_norm])
      (hrun := by simp only [wp_norm, arm64_norm, hrun])
      (hsp := by simp only [wp_norm, arm64_norm, hsp])
      (hs0A := hs0A)
      (hlr := by simp only [wp_norm, arm64_norm])
      (htr := by simp only [wp_norm, arm64_norm, htr])
      (hx0 := by simp only [wp_norm, arm64_norm, hx29, hx29_f0])
      (hlen := by omega)
      (hfits := hfits_dv rfl)
      (hP := by sep_focus) ?_ ?_
    · intro s1 v rest2 evs_dv hdv hevs_dv hlt2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0 hx1_v
      have hle2 : rest2.length ≤ rest1.length := Nat.le_of_lt hlt2
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
        hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_0 hx1_v hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      have hsp1_a : s1.spAligned = true := by
        rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1252#64)
      wp_steps_sync_pool ((blkPl_325).base + 1252#64)
      try simp only [State.setMem_setMem]
      refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
        hrest1_le hrest1_suf hle2) (by sep_focus) ?_
      refine SepWP.fold (vecU8CapOkAt_mono (A := A.repAlloc) (v := s0.sp - 1040#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (bs := vn.authKey) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (optChainPBCapOkAt_mono (A := A.repAlloc) (a := s0.sp - 992#64)
        (rem1 := rest1.length) (rem2 := rest2.length) (opt := optCh) hle2)
        (by sep_focus) ?_
      refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_mono (H_inner := H_inner) (A := A.repAlloc)
        (a := s0.sp - 912#64) (rem1 := rest1.length) (rem2 := rest2.length) (opt := inner) hle2)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
      exact hloop v rest2 evs_dv _ _ rfl hdv hevs_dv hle2 hsuf2
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun1]) (by simp only [wp_norm, arm64_norm, hsp1])
        (by simp only [wp_norm, arm64_norm, htr1])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by
          rw [protoPqRatchetStateCapOkAt_some_vn_eq]
          dsimp only [decodeStateLoopCommonPlaced, BitVec.truncate]
          sep_ac_rfl)
    · intro s1 evs_dv hdv hevs_dv hpc1 hrun1 hsp1 htr1 hcs1 hx0_1 hx1_ne
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
        hx28_1, hx29_1, hvregs_1⟩
      simp only [arm64_norm, wp_norm] at hx0_1 hx1_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2276#64)
      wp_steps 3
      wp_if hcbz
      · exact absurd hcbz hx1_ne
      · wp_steps 1
        refine SepWP.fold (errFrame_parts_fold A.repAlloc x s0 hrest1_le hrest1_suf) (by sep_focus) ?_
        refine SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A.repAlloc (s0.sp - 1040#64)
          rest1.length vn.authKey) (by sep_focus) ?_
        refine SepWP.fold (optChainPBCapOkAt_entails_optChainPBAt A.repAlloc (s0.sp - 992#64)
          rest1.length optCh) (by sep_focus) ?_
        refine SepWP.fold (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner
          A.repAlloc (s0.sp - 912#64) rest1.length inner) (by sep_focus) ?_
        apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
        exact SepWPpIPlaced.of_sepWPp (decodeState_err_push_53d80_placed_ofEnv hc x st0
          (M.stepEvents evs_dv st) ⟨some vn, optCh, inner⟩ w0 0 s0 _ _ R post hpost
          (herr_of_none rfl hdv) (by decide)
          (hfits_dv_err1 evs_dv rfl hdv hevs_dv)
          (fun evs_p1 hp1 => hfits_dv_err2 evs_dv evs_p1 rfl hdv hevs_dv hp1)
          (fun evs_p1 evs_p2 evs_f hp1 hp2 hfree =>
            henv_dv_err evs_dv evs_p1 evs_p2 evs_f rfl hdv hevs_dv hp1 hp2 hfree)
          (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun1])
          (by simp only [wp_norm, arm64_norm, hsp1]) hs0A
          (by simp only [wp_norm, arm64_norm, htr1])
          (by simp only [wp_norm, arm64_norm, *])
          (by
            unfold decodeStateErrFramePlaced
            rw [protoPqRatchetStateAt_some_vn_eq]
            dsimp only [Reg.x1, Reg.x8, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
              Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
            simp only [wp_norm, arm64_norm]
            sep_ac_rfl))
  · subst hP
    dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry] at hpc ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2252#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold
        (loopCommon_cursor_to_errFrame_placed H_inner A lim st x rest1 rest1.length
          ⟨some vn, optCh, inner⟩ s0 s)
        (by sep_focus) ?_
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_53d68_placed_ofEnv hc x st0 st
        ⟨some vn, optCh, inner⟩ w0 s0 _ _ R post hpost (herr_of_ne hwt)
        (hfits_ne1 hwt)
        (fun evs_fr hfr => hfits_ne2 hwt evs_fr hfr)
        (fun evs_fr evs_p1 hfr hp1 => hfits_ne3 hwt evs_fr evs_p1 hfr hp1)
        (fun evs_fr evs_p1 evs_p2 evs_f hfr hp1 hp2 hfree =>
          henv_ne hwt evs_fr evs_p1 evs_p2 evs_f hfr hp1 hp2 hfree)
        (by dsimp only [decodeStatePlacedEntry]; simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        (by simp only [wp_norm, arm64_norm, hsp]) hs0A
        (by simp only [wp_norm, arm64_norm, htr])
        (by simp only [wp_norm, arm64_norm, hx19])
        (by simp only [wp_norm, arm64_norm, hx21])
        (by
          unfold decodeStateErrFramePlaced
          dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
            Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]
          sep_ac_rfl))
    · exact absurd hcbnz (wireType_ofNat64_ne_zero_of_ne_varint hwt)

theorem decodeState_vn_tag3_53a34_placed [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred} {v27 : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A lim ext)
    (x : DecodeStateGhost) (st0 st : M.σ) (w0 : BitVec 64)
    (vn : VersionNegotiationPB) (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner)
    (rest1 : List (BitVec 8)) (limit : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_ne : iwt ≠ .varint → spqrDecodeState x.st.bytes = .error .stateDecode)
    (herr_of_none : iwt = .varint → decodeVarint rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A lim (x, st0) s0 R)
    (hfits_dv : iwt = .varint → FitsEnv M lim st (DecodeVarint2Env rest1))
    (hfits_dv_err1 : ∀ evs_dv, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv →
      FitsEnv M lim (M.stepEvents evs_dv st) (DecodeErrorPushEnv 0))
    (hfits_dv_err2 : ∀ evs_dv evs_p1, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv → DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_dv st)) (DecodeErrorPushEnv 1))
    (henv_dv_err : ∀ evs_dv evs_p1 evs_p2 evs_f, iwt = .varint → decodeVarint rest1 = none →
      DecodeVarint2Env rest1 evs_dv →
      DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_dv st))))
    (hfits_ne1 : iwt ≠ .varint → FitsEnv M lim st DecodeErrorFromEnv)
    (hfits_ne2 : iwt ≠ .varint → ∀ evs_fr, DecodeErrorFromEnv evs_fr →
      FitsEnv M lim (M.stepEvents evs_fr st) (DecodeErrorPushEnv 0))
    (hfits_ne3 : iwt ≠ .varint → ∀ evs_fr evs_p1, DecodeErrorFromEnv evs_fr →
      DecodeErrorPushEnv 0 evs_p1 →
      FitsEnv M lim (M.stepEvents evs_p1 (M.stepEvents evs_fr st)) (DecodeErrorPushEnv 1))
    (henv_ne : iwt ≠ .varint → ∀ evs_fr evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))))
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1432#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest1.length
        ⟨some vn, optCh, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommonPlaced A lim st x s0 s)
    (hloop : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (evs_dv : List AllocEvent)
        (sf : State) (P' : SepProp),
      iwt = .varint →
      decodeVarint rest1 = some (v, rest2) →
      DecodeVarint2Env rest1 evs_dv →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 1252#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A.repAlloc (s0.sp - 1040#64) rest2.length
          ⟨some { vn with minVersion := v.truncate 32 }, optCh, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommonPlaced A lim (M.stepEvents evs_dv st) x s0 sf →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A lim (x, st0) s0 R) :=
  decodeState_vn_tag3_53a34_placed_ofEnv
    (PreEnv := DecodeStateEnv) (PostEnv := DecodeStateEnv)
    hc x st0 st w0 vn optCh inner rest1 limit iwt hrest1_le hrest1_suf hlen_bound
    herr_of_ne herr_of_none s0 s P R post hpost
    hfits_dv hfits_dv_err1 hfits_dv_err2 henv_dv_err
    hfits_ne1 hfits_ne2 hfits_ne3 henv_ne hs0A hpc hrun hsp htr
    hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hloop

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationPlacedBudgetAux

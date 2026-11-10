/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Proof
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Relocatable Dispatch & Variant Composition (Block `333`)

Lifts per-variant post-dispatch `SepWPp` obligations on Block `333` through the relocatable prologue
and `.rodata` jump table to `statesFromPbVariantPlacedSpec`, proves Variant 0 (`KeysUnsampled`), and
reduces `StatesFromPbPlacedOk*` to per-variant contracts.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced

section

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333

/-! ## 1. `SepWPp` Postcondition & Sequencing Helpers (`sfpProof_*_placed`) -/

/-- Sequence a clean `SepWP` step before a `SepWPp` continuation while threading `LibsignalCodeLoaded lsmpl`. -/
theorem sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm → SepWPp prog target sm P_mid Q Qp) :
    SepWPp prog target s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
      SepWPp.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

/-- Convert a `SepWPp` with `Entails`-based postcondition into the `Satisfies`-based postcondition
    expected by `subroutine_ok_of_sepWPp` for `statesFromPbVariantPlacedSpec`. -/
theorem sfpProof_sepWPp_of_states_body_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (P R : SepProp)
    (h : SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesFromPbVariantPlacedSpec A F pb).post (out, pbA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesFromPbVariantPlacedSpec A F pb).onPanic (out, pbA) s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, ⟨hPf, hspf, hcs, htrf⟩⟩ | hpan⟩ := h R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, ⟨fun hmem_f => ?_, hspf, hcs⟩⟩⟩
    dsimp only [statesFromPbVariantPlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htrf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by ac_rfl))) hmem_f⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- Convert a `SepWPp` with `Entails`-based postcondition into the `Satisfies`-based postcondition
    expected by `subroutine_ok_of_sepWPp` for `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb)`. -/
theorem sfpProof_sepWPp_of_states_body_cl_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (P R : SepProp)
    (h : SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb)).post (out, pbA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb)).onPanic (out, pbA) s0 sf ∗ R)) :=
  sfpProof_sepWPp_of_states_body_placed s0 s out pbA pb P R h

/-! ## 2. Canonical Per-Variant Step Shape & Prologue+Dispatch Wrappers -/

/-- Canonical post-dispatch `SepWPp` obligation at offset `off` in Block `333` for a
    `V1State.InnerState` variant `st`. -/
def StatesFromPbVariantStepPlaced [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State))
    (st : V1State.InnerState) (off : BitVec 64) : Prop :=
  ∀ (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp),
    LibsignalCodeLoaded lsmpl s1.mem →
    (s0.sp &&& 15#64 == 0#64) = true →
    s1.pc = lsmpl.base 333 + off →
    s1.status = .Running →
    s1.sp = s0.sp - 2400#64 →
    s1.readReg64 .x19 = out →
    s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 →
    s1.readReg64 .x27 = pbA →
    TraceCalleeSaved s1 s0 →
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some st) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some st }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))

/-- Lift a tagged-variant `StatesFromPbVariantStepPlaced` at `+off` to `subroutine_ok` for
    `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F { innerState := some st })`. -/
theorem sfpProof_tagged_ok_of_step_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    {st : V1State.InnerState} {tag off : BitVec 64} {Tail : BitVec 64 → SepProp}
    (htag : TaggedVariantDispatch tag off)
    (hinner : ∀ pbA, optProtoInnerStateAt A pbA (some st) = (pbA ↦₆₄ tag) ∗ Tail pbA)
    (hstep : v1StatePtsBound { innerState := some st } →
      StatesFromPbVariantStepPlaced A F ext st off) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F { innerState := some st })) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [statesFromPbVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hpts⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A pbA (some st) ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_from_pb_prologue_placed (ext := ext) s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A pbA (some st) ∗
     statesFromPbJumpTablePlacedAt ∗
     A.pool)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean_lscl hcl0 hpro ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, _, hx8_1, hx0_1, htr1⟩
  rw [hinner pbA]
  have hdisp := SepWP.weaken_pre
    (Entails.of_eq (show
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ tag) ∗ Tail pbA) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool =
      (pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
         memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Tail pbA ∗ A.pool) by ac_rfl))
    (states_from_pb_dispatch_tagged_placed (ext := ext) s0 s1 out pbA tag off _
      htag hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1)
  refine sepWPp_seq_clean_lscl hcl1 hdisp ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx27_2, _, _, _, _, hx23_2, htr2⟩
  rw [sfpProof_sp_sub_1552_eq s0.sp] at hx23_2
  have hbody := hstep hpts s0 s2 out pbA R hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx27_2 htr2
  have hpre_join :
      (pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
         memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Tail pbA ∗ A.pool) ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some st) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool := by
    rw [hinner pbA]
    have h2304 := sfpProof_fsp_0_and_2296_entails_2304 (s0.sp - 2400#64)
    refine Entails.trans
      (Entails.of_eq (show _ =
        (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         ((pbA ↦₆₄ tag) ∗ Tail pbA) ∗
         statesFromPbJumpTablePlacedAt ∗ A.pool) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by ac_rfl))
  exact SepWPp.weaken_pre hpre_join
    (sfpProof_sepWPp_of_states_body_cl_placed s0 s2 out pbA { innerState := some st } _ R hbody)

/-! ## 3. Variant 0 (`KeysUnsampled`, `+156`) Complete Subroutine Theorem -/

/-- Variant 0 (`InnerState.keysUnsampled`) of `<States>::from_pb`:
    combines `states_from_pb_prologue_placed`, `states_from_pb_dispatch_tagged_placed .keysUnsampled`, and
    `states_from_pb_keysUnsampled_156_placed` (from `Variant1bPlaced.lean`). -/
theorem states_from_pb_keysUnsampled_ok_ext_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s : V1State.Chunked.KeysUnsampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F { innerState := some (.keysUnsampled s) })) := by
  refine sfpProof_tagged_ok_of_step_placed TaggedVariantDispatch.keysUnsampled
    (Tail := fun pbA => protoChunkedKeysUnsampledAt A (pbA + 8#64) s ∗ memRegion (pbA + 64#64) 160)
    (fun _ => rfl) ?_
  intro _ s0 s1 out pbA R _hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1
  exact states_from_pb_keysUnsampled_156_placed hA s0 s1 out pbA s R
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1

/-! ## 4. Top-Level `<States>::from_pb` Composition & Stack-Frame Bridges -/

/-- Reduce `StatesFromPbPlacedOk A F ext` to `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb)`
    for each `pb : V1State`. -/
theorem states_from_pb_placed_ok_of_forall_pb [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hpb : ∀ pb : V1State,
      subroutine_ok (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333)
        (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb))) :
    StatesFromPbPlacedOk A F ext := by
  apply subroutine_ok_outcome_intro
  intro ⟨out, pbA, pb⟩ R s0 hpc hrun hpre halign
  exact subroutine_ok.mono_outcome (hpb pb) (out, pbA) R s0 hpc hrun hpre halign
    (fun _ hout => hout)

/-- Lift `StatesFromPbPlacedOk A F ext` (`statesFromPbStack = 7552`B) to
    `StatesFromPbPlacedOkExt A F ext` (`statesFromPbStackX` on `lsProg_333`). -/
theorem states_from_pb_placed_ok_ext_of_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hok : StatesFromPbPlacedOk A F ext) :
    StatesFromPbPlacedOkExt A F ext := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre halign
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  let Rextra := memRegion (s0.sp - BitVec.ofNat 64 statesFromPbStackX) sfpProof_stackXExtra
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (statesFromPbPlacedSpec A F)).pre x s0 ∗ (Rextra ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, Satisfies.mono ?_ hpre⟩
    dsimp only [statesFromPbPlacedSpecX, statesFromPbPlacedSpec, Rextra]
    rw [sfpProof_stackAt_statesFromPbStackX_eq s0.sp]
    exact Entails.of_eq (by ac_rfl)
  refine subroutine_ok.mono_outcome hok x (Rextra ∗ R) s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, ⟨hsp_f, hcs_f⟩, hpost⟩ | ⟨hpan_s, hpan⟩ | ⟨_code, _hexit_s, hexit⟩ | ⟨_hoom_s, hoom⟩)
  · left
    refine ⟨hret, ⟨hsp_f, hcs_f⟩, ?_⟩
    refine Satisfies.mono ?_ hpost
    dsimp only [withLsCodeLoaded, statesFromPbPlacedSpecX, statesFromPbPlacedSpec, Rextra]
    rw [sfpProof_stackAt_statesFromPbStackX_eq s0.sp]
    exact Entails.of_eq (by ac_rfl)
  · right; left
    refine ⟨hpan_s, ?_⟩
    refine Satisfies.mono ?_ hpan
    dsimp only [withLsCodeLoaded, statesFromPbPlacedSpecX, statesFromPbPlacedSpec, statesFromPbOnPanic]
    refine Entails.trans (Entails.of_eq (show
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ (Rextra ∗ R) =
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ (anyHeap ∗ Rextra)) ∗ R by ac_rfl)) ?_
    exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))
  · dsimp only [withLsCodeLoaded, statesFromPbPlacedSpec] at hexit
    exact (not_satisfies_false_sepConj hexit).elim
  · dsimp only [withLsCodeLoaded, statesFromPbPlacedSpec] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-- Reduce `StatesFromPbPlacedOkExt A F ext` directly to `statesFromPbVariantPlacedSpec`
    for each `pb : V1State`. -/
theorem states_from_pb_ok_of_forall_pb_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hpb : ∀ pb : V1State,
      subroutine_ok (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333)
        (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb))) :
    StatesFromPbPlacedOkExt A F ext :=
  states_from_pb_placed_ok_ext_of_ok (states_from_pb_placed_ok_of_forall_pb hpb)

/-- Lift `StatesFromPbPlacedOkExt A F ext` (`lsProg_333`, `withLsCodeLoaded`) to
    `StatesFromPbPlacedOkX A F ext` (`libsignalSessionLib.blockProgram lsmpl 333`, `withLsCodeRoLoaded`). -/
theorem states_from_pb_okX_of_ok_ext_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hok : StatesFromPbPlacedOkExt A F ext) :
    StatesFromPbPlacedOkX A F ext := by
  unfold StatesFromPbPlacedOkX
  rw [← IsLsBlockProg.eq_blockProgram (prog := lsProg_333 (Rust.withPanics ext))
    (i := 333) (H := Rust.withPanics ext)]
  exact subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hok

/-- Lift `StatesFromPbPlacedOk A F ext` (`statesFromPbStack = 7552`B, `withLsCodeLoaded`) directly to
    `StatesFromPbPlacedOkX A F ext` (`statesFromPbStackX`, `withLsCodeRoLoaded`). -/
theorem states_from_pb_okX_of_ok_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hok : StatesFromPbPlacedOk A F ext) :
    StatesFromPbPlacedOkX A F ext :=
  states_from_pb_okX_of_ok_ext_placed (states_from_pb_placed_ok_ext_of_ok hok)

end

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  sepWPp_seq_clean_lscl
  sfpProof_sepWPp_of_states_body_placed
  sfpProof_sepWPp_of_states_body_cl_placed
  StatesFromPbVariantStepPlaced
  sfpProof_tagged_ok_of_step_placed
  states_from_pb_keysUnsampled_ok_ext_placed
  states_from_pb_placed_ok_of_forall_pb
  states_from_pb_placed_ok_ext_of_ok
  states_from_pb_ok_of_forall_pb_placed
  states_from_pb_okX_of_ok_ext_placed
  states_from_pb_okX_of_ok_placed
)

end CryptoVerification.SpqrV1.States.FromPb

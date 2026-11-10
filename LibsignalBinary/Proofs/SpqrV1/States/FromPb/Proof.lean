/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Top-Level Dispatch & Variant Composition (`0x5a0a4`)

Combines the prologue and `.rodata` jump-table dispatch with per-variant `SepWPp` body obligations,
proves Variant 0 (`KeysUnsampled`), and reduces `StatesFromPbOkExt` / `StatesFromPbOkX` to
per-variant `statesFromPbVariantSpec` obligations.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Stack, Tag, & `SepWPp` Postcondition Helpers (`sfpProof_*`) -/

theorem sfpProof_fsp_0_and_2296_entails_2304 (fsp : BitVec 64) :
    (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 2296 ⊢ memRegion fsp 2304 :=
  cell0_2296_entails_memRegion_2304 fsp 0#64

theorem sfpProof_sp_sub_1552_eq (sp0 : BitVec 64) :
    sp0 - 1552#64 = (sp0 - 2400#64) + 848#64 := by bv_omega

/-- Convert a `SepWPp` with `Entails`-based postcondition into the `Satisfies`-based postcondition
    expected by `subroutine_ok_of_sepWPp` for `statesFromPbVariantSpec`. -/
theorem sfpProof_sepWPp_of_states_body {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (P R : SepProp)
    (h : SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗
          A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesFromPbVariantSpec A F b pb).post (out, pbA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesFromPbVariantSpec A F b pb).onPanic (out, pbA) s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, ⟨hPf, hspf, hcs, htrf⟩⟩ | hpan⟩ := h R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, ⟨fun hmem_f => ?_, hspf, hcs⟩⟩⟩
    dsimp only [statesFromPbVariantSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htrf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by ac_rfl))) hmem_f⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-! ## 2. Canonical Per-Variant Step Shape & Prologue+Dispatch Wrappers -/

/-- Canonical post-dispatch `SepWPp` obligation at offset `off` for a `V1State.InnerState` variant `st`
    (matching `Variant1b.states_from_pb_keysUnsampled_156`). -/
def StatesFromPbVariantStep
    (A : RustAlloc) (F : ShaCompress) (b : BitVec 64)
    (ext : String → Option (State → State))
    (st : V1State.InnerState) (off : BitVec 64) : Prop :=
  ∀ (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp),
    (s0.sp &&& 15#64 == 0#64) = true →
    s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + off →
    s1.status = .Running →
    s1.sp = s0.sp - 2400#64 →
    s1.readReg64 .x19 = out →
    s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 →
    s1.readReg64 .x27 = pbA →
    TraceCalleeSaved s1 s0 →
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some st) ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some st }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))

/-- Lift a tagged-variant `StatesFromPbVariantStep` at `+off` to `subroutine_ok` for
    `statesFromPbVariantSpec A F b { innerState := some st }`. -/
theorem sfpProof_tagged_ok_of_step
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    {st : V1State.InnerState} {tag off : BitVec 64} {Tail : BitVec 64 → SepProp}
    (htag : TaggedVariantDispatch tag off)
    (hinner : ∀ pbA, optProtoInnerStateAt A pbA (some st) = (pbA ↦₆₄ tag) ∗ Tail pbA)
    (hstep : v1StatePtsBound { innerState := some st } →
      StatesFromPbVariantStep A F b ext st off) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := some st }) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [statesFromPbVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb_align, hpts⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A pbA (some st) ∗
       statesFromPbJumpTableAt b ∗
       A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  have hpro := states_from_pb_prologue (b := b) (ext := ext) s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A pbA (some st) ∗
     statesFromPbJumpTableAt b ∗
     A.pool)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, _, hx8_1, hx0_1, htr1⟩
  rw [hinner pbA]
  have hdisp := SepWP.weaken_pre
    (Entails.of_eq (show
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        ((pbA ↦₆₄ tag) ∗ Tail pbA) ∗
        statesFromPbJumpTableAt b ∗ A.pool =
      (pbA ↦₆₄ tag) ∗ statesFromPbJumpTableAt b ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
         memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Tail pbA ∗ A.pool) by ac_rfl))
    (states_from_pb_dispatch_tagged s0 s1 out pbA tag off _
      htag hb_align hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1)
  refine sepWPp_seq_clean hdisp ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx27_2, _, _, _, _, hx23_2, htr2⟩
  rw [sfpProof_sp_sub_1552_eq s0.sp] at hx23_2
  have hbody := hstep hpts s0 s2 out pbA R hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx27_2 htr2
  have hpre_join :
      (pbA ↦₆₄ tag) ∗ statesFromPbJumpTableAt b ∗
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
        statesFromPbJumpTableAt b ∗
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
         statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by ac_rfl))
  exact SepWPp.weaken_pre hpre_join
    (sfpProof_sepWPp_of_states_body s0 s2 out pbA { innerState := some st } _ R hbody)

/-! ## 3. Variant 0 (`KeysUnsampled`, `+156`) Complete Subroutine Theorem -/

/-- Variant 0 (`InnerState.keysUnsampled`) of `<States>::from_pb`:
    combines `states_from_pb_prologue`, `states_from_pb_dispatch_tagged .keysUnsampled`, and
    `states_from_pb_keysUnsampled_156` (from `Variant1b.lean`). -/
theorem states_from_pb_keysUnsampled_ok_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s : V1State.Chunked.KeysUnsampled) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := some (.keysUnsampled s) }) := by
  refine sfpProof_tagged_ok_of_step TaggedVariantDispatch.keysUnsampled
    (Tail := fun pbA => protoChunkedKeysUnsampledAt A (pbA + 8#64) s ∗ memRegion (pbA + 64#64) 160)
    (fun _ => rfl) ?_
  intro _ s0 s1 out pbA R hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1
  exact states_from_pb_keysUnsampled_156 hA s0 s1 out pbA s R
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1

/-! ## 4. Top-Level `<States>::from_pb` Composition -/

/-- Reduce `StatesFromPbOkExt b A F ext` to `statesFromPbVariantSpec` for each `pb : V1State`. -/
theorem states_from_pb_ok_of_forall_pb
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hpb : ∀ pb : V1State,
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
        (statesFromPbVariantSpec A F b pb)) :
    StatesFromPbOkExt b A F ext := by
  apply subroutine_ok_outcome_intro
  intro ⟨out, pbA, pb⟩ R s0 hpc hrun hpre halign
  exact subroutine_ok.mono_outcome (hpb pb) (out, pbA) R s0 hpc hrun hpre halign (fun _ hout => hout)

/-! ## 5. Stack-Framed Bridge from `StatesFromPbOkExt` to `StatesFromPbOkX` -/

abbrev sfpProof_stackXExtra : Nat := statesFromPbStackX - statesFromPbStack

theorem sfpProof_stackAt_statesFromPbStackX_eq (sp : BitVec 64) :
    stackAt sp statesFromPbStackX =
      memRegion (sp - BitVec.ofNat 64 statesFromPbStackX) sfpProof_stackXExtra ∗
      stackAt sp statesFromPbStack := by
  have heq : statesFromPbStack + sfpProof_stackXExtra = statesFromPbStackX := by decide
  rw [← heq]
  exact ProofLib.stackAt_split_bottom sp statesFromPbStack sfpProof_stackXExtra (by decide)

/-- Lift `StatesFromPbOkExt img.base A F ext` (`statesFromPbStack = 7552`B) to
    `StatesFromPbOkX img A F ext` (`statesFromPbStackX`, `.inImage img`). -/
theorem states_from_pb_okX_of_ok_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hok : StatesFromPbOkExt img.base A F ext) :
    StatesFromPbOkX img A F ext := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre halign
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (statesFromPbSpecX A F img.base).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hinv, hpre⟩
  let Rextra := memRegion (s0.sp - BitVec.ofNat 64 statesFromPbStackX) sfpProof_stackXExtra
  have hpre' : s0.mem ⊨ (statesFromPbSpec A F img.base).pre x s0 ∗ (Rextra ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [statesFromPbSpecX, statesFromPbSpec, Rextra]
    rw [sfpProof_stackAt_statesFromPbStackX_eq s0.sp]
    exact Entails.of_eq (by ac_rfl)
  refine subroutine_ok.mono_outcome hok x (Rextra ∗ R) s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, ⟨hsp_f, hcs_f⟩, hpost⟩ | ⟨hpan_s, hpan⟩ | ⟨_code, _hexit_s, hexit⟩ | ⟨_hoom_s, hoom⟩)
  · left
    refine ⟨hret, ⟨hsp_f, hcs_f⟩, ?_⟩
    refine Satisfies.mono ?_ hpost
    dsimp only [Spec.inImage, statesFromPbSpecX, statesFromPbSpec, Rextra]
    rw [sfpProof_stackAt_statesFromPbStackX_eq s0.sp]
    exact Entails.of_eq (by ac_rfl)
  · right; left
    refine ⟨hpan_s, ?_⟩
    refine Satisfies.mono ?_ hpan
    dsimp only [Spec.inImage, statesFromPbSpecX, statesFromPbSpec, statesFromPbOnPanic]
    refine Entails.trans (Entails.of_eq (show
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ (Rextra ∗ R) =
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ (anyHeap ∗ Rextra)) ∗ R by ac_rfl)) ?_
    exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))
  · dsimp only [statesFromPbSpec] at hexit
    exact (not_satisfies_false_sepConj hexit).elim
  · dsimp only [statesFromPbSpec] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.SpqrV1.States.FromPb

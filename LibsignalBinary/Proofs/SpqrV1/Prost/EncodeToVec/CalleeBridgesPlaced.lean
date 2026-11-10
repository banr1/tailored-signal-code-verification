/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.EncodedLenCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Base
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLen
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1State
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4

/-!
# `PqRatchetState::encode_to_vec` (Block `426`): Placed Callee Contract Bridges

Cross-block `[LibsignalPlacement]` `subroutine_ok` transfer lemmas and placed hook/callee bridges
into Block `426`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Varint

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr

/-- Transfer a plain block `j` `subroutine_ok` into `withStepInv s0 spec` on `Block 426`. -/
theorem etv_subroutine_ok_placed_of_plain [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee_prog : IsLsBlockProg calleeProg j H]
    {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) spec)
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base j)
      (withStepInv s0 spec) :=
  subroutine_ok_withStepInv_lscl hcl0
    (ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain hcallee) (by decide) hj hj_unmut)

/-- Transfer a `withLsCodeLoaded lsmpl spec` block `j` `subroutine_ok` into `withStepInv s0 spec` on `Block 426`. -/
theorem etv_subroutine_ok_placed_of_lscl [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee_prog : IsLsBlockProg calleeProg j H]
    {spec : Spec α} {s0 : State}
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base j)
      (withStepInv s0 spec) :=
  subroutine_ok_withStepInv_lscl hcl0
    (ls_subroutine_ok_of_block hcallee (by decide) hj hj_unmut)

theorem etv_chainEncodedLen_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (lsmpl.base 406)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)) :=
  etv_subroutine_ok_placed_of_lscl hcl0 (chainEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem etv_v1StateEncodedLen_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (lsmpl.base 405)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (lsρ v1StateJtSymLocal2))) :=
  etv_subroutine_ok_placed_of_lscl hcl0 (v1StateEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem etv_handle_alloc_error_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) :
    ((blkPC_426).rebase (blkPl_426).base H).externAt?
      ((blkPl_426).ρ spqrHandleErrorSym) = some Rust.panicked := by
  rw [ls_blockPlacement_ρ]
  exact (ls_externAt?_of_mem (H := H) (sym := spqrHandleErrorSym)).trans h_panic

theorem etv_shim_placed_ok [LibsignalPlacement] {resStack : Nat}
    {H : String → Option (State → State)}
    (hshim_sat : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (s0 : State) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ spqrRustNoAllocShimSym)
      (withStepInv s0 (shimStackSpecOf resStack)) := by
  rw [ls_blockPlacement_ρ]
  have hshim : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec :=
    ls_hook_ok_of_mem hshim_sat
  apply subroutine_ok_withStepInv s0
  apply subroutine_ok_outcome_intro
  intro u R s hpc hrun hpre hal
  dsimp only [shimStackSpecOf] at hpre
  have hpre' : s.mem ⊨ noAllocShimSpec.pre u s ∗ (stackAt s.sp (encodeToVecCalleeStackOf resStack) ∗ R) := by
    dsimp only [noAllocShimSpec]; rw [emp_sepConj]
    exact hpre
  refine hshim.mono_outcome u (stackAt s.sp (encodeToVecCalleeStackOf resStack) ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [noAllocShimSpec, shimStackSpecOf] at hpost ⊢
    rwa [sepConj_assoc]
  · exact (allowPanic_not_exited hpan).elim
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

theorem stackAt_callee_eq_allocHook_placed {resStack : Nat}
    (hlow : allocHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack))
        (encodeToVecCalleeStackOf resStack - allocHookStack) ∗
        stackAt sp1 allocHookStack := by
  have h := ProofLib.stackAt_split_bottom sp1 allocHookStack
    (encodeToVecCalleeStackOf resStack - allocHookStack) (by omega)
  have heq : allocHookStack + (encodeToVecCalleeStackOf resStack - allocHookStack) =
      encodeToVecCalleeStackOf resStack := by omega
  simpa only [heq] using h

theorem etv_rustAlloc_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hlow : allocHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    {A : RustAlloc} {H : String → Option (State → State)}
    (halloc_sat : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (s0 : State) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ spqrRustAllocSym)
      (withStepInv s0 (rustAllocStackSpecOf resStack A)) := by
  rw [ls_blockPlacement_ρ]
  have halloc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    ls_hook_ok_of_mem halloc_sat
  apply subroutine_ok_withStepInv s0
  apply subroutine_ok_outcome_intro
  intro sz R s hpc hrun hpre hal
  dsimp only [rustAllocStackSpecOf] at hpre
  rw [stackAt_callee_eq_allocHook_placed hlow hhigh s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack))
    (encodeToVecCalleeStackOf resStack - allocHookStack)
  have hpre' : s.mem ⊨ (rustAllocSpec A).pre (sz, 1) s ∗ (F_rem ∗ R) := by
    dsimp only [rustAllocSpec]
    simp only [satisfies_pure_sepConj, sepConj_assoc] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hpos, hlt⟩, hm⟩
    have hx1' : (s.readReg64 .x1).toNat = 1 := by rw [hx1]; rfl
    refine ⟨⟨hx0, hx1', hpos, ⟨0, rfl⟩, by omega⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hm
  refine halloc.mono_outcome (sz, 1) (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocSpec, rustAllocStackSpecOf] at hpost ⊢
    simp only [Nat.mod_one, true_and] at hpost
    rw [stackAt_callee_eq_allocHook_placed hlow hhigh s.sp]
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hpost
  · exact (allowPanic_not_exited hpan).elim
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_memcpy_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hmc_sat : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy")
      etvMemcpyRegionSpec := by
  rw [ls_blockPlacement_ρ]
  exact ls_hook_ok_of_mem hmc_sat

theorem etv_epochEncodedLen_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64)
    (A : RustAlloc) (ext : String → Option (State → State)) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (lsmpl.base 399)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)) := by
  have hep : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (lsmpl.base 399) (withLsCodeLoaded lsmpl (epochEncodedLenPinnedSpec A)) :=
    ls_subroutine_ok_of_block
      (subroutine_ok_withLsCodeLoaded_of_plain (epochEncodedLen_local2_pinned_placed_ok_ext A ext))
      (by decide) (by decide) (by decide)
  apply subroutine_ok_withStepInv_lscl hcl0
  apply subroutine_ok_outcome_intro
  intro ⟨a, g, ep⟩ R s hpc hrun hpre hal
  obtain ⟨hcl_s, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [epochEncLenStackSpecOf] at hpre
  rw [stackAt_callee_eq_unchunkedEncodedLen hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (160 + resStack)
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfit⟩, hm⟩
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl (epochEncodedLenPinnedSpec A)).pre ⟨a, g, ep⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [withLsCodeLoaded, epochEncodedLenPinnedSpec, EpochEncodedLenFits]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl_s, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem, epochEncodedLenStack, unchunkedEncodedLenStack]; ac_rfl)) hm
  refine hep.mono_outcome ⟨a, g, ep⟩ (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, epochEncodedLenPinnedSpec, epochEncLenStackSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_unchunkedEncodedLen hres s.sp]
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem, epochEncodedLenStack, unchunkedEncodedLenStack]; ac_rfl)) hpost
  · exact (allowPanic_not_exited hpan).elim
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

private theorem elim_exact_cap_ptr_placed {A : RustAlloc} {v cap ptr : BitVec 64}
    {bs1 bs2 : List (BitVec 8)} (hfit : bs1.length + bs2.length ≤ cap.toNat) :
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜cap.toNat ≤ cap'.toNat ∧ (bs1.length + bs2.length ≤ cap.toNat → cap' = cap ∧ ptr' = ptr)⌝ ∗
      vecU8At A v cap' ptr' (bs1 ++ bs2)) ⊢
    vecU8At A v cap ptr (bs1 ++ bs2) :=
  Entails.sepExists_elim fun cap' =>
    Entails.sepExists_elim fun ptr' =>
      Entails.pure_left fun ⟨_, hpres⟩ => by
        obtain ⟨rfl, rfl⟩ := hpres hfit
        exact Entails.refl _

private theorem etv_or_80_truncate8_and_7f (a : BitVec 64) :
    (a.truncate 8 ||| 0x80#8) = ((a &&& 0x7F#64) ||| 0x80#64).setWidth 8 := by
  bv_bits

private theorem etv_protoEncodeVarintAux_eq_codec_of_lt (fuel : Nat) (a : BitVec 64)
    (hbound : a >>> (7 * fuel) < 0x80#64) :
    Proto.encodeVarintAux (fuel + 1) a =
      CryptoVerification.LibsignalProtoCodec.encodeVarintAux (fuel + 1) a := by
  induction fuel generalizing a with
  | zero =>
    simp only [Nat.mul_zero, BitVec.ushiftRight_zero] at hbound
    have h' : a.toNat < 0x80 := BitVec.lt_def.mp hbound
    simp only [Proto.encodeVarintAux, CryptoVerification.LibsignalProtoCodec.encodeVarintAux,
      hbound, h', ↓reduceIte]
  | succ fuel ih =>
    rw [Proto.encodeVarintAux, CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
    have hlt_iff : (a < 0x80#64) ↔ (a.toNat < 0x80) := BitVec.lt_def
    by_cases h : a < 0x80#64
    · have h' : a.toNat < 0x80 := hlt_iff.mp h
      simp only [h, h', ↓reduceIte]
    · have h' : ¬ a.toNat < 0x80 := fun hc => h (hlt_iff.mpr hc)
      have hb' : (a >>> 7) >>> (7 * fuel) < 0x80#64 := by
        have hsh : (a >>> 7) >>> (7 * fuel) = a >>> (7 * (fuel + 1)) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
            ← Nat.pow_add]
          congr 2; omega
        rw [hsh]; exact hbound
      simp only [h, h', ↓reduceIte, etv_or_80_truncate8_and_7f a, ih (a >>> 7) hb']
      rfl

private theorem etv_protoEncodeVarint_eq_codec (a : BitVec 64) :
    Proto.encodeVarint a = CryptoVerification.LibsignalProtoCodec.encodeVarint a := by
  refine etv_protoEncodeVarintAux_eq_codec_of_lt 9 a ?_
  change a >>> 63 < 0x80#64
  bv_bits

theorem etv_encodeVarint_exact_of_fit_placed {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {prog : Program} {call_pc : BitVec 64}
    {A : RustAlloc} {s0 : State}
    (hfit_ok : subroutine_ok prog call_pc (withStepInv s0 (encodeVarintFitSpecOf resStack A))) :
    subroutine_ok prog call_pc (withStepInv s0 (encodeVarintExactSpecOf resStack A)) := by
  apply subroutine_ok_outcome_intro
  intro x R s hpc hrun hpre hal
  dsimp only [withStepInv, encodeVarintExactSpecOf] at hpre
  rw [stackAt_callee_eq_encodeVarint hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 128
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hfit' : x.bs.length + (LibsignalProtoCodec.encodeVarint x.val).length ≤ x.cap.toNat := by
    rwa [← etv_protoEncodeVarint_eq_codec]
  have hpre' : s.mem ⊨ (withStepInv s0 (encodeVarintFitSpecOf resStack A)).pre
      ⟨x.val, x.v, x.cap, x.ptr, x.bs⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [withStepInv, encodeVarintFitSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, Or.inl hfit'⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem]; ac_rfl)) hm
  refine hfit_ok.mono_outcome ⟨x.val, x.v, x.cap, x.ptr, x.bs⟩ (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodeVarintFitSpecOf, encodeVarintSpecOf, encodeVarintExactSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_encodeVarint hres s.sp, etv_protoEncodeVarint_eq_codec]
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (elim_exact_cap_ptr_placed hfit')))) ?_
    exact Entails.of_eq (by dsimp only [F_rem]; ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStepInv, encodeVarintFitSpecOf, encodeVarintSpec,
      encodeVarintExactSpecOf, encodeToVecOnPanic] at hq ⊢
    rw [← sepConj_assoc] at hq
    exact allowPanic_frame id hq
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_encodeVarint_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf doReserveStack A)) :=
  etv_encodeVarint_exact_of_fit_placed (by decide)
    (etv_subroutine_ok_placed_of_lscl hcl0
      (encode_varint4_fit_placed_ok h_panic hshim halloc hrealloc))

theorem etv_leafEncLen16_withStepInv_placed {G M : Type}
    {reprAt : G → BitVec 64 → M → SepProp} {encLen : M → Nat}
    {prog : Program} {call_pc : BitVec 64} {s0 : State}
    (hok : subroutine_ok prog call_pc (leafEncLen16Spec reprAt encLen)) :
    subroutine_ok prog call_pc (withStepInv s0 (leafEncLen16Spec reprAt encLen)) := by
  apply subroutine_ok_outcome_intro
  intro x R s hpc hrun hpre hal
  dsimp only [withStepInv, leafEncLen16Spec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hpre'⟩
  refine hok.mono_outcome x R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · simp only [leafEncLen16Spec, satisfies_pure_sepConj] at hpan; exact hpan.1.elim
  · simp only [leafEncLen16Spec, satisfies_pure_sepConj] at hex; exact hex.1.elim
  · simp only [leafEncLen16Spec, satisfies_pure_sepConj] at hoom; exact hoom.1.elim

theorem etv_leafEncLen48_withStepInv_placed {G M : Type}
    {reprAt : G → BitVec 64 → M → SepProp} {encLen : M → Nat}
    {prog : Program} {call_pc : BitVec 64} {s0 : State}
    (hok : subroutine_ok prog call_pc (leafEncLen48Spec reprAt encLen)) :
    subroutine_ok prog call_pc (withStepInv s0 (leafEncLen48Spec reprAt encLen)) := by
  apply subroutine_ok_outcome_intro
  intro x R s hpc hrun hpre hal
  dsimp only [withStepInv, leafEncLen48Spec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hpre'⟩
  refine hok.mono_outcome x R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · simp only [leafEncLen48Spec, satisfies_pure_sepConj] at hpan; exact hpan.1.elim
  · simp only [leafEncLen48Spec, satisfies_pure_sepConj] at hex; exact hex.1.elim
  · simp only [leafEncLen48Spec, satisfies_pure_sepConj] at hoom; exact hoom.1.elim

end CryptoVerification.SpqrV1.Prost.EncodeToVec

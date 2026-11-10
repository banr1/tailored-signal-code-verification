/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `spqr::decode_state` Empty-State Leaf and `sessionMemcpySpec` Stack-Slack Weakening

Verifies `spqr::decode_state` on an empty byte slice, lifts `memcpyRecvPcsSpec` to
`extHookStack = 16384`, and proves stack-slack weakening for `sessionMemcpySpec` from `externStack`
to any `s2 ≥ externStack` on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack-slack weakening for `sessionMemcpySpec` -/

/-- Stack-slack weakening for `sessionMemcpySpec`: from `externStack = 16384` to any caller stack
slack `externStack ≤ s2 ≤ 2^64` (e.g. `deserCalleeStack = 32768`). -/
theorem subroutine_ok_sessionMemcpySpec_mono {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {s2 : Nat}
    (hle : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)) :
    subroutine_ok prog entry ((sessionMemcpySpec s2).inImage img) := by
  refine subroutine_ok_inImage_map' h (fun ⟨dst, src, bs⟩ R s0 hpre => ?_)
  have hsplit : s2 = CryptoVerification.LibsignalTripleRatchet.extHookStack + (s2 - CryptoVerification.LibsignalTripleRatchet.extHookStack) := by omega
  have hstack_pre : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack := by
    have h0 := ProofLib.stackAt_split_bottom s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack (s2 - CryptoVerification.LibsignalTripleRatchet.extHookStack) (by omega)
    rwa [← hsplit] at h0
  dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hpure, hmem⟩ := hpre
  rw [hstack_pre] at hmem
  refine ⟨(dst, src, bs), memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R, ?_, ?_⟩
  · dsimp only [sessionMemcpySpec, libcMemcpySpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
  · intro sf hpost
    dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨hpure_post, hmem_post⟩ := hpost
    rw [hstack_pre]
    exact ⟨hpure_post, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem_post⟩

/-! ## Relocatable `[LibsignalPlacement]` stack-slack weakening -/

section Placed

/-- Stack-slack weakening for `sessionMemcpySpec` under `withLsCodeLoaded pl`. -/
theorem subroutine_ok_withLsCodeLoaded_sessionMemcpySpec_mono {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {s2 : Nat}
    (hle : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry
      (withLsCodeLoaded pl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (sessionMemcpySpec s2)) := by
  refine subroutine_ok_withLsCodeLoaded_map' h (fun ⟨dst, src, bs⟩ R s0 hpre => ?_)
  have hsplit : s2 = CryptoVerification.LibsignalTripleRatchet.extHookStack +
      (s2 - CryptoVerification.LibsignalTripleRatchet.extHookStack) := by omega
  have hstack_pre : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗
        stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack := by
    have h0 := ProofLib.stackAt_split_bottom s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack
      (s2 - CryptoVerification.LibsignalTripleRatchet.extHookStack) (by omega)
    rwa [← hsplit] at h0
  dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hpure, hmem⟩ := hpre
  rw [hstack_pre] at hmem
  refine ⟨(dst, src, bs),
    memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R,
    ?_, ?_⟩
  · dsimp only [sessionMemcpySpec, libcMemcpySpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
  · intro sf hpost
    dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨hpure_post, hmem_post⟩ := hpost
    rw [hstack_pre]
    exact ⟨hpure_post, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem_post⟩

/-- Stack-slack weakening for `sessionMemcpySpec` under `withLsCl pl`. -/
theorem subroutine_ok_withLsCl_sessionMemcpySpec_mono {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {s2 : Nat}
    (hle : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry
      (withLsCl pl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok prog entry (withLsCl pl (sessionMemcpySpec s2)) := by
  apply ls_subroutine_ok_cl_of_withLsCodeLoaded
  have h0 : subroutine_ok prog entry
      (withLsCodeLoaded pl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack)) :=
    subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)
  exact subroutine_ok_withLsCodeLoaded_sessionMemcpySpec_mono hle hbound h0

end Placed

end Proofs.libsignal.Hooks2


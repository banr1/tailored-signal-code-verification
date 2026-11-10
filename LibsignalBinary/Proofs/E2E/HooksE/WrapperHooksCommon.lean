/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.HooksE.Common
import ProofLib.VCGen

/-!
# Shared Wrapper Hook Witnesses

Proves `HookOk` for `stringCloneHook0` (`stringCloneSpec A0`) and `timeAddHook` (`timeAddSpec`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.HooksE

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.NonVacuityWitness
  (A₀ witnessDeallocHook witnessDeallocHook_ok satisfies_mapFresh_unmapped
   readReg64_setPC_writeReg64_x0)
open CryptoVerification.E2E
open HooksOkAux


theorem setWidth32_setWidth64 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v := by
  simp


theorem stringCloneHook0_ok : HookOk stringCloneHook0 (stringCloneSpec A0) := by
  intro ⟨p, ret, g⟩ R s0 hrun hpre hsp
  have hpre' := hpre
  simp only [stringCloneSpec, vecGhostAt, vecU8At, A0,
    CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx8⟩, hmem⟩
  rw [sepConj_pure_left_comm, satisfies_pure_sepConj] at hmem
  rcases hmem with ⟨⟨hlen_le, hcap_lt, hptr_ne⟩, hmem⟩
  unfold vecHeader at hmem
  have hmem_ptr : s0.mem ⊨ ((p + 8#64) ↦₆₄ g.ptr) ∗
      ((p ↦₆₄ g.cap) ∗ (((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
        ((if g.cap = 0 then emp else (g.ptr ↦ₛ g.bytes) ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗
          (memRegion ret 24 ∗ (stackAt s0.sp extHookStack ∗ R))))) := by
    ac_nf at hmem ⊢
  have hread_ptr := (IsBlock.pointsTo64 (p + 8#64) g.ptr).read hmem_ptr
  have hmem_len : s0.mem ⊨ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      ((p ↦₆₄ g.cap) ∗ (((p + 8#64) ↦₆₄ g.ptr) ∗
        ((if g.cap = 0 then emp else (g.ptr ↦ₛ g.bytes) ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗
          (memRegion ret 24 ∗ (stackAt s0.sp extHookStack ∗ R))))) := by
    ac_nf at hmem ⊢
  have hread_len :=
    (IsBlock.pointsTo64 (p + 16#64) (BitVec.ofNat 64 g.bytes.length)).read hmem_len
  have hlen_lt : g.bytes.length < 2 ^ 63 := by omega
  have hlen_nat : (BitVec.ofNat 64 g.bytes.length).toNat = g.bytes.length :=
    Nat.mod_eq_of_lt (by omega)
  have hsrc_eq : cloneSrc s0 = g.bytes := by
    unfold cloneSrc
    dsimp only
    rw [hx0, hread_ptr, hread_len, hlen_nat]
    by_cases hcap0 : g.cap = 0
    · have hcap0_nat : g.cap.toNat = 0 := by rw [hcap0]; rfl
      have hlen0 : g.bytes.length = 0 := by omega
      rw [List.eq_nil_of_length_eq_zero hlen0]
      rfl
    · simp only [hcap0, ↓reduceIte] at hmem
      have hmem_bs : s0.mem ⊨ (g.ptr ↦ₛ g.bytes) ∗
          ((p ↦₆₄ g.cap) ∗ (((p + 8#64) ↦₆₄ g.ptr) ∗
            (((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
              (memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) ∗
                (memRegion ret 24 ∗ (stackAt s0.sp extHookStack ∗ R)))))) := by
        ac_nf at hmem ⊢
      exact ((IsBlock.pointsToBytes g.ptr g.bytes).read hmem_bs).2
  unfold stringCloneHook0
  rw [hsrc_eq]
  unfold returnFreshVecU8 bumpThen
  split
  · rename_i q hq
    have hmem_ret : s0.mem ⊨ memRegion ret 24 ∗
        (vecGhostAt A0 g p ∗ (stackAt s0.sp extHookStack ∗ R)) := by
      simp only [stringCloneSpec, A0,
        CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
        emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨_, hpre_mem⟩
      ac_nf at hpre_mem ⊢
    have hx8' : (s0.setMem (s0.mem.mapFresh q g.bytes.length Perm.rw)).readReg64 .x8 = ret := hx8
    dsimp only [retHook]
    rw [hx8']
    dsimp only [State.setMem]
    obtain ⟨hkf, hvec⟩ := vecOutThen_some hlen_lt hq hmem_ret
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    dsimp only [stringCloneSpec]
    simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
      emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨rfl, ?_⟩
    change writeVecHeader ((s0.mem.mapFresh q g.bytes.length Perm.rw).writeBytes q g.bytes)
      ret (BitVec.ofNat 64 g.bytes.length) q (BitVec.ofNat 64 g.bytes.length) ⊨
      vecGhostAt A0 g p ∗ (vecU8 A0 ret g.bytes ∗ (stackAt s0.sp extHookStack ∗ R))
    ac_nf at hvec ⊢
  · exact allocPanicHook_ok (fun _ _ _ => rfl) (p, ret, g) R s0 hrun hpre hsp


theorem timeAddHook_ok : HookOk timeAddHook timeAddSpec := by
  intro ⟨⟨tvSec, tvNsec⟩, secs⟩ R s0 hrun hpre _hsp
  simp only [timeAddSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hnsec, hx2, hx3⟩, hmem⟩
  unfold timeAddHook
  dsimp only
  rw [hx0, hx1, hx2, hx3]
  have hnsec_add : (0#32 : BitVec 32) + tvNsec = tvNsec := BitVec.zero_add tvNsec
  have hdec : decide (1000000000 ≤ tvNsec.toNat) = false :=
    decide_eq_false (by omega)
  simp only [hnsec_add, hdec, Bool.false_eq_true, ↓reduceIte]
  by_cases hle : tvSec.toInt + ↑secs ≤ 2 ^ 63 - 1
  · simp only [hle, ↓reduceIte]
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    dsimp only [timeAddSpec]
    have hadd : (SystemTime.mk tvSec tvNsec).checkedAddSecs secs =
        some ⟨BitVec.ofInt 64 (tvSec.toInt + ↑secs), tvNsec⟩ := by
      unfold SystemTime.checkedAddSecs; dsimp only; simp only [hle, ↓reduceIte]
    rw [hadd, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨?_, rfl⟩, hmem⟩
    congr 1
    change SystemTime.mk (BitVec.ofInt 64 (tvSec.toInt + ↑secs)) tvNsec =
      SystemTime.mk (BitVec.ofInt 64 (tvSec.toInt + ↑secs)) ((tvNsec.setWidth 64).setWidth 32)
    rw [setWidth32_setWidth64]
  · simp only [hle, ↓reduceIte]
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
    dsimp only [timeAddSpec]
    have hadd : (SystemTime.mk tvSec tvNsec).checkedAddSecs secs = none := by
      unfold SystemTime.checkedAddSecs; dsimp only; simp only [hle, ↓reduceIte]
    rw [hadd, sepConj_assoc, satisfies_pure_sepConj]
    have hany : s0.mem ⊨ anyHeap ∗ R := by
      let dspec : Spec Unit :=
        { pre := fun _ _ => stackAt s0.sp extHookStack
          post := fun _ _ _ => ⌜False⌝
          onPanic := fun _ _ _ => ⌜True⌝ ∗ anyHeap }
      obtain ⟨-, -, ⟨⟨-, -, hc⟩, -⟩ | ⟨-, honp⟩ | ⟨_, hc, -⟩ | ⟨hc, -⟩⟩ :=
        allocPanicHook_ok_of (spec := dspec) (φ := fun _ _ _ => True)
          (fun _ _ _ => rfl) (fun _ _ _ _ => trivial) () R s0 hrun hmem _hsp
      · cases hc
      · change s0.mem ⊨ (⌜True⌝ ∗ anyHeap) ∗ R at honp
        rw [sepConj_assoc, satisfies_pure_sepConj] at honp
        exact honp.2
      · cases hc
      · cases hc
    exact ⟨⟨rfl, List.prefix_refl s0.trace⟩, hany⟩


end CryptoVerification.E2E.HooksE

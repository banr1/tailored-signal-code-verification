/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
import ProofLib.SepLogic.WP.Structural
public import LibsignalBinary.Proofs.E2E.HooksE.Common
import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth

/-!
# E2E SPQR V1 Hook Satisfaction

Proves `HookOk` for the eight SPQR V1 concrete hooks in `PqxdhHooks.lean` and assembles
`spqrHooks_of_env_pqxdh : SpqrHooks C (HooksE.allocModelE env) Q.K (absP C Q env)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.NonVacuityWitness
  (A₀ satisfies_mapFresh_unmapped readReg64_setPC_writeReg64_x0)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E CryptoVerification.E2E.HooksE
open CryptoVerification.E2E.HooksE.HooksOkAux

/-! ## Memory Read Helper for `readVecN` -/

theorem readVecN_eq_of_pointsToBytes {m : Memory} {a : BitVec 64} {n : Nat}
    {v : List.Vector (BitVec 8) n} {R : SepProp}
    (h : m ⊨ (a ↦ₛ v.toList) ∗ R) :
    readVecN m a n = v := by
  obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes a v.toList).read h
  rw [v.toList_length] at hread
  exact Subtype.ext hread

/-! ## ML-KEM-768 Incremental Hook Witnesses -/

theorem mlkemFromSeedHook_ok (K : MlKem) :
    HookOk (mlkemFromSeedHook K) (mlkemFromSeedSpec K) := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [mlkemFromSeedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hmem⟩
  have hseed : readVecN s0.mem x.seedA 64 = x.seed :=
    readVecN_eq_of_pointsToBytes hmem
  let dk := (K.fromSeed x.seed).2.2.toList
  have hdk_len : dk.length = 2400 := List.Vector.toList_length _
  have hmem_kp : s0.mem ⊨ memRegion x.kpA dk.length ∗
      ((x.seedA ↦ₛ x.seed.toList) ∗ (stackAt s0.sp extHookStack ∗ R)) := by
    rw [hdk_len]
    ac_nf at hmem ⊢
  have hkf := keepsFrozen_writeBytes_of_memRegion dk (by omega) hmem_kp
  have hw := satisfies_writeBytes dk (by omega) hmem_kp
  dsimp only [mlkemFromSeedHook, retHook]
  rw [hx0, hx8, hseed]
  refine ⟨hkf, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [mlkemFromSeedSpec, State.setMem]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨rfl, ?_⟩
  change s0.mem.writeBytes x.kpA dk ⊨
    (x.seedA ↦ₛ x.seed.toList) ∗ ((x.kpA ↦ₛ dk) ∗ (stackAt s0.sp extHookStack ∗ R))
  ac_nf at hw ⊢

theorem mlkemPk1Hook_ok : HookOk mlkemPk1Hook mlkemPk1Spec := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [mlkemPk1Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hmem⟩
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [mlkemPk1Spec, mlkemPk1Hook, retHook]
  rw [hx0, readReg64_setPC_writeReg64_x0]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, rfl⟩, hmem⟩

theorem mlkemPk2Hook_ok : HookOk mlkemPk2Hook mlkemPk2Spec := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [mlkemPk2Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hmem⟩
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [mlkemPk2Spec, mlkemPk2Hook, retHook]
  rw [hx0, readReg64_setPC_writeReg64_x0]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, rfl⟩, hmem⟩

theorem mlkemEncaps1Hook_ok (K : MlKem) :
    HookOk (mlkemEncaps1Hook K) (mlkemEncaps1Spec K) := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [mlkemEncaps1Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hmem⟩
  obtain ⟨_, hread_hdr⟩ := (IsBlock.pointsToBytes x.hdrA x.hdr).read hmem
  have hmem_rand : s0.mem ⊨ (x.randA ↦ₛ x.rand.toList) ∗
      ((x.hdrA ↦ₛ x.hdr) ∗ (memRegion x.ret 961 ∗
        (memRegion x.esA 2080 ∗ (memRegion x.ssA 32 ∗ (stackAt s0.sp extHookStack ∗ R))))) := by
    ac_nf at hmem ⊢
  have hrand : readVecN s0.mem x.randA 32 = x.rand :=
    readVecN_eq_of_pointsToBytes hmem_rand
  have hlen_ok : (decide ((s0.readReg64 .x4).toNat < 2080) ||
      decide ((s0.readReg64 .x6).toNat < 32)) = false := by
    rw [hx4, hx6]; decide
  dsimp only [mlkemEncaps1Hook, retHook]
  simp only [hlen_ok, Bool.false_eq_true, ↓reduceIte]
  rw [hx8, hx0, hx1, hread_hdr, hx2, hrand, hx3, hx5]
  rcases henc : K.encaps1 x.hdr x.rand with _ | ⟨ct1, es, ss⟩
  · dsimp only
    have hsplit : memRegion x.ret 961 =
        memRegion x.ret 1 ∗
          ((∃∗ err : BitVec 8, (x.ret + 1#64) ↦₈ err) ∗ memRegion (x.ret + 2#64) 959) := by
      rw [memRegion_split' (n := 1) (k := 960) rfl rfl (by decide),
        memRegion_split' (b := x.ret + 1#64) (n := 1) (k := 959) (b' := x.ret + 2#64)
          rfl (by bv_omega) (by decide),
        memRegion_one (x.ret + 1#64)]
    have hmem_ret : s0.mem ⊨ memRegion x.ret ([1#8] : List (BitVec 8)).length ∗
        (((∃∗ err : BitVec 8, (x.ret + 1#64) ↦₈ err) ∗ memRegion (x.ret + 2#64) 959) ∗
          ((x.hdrA ↦ₛ x.hdr) ∗ ((x.randA ↦ₛ x.rand.toList) ∗
            (memRegion x.esA 2080 ∗
              (memRegion x.ssA 32 ∗ (stackAt s0.sp extHookStack ∗ R)))))) := by
      change s0.mem ⊨ memRegion x.ret 1 ∗ _
      rw [hsplit] at hmem
      ac_nf at hmem ⊢
    have hkf := keepsFrozen_writeBytes_of_memRegion [1#8] (by decide) hmem_ret
    have hw := satisfies_writeBytes [1#8] (by decide) hmem_ret
    rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp] at hw
    refine ⟨hkf, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [mlkemEncaps1Spec, State.setMem]
    rw [henc]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨rfl, ?_⟩
    ac_nf at hw ⊢
  · dsimp only
    let retBs : List (BitVec 8) := 0#8 :: ct1.toList
    have hret_len : retBs.length = 961 := by
      simp [retBs, List.Vector.toList_length]
    have hes_len : es.toList.length = 2080 := List.Vector.toList_length _
    have hss_len : ss.toList.length = 32 := List.Vector.toList_length _
    have hmem1 : s0.mem ⊨ memRegion x.ret retBs.length ∗
        (memRegion x.esA 2080 ∗ (memRegion x.ssA 32 ∗
          ((x.hdrA ↦ₛ x.hdr) ∗ ((x.randA ↦ₛ x.rand.toList) ∗
            (stackAt s0.sp extHookStack ∗ R))))) := by
      rw [hret_len]; ac_nf at hmem ⊢
    have hkf1 := keepsFrozen_writeBytes_of_memRegion retBs (by omega) hmem1
    have hw1 := satisfies_writeBytes retBs (by omega) hmem1
    have hmem2 : s0.mem.writeBytes x.ret retBs ⊨ memRegion x.esA es.toList.length ∗
        ((x.ret ↦ₛ retBs) ∗ (memRegion x.ssA 32 ∗
          ((x.hdrA ↦ₛ x.hdr) ∗ ((x.randA ↦ₛ x.rand.toList) ∗
            (stackAt s0.sp extHookStack ∗ R))))) := by
      rw [hes_len]; ac_nf at hw1 ⊢
    have hkf2 := keepsFrozen_writeBytes_of_memRegion es.toList (by omega) hmem2
    have hw2 := satisfies_writeBytes es.toList (by omega) hmem2
    have hmem3 : (s0.mem.writeBytes x.ret retBs).writeBytes x.esA es.toList ⊨
        memRegion x.ssA ss.toList.length ∗
          ((x.ret ↦ₛ retBs) ∗ ((x.esA ↦ₛ es.toList) ∗
            ((x.hdrA ↦ₛ x.hdr) ∗ ((x.randA ↦ₛ x.rand.toList) ∗
              (stackAt s0.sp extHookStack ∗ R))))) := by
      rw [hss_len]; ac_nf at hw2 ⊢
    have hkf3 := keepsFrozen_writeBytes_of_memRegion ss.toList (by omega) hmem3
    have hw3 := satisfies_writeBytes ss.toList (by omega) hmem3
    have hret_cons : (x.ret ↦ₛ retBs) = (x.ret ↦₈ 0#8) ∗ ((x.ret + 1#64) ↦ₛ ct1.toList) := by
      dsimp only [retBs]
      rw [pointsToBytes_cons]
    rw [hret_cons] at hw3
    refine ⟨hkf1.trans (hkf2.trans hkf3), rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [mlkemEncaps1Spec, State.setMem]
    rw [henc]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨rfl, ?_⟩
    ac_nf at hw3 ⊢

theorem mlkemEncaps2Hook_ok (K : MlKem) :
    HookOk (mlkemEncaps2Hook K) (mlkemEncaps2Spec K) := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [mlkemEncaps2Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1⟩, hmem⟩
  have hes : readVecN s0.mem x.esA 2080 = x.es :=
    readVecN_eq_of_pointsToBytes hmem
  have hmem_ek : s0.mem ⊨ (x.ekA ↦ₛ x.ek.toList) ∗
      ((x.esA ↦ₛ x.es.toList) ∗ (memRegion x.ret 128 ∗ (stackAt s0.sp extHookStack ∗ R))) := by
    ac_nf at hmem ⊢
  have hek : readVecN s0.mem x.ekA 1152 = x.ek :=
    readVecN_eq_of_pointsToBytes hmem_ek
  let ct2 := (K.encaps2 x.es x.ek).toList
  have hct2_len : ct2.length = 128 := List.Vector.toList_length _
  have hmem_ret : s0.mem ⊨ memRegion x.ret ct2.length ∗
      ((x.esA ↦ₛ x.es.toList) ∗ ((x.ekA ↦ₛ x.ek.toList) ∗ (stackAt s0.sp extHookStack ∗ R))) := by
    rw [hct2_len]; ac_nf at hmem ⊢
  have hkf := keepsFrozen_writeBytes_of_memRegion ct2 (by omega) hmem_ret
  have hw := satisfies_writeBytes ct2 (by omega) hmem_ret
  dsimp only [mlkemEncaps2Hook, retHook]
  rw [hx8, hx0, hx1, hes, hek]
  refine ⟨hkf, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [mlkemEncaps2Spec, State.setMem]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨rfl, ?_⟩
  change s0.mem.writeBytes x.ret ct2 ⊨
    (x.esA ↦ₛ x.es.toList) ∗
      ((x.ekA ↦ₛ x.ek.toList) ∗ ((x.ret ↦ₛ ct2) ∗ (stackAt s0.sp extHookStack ∗ R)))
  ac_nf at hw ⊢

theorem mlkemDecapsHook_ok (K : MlKem) :
    HookOk (mlkemDecapsHook K) (mlkemDecapsSpec K) := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [mlkemDecapsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2⟩, hmem⟩
  have hdk : readVecN s0.mem x.dkA 2400 = x.dk :=
    readVecN_eq_of_pointsToBytes hmem
  have hmem_ct1 : s0.mem ⊨ (x.ct1A ↦ₛ x.ct1.toList) ∗
      ((x.dkA ↦ₛ x.dk.toList) ∗ ((x.ct2A ↦ₛ x.ct2.toList) ∗
        (memRegion x.ret 32 ∗ (stackAt s0.sp extHookStack ∗ R)))) := by
    ac_nf at hmem ⊢
  have hct1 : readVecN s0.mem x.ct1A 960 = x.ct1 :=
    readVecN_eq_of_pointsToBytes hmem_ct1
  have hmem_ct2 : s0.mem ⊨ (x.ct2A ↦ₛ x.ct2.toList) ∗
      ((x.dkA ↦ₛ x.dk.toList) ∗ ((x.ct1A ↦ₛ x.ct1.toList) ∗
        (memRegion x.ret 32 ∗ (stackAt s0.sp extHookStack ∗ R)))) := by
    ac_nf at hmem ⊢
  have hct2 : readVecN s0.mem x.ct2A 128 = x.ct2 :=
    readVecN_eq_of_pointsToBytes hmem_ct2
  let ss := (K.decaps x.dk x.ct1 x.ct2).toList
  have hss_len : ss.length = 32 := List.Vector.toList_length _
  have hmem_ret : s0.mem ⊨ memRegion x.ret ss.length ∗
      ((x.dkA ↦ₛ x.dk.toList) ∗ ((x.ct1A ↦ₛ x.ct1.toList) ∗
        ((x.ct2A ↦ₛ x.ct2.toList) ∗ (stackAt s0.sp extHookStack ∗ R)))) := by
    rw [hss_len]; ac_nf at hmem ⊢
  have hkf := keepsFrozen_writeBytes_of_memRegion ss (by omega) hmem_ret
  have hw := satisfies_writeBytes ss (by omega) hmem_ret
  dsimp only [mlkemDecapsHook, retHook]
  rw [hx8, hx0, hx1, hx2, hdk, hct1, hct2]
  refine ⟨hkf, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [mlkemDecapsSpec, State.setMem]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨rfl, ?_⟩
  change s0.mem.writeBytes x.ret ss ⊨
    (x.dkA ↦ₛ x.dk.toList) ∗ ((x.ct1A ↦ₛ x.ct1.toList) ∗
      ((x.ct2A ↦ₛ x.ct2.toList) ∗ ((x.ret ↦ₛ ss) ∗ (stackAt s0.sp extHookStack ∗ R))))
  ac_nf at hw ⊢

theorem mlkemValidatePkHook_ok (K : MlKem) :
    HookOk (mlkemValidatePkHook K) (mlkemValidatePkSpec K) := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [mlkemValidatePkSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3⟩, hmem⟩
  obtain ⟨_, hread_hdr⟩ := (IsBlock.pointsToBytes x.hdrA x.hdr).read hmem
  have hmem_ek : s0.mem ⊨ (x.ekA ↦ₛ x.ek) ∗
      ((x.hdrA ↦ₛ x.hdr) ∗ (stackAt s0.sp extHookStack ∗ R)) := by
    ac_nf at hmem ⊢
  obtain ⟨_, hread_ek⟩ := (IsBlock.pointsToBytes x.ekA x.ek).read hmem_ek
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [mlkemValidatePkSpec, mlkemValidatePkHook, retHook]
  rw [hx0, hx1, hread_hdr, hx2, hx3, hread_ek, readReg64_setPC_writeReg64_x0]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨?_, rfl⟩, hmem⟩
  cases K.validPkBytes x.hdr x.ek <;> decide

/-! ## `libcrux_hmac::hmac` Witness -/

theorem libcruxHmacHook_ok (F : ShaState → List (BitVec 8) → ShaState) :
    HookOk (libcruxHmacHook F) (libcruxHmacSpec F A0) := by
  intro x R s0 hrun hpre hsp
  have hpre' := hpre
  simp only [libcruxHmacSpec, A0,
    CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
    emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hmem⟩
  have halg : ((s0.readReg64 .x0).setWidth 32 != 0#32) = false := by
    rw [hx0]; decide
  unfold libcruxHmacHook
  dsimp only
  simp only [halg, Bool.false_eq_true, ↓reduceIte]
  rw [hx2, hx4]
  by_cases hlen : x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32
  · simp only [hlen]
    obtain ⟨_, hread_key⟩ := (IsBlock.pointsToBytes x.keyA x.key).read hmem
    have hmem_data : s0.mem ⊨ (x.dataA ↦ₛ x.data) ∗
        ((x.keyA ↦ₛ x.key) ∗ (memRegion x.ret 24 ∗ (stackAt s0.sp extHookStack ∗ R))) := by
      ac_nf at hmem ⊢
    obtain ⟨_, hread_data⟩ := (IsBlock.pointsToBytes x.dataA x.data).read hmem_data
    rw [hx1, hread_key, hx3, hread_data]
    let tag := hmacWith F x.key x.data
    have htag_len : tag.length = 32 :=
      CryptoVerification.LibsignalSpqrV1.length_hmacWith F x.key x.data
    have htag_lt : tag.length < 2 ^ 63 := by omega
    have hout_eq :
        (if ((s0.readReg64 .x5).setWidth 32 &&& 1#32) != 0#32 then
          min (s0.readReg64 .x6).toNat tag.length
        else tag.length) = tag.length := by
      rw [hx5, hx6, htag_len]; decide
    rw [hout_eq]
    unfold bumpThen
    rcases hp : bumpAddr? s0.mem tag.length 1 with _ | p
    · exact allocPanicHook_ok_of (fun _ _ _ => rfl) (fun _ _ ha ht => ⟨Or.inl ha, ht⟩)
        x R s0 hrun hpre hsp
    · have hmem_ret : s0.mem ⊨ memRegion x.ret 24 ∗
          ((x.keyA ↦ₛ x.key) ∗ ((x.dataA ↦ₛ x.data) ∗ (stackAt s0.sp extHookStack ∗ R))) := by
        ac_nf at hmem ⊢
      have hx8' : (s0.setMem (s0.mem.mapFresh p tag.length Perm.rw)).readReg64 .x8 = x.ret := hx8
      dsimp only [retHook]
      rw [hx8']
      dsimp only [State.setMem]
      obtain ⟨hkf, hvec⟩ := vecOutThen_some htag_lt hp hmem_ret
      refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
      dsimp only [libcruxHmacSpec]
      simp only [A0, CryptoVerification.LibsignalSession.NonVacuityWitness.A₀,
        emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hlen.1, hlen.2, rfl⟩, ?_⟩
      change writeVecHeader ((s0.mem.mapFresh p tag.length Perm.rw).writeBytes p tag)
        x.ret (BitVec.ofNat 64 tag.length) p (BitVec.ofNat 64 tag.length) ⊨
        (x.keyA ↦ₛ x.key) ∗ ((x.dataA ↦ₛ x.data) ∗
          (vecU8 A0 x.ret tag ∗ (stackAt s0.sp extHookStack ∗ R)))
      ac_nf at hvec ⊢
  · simp only [hlen, ↓reduceIte]
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
    dsimp only [libcruxHmacSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have hge : 2 ^ 32 ≤ x.key.length ∨ 2 ^ 32 ≤ x.data.length := by omega
    exact ⟨⟨Or.inr hge, List.prefix_refl s0.trace⟩,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpre⟩

end CryptoVerification.E2E.Pqxdh

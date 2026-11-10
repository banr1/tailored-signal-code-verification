/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
public import Computational.Proofs.SignalPqxdh.Security.CollisionsC
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh

open _root_.SignalPqxdh.Security.FgGapDh

theorem evalDist_preSample_U_dh3_pqxdhKeyIndFgPreImpl {S : Setup} {α : Type}
    (targetIdx targetSpkIdx : ℕ) (optVsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl false targetIdx targetSpkIdx (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl false targetIdx targetSpkIdx none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq_c0
    sampleScalar32
    sampleCoins32
    (hasFiredSess S targetIdx)
    (pqxdhKeyIndFgPreImpl false targetIdx targetSpkIdx none optVsk S P)
    (fun uSk => pqxdhKeyIndFgPreImpl false targetIdx targetSpkIdx (some uSk) optVsk S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhKeyIndFgPreImpl_preserves_hasFired false targetIdx targetSpkIdx none optVsk P q s x
        hx).2.2
        targetIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro uSk
    cases q with
    | initiateOPK u i bundle =>
      unfold pqxdhKeyIndFgPreImpl fgPreInitiate liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      cases bundle.opkB?.isNone
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          Bool.not_false, Bool.true_and]
        by_cases hSlot : (initSessionSlotIdx (.sendOPK u i) == targetIdx) = true
        · have hany := sessions_any_of_hasFiredSess targetIdx s hFired (.sendOPK u i) hSlot
            (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _))
          simp [hany]
        · simp only [hSlot, Bool.false_eq_true, ↓reduceIte]
      · rfl
    | initiateNoOPK u i bundle =>
      unfold pqxdhKeyIndFgPreImpl fgPreInitiate liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      cases bundle.opkB?.isSome
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          Bool.not_false, Bool.true_and]
        by_cases hSlot : (initSessionSlotIdx (.sendNoOPK u i) == targetIdx) = true
        · have hany := sessions_any_of_hasFiredSess targetIdx s hFired (.sendNoOPK u i) hSlot
            (initSessionSlotIdx_sendNoOPK_lt u i)
          simp [hany]
        · simp only [hSlot, Bool.false_eq_true, ↓reduceIte]
      · rfl
    | _ => rfl
  · cases q with
    | initiateOPK u i bundle =>
      unfold pqxdhKeyIndFgPreImpl
      by_cases hOpt : bundle.opkB?.isNone = true
      · refine Or.inl (fun uSk => ?_)
        unfold liftFgBase
        simp [hOpt]
      · have hEqPre : ∀ optU, (liftFgBase (do
            let _ ← get
            if bundle.opkB?.isNone then return .noneResp
            fgPreInitiate false targetIdx optU S P (.sendOPK u i) u bundle)).run s =
          (liftFgBase (fgPreInitiate false targetIdx optU S P (.sendOPK u i) u bundle)).run s := by
          intro optU; unfold liftFgBase
          simp [hOpt]
        simp_rw [hEqPre]
        exact fgPreInitiate_before_c0 targetIdx P (.sendOPK u i) u bundle s
    | initiateNoOPK u i bundle =>
      unfold pqxdhKeyIndFgPreImpl
      by_cases hOpt : bundle.opkB?.isSome = true
      · refine Or.inl (fun uSk => ?_)
        unfold liftFgBase
        simp [hOpt]
      · have hEqPre : ∀ optU, (liftFgBase (do
            let _ ← get
            if bundle.opkB?.isSome then return .noneResp
            fgPreInitiate false targetIdx optU S P (.sendNoOPK u i) u bundle)).run s =
          (liftFgBase (fgPreInitiate false targetIdx optU S P (.sendNoOPK u i) u bundle)).run s :=
            by
          intro optU; unfold liftFgBase
          simp [hOpt]
        simp_rw [hEqPre]
        exact fgPreInitiate_before_c0 targetIdx P (.sendNoOPK u i) u bundle s
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_runKeyIndFgSim_eq_preSample_dh3 {S : Setup}
    (sIdx bIdx : ℕ) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := KeyIndFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runKeyIndFgSim S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hV : ∀ uSk,
      𝒟[sampleScalar32 >>= fun vSk =>
        (simulateQ (fullPre uSk vSk) A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) none S P) A.run).run
          (KeyIndFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] :=
    fun uSk => evalDist_preSample_V_pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_U_dh3_pqxdhKeyIndFgPreImpl sIdx bIdx none P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhKeyIndFgPreImpl_none_none_eq]
  simp only [pure_bind]

theorem evalDist_runKeyIndFgSim_eq_preSample_dh1 {S : Setup}
    (uIdx bIdx : ℕ) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := KeyIndFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runKeyIndFgSim S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hV : ∀ uSk,
      𝒟[sampleScalar32 >>= fun vSk =>
        (simulateQ (fullPre uSk vSk) A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) none S P) A.run).run
          (KeyIndFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] :=
    fun uSk => evalDist_preSample_V_pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_U_dh1_pqxdhKeyIndFgPreImpl uIdx bIdx none P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhKeyIndFgPreImpl_none_none_eq]
  simp only [pure_bind]

@[simp] theorem length_F_X25519_fg : F_X25519.length = 32 := by
  simp [F_X25519]

theorem drop_take_slice_fg {pfx mid sfx : Bytes} {n m : ℕ}
    (hp : pfx.length = n) (hm : mid.length = m) :
    List.take m (List.drop n (pfx ++ mid ++ sfx)) = mid := by
  rw [List.append_assoc, ← hp, List.drop_left, ← hm, List.take_left]

theorem parseRoSecrets_buildSecrets
    {dh1 dh2 dh3 : Bytes} {dh4? : Option Bytes} {ss : Bytes}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) (h3 : dh3.length = 32)
    (h4 : ∀ d, dh4? = some d → d.length = 32) (hss : ss.length = 32) :
    parseRoSecrets (buildSecrets dh1 dh2 dh3 dh4? ss) =
      some (dh1, dh2, dh3, dh4?, ss) := by
  cases dh4? with
  | none =>
    unfold parseRoSecrets
    have htake : (buildSecrets dh1 dh2 dh3 none ss).take 32 = F_X25519 := by
      simp only [buildSecrets]
      have ha : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ ss = F_X25519 ++ (dh1 ++ dh2 ++ dh3 ++ ss) := by
        simp [List.append_assoc]
      rw [ha, ← length_F_X25519_fg, List.take_left]
    have hlen : (buildSecrets dh1 dh2 dh3 none ss).length = 160 := by
      simp [buildSecrets, h1, h2, h3, hss]
    have he1 : extractDh1 (buildSecrets dh1 dh2 dh3 none ss) = dh1 := by
      simp only [extractDh1, buildSecrets]
      have ha : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ ss = F_X25519 ++ dh1 ++ (dh2 ++ dh3 ++ ss) := by
        simp [List.append_assoc]
      rw [ha]
      exact drop_take_slice_fg length_F_X25519_fg h1
    have he2 : extractDh2 (buildSecrets dh1 dh2 dh3 none ss) = dh2 := by
      simp only [extractDh2, buildSecrets]
      have ha : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ ss = (F_X25519 ++ dh1) ++ dh2 ++ (dh3 ++ ss) := by
        simp [List.append_assoc]
      rw [ha]
      exact drop_take_slice_fg (by simp [h1]) h2
    have he3 : extractDh3 (buildSecrets dh1 dh2 dh3 none ss) = dh3 := by
      simp only [extractDh3, buildSecrets]
      exact drop_take_slice_fg (by simp [h1, h2]) h3
    have hess : extractKemSsNoOPK (buildSecrets dh1 dh2 dh3 none ss) = ss := by
      simp only [extractKemSsNoOPK, buildSecrets]
      have ha : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ ss = (F_X25519 ++ dh1 ++ dh2 ++ dh3) ++ ss ++ [] :=
        by
        simp
      rw [ha]
      exact drop_take_slice_fg (by simp [h1, h2, h3]) hss
    rw [htake, hlen, he1, he2, he3, hess]
    rfl
  | some dh4 =>
    have h4' : dh4.length = 32 := h4 dh4 rfl
    unfold parseRoSecrets
    have htake : (buildSecrets dh1 dh2 dh3 (some dh4) ss).take 32 = F_X25519 := by
      simp only [buildSecrets]
      have ha : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss =
          F_X25519 ++ (dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss) := by
        simp [List.append_assoc]
      rw [ha, ← length_F_X25519_fg, List.take_left]
    have hlen : (buildSecrets dh1 dh2 dh3 (some dh4) ss).length = 192 := by
      simp [buildSecrets, h1, h2, h3, h4', hss]
    have he1 : extractDh1 (buildSecrets dh1 dh2 dh3 (some dh4) ss) = dh1 := by
      simp only [extractDh1, buildSecrets]
      have ha : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss =
          F_X25519 ++ dh1 ++ (dh2 ++ dh3 ++ dh4 ++ ss) := by
        simp [List.append_assoc]
      rw [ha]
      exact drop_take_slice_fg length_F_X25519_fg h1
    have he2 : extractDh2 (buildSecrets dh1 dh2 dh3 (some dh4) ss) = dh2 := by
      simp only [extractDh2, buildSecrets]
      have ha : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss =
          (F_X25519 ++ dh1) ++ dh2 ++ (dh3 ++ dh4 ++ ss) := by
        simp [List.append_assoc]
      rw [ha]
      exact drop_take_slice_fg (by simp [h1]) h2
    have he3 : extractDh3 (buildSecrets dh1 dh2 dh3 (some dh4) ss) = dh3 := by
      simp only [extractDh3, buildSecrets]
      have ha : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss =
          (F_X25519 ++ dh1 ++ dh2) ++ dh3 ++ (dh4 ++ ss) := by
        simp [List.append_assoc]
      rw [ha]
      exact drop_take_slice_fg (by simp [h1, h2]) h3
    have he4 : extractDh4 (buildSecrets dh1 dh2 dh3 (some dh4) ss) = dh4 := by
      simp only [extractDh4, buildSecrets]
      exact drop_take_slice_fg (by simp [h1, h2, h3]) h4'
    have hess : extractKemSsOPK (buildSecrets dh1 dh2 dh3 (some dh4) ss) = ss := by
      simp only [extractKemSsOPK, buildSecrets]
      have ha : F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4 ++ ss =
          (F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4) ++ ss ++ [] := by
        simp
      rw [ha]
      exact drop_take_slice_fg (by simp [h1, h2, h3, h4']) hss
    rw [htake, hlen, he1, he2, he3, he4, hess]
    rfl

theorem buildSecrets_of_parseRoSecrets {bs dh1 dh2 dh3 : Bytes}
    {dh4? : Option Bytes} {ss : Bytes}
    (h : parseRoSecrets bs = some (dh1, dh2, dh3, dh4?, ss)) :
    bs = buildSecrets dh1 dh2 dh3 dh4? ss ∧
    dh1.length = 32 ∧ dh2.length = 32 ∧ dh3.length = 32 ∧
    (∀ d, dh4? = some d → d.length = 32) ∧ ss.length = 32 := by
  unfold parseRoSecrets at h
  by_cases hfx : (bs.take 32 != F_X25519) = true
  · simp [hfx] at h
  · simp only [hfx, Bool.false_eq_true, ↓reduceIte] at h
    have hfx_eq : bs.take 32 = F_X25519 := by
      simpa using hfx
    by_cases h160 : (bs.length == 160) = true
    · simp only [h160, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
      have hlen : bs.length = 160 := beq_iff_eq.mp h160
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · change bs = F_X25519 ++ (bs.drop 32).take 32 ++ (bs.drop 64).take 32 ++
          (bs.drop 96).take 32 ++ (bs.drop 128).take 32
        rw [← hfx_eq]
        have h64 : bs.take 32 ++ (bs.drop 32).take 32 = bs.take 64 :=
          (List.take_add (l := bs) (i := 32) (j := 32)).symm
        have h96 : bs.take 64 ++ (bs.drop 64).take 32 = bs.take 96 :=
          (List.take_add (l := bs) (i := 64) (j := 32)).symm
        have h128 : bs.take 96 ++ (bs.drop 96).take 32 = bs.take 128 :=
          (List.take_add (l := bs) (i := 96) (j := 32)).symm
        have h160' : bs.take 128 ++ (bs.drop 128).take 32 = bs.take 160 :=
          (List.take_add (l := bs) (i := 128) (j := 32)).symm
        rw [h64, h96, h128, h160', List.take_of_length_le (by omega)]
      · simp [extractDh1, hlen]
      · simp [extractDh2, hlen]
      · simp [extractDh3, hlen]
      · intro d hd; cases hd
      · simp [extractKemSsNoOPK, hlen]
    · simp only [h160, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h192 : (bs.length == 192) = true
      · simp only [h192, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
        have hlen : bs.length = 192 := beq_iff_eq.mp h192
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · change bs = F_X25519 ++ (bs.drop 32).take 32 ++ (bs.drop 64).take 32 ++
            (bs.drop 96).take 32 ++ (bs.drop 128).take 32 ++ (bs.drop 160).take 32
          rw [← hfx_eq]
          have h64 : bs.take 32 ++ (bs.drop 32).take 32 = bs.take 64 :=
            (List.take_add (l := bs) (i := 32) (j := 32)).symm
          have h96 : bs.take 64 ++ (bs.drop 64).take 32 = bs.take 96 :=
            (List.take_add (l := bs) (i := 64) (j := 32)).symm
          have h128 : bs.take 96 ++ (bs.drop 96).take 32 = bs.take 128 :=
            (List.take_add (l := bs) (i := 96) (j := 32)).symm
          have h160' : bs.take 128 ++ (bs.drop 128).take 32 = bs.take 160 :=
            (List.take_add (l := bs) (i := 128) (j := 32)).symm
          have h192' : bs.take 160 ++ (bs.drop 160).take 32 = bs.take 192 :=
            (List.take_add (l := bs) (i := 160) (j := 32)).symm
          rw [h64, h96, h128, h160', h192', List.take_of_length_le (by omega)]
        · simp [extractDh1, hlen]
        · simp [extractDh2, hlen]
        · simp [extractDh3, hlen]
        · rintro d ⟨rfl⟩
          simp [extractDh4, hlen]
        · simp [extractKemSsOPK, hlen]
      · simp [h192] at h

theorem buildSecrets_eq_iff_of_len32
    {dh1 dh2 dh3 : Bytes} {dh4? : Option Bytes} {ss : Bytes}
    {dh1' dh2' dh3' : Bytes} {dh4?' : Option Bytes} {ss' : Bytes}
    (h1 : dh1.length = 32) (h2 : dh2.length = 32) (h3 : dh3.length = 32)
    (h4 : ∀ d, dh4? = some d → d.length = 32) (hss : ss.length = 32)
    (h1' : dh1'.length = 32) (h2' : dh2'.length = 32) (h3' : dh3'.length = 32)
    (h4' : ∀ d, dh4?' = some d → d.length = 32) (hss' : ss'.length = 32) :
    buildSecrets dh1 dh2 dh3 dh4? ss = buildSecrets dh1' dh2' dh3' dh4?' ss' ↔
      (ss = ss' ∧ dh1 = dh1' ∧ dh2 = dh2' ∧ dh3 = dh3' ∧ dh4? = dh4?') := by
  constructor
  · intro h
    have hp := congrArg parseRoSecrets h
    rw [parseRoSecrets_buildSecrets h1 h2 h3 h4 hss,
        parseRoSecrets_buildSecrets h1' h2' h3' h4' hss'] at hp
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl

/-! ## `FgPoS` representation relations -/

def FgPosRightRep (P : Primitives) (vSk : Bytes) (pos : FgPoS) (dh : Bytes) : Prop :=
  dh.length = 32 ∧
  (pos = mkSecretPosPure P dh ∨
   ∃ pk1 pk2,
     pos = mkPairPosPure P pk1 pk2 ∧
     dh = P.x25519 vSk pk1 ∧
     onCurveKeyLocal P pk1 ∧
     P.pow8 pk2 = P.pow8 (P.x25519Base vSk) ∧
     ∀ z, P.isValidDhTriple pk1 pk2 z = P.isValidDhTriple pk1 (P.x25519Base vSk) z)

def FgPosLeftRep (P : Primitives) (uSk : Bytes) (pos : FgPoS) (dh : Bytes) : Prop :=
  dh.length = 32 ∧
  (pos = mkSecretPosPure P dh ∨
   ∃ pk1 pk2,
     pos = mkPairPosPure P pk1 pk2 ∧
     dh = P.x25519 uSk pk2 ∧
     onCurveKeyLocal P pk2 ∧
     P.pow8 pk1 = P.pow8 (P.x25519Base uSk) ∧
     ∀ z, P.isValidDhTriple pk1 pk2 z = P.isValidDhTriple (P.x25519Base uSk) pk2 z)

def FgOptLeftRep (P : Primitives) (uSk : Bytes) : Option FgPoS → Option Bytes → Prop
  | none, none => True
  | some pos, some dh => FgPosLeftRep P uSk pos dh
  | _, _ => False

def FgOptRightRep (P : Primitives) (vSk : Bytes) : Option FgPoS → Option Bytes → Prop
  | none, none => True
  | some pos, some dh => FgPosRightRep P vSk pos dh
  | _, _ => False

theorem fgPosRightRep_mkSecret (P : Primitives) (vSk dh : Bytes) (hLen : dh.length = 32) :
    FgPosRightRep P vSk (mkSecretPosPure P dh) dh :=
  ⟨hLen, Or.inl rfl⟩

theorem fgPosRightRep_mkPair_right (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (vSk pk1 : Bytes) (hpk1 : onCurveKeyLocal P pk1) :
    FgPosRightRep P vSk (mkPairPosPure P pk1 (P.x25519Base vSk)) (P.x25519 vSk pk1) :=
  ⟨hWF.x25519_len vSk pk1, Or.inr ⟨pk1, P.x25519Base vSk, rfl, rfl, hpk1, rfl, fun _ => rfl⟩⟩

theorem fgPosRightRep_mkPair_left_of_pow8 (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (uSk vSk pk2 : Bytes) (hu : uSk.length = 32) (hv : vSk.length = 32)
    (hpk2 : pk2.length = 32)
    (hpow : P.pow8 pk2 = P.pow8 (P.x25519Base vSk)) :
    FgPosRightRep P vSk (mkPairPosPure P (P.x25519Base uSk) pk2) (P.x25519 uSk pk2) := by
  have hOnCurveU : onCurveKeyLocal P (P.x25519Base uSk) := Or.inl (hWF.canon_base uSk)
  have hOnCurvePk2 : onCurveKeyLocal P pk2 := Or.inr ⟨vSk, hv, hpow⟩
  have hOnCurveV : onCurveKeyLocal P (P.x25519Base vSk) := Or.inl (hWF.canon_base vSk)
  refine ⟨hWF.x25519_len uSk pk2, Or.inr ⟨P.x25519Base uSk, pk2, rfl, ?_, hOnCurveU, hpow, ?_⟩⟩
  · rw [hWF.x25519_pow8_congr uSk pk2 (P.x25519Base vSk) hpk2 (hWF.x25519Base_len vSk) hpow,
        hWF.x25519_comm]
  · intro z
    apply Bool.eq_iff_iff.mpr
    rw [ddh_consistent_left_of_onCurveKeyLocal P hWF uSk pk2 z hu hOnCurvePk2,
        ddh_consistent_left_of_onCurveKeyLocal P hWF uSk (P.x25519Base vSk) z hu hOnCurveV,
        hWF.x25519_pow8_congr uSk pk2 (P.x25519Base vSk) hpk2 (hWF.x25519Base_len vSk) hpow]

theorem fgPosLeftRep_mkPair_left (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (uSk pk2 : Bytes) (hpk2 : onCurveKeyLocal P pk2) :
    FgPosLeftRep P uSk (mkPairPosPure P (P.x25519Base uSk) pk2) (P.x25519 uSk pk2) :=
  ⟨hWF.x25519_len uSk pk2, Or.inr ⟨P.x25519Base uSk, pk2, rfl, rfl, hpk2, rfl, fun _ => rfl⟩⟩

theorem ddhEqPure_of_fgPosRightRep (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    {vSk : Bytes} (hv : vSk.length = 32) {p1 p2 : FgPoS} {dh1 dh2 : Bytes}
    (hp1 : FgPosRightRep P vSk p1 dh1) (hp2 : FgPosRightRep P vSk p2 dh2) :
    ddhEqPure P.isValidDhTriple p1 p2 = (dh1 == dh2) := by
  rcases hp1 with ⟨_, rfl | ⟨pk1, pk2, rfl, rfl, hpk1, hpow2, hddh1⟩⟩ <;>
    rcases hp2 with ⟨_, rfl | ⟨pk3, pk4, rfl, rfl, hpk3, hpow4, hddh2⟩⟩
  · rfl
  · apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    have hEq : ddhEqPure P.isValidDhTriple (mkSecretPosPure P dh1) (mkPairPosPure P pk3 pk4) =
        ddhEqPure P.isValidDhTriple (.secret dh1 (P.isCanonical dh1))
          (.pair pk3 (P.x25519Base vSk) (P.pow8 pk3) (P.pow8 pk4)) := by
      simp only [ddhEqPure, mkSecretPosPure, mkPairPosPure, hddh2]
    rw [hEq]
    exact ddhEqPure_secret_pair_right_iff P hP.toWellFormedPrimitivesδ pk3 vSk (P.pow8 pk3) (P.pow8
      pk4) dh1 hv (onCurveKeyLocal_length_eq_32 P hP hpk3) hpk3
  · apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    have hEq : ddhEqPure P.isValidDhTriple (mkPairPosPure P pk1 pk2) (mkSecretPosPure P dh2) =
        ddhEqPure P.isValidDhTriple (.pair pk1 (P.x25519Base vSk) (P.pow8 pk1) (P.pow8 pk2))
          (.secret dh2 (P.isCanonical dh2)) := by
      simp only [ddhEqPure, mkSecretPosPure, mkPairPosPure, hddh1]
    rw [hEq]
    exact (ddhEqPure_pair_right_secret_iff P hP.toWellFormedPrimitivesδ pk1 vSk (P.pow8 pk1) (P.pow8
      pk2) dh2 hv (onCurveKeyLocal_length_eq_32 P hP hpk1) hpk1).trans eq_comm
  · exact ddhEqPure_pair_pair_same_right_iff P hP vSk pk1 pk2 pk3 pk4 hv
      (onCurveKeyLocal_length_eq_32 P hP hpk1) (onCurveKeyLocal_length_eq_32 P hP hpk3)
      hpow2 hpow4

theorem ddhEqPure_of_fgPosLeftRep (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    {uSk : Bytes} (hu : uSk.length = 32) {p1 p2 : FgPoS} {dh1 dh2 : Bytes}
    (hp1 : FgPosLeftRep P uSk p1 dh1) (hp2 : FgPosLeftRep P uSk p2 dh2) :
    ddhEqPure P.isValidDhTriple p1 p2 = (dh1 == dh2) := by
  rcases hp1 with ⟨_, rfl | ⟨pk1, pk2, rfl, rfl, hpk2, hpow1, hddh1⟩⟩ <;>
    rcases hp2 with ⟨_, rfl | ⟨pk3, pk4, rfl, rfl, hpk4, hpow3, hddh2⟩⟩
  · rfl
  · apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    have hEq : ddhEqPure P.isValidDhTriple (mkSecretPosPure P dh1) (mkPairPosPure P pk3 pk4) =
        ddhEqPure P.isValidDhTriple (.secret dh1 (P.isCanonical dh1))
          (.pair (P.x25519Base uSk) pk4 (P.pow8 pk3) (P.pow8 pk4)) := by
      simp only [ddhEqPure, mkSecretPosPure, mkPairPosPure, hddh2]
    rw [hEq]
    exact ddhEqPure_secret_pair_left_iff P hP.toWellFormedPrimitivesδ uSk pk4 (P.pow8 pk3) (P.pow8
      pk4) dh1 hu (onCurveKeyLocal_length_eq_32 P hP hpk4) hpk4
  · apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    have hEq : ddhEqPure P.isValidDhTriple (mkPairPosPure P pk1 pk2) (mkSecretPosPure P dh2) =
        ddhEqPure P.isValidDhTriple (.pair (P.x25519Base uSk) pk2 (P.pow8 pk1) (P.pow8 pk2))
          (.secret dh2 (P.isCanonical dh2)) := by
      simp only [ddhEqPure, mkSecretPosPure, mkPairPosPure, hddh1]
    rw [hEq]
    exact (ddhEqPure_pair_left_secret_iff P hP.toWellFormedPrimitivesδ uSk pk2 (P.pow8 pk1) (P.pow8
      pk2) dh2 hu (onCurveKeyLocal_length_eq_32 P hP hpk2) hpk2).trans eq_comm
  · exact ddhEqPure_pair_pair_same_left_iff P hP uSk pk1 pk2 pk3 pk4 hu
      (onCurveKeyLocal_length_eq_32 P hP hpk2) (onCurveKeyLocal_length_eq_32 P hP hpk4)
      hpow1 hpow3

theorem ddhEqOptPure_of_fgOptLeftRep (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    {uSk : Bytes} (hu : uSk.length = 32) {o1 o2 : Option FgPoS} {d1 d2 : Option Bytes}
    (ho1 : FgOptLeftRep P uSk o1 d1) (ho2 : FgOptLeftRep P uSk o2 d2) :
    ddhEqOptPure P.isValidDhTriple o1 o2 = (d1 == d2) := by
  cases o1 <;> cases d1 <;> try contradiction
  · cases o2 <;> cases d2 <;> try contradiction
    · rfl
    · rfl
  · cases o2 <;> cases d2 <;> try contradiction
    · rfl
    · simp only [ddhEqOptPure]
      rw [ddhEqPure_of_fgPosLeftRep P hP hu ho1 ho2]
      rfl

theorem ddhEqOptPure_of_fgOptRightRep (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    {vSk : Bytes} (hv : vSk.length = 32) {o1 o2 : Option FgPoS} {d1 d2 : Option Bytes}
    (ho1 : FgOptRightRep P vSk o1 d1) (ho2 : FgOptRightRep P vSk o2 d2) :
    ddhEqOptPure P.isValidDhTriple o1 o2 = (d1 == d2) := by
  cases o1 <;> cases d1 <;> try contradiction
  · cases o2 <;> cases d2 <;> try contradiction
    · rfl
    · rfl
  · cases o2 <;> cases d2 <;> try contradiction
    · rfl
    · simp only [ddhEqOptPure]
      rw [ddhEqPure_of_fgPosRightRep P hP hv ho1 ho2]
      rfl

structure FgSlotReps (P : Primitives) where
  Rep1 : FgPoS → Bytes → Prop
  Rep2 : FgPoS → Bytes → Prop
  Rep3 : FgPoS → Bytes → Prop
  Rep4 : Option FgPoS → Option Bytes → Prop
  len1 : ∀ p d, Rep1 p d → d.length = 32
  len2 : ∀ p d, Rep2 p d → d.length = 32
  len3 : ∀ p d, Rep3 p d → d.length = 32
  len4 : ∀ p d?, Rep4 p d? → ∀ d, d? = some d → d.length = 32
  eq1  : ∀ p1 p2 d1 d2, Rep1 p1 d1 → Rep1 p2 d2 → ddhEqPure P.isValidDhTriple p1 p2 = (d1 == d2)
  eq2  : ∀ p1 p2 d1 d2, Rep2 p1 d1 → Rep2 p2 d2 → ddhEqPure P.isValidDhTriple p1 p2 = (d1 == d2)
  eq3  : ∀ p1 p2 d1 d2, Rep3 p1 d1 → Rep3 p2 d2 → ddhEqPure P.isValidDhTriple p1 p2 = (d1 == d2)
  eq4  : ∀ o1 o2 d1 d2, Rep4 o1 d1 → Rep4 o2 d2 → ddhEqOptPure P.isValidDhTriple o1 o2 = (d1 == d2)
  sec1 : ∀ d, d.length = 32 → Rep1 (mkSecretPosPure P d) d
  sec2 : ∀ d, d.length = 32 → Rep2 (mkSecretPosPure P d) d
  sec3 : ∀ d, d.length = 32 → Rep3 (mkSecretPosPure P d) d
  sec4 : ∀ d? : Option Bytes, (∀ d, d? = some d → d.length = 32) →
           Rep4 (d?.map (mkSecretPosPure P)) d?

def FgTupleRel {P : Primitives} (R : FgSlotReps P)
    (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS)
    (dh1 dh2 dh3 : Bytes) (dh4? : Option Bytes) (ss : Bytes) : Prop :=
  R.Rep1 pos1 dh1 ∧ R.Rep2 pos2 dh2 ∧ R.Rep3 pos3 dh3 ∧ R.Rep4 pos4? dh4? ∧ ss.length = 32

def FgEntryRel {P : Primitives} (R : FgSlotReps P)
    (e : FgPatchEntry) (sdk : Bytes × DRKey) : Prop :=
  ∃ dh1 dh2 dh3 dh4?,
    sdk.1 = buildSecrets dh1 dh2 dh3 dh4? e.ss ∧
    sdk.2 = e.dk ∧
    FgTupleRel R e.pos1 e.pos2 e.pos3 e.pos4? dh1 dh2 dh3 dh4? e.ss

theorem fgEntryMatchesPure_eq_beq_of_fgEntryRel {P : Primitives} (R : FgSlotReps P)
    {pos1 pos2 pos3 : FgPoS} {pos4? : Option FgPoS}
    {dh1 dh2 dh3 : Bytes} {dh4? : Option Bytes} {ss : Bytes}
    {e : FgPatchEntry} {sdk : Bytes × DRKey}
    (hT : FgTupleRel R pos1 pos2 pos3 pos4? dh1 dh2 dh3 dh4? ss)
    (hE : FgEntryRel R e sdk) :
    fgEntryMatchesPure P.isValidDhTriple pos1 pos2 pos3 pos4? ss e =
      (sdk.1 == buildSecrets dh1 dh2 dh3 dh4? ss) := by
  rcases hT with ⟨h1, h2, h3, h4, hss⟩
  rcases hE with ⟨dh1', dh2', dh3', dh4?', hsdk1, _, h1', h2', h3', h4', hss'⟩
  unfold fgEntryMatchesPure
  rw [hsdk1, R.eq1 _ _ _ _ h1 h1', R.eq2 _ _ _ _ h2 h2', R.eq3 _ _ _ _ h3 h3', R.eq4 _ _ _ _ h4 h4']
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq,
      (eq_comm : buildSecrets dh1' dh2' dh3' dh4?' e.ss = buildSecrets dh1 dh2 dh3 dh4? ss ↔ _),
      buildSecrets_eq_iff_of_len32
        (R.len1 _ _ h1) (R.len2 _ _ h2) (R.len3 _ _ h3) (R.len4 _ _ h4) hss
        (R.len1 _ _ h1') (R.len2 _ _ h2') (R.len3 _ _ h3') (R.len4 _ _ h4') hss']
  by_cases hss_eq : ss = e.ss
  · subst hss_eq
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      Bool.and_eq_true, beq_iff_eq, true_and]
    tauto
  · have hne : (ss != e.ss) = true := bne_iff_ne.mpr hss_eq
    simp [hne, hss_eq]

def FgCacheRel {P : Primitives} (R : FgSlotReps P) (maxLen : ℕ)
    (fgL : List FgPatchEntry) (rawRoCache roCache : List (Bytes × DRKey)) : Prop :=
  fgL.length ≤ maxLen ∧
  rawRoCache = roCache.filter (fun (s, _) => (parseRoSecrets s).isNone) ∧
  List.Forall₂ (FgEntryRel R) fgL (roCache.filter (fun (s, _) => (parseRoSecrets s).isSome))

theorem find?_filter_eq_find?_of_imp {α : Type} (p q : α → Bool) (xs : List α)
    (h : ∀ x, p x = true → q x = true) :
    (xs.filter q).find? p = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hpx : p x = true
    · rw [List.filter_cons_of_pos (h x hpx), List.find?_cons_of_pos hpx, List.find?_cons_of_pos hpx]
    · by_cases hqx : q x = true
      · rw [List.filter_cons_of_pos hqx, List.find?_cons_of_neg hpx, List.find?_cons_of_neg hpx, ih]
      · rw [List.filter_cons_of_neg hqx, List.find?_cons_of_neg hpx, ih]

theorem forall₂_find?_map_eq {α β γ : Type} {Rel : α → β → Prop}
    {p : α → Bool} {q : β → Bool} {f : α → γ} {g : β → γ}
    {xs : List α} {ys : List β}
    (hR : List.Forall₂ Rel xs ys)
    (hpq : ∀ x y, Rel x y → p x = q y ∧ f x = g y) :
    (xs.find? p).map f = (ys.find? q).map g := by
  induction hR with
  | nil => rfl
  | cons hxy _ ih =>
    rcases hpq _ _ hxy with ⟨hp, hf⟩
    simp only [List.find?_cons, hp]
    cases q _
    · exact ih
    · simp [hf]

theorem fgPatchPure_eq_or_sample {P : Primitives} (R : FgSlotReps P)
    {maxLen : ℕ} {fgL : List FgPatchEntry} {rawRoCache roCache : List (Bytes × DRKey)}
    {pos1 pos2 pos3 : FgPoS} {pos4? : Option FgPoS}
    {dh1 dh2 dh3 : Bytes} {dh4? : Option Bytes} {ss : Bytes}
    (hCache : FgCacheRel R maxLen fgL rawRoCache roCache)
    (hT : FgTupleRel R pos1 pos2 pos3 pos4? dh1 dh2 dh3 dh4? ss) :
    let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
    (∃ dk,
      evalHkdfOrRo true P roCache secrets = pure (dk, roCache) ∧
      fgPatchPure P.isValidDhTriple maxLen pos1 pos2 pos3 pos4? ss fgL = pure (dk, fgL)) ∨
    (evalHkdfOrRo true P roCache secrets =
      (sampleDRKey96 >>= fun dk => pure (dk, (secrets, dk) :: roCache)) ∧
     fgPatchPure P.isValidDhTriple maxLen pos1 pos2 pos3 pos4? ss fgL =
      (sampleDRKey96 >>= fun dk =>
        pure (dk, { pos1 := pos1, pos2 := pos2, pos3 := pos3, pos4? := pos4?, ss := ss, dk :=
          dk } :: fgL)) ∧
     ∀ dk, fgL.length < maxLen →
       FgCacheRel R maxLen
         ({ pos1 := pos1, pos2 := pos2, pos3 := pos3, pos4? := pos4?, ss := ss, dk := dk } :: fgL)
         rawRoCache ((secrets, dk) :: roCache)) := by
  intro secrets
  rcases hCache with ⟨hLen, hRaw, hForall⟩
  rcases hT with ⟨h1, h2, h3, h4, hss⟩
  have hParse : parseRoSecrets secrets = some (dh1, dh2, dh3, dh4?, ss) :=
    parseRoSecrets_buildSecrets (R.len1 _ _ h1) (R.len2 _ _ h2) (R.len3 _ _ h3) (R.len4 _ _ h4) hss
  have hTake : fgL.take maxLen = fgL := List.take_of_length_le hLen
  have hFiltFind :
      (roCache.filter (fun (s, _) => (parseRoSecrets s).isSome)).find? (fun (s, _) =>
        s == secrets) =
      roCache.find? (fun (s, _) => s == secrets) := by
    apply find?_filter_eq_find?_of_imp
    rintro ⟨s, dk⟩ hs
    simp only [beq_iff_eq] at hs
    subst hs
    simp [hParse]
  have hMapEq :
      (fgL.find? (fgEntryMatchesPure P.isValidDhTriple pos1 pos2 pos3 pos4? ss)).map FgPatchEntry.dk
        =
      (roCache.find? (fun (s, _) => s == secrets)).map Prod.snd := by
    rw [← hFiltFind]
    exact forall₂_find?_map_eq hForall (fun e sdk hE =>
      ⟨fgEntryMatchesPure_eq_beq_of_fgEntryRel R ⟨h1, h2, h3, h4, hss⟩ hE,
        by rcases hE with ⟨_, _, _, _, _, hdk, _⟩; exact hdk.symm⟩)
  unfold evalHkdfOrRo fgPatchPure
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hTake]
  cases hF1 : fgL.find? (fgEntryMatchesPure P.isValidDhTriple pos1 pos2 pos3 pos4? ss) <;>
    cases hF2 : roCache.find? (fun (s, _) => s == secrets)
  · right
    refine ⟨rfl, rfl, fun dk hLt => ⟨by simp; omega, ?_, ?_⟩⟩
    · rw [hRaw, List.filter_cons_of_neg (by simp [hParse])]
    · rw [List.filter_cons_of_pos (by simp [hParse])]
      exact List.Forall₂.cons ⟨dh1, dh2, dh3, dh4?, rfl, rfl, h1, h2, h3, h4, hss⟩ hForall
  · rw [hF1, hF2] at hMapEq; simp at hMapEq
  · rw [hF1, hF2] at hMapEq; simp at hMapEq
  · rw [hF1, hF2] at hMapEq
    simp only [Option.map_some, Option.some.injEq] at hMapEq
    left
    exact ⟨_, by simp [hMapEq], rfl⟩

/-! ## State erasure and EC bounds -/

theorem validTaggedPks_length_le_fg {N : Nat} {tagged : List (Nat × Bytes)}
    (hV : ValidTaggedPks N tagged) : tagged.length ≤ N := by
  have hsub : (tagged.map Prod.fst).Subperm (List.range N) :=
    hV.2.subperm (fun y hy => by
      rw [List.mem_map] at hy
      rcases hy with ⟨p, hp, rfl⟩
      exact List.mem_range.mpr (hV.1 p hp))
  simpa using hsub.length_le

def noOpkSlotFlatIdx (S : Setup) (p : Nat × Nat × Nat) : Nat :=
  (p.1 * S.N_recv + p.2.1) * S.N_no_opk + p.2.2

theorem noOpkSlotFlatIdx_lt (S : Setup) {u j l : Nat}
    (hu : u < S.N_id) (hj : j < S.N_recv) (hl : l < S.N_no_opk) :
    noOpkSlotFlatIdx S (u, j, l) < S.N_no_opk_tot := by
  unfold noOpkSlotFlatIdx Setup.N_no_opk_tot Setup.N_spk_tot
  have h_uj : u * S.N_recv + j < S.N_id * S.N_recv := spkSlotFlatIdx_lt S hu hj
  have h_uj1 : u * S.N_recv + j + 1 ≤ S.N_id * S.N_recv := Nat.succ_le_of_lt h_uj
  calc (u * S.N_recv + j) * S.N_no_opk + l
      < (u * S.N_recv + j) * S.N_no_opk + S.N_no_opk := Nat.add_lt_add_left hl _
    _ = (u * S.N_recv + j + 1) * S.N_no_opk := by ring
    _ ≤ (S.N_id * S.N_recv) * S.N_no_opk := Nat.mul_le_mul_right S.N_no_opk h_uj1
    _ = S.N_id * S.N_recv * S.N_no_opk := rfl

theorem noOpkSlotFlatIdx_inj (S : Setup) {k1 k2 : Nat × Nat × Nat}
    (hj1 : k1.2.1 < S.N_recv) (hl1 : k1.2.2 < S.N_no_opk)
    (hj2 : k2.2.1 < S.N_recv) (hl2 : k2.2.2 < S.N_no_opk)
    (heq : noOpkSlotFlatIdx S k1 = noOpkSlotFlatIdx S k2) : k1 = k2 := by
  rcases k1 with ⟨u1, j1, l1⟩
  rcases k2 with ⟨u2, j2, l2⟩
  dsimp [noOpkSlotFlatIdx] at hj1 hl1 hj2 hl2 heq
  have hdiv1 : ((u1 * S.N_recv + j1) * S.N_no_opk + l1) / S.N_no_opk = u1 * S.N_recv + j1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)), Nat.div_eq_of_lt hl1,
      Nat.add_zero]
  have hdiv2 : ((u2 * S.N_recv + j2) * S.N_no_opk + l2) / S.N_no_opk = u2 * S.N_recv + j2 := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)), Nat.div_eq_of_lt hl2,
      Nat.add_zero]
  have huj : spkSlotFlatIdx S (u1, j1) = spkSlotFlatIdx S (u2, j2) := by
    dsimp [spkSlotFlatIdx]; rw [← hdiv1, ← hdiv2, heq]
  have hpair := spkSlotFlatIdx_inj S hj1 hj2 huj
  injection hpair with hu hj
  subst hu; subst hj
  have hl : l1 = l2 := Nat.add_left_cancel heq
  subst hl
  rfl

def ValidUsedRecvOpk (S : Setup) (used : List (Nat × Nat × Nat)) : Prop :=
  (∀ x ∈ used, x.1 < S.N_id ∧ x.2.1 < S.N_recv ∧ x.2.2 < S.N_opk) ∧
  (used.map (opkSlotFlatIdx S)).Nodup

def ValidUsedRecvNoOpk (S : Setup) (used : List (Nat × Nat × Nat)) : Prop :=
  (∀ x ∈ used, x.1 < S.N_id ∧ x.2.1 < S.N_recv ∧ x.2.2 < S.N_no_opk) ∧
  (used.map (noOpkSlotFlatIdx S)).Nodup

theorem validUsedRecvOpk_cons (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (used : List (Nat × Nat × Nat))
    (hV : ValidUsedRecvOpk S used)
    (hFresh : used.contains (k.val, j.val, o.val) = false) :
    ValidUsedRecvOpk S ((k.val, j.val, o.val) :: used) := by
  have hnot_in : opkSlotFlatIdx S (k.val, j.val, o.val) ∉ used.map (opkSlotFlatIdx S) := by
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨x, hx_mem, hx_eq⟩
    have hx_bounds := hV.1 x hx_mem
    have hxeq : x = (k.val, j.val, o.val) :=
      opkSlotFlatIdx_inj S hx_bounds.2.1 hx_bounds.2.2 j.isLt o.isLt hx_eq
    subst hxeq
    have hcont : used.contains (k.val, j.val, o.val) = true := List.contains_iff_mem.mpr hx_mem
    rw [hFresh] at hcont; cases hcont
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact ⟨k.isLt, j.isLt, o.isLt⟩
    · exact hV.1 x hmem
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨hnot_in, hV.2⟩

theorem validUsedRecvNoOpk_cons (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (used : List (Nat × Nat × Nat))
    (hV : ValidUsedRecvNoOpk S used)
    (hFresh : used.contains (k.val, j.val, l.val) = false) :
    ValidUsedRecvNoOpk S ((k.val, j.val, l.val) :: used) := by
  have hnot_in : noOpkSlotFlatIdx S (k.val, j.val, l.val) ∉ used.map (noOpkSlotFlatIdx S) := by
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨x, hx_mem, hx_eq⟩
    have hx_bounds := hV.1 x hx_mem
    have hxeq : x = (k.val, j.val, l.val) :=
      noOpkSlotFlatIdx_inj S hx_bounds.2.1 hx_bounds.2.2 j.isLt l.isLt hx_eq
    subst hxeq
    have hcont : used.contains (k.val, j.val, l.val) = true := List.contains_iff_mem.mpr hx_mem
    rw [hFresh] at hcont; cases hcont
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact ⟨k.isLt, j.isLt, l.isLt⟩
    · exact hV.1 x hmem
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨hnot_in, hV.2⟩

def ValidKeyIndRespFg (S : Setup) (st : KeyIndState S) : Prop :=
  ValidUsedRecvOpk S st.usedRecvOPK ∧
  ValidUsedRecvNoOpk S st.usedRecvNoOPK ∧
  st.respSessions.length ≤ st.usedRecvOPK.length + st.usedRecvNoOPK.length

def ValidKeyIndEcFg (S : Setup) (st : KeyIndState S) : Prop :=
  ValidPrincipals S st.principals ∧
  ValidSpkBundles S st.spkBundles ∧
  ValidOpkEntries S st.opkEntries ∧
  ValidSessionIds S ((sessPksKeyInd S st).map Prod.fst) ∧
  ValidKeyIndRespFg S st

theorem validKeyIndEcFg_empty (S : Setup) (secb : Bool) :
    ValidKeyIndEcFg S (KeyIndState.empty S secb) := by
  have hNil := validEcLists_nil S
  exact ⟨hNil.1, hNil.2.1, hNil.2.2.1, hNil.2.2.2,
    ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩,
    ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩,
    Nat.le_refl 0⟩

theorem validKeyIndEc_lengths_le_fg (S : Setup) (P : Primitives) (st : KeyIndState S)
    (hV : ValidKeyIndEcFg S st) :
    st.principals.length ≤ S.N_dh ∧
    st.spkBundles.length ≤ S.N_dh ∧
    st.opkEntries.length ≤ S.N_dh ∧
    st.sessions.length ≤ S.N_dh := by
  have hTag := validTaggedPks_ecTaggedFromLists S P
    st.principals st.spkBundles st.opkEntries (sessPksKeyInd S st)
    ⟨hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1⟩
  have hLen := validTaggedPks_length_le_fg hTag
  unfold ecTaggedFromLists sessPksKeyInd at hLen
  simp only [List.length_append, List.length_map] at hLen
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem validKeyIndEc_resp_length_le_fg (S : Setup) (st : KeyIndState S)
    (hV : ValidKeyIndEcFg S st) :
    st.respSessions.length ≤ S.N_sess_tot := by
  have hR := hV.2.2.2.2
  have hsub1 : (st.usedRecvOPK.map (opkSlotFlatIdx S)).Subperm (List.range S.N_opk_tot) :=
    hR.1.2.subperm (fun y hy => by
      rw [List.mem_map] at hy
      rcases hy with ⟨x, hx, rfl⟩
      have hb := hR.1.1 x hx
      exact List.mem_range.mpr (opkSlotFlatIdx_lt S hb.1 hb.2.1 hb.2.2))
  have hsub2 : (st.usedRecvNoOPK.map (noOpkSlotFlatIdx S)).Subperm (List.range S.N_no_opk_tot) :=
    hR.2.1.2.subperm (fun y hy => by
      rw [List.mem_map] at hy
      rcases hy with ⟨x, hx, rfl⟩
      have hb := hR.2.1.1 x hx
      exact List.mem_range.mpr (noOpkSlotFlatIdx_lt S hb.1 hb.2.1 hb.2.2))
  have hle1 : st.usedRecvOPK.length ≤ S.N_opk_tot := by simpa using hsub1.length_le
  have hle2 : st.usedRecvNoOPK.length ≤ S.N_no_opk_tot := by simpa using hsub2.length_le
  have hle3 := hR.2.2
  unfold Setup.N_sess_tot Setup.N_recv_tot
  omega

theorem chooseInitPartnerDrKeyRand_eq_pure {S : Setup} (P : Primitives)
    (respSessions : List (KeyIndRespEntry S)) (s1 s2 : KeyIndInitiatorEntry S)
    (hLen : respSessions.length ≤ S.N_sess_tot)
    (hHdr : s1.hdr = s2.hdr := by rfl)
    (hIk : s1.peerIkPk = s2.peerIkPk := by rfl)
    (hSpk : s1.peerSpkPk = s2.peerSpkPk := by rfl)
    (hOpk : s1.peerOpkPk? = s2.peerOpkPk? := by rfl)
    (hPq : s1.peerPqspkPk = s2.peerPqspkPk := by rfl) :
    chooseInitPartnerDrKeyRand P respSessions s1 =
      chooseInitPartnerDrKeyRandPure P respSessions s2 := by
  unfold chooseInitPartnerDrKeyRand chooseInitPartnerDrKeyRandPure keyIndPartnerRandKey?
  rw [List.take_of_length_le hLen]
  have hFn : (fun r => keyIndPartner P s1 r) = (fun r => keyIndPartner P s2 r) := by
    funext r
    unfold keyIndPartner
    rw [hHdr, hIk, hSpk, hOpk, hPq]
  rw [hFn]
  cases respSessions.find? (fun r => keyIndPartner P s2 r) <;> rfl

def erasePrincipalEntryFg (uIdx idx : ℕ) (e : PrincipalEntry) : PrincipalEntry :=
  if idx == uIdx then { e with secIKA0 := [] } else e

def erasePrincipalsFg (uIdx : ℕ) (principals : List (Nat × PrincipalEntry)) :
    List (Nat × PrincipalEntry) :=
  principals.map (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e))

def eraseSessionEntryFg {S : Setup} (sIdx : ℕ) (s : KeyIndInitiatorEntry S) :
    KeyIndInitiatorEntry S :=
  if initSessionSlotIdx s.sid == sIdx then { s with ekASk := [] } else s

def eraseSessionsFg {S : Setup} (sIdx : ℕ) (sessions : List (KeyIndInitiatorEntry S)) :
    List (KeyIndInitiatorEntry S) :=
  sessions.map (eraseSessionEntryFg sIdx)

def eraseStateFg {S : Setup} (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (st : KeyIndState S) : KeyIndState S :=
  { st with
    principals := if useDh1 then erasePrincipalsFg targetIdx st.principals else st.principals
    spkBundles := eraseSpkBundlesFg S targetSpkIdx st.spkBundles
    sessions   := if useDh1 then st.sessions else eraseSessionsFg targetIdx st.sessions
    roCache    := [] }

@[simp]
theorem erasePrincipalEntryFg_ikAPk (uIdx idx : ℕ) (e : PrincipalEntry) :
    (erasePrincipalEntryFg uIdx idx e).ikAPk = e.ikAPk := by
  unfold erasePrincipalEntryFg; split_ifs <;> rfl

@[simp]
theorem erasePrincipalEntryFg_secIKAsign (uIdx idx : ℕ) (e : PrincipalEntry) :
    (erasePrincipalEntryFg uIdx idx e).secIKAsign = e.secIKAsign := by
  unfold erasePrincipalEntryFg; split_ifs <;> rfl

@[simp]
theorem erasePrincipalEntryFg_ikSignPk (uIdx idx : ℕ) (e : PrincipalEntry) :
    (erasePrincipalEntryFg uIdx idx e).ikSignPk = e.ikSignPk := by
  unfold erasePrincipalEntryFg; split_ifs <;> rfl

@[simp]
theorem erasePrincipalEntryFg_corrupted (uIdx idx : ℕ) (e : PrincipalEntry) :
    (erasePrincipalEntryFg uIdx idx e).corrupted = e.corrupted := by
  unfold erasePrincipalEntryFg; split_ifs <;> rfl

@[simp]
theorem eraseSpkBundleEntryFg_spkPk (S : Setup) (bIdx : ℕ) (k : Nat × Nat) (b : SpkBundleEntry) :
    (eraseSpkBundleEntryFg S bIdx k b).spkPk = b.spkPk := by
  unfold eraseSpkBundleEntryFg; split_ifs <;> rfl

@[simp]
theorem eraseSpkBundleEntryFg_pqspkSk (S : Setup) (bIdx : ℕ) (k : Nat × Nat) (b : SpkBundleEntry) :
    (eraseSpkBundleEntryFg S bIdx k b).pqspkSk = b.pqspkSk := by
  unfold eraseSpkBundleEntryFg; split_ifs <;> rfl

@[simp]
theorem eraseSpkBundleEntryFg_pqspkPk (S : Setup) (bIdx : ℕ) (k : Nat × Nat) (b : SpkBundleEntry) :
    (eraseSpkBundleEntryFg S bIdx k b).pqspkPk = b.pqspkPk := by
  unfold eraseSpkBundleEntryFg; split_ifs <;> rfl

@[simp]
theorem eraseSessionEntryFg_sid {S : Setup} (sIdx : ℕ) (s : KeyIndInitiatorEntry S) :
    (eraseSessionEntryFg sIdx s).sid = s.sid := by
  unfold eraseSessionEntryFg; split_ifs <;> rfl

@[simp]
theorem eraseSessionEntryFg_fresh {S : Setup} (sIdx : ℕ) (s : KeyIndInitiatorEntry S) :
    (eraseSessionEntryFg sIdx s).fresh = s.fresh := by
  unfold eraseSessionEntryFg; split_ifs <;> rfl

@[simp]
theorem eraseSessionEntryFg_tested {S : Setup} (sIdx : ℕ) (s : KeyIndInitiatorEntry S) :
    (eraseSessionEntryFg sIdx s).tested = s.tested := by
  unfold eraseSessionEntryFg; split_ifs <;> rfl

@[simp]
theorem eraseSessionEntryFg_revealed {S : Setup} (sIdx : ℕ) (s : KeyIndInitiatorEntry S) :
    (eraseSessionEntryFg sIdx s).revealed = s.revealed := by
  unfold eraseSessionEntryFg; split_ifs <;> rfl

@[simp]
theorem eraseSessionEntryFg_drKeyReal {S : Setup} (sIdx : ℕ) (s : KeyIndInitiatorEntry S) :
    (eraseSessionEntryFg sIdx s).drKeyReal = s.drKeyReal := by
  unfold eraseSessionEntryFg; split_ifs <;> rfl

@[simp]
theorem eraseSessionEntryFg_drKeyRand {S : Setup} (sIdx : ℕ) (s : KeyIndInitiatorEntry S) :
    (eraseSessionEntryFg sIdx s).drKeyRand = s.drKeyRand := by
  unfold eraseSessionEntryFg; split_ifs <;> rfl

@[simp]
theorem keyIndPartner_eraseSessionEntryFg {S : Setup} (P : Primitives) (sIdx : ℕ)
    (s : KeyIndInitiatorEntry S) (r : KeyIndRespEntry S) :
    keyIndPartner P (eraseSessionEntryFg sIdx s) r = keyIndPartner P s r := by
  unfold eraseSessionEntryFg; split_ifs <;> rfl

@[simp]
theorem erasePrincipalsFg_length (uIdx : ℕ) (principals : List (Nat × PrincipalEntry)) :
    (erasePrincipalsFg uIdx principals).length = principals.length := by
  simp [erasePrincipalsFg]

@[simp]
theorem eraseSpkBundlesFg_length (S : Setup) (bIdx : ℕ)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) :
    (eraseSpkBundlesFg S bIdx spkBundles).length = spkBundles.length := by
  simp [eraseSpkBundlesFg]

@[simp]
theorem any_idx_erasePrincipalsFg (uIdx u : ℕ) (principals : List (Nat × PrincipalEntry)) :
    (erasePrincipalsFg uIdx principals).any (fun (idx, _) => idx == u) =
      principals.any (fun (idx, _) => idx == u) := by
  simp [erasePrincipalsFg, List.any_map, Function.comp_def]

@[simp]
theorem any_idx_eraseSpkBundlesFg (S : Setup) (bIdx : ℕ) (k0 : Nat × Nat)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) :
    (eraseSpkBundlesFg S bIdx spkBundles).any (fun (k, _) => k == k0) =
      spkBundles.any (fun (k, _) => k == k0) := by
  simp [eraseSpkBundlesFg, List.any_map, Function.comp_def]

@[simp]
theorem any_sid_eraseSessionsFg {S : Setup} (sIdx : ℕ) (sid : SessionId S)
    (sessions : List (KeyIndInitiatorEntry S)) :
    (eraseSessionsFg sIdx sessions).any (fun e => e.sid == sid) =
      sessions.any (fun e => e.sid == sid) := by
  simp [eraseSessionsFg, List.any_map, Function.comp_def]

theorem findHonestPrincipal_erasePrincipalsFg (P : Primitives) (uIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    findHonestPrincipal P (erasePrincipalsFg uIdx principals) ikB =
      (findHonestPrincipal P principals ikB).map (fun (idx, e) =>
        (idx, erasePrincipalEntryFg uIdx idx e)) := by
  simp [findHonestPrincipal, erasePrincipalsFg, List.find?_map]

@[simp]
theorem findHonestPrincipal_erasePrincipalsFg_isSome (P : Primitives) (uIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    (findHonestPrincipal P (erasePrincipalsFg uIdx principals) ikB).isSome =
      (findHonestPrincipal P principals ikB).isSome := by
  rw [findHonestPrincipal_erasePrincipalsFg]
  cases findHonestPrincipal P principals ikB <;> rfl

@[simp]
theorem resolveSigPk_erasePrincipalsFg (P : Primitives) (uIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    resolveSigPk P (erasePrincipalsFg uIdx principals) ikB =
      resolveSigPk P principals ikB := by
  unfold resolveSigPk
  rw [findHonestPrincipal_erasePrincipalsFg]
  cases findHonestPrincipal P principals ikB with
  | none => rfl
  | some p => rcases p with ⟨idx, e⟩; simp

@[simp]
theorem isHonestUncorruptedPeer_erasePrincipalsFg (P : Primitives) (uIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    isHonestUncorruptedPeer P (erasePrincipalsFg uIdx principals) ikB =
      isHonestUncorruptedPeer P principals ikB := by
  unfold isHonestUncorruptedPeer
  rw [findHonestPrincipal_erasePrincipalsFg]
  cases findHonestPrincipal P principals ikB with
  | none => rfl
  | some p => rcases p with ⟨idx, e⟩; simp

@[simp]
theorem checkBundleProvenance_eraseSpkBundlesFg (P : Primitives) (S : Setup) (bIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    checkBundleProvenance P principals (eraseSpkBundlesFg S bIdx spkBundles) opkEntries bundle =
      checkBundleProvenance P principals spkBundles opkEntries bundle := by
  unfold checkBundleProvenance
  cases findHonestPrincipal P principals bundle.ikB with
  | none => rfl
  | some p =>
    rcases p with ⟨idx, e⟩
    simp [eraseSpkBundlesFg, List.any_map, Function.comp_def]

@[simp]
theorem checkBundleProvenance_erasePrincipalsFg (P : Primitives) (uIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    checkBundleProvenance P (erasePrincipalsFg uIdx principals) spkBundles opkEntries bundle =
      checkBundleProvenance P principals spkBundles opkEntries bundle := by
  unfold checkBundleProvenance
  rw [findHonestPrincipal_erasePrincipalsFg]
  cases findHonestPrincipal P principals bundle.ikB <;> rfl

theorem find?_idx_erasePrincipalsFg (uIdx u : ℕ) (principals : List (Nat × PrincipalEntry)) :
    (erasePrincipalsFg uIdx principals).find? (fun (idx, _) => idx == u) =
      (principals.find? (fun (idx, _) => idx == u)).map (fun (idx, e) =>
        (idx, erasePrincipalEntryFg uIdx idx e)) := by
  simp [erasePrincipalsFg, List.find?_map]

theorem find?_idx_eraseSpkBundlesFg (S : Setup) (bIdx : ℕ) (k0 : Nat × Nat)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) :
    (eraseSpkBundlesFg S bIdx spkBundles).find? (fun (k, _) => k == k0) =
      (spkBundles.find? (fun (k, _) => k == k0)).map (fun (k, b) =>
        (k, eraseSpkBundleEntryFg S bIdx k b)) := by
  simp [eraseSpkBundlesFg, List.find?_map]

theorem find?_sid_eraseSessionsFg {S : Setup} (sIdx : ℕ) (sid : SessionId S)
    (sessions : List (KeyIndInitiatorEntry S)) :
    (eraseSessionsFg sIdx sessions).find? (fun e => e.sid == sid) =
      (sessions.find? (fun e => e.sid == sid)).map (eraseSessionEntryFg sIdx) := by
  simp [eraseSessionsFg, List.find?_map]

@[simp]
theorem choosePartnerDrKeyRandPure_eraseSessionsFg {S : Setup} (P : Primitives) (sIdx : ℕ)
    (sessions : List (KeyIndInitiatorEntry S)) (r : KeyIndRespEntry S) :
    choosePartnerDrKeyRandPure P (eraseSessionsFg sIdx sessions) r =
      choosePartnerDrKeyRandPure P sessions r := by
  unfold choosePartnerDrKeyRandPure
  have hF : ((eraseSessionsFg sIdx sessions).take S.N_dh).find? (fun s => keyIndPartner P s r) =
      ((sessions.take S.N_dh).find? (fun s =>
        keyIndPartner P s r)).map (eraseSessionEntryFg sIdx) := by
    simp [eraseSessionsFg, ← List.map_take, List.find?_map]
  rw [hF]
  cases (sessions.take S.N_dh).find? (fun s => keyIndPartner P s r) <;> simp

@[simp]
theorem isFreshKeyIndSession_eraseStateFg {S : Setup} (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (st : KeyIndState S) (sid : SessionId S) :
    isKeyIndSessionTestable (eraseStateFg useDh1 targetIdx targetSpkIdx st) sid =
      isKeyIndSessionTestable st sid := by
  unfold isKeyIndSessionTestable eraseStateFg
  cases useDh1 with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, find?_sid_eraseSessionsFg]
    cases st.sessions.find? (fun e => e.sid == sid) <;> simp

theorem corrupt_map_erasePrincipalsFg (uIdx u : ℕ) (principals : List (Nat × PrincipalEntry)) :
    (erasePrincipalsFg uIdx principals).map (fun (idx, e) =>
      if idx == u then (idx, { e with corrupted := true }) else (idx, e)) =
    erasePrincipalsFg uIdx (principals.map (fun (idx, e) =>
      if idx == u then (idx, { e with corrupted := true }) else (idx, e))) := by
  unfold erasePrincipalsFg erasePrincipalEntryFg
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
  dsimp only [Function.comp_def]
  by_cases hk : (idx == uIdx) = true <;> by_cases hu : (idx == u) = true <;> simp [hk, hu]

theorem test_map_eraseSessionsFg {S : Setup} (sIdx : ℕ) (sid : SessionId S)
    (sessions : List (KeyIndInitiatorEntry S)) :
    (eraseSessionsFg sIdx sessions).map (fun s =>
      if s.sid == sid then { s with tested := true } else s) =
    eraseSessionsFg sIdx (sessions.map (fun s =>
      if s.sid == sid then { s with tested := true } else s)) := by
  unfold eraseSessionsFg eraseSessionEntryFg
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun s _ => ?_)
  dsimp only [Function.comp_def]
  by_cases hk : (initSessionSlotIdx s.sid == sIdx) = true <;>
    by_cases hs : (s.sid == sid) = true <;> simp [hk, hs]

theorem reveal_map_eraseSessionsFg {S : Setup} (sIdx : ℕ) (sid : SessionId S)
    (sessions : List (KeyIndInitiatorEntry S)) :
    (eraseSessionsFg sIdx sessions).map (fun s =>
      if s.sid == sid then { s with revealed := true } else s) =
    eraseSessionsFg sIdx (sessions.map (fun s =>
      if s.sid == sid then { s with revealed := true } else s)) := by
  unfold eraseSessionsFg eraseSessionEntryFg
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun s _ => ?_)
  dsimp only [Function.comp_def]
  by_cases hk : (initSessionSlotIdx s.sid == sIdx) = true <;>
    by_cases hs : (s.sid == sid) = true <;> simp [hk, hs]

/-! ## Simulation inequality with sticky cutoff -/

theorem evalDist_bind_true_eq_probExpect_comp {α : Type} (mx : ProbComp α) (k : α → ProbComp Bool) :
    𝒟[mx >>= k] {true} = probExpect mx (fun x => 𝒟[k x] {true}) := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  unfold probExpect
  rw [evalDist_bind_of_discrete,
      MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]

theorem evalDist_bind_true_eq_zero_of_support {α : Type} (mx : ProbComp α) (k : α → ProbComp Bool)
    (h : ∀ x ∈ support mx, 𝒟[k x] {true} = 0) :
    𝒟[mx >>= k] {true} = 0 := by
  rw [evalDist_bind_true_eq_probExpect_comp]
  refine le_antisymm ?_ zero_le
  refine le_trans (probExpect_mono_of_support _ _ (fun _ => 0) (fun x hx => le_of_eq (h x hx))) ?_
  simp [probExpect_const]

theorem evalDist_bind_true_mono_of_support {α : Type} (mx : ProbComp α)
    (k1 k2 : α → ProbComp Bool)
    (h : ∀ x ∈ support mx, 𝒟[k1 x] {true} ≤ 𝒟[k2 x] {true}) :
    𝒟[mx >>= k1] {true} ≤ 𝒟[mx >>= k2] {true} := by
  rw [evalDist_bind_true_eq_probExpect_comp, evalDist_bind_true_eq_probExpect_comp]
  exact probExpect_mono_of_support mx _ _ h

theorem evalDist_simulateQ_eq_zero_of_dead_preserved
    {ι α St : Type} {QSpec : OracleSpec.{0, 0} ι}
    (Dead : St → Bool)
    (impl : QueryImpl QSpec (StateT St ProbComp))
    (hPres : ∀ q st, Dead st = true → ∀ x ∈ support ((impl q).run st), Dead x.2 = true)
    (obs : α × St → ProbComp Bool)
    (hObs : ∀ a st, Dead st = true → 𝒟[obs (a, st)] {true} = 0)
    (oa : OracleComp (unifSpec + QSpec) α) (st : St) (hDead : Dead st = true) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
    𝒟[(simulateQ full oa).run st >>= obs] {true} = 0 := by
  intro full
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hObs a st hDead
  | query_bind q mx ih =>
    rcases q with uq | gq
    · dsimp only [full]
      rw [simulateQ_run_query_inl, bind_assoc]
      exact evalDist_bind_true_eq_zero_of_support _ _ (fun u _ => ih u st hDead)
    · dsimp only [full]
      rw [simulateQ_run_query_inr, bind_assoc]
      exact evalDist_bind_true_eq_zero_of_support _ _ (fun x hx =>
        ih x.1 x.2 (hPres gq st hDead x hx))

theorem evalDist_simulateQ_le_of_step_or_dead
    {ι α St1 St2 : Type} {QSpec : OracleSpec.{0, 0} ι}
    (Dead : St1 → Bool)
    (Rel : ℕ → St1 → St2 → Prop)
    (impl1 : QueryImpl QSpec (StateT St1 ProbComp))
    (impl2 : QueryImpl QSpec (StateT St2 ProbComp))
    (hDeadPres : ∀ q s1, Dead s1 = true → ∀ x ∈ support ((impl1 q).run s1), Dead x.2 = true)
    (hStep : ∀ (q : ι) (rem : ℕ) (s1 : St1) (s2 : St2),
      Dead s1 = false →
      Rel (rem + 1) s1 s2 →
      ∀ (k1 : QSpec.Range q × St1 → ProbComp Bool)
        (k2 : QSpec.Range q × St2 → ProbComp Bool),
        (∀ r s1' s2', Dead s1' = false → Rel rem s1' s2' →
          𝒟[k1 (r, s1')] {true} ≤ 𝒟[k2 (r, s2')] {true}) →
        (∀ r s1', Dead s1' = true → 𝒟[k1 (r, s1')] {true} = 0) →
        𝒟[(impl1 q).run s1 >>= k1] {true} ≤ 𝒟[(impl2 q).run s2 >>= k2] {true})
    (obs1 : α × St1 → ProbComp Bool)
    (obs2 : α × St2 → ProbComp Bool)
    (hDeadObs : ∀ a s1, Dead s1 = true → 𝒟[obs1 (a, s1)] {true} = 0)
    (hObs : ∀ a rem s1 s2, Dead s1 = false → Rel rem s1 s2 →
      𝒟[obs1 (a, s1)] {true} ≤ 𝒟[obs2 (a, s2)] {true})
    (oa : OracleComp (unifSpec + QSpec) α) (rem : ℕ)
    (hQb : IsQueryBoundP oa (fun q : ℕ ⊕ ι => isGameQuery q = true) rem)
    (s1 : St1) (s2 : St2) (hRel : Rel rem s1 s2) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St1 ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) + impl2
    𝒟[(simulateQ full1 oa).run s1 >>= obs1] {true} ≤
      𝒟[(simulateQ full2 oa).run s2 >>= obs2] {true} := by
  intro full1 full2
  induction oa using OracleComp.inductionOn generalizing rem s1 s2 with
  | pure a =>
    by_cases hD : Dead s1 = true
    · simp only [simulateQ_pure, StateT.run_pure, pure_bind, hDeadObs a s1 hD, zero_le]
    · simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hObs a rem s1 s2 (Bool.eq_false_iff.mpr hD) hRel
  | query_bind q mx ih =>
    by_cases hD : Dead s1 = true
    · rw [evalDist_simulateQ_eq_zero_of_dead_preserved Dead impl1 hDeadPres obs1 hDeadObs _ s1 hD]
      exact zero_le
    · have hDF : Dead s1 = false := Bool.eq_false_iff.mpr hD
      rw [isQueryBoundP_query_bind_iff] at hQb
      rcases q with uq | gq
      · rcases hQb with ⟨_, hCont⟩
        simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at hCont
        dsimp only [full1, full2]
        rw [simulateQ_run_query_inl, simulateQ_run_query_inl, bind_assoc, bind_assoc]
        exact evalDist_bind_true_mono_of_support _ _ _ (fun u _ => ih u rem (hCont u) s1 s2 hRel)
      · rcases hQb with ⟨hAbs | hPos, hCont⟩
        · exfalso; exact hAbs rfl
        · obtain ⟨rem', rfl⟩ : ∃ rem', rem = rem' + 1 := ⟨rem - 1, by omega⟩
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at hCont
          dsimp only [full1, full2]
          rw [simulateQ_run_query_inr, simulateQ_run_query_inr, bind_assoc, bind_assoc]
          exact hStep gq rem' s1 s2 hDF hRel
            (fun x => (simulateQ full1 (mx x.1)).run x.2 >>= obs1)
            (fun x => (simulateQ full2 (mx x.1)).run x.2 >>= obs2)
            (fun r s1' s2' _ hR => ih r rem' (hCont r) s1' s2' hR)
            (fun r s1' hD' =>
              evalDist_simulateQ_eq_zero_of_dead_preserved Dead impl1 hDeadPres obs1 hDeadObs (mx r)
                s1' hD')

/-! ## Case C (`DH3`) invariant and terminal win -/

def FgSlotReps.ofDh3 (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) : FgSlotReps P where
  Rep1 := FgPosRightRep P vSk
  Rep2 := FgPosLeftRep P uSk
  Rep3 := FgPosRightRep P vSk
  Rep4 := FgOptLeftRep P uSk
  len1 _ _ h := h.1
  len2 _ _ h := h.1
  len3 _ _ h := h.1
  len4 pos4? dh4? h d hd := by
    subst hd
    cases pos4? with
    | none => exact False.elim h
    | some _ => exact h.1
  eq1 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosRightRep P hP hvSk h1 h2
  eq2 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosLeftRep P hP huSk h1 h2
  eq3 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosRightRep P hP hvSk h1 h2
  eq4 _ _ _ _ h1 h2 := ddhEqOptPure_of_fgOptLeftRep P hP huSk h1 h2
  sec1 d hd := ⟨hd, Or.inl rfl⟩
  sec2 d hd := ⟨hd, Or.inl rfl⟩
  sec3 d hd := ⟨hd, Or.inl rfl⟩
  sec4 d? hd := by
    cases d? with
    | none => trivial
    | some d => exact ⟨hd d rfl, Or.inl rfl⟩

def spkTargetIsV {S : Setup} (bIdx : ℕ) (V : Bytes) (hst : KeyIndFgCutoffState S) : Bool :=
  hst.base.spkBundles.all (fun (k, b) => !(spkBundleFlatIdxVal S k == bIdx) || (b.spkPk == V))

theorem spkTargetIsV_map_revealed_base {S : Setup} (bIdx : ℕ) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst x2 : KeyIndFgCutoffState S)
    (hB : x2.base = { hst.base with spkBundles := hst.base.spkBundles.map (fun (idx, b) =>
        if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b)) }) :
    spkTargetIsV bIdx V x2 = spkTargetIsV bIdx V hst := by
  unfold spkTargetIsV
  rw [hB]; dsimp only
  rw [List.all_map]
  congr 1; funext ⟨idx, b⟩; dsimp only [Function.comp_apply]
  split_ifs <;> rfl

theorem spkTargetIsV_map_revealed {S : Setup} (bIdx : ℕ) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : KeyIndFgCutoffState S) :
    spkTargetIsV bIdx V
      { hst with base := { hst.base with spkBundles := hst.base.spkBundles.map (fun (idx, b) =>
          if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b)) } } =
      spkTargetIsV bIdx V hst :=
  spkTargetIsV_map_revealed_base bIdx V u j hst _ rfl

def deadDh3 {S : Setup} (P : Primitives) (sIdx bIdx : ℕ) (V : Bytes)
    (hst : KeyIndFgCutoffState S) : Bool :=
  spkTargetIsV bIdx V hst &&
  match hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | some s => P.pow8 s.peerSpkPk != P.pow8 V
  | none   => false

theorem badKeyIndFgDh3At_eq_false_of_deadDh3 {S : Setup} (P : Primitives)
    (maxLen sIdx bIdx : ℕ) (V : Bytes) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh3 P sIdx bIdx V hst = true) :
    badKeyIndFgDh3At P maxLen sIdx bIdx hst.base hst.advRoLog = false := by
  unfold deadDh3 spkTargetIsV at hDead
  rcases Bool.and_eq_true_iff.mp hDead with ⟨hAll, hSess⟩
  unfold badKeyIndFgDh3At
  cases hF1 : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s =>
    rw [hF1] at hSess
    cases hF2 : hst.base.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
    | none => rfl
    | some kb =>
      rcases kb with ⟨k, bEntry⟩
      dsimp only
      have hMem : (k, bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hF2
      have hIdx : (spkBundleFlatIdxVal S k == bIdx) = true :=
        List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) =>
          spkBundleFlatIdxVal S x.1 == bIdx) hF2
      have hItem := List.all_eq_true.mp hAll (k, bEntry) hMem
      simp only [hIdx, Bool.not_true, Bool.false_or, beq_iff_eq] at hItem
      rw [hItem]
      have hNe : (P.pow8 s.peerSpkPk == P.pow8 V) = false := by
        simpa [bne] using hSess
      simp [hNe]

theorem pqxdhKeyIndFgPreImpl_preserves_deadDh3 {S : Setup} (P : Primitives)
    (sIdx bIdx : ℕ) (hsIdx : sIdx < S.N_send_tot) (uSk vSk : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P q).run hst),
      deadDh3 P sIdx bIdx (P.x25519Base vSk) x.2 = true := by
  set V := P.x25519Base vSk
  have hUnchanged : ∀ x : KeyIndResponse × KeyIndFgCutoffState S,
      x.2.base.spkBundles = hst.base.spkBundles →
      x.2.base.sessions = hst.base.sessions →
      deadDh3 P sIdx bIdx V x.2 = true := by
    intro x hSpk hSess
    unfold deadDh3 spkTargetIsV at hDead ⊢
    rw [hSpk, hSess]; exact hDead
  unfold deadDh3 at hDead
  rcases Bool.and_eq_true_iff.mp hDead with ⟨hAll, hSessFind⟩
  cases hFS : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rw [hFS] at hSessFind; cases hSessFind
  | some s0 =>
    rw [hFS] at hSessFind
    have hFired : hasFiredSess S sIdx hst := by
      unfold hasFiredSess
      exact List.any_eq_true.mpr ⟨s0, List.mem_of_find?_eq_some hFS,
        List.find?_some (p := fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) hFS⟩
    intro x hx
    refine mem_support_pqxdhKeyIndFgPreImpl_elim false sIdx bIdx (some uSk) (some vSk) P q hst x hx
      (fun _ hS _ hSe => hUnchanged x hS hSe)
      (fun _ _ _ _ hB => hUnchanged x (by rw [hB]) (by rw [hB]))
      (fun _ _ _ _ _ hB => hUnchanged x (by rw [hB]) (by rw [hB]))
      (fun u j bEntry _ _ _ hTgt hB => ?_)
      (fun _ _ _ _ _ _ _ hB => hUnchanged x (by rw [hB]) (by rw [hB]))
      (fun s _ hAnyF hB => ?_)
      (fun _ _ _ _ hS hSe _ => hUnchanged x hS hSe)
      (fun f hSid _ hPeer _ _ hS _ hSe => ?_)
      (fun u j hB => ?_)
    · unfold deadDh3
      rw [hB]; dsimp only
      rw [hFS]
      simp only [hSessFind, Bool.and_true]
      unfold spkTargetIsV at hAll ⊢
      rw [hB]; dsimp only
      rw [List.all_cons, hAll, Bool.and_true]
      by_cases hSlot : (spkBundleFlatIdx S u j == bIdx) = true
      · have hPk := (hTgt vSk rfl hSlot).2
        have hSlotV : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = true := by
          simpa [spkBundleFlatIdxVal, spkBundleFlatIdx] using hSlot
        simp [hSlotV, hPk, V]
      · have hSlotV : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = false := by
          simpa [spkBundleFlatIdxVal, spkBundleFlatIdx] using hSlot
        simp [hSlotV]
    · by_cases hSlot : (initSessionSlotIdx s.sid == sIdx) = true
      · have hAny : hst.base.sessions.any (fun e => e.sid == s.sid) = true :=
          sessions_any_of_hasFiredSess sIdx hst hFired s.sid hSlot
            (by rw [beq_iff_eq.mp hSlot]; exact hsIdx)
        rw [hAnyF] at hAny; cases hAny
      · have hSlotF : (initSessionSlotIdx s.sid == sIdx) = false := Bool.eq_false_iff.mpr hSlot
        unfold deadDh3
        have hSpkEq : spkTargetIsV bIdx V x.2 = spkTargetIsV bIdx V hst := by
          unfold spkTargetIsV; rw [hB]
        rw [hSpkEq, hB]
        simp [hAll, hSlotF, hFS, hSessFind]
    · unfold deadDh3
      have hSpkEq : spkTargetIsV bIdx V x.2 = spkTargetIsV bIdx V hst := by
        unfold spkTargetIsV; rw [hS]
      rw [hSpkEq, hSe]
      have hPred : (fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) ∘ f =
          (fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) := by
        funext s; dsimp; rw [hSid s]
      rw [List.find?_map, hPred, hFS]
      dsimp only [Option.map_some]
      rw [hPeer s0]
      exact Bool.and_eq_true_iff.mpr ⟨hAll, hSessFind⟩
    · unfold deadDh3
      rw [spkTargetIsV_map_revealed_base bIdx V u j hst x.2 hB, hB]
      dsimp only
      rw [hFS]
      exact Bool.and_eq_true_iff.mpr ⟨hAll, hSessFind⟩

noncomputable def spkTargetRevealed {S : Setup} (bIdx : ℕ) (hst : KeyIndFgCutoffState S) : Bool :=
  @decide (hasFiredSpk S bIdx hst) (Classical.propDecidable _) &&
  hst.base.spkBundles.all (fun (k, b) => !(spkBundleFlatIdxVal S k == bIdx) || b.revealed)

theorem badKeyIndFgDh3At_eq_false_of_spkTargetRevealed {S : Setup} (P : Primitives)
    (maxLen sIdx bIdx : ℕ) (hst : KeyIndFgCutoffState S)
    (hRev : spkTargetRevealed bIdx hst = true) :
    badKeyIndFgDh3At P maxLen sIdx bIdx hst.base hst.advRoLog = false := by
  unfold spkTargetRevealed at hRev
  rcases Bool.and_eq_true_iff.mp hRev with ⟨_, hAll⟩
  unfold badKeyIndFgDh3At
  cases hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s =>
    cases hF2 : hst.base.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
    | none => rfl
    | some kb =>
      rcases kb with ⟨k, bEntry⟩
      dsimp only
      have hMem : (k, bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hF2
      have hIdx : (spkBundleFlatIdxVal S k == bIdx) = true :=
        List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) =>
          spkBundleFlatIdxVal S x.1 == bIdx) hF2
      have hItem := List.all_eq_true.mp hAll (k, bEntry) hMem
      simp only [hIdx, Bool.not_true, Bool.false_or] at hItem
      simp [hItem]

theorem badKeyIndFgDh1At_eq_false_of_spkTargetRevealed {S : Setup} (P : Primitives)
    (maxLen uIdx bIdx : ℕ) (hst : KeyIndFgCutoffState S)
    (hRev : spkTargetRevealed bIdx hst = true) :
    badKeyIndFgDh1At P maxLen uIdx bIdx hst.base hst.advRoLog = false := by
  unfold spkTargetRevealed at hRev
  rcases Bool.and_eq_true_iff.mp hRev with ⟨_, hAll⟩
  unfold badKeyIndFgDh1At
  cases hst.base.principals.find? (fun (u, _) => u == uIdx) with
  | none => rfl
  | some up =>
    rcases up with ⟨_, uEntry⟩
    cases hF2 : hst.base.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
    | none => rfl
    | some kb =>
      rcases kb with ⟨k, bEntry⟩
      dsimp only
      have hMem : (k, bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hF2
      have hIdx : (spkBundleFlatIdxVal S k == bIdx) = true :=
        List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) =>
          spkBundleFlatIdxVal S x.1 == bIdx) hF2
      have hItem := List.all_eq_true.mp hAll (k, bEntry) hMem
      simp only [hIdx, Bool.not_true, Bool.false_or] at hItem
      simp [hItem]

end Proofs.SignalPqxdh.Security.FgGapDh

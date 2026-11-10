/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhB
import VCVio.EvalDist.Monad.Basic

/-!
# Fiedler–Günther `KeyInd` `GapDH` Reduction, Case B (`DH2 = CDH(ek_U*, ik_V*)`)

Embeds the `GapDH` challenge `(U, V)` as the ephemeral key of initiator slot `sIdx` and the
identity DH key of principal `kIdx`, and characterizes the simulator under `gapDhFullImpl`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh.Ik

open Proofs.SignalPqxdh.Security.FgGapDh

open _root_.SignalPqxdh.Security.FgGapDh.Ik
export _root_.SignalPqxdh.Security.FgGapDh.Ik (
  noSpkIdx fgKeyIndStepIk extractCdh2FromAdvRoLog
  fgKeyIndGapDhRunAtIk fgKeyIndGapDhAdvAtIk
)

theorem spkBundleFlatIdx_lt (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) :
    spkBundleFlatIdx S u j < S.N_spk_tot := by
  unfold spkBundleFlatIdx Setup.N_spk_tot
  have hu : u.val + 1 ≤ S.N_id := u.isLt
  have hj : j.val < S.N_recv := j.isLt
  calc u.val * S.N_recv + j.val
      < u.val * S.N_recv + S.N_recv := Nat.add_lt_add_left hj _
    _ = (u.val + 1) * S.N_recv := by ring
    _ ≤ S.N_id * S.N_recv := Nat.mul_le_mul_right S.N_recv hu

theorem spkBundleFlatIdx_ne_noSpkIdx (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) :
    (spkBundleFlatIdx S u j == noSpkIdx S) = false := by
  have := spkBundleFlatIdx_lt S u j
  unfold noSpkIdx
  simp only [beq_eq_false_iff_ne, ne_eq]
  omega

noncomputable def fgKeyIndStepPureIk (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (targetIdx targetPrinIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    ProbComp (KeyIndResponse × FgKeyIndSimState S) :=
  match q with
  | .initPrin u =>
    fgKeyIndStepPure P ddh true targetPrinIdx (noSpkIdx S) S maxLen V V (.initPrin u) st
  | q => fgKeyIndStepPure P ddh false targetIdx (noSpkIdx S) S maxLen U V q st

@[simp]
theorem simulateQ_gapDhFullImpl_fgKeyIndStepIk (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndStepIk targetIdx targetPrinIdx S maxLen U V q st) =
      fgKeyIndStepPureIk P ddh targetIdx targetPrinIdx S maxLen U V q st := by
  cases q
  case initPrin u =>
    simp only [fgKeyIndStepIk, fgKeyIndStepPureIk]
    exact simulateQ_gapDhFullImpl_fgKeyIndStep P ddh true targetPrinIdx
      (noSpkIdx S) S maxLen V V _ st
  all_goals
    simp only [fgKeyIndStepIk, fgKeyIndStepPureIk]
    exact simulateQ_gapDhFullImpl_fgKeyIndStep P ddh false targetIdx (noSpkIdx S) S maxLen U V _ st

/-- Pure `QueryImpl` induced by simulating `fgKeyIndStepIk` under `gapDhFullImpl P ddh`. -/
noncomputable def fgKeyIndSimImplIk (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (targetIdx targetPrinIdx : ℕ) (S : Setup) (maxLen : ℕ) (U V : Bytes) :
    QueryImpl (keyIndSpec S) (StateT (FgKeyIndSimState S) ProbComp) :=
  fun gq => StateT.mk (fun st =>
    simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndStepIk targetIdx targetPrinIdx S maxLen U V gq st))

theorem fgKeyIndSimImplIk_run (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (targetIdx targetPrinIdx : ℕ) (S : Setup) (maxLen : ℕ) (U V : Bytes)
    (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    (fgKeyIndSimImplIk P ddh targetIdx targetPrinIdx S maxLen U V q).run st =
      fgKeyIndStepPureIk P ddh targetIdx targetPrinIdx S maxLen U V q st := by
  unfold fgKeyIndSimImplIk
  simp

def pureExtractCdh2FromAdvRoLog (ddh : Bytes → Bytes → Bytes → Bool)
    (maxLen : ℕ) (U V : Bytes) (advRoLog : List Bytes) : Bytes :=
  let cands := (advRoLog.take maxLen).map extractDh2
  match cands.find? (fun z => ddh U V z) with
  | some z => z
  | none   => List.replicate 32 0

@[simp]
theorem simulateQ_gapDhFullImpl_extractCdh2FromAdvRoLog (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ) (U V : Bytes) (advRoLog : List Bytes) :
    simulateQ (gapDhFullImpl P ddh) (extractCdh2FromAdvRoLog maxLen U V advRoLog) =
      pure (pureExtractCdh2FromAdvRoLog ddh maxLen U V advRoLog) := by
  unfold extractCdh2FromAdvRoLog
  dsimp only [pureExtractCdh2FromAdvRoLog]
  rw [simulateQ_bind, simulateQ_gapDhFullImpl_findMGdh P ddh
    (fun z => ddhGdhQ U V z) (fun z => ddh U V z)
    (fun z => simulateQ_gapDhFullImpl_ddhGdhQ P ddh U V z), pure_bind]
  cases ((advRoLog.take maxLen).map extractDh2).find? (fun z => ddh U V z) <;> simp

theorem pureExtractCdh2FromAdvRoLog_wins_of_mem
    (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (maxLen : ℕ) (u v : Bytes) (advRoLog : List Bytes)
    (h_mem : ∃ sec ∈ advRoLog.take maxLen, extractDh2 sec = P.x25519 u (P.x25519Base v)) :
    (P.pow8 (pureExtractCdh2FromAdvRoLog P.isValidDhTriple maxLen
      (P.x25519Base u) (P.x25519Base v) advRoLog) ==
      P.pow8 (P.x25519 u (P.x25519Base v))) = true := by
  dsimp only [pureExtractCdh2FromAdvRoLog]
  set cands := (advRoLog.take maxLen).map extractDh2
  rcases h_mem with ⟨sec, hsec_mem, hsec_eq⟩
  have hcands_mem : P.x25519 u (P.x25519Base v) ∈ cands := by
    rw [← hsec_eq]
    exact List.mem_map_of_mem hsec_mem
  have hddh_target : P.isValidDhTriple (P.x25519Base u) (P.x25519Base v)
      (P.x25519 u (P.x25519Base v)) = true :=
    (hWF.ddh_consistent u v (P.x25519 u (P.x25519Base v))).mpr rfl
  have hfind_some :
      (cands.find? (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z)).isSome =
        true :=
    List.find?_isSome.mpr ⟨P.x25519 u (P.x25519Base v), hcands_mem, hddh_target⟩
  rcases Option.isSome_iff_exists.mp hfind_some with ⟨Z, hZ⟩
  have hZ_ddh : P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) Z = true :=
    List.find?_some hZ
  have hZ_pow : P.pow8 Z = P.pow8 (P.x25519 u (P.x25519Base v)) :=
    (hWF.ddh_consistent u v Z).mp hZ_ddh
  rw [hZ]
  simp [hZ_pow]

theorem simulateQ_gapDhFullImpl_fgKeyIndGapDhRunAtIk
    (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (U V : Bytes) :
    simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndGapDhRunAtIk targetIdx targetPrinIdx S b A U V) =
    (do
      let secb ← $ᵗ Bool
      let initSt := FgKeyIndSimState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyIndSimState S) ProbComp) +
        fgKeyIndSimImplIk P ddh targetIdx targetPrinIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return pureExtractCdh2FromAdvRoLog ddh b.q_total U V finalSt.advRoLog) := by
  unfold fgKeyIndGapDhRunAtIk
  rw [simulateQ_bind, simulateQ_gapDhFullImpl_unifGdh]
  congr 1
  ext secb
  rw [simulateQ_bind,
      simulateQ_gapDhFullImpl_runWithGdhStep P ddh
        (fgKeyIndStepIk targetIdx targetPrinIdx S b.q_total U V)
        (fgKeyIndSimImplIk P ddh targetIdx targetPrinIdx S b.q_total U V)
        (fun _ _ => rfl)]
  congr 1
  ext res
  exact simulateQ_gapDhFullImpl_extractCdh2FromAdvRoLog P ddh b.q_total U V res.2.advRoLog

theorem gapDhExp_fgKeyIndGapDhAdvAtIk_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    gapDhExp P ddh pow8 (fgKeyIndGapDhAdvAtIk targetIdx targetPrinIdx S b A) =
    (do
      let u ← sampleScalar32
      let v ← sampleScalar32
      let U := P.x25519Base u
      let V := P.x25519Base v
      let secb ← $ᵗ Bool
      let initSt := FgKeyIndSimState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyIndSimState S) ProbComp) +
        fgKeyIndSimImplIk P ddh targetIdx targetPrinIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return (pow8 (pureExtractCdh2FromAdvRoLog ddh b.q_total U V finalSt.advRoLog) ==
        pow8 (P.x25519 u V))) := by
  unfold gapDhExp fgKeyIndGapDhAdvAtIk
  dsimp only [gapDhFullImpl, gapDhDdhImpl]
  congr 1; ext u
  congr 1; ext v
  change (simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndGapDhRunAtIk targetIdx targetPrinIdx S b A (P.x25519Base u) (P.x25519Base v)) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  rw [simulateQ_gapDhFullImpl_fgKeyIndGapDhRunAtIk]
  simp only [bind_assoc, pure_bind]

end Proofs.SignalPqxdh.Security.FgGapDh.Ik

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyPre
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC5
import VCVio.EvalDist.Monad.Basic

/-!
# Pure step counterparts and unfolding for the one-key `Auth` `GapDhWithSign` simulator

**Checked by Lean.** Defines `ProbComp` counterparts of the one-key `Auth` simulator steps under
`gapDhWithSignFullImpl` and unfolds `gapDhWithSignExp` at `fgAuth1KeyGapDhAdvAt` into a pure
stateful simulation followed by `pureExtractCdhFromAuthSimState`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh1Key

namespace Proofs.SignalPqxdh.Security

noncomputable def fgAuthInitPrin1KeyPure {S : Setup} (P : Primitives)
    (prinFlag : Bool) (prinIdx : ℕ) (Up : Bytes)
    (u : Fin S.N_id) (st : FgAuth1KeySimState S) :
    ProbComp (AuthResponse × FgAuth1KeySimState S) := do
  if st.sim.base.principals.any (fun (idx, _) => idx == u.val) then
    return (.noneResp, st)
  let isTargetPrin : Bool := prinFlag && (u.val == prinIdx)
  let sk0 ← sampleScalar32
  let pk0 := P.x25519Base sk0
  let sec0 := if isTargetPrin then [] else sk0
  let ikPk := if isTargetPrin then Up else pk0
  let entry : PrincipalEntry := {
    secIKA0    := sec0
    ikAPk      := ikPk
    secIKAsign := sec0
    ikSignPk   := ikPk
    corrupted  := false
  }
  let base' := { st.sim.base with principals := (u.val, entry) :: st.sim.base.principals }
  return (.initPrinResp ikPk ikPk, { st with sim := { st.sim with base := base' } })

noncomputable def fgAuthGenSPK1KeyPure (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (prinFlag : Bool) (prinIdx : ℕ)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgAuth1KeySimState S) :
    ProbComp (AuthResponse × FgAuth1KeySimState S) := do
  if prinFlag && (u.val == prinIdx) then
    if st.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, st)
    let some (_, uEntry) := st.sim.base.principals.find? (fun (idx, _) => idx == u.val)
      | return (.noneResp, st)
    if st.sigBudget == 0 then
      return (.noneResp, st)
    let isTargetSpk : Bool := FgGapDh.spkBundleFlatIdx S u j == targetSpkIdx
    let spkSkRaw ← sampleScalar32
    let spkPkRaw := P.x25519Base spkSkRaw
    let spkSk := if isTargetSpk then [] else spkSkRaw
    let spkPk := if isTargetSpk then V else spkPkRaw
    let rSpk ← sampleRandom64
    let spkSig := P.sigSign uSk (encodeEC spkPk) rSpk
    let seedKem ← sampleRandom64
    let (pqspkPk, pqspkSk) := P.kemKeyGen seedKem
    let rPq ← sampleRandom64
    let pqspkSig := P.sigSign uSk (encodeKEM pqspkPk) rPq
    let bEntry : SpkBundleEntry := {
      spkSk := spkSk, spkPk := spkPk, spkSig := spkSig
      pqspkSk := pqspkSk, pqspkPk := pqspkPk, pqspkSig := pqspkSig }
    let base' :=
      { st.sim.base with spkBundles := ((u.val, j.val), bEntry) :: st.sim.base.spkBundles }
    let bundleOut : PreKeyBundleInput := {
      ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig := spkSig
      opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig := pqspkSig }
    return (.bundleResp bundleOut,
      { sim := { st.sim with base := base' }, sigBudget := st.sigBudget - 1 })
  else
    let (resp, sim') ← AuthDh3.fgAuthStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V
      (.genSPK u j) st.sim
    return (resp, { st with sim := sim' })

noncomputable def fgAuth1KeyStepPure (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : AuthQuery S)
    (st : FgAuth1KeySimState S) :
    ProbComp (AuthResponse × FgAuth1KeySimState S) :=
  match q with
  | .initPrin u => fgAuthInitPrin1KeyPure P useDh1 targetIdx U u st
  | .genSPK u j =>
    fgAuthGenSPK1KeyPure P uSk ddh useDh1 targetIdx useDh1 targetIdx targetSpkIdx S maxLen U V
      u j st
  | q => do
    let (resp, sim') ← AuthDh3.fgAuthStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st.sim
    return (resp, { st with sim := sim' })

noncomputable def fgAuth1KeyStepHaltPure (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : AuthQuery S)
    (st : FgAuth1KeySimState S) :
    ProbComp (AuthResponse × FgAuth1KeySimState S) :=
  if useDh1 && isTargetPrinCorrupted targetIdx st.sim then
    pure (.noneResp, st)
  else
    fgAuth1KeyStepPure P uSk ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st

/-- Pure `StateT` query implementation of the halting one-key `Auth` simulator. -/
noncomputable def fgAuth1KeySimImpl (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) :
    QueryImpl (authSpec S) (StateT (FgAuth1KeySimState S) ProbComp) :=
  fun q => StateT.mk (fgAuth1KeyStepHaltPure P uSk ddh useDh1 targetIdx targetSpkIdx S maxLen U V q)

theorem fgAuth1KeyStepHaltPure_false (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    fgAuth1KeyStepHaltPure P uSk ddh false targetIdx targetSpkIdx S maxLen U V q st =
      fgAuth1KeyStepPure P uSk ddh false targetIdx targetSpkIdx S maxLen U V q st := by
  simp [fgAuth1KeyStepHaltPure]

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_fgAuthInitPrin1KeyGdh {S : Setup}
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (prinFlag : Bool) (prinIdx : ℕ) (Up : Bytes) (u : Fin S.N_id)
    (st : FgAuth1KeySimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgAuthInitPrin1KeyGdh prinFlag prinIdx Up u st) =
      fgAuthInitPrin1KeyPure P prinFlag prinIdx Up u st := by
  unfold fgAuthInitPrin1KeyGdh fgAuthInitPrin1KeyPure
  by_cases hAny : (st.sim.base.principals.any (fun (idx, _) => idx == u.val)) = true
  · simp [hAny]
  · simp [hAny]

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_fgAuthGenSPK1KeyGdh
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (prinFlag : Bool) (prinIdx : ℕ) (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgAuth1KeySimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgAuthGenSPK1KeyGdh prinFlag prinIdx useDh1 targetIdx targetSpkIdx S maxLen U V u j st) =
      fgAuthGenSPK1KeyPure P uSk ddh prinFlag prinIdx useDh1 targetIdx targetSpkIdx S maxLen U V
        u j st := by
  unfold fgAuthGenSPK1KeyGdh fgAuthGenSPK1KeyPure
  by_cases hPrin : (prinFlag && (u.val == prinIdx)) = true
  · simp only [hPrin, ↓reduceIte]
    by_cases hAny : (st.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp [hAny]
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte]
      cases st.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        by_cases hZero : (st.sigBudget == 0) = true
        · simp [hZero]
        · simp only [hZero, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
            simulateQ_gapDhWithSignFullImpl_unifGdhSign,
            simulateQ_gapDhWithSignFullImpl_primGdhSignQ_x25519Base,
            simulateQ_gapDhWithSignFullImpl_sigChalQ,
            simulateQ_gapDhWithSignFullImpl_primGdhSignQ_kemKeyGen,
            simulateQ_pure, pure_bind, bind_assoc]
  · simp only [hPrin, Bool.false_eq_true, ↓reduceIte]
    unfold liftAuthSimStep1Key
    rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      AuthDh3.simulateQ_gapDhFullImpl_fgAuthStep]
    simp

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_fgAuth1KeyStep
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgAuth1KeyStep useDh1 targetIdx targetSpkIdx S maxLen U V q st) =
      fgAuth1KeyStepPure P uSk ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st := by
  cases q with
  | initPrin u =>
    exact simulateQ_gapDhWithSignFullImpl_fgAuthInitPrin1KeyGdh P uSk ddh _ _ _ u st
  | genSPK u j =>
    exact simulateQ_gapDhWithSignFullImpl_fgAuthGenSPK1KeyGdh P uSk ddh _ _ _ _ _ S maxLen U V
      u j st
  | _ =>
    simp only [fgAuth1KeyStep, fgAuth1KeyStepPure, liftAuthSimStep1Key, simulateQ_bind,
      simulateQ_gapDhWithSignFullImpl_liftGdhToSign, AuthDh3.simulateQ_gapDhFullImpl_fgAuthStep,
      simulateQ_pure]

@[simp]
theorem simulateQ_gapDhWithSignFullImpl_fgAuth1KeyStepHalt
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V q st) =
      fgAuth1KeyStepHaltPure P uSk ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st := by
  unfold fgAuth1KeyStepHalt fgAuth1KeyStepHaltPure
  split_ifs
  · simp
  · exact simulateQ_gapDhWithSignFullImpl_fgAuth1KeyStep P uSk ddh useDh1 targetIdx
      targetSpkIdx S maxLen U V q st

/-- Unfolds `gapDhWithSignExp` at `fgAuth1KeyGapDhAdvAt` into a pure simulation under
`fgAuth1KeySimImpl`. -/
theorem gapDhWithSignExp_fgAuth1KeyGapDhAdvAt_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    gapDhWithSignExp P ddh pow8 (fgAuth1KeyGapDhAdvAt useDh1 targetIdx targetSpkIdx S b A) =
    (do
      let u ← sampleScalar32
      let v ← sampleScalar32
      let U := P.x25519Base u
      let V := P.x25519Base v
      let secb ← $ᵗ Bool
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgAuth1KeySimState S) ProbComp) +
        fgAuth1KeySimImpl P u ddh useDh1 targetIdx targetSpkIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run (FgAuth1KeySimState.empty S secb)
      return (pow8 (pureExtractCdhFromAuthSimState S P ddh useDh1 b.q_total U V finalSt.sim) ==
        pow8 (P.x25519 u V))) := by
  unfold gapDhWithSignExp fgAuth1KeyGapDhAdvAt
  congr 1; funext u
  congr 1; funext v
  change (simulateQ (gapDhWithSignFullImpl P u ddh)
      (fgAuth1KeyGapDhRunAt useDh1 targetIdx targetSpkIdx S b A
        (P.x25519Base u) (P.x25519Base v)) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  unfold fgAuth1KeyGapDhRunAt
  rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign, bind_assoc]
  congr 1; funext secb
  rw [simulateQ_bind,
    simulateQ_gapDhWithSignFullImpl_runWithGdhSignStep P u ddh _ _
      (simulateQ_gapDhWithSignFullImpl_fgAuth1KeyStepHalt P u ddh useDh1 targetIdx targetSpkIdx
        S b.q_total (P.x25519Base u) (P.x25519Base v)),
    bind_assoc]
  congr 1; funext ⟨_, finalSt⟩
  rw [simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
    simulateQ_gapDhFullImpl_extractCdhFromAuthSimState, pure_bind]

end Proofs.SignalPqxdh.Security

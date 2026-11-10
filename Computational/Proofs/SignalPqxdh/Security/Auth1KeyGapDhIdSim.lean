/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Auth1KeyStatements
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeyGapDh
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC3b

/-!
# One-key `Auth` `GapDhWithSign` simulator (`G3 → G3.5`)

**Checked by Lean.** Defines the one-key `.g3` reference simulation `runAuthFgLatchedSim1Key` and
the shallow `GapDhWithSign` reduction adversaries `fgAuth1KeyGapDhAdvAt` and `fgAuth1KeyGapDhAdv4`
for Case A (`DH1`, signing target bundles via `sigChalQ` under `sigBudget`) and Case C (`DH3`).
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

/-! ## Reference `.g3` simulation -/

def pqxdhAuthFgImpl1Key (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthFgCutoffState S) ProbComp)
  | .initPrin u => liftAuthFgBase (pqxdhAuthImpl1Key S P (.initPrin u))
  | q => pqxdhAuthFgImpl S P q

def pqxdhAuthFgLatchedImpl1Key (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthFgCutoffState S) ProbComp)
  | .initPrin u => liftAuthFgBase (pqxdhAuthImpl1Key S P (.initPrin u))
  | q => pqxdhAuthFgLatchedImpl S P q

/-- One-key reference `.g3` `Auth` simulation with sticky `latchedDh1`. -/
noncomputable def runAuthFgLatchedSim1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    ProbComp (Bool × Bool × AuthFgCutoffState S) := do
  let secb ← $ᵗ Bool
  let initSt := AuthFgCutoffState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgLatchedImpl1Key S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)

theorem pqxdhAuthFgImpl1Key_initPrin (S : Setup) (P : Primitives) (u : Fin S.N_id) :
    pqxdhAuthFgImpl1Key S P (.initPrin u) =
      liftAuthFgBase (pqxdhAuthImpl1Key S P (.initPrin u)) := rfl

theorem pqxdhAuthFgImpl1Key_of_not_initPrin (S : Setup) (P : Primitives) (q : AuthQuery S)
    (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhAuthFgImpl1Key S P q = pqxdhAuthFgImpl S P q := by
  cases q <;> first | rfl | exact absurd rfl (hq _)

theorem pqxdhAuthFgLatchedImpl1Key_initPrin (S : Setup) (P : Primitives) (u : Fin S.N_id) :
    pqxdhAuthFgLatchedImpl1Key S P (.initPrin u) =
      liftAuthFgBase (pqxdhAuthImpl1Key S P (.initPrin u)) := rfl

theorem pqxdhAuthFgLatchedImpl1Key_of_not_initPrin (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hq : ∀ u, q ≠ .initPrin u) :
    pqxdhAuthFgLatchedImpl1Key S P q = pqxdhAuthFgLatchedImpl S P q := by
  cases q <;> first | rfl | exact absurd rfl (hq _)

/-! ## Shallow `GapDhWithSign` reduction -/

/-- Simulator state pairing `FgAuthSimState S` with the remaining target-bundle signing budget. -/
structure FgAuth1KeySimState (S : Setup) where
  sim       : FgAuthSimState S
  sigBudget : ℕ

def FgAuth1KeySimState.empty (S : Setup) (secb : Bool) : FgAuth1KeySimState S :=
  { sim := FgAuthSimState.empty S secb, sigBudget := min S.N_spk_tot S.N_recv }

def liftAuthSimStep1Key {S : Setup}
    (f : FgAuthSimState S → OracleComp GdhSimSpec (AuthResponse × FgAuthSimState S))
    (st : FgAuth1KeySimState S) :
    OracleComp GdhSignSimSpec (AuthResponse × FgAuth1KeySimState S) := do
  let (resp, sim') ← liftGdhToSign (f st.sim)
  return (resp, { st with sim := sim' })

def fgAuthInitPrin1KeyGdh {S : Setup} (prinFlag : Bool) (prinIdx : ℕ) (Up : Bytes)
    (u : Fin S.N_id) (st : FgAuth1KeySimState S) :
    OracleComp GdhSignSimSpec (AuthResponse × FgAuth1KeySimState S) := do
  if st.sim.base.principals.any (fun (idx, _) => idx == u.val) then
    return (.noneResp, st)
  let isTargetPrin : Bool := prinFlag && (u.val == prinIdx)
  let sk0 ← unifGdhSign sampleScalar32
  let pk0 ← primGdhSignQ (.x25519Base sk0)
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

def fgAuthGenSPK1KeyGdh (prinFlag : Bool) (prinIdx : ℕ)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgAuth1KeySimState S) :
    OracleComp GdhSignSimSpec (AuthResponse × FgAuth1KeySimState S) := do
  if prinFlag && (u.val == prinIdx) then
    if st.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, st)
    let some (_, uEntry) := st.sim.base.principals.find? (fun (idx, _) => idx == u.val)
      | return (.noneResp, st)
    if st.sigBudget == 0 then
      return (.noneResp, st)
    let isTargetSpk : Bool := FgGapDh.spkBundleFlatIdx S u j == targetSpkIdx
    let spkSkRaw ← unifGdhSign sampleScalar32
    let spkPkRaw ← primGdhSignQ (.x25519Base spkSkRaw)
    let spkSk := if isTargetSpk then [] else spkSkRaw
    let spkPk := if isTargetSpk then V else spkPkRaw
    let spkSig ← sigChalQ (encodeEC spkPk)
    let seedKem ← unifGdhSign sampleRandom64
    let (pqspkPk, pqspkSk) ← primGdhSignQ (.kemKeyGen seedKem)
    let pqspkSig ← sigChalQ (encodeKEM pqspkPk)
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
    liftAuthSimStep1Key (fgAuthStep useDh1 targetIdx targetSpkIdx S maxLen U V (.genSPK u j)) st

/-- One-key `Auth` per-query simulator step for Case A (`useDh1 = true`) and Case C
(`useDh1 = false`). -/
def fgAuth1KeyStep (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    OracleComp GdhSignSimSpec (AuthResponse × FgAuth1KeySimState S) :=
  match q with
  | .initPrin u => fgAuthInitPrin1KeyGdh useDh1 targetIdx U u st
  | .genSPK u j =>
    fgAuthGenSPK1KeyGdh useDh1 targetIdx useDh1 targetIdx targetSpkIdx S maxLen U V u j st
  | q => liftAuthSimStep1Key (fgAuthStep useDh1 targetIdx targetSpkIdx S maxLen U V q) st

def fgAuth1KeyStepHalt (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes)
    (q : AuthQuery S) (st : FgAuth1KeySimState S) :
    OracleComp GdhSignSimSpec (AuthResponse × FgAuth1KeySimState S) :=
  if useDh1 && isTargetPrinCorrupted targetIdx st.sim then
    return (.noneResp, st)
  else
    fgAuth1KeyStep useDh1 targetIdx targetSpkIdx S maxLen U V q st

def fgAuth1KeyGapDhRunAt (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b)
    (U V : Bytes) : OracleComp GdhSignSimSpec Bytes := do
  let secb ← unifGdhSign ($ᵗ Bool)
  let initSt := FgAuth1KeySimState.empty S secb
  let (_, finalSt) ← runWithGdhSignStep
    (fgAuth1KeyStepHalt useDh1 targetIdx targetSpkIdx S b.q_total U V) A.1.run initSt
  liftGdhToSign (extractCdhFromAuthSimState S useDh1 b.q_total U V finalSt.sim)

/-- Per-index one-key `Auth` `GapDhWithSign` reduction adversary. -/
def fgAuth1KeyGapDhAdvAt (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) : GapDhWithSignAdv where
  run U V := fgAuth1KeyGapDhRunAt useDh1 targetIdx targetSpkIdx S b A U V
  q_ddh  := authGdhQueryBudget S b
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := gdhPrimQueryBudget S b

/-- Combined Case A + Case C one-key `Auth` `GapDhWithSign` mixture reduction (`G3 → G3.5`). -/
def fgAuth1KeyGapDhAdv4 (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : GapDhWithSignAdv where
  run U V := do
    let (flatIdx, bIdx) ← unifGdhSign (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot)
    if flatIdx < S.N_id then
      fgAuth1KeyGapDhRunAt true flatIdx bIdx S b A U V
    else
      fgAuth1KeyGapDhRunAt false (flatIdx - S.N_id) bIdx S b A U V
  q_ddh  := authGdhQueryBudget S b
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := gdhPrimQueryBudget S b

end Proofs.SignalPqxdh.Security

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndGapDh
public import Computational.Specifications.Assumptions.KeyInd1KeyRo

/-!
# One-key `KeyInd` `GapDhWithSign` simulator

**Checked by Lean.** Shallow oracle-computation simulator (`fgKeyInd1KeyGapDhAdv4`) adapting the
four-leg Fiedler–Günther `KeyInd` reduction to the one-key random-oracle game
`pqxdhKeyIndImpl1KeyRo` against `GapDhWithSign`. Target identity keys embed the first challenge
point `U` and sign pre-key bundles via the challenger signing oracle, while DDH queries maintain
random-oracle consistency across `DH1`–`DH4`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp

namespace FgGapDh1Key

open FgGapDh FgGapDh.Ik FgGapDh.Opk

abbrev GdhSignSimSpec : OracleSpec.{0, 0} ((ℕ ⊕ PrimQuery) ⊕ (SigQuery ⊕ DdhQuery)) :=
  PrimBaseSpec + sigAndDdhSpec

def liftGdhToSign {α : Type} (mx : OracleComp GdhSimSpec α) :
    OracleComp GdhSignSimSpec α :=
  OracleComp.construct
    (C := fun _ => OracleComp GdhSignSimSpec α)
    pure
    (fun q _ r =>
      match q with
      | Sum.inl bq =>
        liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>= r
      | Sum.inr dq =>
        liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>= r)
    mx

def unifGdhSign {α : Type} (mx : ProbComp α) : OracleComp GdhSignSimSpec α :=
  liftGdhToSign (unifGdh mx)

def primGdhSignQ (op : PrimQuery) : OracleComp GdhSignSimSpec (primSpec.Range op) :=
  query (spec := GdhSignSimSpec) (Sum.inl (Sum.inr op))

def sigChalQ (msg : Bytes) : OracleComp GdhSignSimSpec Bytes :=
  query (spec := GdhSignSimSpec) (Sum.inr (Sum.inl (.sign msg)))

def ddhGdhSignQ (X Y Z : Bytes) : OracleComp GdhSignSimSpec Bool :=
  query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr (X, Y, Z)))

/-- Simulator state pairing `FgKeyIndSimState S` with the remaining bundle-signing budget. -/
structure FgKeyInd1KeySimState (S : Setup) where
  sim       : FgKeyIndSimState S
  sigBudget : ℕ

def FgKeyInd1KeySimState.empty (S : Setup) (secb : Bool) : FgKeyInd1KeySimState S :=
  { sim := FgKeyIndSimState.empty S secb, sigBudget := min S.N_spk_tot S.N_recv }

def liftSimStep1Key {S : Setup}
    (f : FgKeyIndSimState S → OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S))
    (st : FgKeyInd1KeySimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeySimState S) := do
  let (resp, sim') ← liftGdhToSign (f st.sim)
  return (resp, { st with sim := sim' })

/-- One-key `.initPrin` handler, embedding `Up` on the target principal when `prinFlag` holds. -/
def fgInitPrin1KeyGdh {S : Setup} (prinFlag : Bool) (prinIdx : ℕ) (Up : Bytes)
    (u : Fin S.N_id) (st : FgKeyInd1KeySimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeySimState S) := do
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

/-- One-key `.genSPK` handler, signing target-principal bundles via `sigChalQ` within `sigBudget`. -/
def fgGenSPK1KeyGdh (prinFlag : Bool) (prinIdx : ℕ)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgKeyInd1KeySimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeySimState S) := do
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
      spkSk    := spkSk
      spkPk    := spkPk
      spkSig   := spkSig
      pqspkSk  := pqspkSk
      pqspkPk  := pqspkPk
      pqspkSig := pqspkSig
    }
    let base' :=
      { st.sim.base with spkBundles := ((u.val, j.val), bEntry) :: st.sim.base.spkBundles }
    let bundleOut : PreKeyBundleInput := {
      ikB      := uEntry.ikAPk
      spkId    := UInt32.ofNat j.val
      spkB     := spkPk
      spkSig   := spkSig
      opkB?    := none
      pqspkId  := UInt32.ofNat j.val
      pqspkB   := pqspkPk
      pqspkSig := pqspkSig
    }
    return (.bundleResp bundleOut,
      { sim := { st.sim with base := base' }, sigBudget := st.sigBudget - 1 })
  else
    liftSimStep1Key (fgKeyIndStep useDh1 targetIdx targetSpkIdx S maxLen U V (.genSPK u j)) st

/-- Per-query step for `Case A` (`DH1`, `useDh1 = true`) and `Case C` (`DH3`, `useDh1 = false`). -/
def fgKeyInd1KeyStep (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeySimState S) :=
  match q with
  | .initPrin u => fgInitPrin1KeyGdh useDh1 targetIdx U u st
  | .genSPK u j => fgGenSPK1KeyGdh useDh1 targetIdx useDh1 targetIdx targetSpkIdx S maxLen U V u j st
  | q => liftSimStep1Key (fgKeyIndStep useDh1 targetIdx targetSpkIdx S maxLen U V q) st

/-- Per-query step for `Case B` (`DH2`), embedding `U` in responder `IK_B` and `V` in `EK_A`. -/
def fgKeyInd1KeyStepIk (targetIdx targetPrinIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeySimState S) :=
  match q with
  | .initPrin u => fgInitPrin1KeyGdh true targetPrinIdx U u st
  | .genSPK u j =>
    fgGenSPK1KeyGdh true targetPrinIdx false targetIdx (FgGapDh.Ik.noSpkIdx S) S maxLen V U u j st
  | q => liftSimStep1Key (fgKeyIndStep false targetIdx (FgGapDh.Ik.noSpkIdx S) S maxLen V U q) st

/-- Per-query step for `Case D` (`DH4`), embedding `U` in `EK_A` and `V` in `OPK_B`. -/
def fgKeyInd1KeyStepOpk (targetIdx targetOpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeySimState S) :=
  match q with
  | .initPrin u => fgInitPrin1KeyGdh false S.N_id U u st
  | .genSPK u j =>
    fgGenSPK1KeyGdh false S.N_id false targetIdx (FgGapDh.Opk.noSpkIdx S) S maxLen U V u j st
  | q => liftSimStep1Key (fgKeyIndStepOpk targetIdx targetOpkIdx S maxLen U V q) st

def runWithGdhSignStep {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp GdhSignSimSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    OracleComp GdhSignSimSpec (α × St) :=
  OracleComp.construct
    (C := fun _ => St → OracleComp GdhSignSimSpec (α × St))
    (fun x st => pure (x, st))
    (fun q _ r st =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl (Sum.inl n)))
        r u st
      | Sum.inr gq => do
        let p ← step gq st
        r p.1 p.2)
    mx st

def fgKeyInd1KeyGapDhRunAt (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (U V : Bytes) : OracleComp GdhSignSimSpec Bytes := do
  let secb ← unifGdhSign ($ᵗ Bool)
  let initSt := FgKeyInd1KeySimState.empty S secb
  let (_, finalSt) ← runWithGdhSignStep
    (fgKeyInd1KeyStep useDh1 targetIdx targetSpkIdx S b.q_total U V) A.1.run initSt
  liftGdhToSign (extractCdhFromSimState S useDh1 b.q_total U V finalSt.sim)

def fgKeyInd1KeyGapDhRunAtIk (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (U V : Bytes) : OracleComp GdhSignSimSpec Bytes := do
  let secb ← unifGdhSign ($ᵗ Bool)
  let initSt := FgKeyInd1KeySimState.empty S secb
  let (_, finalSt) ← runWithGdhSignStep
    (fgKeyInd1KeyStepIk targetIdx targetPrinIdx S b.q_total U V) A.1.run initSt
  liftGdhToSign (extractCdh2FromAdvRoLog b.q_total V U finalSt.sim.advRoLog)

def fgKeyInd1KeyGapDhRunAtOpk (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (U V : Bytes) : OracleComp GdhSignSimSpec Bytes := do
  let secb ← unifGdhSign ($ᵗ Bool)
  let initSt := FgKeyInd1KeySimState.empty S secb
  let (_, finalSt) ← runWithGdhSignStep
    (fgKeyInd1KeyStepOpk targetIdx targetOpkIdx S b.q_total U V) A.1.run initSt
  liftGdhToSign (extractCdh4FromAdvRoLog b.q_total U V finalSt.sim.advRoLog)

def fgKeyInd1KeyGapDhAdvAt (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := fgKeyInd1KeyGapDhRunAt useDh1 targetIdx targetSpkIdx S b A U V
  q_ddh  := 4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := b.q_total * (S.N_dh * 24 + S.N_sess_tot * 8 + 18) + (S.N_dh * 3 + S.N_sess_tot)

def fgKeyInd1KeyGapDhAdvAtIk (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := fgKeyInd1KeyGapDhRunAtIk targetIdx targetPrinIdx S b A U V
  q_ddh  := 4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := b.q_total * (S.N_dh * 24 + S.N_sess_tot * 8 + 18) + (S.N_dh * 3 + S.N_sess_tot)

def fgKeyInd1KeyGapDhAdvAtOpk (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := fgKeyInd1KeyGapDhRunAtOpk targetIdx targetOpkIdx S b A U V
  q_ddh  := 4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := b.q_total * (S.N_dh * 24 + S.N_sess_tot * 8 + 18) + (S.N_dh * 3 + S.N_sess_tot)

/-- Dispatch a flat index `idx < fgTotalIndexCount S` to the `DH1`, `DH3`, `DH2`, or `DH4` leg. -/
def fgKeyInd1KeyGapDhRunAtFlat (idx : ℕ) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) : OracleComp GdhSignSimSpec Bytes :=
  let nA := S.N_id * S.N_spk_tot
  let nC := S.N_send_tot * S.N_spk_tot
  let nB := S.N_send_tot * S.N_id
  if idx < nA then
    fgKeyInd1KeyGapDhRunAt true (idx / S.N_spk_tot) (idx % S.N_spk_tot) S b A U V
  else if idx < nA + nC then
    let r := idx - nA
    fgKeyInd1KeyGapDhRunAt false (r / S.N_spk_tot) (r % S.N_spk_tot) S b A U V
  else if idx < nA + nC + nB then
    let r := idx - (nA + nC)
    fgKeyInd1KeyGapDhRunAtIk (r / S.N_id) (r % S.N_id) S b A U V
  else
    let r := idx - (nA + nC + nB)
    fgKeyInd1KeyGapDhRunAtOpk (r / S.N_opk_tot) (r % S.N_opk_tot) S b A U V

def fgKeyInd1KeyGapDhAdvAtFlat (idx : ℕ) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := fgKeyInd1KeyGapDhRunAtFlat idx S b A U V
  q_ddh  := 4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := b.q_total * (S.N_dh * 24 + S.N_sess_tot * 8 + 18) + (S.N_dh * 3 + S.N_sess_tot)

/-- Unified four-leg `GapDhWithSignAdv` simulator for one-key `KeyInd`. -/
def fgKeyInd1KeyGapDhAdv4 (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := do
    let idx ← unifGdhSign (FgGapDh.sampleIndexRange (fgTotalIndexCount S))
    fgKeyInd1KeyGapDhRunAtFlat idx S b A U V
  q_ddh  := gdhQueryBudget S b
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := b.q_total * (S.N_dh * 24 + S.N_sess_tot * 8 + 18) + (S.N_dh * 3 + S.N_sess_tot)

end FgGapDh1Key

export FgGapDh1Key (
  GdhSignSimSpec
  liftGdhToSign
  unifGdhSign
  primGdhSignQ
  sigChalQ
  ddhGdhSignQ
  FgKeyInd1KeySimState
  liftSimStep1Key
  fgInitPrin1KeyGdh
  fgGenSPK1KeyGdh
  fgKeyInd1KeyStep
  fgKeyInd1KeyStepIk
  fgKeyInd1KeyStepOpk
  runWithGdhSignStep
  fgKeyInd1KeyGapDhRunAt
  fgKeyInd1KeyGapDhRunAtIk
  fgKeyInd1KeyGapDhRunAtOpk
  fgKeyInd1KeyGapDhAdvAt
  fgKeyInd1KeyGapDhAdvAtIk
  fgKeyInd1KeyGapDhAdvAtOpk
  fgKeyInd1KeyGapDhRunAtFlat
  fgKeyInd1KeyGapDhAdvAtFlat
  fgKeyInd1KeyGapDhAdv4
)

end SignalPqxdh.Security

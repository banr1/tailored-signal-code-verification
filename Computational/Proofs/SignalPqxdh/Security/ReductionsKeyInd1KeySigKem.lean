/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndSigKem
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndGapDh

/-!
# One-key `KeyInd` `GapSigEufCma` and `KemShCr` simulators

**Checked by Lean.** Shallow oracle-computation simulators for the one-key random-oracle handshake
game `pqxdhKeyIndImpl1KeyRo`: `shcrReductionKeyInd1Key` (`KemShCr` for `G2 → G3`) and
`sigReductionKeyInd1Key` (`GapSigEufCma` for `G0_1 → G1`, using the DDH oracle to maintain
Fiedler–Günther random-oracle consistency while the target principal's scalar is unknown).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp
open SignalPqxdh.Security.RoKem
open SignalPqxdh.Security.FgGapDh

/-! ## `KemShCr` simulator -/

namespace RoKem

/-- One-key `PrimBaseSpec` implementation of `keyIndSpec S` matching `pqxdhKeyIndImpl1KeyRo`. -/
def pqxdhKeyIndImpl1KeyRoPrim (S : Setup) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndState S) (OracleComp PrimBaseSpec)) := fun q => do
  let st ← get
  match q with
  | .initPrin u =>
    if st.principals.any (fun (idx, _) => idx == u.val) then
      return .noneResp
    let secIKA0 ← liftM (embedUnif sampleScalar32)
    let ikAPk ← liftM (primQ (.x25519Base secIKA0))
    let entry : PrincipalEntry := {
      secIKA0   := secIKA0
      ikAPk     := ikAPk
      secIKAsign := secIKA0
      ikSignPk  := ikAPk
      corrupted := false
    }
    set { st with principals := (u.val, entry) :: st.principals }
    return .initPrinResp ikAPk ikAPk
  | q_other => pqxdhKeyIndImplPrim true S q_other

def pqxdhKeyIndShCrPrimImpl1Key (embedTarget : Bool) (S : Setup) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndShCrState S) (OracleComp PrimBaseSpec))
  | .initPrin u => liftShCrBasePrim (pqxdhKeyIndImpl1KeyRoPrim S (.initPrin u))
  | q_other     => pqxdhKeyIndShCrPrimImpl embedTarget S q_other

def runWithFuelKeyInd1KeyShCrPrim (S : Setup)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : ℕ) :
    OracleComp PrimBaseSpec (Bool × KeyIndShCrState S) :=
  OracleComp.construct
    (C := fun _ => KeyIndShCrState S → ℕ → OracleComp PrimBaseSpec (Bool × KeyIndShCrState S))
    (fun b hst _ => return (b, hst))
    (fun q _ r hst fuel =>
      match q with
      | Sum.inl uq => do
        let u ← embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq))
        r u hst fuel
      | Sum.inr gq =>
        match fuel with
        | 0 => return (false, hst)
        | f + 1 => do
          let (out, hst') ← (pqxdhKeyIndShCrPrimImpl1Key true S gq).run hst
          r out hst' f)
    oa hst fuel

def stepUntilShCrFuelKeyInd1KeyPrim (S : Setup) (sIdx : ℕ)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : ℕ) :
    OracleComp PrimBaseSpec (Sum (Bool × KeyIndShCrState S) (PausedShCrData S)) :=
  OracleComp.construct
    (C := fun _ => KeyIndShCrState S → ℕ →
      OracleComp PrimBaseSpec (Sum (Bool × KeyIndShCrState S) (PausedShCrData S)))
    (fun b hst _ => return Sum.inl (b, hst))
    (fun q cont r hst fuel =>
      match q with
      | Sum.inl uq => do
        let u ← embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq))
        r u hst fuel
      | Sum.inr gq =>
        match fuel with
        | 0 => return Sum.inl (false, hst)
        | f + 1 => do
          match ← tryPauseKeyIndQueryPrim S sIdx gq cont hst with
          | some d => return Sum.inr d
          | none =>
            let (out, hst') ← (pqxdhKeyIndShCrPrimImpl1Key true S gq).run hst
            r out hst' f)
    oa hst fuel

def resumePausedKeyInd1KeyPrim (S : Setup) (fuel : ℕ) (d : PausedShCrData S)
    (ss kemCt : Bytes) : OracleComp PrimBaseSpec (Bool × KeyIndShCrState S) := do
  let (resp, hst') ← postKemKeyIndPrim S d.sid d.bundle d.uEntry d.hst ss kemCt
  runWithFuelKeyInd1KeyShCrPrim S (d.cont resp) hst' fuel

def choosePkKeyInd1KeyPrimAt (S : Setup) (b : QueryBudget) (bIdx sIdx : ℕ)
    (A : KeyIndAdversary S) (pk sk : Bytes) :
    OracleComp PrimBaseSpec (Bytes × ShCrFinishState S) := do
  let secb ← embedUnif ($ᵗ Bool)
  let initSt : KeyIndShCrState S := {
    base        := KeyIndState.empty S secb
    targetBIdx? := some bIdx
    targetPk    := pk
    targetSk    := sk
  }
  let res ← stepUntilShCrFuelKeyInd1KeyPrim S sIdx A.run initSt b.q_total
  let chosenPk := match res with
    | Sum.inl _ => pk
    | Sum.inr d => d.bundle.pqspkB
  return (chosenPk, (pk, sk, chosenPk, res))

def findCollisionKeyInd1KeyPrim (S : Setup) (b : QueryBudget)
    (st : ShCrFinishState S) (ss ct : Bytes) : OracleComp PrimBaseSpec Bytes := do
  let (pk, sk, chosenPk, res) := st
  let (_, finalHst) ← match res with
    | Sum.inl done => pure done
    | Sum.inr d    => resumePausedKeyInd1KeyPrim S b.q_total d ss ct
  extractCollidingKemCtPrim b.q_total pk sk chosenPk ct ss finalHst.recvKemRecs

def shcrReductionKeyInd1KeyCore (S : Setup) (b : QueryBudget) (A : KeyIndAdversary S) :
    KemShCrAdv where
  State := ShCrFinishState S
  choosePk := fun pk sk => do
    let idx ← embedUnif (sampleIndexRange (S.N_spk_tot * S.N_send_tot))
    choosePkKeyInd1KeyPrimAt S b (idx / S.N_send_tot) (idx % S.N_send_tot) A pk sk
  findCollision := findCollisionKeyInd1KeyPrim S b
  q_prim := primQueryBudget S b

/-- Two-stage `KemShCr` reduction adversary for one-key `KeyInd` (`G2 → G3`). -/
def shcrReductionKeyInd1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : KemShCrAdv :=
  shcrReductionKeyInd1KeyCore S b A.1

end RoKem

export RoKem (
  pqxdhKeyIndImpl1KeyRoPrim
  pqxdhKeyIndShCrPrimImpl1Key
  runWithFuelKeyInd1KeyShCrPrim
  stepUntilShCrFuelKeyInd1KeyPrim
  resumePausedKeyInd1KeyPrim
  choosePkKeyInd1KeyPrimAt
  findCollisionKeyInd1KeyPrim
  shcrReductionKeyInd1KeyCore
  shcrReductionKeyInd1Key
)

/-! ## `GapSigEufCma` simulator -/

namespace Sig1Key

abbrev SigDdhSimSpec := PrimBaseSpec + sigAndDdhSpec

def unifSigDdh {α : Type} (mx : ProbComp α) : OracleComp SigDdhSimSpec α :=
  embedPrim (spec := sigAndDdhSpec) (embedUnif mx)

def primSigDdhQ (q : PrimQuery) : OracleComp SigDdhSimSpec (primSpec.Range q) :=
  liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl (Sum.inr q)))

def sigChalQ (msg : Bytes) : OracleComp SigDdhSimSpec Bytes :=
  liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inr (Sum.inl (.sign msg))))

def ddhSigDdhQ (X Y Z : Bytes) : OracleComp SigDdhSimSpec Bool :=
  liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inr (Sum.inr (X, Y, Z))))

def embedGdhSigDdh {α : Type} (mx : OracleComp GdhSimSpec α) : OracleComp SigDdhSimSpec α :=
  OracleComp.construct
    (C := fun _ => OracleComp SigDdhSimSpec α)
    pure
    (fun q _ r =>
      match q with
      | Sum.inl pq => do
        let u ← liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl pq))
        r u
      | Sum.inr dq => do
        let b ← liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inr (Sum.inr dq)))
        r b)
    mx

/-- Simulator state for `sigReductionKeyInd1Key`, tracking signing budget and extracted forgery. -/
structure Sig1KeySimState (S : Setup) where
  fg          : FgKeyIndSimState S
  targetParty : Nat
  targetPk    : Bytes
  signBudget  : Nat
  forgery     : Option (Bytes × Bytes) := none

def Sig1KeySimState.empty (S : Setup) (secb : Bool) (targetParty : Nat) (targetPk : Bytes) :
    Sig1KeySimState S :=
  { fg          := FgKeyIndSimState.empty S secb
    targetParty := targetParty
    targetPk    := targetPk
    signBudget  := min S.N_spk_tot S.N_recv
    forgery     := none }

/-- Single-query handler for the one-key `GapSigEufCma` simulator, freezing once a forgery is found. -/
def sig1KeyStep (S : Setup) (maxLen : ℕ) (q : KeyIndQuery S) (st : Sig1KeySimState S) :
    OracleComp SigDdhSimSpec (KeyIndResponse × Sig1KeySimState S) := do
  if st.forgery.isSome then
    return (.noneResp, st)
  match q with
  | .initPrin u =>
    if st.fg.base.principals.any (fun (idx, _) => idx == u.val) then
      return (.noneResp, st)
    let isTarget : Bool := u.val == st.targetParty
    let secIKA0Raw ← unifSigDdh sampleScalar32
    let ikAPkRaw ← primSigDdhQ (.x25519Base secIKA0Raw)
    let sec := if isTarget then [] else secIKA0Raw
    let pk := if isTarget then st.targetPk else ikAPkRaw
    let entry : PrincipalEntry := {
      secIKA0   := sec
      ikAPk     := pk
      secIKAsign := sec
      ikSignPk  := pk
      corrupted := false
    }
    let base' := { st.fg.base with principals := (u.val, entry) :: st.fg.base.principals }
    return (.initPrinResp pk pk, { st with fg := { st.fg with base := base' } })
  | .genSPK u j =>
    if u.val == st.targetParty then
      if st.fg.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
        return (.noneResp, st)
      let some (_, uEntry) := st.fg.base.principals.find? (fun (idx, _) => idx == u.val)
        | return (.noneResp, st)
      match st.signBudget with
      | 0 => return (.noneResp, st)
      | signBudget' + 1 =>
        let spkSk ← unifSigDdh sampleScalar32
        let spkPk ← primSigDdhQ (.x25519Base spkSk)
        let spkSig ← sigChalQ (encodeEC spkPk)
        let seedKem ← unifSigDdh sampleRandom64
        let (pqspkPk, pqspkSk) ← primSigDdhQ (.kemKeyGen seedKem)
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
          { st.fg.base with spkBundles := ((u.val, j.val), bEntry) :: st.fg.base.spkBundles }
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
          { st with fg := { st.fg with base := base' }, signBudget := signBudget' })
    else do
      let (out, fg') ← embedGdhSigDdh
        (fgKeyIndStep false S.N_send_tot S.N_spk_tot S maxLen [] st.targetPk (.genSPK u j) st.fg)
      return (out, { st with fg := fg' })
  | .initiateOPK u i bundle =>
    let forgery' ← embedPrim (spec := sigAndDdhSpec)
      (extractBundleForgeryPrim S st.targetParty st.targetPk
        st.fg.base.principals st.fg.base.spkBundles bundle st.forgery)
    if forgery'.isSome then
      return (.noneResp, { st with forgery := forgery' })
    let (out, fg') ← embedGdhSigDdh
      (fgKeyIndStep false S.N_send_tot S.N_spk_tot S maxLen [] st.targetPk
        (.initiateOPK u i bundle) st.fg)
    return (out, { st with fg := fg' })
  | .initiateNoOPK u i bundle =>
    let forgery' ← embedPrim (spec := sigAndDdhSpec)
      (extractBundleForgeryPrim S st.targetParty st.targetPk
        st.fg.base.principals st.fg.base.spkBundles bundle st.forgery)
    if forgery'.isSome then
      return (.noneResp, { st with forgery := forgery' })
    let (out, fg') ← embedGdhSigDdh
      (fgKeyIndStep false S.N_send_tot S.N_spk_tot S maxLen [] st.targetPk
        (.initiateNoOPK u i bundle) st.fg)
    return (out, { st with fg := fg' })
  | q_other => do
    let (out, fg') ← embedGdhSigDdh
      (fgKeyIndStep false S.N_send_tot S.N_spk_tot S maxLen [] st.targetPk q_other st.fg)
    return (out, { st with fg := fg' })

def runWithSigDdhStep {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp SigDdhSimSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    OracleComp SigDdhSimSpec (α × St) :=
  OracleComp.construct
    (C := fun _ => St → OracleComp SigDdhSimSpec (α × St))
    (fun x st => pure (x, st))
    (fun q _ r st =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl (Sum.inl n)))
        r u st
      | Sum.inr gq => do
        let p ← step gq st
        r p.1 p.2)
    mx st

def sigReductionKeyInd1KeyRunAt (targetParty : Nat) (S : Setup) (b : QueryBudget)
    (A : KeyIndAdversary S) (pk : Bytes) : OracleComp SigDdhSimSpec (Bytes × Bytes) := do
  let secb ← unifSigDdh ($ᵗ Bool)
  let initSt := Sig1KeySimState.empty S secb targetParty pk
  let (_, finalSt) ← runWithSigDdhStep (sig1KeyStep S b.q_total) A.run initSt
  return finalSt.forgery.getD ([], [])

def sigReductionKeyInd1KeyAt (targetParty : Nat) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapSigEufCmaAdv where
  run := sigReductionKeyInd1KeyRunAt targetParty S b A.1
  q_sig := 2 * min S.N_spk_tot S.N_recv
  q_ddh := gdhQueryBudget S b
  q_prim := primQueryBudget S b

/-- Per-principal-sampled `GapSigEufCma` reduction adversary for one-key `KeyInd` (`G0_1 → G1`). -/
def sigReductionKeyInd1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapSigEufCmaAdv where
  run pk := do
    let k ← unifSigDdh (RoKem.sampleIndexRange S.N_id)
    sigReductionKeyInd1KeyRunAt k S b A.1 pk
  q_sig := 2 * min S.N_spk_tot S.N_recv
  q_ddh := gdhQueryBudget S b
  q_prim := primQueryBudget S b

end Sig1Key

export Sig1Key (
  SigDdhSimSpec
  unifSigDdh
  primSigDdhQ
  sigChalQ
  ddhSigDdhQ
  embedGdhSigDdh
  Sig1KeySimState
  sig1KeyStep
  runWithSigDdhStep
  sigReductionKeyInd1KeyRunAt
  sigReductionKeyInd1KeyAt
  sigReductionKeyInd1Key
)

end SignalPqxdh.Security

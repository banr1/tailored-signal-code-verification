/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeySigKem

/-!
# One-Key `Auth` `GapSigEufCma` Simulator

**Checked by Lean.** Shallow `GapSigEufCmaAdv` reduction (`sigReductionAuth1Key`) for the one-key
`Auth` bad-signature hop (`G1 → G2`), delegating queries to the halting one-key Fiedler–Günther
simulator while extracting bundle signature forgeries on `send*` queries.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

/-- State of the one-key `Auth` `GapSigEufCma` simulator. -/
structure SigAuth1KeySimState (S : Setup) where
  fg          : FgAuth1KeySimState S
  targetParty : ℕ
  targetPk    : Bytes
  forgery     : Option (Bytes × Bytes) := none

def SigAuth1KeySimState.empty (S : Setup) (secb : Bool) (targetParty : ℕ) (pk : Bytes) :
    SigAuth1KeySimState S :=
  { fg := FgAuth1KeySimState.empty S secb, targetParty := targetParty, targetPk := pk,
    forgery := none }

def sigAuth1KeyDelegate (S : Setup) (maxLen : ℕ) (q : AuthQuery S) (st : SigAuth1KeySimState S) :
    OracleComp GdhSignSimSpec (AuthResponse × SigAuth1KeySimState S) := do
  let (out, fg') ← fgAuth1KeyStepHalt true st.targetParty S.N_spk_tot S maxLen
    st.targetPk st.targetPk q st.fg
  return (out, { st with fg := fg' })

def sigAuth1KeySend (S : Setup) (maxLen : ℕ) (q : AuthQuery S) (bundle : PreKeyBundleInput)
    (st : SigAuth1KeySimState S) :
    OracleComp GdhSignSimSpec (AuthResponse × SigAuth1KeySimState S) := do
  let forgery' ← SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec)
    (extractBundleForgeryPrim S st.targetParty st.targetPk
      st.fg.sim.base.principals st.fg.sim.base.spkBundles bundle st.forgery)
  if forgery'.isSome then
    return (.noneResp, { st with forgery := forgery' })
  sigAuth1KeyDelegate S maxLen q st

/-- Per-query handler that freezes the simulator state once a bundle forgery is extracted. -/
def sigAuth1KeyStep (S : Setup) (maxLen : ℕ) (q : AuthQuery S) (st : SigAuth1KeySimState S) :
    OracleComp GdhSignSimSpec (AuthResponse × SigAuth1KeySimState S) :=
  if st.forgery.isSome then
    return (.noneResp, st)
  else
    match q with
    | .sendOPK _ _ bundle _ _ => sigAuth1KeySend S maxLen q bundle st
    | .sendNoOPK _ _ bundle _ _ => sigAuth1KeySend S maxLen q bundle st
    | q => sigAuth1KeyDelegate S maxLen q st

def sigReductionAuth1KeyRunAt (targetParty : ℕ) (S : Setup) (b : QueryBudget)
    (A : AuthAdversary S) (pk : Bytes) : OracleComp GdhSignSimSpec (Bytes × Bytes) := do
  let secb ← unifGdhSign ($ᵗ Bool)
  let initSt := SigAuth1KeySimState.empty S secb targetParty pk
  let (_, finalSt) ← runWithGdhSignStep (sigAuth1KeyStep S b.q_total) A.run initSt
  return finalSt.forgery.getD ([], [])

def sigReductionAuth1KeyAt (targetParty : ℕ) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : GapSigEufCmaAdv where
  run := sigReductionAuth1KeyRunAt targetParty S b A.1
  q_sig := 2 * min S.N_spk_tot S.N_recv
  q_ddh := authGdhQueryBudget S b
  q_prim := gdhPrimQueryBudget S b

/-- One-key `Auth` `GapSigEufCma` reduction (`G1 → G2`) sampling a uniform target principal. -/
def sigReductionAuth1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : GapSigEufCmaAdv where
  run pk := do
    let k ← unifGdhSign (RoKem.sampleIndexRange S.N_id)
    sigReductionAuth1KeyRunAt k S b A.1 pk
  q_sig := 2 * min S.N_spk_tot S.N_recv
  q_ddh := authGdhQueryBudget S b
  q_prim := gdhPrimQueryBudget S b

end Proofs.SignalPqxdh.Security

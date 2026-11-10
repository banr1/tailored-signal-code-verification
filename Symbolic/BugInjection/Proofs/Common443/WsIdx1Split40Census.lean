/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs
public import Symbolic.BugInjection.Proofs.Common443.CompExcuse2

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs
theorem kemDecap_kemEncap_fst (sk e : DY.Bytes) : PQKem.kemDecap sk (PQKem.kemEncap (PQKem.kemPk sk) e).1 = some (PQKem.kemEncap (PQKem.kemPk sk) e).2 := by simp only [PQKem.kemDecap, PQKem.CanPQKem.kemDecap, PQKem.kemEncap, PQKem.CanPQKem.kemEncap, PQKem.kemPk, PQKem.CanPQKem.kemPk, BytesView.view_pack, ↓reduceIte]
theorem aliceAgreement_fst (ikA ek ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) (e : DY.Bytes) : (DY.Libsignal.PQXDH.aliceAgreement ikA ek ikBPk spkPk pqPk opk e).1 = (PQKem.kemEncap pqPk e).1 := rfl
def Split40PkPin : Prop := ∀ r : Records, compFitsPinned setup compI0 r → setupPublic r 6 = PQKem.kemPk (setupSecret r 4)
def split40NewTerms (r : Records) (ms' : List Move) (p : PreKeyFields) (x : PreKeyRep) : List DY.Bytes :=
  match parseTrSignalMsg x.msg with
  | none => [x.ek, x.ct, x.msg]
  | some _ => [x.ek, x.ct, x.msg] ++ bobTerms r (honestSalts r ms') p x
def Split40OwnSaltMac : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (msg : TRSignalMsg), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → parseTrSignalMsg (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂).msg = some msg → ¬ OwnSaltMacCollision compI0 S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (honestSalts r ms') msg (bobTrials r (runTraceMoves r ms') p (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂) msg)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census

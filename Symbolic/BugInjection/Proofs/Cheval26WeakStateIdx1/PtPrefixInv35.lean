/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvIni

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.BugInjection Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1
export Symbolic.BugInjection.Proofs.Common443.CompPrefixInvIni ( storedSecrets_inv_of_no_setup movesAnchored_append_left' runMoves_cons_fst' iniPrefixStateSecretsInv_of_matchedPrefix_ini)
attribute [local irreducible] setupPublic setupSecret Symbolic.BugInjection.hexBytes
def bundle0Chars : List Char := chars_of_hex bundle0
theorem bundle0_eq_hex : bundle0 = hexBytes (str_of_hex bundle0) := rfl
theorem bundle0Str_eq : (str_of_hex bundle0) = String.ofList bundle0Chars := rfl
theorem bundle0_byte4_ne_one : bundle0[4]? ≠ some 1#8 := by
  have h : bundle0 = hexBytes.go hexDigit bundle0Chars := by rw [bundle0_eq_hex, bundle0Str_eq, hexBytes_ofList]
  rw [h]; decide
theorem call0Rng_length : call0Rng.length = 34 := by simpa using congrArg List.length call0Rng_map_kind
theorem ptDeadAt35 : PtDeadAt 35 := ptDeadAt35_of fun _ _ _ _ hfits hnb hexp => iniPrefixStateSecretsInv_of_matchedPrefix_ini hfits.1.1 hnb hexp.1 call0Rng_length call0Rng_kind bundle0_byte4_ne_one
theorem ptDeadAt35_self
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (hfits : compFitsPinned setup compI0 r)
    (hnb : Common443.CompSetupSecrecy.NoBrk r ms)
    (hexp : ExplainsMoves compI0 r S who ok g ms ((Witnesses.Cheval26WeakStateIdx1.trace).take 35))
    (hem : EventMatchesEntry compI0 r S g (.pt (ptAt 35)) (ptEntryOfNextEncrypt r ms)) :
    ¬ MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms :=
  ptDeadAt35_self_of (fun _ _ _ _ hfits hnb hexp => iniPrefixStateSecretsInv_of_matchedPrefix_ini hfits.1.1 hnb hexp.1 call0Rng_length call0Rng_kind bundle0_byte4_ne_one) r S g ms hfits hnb hexp hem
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35

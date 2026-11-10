/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
public import Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0Mem
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire (SendMatchesMoves PreKeyOuterMatches)
theorem sendMatches_append_inv {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {w : HwBytes} {L : List DY.Bytes} {o : DY.Bytes} {q₀ : PreKeyFields} (hsm : SendMatchesMoves i r S g w (L ++ [o])) (hlen : w.length < 2 ^ 63) (hq₀ : parsePreKeyWire w = some q₀) : ∃ ek' ct', L = [ek', ct'] ∧ q₀.baseKey = ecKey (gamma i S g ek') ∧ q₀.kyberCiphertext = some (kyberKey (gamma i S g ct')) ∧ q₀.message = gamma i S g o := by
  obtain ⟨_, hsm⟩ := hsm
  match L, hsm with
  | [ek', ct'], hsm =>
    obtain ⟨pk, spk, kpk, _, hw⟩ := hsm; obtain ⟨_, hkc, hbk, hmsg⟩ := CompRPreKeyWire.parsePreKeyWire_preKeyWire_inv hw hlen hq₀; exact ⟨ek', ct', rfl, hbk, hkc, hmsg⟩
  | [], hsm => exact (hsm : False).elim
  | [_], hsm => exact (hsm : False).elim
  | _ :: _ :: _ :: t, hsm => cases t <;> exact (hsm : False).elim
theorem hγ_of_sendMatches {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {w : HwBytes} {tr : ExecTrace} {e c : Nat} {msg ek ct : DY.Bytes} {q₀ : PreKeyFields} (hsm : SendMatchesMoves i r S g w (received tr [e, c] ++ [msg])) (hlen : w.length < 2 ^ 63) (hq₀ : parsePreKeyWire w = some q₀) (hbk : q₀.baseKey = ecKey (gamma i S g ek)) (hkc : q₀.kyberCiphertext = some (kyberKey (gamma i S g ct))) : (received tr [e, c]).map (gamma i S g) = [gamma i S g ek, gamma i S g ct] := by
  obtain ⟨ek', ct', hL, hbk', hkc', -⟩ := sendMatches_append_inv hsm hlen hq₀; rw [hL]; have h1 : gamma i S g ek' = gamma i S g ek := CompPrefixInvBundle.ecKey_inj (hbk'.symm.trans hbk)
  have h2 : gamma i S g ct' = gamma i S g ct := by rw [hkc'] at hkc; exact CompPrefixInvBundle.kyberKey_inj (Option.some.inj hkc)
  simp only [List.map_cons, List.map_nil, h1, h2]
theorem x0_mem_of_parts {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {ek ct msg : DY.Bytes} {q : PreKeyFields} (hkek : ek.AttackerKnows (runTraceMoves r ms)) (hkct : ct.AttackerKnows (runTraceMoves r ms)) (hkmsg : msg.AttackerKnows (runTraceMoves r ms)) (hq : parsePreKeyWire b = some q) (hbk : q.baseKey.take 33 = ecKey (gamma i S g ek)) (hkc : q.kyberCiphertext = some (kyberKey (gamma i S g ct))) (hmsg : q.message = gamma i S g msg) (hout : PreKeyOuterMatches i r b q) (hfi : FaithfulInner i S g msg q) : (⟨ek, ct, msg⟩ : PreKeyRep) ∈ preKeyRepresentations i r S g ms b := ⟨hkek, hkct, hkmsg, ⟨q, hq, hbk, hkc, hmsg, hout⟩, q, hq, hfi⟩
end Symbolic.BugInjection.Proofs.Common443.CompRX0Mem

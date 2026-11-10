/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZVals
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38Untagged
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus
public import Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZPin
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey Symbolic.BugInjection.Proofs.Common443.CompRNoBSC
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc (zeroSaltedTermsStA)
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore Symbolic.BugInjection.Proofs.Common443.CompRSplit38TaggedAgree Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZTag Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZVals Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def zeros32 : HwBytes := List.replicate 32 0#8
theorem rowDigests_take8_inj {D₁ D₂ : HwBytes} (h₁ : D₁ ∈ CompRI0TermInj.rowDigests) (h₂ : D₂ ∈ CompRI0TermInj.rowDigests) (h : D₁.take 8 = D₂.take 8) : D₁ = D₂ := by
  have hnd : (CompRI0TermInj.rowDigests.map fun D => D.take 8).Nodup := by unfold CompRI0TermInj.rowDigests; rw [List.map_map]; exact rows_take8_nodup
  exact List.inj_on_of_nodup_map hnd h₁ h₂ h
theorem gamma_zeroKey (S : Sem) (g : Ghost) : gamma compI0 S g DY.Spqr.zeroKey = zeros32 := by
  show gamma compI0 S g (({ lit := ⟨Array.replicate 32 0⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack) = zeros32
  rw [gamma_lit]; decide
theorem gamma_zmacKey (S : Sem) (g : Ghost) (stA : DY.Libsignal.TripleRatchet.TRState) : gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).macKey = hmacWith F0 (gamma compI0 S g (zprkT stA)) (hmacWith F0 (gamma compI0 S g (zprkT stA)) (zInfo ++ [1#8]) ++ (zInfo ++ [2#8])) := by simp only [DY.Libsignal.TripleRatchet.trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock1, DY.Libsignal.TripleRatchet.hkdfBlock2, zprkT, CompRNbsc38MacKey.gamma_hmac_compI0, gamma_concat_eq, gamma_info, gamma_litByte, ofByteArray_one, ofByteArray_two]
end Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZPin

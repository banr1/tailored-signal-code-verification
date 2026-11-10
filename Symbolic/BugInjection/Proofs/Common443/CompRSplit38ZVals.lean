/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZTag
import Init.Data.String

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZVals
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc (zeroSaltedTermsStA)
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore Symbolic.BugInjection.Proofs.Common443.CompRSplit38TaggedAgree Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZTag Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def zInfo : HwBytes := [87, 104, 105, 115, 112, 101, 114, 77, 101, 115, 115, 97, 103, 101, 75, 101, 121, 115]
def zChain (P F : HwBytes) : List HwBytes :=
  let ck := hmacWith F0 P (zInfo ++ [1#8]); let mk := hmacWith F0 P (ck ++ (zInfo ++ [2#8])); let iv := hmacWith F0 P (mk ++ (zInfo ++ [3#8]));
  [P, ck, mk, iv, F]
theorem gamma_info (S : Sem) (g : Ghost) : gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") = zInfo := by
  show gamma compI0 S g (({ lit := "WhisperMessageKeys".toUTF8 } : DY.Literal.Literal.SubF DY.Bytes).pack) = zInfo
  rw [gamma_lit, String.toUTF8_eq_toByteArray, ← String.ofList_toList (s := "WhisperMessageKeys"),
      String.toByteArray_ofList]
  decide
theorem gamma_litByte (S : Sem) (g : Ghost) (b : UInt8) : gamma compI0 S g (DY.Libsignal.TripleRatchet.litByte b) = ofByteArray ⟨#[b]⟩ := by
  show gamma compI0 S g (({ lit := ⟨#[b]⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack) = _
  rw [gamma_lit]
theorem ofByteArray_one : ofByteArray ⟨#[1]⟩ = [1#8] := by decide
theorem ofByteArray_two : ofByteArray ⟨#[2]⟩ = [2#8] := by decide
theorem ofByteArray_three : ofByteArray ⟨#[3]⟩ = [3#8] := by decide
abbrev zprkT (stA : DY.Libsignal.TripleRatchet.TRState) : DY.Bytes := DY.Libsignal.TripleRatchet.hmac DY.Spqr.zeroKey (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2
abbrev zfullT (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Bytes := DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).macKey (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr₂ stA cl pq)))
theorem gamma_take5 (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : ((zeroSaltedTermsStA tr₂ stA cl pq).take 5).map (gamma compI0 S g) = zChain (gamma compI0 S g (zprkT stA)) (gamma compI0 S g (zfullT tr₂ stA cl pq)) := by simp only [zeroSaltedTermsStA, DY.Libsignal.TripleRatchet.trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock1, DY.Libsignal.TripleRatchet.hkdfBlock2, DY.Libsignal.TripleRatchet.hkdfBlock3, List.take, List.map, zChain, zprkT, zfullT, gamma_hmac_compI0, gamma_concat_eq, gamma_info, gamma_litByte, ofByteArray_one, ofByteArray_two, ofByteArray_three]
end Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZVals

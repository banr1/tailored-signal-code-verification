/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.Top
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupTorsionComp

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupTorsionComp443
open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.PQXDH.Refinement
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443 (hexDigit hexBytes_ofList not_kyberMismatch_compI0 NoAccept not_readCollision_of_noAccept isAcceptedRecvKindAt isPtKindAt isAcceptedRecvKindAt_of_recv_accepted isPtKindAt_of_pt not_knownBaseKey_of_bobDone_nil not_collisionAt_of_gen)
attribute [local irreducible] Symbolic.BugInjection.hexBytes
abbrev compI0 : ExternInterpretation := Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compI0
def ptMsg35 : HwBytes :=
  match (Witnesses.Cheval26SmallSubgroupTorsionComp.trace[35]? : Option MachineEvent) with
  | some (.pt b) => b
  | _ => []
def recvMsg38 : HwBytes :=
  match (Witnesses.Cheval26SmallSubgroupTorsionComp.trace[38]? : Option MachineEvent) with
  | some (.recv b) => b
  | _ => []
theorem trace_getElem?_35 : Witnesses.Cheval26SmallSubgroupTorsionComp.trace[35]? = some (.pt ptMsg35) := rfl
theorem trace_getElem?_38 : Witnesses.Cheval26SmallSubgroupTorsionComp.trace[38]? = some (.recv recvMsg38) := rfl
def NoFullMatchTC : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → Common443.CompSetupSecrecy.NoBrk r ms → ¬ MatchedPrefix compI0 r S who g ms trace
def PtDeadTC : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → Common443.CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who ok g ms (trace.take 35) → EventMatchesEntry compI0 r S g (.pt ptMsg35) (ptEntryOfNextEncrypt r ms) → ¬ (∀ g' ∈ PrefixGhosts compI0 r S who g ms (trace.take 35),
        MemoCollisionOn compI0 r S g' (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms) (runVis r ms) (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms)
def NoBobDone38TC : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → ExplainsMoves compI0 r S who ok g ms (trace.take 38) → bobDoneBaseKeys (runTraceMoves r ms) = []
def NoBsc38TC : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup compI0 r → Common443.CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who ok g ms (trace.take 38) → parsePreKeyWire recvMsg38 = some p → ∃ g' ms', ExplainsMoves compI0 r S who ok g' ms' (trace.take 38) ∧ ∃ x ∈ preKeyRepresentations compI0 r S g' ms' recvMsg38, ¬ BobStartCollision compI0 r S g' ms' p x
def recvMsg38Chars : List Char := chars_of_hex_def recvMsg38
theorem recvMsg38_eq_hex : recvMsg38 = hexBytes (str_of_hex_def recvMsg38) := rfl
theorem recvMsg38Str_eq : (str_of_hex_def recvMsg38) = String.ofList recvMsg38Chars := rfl
def recvMsg38Fast : HwBytes := hexBytes.go hexDigit recvMsg38Chars
theorem recvMsg38_eq_fast : recvMsg38 = recvMsg38Fast := by change recvMsg38 = hexBytes.go hexDigit recvMsg38Chars; rw [recvMsg38_eq_hex, recvMsg38Str_eq, hexBytes_ofList]
theorem recvMsg38Fast_head_ne_whisper : recvMsg38Fast.head? ≠ some wireWhisperTag := by decide +kernel
theorem recvMsg38_head_ne_whisper : recvMsg38.head? ≠ some wireWhisperTag := by rw [recvMsg38_eq_fast]; exact recvMsg38Fast_head_ne_whisper
theorem noAccept_trace_take38 : NoAccept (trace.take 38) := by
  unfold NoAccept
  decide
private theorem torsionComp_acceptedRecv_fin : ∀ k : Fin trace.length, isAcceptedRecvKindAt trace k.1 = true → k.1 = 38 := by decide
private theorem torsionComp_pt_fin : ∀ k : Fin trace.length, isPtKindAt trace k.1 = true → k.1 = 35 := by decide
theorem torsionComp_acceptedRecv_index {n : Nat} (hn : n < trace.length) (h : isAcceptedRecvKindAt trace n = true) : n = 38 := torsionComp_acceptedRecv_fin ⟨n, hn⟩ h
theorem torsionComp_pt_index {n : Nat} (hn : n < trace.length) (h : isPtKindAt trace n = true) : n = 35 := torsionComp_pt_fin ⟨n, hn⟩ h
theorem not_collisionAt_of (hPt : PtDeadTC) (hBob : NoBobDone38TC) (hBsc : NoBsc38TC) {r : Records} {S : Sem} (hfits : compFitsPinned setup compI0 r) (hnb : ∀ ms, Common443.CompSetupSecrecy.NoBrk r ms) : ¬ CollisionAt compI0 r S who ok trace := not_collisionAt_of_gen setup who ok trace ptMsg35 recvMsg38 trace_getElem?_35 trace_getElem?_38 recvMsg38_head_ne_whisper noAccept_trace_take38 torsionComp_acceptedRecv_index torsionComp_pt_index hPt hBob hBsc hfits hnb
end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupTorsionComp443

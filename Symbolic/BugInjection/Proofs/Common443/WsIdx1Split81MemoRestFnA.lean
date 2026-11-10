/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81Enum
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnA
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
open Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum (decomp40_moves census_iniAliceOut_eq census_iniAliceStartState_eq census_encSt_eq)
open Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Core (rngAt acceptAt wireAt40_canon not_gamma_encOut_ns0_at1 decomp45_raw seg40_shape)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def Split81PrefixAtomAt (r : Records) (_S : Sem) (_g : Ghost)
    (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) (u : DY.Bytes) : Prop :=
  let o₁ := Census443Defs.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := Census443Defs.iniAliceStartState tr₁ r.bob o₁
  let stA₁' := Census443Defs.encSt tr₂ stA₁ cl₁
  Split81PrefixAtomGen r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅
    (fun u => ∃ (spqrMsgIdx₂ : UInt32) (spqr₂' : DY.Bytes),
      (DY.Spqr.spqrRecv (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂' ∧
      u = serBob r (bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' 1)) u
theorem split81PrefixEnumAt_of_mp_links {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {b1 b2 b5 : List MachineEvent} (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (seg 35 3) b1) (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2) (hc5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (seg 78 3) b5) (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms' (seg 0 35 ++ b1 ++ b2 ++ seg 40 3 ++ seg 43 35 ++ b5)) (hlinks : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : ∃ (tr_bob : ExecTrace), gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes ∧ ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), Split81PrefixAtomAt r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ u ∨ u ∈ storedSecrets (runTraceMoves r ms') := by
  let o₁ := Census443Defs.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := Census443Defs.iniAliceStartState tr₁ r.bob o₁
  let stA₁' := Census443Defs.encSt tr₂ stA₁ cl₁
  exact split81PrefixEnum_gen_of_mp_links
    (fun tr_bob u => ∃ (spqrMsgIdx₂ : UInt32) (spqr₂' : DY.Bytes),
      (DY.Spqr.spqrRecv (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂' ∧
      u = serBob r (bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' 1))
    (fun _ spqrMsgIdx₂ spqr₂' _ hspqr => ⟨spqrMsgIdx₂, spqr₂',
      by dsimp only [o₁, stA₁, stA₁']; rw [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq]; exact hspqr,
      by dsimp only [o₁, stA₁]; rw [census_iniAliceOut_eq, census_iniAliceStartState_eq]⟩) hc1 hc2 hc5 hmp hlinks
theorem split81PrefixEnumAt {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hlinks : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : ∃ (tr_bob : ExecTrace), gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes ∧ ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), Split81PrefixAtomAt r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ u ∨ u ∈ storedSecrets (runTraceMoves r ms') := by
  obtain ⟨b1, b2, b5, hc1, hc2, hc5, hmp⟩ := hinv.mp.2.2.2.2.2
  exact split81PrefixEnumAt_of_mp_links hc1 hc2 hc5 (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp) hlinks
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnA

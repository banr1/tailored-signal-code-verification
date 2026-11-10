/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs
abbrev serAlice (r : Records) (st : DY.Libsignal.TripleRatchet.TRState) : DY.Bytes := Comparse.serialize (⟨r.alice, st⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)
abbrev serBob (r : Records) (st : DY.Libsignal.TripleRatchet.TRState) : DY.Bytes := Comparse.serialize (⟨r.bob, st⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)
def bobRng41Bytes : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[41]? : Option MachineEvent) with
  | some (.rng b) => b | _ => []
def bobSt81 (r : Records) (o₁ : DY.Libsignal.PQXDH.AliceHandshakeOut) (tr_bob : ExecTrace)
    (rt₂ spqr₂' : DY.Bytes) (ctr₂ : UInt32) : DY.Libsignal.TripleRatchet.TRState :=
  let (rk1, ck1) := DY.Libsignal.TripleRatchet.createChain o₁.keys.rk rt₂ (setupSecret r 2)
  let (rk2, cks) := DY.Libsignal.TripleRatchet.createChain rk1 rt₂ (randTerm tr_bob.length 32)
  { peer := r.alice, myIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r 2), peerIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r 0), rk := rk2, dhs := randTerm tr_bob.length 32, cks := cks, ns := 0, pn := 0, sid := DY.Concat.concat (DY.X25519.x25519Key rt₂) o₁.keys.rk, initiator := false, rIdx := 2, recv := [{ ratchetKey := rt₂, chainKey := (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.chainKeyAt ck1 ctr₂.toNat)).1, index := ctr₂ + 1, rIdx := 2 }], spqr := spqr₂' }
def Split81PrefixAtom (r : Records) (S : Sem) (g : Ghost)
    (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) (u : DY.Bytes) : Prop :=
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := iniAliceStartState tr₁ r.bob o₁
  let stA₁' := encSt tr₂ stA₁ cl₁
  let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₂ := iniAliceStartState tr₄ r.bob o₂
  u = o₁.ek ∨ u = o₁.ct ∨ u = encOut tr₂ stA₁ cl₁ (tr₂.length + 2) ∨ u = encOut tr₃ stA₁' cl₂ (tr₃.length + 2) ∨ u = o₂.ek ∨ u = o₂.ct ∨ u = encOut tr₅ stA₂ cl₅ (tr₅.length + 2) ∨ u = randTerm tr₂.length 32 ∨ u = randTerm tr₃.length 32 ∨ u = randTerm tr₅.length 32 ∨ u = serAlice r stA₁ ∨ u = serAlice r stA₁' ∨ u = serAlice r (encSt tr₃ stA₁' cl₂) ∨ u = serAlice r stA₂ ∨ u = serAlice r (encSt tr₅ stA₂ cl₅) ∨ (∃ (tr_bob : ExecTrace) (spqrMsgIdx₂ : UInt32) (spqr₂' : DY.Bytes), gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes ∧ (DY.Spqr.spqrRecv (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂' ∧ u = serBob r (bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' 1))
def Split81PrefixEnumOn (r : Records) (S : Sem) (g : Ghost) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : Prop := ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), Split81PrefixAtom r S g tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ u ∨ u ∈ storedSecrets (runTraceMoves r ms')
def Split81PrefixEnum : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Split81PrefixEnumOn r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs
open CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (parseTrSignalMsg)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census
abbrev Row : Type := DY.Bytes × DY.Bytes × HwBytes
def saltedNodes40 (salt : DY.Bytes) (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState)
    (cl : Nat) : List DY.Bytes :=
  let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2
  let w := encWire tr stA cl (tr.length + 2)
  let prk := DY.Libsignal.TripleRatchet.hmac salt seed
  let keys := DY.Libsignal.TripleRatchet.trMsgKeys salt seed
  let macFull := DY.Libsignal.TripleRatchet.hmac keys.macKey (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk w))
  let mac := DY.Libsignal.TripleRatchet.computeMac keys.macKey stA.myIk stA.peerIk w
  [prk, keys.cipherKey, keys.macKey, keys.iv, macFull, mac]
def stA40 (r : Records) (tr₁ tr₂ : ExecTrace) (cl₁ : Nat) : DY.Libsignal.TripleRatchet.TRState := encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁
def ck1Salt40 (r : Records) (tr₁ : ExecTrace) : DY.Bytes :=
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  DY.Spqr.spqrChainKey o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1)
def z40Terms (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : List DY.Bytes := saltedNodes40 DY.Spqr.zeroKey tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ ++ saltedNodes40 (ck1Salt40 r tr₁) tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂
def preMemo40 (r : Records) (S : Sem) (g : Ghost) (ms' : List Move) : List Row := (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap fun u => (gamma' compI0 S g u).memo
def newMemo40 (r : Records) (S : Sem) (g : Ghost) (ms' : List Move) (p : PreKeyFields) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : List Row := (split40NewTerms r ms' p (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂)).flatMap fun u => (gamma' compI0 S g u).memo
def MemoColl40 (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : Row) : Prop := x₁.2.1 ≠ x₂.2.1 ∧ (assumedInjective x₁.1 ∨ assumedInjective x₂.1) ∧ (x₁.1 ∈ pts → x₂.1 ∉ pts ∧ assumedInjective x₂.1 ∧ ¬ known x₂.1) ∧ (x₂.1 ∈ pts → x₁.1 ∉ pts ∧ assumedInjective x₁.1 ∧ ¬ known x₁.1) ∧ x₁.2.2 = x₂.2.2
def Cls40 (pre : List Row) (Z : List DY.Bytes) (x : Row) : Prop := x ∈ pre ∨ assumedInjective x.1 = false ∨ x.1 ∈ Z
abbrev PairQ40 : Type := Sem → Ghost → (DY.Bytes → Prop) → List DY.Bytes → List Row → List DY.Bytes → Row → Row → Prop
def QZ40 : PairQ40 := fun _ _ known pts _ Z x₁ x₂ => (x₁.1 ∈ Z ∨ x₂.1 ∈ Z) → ¬ MemoColl40 known pts x₁ x₂
def QRest40 : PairQ40 := fun _ _ known pts _ Z x₁ x₂ => x₁.1 ∉ Z → x₂.1 ∉ Z → ¬ MemoColl40 known pts x₁ x₂
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs

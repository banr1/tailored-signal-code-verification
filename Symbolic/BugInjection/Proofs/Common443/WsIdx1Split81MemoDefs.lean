/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged
public import Symbolic.BugInjection.Proofs.Common443.CompMemoInjGtDraws

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.TripleRatchet (TRState parseTrSignalMsg)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4) open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 (setup)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
theorem setupPublic_0 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 0 = DY.DiffieHellman.dhPk (randTerm 0 32) := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.setupPublic_0_bridge r hNe
theorem split81PinObl : Split81PinObl := fun r hfits =>
  have hNe : r.alice ≠ r.bob := hfits.1.1.1
  ⟨setupSecret_0 hNe, setupSecret_1 hNe, setupSecret_2 hNe, setupSecret_4 hNe, setupPublic_0 hNe, setupPublic_2 hNe, setupPublic_4 hNe, setupPublic_6 hNe, hNe⟩
theorem split81PkPin : Split81PkPin := split81PkPin_of_pinObl split81PinObl
theorem split40PkPin : Split40PkPin := split81PkPin
def stA81 (r : Records) (tr₁ : ExecTrace) : TRState :=
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  iniAliceStartState tr₁ r.bob o₁
def bobSeed81 (r : Records) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : DY.Bytes :=
  let x := x81Idx1 r tr₁ tr₂ tr₄ cl₁
  let stA₁ := stA81 r tr₁
  (DY.Libsignal.TripleRatchet.kdfCk (bobChainCk0 r (bobStartKeys r x).rk (DY.DiffieHellman.dhPk stA₁.dhs))).2
def saltedNodes81 (r : Records) (salt : DY.Bytes) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : List DY.Bytes :=
  let seed := bobSeed81 r tr₁ tr₂ tr₄ cl₁
  let stA₁ := stA81 r tr₁
  let w := encWire tr₂ stA₁ cl₁ (tr₂.length + 2)
  let peerIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r 0)
  let myIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)
  let prk := DY.Libsignal.TripleRatchet.hmac salt seed
  let keys := DY.Libsignal.TripleRatchet.trMsgKeys salt seed
  let macFull := DY.Libsignal.TripleRatchet.hmac keys.macKey (DY.Concat.concat peerIk (DY.Concat.concat myIk w))
  let mac := DY.Libsignal.TripleRatchet.computeMac keys.macKey peerIk myIk w
  [prk, keys.cipherKey, keys.macKey, keys.iv, macFull, mac]
def send2Salt81 (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : DY.Bytes := (DY.Spqr.spqrSend (stA40 r tr₁ tr₂ cl₁).spqr (randTerm (tr₃.length + 1) cl₂)).2.1
def ck5Salt81 (r : Records) (tr₄ : ExecTrace) : DY.Bytes :=
  let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  DY.Spqr.spqrChainKey o₂.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1)
def z81Terms (r : Records) (tr₁ tr₂ tr₃ tr₄ : ExecTrace) (cl₁ cl₂ : Nat) : List DY.Bytes := saltedNodes81 r DY.Spqr.zeroKey tr₁ tr₂ tr₄ cl₁ ++ saltedNodes81 r (ck1Salt40 r tr₁) tr₁ tr₂ tr₄ cl₁ ++ saltedNodes81 r (send2Salt81 r tr₁ tr₂ tr₃ cl₁ cl₂) tr₁ tr₂ tr₄ cl₁ ++ saltedNodes81 r (ck5Salt81 r tr₄) tr₁ tr₂ tr₄ cl₁
def preMemo81 (r : Records) (S : Sem) (g : Ghost) (ms' : List Move) : List Row := (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap fun u => (gamma' compI0 S g u).memo
def newMemo81 (r : Records) (S : Sem) (g : Ghost) (ms' : List Move) (p : PreKeyFields) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : List Row := (split81NewTerms r ms' p (x81Idx1 r tr₁ tr₂ tr₄ cl₁)).flatMap fun u => (gamma' compI0 S g u).memo
def bobChainTerms81 (r : Records) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : List DY.Bytes :=
  let x := x81Idx1 r tr₁ tr₂ tr₄ cl₁
  let stA₁ := stA81 r tr₁
  let dhsPub := DY.DiffieHellman.dhPk stA₁.dhs
  let prk := DY.Libsignal.TripleRatchet.hmac (bobStartKeys r x).rk (DY.Libsignal.PQXDH.agree dhsPub (setupSecret r 2))
  let ckSend := (DY.Libsignal.TripleRatchet.createChain (bobStartKeys r x).rk dhsPub (setupSecret r 2)).1
  let ck0 := bobChainCk0 r (bobStartKeys r x).rk dhsPub
  let ck1 := (DY.Libsignal.TripleRatchet.kdfCk ck0).1
  let seed0 := (DY.Libsignal.TripleRatchet.kdfCk ck0).2
  [prk, ckSend, ck0, ck1, seed0]
def Split81ZTagInj : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → (∀ z ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂, (gamma compI0 S g z).take 4 = compTag4) ∧ (∀ a ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂, ∀ b ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂, gamma compI0 S g a = gamma compI0 S g b → a = b)
theorem sound_of_mem_pre_new81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {p : PreKeyFields} {tr₁ tr₂ tr₄ : ExecTrace} {cl₁ : Nat} {x : Row} (hx : x ∈ preMemo81 r S g ms' ++ newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁) : x.2.1 = (gamma' compI0 S g x.1).shape ∧ x.2.2 = gamma compI0 S g x.1 := by rcases List.mem_append.mp hx with h | h <;> exact sound_of_mem_flatMap h
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs

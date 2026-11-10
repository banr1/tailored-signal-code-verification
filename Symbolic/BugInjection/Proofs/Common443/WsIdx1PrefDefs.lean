/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1DecryptNoop
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compKyberE1 compKyberE2 compTag4 compTag4Ipad compTag4Opad)
open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs
def Links40Own (r : Records) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : Prop := ∃ (k₁ k₂ k₃ : Nat) (hb₁ : DY.Libsignal.PQXDH.BundleHandles) (sh₁ s₁ s₂ : Nat), k₁ < k₂ ∧ k₂ < k₃ ∧ runTraceMoves r (ms'.take k₁) = tr₁ ∧ ms'[k₁]? = some (.aliceStart r.alice r.bob 4 6 hb₁ sh₁) ∧ runTraceMoves r (ms'.take k₂) = tr₂ ∧ ms'[k₂]? = some (.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))) ∧ runTraceMoves r (ms'.take k₃) = tr₃ ∧ ms'[k₃]? = some (.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))) ∧ (Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁ = iniAliceStartTr tr₁ r.alice r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) ∧ (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂ = encNextTr tr₂ r.alice s₁ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2) ∧ (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃ = encNextTr tr₃ r.alice s₂ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2)
structure WS40Idx1Pre (r : Records) (S : Sem) (g : Ghost) (ms' : List Move)
    (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : Prop where
  fits : compFitsPinned setup compI0 r
  ex : True
  dn : WsIdx1DecryptNoop.DecryptNoop r ms'
  mp : MatchedPrefix40 r S g ms'
  links : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂
  compat : Compat compI0 r S g
  reach : (runTraceMoves r ms').Reachable reachability
  hent₁ : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = compKyberE1
  hek₁ : gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₁.length 32)) = ek1PubKey
  hwire₂ :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁' := encSt tr₂ (iniAliceStartState tr₁ r.bob o₁) cl₁
    ∀ p, parsePreKeyWire wire3Idx1Bytes = some p →
      gamma compI0 S g (encWire tr₃ stA₁' cl₂ (tr₃.length + 2)) = p.message.take (p.message.length - 8) ∧
      gamma compI0 S g (encMac tr₃ stA₁' cl₂ (tr₃.length + 2)) = p.message.drop (p.message.length - 8) ∧
      gamma compI0 S g (DY.DiffieHellman.dhPk stA₁'.dhs) = p.inner.senderRatchetKey.bytes.toList
  hsalts :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    let stA₁' := encSt tr₂ stA₁ cl₁
    ∀ s ∈ honestSalts r ms',
      s = DY.Spqr.zeroKey ∨
      s = DY.Spqr.spqrChainKey o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1) ∨
      s = (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.1
structure WS40Idx1Fresh (r : Records) (S : Sem) (g : Ghost) (ms' : List Move)
    (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : Prop where
  hdhs₁ : FreshSafeTerm compI0 S g (randTerm (tr₁.length + 2) 32)
  hm₁ : FreshSafeTerm compI0 S g (randTerm tr₂.length 32)
  hm₁_len : (g.σ tr₂.length 32).length ≠ 64
  hcoins₁ : FreshSafeTerm compI0 S g (randTerm (tr₂.length + 1) cl₁)
  hm₂ : FreshSafeTerm compI0 S g (randTerm tr₃.length 32)
  hm₂_len : (g.σ tr₃.length 32).length ≠ 64
  hcoins₂ : FreshSafeTerm compI0 S g (randTerm (tr₃.length + 1) cl₂)
  hpref_safe : ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), FreshSafeTerm compI0 S g u
def Pref40Hyp : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), WS40Idx1Pre r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → WS40Idx1Fresh r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂
def Links81Own (r : Records) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : Prop := CompSetupSecrecy.NoBrk r ms' ∧ ∃ (k₁ k₂ k₃ k₄ k₅ : Nat) (hb₁ hb₄ : DY.Libsignal.PQXDH.BundleHandles) (sh₁ sh₄ s₁ s₂ s₅ : Nat), k₁ < k₂ ∧ k₂ < k₃ ∧ k₃ < k₄ ∧ k₄ < k₅ ∧ runTraceMoves r (ms'.take k₁) = tr₁ ∧ ms'[k₁]? = some (.aliceStart r.alice r.bob 4 6 hb₁ sh₁) ∧ runTraceMoves r (ms'.take k₂) = tr₂ ∧ ms'[k₂]? = some (.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))) ∧ runTraceMoves r (ms'.take k₃) = tr₃ ∧ ms'[k₃]? = some (.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))) ∧ runTraceMoves r (ms'.take k₄) = tr₄ ∧ ms'[k₄]? = some (.aliceStart r.alice r.bob 4 6 hb₄ sh₄) ∧ runTraceMoves r (ms'.take k₅) = tr₅ ∧ ms'[k₅]? = some (.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4))) ∧ (Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁ = iniAliceStartTr tr₁ r.alice r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) ∧ (Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄).next tr₄ = iniAliceStartTr tr₄ r.alice r.bob (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) ∧ (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₂ = encNextTr tr₂ r.alice s₁ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2) ∧ (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4))).next tr₃ = encNextTr tr₃ r.alice s₂ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2) ∧ (Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4))).next tr₅ = encNextTr tr₅ r.alice s₅ (iniAliceStartState tr₄ r.bob (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₅ (tr₅.length + 2)
structure WS81Idx1Pre (r : Records) (S : Sem) (g : Ghost) (ms' : List Move)
    (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : Prop where
  fits : compFitsPinned setup compI0 r
  ex : CompSetupSecrecy.NoBrk r ms'
  dn : WsIdx1DecryptNoop.DecryptNoop r ms'
  mp : MatchedPrefix81 r S g ms'
  links : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅
  compat : Compat compI0 r S g
  reach : (runTraceMoves r ms').Reachable reachability
  hent₁ : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = compKyberE1
  hek₁ : gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₁.length 32)) = ek1PubKey
  hek₂ : gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₄.length 32)) = ek2PubKey
  hent₂ : gamma compI0 S g (randTerm (tr₄.length + 1) 32) = compKyberE2
  hwire₁ :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    ∀ p, parsePreKeyWire wire6Idx1Bytes = some p →
      gamma compI0 S g (encWire tr₂ stA₁ cl₁ (tr₂.length + 2)) = p.message.take (p.message.length - 8) ∧
      gamma compI0 S g (encMac tr₂ stA₁ cl₁ (tr₂.length + 2)) = p.message.drop (p.message.length - 8) ∧
      gamma compI0 S g (DY.DiffieHellman.dhPk stA₁.dhs) = p.inner.senderRatchetKey.bytes.toList
  hsalts :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    let stA₁' := encSt tr₂ stA₁ cl₁
    let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    ∀ s ∈ honestSalts r ms',
      s = DY.Spqr.zeroKey ∨
      s = DY.Spqr.spqrChainKey o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1) ∨
      s = (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.1 ∨
      s = DY.Spqr.spqrChainKey o₂.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1)
structure WS81Idx1Fresh (r : Records) (S : Sem) (g : Ghost) (ms' : List Move)
    (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : Prop where
  hdhs₁ : FreshSafeTerm compI0 S g (randTerm (tr₁.length + 2) 32)
  hm₁ : FreshSafeTerm compI0 S g (randTerm tr₂.length 32)
  hm₁_len : (g.σ tr₂.length 32).length ≠ 64
  hcoins₁ : FreshSafeTerm compI0 S g (randTerm (tr₂.length + 1) cl₁)
  hm₂ : FreshSafeTerm compI0 S g (randTerm tr₃.length 32)
  hm₂_len : (g.σ tr₃.length 32).length ≠ 64
  hcoins₂ : FreshSafeTerm compI0 S g (randTerm (tr₃.length + 1) cl₂)
  hek₂_safe : FreshSafeTerm compI0 S g (randTerm tr₄.length 32)
  hent₂_safe : FreshSafeTerm compI0 S g (randTerm (tr₄.length + 1) 32)
  hpref_safe : ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), FreshSafeTerm compI0 S g u
def Pref81Idx1Hyp : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), WS81Idx1Pre r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → WS81Idx1Fresh r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅
end Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs

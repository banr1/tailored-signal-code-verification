/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26WeakStateIdx1
public import Symbolic.BugInjection.Proofs.Common443.Census443Defs

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compKyberE1 compKyberE2 compTag4 compTag4Ipad compTag4Opad)
open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs
abbrev wsIdx1Trace : List MachineEvent := Witnesses.Cheval26WeakStateIdx1.trace
def recvAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.recv b) => b | _ => []
def ptAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.pt b) => b | _ => []
def sendAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.send b) => b | _ => []
abbrev wire3Idx1Bytes : HwBytes := recvAt 40
abbrev wire6Idx1Bytes : HwBytes := recvAt 81
def x40Idx1 (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : PreKeyRep :=
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁' := encSt tr₂ (iniAliceStartState tr₁ r.bob o₁) cl₁
  ⟨o₁.ek, o₁.ct, encOut tr₃ stA₁' cl₂ (tr₃.length + 2)⟩
def x81Idx1 (r : Records) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : PreKeyRep :=
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := iniAliceStartState tr₁ r.bob o₁
  let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  ⟨o₂.ek, o₂.ct, encOut tr₂ stA₁ cl₁ (tr₂.length + 2)⟩
def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
def ek1PubKey : HwBytes := hexBytes.go hexDigit ['8', 'f', '0', '7', '7', 'b', '9', '9', 'c', 'f', '1', '8', '8', '2', '1', 'e', 'e', '2', 'a', 'e', '9', '6', '5', 'c', '8', '1', 'e', '4', '8', '9', 'c', '1', '7', 'b', 'e', '9', '2', 'f', '1', 'e', 'e', '6', '9', '8', '2', '4', '6', '8', '8', '5', '2', 'd', 'a', 'a', '2', '5', 'f', '2', 'd', '0', '7', '6', '3', '8']
def ek2PubKey : HwBytes := hexBytes.go hexDigit ['9', '7', 'a', '8', '5', 'f', 'f', 'b', '6', 'd', '6', '2', 'c', 'c', '5', 'f', '2', '1', 'b', '0', 'a', '4', '8', '1', '8', '0', '1', '2', '2', '4', '9', 'f', 'c', '4', '6', 'f', 'c', 'b', '2', '5', 'e', 'e', '2', 'd', '1', '8', '9', '6', 'e', 'c', 'c', 'c', '2', 'e', '3', '5', 'f', '5', '3', '3', '1', '9', '1', '9']
def cliCoins2Fast : HwBytes := hexBytes.go hexDigit ['6', '7', '6', '9', 'f', '5', 'a', '2', '6', 'b', '9', '7', '2', 'f', 'f', 'c', 'b', '5', 'e', 'c', 'b', 'c', 'd', 'b', '5', 'c', 'b', '2', '5', '7', '7', '3', 'b', 'c', '2', 'f', '2', 'b', 'a', 'd', '9', '3', 'f', '9', '0', 'a', 'c', '9', '5', 'a', '0', '8', '3', '7', 'b', '8', '3', '1', 'd', 'b', 'c', '2', '2', 'b', 'f', 'd', '0', '8', '6', 'e', 'b', '7', '3', '1', 'e', '0', '6', '5', '6', '9', '7', '7', 'e', '4', '8', '1', '5', '9', 'f', '2', '7', '3', '3', '5', '9', 'c', 'b', '6', '5', '2', '1', '8', '7', '0', 'f', '8', '2', '7', '0', 'd', '3', '1', 'c', '7', 'e', '8', 'f', 'c', '0', 'a', 'd', '6', 'c', '7', '2', 'a', '2', '7']
def seg38SplitSrc : List MachineEvent := [.pt (ptAt 38), .rng cliCoins2Fast, .send (sendAt 39)]
theorem coinSplit_seg38_self : DY.Libsignal.Composed.Refinement.Cli.CoinSplit seg38SplitSrc (wsIdx1Trace.drop 38 |>.take 2) :=
  .keep (fun _ h => nomatch h) (.split (pieces := []) (fun _ h => nomatch h) (List.nil_prefix) (.keep (fun _ h => nomatch h) .nil))
def IsSetupFresh64Tag (t : Nat) : Prop := t = 11 ∨ t = 16 ∨ t = 17
def FreshSafeTerm (i : ExternInterpretation) (S : Sem) (g : Ghost) (term : DY.Bytes) : Prop := ∀ x ∈ (gamma' i S g term).memo, (∀ t, IsSetupFresh64Tag t → x.2.2 = fillFresh t 64 → x.1 = randTerm t 64 ∧ x.2.1 = randTerm t 64) ∧ (∀ r : DY.Random.Random DY.Bytes, x.1 = r.pack → x.2.2.take 4 ≠ compTag4 ∧ x.2.2.take 4 ≠ compTag4Ipad ∧ x.2.2.take 4 ≠ compTag4Opad)
def MatchedPrefix40 (r : Records) (S : Sem) (g : Ghost) (ms' : List Move) : Prop :=
  Compat compI0 r S g ∧ ModelRun r ms' ∧ True ∧ True ∧ True ∧
  ∃ b1 b2, DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 35 |>.take 3) b1 ∧
    DY.Libsignal.Composed.Refinement.Cli.CoinSplit seg38SplitSrc b2 ∧
    MatchedPrefix compI0 r S who g ms' ((wsIdx1Trace.take 35 ++ b1) ++ b2)
def MatchedPrefix81 (r : Records) (S : Sem) (g : Ghost) (ms' : List Move) : Prop :=
  Compat compI0 r S g ∧ ModelRun r ms' ∧ True ∧ True ∧ True ∧
  ∃ b1 b2 b5,
    DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 35 |>.take 3) b1 ∧
    DY.Libsignal.Composed.Refinement.Cli.CoinSplit seg38SplitSrc b2 ∧
    DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 78 |>.take 3) b5 ∧
    MatchedPrefix compI0 r S who g ms'
      (((((wsIdx1Trace.take 35 ++ b1) ++ b2) ++
        (wsIdx1Trace.drop 40 |>.take 3)) ++ (wsIdx1Trace.drop 43 |>.take 35)) ++ b5)
theorem matchedPrefix40_of_split2 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {b1 b2 : List MachineEvent}
    (hcs1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 35 |>.take 3) b1)
    (hcs2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit seg38SplitSrc b2)
    (hmp : MatchedPrefix compI0 r S who g ms' ((wsIdx1Trace.take 35 ++ b1) ++ b2)) :
    MatchedPrefix40 r S g ms' :=
  ⟨hmp.1, hmp.2.1, trivial, trivial, trivial, ⟨b1, b2, hcs1, hcs2, hmp⟩⟩
theorem matchedPrefix40_of_split {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {b1 : List MachineEvent}
    (hcs1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 35 |>.take 3) b1)
    (hmp : MatchedPrefix compI0 r S who g ms' ((wsIdx1Trace.take 35 ++ b1) ++ (wsIdx1Trace.drop 38 |>.take 2))) :
    MatchedPrefix40 r S g ms' :=
  matchedPrefix40_of_split2 hcs1 coinSplit_seg38_self hmp
theorem matchedPrefix81_of_split3 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {b1 b2 b5 : List MachineEvent}
    (hcs1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 35 |>.take 3) b1)
    (hcs2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit seg38SplitSrc b2)
    (hcs5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 78 |>.take 3) b5)
    (hmp : MatchedPrefix compI0 r S who g ms'
      (((((wsIdx1Trace.take 35 ++ b1) ++ b2) ++
        (wsIdx1Trace.drop 40 |>.take 3)) ++ (wsIdx1Trace.drop 43 |>.take 35)) ++ b5)) :
    MatchedPrefix81 r S g ms' :=
  ⟨hmp.1, hmp.2.1, trivial, trivial, trivial, ⟨b1, b2, b5, hcs1, hcs2, hcs5, hmp⟩⟩
theorem matchedPrefix81_of_split {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {b1 b5 : List MachineEvent}
    (hcs1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 35 |>.take 3) b1)
    (hcs5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (wsIdx1Trace.drop 78 |>.take 3) b5)
    (hmp : MatchedPrefix compI0 r S who g ms'
      (((((wsIdx1Trace.take 35 ++ b1) ++ (wsIdx1Trace.drop 38 |>.take 2)) ++
        (wsIdx1Trace.drop 40 |>.take 3)) ++ (wsIdx1Trace.drop 43 |>.take 35)) ++ b5)) :
    MatchedPrefix81 r S g ms' :=
  matchedPrefix81_of_split3 hcs1 coinSplit_seg38_self hcs5 hmp
structure WS40Idx1RunInv (r : Records) (S : Sem) (g : Ghost) (ms' : List Move)
    (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : Prop where
  mp : MatchedPrefix40 r S g ms'
  links : ∃ (k₁ k₂ k₃ : Nat) (hb₁ : DY.Libsignal.PQXDH.BundleHandles) (sh₁ s₁ s₂ pq₁ pq₂ : Nat)
      (w₁ w₂ : Option (Nat × Nat)),
    k₁ < k₂ ∧ k₂ < k₃ ∧
    runTraceMoves r (ms'.take k₁) = tr₁ ∧ ms'[k₁]? = some (.aliceStart r.alice r.bob 4 6 hb₁ sh₁) ∧
    runTraceMoves r (ms'.take k₂) = tr₂ ∧ ms'[k₂]? = some (.encrypt r.alice s₁ cl₁ pq₁ w₁) ∧
    runTraceMoves r (ms'.take k₃) = tr₃ ∧ ms'[k₃]? = some (.encrypt r.alice s₂ cl₂ pq₂ w₂) ∧
    (Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁ =
      iniAliceStartTr tr₁ r.alice r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) ∧
    pq₁ = tr₂.length + 2 ∧ pq₂ = tr₃.length + 2 ∧
    (Move.encrypt r.alice s₁ cl₁ pq₁ w₁).next tr₂ =
      encNextTr tr₂ r.alice s₁ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2) ∧
    (Move.encrypt r.alice s₂ cl₂ pq₂ w₂).next tr₃ =
      encNextTr tr₃ r.alice s₂ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2)
  compat : Compat compI0 r S g
  reach : (runTraceMoves r ms').Reachable reachability
  hent₁ : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = compKyberE1
  hek₁ : gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₁.length 32)) = ek1PubKey
  hdhs₁ : FreshSafeTerm compI0 S g (randTerm (tr₁.length + 2) 32)
  hm₁ : FreshSafeTerm compI0 S g (randTerm tr₂.length 32)
  hm₁_len : (g.σ tr₂.length 32).length ≠ 64
  hcoins₁ : FreshSafeTerm compI0 S g (randTerm (tr₂.length + 1) cl₁)
  hm₂ : FreshSafeTerm compI0 S g (randTerm tr₃.length 32)
  hm₂_len : (g.σ tr₃.length 32).length ≠ 64
  hcoins₂ : FreshSafeTerm compI0 S g (randTerm (tr₃.length + 1) cl₂)
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
  hpref_safe : ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), FreshSafeTerm compI0 S g u
structure WS81Idx1RunInv (r : Records) (S : Sem) (g : Ghost) (ms' : List Move)
    (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : Prop where
  mp : MatchedPrefix81 r S g ms'
  links : ∃ (k₁ k₂ k₃ k₄ k₅ : Nat) (hb₁ hb₄ : DY.Libsignal.PQXDH.BundleHandles) (sh₁ sh₄ s₁ s₂ s₅ pq₁ pq₂ pq₅ : Nat)
      (w₁ w₂ w₅ : Option (Nat × Nat)),
    k₁ < k₂ ∧ k₂ < k₃ ∧ k₃ < k₄ ∧ k₄ < k₅ ∧
    runTraceMoves r (ms'.take k₁) = tr₁ ∧ ms'[k₁]? = some (.aliceStart r.alice r.bob 4 6 hb₁ sh₁) ∧
    runTraceMoves r (ms'.take k₂) = tr₂ ∧ ms'[k₂]? = some (.encrypt r.alice s₁ cl₁ pq₁ w₁) ∧
    runTraceMoves r (ms'.take k₃) = tr₃ ∧ ms'[k₃]? = some (.encrypt r.alice s₂ cl₂ pq₂ w₂) ∧
    runTraceMoves r (ms'.take k₄) = tr₄ ∧ ms'[k₄]? = some (.aliceStart r.alice r.bob 4 6 hb₄ sh₄) ∧
    runTraceMoves r (ms'.take k₅) = tr₅ ∧ ms'[k₅]? = some (.encrypt r.alice s₅ cl₅ pq₅ w₅) ∧
    (Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁ =
      iniAliceStartTr tr₁ r.alice r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) ∧
    (Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄).next tr₄ =
      iniAliceStartTr tr₄ r.alice r.bob (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) ∧
    pq₁ = tr₂.length + 2 ∧ pq₂ = tr₃.length + 2 ∧ pq₅ = tr₅.length + 2 ∧
    (Move.encrypt r.alice s₁ cl₁ pq₁ w₁).next tr₂ =
      encNextTr tr₂ r.alice s₁ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2) ∧
    (Move.encrypt r.alice s₂ cl₂ pq₂ w₂).next tr₃ =
      encNextTr tr₃ r.alice s₂ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2) ∧
    (Move.encrypt r.alice s₅ cl₅ pq₅ w₅).next tr₅ =
      encNextTr tr₅ r.alice s₅ (iniAliceStartState tr₄ r.bob (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₅ (tr₅.length + 2)
  compat : Compat compI0 r S g
  reach : (runTraceMoves r ms').Reachable reachability
  hent₁ : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = compKyberE1
  hek₁ : gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₁.length 32)) = ek1PubKey
  hdhs₁ : FreshSafeTerm compI0 S g (randTerm (tr₁.length + 2) 32)
  hm₁ : FreshSafeTerm compI0 S g (randTerm tr₂.length 32)
  hm₁_len : (g.σ tr₂.length 32).length ≠ 64
  hcoins₁ : FreshSafeTerm compI0 S g (randTerm (tr₂.length + 1) cl₁)
  hm₂ : FreshSafeTerm compI0 S g (randTerm tr₃.length 32)
  hm₂_len : (g.σ tr₃.length 32).length ≠ 64
  hcoins₂ : FreshSafeTerm compI0 S g (randTerm (tr₃.length + 1) cl₂)
  hek₂_safe : FreshSafeTerm compI0 S g (randTerm tr₄.length 32)
  hek₂ : gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₄.length 32)) = ek2PubKey
  hent₂_safe : FreshSafeTerm compI0 S g (randTerm (tr₄.length + 1) 32)
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
  hpref_safe : ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), FreshSafeTerm compI0 S g u
def NoBscAt40 : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup compI0 r → ExplainsMoves compI0 r S who ok g ms (wsIdx1Trace.take 40) → parsePreKeyWire (recvAt 40) = some p → ∃ g' ms', ExplainsMoves compI0 r S who ok g' ms' (wsIdx1Trace.take 40) ∧ ¬ ReadCollision compI0 r S g' ms' (wsIdx1Trace.take 40) ∧ ∃ x ∈ preKeyRepresentations compI0 r S g' ms' (recvAt 40), ¬ BobStartCollision compI0 r S g' ms' p x
def NoBscAt81 : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup compI0 r → ExplainsMoves compI0 r S who ok g ms (wsIdx1Trace.take 81) → parsePreKeyWire (recvAt 81) = some p → ∃ g' ms', ExplainsMoves compI0 r S who ok g' ms' (wsIdx1Trace.take 81) ∧ ¬ ReadCollision compI0 r S g' ms' (wsIdx1Trace.take 81) ∧ ∃ x ∈ preKeyRepresentations compI0 r S g' ms' (recvAt 81), ¬ BobStartCollision compI0 r S g' ms' p x
end Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs

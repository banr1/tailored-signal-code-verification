/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Core
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Aux

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents
open DY.Libsignal (HwBytes) open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Core Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Aux Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
theorem rngAt79_ne_nil : rngAt 79 ≠ [] := by decide +kernel
theorem coinSplit_seg78_self :
    DY.Libsignal.Composed.Refinement.Cli.CoinSplit
      (WsIdx1CensusDefs.wsIdx1Trace.drop 78 |>.take 3)
      (WsIdx1CensusDefs.wsIdx1Trace.drop 78 |>.take 3) := by
  show DY.Libsignal.Composed.Refinement.Cli.CoinSplit
    [.pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)]
    [.pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)]
  exact .keep (fun _ h => nomatch h)
    (.split (pieces := [rngAt 79])
      (fun d hd => (List.mem_singleton.mp hd) ▸ rngAt79_ne_nil)
      (WsIdx1Decomp40.singleton_flatten_prefix (rngAt 79)) (.keep (fun _ h => nomatch h) .nil))

theorem split81_pre_split {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields}
    {b1 b2 b5 : List MachineEvent}
    (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 r)
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (WsIdx1CensusDefs.wsIdx1Trace.drop 35 |>.take 3) b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2)
    (hc5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (WsIdx1CensusDefs.wsIdx1Trace.drop 78 |>.take 3) b5)
    (hex : DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms
      (((((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 40 |>.take 3)) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 43 |>.take 35)) ++ b5))
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hp : parsePreKeyWire WsIdx1CensusDefs.wire6Idx1Bytes = some p) :
    ∃ (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat),
      DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms'
        (((((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 40 |>.take 3)) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 43 |>.take 35)) ++ b5) ∧
      (∃ P₁ mid₂ P₂ post₅ me s₁ pq₁ s₂ pq₂ s₅ pq₅ w₁ w₂ w₅ w₁' w₂' w₅',
        ms = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅ :: post₅ ∧
        ms' = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁' :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂' :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅' :: post₅) ∧
      WsIdx1PrefDefs.WS81Idx1Pre r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ∧
      WsIdx1CensusDefs.x81Idx1 r tr₁ tr₂ tr₄ cl₁ ∈ preKeyRepresentations compI0 r S g ms' WsIdx1CensusDefs.wire6Idx1Bytes := by
  obtain ⟨pre₀, mid₁, mid₂, mid₃, mid₄, mid₅, post₅, hb₀, hb₄, sh₀, sh₄, cl₁, e₁, c₁, cl₂, e₂, c₂, cl₅, e₅, c₅, b_bob, a_bob, kh, regIdxA, mh, pqIdx, spqrMsgIdx, sh_bob, tr₁, tr₂, tr₃, tr_bob, tr₄, tr₅, _w_bob, o₁, o₂, stA₁, stA₂, htr₁, ho₁, hstA₁, htr₂, htr₃, htr_bob, htr₄, ho₂, hstA₂, htr₅, hms, hm₀, hE₁, hE₂, _hnext_bob, hm₄, hE₅, hpre₀, hmid₁, hmid₂, hmid₃, hmid₄, hmid₅, hpost₅,
    hek₁, hct₁, hek₂, hct₂, hvis₀, hvis₄, hsm₁, hsm₂, hsm₅⟩ :=
    decomp81_full hfits hnb hc1 hc2 hc5 (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hex.1)
  exact split81_pre_of_parts hfits hc1 hc2 hc5 hex hnb hp
    (m₃ := Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob)
    rfl (fun _ _ _ _ _ h => nomatch h) htr₁ ho₁ hstA₁ htr₂ htr₃ htr_bob htr₄ ho₂ hstA₂ htr₅
    hms hm₀ hE₁ hE₂ hm₄ hE₅ hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅
    hek₁ hct₁ hek₂ hct₂ hvis₀ hvis₄ hsm₁ hsm₂ hsm₅

theorem split81_pre {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields} (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 r) (hex : DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms (WsIdx1CensusDefs.wsIdx1Trace.take 81)) (hnb : CompSetupSecrecy.NoBrk r ms) (hp : parsePreKeyWire WsIdx1CensusDefs.wire6Idx1Bytes = some p) : ∃ (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms' (WsIdx1CensusDefs.wsIdx1Trace.take 81) ∧ WsIdx1PrefDefs.WS81Idx1Pre r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ∧ WsIdx1CensusDefs.x81Idx1 r tr₁ tr₂ tr₄ cl₁ ∈ preKeyRepresentations compI0 r S g ms' WsIdx1CensusDefs.wire6Idx1Bytes := by
  obtain ⟨ms', tr₁, tr₂, tr₃, tr₄, tr₅, cl₁, cl₂, cl₅, hex', _, hP, hmem⟩ :=
    split81_pre_split hfits WsIdx1Decomp40.coinSplit_seg35_self WsIdx1CensusDefs.coinSplit_seg38_self coinSplit_seg78_self hex hnb hp
  exact ⟨ms', tr₁, tr₂, tr₃, tr₄, tr₅, cl₁, cl₂, cl₅, hex', hP, hmem⟩

theorem split81DecompSwapRep_split_of {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields}
    {b1 b2 b5 : List MachineEvent}
    (hpref : WsIdx1PrefDefs.Pref81Idx1Hyp)
    (hfits : compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.setup compI0 r)
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (WsIdx1CensusDefs.wsIdx1Trace.drop 35 |>.take 3) b1)
    (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2)
    (hc5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit (WsIdx1CensusDefs.wsIdx1Trace.drop 78 |>.take 3) b5)
    (hex : DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms
      (((((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 40 |>.take 3)) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 43 |>.take 35)) ++ b5))
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hp : parsePreKeyWire WsIdx1CensusDefs.wire6Idx1Bytes = some p) :
    ∃ (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat),
      DY.Libsignal.Composed.Refinement.ExplainsMoves compI0 r S Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.who Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.ok g ms'
        (((((WsIdx1CensusDefs.wsIdx1Trace.take 35 ++ b1) ++ b2) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 40 |>.take 3)) ++ (WsIdx1CensusDefs.wsIdx1Trace.drop 43 |>.take 35)) ++ b5) ∧
      (∃ P₁ mid₂ P₂ post₅ me s₁ pq₁ s₂ pq₂ s₅ pq₅ w₁ w₂ w₅ w₁' w₂' w₅',
        ms = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅ :: post₅ ∧
        ms' = P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁' :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂' :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅' :: post₅) ∧
      WsIdx1DecryptNoop.DecryptNoop r ms' ∧
      WsIdx1CensusDefs.WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ∧
      WsIdx1PrefDefs.Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ ∧
      WsIdx1CensusDefs.x81Idx1 r tr₁ tr₂ tr₄ cl₁ ∈ preKeyRepresentations compI0 r S g ms' WsIdx1CensusDefs.wire6Idx1Bytes :=
  split81DecompSwapRep_split_of_pre hpref (split81_pre_split hfits hc1 hc2 hc5 hex hnb hp)

theorem split81DecompSwapRepOwn_of (hpref : WsIdx1PrefDefs.Pref81Idx1Hyp) : WsIdx1CensusOwn.Split81DecompSwapRepOwn := by
  intro r S g ms p hfits hex hnb hp
  obtain ⟨ms', tr₁, tr₂, tr₃, tr₄, tr₅, cl₁, cl₂, cl₅, hex', _, hdn, hinv, hlinks, hmem⟩ :=
    split81DecompSwapRep_split_of hpref hfits WsIdx1Decomp40.coinSplit_seg35_self WsIdx1CensusDefs.coinSplit_seg38_self coinSplit_seg78_self hex hnb hp
  exact ⟨ms', tr₁, tr₂, tr₃, tr₄, tr₅, cl₁, cl₂, cl₅, hex', hdn, hinv, hlinks, hmem⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81

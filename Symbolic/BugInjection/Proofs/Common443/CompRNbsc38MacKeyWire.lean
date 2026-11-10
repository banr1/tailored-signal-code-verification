/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire
public import Symbolic.BugInjection.Proofs.Common443.CompRX0SS38

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKeyWire
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
private theorem encMac_eq' (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : encMac tr₂ stA cl pq = DY.Libsignal.TripleRatchet.computeMac (encKeys tr₂ stA cl pq).macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq) :=
  rfl
theorem split38_encMac_chain {r : Records} {S : Sem} {g : Ghost} (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl e c' : Nat} (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c'))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob (iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) {bun b₀ pt c wire k P : HwBytes} {rs' : List MachineEvent} (hrs' : rs'.length = 33) (hwlen : wire.length < 2 ^ 63) (hok : wireMacChainOk k P wire = true) (hvis : List.Forall₂ (EventMatchesEntry compI0 r S g) ((.recv bun :: .rng b₀ :: rs') ++ [.pt pt, .rng c, .send wire]) (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c')) :: post))) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let tr₂ := (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o;
    gamma compI0 S g (encKeys tr₂ stA cl (tr₂.length + 2)).macKey = k ∧ gamma compI0 S g (encPrk tr₂ stA cl (tr₂.length + 2)) = P ∧ k ∈ compHmacKeys32 ∧ P ∈ compHmacKeys32 ∧ (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₂ stA cl (tr₂.length + 2)).macKey (Concat.concat stA.myIk (Concat.concat stA.peerIk (encWire tr₂ stA cl (tr₂.length + 2)))))).take 4 ≠ compTag4 ∧
      (gamma compI0 S g (encKeys tr₂ stA cl (tr₂.length + 2)).macKey).take 4 ≠ compTag4 := by
  intro tr₁ o tr₂ stA; obtain ⟨_, hm₁⟩ := split38_forall2_vis_inv hNe (o := o) rfl hpre hmid hpost hm₀ hrs' hvis
  cases hq : parsePreKeyWire wire with
  | none =>
    unfold wireMacChainOk at hok; rw [hq] at hok; exact absurd hok Bool.false_ne_true
  | some q₀ =>
    have hpq := macChainOk_of_wire hok hq; obtain ⟨_, _, _, hmsg⟩ := encVis_split38_pins hwlen hq hm₁; have hmac : gamma compI0 S g (encMac tr₂ stA cl (tr₂.length + 2)) = msgMac8 q₀ := (gamma_encWire_mac_of_encOut hmsg).2; obtain ⟨hk, hP, hkK, hPK⟩ := encMac_chain_of_macChainOk S g tr₂ stA cl _ hmac hpq; have h3 := (macChainOk_spec hpq).2.2.1
    have hu1 : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₂ stA cl (tr₂.length + 2)).macKey (Concat.concat stA.myIk (Concat.concat stA.peerIk (encWire tr₂ stA cl (tr₂.length + 2)))))).take 4 ≠
        compTag4 := by
      have h := hmac ▸ (macChainOk_spec hpq).1; rw [encMac_eq', gamma_computeMac, take4_take8] at h; exact h
    exact ⟨hk, hP, hkK, hPK, hu1, by rw [hk]; exact h3⟩
end Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKeyWire

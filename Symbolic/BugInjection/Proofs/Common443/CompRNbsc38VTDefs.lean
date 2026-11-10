/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38
public import Symbolic.BugInjection.Proofs.Common443.CompRPlantWire
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
def zeroSaltedTermsStA (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : List DY.Bytes :=
  let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2; let zprk := DY.Libsignal.TripleRatchet.hmac DY.Spqr.zeroKey seed; let zkeys := DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey seed;
  let zmac_full := DY.Libsignal.TripleRatchet.hmac zkeys.macKey
    (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr₂ stA cl pq)));
  let zmac := DY.Libsignal.TripleRatchet.computeMac zkeys.macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq);
  [zprk, zkeys.cipherKey, zkeys.macKey, zkeys.iv, zmac_full, zmac]
end Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc
namespace Symbolic.BugInjection.Proofs.Common443.CompRNbsc38VT
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse
open Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct (gamma_concat_eq gamma_trunc8_eq)
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRPlantWire Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def MemoPairCollides (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) : Prop := x₁.2.1 ≠ x₂.2.1 ∧ (assumedInjective x₁.1 ∨ assumedInjective x₂.1) ∧ (x₁.1 ∈ pts → x₂.1 ∉ pts ∧ assumedInjective x₂.1 ∧ ¬ known x₂.1) ∧ (x₂.1 ∈ pts → x₁.1 ∉ pts ∧ assumedInjective x₁.1 ∧ ¬ known x₁.1) ∧ x₁.2.2 = x₂.2.2
theorem not_memoCollisionOn_of_no_pair_collides {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {known : DY.Bytes → Prop} {tr : ExecTrace} {vis : List VisEntry} {newTerms newPts : List DY.Bytes} (h : ∀ x₁ ∈ newTerms.flatMap (fun t => (gamma' i S g t).memo), ∀ x₂ ∈ (prefixTerms r tr vis).flatMap (fun t => (gamma' i S g t).memo) ++ newTerms.flatMap (fun t => (gamma' i S g t).memo), ¬ MemoPairCollides known (plaintextTerms vis ++ newPts) x₁ x₂) : ¬ MemoCollisionOn i r S g known tr vis newTerms newPts := by rintro ⟨x₁, hx₁, x₂, hx₂, hcol⟩; exact h x₁ hx₁ x₂ hx₂ hcol
theorem gamma_encMac_length (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : (gamma compI0 S g (encMac tr₂ stA cl pq)).length = 8 := by unfold encMac DY.Libsignal.TripleRatchet.computeMac; rw [gamma_trunc8_eq, List.length_take, CompRNbsc38MacKey.gamma_hmac_length]; decide
theorem gamma_encWire_mac_of_encOut {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {msg : HwBytes} (h : gamma compI0 S g (encOut tr₂ stA cl pq) = msg) : gamma compI0 S g (encWire tr₂ stA cl pq) = msg.take (msg.length - 8) ∧ gamma compI0 S g (encMac tr₂ stA cl pq) = msg.drop (msg.length - 8) := by
  unfold encOut at h; rw [gamma_concat_eq] at h; have hmac_len : (gamma compI0 S g (encMac tr₂ stA cl pq)).length = 8 := gamma_encMac_length S g tr₂ stA cl pq
  have hlen : msg.length - 8 = (gamma compI0 S g (encWire tr₂ stA cl pq)).length := by rw [← h, List.length_append, hmac_len]; omega
  rw [hlen, ← h]; exact ⟨(List.take_left' rfl).symm, (List.drop_left' rfl).symm⟩
def Split38MemoClass (r : Records) (S : Sem) (g : Ghost) (ms' : List Move) (tr₁ tr₂ : ExecTrace) (cl : Nat) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop :=
  let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let stA := iniAliceStartState tr₁ r.bob o;
  x ∈ (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap (fun u => (gamma' compI0 S g u).memo) ∨
  assumedInjective x.1 = false ∨ x.1 ∈ zeroSaltedTermsStA tr₂ stA cl (tr₂.length + 2)
def Split38NoClassifiedCollisionAtVT (w : PQXDHSpqrSetup) (τ : List MachineEvent) (wire : HwBytes) (v : Fin 4) (t : Fin 8) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields), compFitsPinned w compI0 r → parsePreKeyWire wire = some p → p.preKeyId = none → ∀ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl pq⟩;
      Compat compI0 r S g → ModelRun r ms → List.Forall₂ (EventMatchesEntry compI0 r S g) τ (runVis r ms) → MovesFrom InvisibleNoEffect (setupTrace r) pre →
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
      MovesFrom InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c'))).next tr₂) post →
      m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o →
      bobDoneBaseKeys (runTraceMoves r ms) = [] →
      let memo := fun u => (gamma' compI0 S g u).memo;
      let preMemo := (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap memo; let newMemo := ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀).flatMap memo;
      let known := fun u : DY.Bytes => u.AttackerKnows (runTraceMoves r ms');
      let pts := plaintextTerms (runVis r ms');
      ∀ x₁ ∈ newMemo, ∀ x₂ ∈ preMemo ++ newMemo, Split38MemoClass r S g ms' tr₁ tr₂ cl x₁ → Split38MemoClass r S g ms' tr₁ tr₂ cl x₂ → ¬ MemoPairCollides known pts x₁ x₂
abbrev Split38NoClassifiedCollisionHBVT : Prop := Split38NoClassifiedCollisionAtVT Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev Split38NoClassifiedCollisionTCVT : Prop := Split38NoClassifiedCollisionAtVT Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
end Symbolic.BugInjection.Proofs.Common443.CompRNbsc38VT

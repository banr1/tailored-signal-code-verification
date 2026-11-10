/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRNbsc38VT
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRPlantWire Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
private def wireHopkIdx1 (b : HwBytes) : Bool :=
  match parsePreKeyWire b with
  | some p => decide (p.preKeyId = none) && decide (spqrIdx p = 1)
  | none => false
private theorem wireHopkIdx1_spec {b : HwBytes} (h : wireHopkIdx1 b = true) {p : PreKeyFields} (hp : parsePreKeyWire b = some p) : p.preKeyId = none ∧ spqrIdx p = 1 := by unfold wireHopkIdx1 at h; rw [hp] at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h
private theorem wireHopkIdx1_highBitFast : wireHopkIdx1 highBitWireFast = true := by decide +kernel
private theorem wireHopkIdx1_torsionFast : wireHopkIdx1 torsionWireFast = true := by decide +kernel
theorem highBitWireBytes_hopk_hidx' {p : PreKeyFields} (hp : parsePreKeyWire highBitWireBytes = some p) : p.preKeyId = none ∧ (spqrIdx p = 0 ∨ spqrIdx p = 1) := by
  have hb : wireHopkIdx1 highBitWireBytes = true := by rw [highBitWireBytes_eq]; exact wireHopkIdx1_highBitFast
  obtain ⟨hopk, hidx⟩ := wireHopkIdx1_spec hb hp; exact ⟨hopk, Or.inr hidx⟩
theorem torsionWireBytes_hopk_hidx' {p : PreKeyFields} (hp : parsePreKeyWire torsionWireBytes = some p) : p.preKeyId = none ∧ (spqrIdx p = 0 ∨ spqrIdx p = 1) := by
  have hb : wireHopkIdx1 torsionWireBytes = true := by rw [torsionWireBytes_eq]; exact wireHopkIdx1_torsionFast
  obtain ⟨hopk, hidx⟩ := wireHopkIdx1_spec hb hp; exact ⟨hopk, Or.inr hidx⟩
def HmcAt38 (r : Records) (S : Sem) (g : Ghost) (v : Fin 4) (t : Fin 8) (τ₁ : List MachineEvent) (p : PreKeyFields) : Prop := ∀ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
    let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o; let ms := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post;
    let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2)
        (some (tr₁.length + 3, tr₁.length + 4)) :: post;
    let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl (tr₂.length + 2)⟩;
    Compat compI0 r S g → ModelRun r ms → List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r ms) → MovesFrom InvisibleNoEffect (setupTrace r) pre →
    MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
    MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post →
    m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o →
    bobDoneBaseKeys (runTraceMoves r ms) = [] →
    ¬ MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (runTraceMoves r ms') (runVis r ms') ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀) []
theorem nbsc_highBitComp_of_hmc (i : ExternInterpretation) (r : Records) (S : Sem) (hfits : compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup i r) (g : Ghost) (p : PreKeyFields) (hp : parsePreKeyWire highBitWireBytes = some p) (hhmc : HmcAt38 r S g 1 0 (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) p) : NBSC38 r S g 1 0 (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) p := by obtain ⟨hopk, hidx⟩ := highBitWireBytes_hopk_hidx' hp; exact nbsc38_of_hmc hfits.1.1.1 hopk hidx hhmc
theorem nbsc_torsionComp_of_hmc (i : ExternInterpretation) (r : Records) (S : Sem) (hfits : compFitsPinned Witnesses.Cheval26SmallSubgroupTorsionComp.setup i r) (g : Ghost) (p : PreKeyFields) (hp : parsePreKeyWire torsionWireBytes = some p) (hhmc : HmcAt38 r S g 0 1 (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) p) : NBSC38 r S g 0 1 (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) p := by obtain ⟨hopk, hidx⟩ := torsionWireBytes_hopk_hidx' hp; exact nbsc38_of_hmc hfits.1.1.1 hopk hidx hhmc
theorem nbscHighBitComp_of (hhmc : ∀ (i : ExternInterpretation) (r : Records) (S : Sem), compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup i r → ∀ (g : Ghost) (p : PreKeyFields), parsePreKeyWire highBitWireBytes = some p → HmcAt38 r S g 1 0 (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) p) : Census443Defs.NbscHighBitComp' :=
  fun i r S hfits g p hp =>
    nbsc38'_of_nbsc38 (nbsc_highBitComp_of_hmc i r S hfits g p hp (hhmc i r S hfits g p hp))
theorem nbscTorsionComp_of (hhmc : ∀ (i : ExternInterpretation) (r : Records) (S : Sem), compFitsPinned Witnesses.Cheval26SmallSubgroupTorsionComp.setup i r → ∀ (g : Ghost) (p : PreKeyFields), parsePreKeyWire torsionWireBytes = some p → HmcAt38 r S g 0 1 (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) p) : Census443Defs.NbscTorsionComp' :=
  fun i r S hfits g p hp =>
    nbsc38'_of_nbsc38 (nbsc_torsionComp_of_hmc i r S hfits g p hp (hhmc i r S hfits g p hp))
theorem split38MemoClass_of_newMemo {r : Records} {S : Sem} {g : Ghost} {v : Fin 4} {t : Fin 8} {p : PreKeyFields} {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} (hNe : r.alice ≠ r.bob) (hopk : p.preKeyId = none) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob (iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl pq⟩; x ∈ (([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀).flatMap fun u => (gamma' compI0 S g u).memo)) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post;
    Split38MemoClass r S g ms' tr₁ tr₂ cl x :=
  mem_newTerms_memo_split38 hNe hopk hpre hmid hpost hm₀ x hx
theorem split38MemoClass_of_preOrNewMemo {r : Records} {S : Sem} {g : Ghost} {v : Fin 4} {t : Fin 8} {p : PreKeyFields} {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} (hNe : r.alice ≠ r.bob) (hopk : p.preKeyId = none) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob (iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl pq⟩; x ∈ ((prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap fun u => (gamma' compI0 S g u).memo) ++ (([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀).flatMap fun u => (gamma' compI0 S g u).memo)) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post;
    Split38MemoClass r S g ms' tr₁ tr₂ cl x := by
  rcases List.mem_append.mp hx with hpre_mem | hnew_mem
  · exact Or.inl hpre_mem
  · exact split38MemoClass_of_newMemo hNe hopk hpre hmid hpost hm₀ hnew_mem
theorem hmcAt38_of_classVT {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hrest : Split38NoClassifiedCollisionAtVT w τ wire v t) {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} (hfits : compFitsPinned w compI0 r) (hp : parsePreKeyWire wire = some p) (hopk : p.preKeyId = none) : HmcAt38 r S g v t τ p := by
  intro pre mid post hb shown cl e c' tr₁ o m₀ tr₂ stA ms ms' x₀ hcompat hrun hvis hpre hmid hpost hm₀ hbd; have hNe : r.alice ≠ r.bob := hfits.1.1.1
  have hpost' : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2)
        (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) post := hpost
  have hpts_eq : plaintextTerms (runVis r ms') ++ ([] : List DY.Bytes) = plaintextTerms (runVis r ms') := List.append_nil _; refine not_memoCollisionOn_of_no_pair_collides (fun x₁ hx₁ x₂ hx₂ => ?_); rw [hpts_eq]; exact hrest r S g p hfits hp hopk pre mid post hb shown cl e c' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ (split38MemoClass_of_newMemo hNe hopk hpre hmid hpost' hm₀ hx₁) (split38MemoClass_of_preOrNewMemo hNe hopk hpre hmid hpost' hm₀ hx₂)
theorem nbscHighBitComp_of_classVT (hrest : Split38NoClassifiedCollisionHBVT) : Census443Defs.NbscHighBitComp' := by refine nbscHighBitComp_of (fun i r S hfits g p hp => ?_); have hi : i = compI0 := hfits.2.1; subst hi; obtain ⟨hopk, _⟩ := highBitWireBytes_hopk_hidx' hp; exact hmcAt38_of_classVT (w := Witnesses.Cheval26SmallSubgroupHighBitComp.setup) hrest hfits hp hopk
theorem nbscTorsionComp_of_classVT (hrest : Split38NoClassifiedCollisionTCVT) : Census443Defs.NbscTorsionComp' := by refine nbscTorsionComp_of (fun i r S hfits g p hp => ?_); have hi : i = compI0 := hfits.2.1; subst hi; obtain ⟨hopk, _⟩ := torsionWireBytes_hopk_hidx' hp; exact hmcAt38_of_classVT (w := Witnesses.Cheval26SmallSubgroupTorsionComp.setup) hrest hfits hp hopk
end Symbolic.BugInjection.Proofs.Common443.CompRNbsc38VT

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.BugInjection.Proofs.Common443.CompRNoBSC
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def NBSC38 (r : Records) (S : Sem) (g : Ghost) (v : Fin 4) (t : Fin 8) (τ₁ : List MachineEvent) (p : PreKeyFields) : Prop := ∀ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
    let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o;
    Compat compI0 r S g → ModelRun r (pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post) → List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r (pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post)) → MovesFrom InvisibleNoEffect (setupTrace r) pre →
    MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
    MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post →
    m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o →
    bobDoneBaseKeys (runTraceMoves r (pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post)) = [] → ¬ BobStartCollision compI0 r S g (pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post) p ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl (tr₂.length + 2)⟩
private theorem iniAliceOut_eq_census443 (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) : Census443Defs.iniAliceOut tr ikA ikBPk spkPk pqPk opk = iniAliceOut tr ikA ikBPk spkPk pqPk opk := rfl
private theorem iniAliceStartState_eq_census443 (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : Census443Defs.iniAliceStartState tr b o = iniAliceStartState tr b o := rfl
private theorem iniAliceStartTr_eq_census443 (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : Census443Defs.iniAliceStartTr tr a b o = iniAliceStartTr tr a b o := rfl
private theorem encOut_eq_census443 (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : Census443Defs.encOut tr₂ stA cl pq = encOut tr₂ stA cl pq := rfl
private theorem invisibleNoEffect_of_census443 {tr : ExecTrace} {m : Move} (h : Census443Defs.InvisibleNoEffect tr m) : InvisibleNoEffect tr m :=
  ⟨h.1, fun i hi => ⟨(h.2 i hi).1,
    Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_of_eq_none (h.2 i hi).2.1,
    (h.2 i hi).2.2.1, (h.2 i hi).2.2.2⟩⟩
private theorem movesFrom_of_census443 {tr : ExecTrace} {δ : List Move} (h : Census443Defs.MovesFrom Census443Defs.InvisibleNoEffect tr δ) : MovesFrom InvisibleNoEffect tr δ := by
  induction δ generalizing tr with
  | nil => trivial
  | cons m δ ih => exact ⟨invisibleNoEffect_of_census443 h.1, ih h.2⟩
theorem nbsc38'_of_nbsc38 {r : Records} {S : Sem} {g : Ghost} {v : Fin 4} {t : Fin 8} {τ₁ : List MachineEvent} {p : PreKeyFields} (h : NBSC38 r S g v t τ₁ p) : Census443Defs.NBSC38' r S g v t τ₁ p := by
  intro pre mid post hb shown cl e c' tr₁ o m₀ tr₂ stA hc hmr hvis hpre hmid hpost hm₀ hnil; have ho : o = iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none := iniAliceOut_eq_census443 ..
  have hstA : stA = iniAliceStartState tr₁ r.bob
      (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) := by
    change Census443Defs.iniAliceStartState tr₁ r.bob o = _; rw [iniAliceStartState_eq_census443, ho]
  have hm₀' : m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob
      (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) := by
    rw [hm₀, iniAliceStartTr_eq_census443, ho]
  rw [ho, hstA, encOut_eq_census443]; exact h pre mid post hb shown cl e c' hc hmr hvis (movesFrom_of_census443 hpre) (movesFrom_of_census443 hmid) (movesFrom_of_census443 hpost) hm₀' hnil
theorem aliceStartTrOfOut_eq_ini (tr : ExecTrace) (a b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : CompPrefixInvBundle.aliceStartTrOfOut tr a b o = iniAliceStartTr tr a b o :=
  rfl
theorem iniAliceStartState_ns_ne_u32Max (tr : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : (iniAliceStartState tr b o).ns ≠ DY.Libsignal.TripleRatchet.u32Max := by change (0 : UInt32) ≠ DY.Libsignal.TripleRatchet.u32Max; decide
theorem encrypt_next_split38_eq {r : Records} {tr₁ tr₂ : ExecTrace} {m₀ : Move} {mid : List Move} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl : Nat} (wrap : Option (Nat × Nat)) (hm₀ : m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o) (hmid : MovesFrom InvisibleNoEffect (m₀.next tr₁) mid) (htr₂ : tr₂ = (runMoves mid (m₀.next tr₁)).1) : (Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) wrap).next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) (iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2) := by
  have hst : (tr₂.at? (tr₁.length + 8) : Option TRStEntry) =
      some (TRStE r.alice (iniAliceStartState tr₁ r.bob o)) := by
    rw [htr₂, at?_trSt_of_movesFrom_invisibleNoEffect hmid, hm₀]; exact trStateStoredAt_iniAliceStartTr tr₁ r.alice r.bob o
  exact encrypt_next_eq_encNextTr_of_ownSalt hst (iniAliceStartState_ns_ne_u32Max tr₁ r.bob o) rfl
theorem not_bobStartCollision_split38_ini {r : Records} {S : Sem} {g : Ghost} {v : Fin 4} {t : Fin 8} {p : PreKeyFields} {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl e c' : Nat} (hNe : r.alice ≠ r.bob) (hopk : p.preKeyId = none) (hidx : spqrIdx p = 0 ∨ spqrIdx p = 1) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c'))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob (iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) (hmc : let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o; let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl (tr₂.length + 2)⟩; ¬ MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (runTraceMoves r ms') (runVis r ms') ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀) []) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o;
    ¬ BobStartCollision compI0 r S g (pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post) p
      ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl (tr₂.length + 2)⟩ := by
  let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o;
  have henc_swap :
      (Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2)
        (some (tr₁.length + 3, tr₁.length + 4))).next tr₂ =
      encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2) :=
    encrypt_next_split38_eq (some (tr₁.length + 3, tr₁.length + 4)) hm₀ hmid rfl
  have hpost_swap :
      MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2)
          (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) post := by
    rw [encrypt_next_eq_wrap tr₂ r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) (some (e, c'))]; exact hpost
  exact not_bobStartCollision_x0 (x₀ := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl (tr₂.length + 2)⟩) hNe hopk (x25519Key_torsionVariant_aliceOut_ek tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none v t)
    rfl
    hmc
    hidx
    (spqrChainKey_mem_honestSalts_of_split (o := o) rfl rfl hpre hmid hpost_swap henc_swap)
end Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38

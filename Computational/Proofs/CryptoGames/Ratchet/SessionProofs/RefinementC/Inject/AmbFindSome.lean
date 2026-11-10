/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Inject step: ambiguous new chain, resolved chain found

Proves `closeByStateC_inject_newChain_amb_find_some` for `closeByStateC_inject_step` when an ambiguous new-chain injection resolves to an existing chain after accounting for the SPK ratchet.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

private theorem iafs_chainSync_with_key {g : GhostChain} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (k : Option PublicKey) (h : ChainSync g v) :
    ChainSync { g with key := k } v := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, h4, h5, h6⟩

private def iafs_cwin_preserves {α : Type}
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    gh.1.win = true →
    ∀ r ∈ support ((m.run sC).run gh), r.2.1.win = true

private theorem iafs_cwin_preserves_pure {α : Type} (a : α) :
    iafs_cwin_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (pure a) := by
  intro sC gh hgh r hr
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iafs_cwin_preserves_bind {α β : Type}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    (hm : iafs_cwin_preserves m) (hk : ∀ a, iafs_cwin_preserves (k a)) :
    iafs_cwin_preserves (m >>= k) := by
  intro sC gh hgh r hr
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨r₁, hr₁, hr⟩
  exact hk r₁.1.1 r₁.1.2 r₁.2 (hm sC gh hgh r₁ hr₁) r hr

private theorem iafs_cwin_preserves_get :
    iafs_cwin_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) get := by
  intro sC gh hgh r hr
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iafs_cwin_preserves_set (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    iafs_cwin_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (set sC') := by
  intro sC gh hgh r hr
  simp only [StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iafs_cwin_preserves_modify (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    iafs_cwin_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (modify f) := by
  intro sC gh hgh r hr
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iafs_cwin_preserves_ite {α : Type} {P_cond : Prop} [Decidable P_cond]
    {t e : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (ht : iafs_cwin_preserves t) (he : iafs_cwin_preserves e) :
    iafs_cwin_preserves (if P_cond then t else e) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem iafs_cwin_preserves_zoomB {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) :
    iafs_cwin_preserves (PQ := PQ) (runOnBaseState (probeHook fig qepF) x) := by
  intro sC gh hgh r hr
  rw [zoomB_probe_run] at hr
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨w, hw, rfl⟩
  exact simulateQ_run_preserve (SM.oracleImpl fig 3 qepF SM.Config.h1) (fun s => s.win = true)
    (fun q' s hs => oracleImpl_run_of_win_true fig 3 qepF SM.Config.h1 q' s hs)
    (x.run sC.base) gh.1 hgh w hw

private theorem iafs_cwin_preserves_liftC {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) :
    iafs_cwin_preserves (PQ := PQ) (LibsignalSimC.liftC (probeHook fig qepF) x) := by
  intro sC gh hgh r hr
  rw [liftC_probe_run] at hr
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨w, hw, rfl⟩
  exact simulateQ_run_preserve (SM.oracleImpl fig 3 qepF SM.Config.h1) (fun s => s.win = true)
    (fun q' s hs => oracleImpl_run_of_win_true fig 3 qepF SM.Config.h1 q' s hs)
    x gh.1 hgh w hw

private theorem iafs_cwin_preserves_probe
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    iafs_cwin_preserves (PQ := PQ)
      (StateT.lift ((probeHook fig qepF).probe Q c') :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) Unit) := by
  intro sC gh hgh r hr
  change r ∈ support ((((probeHook fig qepF).probe Q c' >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind] at hr
  change r ∈ support ((pure ((), (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)) :
    ProbComp _) >>= fun x => (pure (x.1, sC) : ProbeM Pt ℓ _).run x.2) at hr
  simp only [pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iafs_cwin_preserves_guardC {α : Type}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : iafs_cwin_preserves m) :
    iafs_cwin_preserves (guardC m) := by
  unfold guardC
  refine iafs_cwin_preserves_bind iafs_cwin_preserves_get fun sC => ?_
  exact iafs_cwin_preserves_ite (iafs_cwin_preserves_pure none) hm

private theorem iafs_cwin_preserves_simSendC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    iafs_cwin_preserves (simSendC P qep fig (probeHook fig qepF) Q m₀ chal r) := by
  unfold simSendC
  refine iafs_cwin_preserves_bind (iafs_cwin_preserves_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact iafs_cwin_preserves_pure none
  | some w =>
    refine iafs_cwin_preserves_bind iafs_cwin_preserves_get fun sC => ?_
    exact iafs_cwin_preserves_bind (iafs_cwin_preserves_set _) fun _ => iafs_cwin_preserves_pure (some w)

private theorem iafs_cwin_preserves_fwdAnswerC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    iafs_cwin_preserves (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine iafs_cwin_preserves_bind (iafs_cwin_preserves_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact iafs_cwin_preserves_zoomB (PQ := PQ) fig qepF _
  | some r =>
    cases r <;>
      first
      | exact iafs_cwin_preserves_zoomB (PQ := PQ) fig qepF _
      | exact iafs_cwin_preserves_bind (iafs_cwin_preserves_modify _) fun _ =>
          iafs_cwin_preserves_zoomB (PQ := PQ) fig qepF _

private theorem iafs_cwin_preserves_resyncC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    iafs_cwin_preserves (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact iafs_cwin_preserves_pure _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine iafs_cwin_preserves_bind (iafs_cwin_preserves_liftC fig qepF _) fun res => ?_
    cases res with
    | none => exact iafs_cwin_preserves_pure _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        exact iafs_cwin_preserves_bind (iafs_cwin_preserves_modify _) fun _ =>
          iafs_cwin_preserves_zoomB (PQ := PQ) fig qepF _
      | _ => exact iafs_cwin_preserves_pure _

private theorem iafs_cwin_preserves_fwdC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    iafs_cwin_preserves
      (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold fwdC
  refine iafs_cwin_preserves_bind iafs_cwin_preserves_get fun sC => ?_
  cases honestC with
  | none => exact iafs_cwin_preserves_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c'
  | some c =>
    refine iafs_cwin_preserves_ite ?_ (iafs_cwin_preserves_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c')
    cases predictReceiveWithSnapshots (fig := fig) (fs := fs) P sC Q w c c' with
    | some r => exact iafs_cwin_preserves_resyncC qep fig fs qepF Q w ci? T pq' c r
    | none =>
      exact iafs_cwin_preserves_bind (iafs_cwin_preserves_probe fig qepF Q c') fun _ =>
        iafs_cwin_preserves_pure _

private theorem iafs_cwin_preserves_fwdEvictC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    iafs_cwin_preserves (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine iafs_cwin_preserves_bind iafs_cwin_preserves_get fun sC => ?_
  refine iafs_cwin_preserves_ite ?_ (iafs_cwin_preserves_fwdAnswerC qep fig fs qepF Q w isDel none T pq' c')
  exact iafs_cwin_preserves_bind (iafs_cwin_preserves_probe fig qepF Q c') fun _ => iafs_cwin_preserves_pure _

private theorem iafs_cwin_preserves_simRecvC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    iafs_cwin_preserves (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  unfold simRecvC
  generalize (2 ^ 32 : ℕ) = maxI
  generalize (25000 : ℕ) = maxSkip
  refine iafs_cwin_preserves_bind iafs_cwin_preserves_get fun sC => ?_
  dsimp only
  refine iafs_cwin_preserves_ite (iafs_cwin_preserves_pure _) ?_
  refine iafs_cwin_preserves_ite (iafs_cwin_preserves_pure _) ?_
  refine iafs_cwin_preserves_ite (iafs_cwin_preserves_pure _) ?_
  refine iafs_cwin_preserves_ite (iafs_cwin_preserves_pure _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact iafs_cwin_preserves_pure _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine iafs_cwin_preserves_ite (iafs_cwin_preserves_pure _) ?_
    refine iafs_cwin_preserves_ite (iafs_cwin_preserves_pure _) ?_
    cases P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact iafs_cwin_preserves_pure _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine iafs_cwin_preserves_ite (iafs_cwin_preserves_pure _) ?_
        exact iafs_cwin_preserves_fwdC P qep fig fs qepF Q w isDel
          (some ci) h.senderRatchetKey pq' _ _
      | none =>
        dsimp only
        refine iafs_cwin_preserves_ite (iafs_cwin_preserves_pure _) ?_
        refine iafs_cwin_preserves_ite (iafs_cwin_preserves_pure _) ?_
        refine iafs_cwin_preserves_ite
          (iafs_cwin_preserves_bind (iafs_cwin_preserves_modify _) fun _ => ?_) ?_ <;>
        · refine iafs_cwin_preserves_ite (iafs_cwin_preserves_pure _) ?_
          cases decT h.senderRatchetKey with
          | none => exact iafs_cwin_preserves_pure _
          | some T =>
            exact iafs_cwin_preserves_ite
              (iafs_cwin_preserves_fwdEvictC qep fig fs qepF Q w isDel h.senderRatchetKey pq' _)
              (iafs_cwin_preserves_fwdC P qep fig fs qepF Q w isDel none h.senderRatchetKey pq' _ _)

private theorem iafs_cwin_preserves_simCorrC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    iafs_cwin_preserves (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  unfold simCorrC
  refine iafs_cwin_preserves_bind iafs_cwin_preserves_get fun sC => ?_
  refine iafs_cwin_preserves_ite (iafs_cwin_preserves_pure _) ?_
  refine iafs_cwin_preserves_bind (iafs_cwin_preserves_liftC fig qepF _) fun res => ?_
  cases res with
  | none => exact iafs_cwin_preserves_pure _
  | some st =>
    exact iafs_cwin_preserves_bind (iafs_cwin_preserves_set _) fun _ => iafs_cwin_preserves_pure _

private theorem iafs_stepSimCNone_preserve_win_true (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q x), z.2.2.1.win = true := by
  intro z hz
  unfold stepSimCNone at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨r, hr, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hpres : iafs_cwin_preserves
      (simImplC P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh (.inr q)) := by
    rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
    · exact iafs_cwin_preserves_guardC (iafs_cwin_preserves_simSendC P qep _ (qep + 1) Q m₀ none r')
    · exact iafs_cwin_preserves_guardC (iafs_cwin_preserves_simSendC P qep _ (qep + 1) Q m₀ (some m₁) r')
    · exact iafs_cwin_preserves_guardC (iafs_cwin_preserves_simRecvC P encT decT qep _ _ (qep + 1) Q w true)
    · exact iafs_cwin_preserves_guardC (iafs_cwin_preserves_simRecvC P encT decT qep _ _ (qep + 1) Q w false)
    · exact iafs_cwin_preserves_guardC (iafs_cwin_preserves_simCorrC P encT _ (qep + 1) Dh Q)
  exact hpres x.1 x.2 hwin r hr

private theorem iafs_stepSimC_preserve_win_true (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimC P ℓ Dh encPt encT decT idOf lam qep none q x), z.2.2.1.win = true := by
  rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact iafs_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin
  · exact iafs_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin
  · intro z hz
    simp only [stepSimC] at hz
    split at hz
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨r, hr, rfl⟩
      exact stepSim_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep none _ x.sim hwin rfl r hr
    · exact iafs_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin z hz
  · intro z hz
    simp only [stepSimC] at hz
    split at hz
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨r, hr, rfl⟩
      exact stepSim_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep none _ x.sim hwin rfl r hr
    · exact iafs_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin z hz
  · exact iafs_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin

private theorem iafs_stepSimCEager_preserve_win_true (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q x ec),
      z.2.1.2.1.win = true := by
  intro z hz
  rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · simp only [stepSimCEager, stepSimCEagerTransmit, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inl (.inl (.inl (Q, m₀, r'))))) x.sim ec hwin rfl res hres
  · simp only [stepSimCEager, stepSimCEagerChall, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inl (.inl (.inr (Q, m₀, m₁, r'))))) x.sim ec hwin rfl res hres
  · simp only [stepSimCEager, stepSimCEagerDeliver] at hz
    rw [simRecvUsesCoin_of_win_true P encT decT none Q w true x.sim hwin, evictStopsC_none] at hz
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, _, _, rfl⟩
    exact iafs_stepSimC_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin res hres
  · simp only [stepSimCEager, stepSimCEagerInject] at hz
    rw [simRecvUsesCoin_of_win_true P encT decT none Q w false x.sim hwin, evictStopsC_none] at hz
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, _, _, rfl⟩
    exact iafs_stepSimC_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin res hres
  · simp only [stepSimCEager, stepSimCEagerCorr, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, _, _, rfl⟩
    exact iafs_stepSimC_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin res hres

private theorem iafs_evalDist_runSimCEager_win_true {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) (hwin : x.2.1.win = true)
    (F : α × (JointC PQ Pt ℓ × (Party → BitVec 256)) → ProbComp Bool)
    (hF : ∀ z, z.2.1.2.1.win = true → 𝒟[F z] {true} = 1) :
    𝒟[runSimCEager P ℓ Dh encPt encT decT idOf lam qep none oa x ec >>= F] {true} = 1 := by
  unfold runSimCEager
  refine Construction.AuthL11.evalDist_bind_eq_one _ F fun z hz => ?_
  refine hF z (simulateQ_run_preserve
    (simEagerImplC P ℓ Dh encPt encT decT idOf lam qep none)
    (fun s => s.1.2.1.win = true) ?_ oa (x, ec) hwin z hz)
  intro q s hs
  exact iafs_stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep q s.1 s.2 hs

/-- Closes an ambiguous new-chain injection whose resolved SPK chain is found: every acceptance wins in Fig. 8, and rejection increments `amb` while preserving `SimInvCX`. -/
theorem closeByStateC_inject_newChain_amb_find_some {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = false)
    (hamb_b : (inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))) = true)
    {ci : ℕ}
    (hfind_res : ((resolveSim (encT (Dh.dh x₀ Dh.base)) sC.base).chains Q).findIdx?
      (fun g => g.key == some h.senderRatchetKey) = some ci)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  let spkKey := encT (Dh.dh x₀ Dh.base)
  let s_res := resolveSim spkKey sC.base
  cases Q with
  | B =>
    have hchainsB : s_res.chains .B = sC.base.chains .B := rfl
    rw [hchainsB, hfind] at hfind_res
    cases hfind_res
  | A =>
    have hstop0 := (simRecvStepEager_inject_ambC P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep q r x₀
      .A w s_R sC.base s_fig8 ec winBefore epExp hinv.hsim hguard hlen hparse haddrs hspqr hpan hfind hevict hzero hamb_b).1
    rcases getElem?_of_findIdx_ghost (s_res.chains .A) h.senderRatchetKey ci hfind_res with
      ⟨g_res, helem_res, hg_res_key⟩
    have hresA : s_res.chains .A =
        (sC.base.chains .A).map (fun g₀ => if g₀.key.isNone then { g₀ with key := some spkKey } else g₀) := rfl
    have helem_map : ((sC.base.chains .A).map
        (fun g₀ => if g₀.key.isNone then { g₀ with key := some spkKey } else g₀))[ci]? = some g_res :=
      helem_res
    rw [List.getElem?_map] at helem_map
    rcases Option.map_eq_some_iff.mp helem_map with ⟨g₀, hg₀_elem, hg_res_def⟩
    have hg₀_mem : g₀ ∈ sC.base.chains .A := List.mem_of_getElem? hg₀_elem
    have hg₀_none : g₀.key.isNone = true := by
      cases hnone : g₀.key.isNone with
      | true => rfl
      | false =>
        exfalso
        rw [hnone, ite_eq_right Bool.false_ne_true] at hg_res_def
        subst hg_res_def
        have hfind_none := List.findIdx?_eq_none_iff.mp hfind g₀ hg₀_mem
        rw [hg_res_key, beq_self_eq_true] at hfind_none
        exact Bool.noConfusion hfind_none
    rw [hg₀_none, ite_eq_left rfl] at hg_res_def
    have hsrk_eq : h.senderRatchetKey = spkKey := by
      have hk : g_res.key = some spkKey := by rw [← hg_res_def]
      exact Option.some.inj (hg_res_key.symm.trans hk)
    have hdecT : decT h.senderRatchetKey = some (Dh.dh x₀ Dh.base) := by
      rw [hsrk_eq]; exact hdec (Dh.dh x₀ Dh.base)
    have hT_map : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
      rw [hdecT, Option.map_some, Option.getD_some, hsrk_eq]
    have hg₀_ep0 : g₀.epoch = 0 := hinv.hsim.hchainsA.1 g₀ hg₀_mem hg₀_none
    have hg_res_ep0 : g_res.epoch = 0 := by rw [← hg_res_def, hg₀_ep0]
    rcases hinv.hsim.hchains_sync .A g₀ hg₀_mem with ⟨hg₀_ep_le, hrecv₀, _, v, hvR₀, hsync₀⟩
    have hg_res_ep_tcur : g_res.epoch ≤ (s_fig8.st .A).tcur := by
      rw [hinv.hsim.htcur .A, hg_res_ep0]
      exact Nat.zero_le _
    have hrecv_res : Party.A.sendsIn g_res.epoch = false := by
      rw [hg_res_ep0]; rfl
    have hvR_res : (s_fig8.st .A).vR g_res.epoch = some v := by
      rw [hg_res_ep0, ← hg₀_ep0]; exact hvR₀
    have hsync_res : ChainSync g_res v := by
      rw [← hg_res_def]
      exact iafs_chainSync_with_key (some spkKey) hsync₀
    have hno_none_res : ∀ g ∈ s_res.chains .A, g.key.isNone = false :=
      resolveSim_chains_no_none' spkKey sC.base .A hinv.hsim.hchainsB_none
    have hdummy_res : ∀ g ∈ s_res.chains .A, g.key = none → h.senderRatchetKey ≠ dummyKey := by
      intro g hg hgn
      have hgn' := hno_none_res g hg
      simp [hgn] at hgn'
    have hmap_ep : (s_res.chains .A).map (·.epoch) = (sC.base.chains .A).map (·.epoch) :=
      resolveSpkChains_map_epoch spkKey sC.base.chains .A
    have hnodup_res : ((s_res.chains .A).map (·.epoch)).Nodup := by
      rw [hmap_ep, hinv.hsim.hchainsA_ep]
      exact epListA_nodup (sC.base.mir.epoch .A / 2)
    have hdistinct : ∀ j < (s_res.chains .A).length, j ≠ ci →
        ∀ g_j, (s_res.chains .A)[j]? = some g_j → g_j.epoch ≠ g_res.epoch :=
      fun j hj_lt hj_ne g_j hg_j => nodup_distinct_epoch hnodup_res helem_res j hj_lt hj_ne g_j hg_j
    let st := s_fig8.st .A
    let g_ghost := toGhost P s_res .A st
    let rk := if inReceiveOnlyEpoch sC.base.mir .A then
        match st.γ with
        | .pub T => ((rootPRNG P.C.F encPt).up st.root (Dh.dh (ec .A) T)).1
        | _ => g_ghost.session.rootKey
      else g_ghost.session.rootKey
    let sc := if inReceiveOnlyEpoch sC.base.mir .A then
        match st.γ with
        | .pub T => some ⟨KeyPair.generate P.C (ec .A), ⟨((rootPRNG P.C.F encPt).up st.root (Dh.dh (ec .A) T)).2, 0⟩⟩
        | _ => g_ghost.session.senderChain
      else g_ghost.session.senderChain
    let pn := if inReceiveOnlyEpoch sC.base.mir .A then
        match st.γ with
        | .pub _ => BitVec.ofNat 32 (sC.base.mir.idx .A - 1)
        | _ => g_ghost.session.previousCounter
      else g_ghost.session.previousCounter
    have hst_R_eq : s_R.st .A = withEager g_ghost rk sc pn := by
      rw [hinv.hsim.hst_R .A]
      exact expectedGhost_eq_withEager P Dh encPt spkKey sC.base .A st (ec .A)
    let i := h.counter.toNat + 1
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let c₀ : Fig8C Pt := ((g_res.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    let pos₀ : SM.Pos := ⟨.B, g_res.epoch, i⟩
    let mir'₀ := sC.base.mir.accept .A () pos₀
    have hmir'₀_ep : mir'₀.epoch .A = sC.base.mir.epoch .A := by
      have hep := accept_epoch_eq_of_le sC.base.mir .A () pos₀ (by dsimp only [pos₀]; rw [hg_res_ep0]; exact Nat.zero_le _)
      exact congrFun hep .A
    have hstep_res := fun rc =>
      receive_knownChain_withEager_toGhost_eq P Dh encPt encT idOf lam hid s_res .A st
        (hinv.hsim.hst_id .A) w hlen h body hparse haddrs pq' salt hspqr hpan ci hfind_res hdummy_res
        g_res helem_res hg_res_ep_tcur hrecv_res v hvR_res hsync_res (decT h.senderRatchetKey) hT_map
        hdistinct mir'₀ hmir'₀_ep rk sc pn rc
    have hguard_B : ((sC.base.mir.inTransit Party.B w).isSome || !sC.base.mir.safeInj 3 || !ratchetKeyAdmissible P.codec decT encT w) = false := hguard
    have htr_mir : (sC.base.mir.inTransit Party.B w).isSome = false := by
      revert hguard_B; cases (sC.base.mir.inTransit Party.B w).isSome <;> simp
    have hsafe_mir : sC.base.mir.safeInj 3 = true := by
      revert hguard_B; cases (sC.base.mir.inTransit Party.B w).isSome <;> cases sC.base.mir.safeInj 3 <;> simp
    have hguard_R : (s_R.win || (s_R.inTransit Party.B w).isSome || !s_R.safeInj 3 ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hinv.hsim.hmeta.hwin_R, hinv.hsim.hmeta.inTransit_R_isSome, hinv.hsim.hmeta.safeInj_R]
      simpa [configR1OnCurve] using hguard_B
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    have hfig0_eq : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st
        ((g_res.epoch, decT h.senderRatchetKey), h.counter.toNat + 1,
          (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) =
            sm.receive st c₀ := rfl
    have hrcv_none_or_some :
        (∀ rc, P.receive (s_R.st .A) w rc = none) ∨
        (g_res.rejects i = false ∧ ∃ st' t' i' pub m, sm.receive st c₀ = some (st', t', i', (pub, m))) := by
      by_cases hrej : g_res.rejects i = true
      · refine Or.inl fun rc => ?_
        rw [hst_R_eq]
        exact (hstep_res rc).1 hrej
      · have hrej_f : g_res.rejects i = false := Bool.eq_false_iff.mpr hrej
        cases hfig0 : sm.receive st c₀ with
        | none =>
          refine Or.inl fun rc => ?_
          have h2 := (hstep_res rc).2 hrej_f
          dsimp only at h2
          rw [hfig0_eq, hfig0] at h2
          dsimp only at h2
          rw [hst_R_eq]
          exact h2
        | some val =>
          rcases val with ⟨st', t', i', ⟨pub, m⟩⟩
          exact Or.inr ⟨hrej_f, st', t', i', pub, m, rfl⟩
    have hfind_hon : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Party.A.other) = none := by
      cases hf : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Party.A.other) with
      | none => rfl
      | some wc =>
        exfalso
        have hmem_wc := List.mem_of_find?_eq_some hf
        have hpred_wc := List.find?_some hf
        simp only [Bool.and_eq_true, beq_iff_eq] at hpred_wc
        rcases wc with ⟨w_wc, c_wc⟩
        dsimp only at hpred_wc
        rcases hpred_wc with ⟨rfl, hsend_wc⟩
        have hinv_wc := hinv.hsim.hhon (w_wc, c_wc) hmem_wc
        rcases hinv_wc.1 with ⟨_, _, hge1, _, _, _, _, h_wc, body_wc, hparse_wc, _, hsrk_wc, _, _⟩
        have hhb : (h_wc, body_wc) = (h, body) := Option.some.inj (hparse_wc.symm.trans hparse)
        rcases Prod.mk.inj hhb with ⟨rfl, rfl⟩
        have hdh_eq : Dh.dh (epExp c_wc.1.1) Dh.base = Dh.dh (epExp 0) Dh.base := by
          rw [hinv.hsim.hepExp0]
          exact hinj (hsrk_wc.symm.trans hsrk_eq)
        have ht_eq0 : c_wc.1.1 = 0 :=
          hinv.hsim.hcoll c_wc.1.1 0 hinv_wc.2.1 (Nat.zero_le _) hdh_eq
        dsimp only at hge1
        omega
    let s₁ : SimState PQ Pt ℓ := { sC.base with amb := sC.base.amb + 1 }
    let sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := s₁ }
    have hs₁_stop : ({ sC.base with amb := sC.base.amb + 1, stopped := false } : SimState PQ Pt ℓ) = s₁ := by
      dsimp only [s₁]; exact congrArg (SimState.mk _ _ _ _ _ _ _) hinv.hsim.hmeta.hstop.symm
    have hhon_wire : ∀ wc ∈ s₁.honest, wc.1 = LibsignalSim.toWire wc.2 :=
      fun wc hwc => (hinv.hsim.hhon wc hwc).1.1
    rcases hrcv_none_or_some with hrcv_none | ⟨hrej_f, st', t', i', pub, m, hfig0⟩
    · have huse_none : simRecvUsesCoin P encT decT none .A w false (sC.base, s_fig8) = false :=
        simRecvUsesCoin_none P encT decT .A w false (sC.base, s_fig8)
      have hnone_div : ((none : Option ℕ) == some sC.base.amb) = false := rfl
      have hrcv_R : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st .A) w rc = none := by
        intro rc
        unfold libsignalSessionScheme
        dsimp only
        rw [hrcv_none rc]
        rfl
      by_cases hinw_j : (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
      · have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none .A w false 0 (sC.base, s_fig8) =
            (some .rejected, (s₁, s_fig8)) := by
          unfold simRecvStep
          simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
            hevict, hzero, hamb_b, hnone_div,
            show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hinw_j,
            hs₁_stop]
        have hstepC_none : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false .A w false (sC, s_fig8, false) =
            (some .rejected, (sC₁, s_fig8, false)) := by
          unfold simRecvStepCGen
          simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
            hevict, hzero, hamb_b,
            show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hinw_j,
            hs₁_stop]
          rfl
        have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8) = false :=
          simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8)
            (by rw [hstep_none]; exact hinv.hsim.hmeta.hstop)
        have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (.A, w)))
            (sC, s_fig8, false) ec =
            pure (some .rejected, ((sC₁, s_fig8, false), ec)) :=
          stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none .A w
            (sC, s_fig8, false) ec hinv.hsim.hec huse_none hstops_none _ hstepC_none rfl
        exact closeByStateC_inject_amb_reject (hnpW := recvPanicsW_eq_false_of P .A w sC.base hlen hparse hpan) P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
          .A w cont s_R sC s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0 hnone_eager
          (ih (some .rejected))
      · have hinw_j_f : (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = false :=
          Bool.eq_false_iff.mpr hinw_j
        have hinw : inReceiveOnlyEpoch sC.base.mir .A = false := by
          revert hinw_j_f; cases inReceiveOnlyEpoch sC.base.mir .A <;> simp
        have hjump_f : (decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = false := by
          revert hinw_j_f; cases inReceiveOnlyEpoch sC.base.mir .A <;> simp
        let c_new : Fig8C Pt :=
          ((sC.base.mir.epoch .A + 1, some (Dh.dh x₀ Dh.base)), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
        have htoWire_new : LibsignalSim.toWire c_new = w :=
          toWire_raw_eq w hlen (sC.base.mir.epoch .A + 1) (some (Dh.dh x₀ Dh.base)) i (effectiveHkdfSalt32 salt)
        have hfwd_new : fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8 =
            injectPure sm 3 (qep + 1) SM.Config.h1 .A c_new s_fig8 :=
          fwdPure_of_inTransit_false sm 3 (qep + 1) SM.Config.h1 s₁ .A w c_new s_fig8 hhon_wire htoWire_new htr_mir
        have htr_fig8_new : (s_fig8.inTransit Party.B c_new).isSome = false :=
          inTransit_fig8_isSome_of_toWire hinv.hsim.hmeta .A w c_new htoWire_new htr_mir
        have hguard_fig8_new : (s_fig8.win || (s_fig8.inTransit Party.B c_new).isSome || !s_fig8.safeInj 3) = false := by
          rw [hinv.hsim.hmeta.hwin_fig8, htr_fig8_new, hinv.hsim.hmeta.safeInj_fig8 3, hsafe_mir]
          rfl
        cases hfig_new : sm.receive (s_fig8.st .A) c_new with
        | none =>
          have hinj_new : injectPure sm 3 (qep + 1) SM.Config.h1 .A c_new s_fig8 = (some .rejected, s_fig8) := by
            unfold injectPure
            dsimp only [Party.other]
            simp [hguard_fig8_new, hfig_new]
          have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none .A w false 0 (sC.base, s_fig8) =
              (some .rejected, (s₁, s_fig8)) := by
            have hT0_b : (some (Dh.dh x₀ Dh.base) == some 0) = false := by rw [← hdecT]; exact hzero
            unfold simRecvStep
            simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
              Bool.false_and, Bool.true_and, Bool.and_false, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
              hevict, hzero, hT0_b, hamb_b, hnone_div,
              hfind_hon, Option.map_none, hdecT,
              show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hinw_j_f,
              hs₁_stop]
            change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8
                    let a := onAnswerPure qep .A w false none h.senderRatchetKey pq' z.1 s₁
                    (a.1, (a.2, z.2))) = (some .rejected, (s₁, s_fig8))
            rw [hfwd_new, hinj_new]
            rfl
          have hstepC_none : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false .A w false (sC, s_fig8, false) =
              (some .rejected, (sC₁, s_fig8, false)) := by
            have hT0_b : (some (Dh.dh x₀ Dh.base) == some 0) = false := by rw [← hdecT]; exact hzero
            unfold simRecvStepCGen
            simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
              Bool.false_and, Bool.true_and, Bool.and_false, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
              hevict, hzero, hT0_b, hamb_b, hdecT,
              show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hinw_j_f,
              hs₁_stop]
            simp only [hfind_hon, Option.map_none]
            change fwdCPure P ℓ Dh encPt encT idOf lam qep false .A w false none h.senderRatchetKey pq' none c_new
              (sC₁, s_fig8, false) = (some .rejected, (sC₁, s_fig8, false))
            unfold fwdCPure
            dsimp only
            change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8
                    let kept' := match z.1 with
                      | some (.accepted _ _ _) => Function.update sC.kept .A (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c_new (sC.kept .A))
                      | _ => sC.kept
                    let a := onAnswerPure qep .A w false none h.senderRatchetKey pq' z.1 s₁
                    (a.1, ({ sC₁ with base := a.2, kept := kept' }, z.2, false))) =
              (some .rejected, (sC₁, s_fig8, false))
            rw [hfwd_new, hinj_new]
            rfl
          have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8) = false :=
            simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8)
              (by rw [hstep_none]; exact hinv.hsim.hmeta.hstop)
          have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (.A, w)))
              (sC, s_fig8, false) ec =
              pure (some .rejected, ((sC₁, s_fig8, false), ec)) :=
            stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none .A w
              (sC, s_fig8, false) ec hinv.hsim.hec huse_none hstops_none _ hstepC_none rfl
          exact closeByStateC_inject_amb_reject (hnpW := recvPanicsW_eq_false_of P .A w sC.base hlen hparse hpan) P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
            .A w cont s_R sC s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0 hnone_eager
            (ih (some .rejected))
        | some val_new =>
          rcases val_new with ⟨st_new, t_new, i_new, ⟨pub_new, m_new⟩⟩
          rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam (s_fig8.st .A) c_new hfig_new with
            ⟨ht_new, hi_new⟩
          dsimp only [c_new] at ht_new hi_new
          subst ht_new hi_new
          have htriv_new_mir : sC.base.mir.trivial 3 ⟨.B, sC.base.mir.epoch .A + 1, i⟩ = false :=
            trivial_false_of_newChain_inject hsafe_mir hinv.hsim.hcomp .A ⟨.B, sC.base.mir.epoch .A + 1, i⟩
              (by dsimp only; omega)
          have htriv_new_fig8 : s_fig8.trivial 3 ⟨.B, sC.base.mir.epoch .A + 1, i⟩ = false := by
            rw [hinv.hsim.hmeta.trivial_fig8, htriv_new_mir]
          have hnot_gt_new : ¬ ((qep + 1) + 1 < sC.base.mir.epoch .A + 1) := by
            have := hinv.hsim.hep_le .A
            omega
          have hinj_new : injectPure sm 3 (qep + 1) SM.Config.h1 .A c_new s_fig8 =
              (some .rejected, { s_fig8 with win := true }) := by
            unfold injectPure SM.Config.h1
            dsimp only [Party.other]
            simp only [hguard_fig8_new, Bool.false_eq_true, ↓reduceIte, hfig_new, hnot_gt_new, htriv_new_fig8]
          have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none .A w false 0 (sC.base, s_fig8) =
              (some .rejected, (s₁, { s_fig8 with win := true })) := by
            have hT0_b : (some (Dh.dh x₀ Dh.base) == some 0) = false := by rw [← hdecT]; exact hzero
            unfold simRecvStep
            simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
              Bool.false_and, Bool.true_and, Bool.and_false, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
              hevict, hzero, hT0_b, hamb_b, hnone_div,
              hfind_hon, Option.map_none, hdecT,
              show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hinw_j_f,
              hs₁_stop]
            change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8
                    let a := onAnswerPure qep .A w false none h.senderRatchetKey pq' z.1 s₁
                    (a.1, (a.2, z.2))) = (some .rejected, (s₁, { s_fig8 with win := true }))
            rw [hfwd_new, hinj_new]
            rfl
          have hstepC_none : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false .A w false (sC, s_fig8, false) =
              (some .rejected, (sC₁, { s_fig8 with win := true }, false)) := by
            have hT0_b : (some (Dh.dh x₀ Dh.base) == some 0) = false := by rw [← hdecT]; exact hzero
            unfold simRecvStepCGen
            simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
              Bool.false_and, Bool.true_and, Bool.and_false, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
              hevict, hzero, hT0_b, hamb_b, hdecT,
              show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hinw_j_f,
              hs₁_stop]
            simp only [hfind_hon, Option.map_none]
            change fwdCPure P ℓ Dh encPt encT idOf lam qep false .A w false none h.senderRatchetKey pq' none c_new
              (sC₁, s_fig8, false) = (some .rejected, (sC₁, { s_fig8 with win := true }, false))
            unfold fwdCPure
            dsimp only
            change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8
                    let kept' := match z.1 with
                      | some (.accepted _ _ _) => Function.update sC.kept .A (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c_new (sC.kept .A))
                      | _ => sC.kept
                    let a := onAnswerPure qep .A w false none h.senderRatchetKey pq' z.1 s₁
                    (a.1, ({ sC₁ with base := a.2, kept := kept' }, z.2, false))) =
              (some .rejected, (sC₁, { s_fig8 with win := true }, false))
            rw [hfwd_new, hinj_new]
            rfl
          have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8) = false :=
            simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8)
              (by rw [hstep_none]; exact hinv.hsim.hmeta.hstop)
          have hstepSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (.A, w))) (sC, s_fig8, false) ec =
              pure (some .rejected, ((sC₁, { s_fig8 with win := true }, false), ec)) :=
            stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none .A w
              (sC, s_fig8, false) ec hinv.hsim.hec huse_none hstops_none _ hstepC_none rfl
          unfold CloseByStateC
          refine closeByRefinesH_of_win_eq_one (k₀ := 0) (by simp) ?_
          unfold runWinAtC
          rw [runSimCEager_inr_bind, hstepSim, pure_bind]
          exact iafs_evalDist_runSimCEager_win_true P ℓ Dh encPt encT decT idOf lam qep
            (cont (some .rejected)) (sC₁, { s_fig8 with win := true }, false) ec rfl _
            (fun z hz => by simp [hz])
    · have h2_0 := (hstep_res 0).2 hrej_f
      dsimp only at h2_0
      rw [hfig0_eq, hfig0] at h2_0
      dsimp only at h2_0
      rcases h2_0 with ⟨ht', hi', _, _, m_raw, hm_raw, _⟩
      let st_R' :=
        withEager
          (toGhost P
            { s_res with
              mir := mir'₀,
              pq := Function.update s_res.pq .A pq',
              unackA := s_res.unackA && Party.A != Party.A,
              chains := Function.update s_res.chains .A ((s_res.chains .A).set ci (g_res.accept i)) }
            .A st')
          rk sc pn
      have hguard_D0 : (s_R.win || (s_R.inTransit Party.B w).isSome || !s_R.safeInj 3 ||
          !((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false :=
        hguard_R
      have hnot_gt0' : ¬ (qep + 1 < 0) := by omega
      have hcorr_R : (.B, 0) ∉ s_R.corrs := by
        rw [hinv.hsim.hmeta.hcorrs_R]
        exact hspk_corr_of_simInvC P (InvB Inv q r) ℓ Dh encPt encT qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hinv.hsim hg₀_mem hg₀_none
      by_cases htriv0 : sC.base.mir.trivial 3 ⟨.B, 0, i⟩ = true
      · have htriv_R0 : s_R.trivial 3 ⟨.B, 0, i⟩ = true := by
          rw [hinv.hsim.hmeta.trivial_R, htriv0]
        let s_R' := s_R.accept .A st_R' ⟨.B, 0, i⟩
        have hstepD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (.A, w))) s_R =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
              pure (some (.accepted 0 i (some m)), s_R')) := by
          rw [stepR_inject_eq]
          dsimp only [Party.other]
          simp only [hguard_D0, Bool.false_eq_true, ↓reduceIte]
          congr 1; funext rc
          have h2_rc := (hstep_res rc).2 hrej_f
          dsimp only at h2_rc
          rw [hfig0_eq, hfig0] at h2_rc
          dsimp only at h2_rc
          rcases h2_rc with ⟨_, _, _, _, m_raw_rc, hm_raw_rc, hrec_rc⟩
          have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st .A) w rc =
              some (st_R', 0, i, m) := by
            unfold libsignalSessionScheme
            dsimp only
            rw [hst_R_eq, hrec_rc]
            dsimp only [Option.map]
            rw [← hm_raw_rc, hg_res_ep0]
          unfold injectRPure configEpoch0Distinguisher
          dsimp only [Party.other]
          simp only [hguard_D0, hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R, hnot_gt0', htriv_R0]
          rfl
        have hsafe_R : s_R.safeInj 3 = true := by
          rw [hinv.hsim.hmeta.safeInj_R, hsafe_mir]
        have hcomp_R : ∀ p ∈ s_R.comp, SM.healedBy s_R.tL 3 p.epoch = false := by
          rw [hinv.hsim.hmeta.hcomp_R, hinv.hsim.hmeta.htL_R]
          exact hinv.hsim.hcomp
        have heps0 : eps0Cond s_R' :=
          eps0Cond_of_inject_epoch0' hsafe_R htriv_R0 hcomp_R hcorr_R (by dsimp only [i]; omega)
        exact closeByStateC_inr_eps0_const_rc P ℓ Dh encPt encT decT idOf lam qep q δ post
          (.inl (.inr (.A, w))) cont s_R s_R' sC s_fig8 false ec winBefore (some (.accepted 0 i (some m))) hstepD0 heps0
      · have htriv0_f : sC.base.mir.trivial 3 ⟨.B, 0, i⟩ = false := Bool.eq_false_iff.mpr htriv0
        have htriv_R0 : s_R.trivial 3 ⟨.B, 0, i⟩ = false := by
          rw [hinv.hsim.hmeta.trivial_R, htriv0_f]
        let s_R' := { s_R with win := true }
        have hstepD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (.A, w))) s_R =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
              pure (some .rejected, s_R')) := by
          rw [stepR_inject_eq]
          dsimp only [Party.other]
          simp only [hguard_D0, Bool.false_eq_true, ↓reduceIte]
          congr 1; funext rc
          have h2_rc := (hstep_res rc).2 hrej_f
          dsimp only at h2_rc
          rw [hfig0_eq, hfig0] at h2_rc
          dsimp only at h2_rc
          rcases h2_rc with ⟨_, _, _, _, m_raw_rc, hm_raw_rc, hrec_rc⟩
          have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st .A) w rc =
              some (st_R', 0, i, m) := by
            unfold libsignalSessionScheme
            dsimp only
            rw [hst_R_eq, hrec_rc]
            dsimp only [Option.map]
            rw [← hm_raw_rc, hg_res_ep0]
          unfold injectRPure configEpoch0Distinguisher
          dsimp only [Party.other]
          simp only [hguard_D0, hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R, hnot_gt0', htriv_R0]
          rfl
        have heps0 : eps0Cond s_R' := Or.inr ⟨rfl, hcorr_R⟩
        exact closeByStateC_inr_eps0_const_rc P ℓ Dh encPt encT decT idOf lam qep q δ post
          (.inl (.inr (.A, w))) cont s_R s_R' sC s_fig8 false ec winBefore (some .rejected) hstepD0 heps0

end CryptoGames.LibsignalSM.Proofs.Refinement

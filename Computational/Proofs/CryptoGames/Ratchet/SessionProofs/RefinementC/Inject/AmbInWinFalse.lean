/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Inject step: ambiguous new chain outside receive-only window

Proves `closeByStateC_inject_newChain_amb_inWin_false_find_none` for `closeByStateC_inject_step` when an ambiguous new-chain injection occurs outside `inReceiveOnlyEpoch` and is not found after resolving.
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

private def iaf_cwin_preserves {α : Type}
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    gh.1.win = true →
    ∀ r ∈ support ((m.run sC).run gh), r.2.1.win = true

private theorem iaf_cwin_preserves_pure {α : Type} (a : α) :
    iaf_cwin_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (pure a) := by
  intro sC gh hgh r hr
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iaf_cwin_preserves_bind {α β : Type}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    (hm : iaf_cwin_preserves m) (hk : ∀ a, iaf_cwin_preserves (k a)) :
    iaf_cwin_preserves (m >>= k) := by
  intro sC gh hgh r hr
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨r₁, hr₁, hr⟩
  exact hk r₁.1.1 r₁.1.2 r₁.2 (hm sC gh hgh r₁ hr₁) r hr

private theorem iaf_cwin_preserves_get :
    iaf_cwin_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) get := by
  intro sC gh hgh r hr
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iaf_cwin_preserves_set (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    iaf_cwin_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (set sC') := by
  intro sC gh hgh r hr
  simp only [StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iaf_cwin_preserves_modify (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    iaf_cwin_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (modify f) := by
  intro sC gh hgh r hr
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iaf_probeHook_lift_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (y : Fig8Comp Pt ℓ α)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift y).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) y).run gh.1 >>= fun p => pure (p.1, (p.2, gh.2))) := rfl

private theorem iaf_cwin_preserves_ite {α : Type} {P_cond : Prop} [Decidable P_cond]
    {t e : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (ht : iaf_cwin_preserves t) (he : iaf_cwin_preserves e) :
    iaf_cwin_preserves (if P_cond then t else e) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem iaf_cwin_preserves_zoomB {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) :
    iaf_cwin_preserves (PQ := PQ) (runOnBaseState (probeHook fig qepF) x) := by
  intro sC gh hgh r hr
  change r ∈ support ((((probeHook fig qepF).lift (x.run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, iaf_probeHook_lift_run] at hr
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨p, hp, rfl⟩
  exact simulateQ_run_preserve
    (SM.oracleImpl fig 3 qepF SM.Config.h1)
    (fun s => s.win = true)
    (fun q' s hs => oracleImpl_run_of_win_true fig 3 qepF SM.Config.h1 q' s hs)
    (x.run sC.base) gh.1 hgh p hp

private theorem iaf_cwin_preserves_liftC {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) :
    iaf_cwin_preserves (PQ := PQ) (LibsignalSimC.liftC (probeHook fig qepF) x) := by
  intro sC gh hgh r hr
  change r ∈ support ((((probeHook fig qepF).lift x >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, iaf_probeHook_lift_run] at hr
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨p, hp, rfl⟩
  exact simulateQ_run_preserve
    (SM.oracleImpl fig 3 qepF SM.Config.h1)
    (fun s => s.win = true)
    (fun q' s hs => oracleImpl_run_of_win_true fig 3 qepF SM.Config.h1 q' s hs)
    x gh.1 hgh p hp

private theorem iaf_probeHook_probe_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).probe Q c').run gh =
      pure ((), (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)) := rfl

private theorem iaf_cwin_preserves_probe
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    iaf_cwin_preserves (PQ := PQ)
      (StateT.lift ((probeHook fig qepF).probe Q c') :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) Unit) := by
  intro sC gh hgh r hr
  change r ∈ support ((((probeHook fig qepF).probe Q c' >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, iaf_probeHook_probe_run] at hr
  simp only [pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iaf_cwin_preserves_guardC {α : Type}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : iaf_cwin_preserves m) :
    iaf_cwin_preserves (guardC m) := by
  unfold guardC
  refine iaf_cwin_preserves_bind iaf_cwin_preserves_get fun sC => ?_
  exact iaf_cwin_preserves_ite (iaf_cwin_preserves_pure none) hm

private theorem iaf_cwin_preserves_simSendC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    iaf_cwin_preserves (simSendC P qep fig (probeHook fig qepF) Q m₀ chal r) := by
  unfold simSendC
  refine iaf_cwin_preserves_bind (iaf_cwin_preserves_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact iaf_cwin_preserves_pure none
  | some w =>
    refine iaf_cwin_preserves_bind iaf_cwin_preserves_get fun sC => ?_
    exact iaf_cwin_preserves_bind (iaf_cwin_preserves_set _) fun _ => iaf_cwin_preserves_pure (some w)

private theorem iaf_cwin_preserves_fwdAnswerC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    iaf_cwin_preserves (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine iaf_cwin_preserves_bind (iaf_cwin_preserves_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact iaf_cwin_preserves_zoomB (PQ := PQ) fig qepF _
  | some r =>
    cases r <;>
      first
      | exact iaf_cwin_preserves_zoomB (PQ := PQ) fig qepF _
      | exact iaf_cwin_preserves_bind (iaf_cwin_preserves_modify _) fun _ =>
          iaf_cwin_preserves_zoomB (PQ := PQ) fig qepF _

private theorem iaf_cwin_preserves_resyncC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    iaf_cwin_preserves (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact iaf_cwin_preserves_pure _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine iaf_cwin_preserves_bind (iaf_cwin_preserves_liftC fig qepF _) fun res => ?_
    cases res with
    | none => exact iaf_cwin_preserves_pure _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        exact iaf_cwin_preserves_bind (iaf_cwin_preserves_modify _) fun _ =>
          iaf_cwin_preserves_zoomB (PQ := PQ) fig qepF _
      | _ => exact iaf_cwin_preserves_pure _

private theorem iaf_cwin_preserves_fwdC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    iaf_cwin_preserves (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold fwdC
  refine iaf_cwin_preserves_bind iaf_cwin_preserves_get fun sC => ?_
  cases honestC with
  | none => exact iaf_cwin_preserves_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c'
  | some c =>
    refine iaf_cwin_preserves_ite ?_ (iaf_cwin_preserves_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c')
    cases predictReceiveWithSnapshots (fig := fig) (fs := fs) P sC Q w c c' with
    | some r => exact iaf_cwin_preserves_resyncC qep fig fs qepF Q w ci? T pq' c r
    | none =>
      exact iaf_cwin_preserves_bind (iaf_cwin_preserves_probe fig qepF Q c') fun _ =>
        iaf_cwin_preserves_pure _

private theorem iaf_cwin_preserves_fwdEvictC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    iaf_cwin_preserves (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine iaf_cwin_preserves_bind iaf_cwin_preserves_get fun sC => ?_
  refine iaf_cwin_preserves_ite ?_ (iaf_cwin_preserves_fwdAnswerC qep fig fs qepF Q w isDel none T pq' c')
  exact iaf_cwin_preserves_bind (iaf_cwin_preserves_probe fig qepF Q c') fun _ => iaf_cwin_preserves_pure _

private theorem iaf_cwin_preserves_simRecvC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    iaf_cwin_preserves (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  unfold simRecvC
  generalize (2 ^ 32 : ℕ) = maxI
  generalize (25000 : ℕ) = maxSkip
  refine iaf_cwin_preserves_bind iaf_cwin_preserves_get fun sC => ?_
  dsimp only
  refine iaf_cwin_preserves_ite (iaf_cwin_preserves_pure _) ?_
  refine iaf_cwin_preserves_ite (iaf_cwin_preserves_pure _) ?_
  refine iaf_cwin_preserves_ite (iaf_cwin_preserves_pure _) ?_
  refine iaf_cwin_preserves_ite (iaf_cwin_preserves_pure _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact iaf_cwin_preserves_pure _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine iaf_cwin_preserves_ite (iaf_cwin_preserves_pure _) ?_
    refine iaf_cwin_preserves_ite (iaf_cwin_preserves_pure _) ?_
    cases P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact iaf_cwin_preserves_pure _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine iaf_cwin_preserves_ite (iaf_cwin_preserves_pure _) ?_
        exact iaf_cwin_preserves_fwdC P qep fig fs qepF Q w isDel
          (some ci) h.senderRatchetKey pq' _ _
      | none =>
        dsimp only
        refine iaf_cwin_preserves_ite (iaf_cwin_preserves_pure _) ?_
        refine iaf_cwin_preserves_ite (iaf_cwin_preserves_pure _) ?_
        refine iaf_cwin_preserves_ite
          (iaf_cwin_preserves_bind (iaf_cwin_preserves_modify _) fun _ => ?_) ?_ <;>
        · refine iaf_cwin_preserves_ite (iaf_cwin_preserves_pure _) ?_
          cases decT h.senderRatchetKey with
          | none => exact iaf_cwin_preserves_pure _
          | some T =>
            exact iaf_cwin_preserves_ite
              (iaf_cwin_preserves_fwdEvictC qep fig fs qepF Q w isDel h.senderRatchetKey pq' _)
              (iaf_cwin_preserves_fwdC P qep fig fs qepF Q w isDel none h.senderRatchetKey pq' _ _)

private theorem iaf_cwin_preserves_simCorrC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    iaf_cwin_preserves (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  unfold simCorrC
  refine iaf_cwin_preserves_bind iaf_cwin_preserves_get fun sC => ?_
  refine iaf_cwin_preserves_ite (iaf_cwin_preserves_pure _) ?_
  refine iaf_cwin_preserves_bind (iaf_cwin_preserves_liftC fig qepF _) fun res => ?_
  cases res with
  | none => exact iaf_cwin_preserves_pure _
  | some st =>
    exact iaf_cwin_preserves_bind (iaf_cwin_preserves_set _) fun _ => iaf_cwin_preserves_pure _

private theorem iaf_cwin_stepSimCNone_preserve_win_true (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
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
  have hpres : iaf_cwin_preserves
      (simImplC P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh (.inr q)) := by
    rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
    · exact iaf_cwin_preserves_guardC (iaf_cwin_preserves_simSendC P qep _ (qep + 1) Q m₀ none r')
    · exact iaf_cwin_preserves_guardC (iaf_cwin_preserves_simSendC P qep _ (qep + 1) Q m₀ (some m₁) r')
    · exact iaf_cwin_preserves_guardC (iaf_cwin_preserves_simRecvC P encT decT qep _ _ (qep + 1) Q w true)
    · exact iaf_cwin_preserves_guardC (iaf_cwin_preserves_simRecvC P encT decT qep _ _ (qep + 1) Q w false)
    · exact iaf_cwin_preserves_guardC (iaf_cwin_preserves_simCorrC P encT _ (qep + 1) Dh Q)
  exact hpres x.1 x.2 hwin r hr

private theorem iaf_cwin_stepSimC_preserve_win_true (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimC P ℓ Dh encPt encT decT idOf lam qep none q x), z.2.2.1.win = true := by
  rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact iaf_cwin_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin
  · exact iaf_cwin_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin
  · intro z hz
    simp only [stepSimC] at hz
    split at hz
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨r, hr, rfl⟩
      exact stepSim_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep none _ x.sim hwin rfl r hr
    · exact iaf_cwin_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin z hz
  · intro z hz
    simp only [stepSimC] at hz
    split at hz
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨r, hr, rfl⟩
      exact stepSim_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep none _ x.sim hwin rfl r hr
    · exact iaf_cwin_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin z hz
  · exact iaf_cwin_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin

private theorem iaf_stepSimCEager_preserve_win_true (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
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
    exact iaf_cwin_stepSimC_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin res hres
  · simp only [stepSimCEager, stepSimCEagerInject] at hz
    rw [simRecvUsesCoin_of_win_true P encT decT none Q w false x.sim hwin, evictStopsC_none] at hz
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, _, _, rfl⟩
    exact iaf_cwin_stepSimC_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin res hres
  · simp only [stepSimCEager, stepSimCEagerCorr, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, _, _, rfl⟩
    exact iaf_cwin_stepSimC_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin res hres

private theorem iaf_evalDist_runSimCEager_win_true {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
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
  exact iaf_stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep q s.1 s.2 hs

private theorem iaf_closeByStateC_inr_both_win_const_rc {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl fl' : Bool)
    (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm)
    (hR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (ans, s_R')))
    (hSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) ec =
      pure (ans, ((sC', s_fig8', fl'), ec')))
    (hwin_R : s_R'.win = true)
    (hwin_fig8 : s_fig8'.win = true) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  unfold CloseByStateC
  refine closeByRefinesH_iff.mpr (closeByRefines_of_both_win_eq_one _ _ _ _ _ _ ?_ ?_)
  · rw [runRCont_inr_bind, hR]
    simp only [bind_assoc, pure_bind]
    rw [congrFun (congrArg DFunLike.coe (OracleComp.evalDist_bind_const ($ᵗ BitVec 256) _)) {true}]
    exact evalDist_runRCont_win_true (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (cont ans) s_R' hwin_R _
      (fun z hz => by simp [hz])
  · simp only [runSimCEager_inr_bind, hSim, pure_bind]
    exact iaf_evalDist_runSimCEager_win_true P ℓ Dh encPt encT decT idOf lam qep
      (cont ans) (sC', s_fig8', fl') ec' hwin_fig8 _
      (fun z hz => by simp [hz])

private theorem iaf_mkC_newChain_eq (P : Params PQ PQC) (Inv : PQ → Prop) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hrtT : ∀ T, decT (encT T) = some T)
    (Q : Party) (w : List (BitVec 8))
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (salt : Salt)
    (hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false)
    (T : Pt) (hencT : encT T = h.senderRatchetKey) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let honestC := (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    (match honestC with
     | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
     | none => ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))) =
      ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) := by
  intro ser tag i honestC
  have hinj := encT_injective hrtT
  dsimp only [honestC]
  cases hfind_hon : s.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none => rfl
  | some wc =>
    have hmem : wc ∈ s.honest := List.mem_of_find?_eq_some hfind_hon
    have hpred := List.find?_some hfind_hon
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    rcases wc with ⟨w_c, c_h⟩
    rcases hpred with ⟨hw_eq, _⟩
    dsimp only at hw_eq
    rw [hw_eq] at hmem
    simp only [hfind_hon, Option.map_some, beq_eq_false_iff_ne, Ne, Option.some.injEq,
      decide_eq_true_eq] at hevict
    have hc_ep : c_h.1.1 = s.mir.epoch Q + 1 := Decidable.of_not_not hevict
    dsimp only [Option.map]
    split
    · rename_i hsalt
      rcases (hinv.hhon (w, c_h) hmem).1 with
        ⟨_, _, _, hraw, _, _, hT_c, h₀, body₀, hparse₀, _, hsrk, hctr, _⟩
      have hhb : (h, body) = (h₀, body₀) := Option.some.inj (hparse.symm.trans hparse₀)
      rcases Prod.mk.inj hhb with ⟨rfl, rfl⟩
      have hT_eq : T = Dh.dh (epExp c_h.1.1) Dh.base := hinj (hencT.trans hsrk)
      rcases c_h with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
      dsimp only at hc_ep hT_c hT_eq hctr hraw hsalt ⊢
      rw [hc_ep, hT_c, ← hT_eq, ← hctr, hraw, hsalt]
    · rfl

private theorem iaf_fwdCPure_false_rejected (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g g' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (hfwd : fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
      sC'.base Q c' g = (some .rejected, g')) :
    fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' honestC c' (sC', g, fl) =
      (some .rejected, (sC', g', fl)) := by
  have hplain : fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' honestC c' (sC', g, fl) =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' none c' (sC', g, fl) := by
    unfold fwdCPure
    cases honestC <;> simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hplain]
  unfold fwdCPure
  dsimp only
  rw [hfwd]
  rfl

/-- Closes an ambiguous new-chain injection outside `inReceiveOnlyEpoch` when the resolved chain is not found: every acceptance wins in Fig. 8, and rejection increments `amb` while preserving `SimInvCX`. -/
theorem closeByStateC_inject_newChain_amb_inWin_false_find_none {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hfind_res : ((resolveSim (encT (Dh.dh x₀ Dh.base)) sC.base).chains Q).findIdx?
      (fun g => g.key == some h.senderRatchetKey) = none)
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
  have hstop0 := (simRecvStepEager_inject_ambC P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep q r x₀
    Q w s_R sC.base s_fig8 ec winBefore epExp hinv.hsim hguard hlen hparse haddrs hspqr hpan hfind hevict hzero hamb_b).1
  have hspk_amb : (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = true := by
    rw [hinw, Bool.false_or] at hamb_b
    exact hamb_b
  have hst_R_eq : s_R.st Q = toGhost P s_res Q (s_fig8.st Q) := by
    rw [hinv.hsim.hst_R Q, expectedGhost_of_inWin_false P Dh encPt spkKey sC.base Q (s_fig8.st Q) (ec Q) hinw]
  have hon_img : ratchetKeyAdmissible P.codec decT encT w = true := by
    revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  rcases lOnImage_some_of_parse P decT encT w h body hon_img hlen hparse with ⟨T, hdecT, hencT⟩
  have hT_ne0 : T ≠ 0 := by
    intro h0
    subst h0
    have h0' : (decT h.senderRatchetKey == some 0) = true := by simp [hdecT]
    rw [h0'] at hzero
    exact Bool.noConfusion hzero
  rcases hinv.hsim.hspur Q with ⟨rk_base, T_base, _, hninw, _⟩
  rcases hninw hinw with ⟨hγ, _, ⟨vS, hvS, _⟩⟩
  have hrecv : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hinv.hsim.htcur Q]
    exact sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
  have hno_none_res : ∀ g ∈ s_res.chains Q, g.key.isNone = false :=
    resolveSim_chains_no_none' spkKey sC.base Q hinv.hsim.hchainsB_none
  have hdummy : ∀ g ∈ s_res.chains Q, g.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro g hg hgn
    have hgn' := hno_none_res g hg
    simp [hgn] at hgn'
  have hchains_ep : ∀ g ∈ s_res.chains Q, g.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g hg
    have hmem_ep : g.epoch ∈ (resolveSpkChains spkKey sC.base.chains Q).map (·.epoch) := List.mem_map_of_mem hg
    rw [resolveSpkChains_map_epoch spkKey sC.base.chains Q, List.mem_map] at hmem_ep
    rcases hmem_ep with ⟨g₀, hg₀, hgep⟩
    have hle := (hinv.hsim.hchains_sync Q g₀ hg₀).1
    have htcur := hinv.hsim.htcur Q
    omega
  let i := h.counter.toNat + 1
  let t := (s_fig8.st Q).tcur + 1
  let pos : SM.Pos := ⟨Q.other, t, i⟩
  let mir' := sC.base.mir.accept Q () pos
  have hmir'_ep : mir'.epoch Q = (s_fig8.st Q).tcur + 1 := by
    have htcur := (hinv.hsim.htcur Q).symm
    unfold mir' SM.GameState.accept SM.GameState.delete
    dsimp only [pos, t]
    rw [Function.update_self, htcur]
    exact Nat.max_eq_right (Nat.le_succ _)
  have hstep_all := fun rc =>
    receive_newChain_toGhost_eq P Dh encPt encT idOf lam hX hid
      s_res Q (s_fig8.st Q) (hinv.hsim.hst_id Q) (hinv.hsim.htcur Q).symm hrecv
      (epExp (sC.base.mir.epoch Q)) hγ vS hvS w hlen h body hparse haddrs
      pq' salt hspqr hpan hfind_res hdummy hchains_ep T hT_ne0 hencT mir' hmir'_ep rc
  let g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have huse_none : simRecvUsesCoin P encT decT none Q w false (sC.base, s_fig8) = false :=
    simRecvUsesCoin_none P encT decT Q w false (sC.base, s_fig8)
  have hnone_div : ((none : Option ℕ) == some sC.base.amb) = false := rfl
  let s₁ : SimState PQ Pt ℓ := { sC.base with amb := sC.base.amb + 1 }
  have hs₁_stop : ({ sC.base with amb := sC.base.amb + 1, stopped := false } : SimState PQ Pt ℓ) = s₁ := by
    dsimp only [s₁]
    generalize hs : sC.base = sb
    have hst : sb.stopped = false := hs ▸ hinv.hsim.hmeta.hstop
    cases sb
    dsimp only at hst
    subst hst
    rfl
  by_cases hjump : (25000 < i - 1 || 2 ^ 32 ≤ i) = true
  · have hrej_init : g_init.rejects i = true := by
      unfold GhostChain.rejects
      dsimp only [g_init]
      have hi_pos : ¬ i ≤ 0 := by dsimp only [i]; omega
      simp only [hi_pos, ↓reduceIte, Nat.sub_zero]
      exact hjump
    have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (sC.base, s_fig8) =
        (some .rejected, (s₁, s_fig8)) := by
      unfold simRecvStep
      simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hevict, hzero, hamb_b, hnone_div, hinw, hspk_amb, Bool.false_or,
        show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hjump,
        hs₁_stop]
    have hstepC_none : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
        (some .rejected, ({ sC with base := s₁ }, s_fig8, false)) := by
      unfold simRecvStepCGen
      simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hevict, hzero, hamb_b, hinw, hspk_amb, Bool.false_or,
        show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hjump,
        hs₁_stop]
    have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8) = false :=
      simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8)
        (by rw [hstep_none]; exact hinv.hsim.hmeta.hstop)
    have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
        (sC, s_fig8, false) ec =
        pure (some .rejected, (({ sC with base := s₁ }, s_fig8, false), ec)) :=
      stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec hinv.hsim.hec huse_none hstops_none _ hstepC_none rfl
    have hrcv_R : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
      intro rc
      unfold libsignalSessionScheme
      dsimp only
      rw [hst_R_eq, (hstep_all rc).1 hrej_init]
      rfl
    exact closeByStateC_inject_amb_reject (hnpW := recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
      Q w cont s_R sC s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0 hnone_eager
      (ih (some .rejected))
  · have hjump_f : (25000 < i - 1 || 2 ^ 32 ≤ i) = false := Bool.eq_false_iff.mpr hjump
    have hrej_init_f : g_init.rejects i = false := by
      unfold GhostChain.rejects
      dsimp only [g_init]
      have hi_pos : ¬ i ≤ 0 := by dsimp only [i]; omega
      simp only [hi_pos, ↓reduceIte, Nat.sub_zero]
      exact hjump_f
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let c : Fig8C Pt := ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    let honestC := (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    let c_mk : Fig8C Pt :=
      match honestC with
      | some c₀ => if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀ else ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
      | none => ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    have hc_eq : ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = c := by
      dsimp only [t, c]; rw [hinv.hsim.htcur Q]
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    have hhon_wire : ∀ wc ∈ sC.base.honest, wc.1 = LibsignalSim.toWire wc.2 :=
      fun wc hwc => (hinv.hsim.hhon wc hwc).1.1
    have htr_mir : (sC.base.mir.inTransit Q.other w).isSome = false := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> simp
    have hsafe_mir : sC.base.mir.safeInj 3 = true := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;> simp
    have hmkC : c_mk = c := iaf_mkC_newChain_eq P (InvB Inv q r) Dh encPt encT decT qep q r x₀
      hinv.hsim hdec Q w hparse salt hevict T hencT
    have htoWire : LibsignalSim.toWire c = w :=
      toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T) i (effectiveHkdfSalt32 salt)
    have hfwd : fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c s_fig8 =
        injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 :=
      fwdPure_of_inTransit_false sm 3 (qep + 1) SM.Config.h1 s₁ Q w c s_fig8 hhon_wire htoWire htr_mir
    have htr_fig8 : (s_fig8.inTransit Q.other c).isSome = false :=
      inTransit_fig8_isSome_of_toWire hinv.hsim.hmeta Q w c htoWire htr_mir
    have hguard_fig8 : (s_fig8.win || (s_fig8.inTransit Q.other c).isSome || !s_fig8.safeInj 3) = false := by
      rw [hinv.hsim.hmeta.hwin_fig8, htr_fig8, hinv.hsim.hmeta.safeInj_fig8 3, hsafe_mir]
      rfl
    have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !s_R.safeInj 3 ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hinv.hsim.hmeta.hwin_R, hinv.hsim.hmeta.inTransit_R_isSome, hinv.hsim.hmeta.safeInj_R]
      simpa [configR1OnCurve] using hguard
    cases hfig : sm.receive (s_fig8.st Q) c with
    | none =>
      have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 = (some .rejected, s_fig8) := by
        unfold injectPure
        simp [hguard_fig8, hfig]
      have hfig_t : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
          (((s_fig8.st Q).tcur + 1, some T), h.counter.toNat + 1,
            (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) = none := by
        change sm.receive (s_fig8.st Q) ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = none
        rw [hc_eq, hfig]
      have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (sC.base, s_fig8) =
          (some .rejected, (s₁, s_fig8)) := by
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStep
        simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hamb_b, hnone_div, hinw, hspk_amb, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT, hs₁_stop]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c_mk s_fig8
                let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 s₁
                (a.1, (a.2, z.2))) = (some .rejected, (s₁, s_fig8))
        rw [hmkC, hfwd, hinj_fig8]
        rfl
      have hstepC_none : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
          (some .rejected, ({ sC with base := s₁ }, s_fig8, false)) := by
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStepCGen
        simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hamb_b, hinw, hspk_amb, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT, hs₁_stop]
        exact iaf_fwdCPure_false_rejected P ℓ Dh encPt encT idOf lam qep Q w false none
          h.senderRatchetKey pq' honestC c_mk { sC with base := s₁ } s_fig8 s_fig8 false
          (by dsimp only; rw [hmkC, hfwd, hinj_fig8])
      have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8) = false :=
        simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8)
          (by rw [hstep_none]; exact hinv.hsim.hmeta.hstop)
      have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
          (sC, s_fig8, false) ec =
          pure (some .rejected, (({ sC with base := s₁ }, s_fig8, false), ec)) :=
        stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
          (sC, s_fig8, false) ec hinv.hsim.hec huse_none hstops_none _ hstepC_none rfl
      have hrcv_R : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
        intro rc
        have h2_rc := (hstep_all rc).2 hrej_init_f
        dsimp only at h2_rc
        rw [hfig_t] at h2_rc
        unfold libsignalSessionScheme
        dsimp only
        rw [hst_R_eq, h2_rc]
        rfl
      exact closeByStateC_inject_amb_reject (hnpW := recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan) P Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
        Q w cont s_R sC s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0 hnone_eager
        (ih (some .rejected))
    | some val =>
      rcases val with ⟨st', t', i', ⟨pub, m⟩⟩
      have hfig_t : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
          (((s_fig8.st Q).tcur + 1, some T), h.counter.toNat + 1,
            (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) =
          some (st', t', i', (pub, m)) := by
        change sm.receive (s_fig8.st Q) ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = some (st', t', i', (pub, m))
        rw [hc_eq, hfig]
      have h2_0 := (hstep_all 0).2 hrej_init_f
      dsimp only at h2_0
      rw [hfig_t] at h2_0
      rcases h2_0 with ⟨ht', hi', _, _, _⟩
      have ht_eq : t = sC.base.mir.epoch Q + 1 := by dsimp only [t]; rw [hinv.hsim.htcur Q]
      subst ht' hi'
      have hnot_gt : ¬ (qep + 1 < t) := by
        have hep_le := hinv.hsim.hep_le Q
        omega
      have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < t) := by omega
      have htriv_f : sC.base.mir.trivial 3 ⟨Q.other, t, i⟩ = false :=
        trivial_false_of_newChain_inject hsafe_mir hinv.hsim.hcomp Q ⟨Q.other, t, i⟩
          (by dsimp only; omega)
      have htriv_R : s_R.trivial 3 ⟨Q.other, t, i⟩ = false := by
        rw [hinv.hsim.hmeta.trivial_R, htriv_f]
      have htriv_fig8 : s_fig8.trivial 3 ⟨Q.other, t, i⟩ = false := by
        rw [hinv.hsim.hmeta.trivial_fig8, htriv_f]
      let s_fig8' := { s_fig8 with win := true }
      have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 =
          (some .rejected, s_fig8') := by
        unfold injectPure
        simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig,
          show ¬ (qep + 1 + 1 < (s_fig8.st Q).tcur + 1) from hnot_gt_fig8,
          show s_fig8.trivial 3 ⟨Q.other, (s_fig8.st Q).tcur + 1, h.counter.toNat + 1⟩ = false from htriv_fig8]
        rfl
      have hstep_sim_none :
          simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (sC.base, s_fig8) =
            (some .rejected, (s₁, s_fig8')) := by
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStep
        simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hamb_b, hnone_div, hinw, hspk_amb, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT, hs₁_stop]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c_mk s_fig8
                let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 s₁
                (a.1, (a.2, z.2))) = _
        rw [hmkC, hfwd, hinj_fig8]
        rfl
      have hstepC_none :
          simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
            (some .rejected, ({ sC with base := s₁ }, s_fig8', false)) := by
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStepCGen
        simp only [hinv.hsim.hmeta.hstop, hinv.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hamb_b, hinw, hspk_amb, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT, hs₁_stop]
        exact iaf_fwdCPure_false_rejected P ℓ Dh encPt encT idOf lam qep Q w false none
          h.senderRatchetKey pq' honestC c_mk { sC with base := s₁ } s_fig8 s_fig8' false
          (by dsimp only; rw [hmkC, hfwd, hinj_fig8])
      have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8) = false :=
        simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8)
          (by rw [hstep_sim_none]; exact hinv.hsim.hmeta.hstop)
      have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
          (sC, s_fig8, false) ec =
          pure (some .rejected, (({ sC with base := s₁ }, s_fig8', false), ec)) :=
        stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
          (sC, s_fig8, false) ec hinv.hsim.hec huse_none hstops_none _ hstepC_none rfl
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          (.inl (.inr (Q, w))) s_R =
          (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
            pure (some .rejected, { s_R with win := true })) := by
        rw [stepR_inject_eq]
        simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
        congr 1; funext rc
        have h2_rc := (hstep_all rc).2 hrej_init_f
        dsimp only at h2_rc
        rw [hfig_t] at h2_rc
        rcases h2_rc with ⟨_, _, _, _, m_raw, hm_raw, hrec_rc, _⟩
        unfold injectRPure
        simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
        unfold libsignalSessionScheme
        dsimp only
        rw [hst_R_eq, hrec_rc, Option.map_some]
        simp only [show ¬ (qep + 1 < (s_fig8.st Q).tcur + 1) from hnot_gt,
          show s_R.trivial 3 ⟨Q.other, (s_fig8.st Q).tcur + 1, h.counter.toNat + 1⟩ = false from htriv_R,
          Bool.false_eq_true, ↓reduceIte]
        rfl
      exact iaf_closeByStateC_inr_both_win_const_rc P ℓ Dh encPt encT decT idOf lam qep q δ post
        (.inl (.inr (Q, w))) cont s_R { s_R with win := true }
        sC { sC with base := s₁ } s_fig8 s_fig8' false false ec ec winBefore
        (some .rejected) hstepR hnone_eager rfl rfl

end CryptoGames.LibsignalSM.Proofs.Refinement

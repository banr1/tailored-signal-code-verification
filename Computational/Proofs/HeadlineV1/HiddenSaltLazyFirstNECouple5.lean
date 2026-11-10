/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple4
import ProofLib.SepLogic.WP.StateNorm

/-!
# Per-Query Cell Coupling for `deliver` and `inject`

**Checked by Lean.** Proves `runCellStep` forwarding lemmas, post-step cell-sum bounds, and `inject`
synchronization for coupling `firstNESimImpl` with `cellSimRun`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

theorem onAccept_run_pure {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (t_acc i_acc : ℕ) (m : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (b : SimState PQ Pt ℓ) :
    ∃ (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ),
      (onAccept (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
        Q w isDel t_acc i_acc m ci? T pq').run b = pure (ans, b') ∧
      b'.honest = b.honest ∧
      b'.stopped = b.stopped ∧
      (isDel = false →
        (b'.mir = b.mir ∨
         b'.mir = { b.mir with win := true } ∨
         b'.mir = b.mir.accept Q () ⟨Q.other, t_acc, i_acc⟩)) := by
  unfold onAccept putS
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with h1 h2
    · exact ⟨_, _, rfl, rfl, rfl, fun _ => Or.inl rfl⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun _ => Or.inr (Or.inr rfl)⟩
    · exact ⟨_, _, rfl, rfl, rfl, fun _ => Or.inr (Or.inl rfl)⟩
  · simp only [↓reduceIte]
    cases hInT : b.mir.inTransit Q.other w with
    | none => exact ⟨_, _, rfl, rfl, rfl, by intro h; cases h⟩
    | some r =>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      exact ⟨_, _, rfl, rfl, rfl, by intro h; cases h⟩

theorem onAnswer_run_pure {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (b : SimState PQ Pt ℓ) :
    ∃ (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ),
      (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
        Q w isDel ci? T pq' res).run b = pure (ans, b') ∧
      b'.honest = b.honest ∧
      b'.stopped = b.stopped := by
  unfold onAnswer
  rcases res with _ | (_ | ⟨t_acc, i_acc, pm⟩)
  · exact ⟨some .rejected, b, rfl, rfl, rfl⟩
  · exact ⟨some .rejected, b, rfl, rfl, rfl⟩
  · obtain ⟨ans, b', hrun, hhon, hstop, _⟩ :=
      onAccept_run_pure qep Q w isDel t_acc i_acc ((pm.map (·.2)).getD default) ci? T pq' b
    exact ⟨ans, b', hrun, hhon, hstop⟩

theorem runCellStep_zoomB_onAnswer {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ)
    (hrun : (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w isDel ci? T pq' res).run sC.base = pure (ans, b')) :
    runCellStep fig qep t tL
      (LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ)
        (onAnswer (qep := qep) Q w isDel ci? T pq' res))
      sC sent m' s_cell =
      pure ((((ans, { sC with base := b' }), sent), m'), s_cell) := by
  rw [runCellStep_zoomB, hrun]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]

theorem runCellStep_zoomB_liftQ {PQ Pt α : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (x : Fig8Comp Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL
      (LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ) (liftQ x)) sC sent m' s_cell =
      runCellStep fig qep t tL
        (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) x) sC sent m' s_cell := by
  rw [runCellStep_zoomB, runCellStep_liftC]
  unfold liftQ
  simp only [StateT_run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    bind_assoc, pure_bind]

theorem runCellStep_zoomB_fwd {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party) (c : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL
      (LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ) (fwd Q c)) sC sent m' s_cell =
      if (sC.base.honest.any fun wc =>
          decide (wc.2 = c) && (sC.base.mir.inTransit Q.other wc.1).isSome) = true then
        runCellStep fig qep t tL
          (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (SM.deliverQuery Q c)) sC sent m' s_cell
      else
        runCellStep fig qep t tL
          (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (SM.injectQuery Q c)) sC sent m' s_cell := by
  rw [runCellStep_zoomB]
  unfold fwd
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hInT
  · rw [← runCellStep_zoomB_liftQ, runCellStep_zoomB]
  · rw [← runCellStep_zoomB_liftQ, runCellStep_zoomB]

theorem zoomB_run {PQ Pt α : Type} {ℓ : ℕ} {M : Type → Type} [Monad M]
    (H : Hook Pt ℓ M) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (LibsignalSimC.runOnBaseState H x).run sC =
      (H.lift (x.run sC.base) >>= fun p => pure (p.1, { sC with base := p.2 })) :=
  rfl

theorem liftC_run {PQ Pt α : Type} {ℓ : ℕ} {M : Type → Type} [Monad M]
    (H : Hook Pt ℓ M) (x : Fig8Comp Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (LibsignalSimC.liftC H x).run sC =
      (H.lift x >>= fun a => pure (a, sC)) :=
  rfl

theorem zoomB_probeHook_onAnswer_run {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ)
    (hrun : (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w isDel ci? T pq' res).run sC.base = pure (ans, b')) :
    (((LibsignalSimC.runOnBaseState (probeHook fig (qep + 1))
        (onAnswer (qep := qep) Q w isDel ci? T pq' res)).run sC).run (g, fl)) =
      pure ((ans, { sC with base := b' }), (g, fl)) := by
  rw [zoomB_run, StateT.run_bind, probeHook_lift_run, hrun]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]

theorem zoomB_probeHook_liftQ_run {PQ Pt α : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (x : Fig8Comp Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool) :
    (((LibsignalSimC.runOnBaseState (probeHook fig (qep + 1)) (liftQ x)).run sC).run (g, fl)) =
      (((LibsignalSimC.liftC (probeHook fig (qep + 1)) x).run sC).run (g, fl)) := by
  rw [zoomB_run, liftC_run, StateT.run_bind, StateT.run_bind, probeHook_lift_run,
    probeHook_lift_run]
  unfold liftQ
  simp only [StateT_run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    bind_assoc, pure_bind]

theorem zoomB_probeHook_fwd_run {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (c : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool) :
    (((LibsignalSimC.runOnBaseState (probeHook fig (qep + 1)) (fwd Q c)).run sC).run (g, fl)) =
      if (sC.base.honest.any fun wc =>
          decide (wc.2 = c) && (sC.base.mir.inTransit Q.other wc.1).isSome) = true then
        (((LibsignalSimC.liftC (probeHook fig (qep + 1))
            (SM.deliverQuery Q c)).run sC).run (g, fl))
      else
        (((LibsignalSimC.liftC (probeHook fig (qep + 1))
            (SM.injectQuery Q c)).run sC).run (g, fl)) := by
  have hfwd :
      (fwd Q c).run sC.base =
        if (sC.base.honest.any fun wc =>
            decide (wc.2 = c) && (sC.base.mir.inTransit Q.other wc.1).isSome) = true then
          (liftQ (SM.deliverQuery Q c)).run sC.base
        else
          (liftQ (SM.injectQuery Q c)).run sC.base := by
    unfold fwd
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> rfl
  split_ifs with hInT
  · rw [← zoomB_probeHook_liftQ_run, zoomB_run, zoomB_run, hfwd]
    simp only [hInT, ↓reduceIte]
  · rw [← zoomB_probeHook_liftQ_run, zoomB_run, zoomB_run, hfwd]
    simp only [hInT, Bool.false_eq_true, ↓reduceIte]

theorem fwdC_false_eq {PQ PQC Pt : Type} {ℓ : ℕ} [DecidableEq Pt]
    {M : Type → Type} [Monad M] [LawfulMonad M]
    (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    LibsignalSimC.fwdC P qep fig fs H Q w false ci? T pq' honestC c' =
      LibsignalSimC.fwdAnswerC qep fig fs H Q w false ci? T pq' c' := by
  ext sC
  unfold LibsignalSimC.fwdC
  cases honestC <;> simp

theorem fwdEvictC_false_eq {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt]
    {M : Type → Type} [Monad M] [LawfulMonad M]
    (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Q : Party) (w : List (BitVec 8)) (T : PublicKey)
    (pq' : PQ) (c' : Fig8C Pt) :
    LibsignalSimC.fwdEvictC qep fig fs H Q w false T pq' c' =
      LibsignalSimC.fwdAnswerC qep fig fs H Q w false none T pq' c' := by
  ext sC
  unfold LibsignalSimC.fwdEvictC
  simp

theorem ite_modify_bind_run {σ α : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (c : Bool) (f : σ → σ) (k : PUnit → StateT σ M α) (s : σ) :
    (if c = true then modify f >>= k else k ⟨⟩).run s =
      (k ⟨⟩).run (if c = true then f s else s) := by
  cases c <;> simp [StateT.run_bind, StateT.run_modify, pure_bind]

def updKeptOnRes {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (c' : Fig8C Pt) (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) : LibsignalToModularSchemeSimState PQ Pt ℓ :=
  match res with
  | some (.accepted _ _ _) =>
    let k' := LibsignalSimC.Kept.recv (fig := fig) (fs := fs) c' (sC.kept Q)
    { sC with kept := Function.update sC.kept Q k' }
  | _ => sC

@[simp]
theorem updKeptOnRes_base {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (c' : Fig8C Pt) (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (updKeptOnRes fig fs Q c' res sC).base = sC.base := by
  unfold updKeptOnRes
  cases res with
  | none => rfl
  | some r => cases r <;> rfl

theorem fwdAnswerC_run {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt]
    {M : Type → Type} [Monad M] [LawfulMonad M]
    (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (LibsignalSimC.fwdAnswerC qep fig fs H Q w isDel ci? T pq' c').run sC =
      ((LibsignalSimC.runOnBaseState H (fwd Q c')).run sC >>= fun z =>
        (LibsignalSimC.runOnBaseState H (onAnswer (qep := qep) Q w isDel ci? T pq' z.1)).run
          (updKeptOnRes fig fs Q c' z.1 z.2)) := by
  unfold LibsignalSimC.fwdAnswerC updKeptOnRes
  rw [StateT.run_bind]
  refine bind_congr fun ⟨res, sC₁⟩ => ?_
  cases res with
  | none => simp
  | some r =>
    cases r <;> simp [StateT.run_bind, StateT.run_modify, pure_bind]

theorem probeHook_liftC_deliver_run {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (c : Fig8C Pt) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool) :
    ((LibsignalSimC.liftC (probeHook fig (qep + 1)) (SM.deliverQuery Q c)).run sC).run (g, fl) =
      ((SM.deliverImpl fig SM.Config.h1 (Q, c)).run g >>= fun x =>
        pure ((x.1, sC), (x.2, fl))) := by
  unfold LibsignalSimC.liftC probeHook fig8ImplH1 SM.oracleImpl SM.deliverQuery
  simp only [StateT_run_lift, simulateQ_HasQuery_query, StateT.run_bind, StateT.run_pure]
  change (((SM.deliverImpl fig SM.Config.h1 (Q, c)).run g >>= fun x => pure (x.1, (x.2, fl))) >>=
    fun p => pure ((p.1, sC), p.2)) = _
  simp only [bind_assoc, pure_bind]

theorem probeHook_liftC_inject_run {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (c : Fig8C Pt) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool) :
    ((LibsignalSimC.liftC (probeHook fig (qep + 1)) (SM.injectQuery Q c)).run sC).run (g, fl) =
      ((SM.injectImpl fig (2 + 1) (qep + 1) SM.Config.h1 (Q, c)).run g >>= fun x =>
        pure ((x.1, sC), (x.2, fl))) := by
  unfold LibsignalSimC.liftC probeHook fig8ImplH1 SM.oracleImpl SM.injectQuery
  simp only [StateT_run_lift, simulateQ_HasQuery_query, StateT.run_bind, StateT.run_pure]
  change (((SM.injectImpl fig (2 + 1) (qep + 1) SM.Config.h1 (Q, c)).run g >>=
    fun x => pure (x.1, (x.2, fl))) >>= fun p => pure ((p.1, sC), p.2)) = _
  simp only [bind_assoc, pure_bind]

theorem runCellStep_congr_run {PQ Pt α : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ)
    (m₁ m₂ : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α)
    (sC₁ sC₂ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : m₁.run sC₁ = m₂.run sC₂) :
    runCellStep fig qep t tL m₁ sC₁ sent m' s_cell =
      runCellStep fig qep t tL m₂ sC₂ sent m' s_cell := by
  unfold runCellStep
  rw [h]

theorem runCellStep_fwdAnswerC {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL
      (LibsignalSimC.fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w isDel ci? T pq' c')
      sC sent m' s_cell =
      (runCellStep fig qep t tL (LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ) (fwd Q c'))
        sC sent m' s_cell >>= fun z =>
          runCellStep fig qep t tL
            (LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ)
              (onAnswer (qep := qep) Q w isDel ci? T pq' z.1.1.1.1))
            (updKeptOnRes fig fs Q c' z.1.1.1.1 z.1.1.1.2) z.1.1.2 z.1.2 z.2) := by
  unfold runCellStep
  rw [fwdAnswerC_run]
  simp only [StateT.run_bind, simulateQ_bind]

theorem firstNESimImpl_inject_run {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl : Bool) (tr : KemFailTrackState P.C.F) :
    (firstNESimImpl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inr (.inl (.inr (Q, w))))).run (sC, (g, fl), tr) =
      (let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
       let fs := lFS P.C P.codec ℓ encT idOf 25000
       (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
           (probeHook fig (qep + 1)) Q w false)).run sC).run (g, fl)) >>=
         fun p => pure (p.1.1, (p.1.2, p.2, tr))) := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  change (runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
      (probeHook fig (qep + 1)) Q w false))).run (sC, (g, fl), tr) = _
  exact runProbeStep_run P ℓ Dh encPt encT decT idOf lam qep _ sC (g, fl) tr

theorem firstNESimImpl_inject_pure_run {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (ans : Option (RecvResult (Plain ℓ)))
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl : Bool) (tr : KemFailTrackState P.C.F)
    (hpure :
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (probeHook fig (qep + 1)) Q w false)).run sC = pure (ans, sC₁)) :
    (firstNESimImpl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inr (.inl (.inr (Q, w))))).run (sC, (g, fl), tr) =
      pure (ans, (sC₁, (g, fl), tr)) := by
  rw [firstNESimImpl_inject_run]
  dsimp only at hpure ⊢
  rw [hpure]
  simp only [StateT.run_pure, pure_bind]

theorem runCellStep_inject_pure {PQ PQC Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (sC sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ans : Option (RecvResult (Plain ℓ)))
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hpure : (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
      (deliverForgeHook Pt ℓ) Q w false)).run sC = pure (ans, sC₁)) :
    runCellStep fig qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (deliverForgeHook Pt ℓ) Q w false))
      sC sent m' s_cell =
      pure ((((ans, sC₁), sent), m'), s_cell) := by
  rw [runCellStep_congr_run fig qep t tL _ (pure ans) sC sC₁ sent m' s_cell hpure,
    runCellStep_pure]

theorem probeHook_fwdAnswerC_run {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool) :
    (((LibsignalSimC.fwdAnswerC qep fig fs (probeHook fig (qep + 1))
        Q w isDel ci? T pq' c').run sC).run (g, fl)) =
      ((((LibsignalSimC.runOnBaseState (probeHook fig (qep + 1)) (fwd Q c')).run sC).run (g, fl)) >>=
        fun x =>
          (((LibsignalSimC.runOnBaseState (probeHook fig (qep + 1))
              (onAnswer (qep := qep) Q w isDel ci? T pq' x.1.1)).run
            (updKeptOnRes fig fs Q c' x.1.1 x.1.2)).run x.2)) := by
  rw [fwdAnswerC_run, StateT.run_bind]

attribute [local instance] Classical.propDecidable

theorem zoomB_probeHook_fwd_deliver_run {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (c : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (hInT : (sC.base.honest.any fun wc =>
      decide (wc.2 = c) && (sC.base.mir.inTransit Q.other wc.1).isSome) = true) :
    (((LibsignalSimC.runOnBaseState (probeHook fig (qep + 1)) (fwd Q c)).run sC).run (g, fl)) =
      ((SM.deliverImpl fig SM.Config.h1 (Q, c)).run g >>= fun x =>
        pure ((x.1, sC), (x.2, fl))) := by
  rw [zoomB_probeHook_fwd_run]
  simp only [hInT, ↓reduceIte, probeHook_liftC_deliver_run]

theorem zoomB_probeHook_fwd_inject_run {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (c : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (hInT : (sC.base.honest.any fun wc =>
      decide (wc.2 = c) && (sC.base.mir.inTransit Q.other wc.1).isSome) = false) :
    (((LibsignalSimC.runOnBaseState (probeHook fig (qep + 1)) (fwd Q c)).run sC).run (g, fl)) =
      ((SM.injectImpl fig (2 + 1) (qep + 1) SM.Config.h1 (Q, c)).run g >>= fun x =>
        pure ((x.1, sC), (x.2, fl))) := by
  rw [zoomB_probeHook_fwd_run]
  simp only [hInT, Bool.false_eq_true, ↓reduceIte, probeHook_liftC_inject_run]

theorem injectImpl_h1_run {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (Q : Party) (c : C)
    (g : SM.GameState St Msg C) (hwin : g.win = false) :
    (SM.injectImpl sm (2 + 1) (qep + 1) SM.Config.h1 (Q, c)).run g =
      if (g.inTransit Q.other c).isSome || !(g.safeInj (2 + 1)) then
        pure (none, g)
      else
        match sm.receive (g.st Q) c with
        | none => pure (some .rejected, g)
        | some (st', t', i', m') =>
          if (qep + 1) + 1 < t' then
            pure (some .rejected, g)
          else
            let pos : SM.Pos := ⟨Q.other, t', i'⟩
            if g.trivial (2 + 1) pos then
              pure (some (.accepted t' i' (some m')), g.accept Q st' pos)
            else
              pure (some .rejected, { g with win := true }) := by
  unfold SM.injectImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_or]
  by_cases h1 : ((g.inTransit Q.other c).isSome || !(g.safeInj (2 + 1))) = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases hrcv : sm.receive (g.st Q) c with
    | none => rfl
    | some v =>
      rcases v with ⟨st', t', i', m'⟩
      dsimp only
      by_cases hq : (qep + 1) + 1 < t'
      · simp [hq]
      · simp only [hq, ↓reduceIte]
        by_cases htriv : g.trivial (2 + 1) ⟨Q.other, t', i'⟩ = true
        · simp [htriv, StateT.run_set]
        · simp [htriv, SM.Config.h1, StateT.run_set]


theorem injectImplCell_run {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (t : ℕ) (Q : Party) (c : C)
    (s : SM.GameState St Msg C) (hwin : s.win = false) :
    (injectImplCell sm (qep + 1) tL t (SM.Config.auth t) (Q, c)).run s =
      if (s.inTransit Q.other c).isSome || !(s.safeInj (cellDelta tL t)) then
        pure (none, s)
      else
        match sm.receive (s.st Q) c with
        | none => pure (some .rejected, s)
        | some (st', t', i', m') =>
          if (qep + 1) + 1 < t' then
            pure (some .rejected, s)
          else
            let pos : SM.Pos := ⟨Q.other, t', i'⟩
            if cellTrivialT tL t s pos then
              pure (some (.accepted t' i' (some m')), s.accept Q st' pos)
            else
              pure (some .rejected, if t' == t then { s with win := true } else s) := by
  unfold injectImplCell
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_or]
  by_cases h1 : ((s.inTransit Q.other c).isSome || !(s.safeInj (cellDelta tL t))) = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases hrcv : sm.receive (s.st Q) c with
    | none => rfl
    | some v =>
      rcases v with ⟨st', t', i', m'⟩
      dsimp only
      by_cases hq : (qep + 1) + 1 < t'
      · simp [hq]
      · simp only [hq, ↓reduceIte]
        by_cases htriv : cellTrivialT tL t s ⟨Q.other, t', i'⟩ = true
        · simp [htriv, StateT.run_set]
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte, SM.Config.auth]
          by_cases ht : (t' == t) = true
          · simp [ht, StateT.run_set]
          · simp [ht]

theorem evalDist_le_sum_cellSimRun_of_cell_step_win {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (lhs : ProbComp Bool)
    (oa_pre oa_post : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) α)
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) (sent sent₁ : List (Fig8C Pt))
    (m' m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (t₀ : ℕ) (ht₀ : t₀ ∈ Finset.range ((qep + 1) + 2))
    (tL₀ : Option ℕ) (htL₀ : tL₀ ∈ SM.admissibleLastLeakGuesses 2 t₀)
    (s_win : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstep_eq :
      cellSimRun P ℓ Dh encPt encT decT idOf lam qep t₀ tL₀ oa_pre sC sent m' (s_cell t₀ tL₀) =
      cellSimRun P ℓ Dh encPt encT decT idOf lam qep t₀ tL₀ oa_post sC₁ sent₁ m₁' s_win)
    (hwin : cellWinPred tL₀ t₀ s_win = true) :
    𝒟[lhs] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa_pre sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  have hone :
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t₀ tL₀ oa_pre sC sent m'
          (s_cell t₀ tL₀) >>=
        fun z => pure (cellWinPred tL₀ t₀ z.2)] {true} = 1 := by
    rw [hstep_eq]
    exact evalDist_simulateQ_fullImplBaseDFCellPaper_cellWinPred_eq_one
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep DeliverForge.sameHdrScheme
      tL₀ t₀ _ s_win hwin
  refine le_trans MeasureTheory.prob_le_one ?_
  rw [← hone]
  exact le_trans
    (Finset.single_le_sum (f := fun tL =>
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t₀ tL oa_pre sC sent m'
          (s_cell t₀ tL) >>=
        fun z => pure (cellWinPred tL t₀ z.2)] {true})
      (fun _ _ => (zero_le : (0 : ℝ≥0∞) ≤ _)) htL₀)
    (Finset.single_le_sum (f := fun t => ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa_pre sC sent m'
          (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true})
      (fun _ _ => (zero_le : (0 : ℝ≥0∞) ≤ _)) ht₀)

def updMirOnRes {Msg C : Type}
    (Q : Party) (res : Option (RecvResult Msg)) (m' : Mirror Msg C) : Mirror Msg C :=
  match res with
  | some (.accepted t' i' _) => m'.accept Q () ⟨Q.other, t', i'⟩
  | _ => m'

theorem sum_cellSimRun_le_of_post_doomed_or_eq {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa_pre oa_post : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) α)
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) (sent sent₁ : List (Fig8C Pt))
    (m' m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (g' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell s_cell' : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hcell : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      CellK4Doomed tL t g' (s_cell' t tL) ∨
      cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa_pre sC sent m' (s_cell t tL) =
      cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa_post sC₁ sent₁ m₁' (s_cell' t tL)) :
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa_post sC₁ sent₁ m₁' (s_cell' t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa_pre sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun tL htL => ?_
  rcases hcell t ht tL htL with hdoomed' | heq
  · rw [evalDist_cellSimRun_cellWinPred_eq_zero_of_doomed P ℓ Dh encPt encT decT idOf lam qep
      t tL oa_post sC₁ sent₁ m₁' hdoomed']
    exact zero_le
  · rw [heq]

theorem runCellStep_fwdAnswerC_inject {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hInT : (sC₀.base.honest.any fun wc =>
      decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = false) :
    runCellStep fig qep t tL
      (LibsignalSimC.fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w isDel ci? T pq' c')
      sC₀ sent m' s_cell =
      ((injectImplCell fig (qep + 1) tL t (SM.Config.auth t) (Q, c')).run s_cell >>= fun z =>
        runCellStep fig qep t tL
          (LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ)
            (onAnswer (qep := qep) Q w isDel ci? T pq' z.1))
          (updKeptOnRes fig fs Q c' z.1 sC₀) sent (updMirOnRes Q z.1 m') z.2) := by
  rw [runCellStep_fwdAnswerC, runCellStep_zoomB_fwd]
  simp only [hInT, Bool.false_eq_true, ↓reduceIte, runCellStep_liftC_inject, bind_assoc, pure_bind]
  congr 1; funext z
  rcases z with ⟨_ | ⟨_ | ⟨t', i', m⟩⟩, s_z⟩ <;> rfl

theorem probeHook_fwdAnswerC_inject_run {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (hInT : (sC₀.base.honest.any fun wc =>
      decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = false) :
    (((LibsignalSimC.fwdAnswerC qep fig fs (probeHook fig (qep + 1))
        Q w isDel ci? T pq' c').run sC₀).run (g, fl)) =
      ((SM.injectImpl fig (2 + 1) (qep + 1) SM.Config.h1 (Q, c')).run g >>= fun x =>
        (((LibsignalSimC.runOnBaseState (probeHook fig (qep + 1))
            (onAnswer (qep := qep) Q w isDel ci? T pq' x.1)).run
          (updKeptOnRes fig fs Q c' x.1 sC₀)).run (x.2, fl))) := by
  rw [probeHook_fwdAnswerC_run, zoomB_probeHook_fwd_inject_run fig qep Q c' sC₀ g fl hInT]
  simp only [bind_assoc, pure_bind]

theorem runCellStep_fwdAnswerC_inject_of_eq {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell s_cell' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ)
    (hInT : (sC₀.base.honest.any fun wc =>
      decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = false)
    (hinj : (injectImplCell fig (qep + 1) tL t (SM.Config.auth t) (Q, c')).run s_cell =
      pure (res, s_cell'))
    (hrun : (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w isDel ci? T pq' res).run (updKeptOnRes fig fs Q c' res sC₀).base = pure (ans, b')) :
    runCellStep fig qep t tL
      (LibsignalSimC.fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w isDel ci? T pq' c')
      sC₀ sent m' s_cell =
      pure ((((ans, { updKeptOnRes fig fs Q c' res sC₀ with base := b' }), sent),
        updMirOnRes Q res m'), s_cell') := by
  rw [runCellStep_fwdAnswerC_inject fig fs qep t tL Q w isDel ci? T pq' c' sC₀ sent m' s_cell hInT,
    hinj, pure_bind]
  exact runCellStep_zoomB_onAnswer fig qep t tL Q w isDel ci? T pq' res
    (updKeptOnRes fig fs Q c' res sC₀) sent (updMirOnRes Q res m') s_cell' ans b' hrun

theorem probeHook_fwdAnswerC_inject_run_of_eq {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g g' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ)
    (hInT : (sC₀.base.honest.any fun wc =>
      decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = false)
    (hinj : (SM.injectImpl fig (2 + 1) (qep + 1) SM.Config.h1 (Q, c')).run g =
      pure (res, g'))
    (hrun : (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w isDel ci? T pq' res).run (updKeptOnRes fig fs Q c' res sC₀).base = pure (ans, b')) :
    (((LibsignalSimC.fwdAnswerC qep fig fs (probeHook fig (qep + 1))
        Q w isDel ci? T pq' c').run sC₀).run (g, fl)) =
      pure ((ans, { updKeptOnRes fig fs Q c' res sC₀ with base := b' }), (g', fl)) := by
  rw [probeHook_fwdAnswerC_inject_run fig fs qep Q w isDel ci? T pq' c' sC₀ g fl hInT,
    hinj, pure_bind]
  exact zoomB_probeHook_onAnswer_run fig qep Q w isDel ci? T pq' res
    (updKeptOnRes fig fs Q c' res sC₀) g' fl ans b' hrun

theorem inject_step_branch_cases {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ)
    (Q : Party) (c : C) (st' : St) (t' i' : ℕ) (m_out : Msg)
    {m' m₁' : Mirror Msg C} {g : SM.GameState St Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hcol : ∀ t₁ ∈ Finset.range ((qep + 1) + 2), ∀ t₂ ∈ Finset.range ((qep + 1) + 2),
      s_cell t₁ none = s_cell t₂ none)
    (hrel_all : ∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL)))
    (ht'_le : t' ≤ (qep + 1) + 1)
    (hnone_g : (g.inTransit Q.other c).isSome = false)
    (hsafe_g : g.safeInj (2 + 1) = true)
    (hrcv_g : sm.receive (g.st Q) c = some (st', t', i', m_out)) :
    let pos : SM.Pos := ⟨Q.other, t', i'⟩
    let g' := if g.trivial (2 + 1) pos then g.accept Q st' pos else { g with win := true }
    let s_cell' : ℕ → Option ℕ → SM.GameState St Msg C := fun t tL =>
      if (s_cell t tL).win then s_cell t tL
      else if cellTrivialT tL t (s_cell t tL) pos then
        (s_cell t tL).accept Q st' pos
      else if t' == t then { s_cell t tL with win := true }
      else s_cell t tL
    (∃ t₀ ∈ Finset.range ((qep + 1) + 2), ∃ tL₀ ∈ SM.admissibleLastLeakGuesses 2 t₀,
      PPrimePaperRelShifted (s_cell t₀ tL₀) m' g ∧
      cellTrivialT tL₀ t₀ (s_cell t₀ tL₀) pos = false ∧
      (t' == t₀) = true ∧
      cellWinPred tL₀ t₀ { s_cell t₀ tL₀ with win := true } = true) ∨
    (g.trivial (2 + 1) pos = true ∧ g' = g.accept Q st' pos ∧
      FirstNECellFamilyInvT qep false g' m₁' s_cell' ∧
      ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g' (s_cell' t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          cellTrivialT tL t (s_cell t tL) pos = true ∧
          s_cell' t tL = (s_cell t tL).accept Q st' pos)) := by
  intro pos g' s_cell'
  have hinv' : FirstNECellFamilyInvT qep false g' m₁' s_cell' :=
    firstNECellFamilyInvT_inject_step sm qep Q c st' t' i' m_out
      (Or.inr ⟨rfl, hcol, hrel_all⟩) ht'_le hnone_g hsafe_g hrcv_g
  rcases hinv' with ⟨t₀, ht₀, tL₀, htL₀, hwin₀⟩ | ⟨_, hcol', hrel_all'⟩
  · left
    rcases (hrel_all t₀ ht₀).2.2 tL₀ htL₀ with hdoomed | ⟨hrel_sh, _, _, _⟩
    · have hw : s_cell' t₀ tL₀ = s_cell t₀ tL₀ := by
        dsimp only [s_cell']; simp only [hdoomed.2.2.2, ↓reduceIte]
      rw [hw, hdoomed.cellWinPred_eq_false] at hwin₀; nomatch hwin₀
    · have hw_post : (s_cell' t₀ tL₀).win = true := s_win_of_cellWinPred hwin₀
      have htriv_f : cellTrivialT tL₀ t₀ (s_cell t₀ tL₀) pos = false := by
        by_contra htriv_t
        simp only [Bool.not_eq_false] at htriv_t
        dsimp only [s_cell'] at hw_post
        simp only [hrel_sh.win_df_false, Bool.false_eq_true, htriv_t, ↓reduceIte] at hw_post
        exact Bool.false_ne_true (hrel_sh.win_df_false.symm.trans hw_post)
      have ht_eq : (t' == t₀) = true := by
        by_contra ht_ne
        simp only [Bool.not_eq_true] at ht_ne
        dsimp only [s_cell'] at hw_post
        simp only [hrel_sh.win_df_false, htriv_f, ht_ne, Bool.false_eq_true, ↓reduceIte] at hw_post
      have hs_eq : s_cell' t₀ tL₀ = { s_cell t₀ tL₀ with win := true } := by
        dsimp only [s_cell']
        simp only [hrel_sh.win_df_false, htriv_f, ht_eq, Bool.false_eq_true, ↓reduceIte]
      rw [hs_eq] at hwin₀
      exact ⟨t₀, ht₀, tL₀, htL₀, hrel_sh, htriv_f, ht_eq, hwin₀⟩
  · right
    have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
    have hwin_g' : g'.win = false := (hrel_all' 0 ht0).1.win_mir_false
    have htriv_g : g.trivial (2 + 1) pos = true := by
      by_contra htg
      simp only [Bool.not_eq_true] at htg
      dsimp only [g'] at hwin_g'
      simp only [htg, Bool.false_eq_true, ↓reduceIte] at hwin_g'
      nomatch hwin_g'
    have hg'_eq : g' = g.accept Q st' pos := by
      dsimp only [g']; simp only [htriv_g, ↓reduceIte]
    have ht'_mem : t' ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
    have htriv_u : (s_cell t' none).trivial (2 + 1) pos = true := by
      by_contra htu
      simp only [Bool.not_eq_true] at htu
      have hw_u' : (s_cell' t' none).win = false := (hrel_all' t' ht'_mem).1.win_df_false
      have hw_u : (s_cell t' none).win = false := (hrel_all t' ht'_mem).1.win_df_false
      dsimp only [s_cell'] at hw_u'
      simp only [hw_u, cellTrivialT_none, htu, Bool.false_eq_true, ↓reduceIte,
        beq_self_eq_true] at hw_u'
      nomatch hw_u'
    refine ⟨htriv_g, hg'_eq, Or.inr ⟨rfl, hcol', hrel_all'⟩, fun t ht tL htL => ?_⟩
    rcases (hrel_all' t ht).2.2 tL htL with hdoomed' | ⟨hrel_sh', _, _, _⟩
    · exact Or.inl hdoomed'
    · right
      have hw_sh' : (s_cell' t tL).win = false := hrel_sh'.win_df_false
      rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, hleak_sh, hcomp_sh⟩
      · dsimp only [s_cell'] at hw_sh'
        simp only [hdoomed.2.2.2, ↓reduceIte] at hw_sh'
        nomatch hw_sh'
      · have htriv_sh : cellTrivialT tL t (s_cell t tL) pos = true := by
          by_cases hteq : t' = t
          · subst hteq
            by_contra hts
            simp only [Bool.not_eq_true] at hts
            dsimp only [s_cell'] at hw_sh'
            simp only [hrel_sh.win_df_false, hts, Bool.false_eq_true, ↓reduceIte,
              beq_self_eq_true] at hw_sh'
            nomatch hw_sh'
          · have htriv_ut : (s_cell t none).trivial (2 + 1) pos = true :=
              (hcol t ht t' ht'_mem) ▸ htriv_u
            exact cellTrivialT_true_of_unsh_trivial_true_of_ne (hrel_all t ht).2.1
              ((hrel_all t ht).1.safeInj_df_of_safeInj_mir le_rfl hsafe_g)
              hleak_sh hcomp_sh htriv_ut hteq
        have hs_eq : s_cell' t tL = (s_cell t tL).accept Q st' pos := by
          dsimp only [s_cell']
          simp only [hrel_sh.win_df_false, htriv_sh, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hrel_sh, htriv_sh, hs_eq⟩

theorem firstNESimImpl_inject_fwd_of_eq {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8)) (c' : Fig8C Pt)
    (sC sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g g' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl : Bool) (tr : KemFailTrackState P.C.F)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (ans : Option (RecvResult (Plain ℓ))) (b' : SimState (List (BitVec 8)) Pt ℓ)
    (hfwd :
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (probeHook fig (qep + 1)) Q w false)).run sC =
        (LibsignalSimC.fwdAnswerC qep fig fs (probeHook fig (qep + 1))
          Q w false ci? T pq' c').run sC₀)
    (hInT : (sC₀.base.honest.any fun wc =>
      decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = false)
    (hinj : (SM.injectImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (2 + 1) (qep + 1) SM.Config.h1 (Q, c')).run g = pure (res, g'))
    (hrun :
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      (onAnswer (qep := qep) Q w false ci? T pq' res).run
        (updKeptOnRes fig fs Q c' res sC₀).base = pure (ans, b')) :
    (firstNESimImpl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inr (.inl (.inr (Q, w))))).run (sC, (g, fl), tr) =
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      pure (ans, ({ updKeptOnRes fig fs Q c' res sC₀ with base := b' }, (g', fl), tr)) := by
  rw [firstNESimImpl_inject_run]
  dsimp only at hfwd hrun ⊢
  rw [hfwd, probeHook_fwdAnswerC_inject_run_of_eq _ _ qep Q w false ci? T pq' c' sC₀ g g' fl
    res ans b' hInT hinj hrun, pure_bind]

theorem runCellStep_inject_fwd_of_eq {PQ PQC Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] [SampleableType Pt]
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell s_cell' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ)
    (hfwd : (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
      (deliverForgeHook Pt ℓ) Q w false)).run sC =
      (LibsignalSimC.fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w false ci? T pq' c').run sC₀)
    (hInT : (sC₀.base.honest.any fun wc =>
      decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = false)
    (hinj : (injectImplCell fig (qep + 1) tL t (SM.Config.auth t) (Q, c')).run s_cell =
      pure (res, s_cell'))
    (hrun : (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w false ci? T pq' res).run (updKeptOnRes fig fs Q c' res sC₀).base = pure (ans, b')) :
    runCellStep fig qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (deliverForgeHook Pt ℓ) Q w false))
      sC sent m' s_cell =
      pure ((((ans, { updKeptOnRes fig fs Q c' res sC₀ with base := b' }), sent),
        updMirOnRes Q res m'), s_cell') := by
  rw [runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' s_cell hfwd]
  exact runCellStep_fwdAnswerC_inject_of_eq fig fs qep t tL Q w false ci? T pq' c' sC₀ sent m'
    s_cell s_cell' res ans b' hInT hinj hrun

theorem inject_sync_of_baseSync {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt]
    (Q : Party) (w : List (BitVec 8)) (c' : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hhon : ∀ wc ∈ sC.base.honest, wc.1 = LibsignalSim.toWire wc.2)
    (htrans : ∀ r ∈ g.trans,
      ∃ r_m ∈ sC.base.mir.trans, r_m.pos = r.pos ∧ r_m.ct = LibsignalSim.toWire r.ct)
    (hep_mir : sC.base.mir.epoch = g.epoch)
    (htL_mir : sC.base.mir.tL = g.tL)
    (hcw : LibsignalSim.toWire c' = w ∨ (w, c') ∈ sC.base.honest)
    (_hstop : sC.base.stopped = false)
    (hinT : (sC.base.mir.inTransit Q.other w).isSome = false)
    (hsafe : sC.base.mir.safeInj 3 = true) :
    (sC.base.honest.any fun wc =>
      decide (wc.2 = c') && (sC.base.mir.inTransit Q.other wc.1).isSome) = false ∧
    (g.inTransit Q.other c').isSome = false ∧
    g.safeInj (2 + 1) = true := by
  have hw : LibsignalSim.toWire c' = w := by
    rcases hcw with h | hmem
    · exact h
    · exact (hhon (w, c') hmem).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [List.any_eq_false]
    intro wc hwc
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro heq
    have hwc1 : wc.1 = w := by rw [hhon wc hwc, heq, hw]
    rw [hwc1, hinT]
    exact Bool.false_ne_true
  · rw [Bool.eq_false_iff]
    intro hsome
    rcases Option.isSome_iff_exists.mp hsome with ⟨r, hr⟩
    unfold SM.GameState.inTransit at hr
    have hmem := List.mem_of_find?_eq_some hr
    have hpred := List.find?_some hr
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
    obtain ⟨r_m, hrm_mem, hpos, hct⟩ := htrans r hmem
    cases hnone : sC.base.mir.inTransit Q.other w with
    | some _ => rw [hnone] at hinT; cases hinT
    | none =>
      have hnot := List.find?_eq_none.mp hnone r_m hrm_mem
      simp [hpos, hpred.1, hct, hpred.2, hw] at hnot
  · unfold SM.GameState.safeInj at hsafe ⊢
    simpa [hep_mir, htL_mir] using hsafe

end CryptoVerification.LibsignalSession.HeadlineV1


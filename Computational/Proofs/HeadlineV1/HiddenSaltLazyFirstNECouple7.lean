/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple6
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNESplit
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple5
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit3
import ProofLib.SepLogic.WP.StateNorm

/-!
# Simulator Synchronization Invariant and `deliver` Lockstep

Defines `HonestSentSync`, `SyncInv`, and the three-branch coupled invariant `FirstNECoupledInvD`,
and proves lockstep lemmas relating `deliver` steps in the simulator to every live cell.
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

section
variable (Pt : Type) [Zero Pt] [DecidableEq Pt] [SampleableType Pt]

/-- Invariant asserting that `honest` is the wire-tagged image of the `deliverForgeHook` `sent` list. -/
def HonestSentSync (honest : List (List (BitVec 8) × Fig8C Pt))
    (sent : List (Fig8C Pt)) : Prop :=
  honest = sent.map (fun c => (LibsignalSim.toWire c, c))

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem honestSentSync_nil :
    HonestSentSync Pt [] [] := rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem honestSentSync_cons
    {honest : List (List (BitVec 8) × Fig8C Pt)} {sent : List (Fig8C Pt)}
    (hsync : HonestSentSync Pt honest sent) (c : Fig8C Pt) :
    HonestSentSync Pt ((LibsignalSim.toWire c, c) :: honest) (c :: sent) := by
  unfold HonestSentSync at hsync ⊢
  rw [List.map_cons, hsync]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem mem_honest_of_honestSentSync
    {honest : List (List (BitVec 8) × Fig8C Pt)} {sent : List (Fig8C Pt)}
    (hsync : HonestSentSync Pt honest sent)
    {wc : List (BitVec 8) × Fig8C Pt} (hmem : wc ∈ honest) :
    wc.1 = LibsignalSim.toWire wc.2 ∧ wc.2 ∈ sent := by
  rw [hsync, List.mem_map] at hmem
  rcases hmem with ⟨c, hc_mem, rfl⟩
  exact ⟨rfl, hc_mem⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem find?_eq_some_of_imp {α : Type} {l : List α} {p₁ p₂ : α → Bool} {c : α}
    (hfind₁ : l.find? p₁ = some c)
    (hc₂ : p₂ c = true)
    (himp : ∀ x ∈ l, p₂ x = true → p₁ x = true) :
    l.find? p₂ = some c := by
  induction l with
  | nil => simp at hfind₁
  | cons a xs ih =>
    simp only [List.find?_cons] at hfind₁ ⊢
    revert hfind₁
    cases hp₁ : p₁ a
    · intro hfind₁
      have hp₂ : p₂ a = false := by
        cases h : p₂ a
        · rfl
        · have := himp a List.mem_cons_self h
          rw [this] at hp₁
          cases hp₁
      rw [hp₂]
      exact ih hfind₁ (fun x hx => himp x (List.mem_cons_of_mem a hx))
    · intro hfind₁
      injection hfind₁ with ha
      subst ha
      rw [hc₂]

omit [Zero Pt] [SampleableType Pt] in
theorem toWire_eq_of_sameWireFig8 {c₁ c₂ : Fig8C Pt}
    (hsame : sameWireFig8 c₁ c₂ = true) :
    LibsignalSim.toWire c₁ = LibsignalSim.toWire c₂ ∧ c₁.1 = c₂.1 ∧ c₁.2.1 = c₂.2.1 := by
  unfold sameWireFig8 at hsame
  rw [decide_eq_true_iff] at hsame
  rcases hsame with ⟨h1, h2, h3⟩
  refine ⟨?_, h1, h2⟩
  unfold LibsignalSim.toWire
  rw [h3]

omit [Zero Pt] [SampleableType Pt] in
theorem find?_sameWire_eq_honestC_of_sync
    {honest : List (List (BitVec 8) × Fig8C Pt)} {sent : List (Fig8C Pt)}
    (hsync : HonestSentSync Pt honest sent)
    {w w_c : List (BitVec 8)} {Q : Party} {c c' : Fig8C Pt}
    (hhonC : honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) =
      some (w_c, c))
    (hsame : sameWireFig8 c c' = true) :
    sent.find? (fun x => sameWireFig8 x c') = some c := by
  rw [hsync, List.find?_map] at hhonC
  simp only [Option.map_eq_some_iff] at hhonC
  rcases hhonC with ⟨c₀, hfind₀, hpair⟩
  injection hpair with hw_c hc₀
  subst hc₀
  have hp₁_c := List.find?_some hfind₀
  dsimp only [Function.comp_def] at hp₁_c
  obtain ⟨hw_eq, h1_eq, _⟩ := toWire_eq_of_sameWireFig8 Pt hsame
  refine find?_eq_some_of_imp hfind₀ hsame ?_
  intro x _ hx
  obtain ⟨hx_w, hx_1, _⟩ := toWire_eq_of_sameWireFig8 Pt hx
  have hwx : LibsignalSim.toWire x = LibsignalSim.toWire c₀ := hx_w.trans hw_eq.symm
  have h1x : x.1 = c₀.1 := hx_1.trans h1_eq.symm
  simpa [Function.comp_def, hwx, h1x] using hp₁_c

theorem deliverForgeBaseImplCell_run_win_of_nontrivial {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (tL : Option ℕ) (qep : ℕ) (sameHdr : C → C → Bool)
    {s_df : SM.GameState St Msg C} {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g)
    (Q : Party) (c c' : C) (r : SM.Record Msg C) (st' : St) (t' i' : ℕ) (m_out : Msg)
    (ht'_le : t' ≤ (qep + 1) + 1)
    (hin_g : g.inTransit Q.other c = some r)
    (hnone_g : (g.inTransit Q.other c').isSome = false)
    (hcomp_df : s_df.comp.contains r.pos = false)
    (hhdr : sameHdr c c' = true)
    (hrcv_g : sm.receive (g.st Q) c' = some (st', t', i', m_out))
    (hr_pos : r.pos = ⟨Q.other, t', i'⟩)
    (htriv : s_df.trivial (cellDelta tL t') ⟨Q.other, t', i'⟩ = false) :
    (deliverForgeBaseImplCell sm (qep + 1) tL t' sameHdr (SM.Config.auth t')
      (Q, c, c')).run s_df = pure (some .rejected, { s_df with win := true }) := by
  have hin_df : s_df.inTransit Q.other c = some r := by
    rw [hrel.inTransit_eq]; exact hin_g
  have hbad_df : ((s_df.inTransit Q.other c').isSome || s_df.comp.contains r.pos ||
      !sameHdr c c') = false := by
    rw [hrel.inTransit_eq Q.other c', hnone_g, hcomp_df, hhdr]; rfl
  have hrcv_df : sm.receive (s_df.st Q) c' = some (st', t', i', m_out) := by
    rw [hrel.st_eq]; exact hrcv_g
  have ht'_eq : t' = r.pos.epoch := by rw [hr_pos]
  have ht'_cond : (decide ((qep + 1) + 1 < t') || t' != r.pos.epoch) = false := by
    have h1 : decide ((qep + 1) + 1 < t') = false := decide_eq_false (by omega)
    have h2 : (t' != r.pos.epoch) = false := by simp [ht'_eq]
    rw [h1, h2]; rfl
  have htrivT : cellTrivialT tL t' s_df ⟨Q.other, t', i'⟩ = false := by
    rw [cellTrivialT_at_target tL t' s_df ⟨Q.other, t', i'⟩ rfl]
    exact htriv
  unfold deliverForgeBaseImplCell
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hrel.win_df_false,
    Bool.false_eq_true, ↓reduceIte, hin_df, hbad_df, hrcv_df, ht'_cond, htrivT,
    SM.Config.auth, beq_self_eq_true, StateT.run_set, StateT.run_pure]

theorem cellSimRun_deliverForgeHook_probe_win {PQ : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep t' : ℕ) (tL : Option ℕ)
    (Q : Party) (c c' : Fig8C Pt)
    (r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (st' : Fig8St Pt) (i' : ℕ) (m_out : LibsignalMsgPublicPart × Plain ℓ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {s_cell g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hrel : PPrimePaperRelShifted s_cell m' g)
    (hfind : sent.find? (fun c₀ => sameWireFig8 c₀ c') = some c)
    (ht'_le : t' ≤ (qep + 1) + 1)
    (hin_g : g.inTransit Q.other c = some r)
    (hnone_g : (g.inTransit Q.other c').isSome = false)
    (hcomp_df : s_cell.comp.contains r.pos = false)
    (hhdr : DeliverForge.sameHdrScheme c c' = true)
    (hrcv_g : fig.receive (g.st Q) c' = some (st', t', i', m_out))
    (hr_pos : r.pos = ⟨Q.other, t', i'⟩)
    (htriv : s_cell.trivial (cellDelta tL t') ⟨Q.other, t', i'⟩ = false) :
    runCellStep fig qep t' tL
      (StateT.lift ((deliverForgeHook Pt ℓ).probe Q c')) sC sent m' s_cell =
      pure (((((), sC), sent), m'), { s_cell with win := true }) := by
  unfold runCellStep
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
    simulateQ_cell_deliverForgeHook_probe_run, hfind,
    deliverForgeBaseImplCell_run_win_of_nontrivial fig tL qep
      DeliverForge.sameHdrScheme hrel Q c c' r st' t' i' m_out ht'_le hin_g hnone_g hcomp_df hhdr
      hrcv_g hr_pos htriv,
    pure_bind]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem MirrorSync.inTransit_eq {St Msg C : Type} [DecidableEq C]
    {m' : Mirror Msg C} {g s_unsh : SM.GameState St Msg C}
    (hsync : MirrorSync m' g s_unsh) (P : Party) (c : C) :
    m'.inTransit P c = g.inTransit P c := by
  simp [SM.GameState.inTransit, hsync.trans_eq]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem MirrorSync.deliver_step {St Msg C : Type} [DecidableEq C]
    (Q : Party) (st' : St) (pos : SM.Pos)
    {m' : Mirror Msg C} {g s_unsh : SM.GameState St Msg C}
    (hsync : MirrorSync m' g s_unsh) :
    MirrorSync (m'.accept Q () pos) (g.accept Q st' pos) (s_unsh.accept Q st' pos) :=
  hsync.inject_step Q st' pos

theorem runCellStep_fwdAnswerC_deliver {PQ : Type} {ℓ : ℕ} [Inhabited PQ]
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
      decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = true) :
    runCellStep fig qep t tL
      (LibsignalSimC.fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w isDel ci? T pq' c')
      sC₀ sent m' s_cell =
      ((SM.deliverImpl fig (SM.Config.auth t) (Q, c')).run s_cell >>= fun z =>
        match z.1, m'.inTransit Q.other c' with
        | some (.accepted t' i' m), some r =>
          let res_m := some (.accepted t' i' (if r.pos ∈ m'.chall then none else m))
          runCellStep fig qep t tL
            (LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ)
              (onAnswer (qep := qep) Q w isDel ci? T pq' res_m))
            (updKeptOnRes fig fs Q c' res_m sC₀) sent (m'.accept Q () r.pos) z.2
        | res, _ =>
          runCellStep fig qep t tL
            (LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ)
              (onAnswer (qep := qep) Q w isDel ci? T pq' res))
            (updKeptOnRes fig fs Q c' res sC₀) sent m' z.2) := by
  rw [runCellStep_fwdAnswerC, runCellStep_zoomB_fwd]
  simp only [hInT, ↓reduceIte, runCellStep_liftC_deliver, bind_assoc]
  congr 1; funext z
  rcases z with ⟨_ | ⟨_ | ⟨t', i', m⟩⟩, s_z⟩
  · rfl
  · rfl
  · cases m'.inTransit Q.other c' <;> simp

theorem probeHook_fwdAnswerC_deliver_run {PQ : Type} {ℓ : ℕ} [Inhabited PQ]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (hInT : (sC₀.base.honest.any fun wc =>
      decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = true) :
    (((LibsignalSimC.fwdAnswerC qep fig fs (probeHook fig (qep + 1)) Q w isDel ci? T pq' c').run
        sC₀).run (g, fl)) =
      ((SM.deliverImpl fig SM.Config.h1 (Q, c')).run g >>= fun z =>
        (((LibsignalSimC.runOnBaseState (probeHook fig (qep + 1))
            (onAnswer (qep := qep) Q w isDel ci? T pq' z.1)).run
          (updKeptOnRes fig fs Q c' z.1 sC₀)).run (z.2, fl))) := by
  rw [probeHook_fwdAnswerC_run, zoomB_probeHook_fwd_deliver_run _ _ _ _ _ _ _ hInT]
  simp only [bind_assoc, pure_bind]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem deliverImpl_h1_run {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (Q : Party) (c : C)
    (g : SM.GameState St Msg C) (hwin : g.win = false) :
    (SM.deliverImpl sm SM.Config.h1 (Q, c)).run g =
      match g.inTransit Q.other c with
      | none => pure (none, g)
      | some r =>
        match sm.receive (g.st Q) c with
        | none => pure (some .rejected, g)
        | some (st', t', i', m') =>
          pure (some (.accepted t' i' (if r.pos ∈ g.chall then none else some m')),
            g.accept Q st' r.pos) := by
  unfold SM.deliverImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_eq_true, ↓reduceIte]
  cases htr : g.inTransit Q.other c with
  | none => rfl
  | some r =>
    dsimp only
    cases hrcv : sm.receive (g.st Q) c with
    | none => rfl
    | some v =>
      rcases v with ⟨st', t', i', m'⟩
      simp [SM.Config.h1, StateT.run_set]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem deliverImpl_auth_run {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (t : ℕ) (Q : Party) (c : C)
    (s : SM.GameState St Msg C) (hwin : s.win = false) (hchall : s.chall = []) :
    (SM.deliverImpl sm (SM.Config.auth t) (Q, c)).run s =
      match s.inTransit Q.other c with
      | none => pure (none, s)
      | some r =>
        match sm.receive (s.st Q) c with
        | none => pure (some .rejected, s)
        | some (st', t', i', m') =>
          pure (some (.accepted t' i' (some m')), s.accept Q st' r.pos) := by
  unfold SM.deliverImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_eq_true, ↓reduceIte]
  cases htr : s.inTransit Q.other c with
  | none => rfl
  | some r =>
    dsimp only
    cases hrcv : sm.receive (s.st Q) c with
    | none => rfl
    | some v =>
      rcases v with ⟨st', t', i', m'⟩
      simp [SM.Config.auth, hchall, StateT.run_set]

theorem fwdAnswerC_deliver_lockstep {PQ : Type} {ℓ : ℕ} [Inhabited PQ]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell g s_unsh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)} (fl : Bool)
    (hrel : PPrimePaperRelShifted s_cell m' g)
    (hsync : MirrorSync m' g s_unsh)
    (hInT : (sC₀.base.honest.any fun wc =>
      decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = true) :
    let res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) :=
      match g.inTransit Q.other c' with
      | none => none
      | some r =>
        match fig.receive (g.st Q) c' with
        | none => some .rejected
        | some (_, t', i', m) =>
          some (.accepted t' i' (if r.pos ∈ g.chall then none else some m))
    let g' :=
      match g.inTransit Q.other c', fig.receive (g.st Q) c' with
      | some r, some (st', _, _, _) => g.accept Q st' r.pos
      | _, _ => g
    let m₁' :=
      match g.inTransit Q.other c', fig.receive (g.st Q) c' with
      | some r, some _ => m'.accept Q () r.pos
      | _, _ => m'
    let s_cell' :=
      match g.inTransit Q.other c', fig.receive (g.st Q) c' with
      | some r, some (st', _, _, _) => s_cell.accept Q st' r.pos
      | _, _ => s_cell
    ∀ (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ),
      (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
        Q w isDel ci? T pq' res).run sC₀.base = pure (ans, b') →
      (((LibsignalSimC.fwdAnswerC qep fig fs (probeHook fig (qep + 1))
          Q w isDel ci? T pq' c').run sC₀).run (g, fl)) =
        pure ((ans, { updKeptOnRes fig fs Q c' res sC₀ with base := b' }), (g', fl)) ∧
      runCellStep fig qep t tL
        (LibsignalSimC.fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w isDel ci? T pq' c')
        sC₀ sent m' s_cell =
        pure ((((ans, { updKeptOnRes fig fs Q c' res sC₀ with base := b' }), sent), m₁'),
          s_cell') := by
  intro res g' m₁' s_cell' ans b' hrun
  have hrun' : (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w isDel ci? T pq' res).run (updKeptOnRes fig fs Q c' res sC₀).base = pure (ans, b') := by
    rw [updKeptOnRes_base]; exact hrun
  rw [probeHook_fwdAnswerC_deliver_run Pt fig fs qep Q w isDel ci? T pq' c' sC₀ g fl hInT,
    runCellStep_fwdAnswerC_deliver Pt fig fs qep t tL Q w isDel ci? T pq' c' sC₀ sent m' s_cell
      hInT,
    deliverImpl_h1_run fig Q c' g hrel.win_mir_false,
    deliverImpl_auth_run fig t Q c' s_cell hrel.win_df_false hrel.chall_df_nil,
    hrel.inTransit_eq Q.other c', hrel.st_eq, hsync.inTransit_eq Q.other c', hsync.chall_eq]
  cases htr : g.inTransit Q.other c' with
  | none =>
    simp only [res, g', m₁', s_cell', htr, pure_bind] at hrun' ⊢
    exact ⟨zoomB_probeHook_onAnswer_run fig qep Q w isDel ci? T pq' _ _ _ _ ans b' hrun',
      runCellStep_zoomB_onAnswer fig qep t tL Q w isDel ci? T pq' _ _ _ _ _ ans b' hrun'⟩
  | some r =>
    cases hrcv : fig.receive (g.st Q) c' with
    | none =>
      simp only [res, g', m₁', s_cell', htr, hrcv, pure_bind] at hrun' ⊢
      exact ⟨zoomB_probeHook_onAnswer_run fig qep Q w isDel ci? T pq' _ _ _ _ ans b' hrun',
        runCellStep_zoomB_onAnswer fig qep t tL Q w isDel ci? T pq' _ _ _ _ _ ans b' hrun'⟩
    | some v =>
      rcases v with ⟨st', t', i', m⟩
      simp only [res, g', m₁', s_cell', htr, hrcv, pure_bind] at hrun' ⊢
      exact ⟨zoomB_probeHook_onAnswer_run fig qep Q w isDel ci? T pq' _ _ _ _ ans b' hrun',
        runCellStep_zoomB_onAnswer fig qep t tL Q w isDel ci? T pq' _ _ _ _ _ ans b' hrun'⟩

theorem deliverForgeBaseImplCell_run_of_receive_none {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (tL : Option ℕ) (qep t : ℕ) (sameHdr : C → C → Bool)
    (Q : Party) (c c' : C) (s_df : SM.GameState St Msg C)
    (hrcv : sm.receive (s_df.st Q) c' = none) :
    ∃ res, (res = none ∨ res = some .rejected) ∧
      (deliverForgeBaseImplCell sm (qep + 1) tL t sameHdr (SM.Config.auth t)
        (Q, c, c')).run s_df = pure (res, s_df) := by
  unfold deliverForgeBaseImplCell
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hwin
  · exact ⟨none, Or.inl rfl, rfl⟩
  · cases hin : s_df.inTransit Q.other c with
    | none => exact ⟨none, Or.inl rfl, rfl⟩
    | some r =>
      simp only []
      split_ifs with hbad
      · exact ⟨none, Or.inl rfl, rfl⟩
      · exact ⟨some .rejected, Or.inr rfl, by simp [hrcv]⟩

theorem cellSimRun_deliverForgeHook_probe_of_receive_none {PQ : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (c' : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {s_cell g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hrel : PPrimePaperRelShifted s_cell m' g)
    (hrcv_g : fig.receive (g.st Q) c' = none) :
    runCellStep fig qep t tL
      (StateT.lift ((deliverForgeHook Pt ℓ).probe Q c') :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) Unit)
      sC sent m' s_cell =
      pure (((((), sC), sent), m'), s_cell) := by
  have hrcv_df : fig.receive (s_cell.st Q) c' = none := by
    rw [hrel.st_eq]; exact hrcv_g
  unfold runCellStep
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
    simulateQ_cell_deliverForgeHook_probe_run]
  cases sent.find? (fun c₀ => sameWireFig8 c₀ c') with
  | none => simp
  | some c =>
    obtain ⟨res, hres_cases, hres⟩ := deliverForgeBaseImplCell_run_of_receive_none fig tL qep t
      DeliverForge.sameHdrScheme Q c c' s_cell hrcv_df
    rcases hres_cases with rfl | rfl <;> simp only [hres, pure_bind]

omit [Zero Pt] [SampleableType Pt] in
theorem fwdEvictC_true_cases {PQ : Type} {ℓ : ℕ}
    (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (sC₀.base.mir.safeInj 3 = false ∧
      ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
        (LibsignalSimC.fwdEvictC qep fig fs H Q w true T pq' c').run sC₀ =
          ((StateT.lift (H.probe Q c') >>= fun _ => pure (some .rejected)) :
            StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) M _).run sC₀) ∨
    (sC₀.base.mir.safeInj 3 = true ∧
      ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
        (LibsignalSimC.fwdEvictC qep fig fs H Q w true T pq' c').run sC₀ =
          (LibsignalSimC.fwdAnswerC qep fig fs H Q w true none T pq' c').run sC₀) := by
  cases hsafe : sC₀.base.mir.safeInj 3
  · left; refine ⟨rfl, fun H => ?_⟩
    unfold LibsignalSimC.fwdEvictC
    simp [StateT.run_bind, StateT.run_get, pure_bind, hsafe]
  · right; refine ⟨rfl, fun H => ?_⟩
    unfold LibsignalSimC.fwdEvictC
    simp [StateT.run_bind, StateT.run_get, pure_bind, hsafe]

omit [Zero Pt] [SampleableType Pt] in
theorem fwdC_true_cases {PQ PQC : Type} {ℓ : ℕ} [Inhabited PQ]
    (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (∃ c, honestC = some c ∧ c ≠ c' ∧ sC₀.base.mir.safeInj 3 = false ∧
      predictReceiveWithSnapshots fig fs P sC₀ Q w c c' = none ∧
      ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
        (LibsignalSimC.fwdC P qep fig fs H Q w true ci? T pq' honestC c').run sC₀ =
          ((StateT.lift (H.probe Q c') >>= fun _ => pure (some .rejected)) :
            StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) M _).run sC₀) ∨
    (∃ c v, honestC = some c ∧ c ≠ c' ∧ sC₀.base.mir.safeInj 3 = false ∧
      predictReceiveWithSnapshots fig fs P sC₀ Q w c c' = some v ∧
      ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
        (LibsignalSimC.fwdC P qep fig fs H Q w true ci? T pq' honestC c').run sC₀ =
          (LibsignalSimC.resyncC qep fig fs H Q w ci? T pq' c v).run sC₀) ∨
    ((honestC.isNone = true ∨ sC₀.base.mir.safeInj 3 = true ∨ honestC = some c') ∧
      ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
        (LibsignalSimC.fwdC P qep fig fs H Q w true ci? T pq' honestC c').run sC₀ =
          (LibsignalSimC.fwdAnswerC qep fig fs H Q w true ci? T pq' c').run sC₀) := by
  cases honestC with
  | none =>
    right; right; refine ⟨Or.inl rfl, fun H => ?_⟩
    unfold LibsignalSimC.fwdC
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
  | some c =>
    by_cases hcond : (decide (c ≠ c') && true && !sC₀.base.mir.safeInj 3) = true
    · have hne : c ≠ c' := of_decide_eq_true (by
        revert hcond; cases decide (c ≠ c') <;> simp)
      have hnsafe : sC₀.base.mir.safeInj 3 = false := by
        revert hcond; cases sC₀.base.mir.safeInj 3 <;> simp
      cases heval : predictReceiveWithSnapshots fig fs P sC₀ Q w c c' with
      | none =>
        left; refine ⟨c, rfl, hne, hnsafe, heval, fun H => ?_⟩
        unfold LibsignalSimC.fwdC
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hcond, ↓reduceIte, heval]
      | some v =>
        right; left; refine ⟨c, v, rfl, hne, hnsafe, heval, fun H => ?_⟩
        unfold LibsignalSimC.fwdC
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hcond, ↓reduceIte, heval]
    · right; right
      have hcases : sC₀.base.mir.safeInj 3 = true ∨ some c = some c' := by
        by_cases h : c = c'
        · exact Or.inr (congrArg some h)
        · left
          have hdec : decide (c ≠ c') = true := decide_eq_true h
          revert hcond
          cases sC₀.base.mir.safeInj 3 <;> simp [hdec]
      refine ⟨Or.inr hcases, fun H => ?_⟩
      unfold LibsignalSimC.fwdC
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hcond, Bool.false_eq_true,
        ↓reduceIte]

omit [SampleableType Pt] in
theorem resyncC_none_lockstep {PQ : Type} {ℓ : ℕ}
    (qep t : ℕ) (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (g s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool) :
    (((LibsignalSimC.resyncC qep fig fs (probeHook fig (qep + 1))
        Q w ci? T pq' c none).run sC₀).run (g, fl)) =
      pure ((some .rejected, sC₀), (g, fl)) ∧
    runCellStep fig qep t tL
      (LibsignalSimC.resyncC qep fig fs (deliverForgeHook Pt ℓ) Q w ci? T pq' c none)
      sC₀ sent m' s_cell =
      pure ((((some .rejected, sC₀), sent), m'), s_cell) := by
  unfold LibsignalSimC.resyncC
  exact ⟨rfl, runCellStep_pure fig qep t tL (some RecvResult.rejected) sC₀ sent m' s_cell⟩

omit [Zero Pt] [SampleableType Pt] in
theorem zoomB_probeHook_onAccept_run {PQ : Type} {ℓ : ℕ} [Inhabited PQ]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t_v i_v : ℕ) (m_v : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ)
    (hrun : (onAccept (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w isDel t_v i_v m_v ci? T pq').run sC.base = pure (ans, b')) :
    (((LibsignalSimC.runOnBaseState (probeHook fig (qep + 1))
        (onAccept (qep := qep) Q w isDel t_v i_v m_v ci? T pq')).run sC).run (g, fl)) =
      pure ((ans, { sC with base := b' }), (g, fl)) := by
  rw [zoomB_run, StateT.run_bind, probeHook_lift_run, hrun]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]

omit [SampleableType Pt] in
theorem runCellStep_zoomB_onAccept {PQ : Type} {ℓ : ℕ} [Inhabited PQ]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t_v i_v : ℕ) (m_v : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ)
    (hrun : (onAccept (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w isDel t_v i_v m_v ci? T pq').run sC.base = pure (ans, b')) :
    runCellStep fig qep t tL
      (LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ)
        (onAccept (qep := qep) Q w isDel t_v i_v m_v ci? T pq'))
      sC sent m' s_cell =
      pure ((((ans, { sC with base := b' }), sent), m'), s_cell) := by
  rw [runCellStep_zoomB, hrun]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]

theorem resyncC_some_lockstep {PQ : Type} {ℓ : ℕ} [Inhabited PQ]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c : Fig8C Pt)
    (t_v i_v : ℕ) (pm_v : LibsignalMsgPublicPart × Plain ℓ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell g s_unsh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (fl : Bool)
    (hrel : PPrimePaperRelShifted s_cell m' g)
    (hsync : MirrorSync m' g s_unsh)
    (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ)
    (hrun : (onAccept (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w true t_v i_v pm_v.2 ci? T pq').run sC₀.base = pure (ans, b')) :
    let res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) :=
      match g.inTransit Q.other c with
      | none => none
      | some r =>
        match fig.receive (g.st Q) c with
        | none => some .rejected
        | some (_, t', i', m) =>
          some (.accepted t' i' (if g.chall.contains r.pos then none else some m))
    let g' :=
      match g.inTransit Q.other c with
      | none => g
      | some r =>
        match fig.receive (g.st Q) c with
        | none => g
        | some (st', _, _, _) => g.accept Q st' r.pos
    let m₁' :=
      match g.inTransit Q.other c with
      | none => m'
      | some r =>
        match fig.receive (g.st Q) c with
        | none => m'
        | some (_, _, _, _) => m'.accept Q () r.pos
    let s_cell' :=
      match g.inTransit Q.other c with
      | none => s_cell
      | some r =>
        match fig.receive (g.st Q) c with
        | none => s_cell
        | some (st', _, _, _) => s_cell.accept Q st' r.pos
    let out_ans := match res with
      | some (.accepted _ _ _) => ans
      | _ => some .rejected
    let out_sC := match res with
      | some (.accepted _ _ _) => { updKeptOnRes fig fs Q c res sC₀ with base := b' }
      | _ => sC₀
    (((LibsignalSimC.resyncC qep fig fs (probeHook fig (qep + 1))
        Q w ci? T pq' c (some (t_v, i_v, pm_v))).run sC₀).run (g, fl)) =
      pure ((out_ans, out_sC), (g', fl)) ∧
    runCellStep fig qep t tL
      (LibsignalSimC.resyncC qep fig fs (deliverForgeHook Pt ℓ)
        Q w ci? T pq' c (some (t_v, i_v, pm_v)))
      sC₀ sent m' s_cell =
      pure ((((out_ans, out_sC), sent), m₁'), s_cell') := by
  intro res g' m₁' s_cell' out_ans out_sC
  unfold LibsignalSimC.resyncC
  dsimp only
  rw [StateT.run_bind, StateT.run_bind, probeHook_liftC_deliver_run,
    runCellStep_bind, runCellStep_liftC_deliver,
    deliverImpl_h1_run fig Q c g hrel.win_mir_false,
    deliverImpl_auth_run fig t Q c s_cell hrel.win_df_false hrel.chall_df_nil,
    hrel.inTransit_eq Q.other c, hrel.st_eq, hsync.inTransit_eq Q.other c, hsync.chall_eq]
  cases htr : g.inTransit Q.other c with
  | none =>
    simp only [res, g', m₁', s_cell', out_ans, out_sC, htr, pure_bind, StateT.run_pure,
      runCellStep_pure, and_self]
  | some r =>
    cases hrcv : fig.receive (g.st Q) c with
    | none =>
      simp only [res, g', m₁', s_cell', out_ans, out_sC, htr, hrcv, pure_bind, StateT.run_pure,
        runCellStep_pure, and_self]
    | some v =>
      rcases v with ⟨st', t', i', m⟩
      simp only [res, g', m₁', s_cell', out_ans, out_sC, htr, hrcv, pure_bind,
        StateT.run_bind, StateT.run_modify, runCellStep_bind, runCellStep_modify,
        updKeptOnRes]
      exact ⟨zoomB_probeHook_onAccept_run Pt fig qep Q w true t_v i_v pm_v.2 ci? T pq'
          _ _ fl ans b' hrun,
        runCellStep_zoomB_onAccept Pt fig qep t tL Q w true t_v i_v pm_v.2 ci? T pq'
          _ sent _ _ ans b' hrun⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem deliver_noProbe_step_of_inTransit {St Msg C : Type}
    [DecidableEq Msg] [DecidableEq C]
    (qep : ℕ) (Q : Party) (st' : St) (pos : SM.Pos)
    {g : SM.GameState St Msg C} {m' : Mirror Msg C}
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
    (hepoch_pos : pos.epoch ≤ max (g.epoch Q) (g.epoch Q.other)) :
    let g' := g.accept Q st' pos
    let m₁' := m'.accept Q () pos
    let s_cell' : ℕ → Option ℕ → SM.GameState St Msg C := fun t tL =>
      if (s_cell t tL).win then s_cell t tL else (s_cell t tL).accept Q st' pos
    FirstNECellFamilyInvT qep false g' m₁' s_cell' ∧
    ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      CellK4Doomed tL t g' (s_cell' t tL) ∨
      (PPrimePaperRelShifted (s_cell t tL) m' g ∧
        s_cell' t tL = (s_cell t tL).accept Q st' pos) := by
  intro g' m₁' s_cell'
  have hinv' : FirstNECellFamilyInvT qep false g' m₁' s_cell' :=
    firstNECellFamilyInvT_deliver_noProbe_step (Key := BitVec 256) (Coins := BitVec 256)
      qep Q st' pos (Or.inr ⟨rfl, hcol, hrel_all⟩) hepoch_pos
  refine ⟨hinv', fun t ht tL htL => ?_⟩
  rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
  · left
    have hs_eq : s_cell' t tL = s_cell t tL := by
      dsimp only [s_cell']; simp only [hdoomed.2.2.2, ↓reduceIte]
    rw [hs_eq]
    exact ⟨hdoomed.1, hdoomed.2.1, hdoomed.2.2.1, hdoomed.2.2.2⟩
  · right
    refine ⟨hrel_sh, ?_⟩
    dsimp only [s_cell']
    simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
def updAmbSimStateC {PQ : Type} {ℓ : ℕ} (b : Bool) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    LibsignalToModularSchemeSimState PQ Pt ℓ :=
  if b then { sC with base := { sC.base with amb := sC.base.amb + 1 } } else sC

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
@[simp]
theorem updAmbSimStateC_fields {PQ : Type} {ℓ : ℕ} (b : Bool) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (updAmbSimStateC Pt b sC).kept = sC.kept ∧
    (updAmbSimStateC Pt b sC).sent = sC.sent ∧
    (updAmbSimStateC Pt b sC).snaps = sC.snaps ∧
    (updAmbSimStateC Pt b sC).base.honest = sC.base.honest ∧
    (updAmbSimStateC Pt b sC).base.mir = sC.base.mir ∧
    (updAmbSimStateC Pt b sC).base.stopped = sC.base.stopped := by
  unfold updAmbSimStateC
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

open Classical in
theorem firstNESimImpl'_deliver_run
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, fl, dead), tr) =
      (let r := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
       let j? := sC.base.honest.reverse.findIdx?
         (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
       let tr' := match r.1, j? with
         | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
         | _, _ => tr
       let hlazy := decide (∃ r_idx w_rem,
         EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
       let hprobe := r.2.2.2
       let fl' := fl || (hlazy && hprobe && !dead)
       let dead' := dead || !hlazy
       pure (r.1, (r.2.1, (r.2.2.1, fl', dead'), tr'))) := by
  unfold firstNESimImpl'
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
  rcases (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, g, false)).1 with
    _ | (_ | ⟨t, i, m⟩) <;>
    cases sC.base.honest.reverse.findIdx?
      (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;> rfl

open Classical in
theorem simulateQ_firstNESimImpl'_deliver_query_bind {α : Type}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (st : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
      (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool) ×
      KemFailTrackState P.C.F) :
    (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run st =
    ((firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
        (.inr (.inl (.inl (.inr (Q, w)))))).run st >>=
      fun z => (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (u z.1)).run z.2) := by
  simp only [simulateQ_query_bind, StateT.run_bind]
  dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
    OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd,
    PFunctor.Obj.mk, id]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem corrsKeptRecvInv_updAmbSimStateC {PQ : Type} {ℓ : ℕ}
    (b : Bool) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : CorrsKeptRecvInv sC g) :
    CorrsKeptRecvInv (updAmbSimStateC Pt b sC) g := by
  unfold updAmbSimStateC
  split_ifs <;> exact h

end

/-- Invariant requiring every corruption `(R, e) ∈ g.corrs` to have a corresponding snapshot in `snaps`. -/
def CorrsSnapsInv {PQ St Msg C : Type}
    (snaps : List (Party × ℕ × GhostState PQ))
    (g : SM.GameState St Msg C) : Prop :=
  ∀ R e, (R, e) ∈ g.corrs → ∃ g₀, (R, e, g₀) ∈ snaps

theorem corrsSnapsInv_of_corrs_nil {PQ St Msg C : Type}
    (snaps : List (Party × ℕ × GhostState PQ)) {s : SM.GameState St Msg C}
    (hnil : s.corrs = []) : CorrsSnapsInv snaps s := by
  intro R e hmem; rw [hnil] at hmem; cases hmem

theorem corrsSnapsInv_init_b {PQ Key St Msg Coins C : Type}
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C)
    (snaps : List (Party × ℕ × GhostState PQ)) (k : Key) (b : Bool) :
    CorrsSnapsInv snaps (SM.initState sm k b) :=
  corrsSnapsInv_of_corrs_nil snaps rfl

theorem corrsSnapsInv_afterCorr {PQ St Msg C : Type}
    {snaps : List (Party × ℕ × GhostState PQ)} {s : SM.GameState St Msg C}
    (P : Party) (g₀ : GhostState PQ) (h : CorrsSnapsInv snaps s) :
    CorrsSnapsInv ((P, s.epoch P, g₀) :: snaps) (s.afterCorr P) := by
  intro R e hmem
  rcases List.mem_cons.mp hmem with hhead | htail
  · cases hhead; exact ⟨g₀, List.mem_cons_self⟩
  · rcases h R e htail with ⟨g₁, hg₁⟩
    exact ⟨g₁, List.mem_cons_of_mem _ hg₁⟩

theorem corrsSnapsInv_of_corrs_eq {PQ St Msg C : Type}
    {snaps : List (Party × ℕ × GhostState PQ)} {s s' : SM.GameState St Msg C}
    (h : CorrsSnapsInv snaps s) (hcorrs : s'.corrs = s.corrs) :
    CorrsSnapsInv snaps s' := by
  intro R e hmem; exact h R e (hcorrs ▸ hmem)

theorem corrsSnapsInv_accept {PQ St Msg C : Type}
    {snaps : List (Party × ℕ × GhostState PQ)} {s : SM.GameState St Msg C}
    (Q : Party) (st' : St) (pos : SM.Pos) (h : CorrsSnapsInv snaps s) :
    CorrsSnapsInv snaps (s.accept Q st' pos) :=
  h

/-- Synchronization invariant relating `LibsignalToModularSchemeSimState`, `GameState`, and `Mirror`. -/
def SyncInv {PQ PQC Pt : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (g s_unsh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  (sC.base.stopped = false → ∃ s_R, SameMeta s_R sC.base g) ∧
  MirrorSync m' g s_unsh ∧
  SM.Thm1L17.WFState 3 g ∧
  CorrsLeEpoch g ∧
  (∀ P, g.epoch P ≤ qep + 1) ∧
  CorrsSnapIdxInv sC.snaps g ∧
  CorrsSnapsInv sC.snaps g ∧
  Fig8SenderSync g ∧
  CorrsKeptRecvInv sC g ∧
  KeptInv P Dh encPt encT idOf lam sC g ∧
  (∀ P, (g.st P).id = P) ∧
  HonestSentSync Pt sC.base.honest sent

def FirstNECellFamilyInvT_body {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (qep : ℕ) (g : SM.GameState St Msg C) (m' : Mirror Msg C)
    (s_cell : ℕ → Option ℕ → SM.GameState St Msg C) : Prop :=
  (∀ t₁ ∈ Finset.range ((qep + 1) + 2), ∀ t₂ ∈ Finset.range ((qep + 1) + 2),
    s_cell t₁ none = s_cell t₂ none) ∧
  ∀ t ∈ Finset.range ((qep + 1) + 2),
    PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
    ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      CellK4Doomed tL t g (s_cell t tL) ∨
      (PPrimePaperRelShifted (s_cell t tL) m' g ∧
        SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
        ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
        CellCompRel tL t (s_cell t none) (s_cell t tL))

/-- Three-branch coupled invariant (`Win`, absorbing `Dead`, or `Coupled ∧ Sync`) across the cell
family. -/
def FirstNECoupledInvD {PQ PQC Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (fl dead : Bool) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  (∃ t ∈ Finset.range ((qep + 1) + 2), ∃ tL ∈ SM.admissibleLastLeakGuesses 2 t,
    cellWinPred tL t (s_cell t tL) = true) ∨
  (dead = true ∧ fl = false) ∨
  (fl = false ∧ dead = false ∧
    FirstNECellFamilyInvT_body qep g m' s_cell ∧
    FirstNEInTransOriginInv qep sC.snaps g s_cell ∧
    SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))

theorem firstNECoupledInvD_unif_step {PQ PQC Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {P : Params PQ PQC} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt}
    {qep : ℕ} {fl dead : Bool} {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {sent : List (Fig8C Pt)}
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hinv : FirstNECoupledInvD P Dh encPt encT idOf lam qep fl dead sC sent m' g s_cell) :
    FirstNECoupledInvD P Dh encPt encT idOf lam qep fl dead sC sent m' g s_cell :=
  hinv

end CryptoVerification.LibsignalSession.HeadlineV1

end


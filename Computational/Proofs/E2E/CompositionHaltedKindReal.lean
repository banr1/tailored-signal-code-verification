/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.MainHaltedKeyInd -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHaltedInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst
import Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst
import Computational.Proofs.E2E.Dsl.HaltedStartSessionSim
import Computational.Proofs.E2E.Dsl.KindRedHaltedEval
import Computational.Proofs.E2E.Dsl.PqxdhSim

/-!
# Clamped handshake reduction `1KeyReal` equivalence

Proves `kindRedHalted_clamped_1KeyRealExp_eq` by coupling `HaltedKindSimInvInst` with
`pqxdhKeyIndImpl1KeyReal` state-list bounds.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Computational.Proofs.E2E.CompositionHaltedKindReal

open scoped BigOperators
open OracleComp OracleSpec
open _root_.ReductionDsl (Sig Ops Iface Ty Env Expr Comp GameCodec CostedReduction
  atomicSig atomicE2EOps bits e2eKeyIndTargetIface e2eSessionTargetIface smQT smQenc
  sidT sidV keyIndQT keyIndRT keyIndQenc keyIndRenc BV256 E2EKeyIndTag)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (BHE2EDrvState BHModelInst BHTargetResp Bytes BhShallowRed
  CompositionCostedReductionFamily bhDrvKiQueryOk
  bhE2EDrvWon bhE2EFinishStartSpk bhE2EGuard bhE2EMirror bhBaseMirror bhFwdU bhLiftP
  bhNoOpkRespPromoted bhPackSmResp bhShallowImplOfHandle bhTargetGameSpec
  bhTargetQenc bhTargetRdec configRefuseEarlyBobCorr e2eTargetGameCodec
  paramsIdsWithSpqr sessionSchemeFixedSpk)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack)
open Computational.Proofs.LibsignalCli.MainHaltedKeyInd (bhKindRedWithTracked)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (bhClassifyTarget bhClassifyTargetOnly
  bhE2EStepLocalSmSessionTracked bhFilterSmQuery oracleImplRSessionTracked)
open Computational.Proofs.E2E.Dsl.KindRedHalted (HaltedKindSubprograms bhKindHandleWithHalted
  bhKindRedWithHalted drvKindHaltedEnc drvKindHaltedTy kindHandleHalted_eval_ctl
  kindHandleHalted_eval_ki kindHandleHalted_eval_sm kindRedHalted kindStartStepHaltedC
  mkAtomicRevealSpkSkE mkAtomicTestSessionE)
open Computational.Proofs.E2E.Dsl.KindRedHaltedEval (atomicKeyIndTargetIface_liftP_eq_bhLiftP
  atomicKindRespEnc e2eTargetGameCodec_rdec_atomicKindRespEnc mem_support_of_bhLiftP
  packAtomicSmRespEnc)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (HaltedTargetAdvPerInstanceBounded
  bhKindRedWithHalted_eq_bhKindRedWithTracked kemFailSessionTracker)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst (HaltedKindSimInvInst
  isQueryBoundP_min isSendKiQuery nextSendDone nextSessDone)
open Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst (StepBudgetOkInst StepNextInvInst
  isKiQ isSendQ isSendQ_inl_inl isSessQ isStartQ stepBudgetOkInst_of_bounds)
open Computational.Proofs.E2E.Dsl.M3Interfaces (DrvMirrorBounded)

private theorem st_run_get_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (k : σ → StateT σ m α) (s : σ) : (MonadState.get >>= k).run s = (k s).run s :=
  pure_bind (s, s) _

private theorem st_run_getOf_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (k : σ → StateT σ m α) (s : σ) : (MonadStateOf.get >>= k).run s = (k s).run s :=
  pure_bind (s, s) _

private def StMono {S : SignalPqxdh.Setup} (st₀ st : SignalPqxdh.KeyIndState S) : Prop :=
  st₀.spkBundles.length ≤ st.spkBundles.length ∧ st₀.opkEntries.length ≤ st.opkEntries.length

private theorem stMono_refl {S : SignalPqxdh.Setup} (st : SignalPqxdh.KeyIndState S) :
    StMono st st := ⟨le_rfl, le_rfl⟩

private theorem stateT_mono_pure {S : SignalPqxdh.Setup} {α : Type} (a : α)
    {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((pure a : StateT (SignalPqxdh.KeyIndState S) ProbComp α).run st),
      StMono st₀ out.2 := by
  intro out hout
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  subst hout; exact h

private theorem stateT_mono_bind {S : SignalPqxdh.Setup} {α β : Type}
    (m : StateT (SignalPqxdh.KeyIndState S) ProbComp α)
    (f : α → StateT (SignalPqxdh.KeyIndState S) ProbComp β)
    {st₀ st : SignalPqxdh.KeyIndState S}
    (hm : ∀ p ∈ support (m.run st), StMono st₀ p.2)
    (hf : ∀ a st1, StMono st₀ st1 → ∀ out ∈ support ((f a).run st1), StMono st₀ out.2) :
    ∀ out ∈ support ((m >>= f).run st), StMono st₀ out.2 := by
  intro out hout
  simp only [StateT.run_bind, mem_support_bind_iff] at hout
  rcases hout with ⟨p, hp, hout⟩
  exact hf p.1 p.2 (hm p hp) out hout

private theorem stateT_mono_getOf {S : SignalPqxdh.Setup} {α : Type}
    (f : SignalPqxdh.KeyIndState S → StateT (SignalPqxdh.KeyIndState S) ProbComp α)
    {st₀ st : SignalPqxdh.KeyIndState S}
    (hf : ∀ out ∈ support ((f st).run st), StMono st₀ out.2) :
    ∀ out ∈ support ((MonadStateOf.get >>= f).run st), StMono st₀ out.2 := by
  simpa only [st_run_getOf_bind] using hf

private theorem stateT_mono_lift {S : SignalPqxdh.Setup} {α : Type} (x : ProbComp α)
    {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((liftM x : StateT (SignalPqxdh.KeyIndState S) ProbComp α).run st),
      StMono st₀ out.2 := by
  intro out hout
  change out ∈ support (x >>= fun a => pure (a, st)) at hout
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  rcases hout with ⟨_, -, rfl⟩
  exact h

private theorem stateT_mono_set {S : SignalPqxdh.Setup}
    {st₀ st st' : SignalPqxdh.KeyIndState S} (h : StMono st₀ st') :
    ∀ out ∈ support ((MonadStateOf.set st' : StateT (SignalPqxdh.KeyIndState S) ProbComp PUnit).run st),
      StMono st₀ out.2 := by
  intro out hout
  change out ∈ support (pure (PUnit.unit, st')) at hout
  simp only [support_pure, Set.mem_singleton_iff] at hout
  subst hout; exact h

private theorem st_run_lift_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (x : m α) (k : α → StateT σ m β) (s : σ) :
    ((liftM x : StateT σ m α) >>= k).run s = (x >>= fun a => (k a).run s) := by
  change ((x >>= fun a => pure (a, s)) >>= fun p => (k p.1).run p.2) = _
  simp only [LawfulMonad.bind_assoc, pure_bind]

set_option linter.unusedSimpArgs false in
private theorem recordKeyIndResp_stMono {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (r : SignalPqxdh.KeyIndRespEntry S) {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((SignalPqxdh.recordKeyIndResp S P r).run st), StMono st₀ out.2 := by
  intro out hmem
  unfold SignalPqxdh.recordKeyIndResp at hmem
  simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
  rcases hpart : st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s r) with _ | s
  · rw [hpart] at hmem; dsimp only at hmem
    simp only [st_run_lift_bind, StateT.run_set, support_pure, mem_support_bind_iff,
      Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨_, -, rfl⟩; exact h
  · rw [hpart] at hmem; dsimp only at hmem
    simp only [pure_bind, StateT.run_set, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact h

private theorem runKeyIndInitiate_stMono {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((SignalPqxdh.runKeyIndInitiate false S P sid u bundle).run st),
      StMono st₀ out.2 := by
  dsimp only [SignalPqxdh.runKeyIndInitiate]
  refine stateT_mono_getOf _ ?_
  by_cases hc1 : (st.sessions.any (fun e => e.sid == sid)) = true
  · simp only [hc1, ↓reduceIte]; exact stateT_mono_pure _ h
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
    split
    · next uEntry =>
      by_cases hc2 : (!SignalPqxdh.koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle) = true
      · simp only [hc2, ↓reduceIte]; exact stateT_mono_pure _ h
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h) fun ekASk _ h1 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h1) fun kemCoins _ h2 => ?_
        by_cases hc3 : (!(P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
            (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
          P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
            (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
        · simp only [hc3, ↓reduceIte]; exact stateT_mono_pure _ h2
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte]
          split
          · refine stateT_mono_bind _ _ (stateT_mono_lift _ h2) fun ⟨drKeyReal, roCache'⟩ _ h3 => ?_
            split
            · refine stateT_mono_bind _ _ (stateT_mono_pure _ h3) fun _ _ _ => ?_
              refine stateT_mono_bind _ _ (stateT_mono_set ⟨h.1, h.2⟩) fun _ _ h4 => ?_
              split <;> exact stateT_mono_pure _ h4
            · refine stateT_mono_bind _ _ (stateT_mono_lift _ h3) fun _ _ _ => ?_
              refine stateT_mono_bind _ _ (stateT_mono_set ⟨h.1, h.2⟩) fun _ _ h4 => ?_
              split <;> exact stateT_mono_pure _ h4
          · exact stateT_mono_pure _ h2
    · exact stateT_mono_pure _ h

set_option linter.unusedSimpArgs false in
private theorem pqxdh1KeyReal_stMono {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (kq : SignalPqxdh.KeyIndQuery S) (st : SignalPqxdh.KeyIndState S) :
    ∀ out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st), StMono st out.2 := by
  have h0 := stMono_refl st
  cases kq with
  | initPrin u =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (st.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ _ => ?_
      exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | roQuery secrets =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal; dsimp only
    refine stateT_mono_getOf _ ?_
    refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ _ => ?_
    exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | revealDhSecrets =>
    exact stateT_mono_pure _ h0
  | corruptIK u =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · exact stateT_mono_pure _ h0
    · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | genSPK u j =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (st.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      split
      · refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ h0 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ h0 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ h0 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ _ => ?_
        refine stateT_mono_bind _ _ (stateT_mono_set ⟨Nat.le_succ _, le_rfl⟩) fun _ _ h5 =>
          stateT_mono_pure _ h5
      · exact stateT_mono_pure _ h0
  | genOPK u j o =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ _ => ?_
      refine stateT_mono_bind _ _ (stateT_mono_set ⟨le_rfl, Nat.le_succ _⟩) fun _ _ h2 =>
        stateT_mono_pure _ h2
  | initiateOPK u i bundle =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : bundle.opkB?.isNone = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_stMono P (.sendOPK u i) u bundle h0
  | initiateNoOPK u i bundle =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : bundle.opkB?.isSome = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_stMono P (.sendNoOPK u i) u bundle h0
  | acceptOPK k j o hdr =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc1 : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == some (UInt32.ofNat o.val) &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hc1, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      by_cases hc2 : (st.usedRecvOPK.contains (k.val, j.val, o.val)) = true
      · simp only [hc2, ↓reduceIte]; exact stateT_mono_pure _ h0
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        by_cases hc3 : (!SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
        · simp only [hc3, ↓reduceIte]; exact stateT_mono_pure _ h0
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte]
          split
          · split
            · split
              · split_ifs
                · exact stateT_mono_pure _ h0
                · split
                  · split
                    · refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ _ => ?_
                      refine stateT_mono_bind _ _ (stateT_mono_set ⟨le_rfl, by simp⟩) fun _ _ h2 => ?_
                      refine stateT_mono_bind _ _ (recordKeyIndResp_stMono P _ h2) fun _ _ h3 => ?_
                      split <;> exact stateT_mono_pure _ h3
                    · exact stateT_mono_pure _ h0
                  · exact stateT_mono_pure _ h0
              · exact stateT_mono_pure _ h0
            · exact stateT_mono_pure _ h0
          · exact stateT_mono_pure _ h0
  | acceptNoOPK k j l hdr =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc1 : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == none &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hc1, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      by_cases hc2 : (st.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
      · simp only [hc2, ↓reduceIte]; exact stateT_mono_pure _ h0
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        by_cases hc3 : (!SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
        · simp only [hc3, ↓reduceIte]; exact stateT_mono_pure _ h0
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte]
          split
          · split
            · split
              · split
                · refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ _ => ?_
                  refine stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => ?_
                  refine stateT_mono_bind _ _ (recordKeyIndResp_stMono P _ h2) fun _ _ h3 => ?_
                  split <;> exact stateT_mono_pure _ h3
                · exact stateT_mono_pure _ h0
              · exact stateT_mono_pure _ h0
            · exact stateT_mono_pure _ h0
          · exact stateT_mono_pure _ h0
  | testSession sid =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (!SignalPqxdh.isKeyIndSessionTestable st sid) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      split
      · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
      · split
        · exact stateT_mono_pure _ h0
        · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | revealSessionKey sid =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · split_ifs
      · exact stateT_mono_pure _ h0
      · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
    · split
      · exact stateT_mono_pure _ h0
      · split_ifs
        · exact stateT_mono_pure _ h0
        · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | revealSpkSk u j =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · exact stateT_mono_pure _ h0
    · refine stateT_mono_bind _ _ (stateT_mono_set ⟨by simp, le_rfl⟩) fun _ _ h2 =>
        stateT_mono_pure _ h2
  | registerKey sk =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · exact stateT_mono_pure _ h0
    · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2

set_option linter.unusedSimpArgs false in
private theorem pqxdh1KeyReal_genSPK_succ {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (st : SignalPqxdh.KeyIndState S)
    {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.genSPK u j)).run st))
    (hresp : out.1 matches .bundleResp ..) :
    out.2.spkBundles.length = st.spkBundles.length + 1 := by
  unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
  simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
  by_cases hc : (st.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
  · simp only [hc, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; nomatch hresp
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hp : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
    · rw [hp] at hmem; dsimp only at hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; nomatch hresp
    · rw [hp] at hmem; dsimp only at hmem
      simp only [st_run_lift_bind, StateT.run_set, StateT.run_pure, pure_bind,
        LawfulMonad.bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨_, -, _, -, ⟨_, _⟩, -, _, -, rfl⟩
      simp

set_option linter.unusedSimpArgs false in
private theorem pqxdh1KeyReal_genOPK_succ {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (st : SignalPqxdh.KeyIndState S)
    {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.genOPK u j o)).run st))
    (hresp : out.1 matches .pkResp ..) :
    out.2.opkEntries.length = st.opkEntries.length + 1 := by
  unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
  simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
  by_cases hc : (st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
  · simp only [hc, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; nomatch hresp
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
    simp only [st_run_lift_bind, StateT.run_set, StateT.run_pure, pure_bind,
      LawfulMonad.bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨_, -, rfl⟩
    simp

private structure KindRealInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (qKiDone qSendDone qStartDone : ℕ) (qSessDone : ℕ → ℕ)
    (σst : (BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)) × SignalPqxdh.KeyIndState S) :
    Prop where
  base : HaltedKindSimInvInst (Dsl.PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K)
    C K b qStart qs qKiDone qSendDone qStartDone qSessDone σst.1
  st_list : Dsl.PqxdhSimTypes.stListBounded S qKiDone σst.2
  bundles_le_st : σst.1.1.bundles.length ≤ σst.2.spkBundles.length
  opks_le_st : σst.1.1.opks.length ≤ σst.2.opkEntries.length

private theorem KindRealInv.drvMirrorBounded_clamped {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σst : (BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)) × SignalPqxdh.KeyIndState S}
    (h : KindRealInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σst) :
    DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot) (min b.q_total S.N_opk_tot)
      (min b.q_total S.N_send_tot) b.q_total (min qStart (min b.q_total S.N_send_tot)) σst.1.1 where
  prins_le := Nat.le_trans h.base.mirror.prins_le h.base.ki_le
  bundles_le := Nat.le_trans h.bundles_le_st ((h.st_list.mono h.base.ki_le).spkBundles_le)
  opks_le := Nat.le_trans h.opks_le_st ((h.st_list.mono h.base.ki_le).opkEntries_le)
  sends_le := h.base.sends_length_le
  corrPrins_le := Nat.le_trans h.base.mirror.corrPrins_le h.base.ki_le
  insts_le := h.base.insts_length_le
  instMeta_le := h.base.instMeta_length_le
  revSpks_le := Nat.le_trans h.base.mirror.revSpks_le h.base.ki_le

private abbrev simKiImpl (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives) :
    QueryImpl (unifSpec + SignalPqxdh.keyIndSpec S)
      (StateT (SignalPqxdh.KeyIndState S) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SignalPqxdh.KeyIndState S) ProbComp) +
    SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P

private theorem simKiImpl_bhLiftP {S : SignalPqxdh.Setup} {P : SignalPqxdh.Primitives}
    {α : Type} (p : ProbComp α) (st : SignalPqxdh.KeyIndState S) :
    (simulateQ (simKiImpl S P) (bhLiftP (G := SignalPqxdh.keyIndSpec S) p)).run st =
      (p >>= fun a => pure (a, st)) := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp [bhLiftP, simulateQ_pure]
  | query_bind n mx ih =>
    simp only [bhLiftP, simulateQ_bind, simulateQ_query, StateT.run_bind]
    change (($ᵗ (Fin (n + 1)) : ProbComp _) >>= fun a => pure (a, st)) >>= _ = _
    simp only [bind_assoc, pure_bind]
    exact bind_congr fun u => ih u

private theorem simKiImpl_bhFwdU {S : SignalPqxdh.Setup} {P : SignalPqxdh.Primitives}
    (n : ℕ) (st : SignalPqxdh.KeyIndState S) :
    (simulateQ (simKiImpl S P) (bhFwdU (G := SignalPqxdh.keyIndSpec S) n)).run st =
      (($ᵗ (Fin (n + 1)) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, st)) := by
  simp only [bhFwdU]
  rfl

private theorem simKiImpl_query_ki {S : SignalPqxdh.Setup} {P : SignalPqxdh.Primitives}
    (kq : SignalPqxdh.KeyIndQuery S) (st : SignalPqxdh.KeyIndState S) :
    (simulateQ (simKiImpl S P)
      (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)).run st =
      (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st := by
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rfl

private theorem bhE2EFinishStartSpk_bundles_opks_eq {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    (bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac).2.bundles = σ.bundles ∧
      (bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac).2.opks = σ.opks := by
  unfold bhE2EFinishStartSpk
  rcases bhE2EGuard σ sid with _ | ⟨_, _, _, _⟩
  · exact ⟨rfl, rfl⟩
  · cases kr1 <;> cases kr2 <;> dsimp only <;> (try split_ifs) <;> exact ⟨rfl, rfl⟩

private theorem bhE2EStepLocalSmSessionTracked_bundles_opks_eq
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.SessionHaltTracker
      (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes CryptoVerification.E2E.SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : CryptoVerification.E2E.BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)}
    (hout : out ∈ support (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)) :
    out.2.1.bundles = σH.1.bundles ∧ out.2.1.opks = σH.1.opks := by
  rw [Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhE2EStepLocalSmSessionTracked_eq_filter] at hout
  split_ifs at hout
  · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
  · rcases hi : σH.1.insts[i]? with _ | d <;> rcases hm : σH.1.instMeta[i]? with _ | im <;>
      rw [hi, hm] at hout <;> dsimp only at hout
    · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
    · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
    · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
    · split_ifs at hout
      · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
      · rcases hg : d.gs with _ | gs <;>
          rcases hf : bhFilterSmQuery d im sq with _ | q' <;>
          rw [hg, hf] at hout <;> dsimp only at hout
        · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
        · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
        · simp only [support_pure, Set.mem_singleton_iff] at hout; subst hout; exact ⟨rfl, rfl⟩
        · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
          rcases hout with ⟨⟨⟨_, _⟩, _⟩, -, rfl⟩
          exact ⟨rfl, rfl⟩

private def kiNoOpkPromoted {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) : SignalPqxdh.KeyIndQuery S → Bool
  | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u
  | _ => false

private theorem atomicKeyIndLiftP_map {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α β : Type}
    (f : α → β) (p : ProbComp α) :
    (e2eKeyIndTargetIface S ℓ Pt).liftP (f <$> p) =
      f <$> (e2eKeyIndTargetIface S ℓ Pt).liftP p := by
  simp [atomicKeyIndTargetIface_liftP_eq_bhLiftP, bhLiftP]

private theorem eval_query_keyInd {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (qE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (kq : SignalPqxdh.KeyIndQuery S)
    (hq : qE.eval ρ = keyIndQenc kq) :
    (Comp.query (O := atomicE2EOps ℓ P C K decT encT)
      (I := e2eKeyIndTargetIface S ℓ Pt) E2EKeyIndTag.keyInd qE).eval ρ =
      keyIndRenc <$>
        (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
          OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) := by
  dsimp only [Comp.eval, e2eKeyIndTargetIface]
  rw [hq, Dsl.KindRedHalted.keyIndQdec_keyIndQenc]

private theorem comp_eval_bind_sample_bv256 {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (atomicSig ℓ Pt))} {b : Ty (atomicSig ℓ Pt)}
    (c2 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt)
      (BV256 (ℓ := ℓ) (Pt := Pt) :: Γ) b) (ρ : Env Γ) :
    (Comp.bind (.sample (I := e2eKeyIndTargetIface S ℓ Pt)
      (_root_.ReductionDsl.UniformSamplerTag.base _root_.ReductionDsl.AtomicBaseUnif.bv256) .unit) c2).eval ρ =
      (bhLiftP (G := SignalPqxdh.keyIndSpec S) ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
        fun bv => c2.eval (.cons bv ρ)) := by
  dsimp only [Comp.eval, e2eKeyIndTargetIface, _root_.ReductionDsl.atomicBaseSamplers,
    _root_.ReductionDsl.unifSamplers]
  rw [atomicKeyIndTargetIface_liftP_eq_bhLiftP]; rfl

private theorem comp_eval_bind {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {a b : Ty (atomicSig ℓ Pt)}
    (c1 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ a)
    (c2 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) (a :: Γ) b) (ρ : Env Γ) :
    (Comp.bind c1 c2).eval ρ = (c1.eval ρ >>= fun x => c2.eval (.cons x ρ)) := rfl

private theorem comp_eval_ret {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {a : Ty (atomicSig ℓ Pt)}
    (e : Expr (atomicE2EOps ℓ P C K decT encT) Γ a) (ρ : Env Γ) :
    (Comp.ret (I := e2eKeyIndTargetIface S ℓ Pt) e).eval ρ = pure (e.eval ρ) := rfl

private theorem comp_eval_caseOpt {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {a b : Ty (atomicSig ℓ Pt)}
    (e : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt a))
    (cN : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ b)
    (cS : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) (a :: Γ) b) (ρ : Env Γ) :
    (Comp.caseOpt e cN cS).eval ρ = match e.eval ρ with | none => cN.eval ρ | some x => cS.eval (.cons x ρ) := by
  dsimp only [Comp.eval]; cases e.eval ρ <;> rfl

set_option maxHeartbeats 800000 in
private theorem kindHandle_1KeyReal_step
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (smStep : Dsl.KindRedHaltedInst.HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT
      (Dsl.PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K))
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {b : SignalPqxdh.QueryBudget} {qStart qep : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)}
    {st : SignalPqxdh.KeyIndState S}
    (hInv : KindRealInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone (σH, st))
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (hBud : StepBudgetOkInst b qStart qs qKiDone qSendDone qStartDone qSessDone t) :
    let qInst := Finset.sup (Finset.range qStart) qs
    let subs := Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b
    let R := kindRedHalted subs b qStart qInst qep
    let T := kemFailSessionTracker (ℓ := ℓ) C.F K
    let handleRef := bhKindHandleWithHalted T.init
      (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K
    ((simulateQ (simKiImpl S P)
        (R.handle.eval
          (.cons (drvKindHaltedEnc subs σH) (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil)))).run st =
      Prod.map (Prod.map atomicKindRespEnc (drvKindHaltedEnc subs)) id <$>
        (simulateQ (simKiImpl S P) (handleRef σH (bhTargetQenc t))).run st) ∧
    (∀ out ∈ support ((simulateQ (simKiImpl S P) (handleRef σH (bhTargetQenc t))).run st),
      StepNextInvInst (fun qKi qSend qSt qSess s =>
          KindRealInv C K b qStart qs qKi qSend qSt qSess s)
        qStart qKiDone qSendDone qStartDone qSessDone t (out.1.2, out.2)) := by
  dsimp only
  set qInst := Finset.sup (Finset.range qStart) qs
  set subs := Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b
  set T := kemFailSessionTracker (ℓ := ℓ) C.F K
  have hTrack := Dsl.PrefixRedHaltedInst.kemBridgeTrackInvLocal_validSimTrackInv (ℓ := ℓ) C.F K
  have hMir := hInv.drvMirrorBounded_clamped
  rcases t with (kq | ctl) | ⟨i, sq⟩
  · dsimp only [StepBudgetOkInst] at hBud
    rcases hBud with ⟨hKiNext, hSendNext⟩
    have hSendNext' : nextSendDone qSendDone kq ≤ S.N_send_tot := by
      dsimp only [nextSendDone]; split_ifs with hs
      · exact hSendNext hs
      · exact hInv.base.send_le
    dsimp only [kindRedHalted]
    rw [kindHandleHalted_eval_ki]
    have hRhsEq :
        bhKindHandleWithHalted T.init
          (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K σH
          (bhTargetQenc (.inl (.inl kq))) =
        if (bhDrvKiQueryOk P σH.1.toModelDriverBase kq && !kiNoOpkPromoted σH.1 kq) = true then
          do
            let kr ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
              OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
            pure ((.inl (.inl kr) : CryptoVerification.E2E.BHTargetResp ℓ),
              (bhE2EMirror σH.1 kq kr, σH.2))
        else
          pure ((.inl (.inl .noneResp) : CryptoVerification.E2E.BHTargetResp ℓ), σH) := by
      cases kq <;> rfl
    rw [hRhsEq]
    let ρ_ki : Env [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
        Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
        drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
      .cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
        (.cons (drvKindHaltedEnc subs σH) (.cons (.inl (.inl (keyIndQenc kq))) .nil)))
    have hokE : (subs.kiQueryOkE b qStart (.fst .v2) .v0).eval ρ_ki =
        (bhDrvKiQueryOk P σH.1.toModelDriverBase kq && !kiNoOpkPromoted σH.1 kq) := by
      have hok0 := Dsl.HaltedStartSessionSim.kiQueryOkClampedE_eval (C := C) (K := K) (decT := decT)
        (encT := encT) (σ := σH.1) (kq := kq)
        b qStart hP (.fst .v2) .v0 ρ_ki rfl rfl hMir.prins_le hMir.instMeta_le
      dsimp only [subs, Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped, ρ_ki] at hok0 ⊢
      rw [hok0]
      cases kq <;> rfl
    dsimp only [ρ_ki] at hokE
    rw [hokE]
    cases hok : (bhDrvKiQueryOk P σH.1.toModelDriverBase kq && !kiNoOpkPromoted σH.1 kq)
    · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure,
        map_pure, Prod.map, atomicKindRespEnc, drvKindHaltedEnc, id_eq]
      refine ⟨rfl, fun out hout => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact {
        base := hInv.base.kiSkip_preserves kq hKiNext hSendNext'
        st_list := hInv.st_list.mono (Nat.le_succ _)
        bundles_le_st := hInv.bundles_le_st
        opks_le_st := hInv.opks_le_st
      }
    · simp only [↓reduceIte]
      have hq := eval_query_keyInd (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        .v0 ρ_ki kq rfl
      dsimp only [ρ_ki] at hq
      rw [hq]
      simp only [bind_map_left, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        map_bind, map_pure]
      change ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st >>= _) =
        ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st >>= _) ∧ _
      refine ⟨bind_congr_of_forall_mem_support _
          fun (p : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S) hkr => ?_,
        fun out hout => ?_⟩
      · rcases p with ⟨kr, st'⟩
        have hm := Dsl.HaltedStartSessionSim.mirrorClampedE_eval (P := P) (C := C) (K := K)
          (decT := decT) (encT := encT) b (.fst .v3) .v1 .v0 (.cons (keyIndRenc kr) ρ_ki)
          σH.1 kq kr rfl rfl rfl
        have hst' := Dsl.PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_preserves_stListBounded kq hInv.st_list hkr
        have hstTot := hst'.mono hKiNext
        have hClampEq : Dsl.HaltedStartSessionSim.bhE2EMirrorClamped
            (min b.q_total S.N_spk_tot) (min b.q_total S.N_opk_tot) σH.1 kq kr =
            bhE2EMirror σH.1 kq kr := by
          refine Dsl.HaltedStartSessionSim.bhE2EMirrorClamped_eq_of_lt σH.1 kq kr
            (fun hkg hkrb => ?_) (fun hkg hkrp => ?_)
          · cases kq with
            | genSPK u j =>
              cases kr with
              | bundleResp _ =>
                have hlen := pqxdh1KeyReal_genSPK_succ P u j st hkr (by trivial)
                have h1 := hInv.bundles_le_st; have h2 := hstTot.spkBundles_le
                dsimp only at hlen h1 h2 ⊢; omega
              | _ => nomatch hkrb
            | _ => nomatch hkg
          · cases kq with
            | genOPK u j o =>
              cases kr with
              | pkResp _ =>
                have hlen := pqxdh1KeyReal_genOPK_succ P u j o st hkr (by trivial)
                have h1 := hInv.opks_le_st; have h2 := hstTot.opkEntries_le
                dsimp only at hlen h1 h2 ⊢; omega
              | _ => nomatch hkrp
            | _ => nomatch hkg
        rw [hClampEq] at hm
        dsimp only [Comp.eval, Expr.eval, Env.get, subs,
          Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped, ρ_ki] at hm ⊢
        rw [hm]
        simp [Prod.map, atomicKindRespEnc, drvKindHaltedEnc]
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
        rcases hout with ⟨⟨kr, st'⟩, hkr, rfl⟩
        have hst' := Dsl.PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_preserves_stListBounded kq hInv.st_list hkr
        have hMono := pqxdh1KeyReal_stMono P kq st (kr, st') hkr
        have hStSelf : { σH.1 with st := σH.1.st } = σH.1 := rfl
        have hBase' := (hInv.base.kiMirror_preserves kq kr σH.1.st hKiNext hSendNext'
          (hInv.base.kiReach.mono (Nat.le_succ _))).1
        rw [hStSelf] at hBase'
        refine {
          base := hBase'
          st_list := hst'
          bundles_le_st := ?_
          opks_le_st := ?_
        }
        · dsimp only [bhE2EMirror, bhBaseMirror]
          cases kq with
          | genSPK u j =>
            cases kr with
            | bundleResp bnd =>
              have hlen := pqxdh1KeyReal_genSPK_succ P u j st hkr (by trivial)
              have h1 := hInv.bundles_le_st
              dsimp only at hlen h1 ⊢; simp only [List.length_cons]; omega
            | _ => exact le_trans hInv.bundles_le_st hMono.1
          | _ => cases kr <;> exact le_trans hInv.bundles_le_st hMono.1
        · dsimp only [bhE2EMirror, bhBaseMirror]
          cases kq with
          | genOPK u j o =>
            cases kr with
            | pkResp pk =>
              have hlen := pqxdh1KeyReal_genOPK_succ P u j o st hkr (by trivial)
              have h1 := hInv.opks_le_st
              dsimp only at hlen h1 ⊢; simp only [List.length_cons]; omega
            | _ => exact le_trans hInv.opks_le_st hMono.2
          | _ => cases kr <;> exact le_trans hInv.opks_le_st hMono.2
  · cases ctl with | startDR sid =>
    dsimp only [StepBudgetOkInst] at hBud
    have hEvalCtl :
        (kindRedHalted subs b qStart qInst qep).handle.eval
          (.cons (drvKindHaltedEnc subs σH)
            (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inr (.startDR sid)))) .nil)) =
        Prod.map atomicKindRespEnc (drvKindHaltedEnc subs) <$>
          bhKindHandleWithHalted T.init
            (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K σH
            (bhTargetQenc (.inl (.inr (.startDR sid)))) := by
      dsimp only [kindRedHalted]
      rw [kindHandleHalted_eval_ctl]
      dsimp only [bhKindHandleWithHalted, bhTargetQenc, kindStartStepHaltedC]
      let Γ_ctl : List (Ty (atomicSig ℓ Pt)) :=
        [sidT (ℓ := ℓ) (Pt := Pt) S,
          Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
      let ρ_ctl : Env Γ_ctl :=
        .cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons (drvKindHaltedEnc subs σH) (.cons (.inl (.inr (sidV sid))) .nil)))
      rw [comp_eval_bind, comp_eval_ret]
      have hpair : (Expr.pair (O := atomicE2EOps ℓ P C K decT encT) .v2 .v0).eval ρ_ctl =
          (drvKindHaltedEnc subs σH, sidV sid) := rfl
      dsimp only [ρ_ctl] at hpair
      rw [hpair, pure_bind, comp_eval_caseOpt]
      let Γ1 := Ty.prod (drvKindHaltedTy subs) (sidT (ℓ := ℓ) (Pt := Pt) S) :: Γ_ctl
      let ρ1 : Env Γ1 := .cons (drvKindHaltedEnc subs σH, sidV sid) ρ_ctl
      have hprep : (subs.prepStartSpkE b qStart (.fst (.fst .v0)) (.snd .v0)).eval ρ1 =
          (bhE2EGuard σH.1 sid).map (fun (_, _, uj) => uj) := by
        dsimp only [subs, Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped]
        exact Dsl.HaltedStartSessionSim.prepStartSpkClampedE_eval b qStart
          (.fst (.fst .v0)) (.snd .v0) ρ1 σH.1 sid rfl rfl hMir
      dsimp only [ρ1, ρ_ctl] at hprep
      rw [hprep]
      rcases hguard : bhE2EGuard σH.1 sid with _ | ⟨_, _, u, j⟩
      · dsimp only [Option.map]
        rw [comp_eval_ret]
        simp [Expr.eval, Expr.v0, Prod.map, atomicKindRespEnc]
      · dsimp only [Option.map]
        let Γ2 := Ty.prod (_root_.ReductionDsl.FinT (ℓ := ℓ) (Pt := Pt) S.N_id)
          (_root_.ReductionDsl.FinT (ℓ := ℓ) (Pt := Pt) S.N_recv) :: Γ1
        let ρ2 : Env Γ2 := .cons (u, j) ρ1
        rw [comp_eval_bind]
        have htsQ : (mkAtomicTestSessionE (O := atomicE2EOps ℓ P C K decT encT) (.snd .v1)).eval ρ2 =
            keyIndQenc (.testSession sid) := by
          simp [ρ2, ρ1, Expr.eval, Expr.v1, Dsl.KindRedHalted.sidOfV_sidV]
        have hq1 := eval_query_keyInd (mkAtomicTestSessionE (.snd .v1)) ρ2 (.testSession sid) htsQ
        dsimp only [ρ2, ρ1, ρ_ctl] at hq1
        rw [hq1]
        simp only [bind_map_left, map_bind, bind_assoc]
        refine bind_congr fun ts => ?_
        let Γ3 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ2
        let ρ3 : Env Γ3 := .cons (keyIndRenc ts) ρ2
        rw [comp_eval_bind]
        have hskQ : (mkAtomicRevealSpkSkE (O := atomicE2EOps ℓ P C K decT encT) .v1).eval ρ3 =
            keyIndQenc (.revealSpkSk u j) := by
          simp [ρ3, ρ2, Expr.eval, Expr.v1]
        have hq2 := eval_query_keyInd (mkAtomicRevealSpkSkE .v1) ρ3 (.revealSpkSk u j) hskQ
        dsimp only [ρ3, ρ2, ρ1, ρ_ctl] at hq2
        rw [hq2]
        simp only [bind_map_left, bind_assoc]
        refine bind_congr fun sk => ?_
        let Γ4 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ3
        let ρ4 : Env Γ4 := .cons (keyIndRenc sk) ρ3
        have hsmp := comp_eval_bind_sample_bv256
          (subs.finishStartSpkHaltedC b qStart (.some (subs.drvBitE (.fst (.fst .v4))))
            (.fst .v4) (.snd .v4) .v2 .v1 .v0) ρ4
        refine (congrArg (fun m => m >>= fun v =>
          pure ((.inl (.inr v.1) : (e2eTargetGameCodec S ℓ Pt).R.denote), v.2)) hsmp).trans ?_
        dsimp only [ρ4, ρ3, ρ2, ρ1, ρ_ctl]
        rw [bind_assoc]
        refine bind_congr fun bv => ?_
        dsimp only [subs, Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped]
        rw [Dsl.HaltedStartSessionSim.finishStartSpkHaltedClampedC_eval
          (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          b qStart _ _ _ _ _ _ _ σH sid ts sk rfl rfl rfl rfl hInv.base.tracks_length_le hMir]
        dsimp only [Expr.eval, Expr.v0, Env.get]
        rw [Dsl.HaltedStartSessionSim.drvBitE_eval
          (P := P) (C := C) (K := K) (decT := decT) (encT := encT) _ _ σH.1 rfl]
        simp only [pure_bind, map_pure]
        rfl
    refine ⟨?_, fun out hout => ?_⟩
    · rw [hEvalCtl, simulateQ_map, StateT.run_map]
      exact congrArg (· <$> _) (funext fun ⟨_, _⟩ => rfl)
    dsimp only [bhKindHandleWithHalted, bhTargetQenc] at hout
    rcases hguard : bhE2EGuard σH.1 sid with _ | ⟨_, _, u, j⟩
    · rw [hguard] at hout
      simp only [Option.map, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact {
        base := {
          ki_le := hInv.base.ki_le, send_le := hInv.base.send_le, start_le := hBud
          sess_le := hInv.base.sess_le, sends_le_ki := hInv.base.sends_le_ki
          sends_le_send := hInv.base.sends_le_send
          insts_le_start := Nat.le_succ_of_le hInv.base.insts_le_start
          subsetSends := hInv.base.subsetSends
          mirror := hInv.base.mirror.mono le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_succ _)
          metaAligned := hInv.base.metaAligned, kiReach := hInv.base.kiReach
          tracks_len := hInv.base.tracks_len, slot_reach := hInv.base.slot_reach
          slot_track := hInv.base.slot_track }
        st_list := hInv.st_list, bundles_le_st := hInv.bundles_le_st, opks_le_st := hInv.opks_le_st }
    · rw [hguard] at hout
      dsimp only [Option.map] at hout
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        simKiImpl_query_ki, simKiImpl_bhLiftP, bind_assoc, pure_bind,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
      rcases hout with ⟨⟨ts, st1⟩, hts, ⟨sk, st2⟩, hsk, bv0, -, rfl⟩
      have hst1 := Dsl.PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_testSession_preserves_stListBounded
        sid hInv.st_list hts
      have hst2 := Dsl.PqxdhSimTypes.pqxdhKeyIndImpl1KeyReal_revealSpkSk_preserves_stListBounded
        u j hst1 hsk
      have hm1 := pqxdh1KeyReal_stMono P (.testSession sid) st (ts, st1) hts
      have hm2 := pqxdh1KeyReal_stMono P (.revealSpkSk u j) st1 (sk, st2) hsk
      have hBase' := (hInv.base.finishStartSpkTracked_preserves hTrack C K (some σH.1.b)
        hBud sid ts sk bv0).1
      have hBO := bhE2EFinishStartSpk_bundles_opks_eq C K (some σH.1.b) σH.1 sid ts sk bv0
      exact {
        base := hBase'
        st_list := hst2
        bundles_le_st := by
          dsimp only [Dsl.KindRedHalted.bhE2EFinishStartSpkTracked]
          rw [hBO.1]; exact le_trans hInv.bundles_le_st (le_trans hm1.1 hm2.1)
        opks_le_st := by
          dsimp only [Dsl.KindRedHalted.bhE2EFinishStartSpkTracked]
          rw [hBO.2]; exact le_trans hInv.opks_le_st (le_trans hm1.2 hm2.2)
      }
  · dsimp only [StepBudgetOkInst] at hBud
    dsimp only [kindRedHalted]
    rw [kindHandleHalted_eval_sm]
    dsimp only [bhKindHandleWithHalted, bhTargetQenc]
    let ρ_sm : Env [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)),
        drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
      .cons (i, smQenc sq) (.cons (drvKindHaltedEnc subs σH) (.cons (.inr (i, smQenc sq)) .nil))
    have hSim := hInv.base.toHaltedSimInv hTrack
    have hSmEq :
        (subs.haltedStepLocalSmC b qStart qInst qep .v1 (.fst .v0) (.snd .v0)).eval ρ_sm =
          (e2eKeyIndTargetIface S ℓ Pt).liftP
            ((fun out => (packAtomicSmRespEnc out.1, drvKindHaltedEnc subs out.2)) <$>
              bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq) := by
      dsimp only [subs, Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped, drvKindHaltedEnc, T]
      exact smStep.stepC_eval b qStart qInst qep
        hInv.base.insts_length_le hInv.base.metaAligned
        hMir.corrPrins_le hMir.revSpks_le hMir.prins_le
        hSim.sessions hInv.base.epoch_bounded
        hInv.base.tracks_length_le hSim.tracks_inv
        .v1 (.fst .v0) (.snd .v0) ρ_sm i sq rfl rfl rfl
    dsimp only [ρ_sm] at hSmEq
    have hCompEq :
        ((subs.haltedStepLocalSmC b qStart qInst qep .v1 (.fst .v0) (.snd .v0)).eval ρ_sm >>=
          fun v => pure ((.inr v.1 : (e2eTargetGameCodec S ℓ Pt).R.denote), v.2)) =
        Prod.map (atomicKindRespEnc (S := S) (ℓ := ℓ) (Pt := Pt)) (drvKindHaltedEnc subs) <$>
          (bhLiftP (G := SignalPqxdh.keyIndSpec S)
            (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq) >>= fun p =>
              pure ((.inr p.1 : CryptoVerification.E2E.BHTargetResp ℓ), p.2)) := by
      dsimp only [ρ_sm]
      rw [hSmEq, atomicKeyIndLiftP_map, bind_map_left, atomicKeyIndTargetIface_liftP_eq_bhLiftP,
        map_bind]
      refine bind_congr fun p => ?_
      rw [map_pure]
      rfl
    refine ⟨?_, fun out hout => ?_⟩
    · dsimp only [ρ_sm] at hCompEq
      rw [hCompEq, simulateQ_map, StateT.run_map]
      exact congrArg (· <$> _) (funext fun ⟨_, _⟩ => rfl)
    · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        simKiImpl_bhLiftP, bind_assoc, pure_bind, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hout
      rcases hout with ⟨⟨sr0, σH0⟩, hsm, rfl⟩
      have hBase' := (hInv.base.stepLocalSmSessionTracked_preserves hTrack C K qep decT encT
        i hBud sq hsm).1
      have hBO := bhE2EStepLocalSmSessionTracked_bundles_opks_eq T C K qep decT encT σH i sq hsm
      exact {
        base := hBase'
        st_list := hInv.st_list
        bundles_le_st := by rw [hBO.1]; exact hInv.bundles_le_st
        opks_le_st := by rw [hBO.2]; exact hInv.opks_le_st
      }

private def nextSessRemLocal (qStart : ℕ) (qSessRem : ℕ → ℕ) (i : ℕ) : ℕ → ℕ :=
  fun j => if i < qStart ∧ j = i then qSessRem j - 1 else qSessRem j

private theorem unpack_qb {ι : Type} {spec : OracleSpec ι} {α : Type}
    {Pred : ι → Prop} [DecidablePred Pred] {q : ι} {mx : spec.Range q → OracleComp spec α} {n : ℕ}
    (h : (liftM (OracleSpec.query (spec := spec) q) >>= mx).IsQueryBoundP Pred n) :
    (Pred q → 0 < n ∧ ∀ v, (mx v).IsQueryBoundP Pred (n - 1)) ∧
    (¬Pred q → ∀ v, (mx v).IsQueryBoundP Pred n) := by
  rw [isQueryBoundP_query_bind_iff] at h
  refine ⟨fun hp => ⟨h.1.resolve_left (fun hnp => hnp hp), fun v => ?_⟩, fun hnp v => ?_⟩
  · simpa [hp] using h.2 v
  · simpa [hnp] using h.2 v

private theorem kindRed_simulateQ_1KeyReal_eq_and_inv
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (smStep : Dsl.KindRedHaltedInst.HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT
      (Dsl.PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K))
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (b : SignalPqxdh.QueryBudget) (qStart qep : ℕ) (qs : ℕ → ℕ) :
    let qInst := Finset.sup (Finset.range qStart) qs
    let subs := Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b
    let R := kindRedHalted subs b qStart qInst qep
    let T := kemFailSessionTracker (ℓ := ℓ) C.F K
    let R_ref := bhKindRedWithHalted T.init
      (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K
    ∀ {α : Type} (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem : ℕ)
      (qSessDone qSessRem : ℕ → ℕ)
      (σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes))
      (st : SignalPqxdh.KeyIndState S),
      oa.IsQueryBoundP isKiQ qKiRem →
      oa.IsQueryBoundP isSendQ qSendRem →
      oa.IsQueryBoundP isStartQ qStartRem →
      (∀ k < qStart, oa.IsQueryBoundP (isSessQ k) (qSessRem k)) →
      qKiDone + qKiRem ≤ b.q_total →
      qSendDone + qSendRem ≤ S.N_send_tot →
      qStartDone + qStartRem ≤ min qStart S.N_send_tot →
      (∀ k < qStart, qSessDone k + qSessRem k ≤ qs k) →
      KindRealInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone (σH, st) →
      ((simulateQ (simKiImpl S P) ((simulateQ R.impl oa).run (drvKindHaltedEnc subs σH))).run st =
        Prod.map (Prod.map id (drvKindHaltedEnc subs)) id <$>
          (simulateQ (simKiImpl S P) ((simulateQ R_ref.impl oa).run σH)).run st) ∧
      (∀ p ∈ support ((simulateQ (simKiImpl S P) ((simulateQ R_ref.impl oa).run σH)).run st),
        ∃ qKi1 qSend1 qSt1 qSess1,
          KindRealInv C K b qStart qs qKi1 qSend1 qSt1 qSess1 (p.1.2, p.2)) := by
  dsimp only
  set qInst := Finset.sup (Finset.range qStart) qs
  set subs := Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b
  set R := kindRedHalted subs b qStart qInst qep
  set T := kemFailSessionTracker (ℓ := ℓ) C.F K
  set handleRef := bhKindHandleWithHalted T.init
    (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K
  set R_ref := bhKindRedWithHalted T.init
    (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qKiDone _ qSendDone _ qStartDone _ qSessDone _ σH st _ _ _ _ _ _ _ _ hInv
    refine ⟨by simp [simulateQ_pure, Prod.map], fun p hp => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨qKiDone, qSendDone, qStartDone, qSessDone, hInv⟩
  | query_bind q mx ih =>
    intro qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem σH st
      hTot0 hSend0 hStart0 hSess hqKi hqSend hqSt hqSess hInv
    have hTot := unpack_qb hTot0
    have hSend := unpack_qb hSend0
    have hStart := unpack_qb hStart0
    have hSess' : ∀ k < qStart,
        (isSessQ k q → 0 < qSessRem k ∧ ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k - 1)) ∧
        (¬isSessQ k q → ∀ v, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k)) :=
      fun k hk => unpack_qb (hSess k hk)
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    cases q with
    | inl n =>
      have hStepDsl : ((R.impl (.inl n)).run (drvKindHaltedEnc subs σH)) =
          (bhFwdU n >>= fun u => pure (u, drvKindHaltedEnc subs σH)) := rfl
      have hStepRef : ((R_ref.impl (.inl n)).run σH) =
          (bhFwdU n >>= fun u => pure (u, σH)) := rfl
      rw [hStepDsl, hStepRef]
      simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, simKiImpl_bhFwdU]
      have hcKi : ∀ u, (mx u).IsQueryBoundP isKiQ qKiRem :=
        hTot.2 (by simp [isKiQ, bhClassifyTarget])
      have hcSend : ∀ u, (mx u).IsQueryBoundP isSendQ qSendRem :=
        hSend.2 (by simp [isSendQ, bhClassifyTarget])
      have hcSt : ∀ u, (mx u).IsQueryBoundP isStartQ qStartRem :=
        hStart.2 (by simp [isStartQ, bhClassifyTarget])
      have hcSess : ∀ u k, k < qStart → (mx u).IsQueryBoundP (isSessQ k) (qSessRem k) :=
        fun u k hk => (hSess' k hk).2 (by simp [isSessQ, bhClassifyTarget]) u
      refine ⟨bind_congr fun u => ?_, fun p hp => ?_⟩
      · exact (ih u qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem
          σH st (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv).1
      · simp only [mem_support_bind_iff] at hp
        rcases hp with ⟨u, -, hpu⟩
        exact (ih u qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem qSessDone qSessRem
          σH st (hcKi u) (hcSend u) (hcSt u) (hcSess u) hqKi hqSend hqSt hqSess hInv).2 p hpu
    | inr t =>
      have htBound := stepBudgetOkInst_of_bounds hTot hSend hStart hSess' hqKi hqSend hqSt hqSess
      have hStepDsl : ((R.impl (.inr t)).run (drvKindHaltedEnc subs σH)) =
          (R.handle.eval
            (.cons (drvKindHaltedEnc subs σH) (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) >>=
            fun p => pure ((e2eTargetGameCodec S ℓ Pt).rdec t p.1, p.2)) := rfl
      have hStepRef : ((R_ref.impl (.inr t)).run σH) =
          (handleRef σH (bhTargetQenc t) >>=
            fun rs => pure (bhTargetRdec t rs.1, rs.2)) := rfl
      rw [hStepDsl, hStepRef]
      simp only [bind_assoc, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        pure_bind]
      obtain ⟨hStepEq, hResInv⟩ := kindHandle_1KeyReal_step (qep := qep) smStep hP hInv t htBound
      dsimp only at hStepEq hResInv
      rw [hStepEq]
      simp only [bind_map_left]
      have hCont : ∀ (v : (bhTargetGameSpec S ℓ (BitVec 512)).Range t)
          (σ1 : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes))
          (st1 : SignalPqxdh.KeyIndState S),
          StepNextInvInst (fun qKi qSend qSt qSess s =>
              KindRealInv C K b qStart qs qKi qSend qSt qSess s)
            qStart qKiDone qSendDone qStartDone qSessDone t (σ1, st1) →
          ((simulateQ (simKiImpl S P) ((simulateQ R.impl (mx v)).run (drvKindHaltedEnc subs σ1))).run st1 =
            Prod.map (Prod.map id (drvKindHaltedEnc subs)) id <$>
              (simulateQ (simKiImpl S P) ((simulateQ R_ref.impl (mx v)).run σ1)).run st1) ∧
          (∀ p ∈ support ((simulateQ (simKiImpl S P) ((simulateQ R_ref.impl (mx v)).run σ1)).run st1),
            ∃ qKi1 qSend1 qSt1 qSess1,
              KindRealInv C K b qStart qs qKi1 qSend1 qSt1 qSess1 (p.1.2, p.2)) := by
        intro v σ1 st1 hR
        rcases t with (kq | cq) | ⟨i, sq⟩
        · have hKi1 := hTot.1 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly])
          have hcSt := hStart.2 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSess : ∀ k < qStart, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k) :=
            fun k hk => (hSess' k hk).2 (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          by_cases hsk : isSendKiQuery kq = true
          · have hSend1 := hSend.1 ((isSendQ_inl_inl kq).mpr hsk)
            have hNext : nextSendDone qSendDone kq = qSendDone + 1 := by simp [nextSendDone, hsk]
            dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
            exact ih v (qKiDone + 1) (qKiRem - 1) (qSendDone + 1) (qSendRem - 1)
              qStartDone qStartRem qSessDone qSessRem σ1 st1
              (hKi1.2 v) (hSend1.2 v) hcSt hcSess
              (by have := hKi1.1; omega) (by have := hSend1.1; omega) hqSt hqSess hR
          · have hSend0' := hSend.2 (mt (isSendQ_inl_inl kq).mp hsk) v
            have hNext : nextSendDone qSendDone kq = qSendDone := by simp [nextSendDone, hsk]
            dsimp only [StepNextInvInst] at hR; rw [hNext] at hR
            exact ih v (qKiDone + 1) (qKiRem - 1) qSendDone qSendRem
              qStartDone qStartRem qSessDone qSessRem σ1 st1
              (hKi1.2 v) hSend0' hcSt hcSess
              (by have := hKi1.1; omega) hqSend hqSt hqSess hR
        · have hSt1 := hStart.1 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly])
          have hcKi := hTot.2 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSend := hSend.2 (by simp [isSendQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSess : ∀ k < qStart, (mx v).IsQueryBoundP (isSessQ k) (qSessRem k) :=
            fun k hk => (hSess' k hk).2 (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          exact ih v qKiDone qKiRem qSendDone qSendRem (qStartDone + 1) (qStartRem - 1)
            qSessDone qSessRem σ1 st1
            hcKi hcSend (hSt1.2 v) hcSess hqKi hqSend (by have := hSt1.1; omega) hqSess hR
        · have hcKi := hTot.2 (by simp [isKiQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSend := hSend.2 (by simp [isSendQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSt := hStart.2 (by simp [isStartQ, bhClassifyTarget, bhClassifyTargetOnly]) v
          have hcSess : ∀ k < qStart,
              (mx v).IsQueryBoundP (isSessQ k) (nextSessRemLocal qStart qSessRem i k) := by
            intro k hk
            dsimp only [nextSessRemLocal]
            split_ifs with hki
            · rcases hki with ⟨_, rfl⟩
              exact ((hSess' k hk).1 (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly])).2 v
            · have hne : i ≠ k := fun h => hki ⟨h ▸ hk, h.symm⟩
              exact (hSess' k hk).2
                (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly, hne]) v
          have hqSess' : ∀ k < qStart,
              nextSessDone qStart qSessDone i k + nextSessRemLocal qStart qSessRem i k ≤ qs k := by
            intro k hk
            dsimp only [nextSessDone, nextSessRemLocal]
            split_ifs with hki
            · rcases hki with ⟨_, rfl⟩
              have hpos :=
                ((hSess' k hk).1 (by simp [isSessQ, bhClassifyTarget, bhClassifyTargetOnly])).1
              have hle := hqSess k hk
              omega
            · exact hqSess k hk
          exact ih v qKiDone qKiRem qSendDone qSendRem qStartDone qStartRem
            (nextSessDone qStart qSessDone i) (nextSessRemLocal qStart qSessRem i) σ1 st1
            hcKi hcSend hcSt hcSess hqKi hqSend hqSt hqSess' hR
      refine ⟨bind_congr_of_forall_mem_support _
          fun (p0 : (CryptoVerification.E2E.BHTargetResp ℓ ×
            (BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes))) × SignalPqxdh.KeyIndState S) hrs => ?_,
        fun p hp => ?_⟩
      · rcases p0 with ⟨⟨r, σ1⟩, st1⟩
        have hAns := e2eTargetGameCodec_rdec_atomicKindRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t r
        dsimp only [Prod.map, id_eq, e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
        rw [hAns]
        exact (hCont (bhTargetRdec t r) σ1 st1 (hResInv ((r, σ1), st1) hrs)).1
      · simp only [mem_support_bind_iff] at hp
        rcases hp with ⟨⟨⟨r, σ1⟩, st1⟩, hrs, hprs⟩
        exact (hCont (bhTargetRdec t r) σ1 st1 (hResInv ((r, σ1), st1) hrs)).2 p hprs

/-- Exact `pqxdhKeyInd1KeyRealExp` `ProbComp` equivalence for `kindRedHalted` instantiated with
`mkKindSubprogramsHaltedClamped smStep b`. -/
theorem kindRedHalted_clamped_1KeyRealExp_eq
    {Pt : Type} (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (smStep : Dsl.KindRedHaltedInst.HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT
      (Dsl.PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K))
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) :
    let qInst := Finset.sup (Finset.range qStart) qs
    let subs := Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b
    SignalPqxdh.pqxdhKeyInd1KeyRealExp S P
        ⟨(kindRedHalted subs b qStart qInst qep).eval (fun _ => B_A) ()⟩ =
      SignalPqxdh.pqxdhKeyInd1KeyRealExp S P
        ⟨(bhKindRedWithTracked (kemFailSessionTracker (ℓ := ℓ) C.F K).init
            (fun d : BHModelInst S ℓ =>
              oracleImplRSessionTracked (kemFailSessionTracker (ℓ := ℓ) C.F K)
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                  ℓ d.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT))
            P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K).eval (fun _ => B_A) ()⟩ := by
  dsimp only
  set qInst := Finset.sup (Finset.range qStart) qs
  set subs := Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b
  set T := kemFailSessionTracker (ℓ := ℓ) C.F K
  rw [← bhKindRedWithHalted_eq_bhKindRedWithTracked T P
    (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT]
  unfold SignalPqxdh.pqxdhKeyInd1KeyRealExp SignalPqxdh.pqxdhKeyInd1KeyExpForHandshake
  refine bind_congr fun secb => ?_
  dsimp only
  suffices hRun :
      (simulateQ (simKiImpl S P) ((kindRedHalted subs b qStart qInst qep).eval (fun _ => B_A) ())).run
        (SignalPqxdh.KeyIndState.empty S secb) =
      (simulateQ (simKiImpl S P)
        ((bhKindRedWithHalted T.init (bhE2EStepLocalSmSessionTracked T C K qep decT encT)
          P C K).eval (fun _ => B_A) ())).run
        (SignalPqxdh.KeyIndState.empty S secb) by
    exact congrArg (· >>= _) hRun
  rcases hB with ⟨_, hSend, _, hTot, _, hStSend, hStQ, _, hSess⟩
  have hStMin := isQueryBoundP_min B_A isStartQ hStQ hStSend
  unfold CostedReduction.eval BhShallowRed.eval
  have hInitEq :
      (kindRedHalted subs b qStart qInst qep).init.eval (.cons () .nil) =
        Prod.map id (drvKindHaltedEnc subs) <$>
          (bhKindRedWithHalted T.init (bhE2EStepLocalSmSessionTracked T C K qep decT encT)
            P C K).init () := by
    dsimp only [kindRedHalted, bhKindRedWithHalted, Comp.eval, subs,
      Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped]
    rw [Dsl.HaltedStartSessionSim.initKindC_eval, atomicKeyIndLiftP_map, bind_map_left]
    simp only [atomicKeyIndTargetIface_liftP_eq_bhLiftP, bhLiftP,
      simulateQ_bind, simulateQ_pure, map_bind, map_pure, bind_assoc, pure_bind,
      Expr.eval, Expr.v0, Env.get, Prod.map, id_eq, drvKindHaltedEnc, List.map_nil]
  rw [hInitEq, bind_map_left]
  simp only [simulateQ_bind, StateT.run_bind]
  refine bind_congr_of_forall_mem_support _
    fun (p0 : (Unit × (BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes))) ×
      SignalPqxdh.KeyIndState S) hσ0 => ?_
  dsimp only [bhKindRedWithHalted] at hσ0
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    simKiImpl_bhLiftP, bind_assoc, pure_bind,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hσ0
  rcases hσ0 with ⟨secb_drv, -, rfl⟩
  let σ0 : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes) := ({ b := secb_drv }, [])
  have hInitInv : KindRealInv C K b qStart qs 0 0 0 (fun _ => 0)
      (σ0, SignalPqxdh.KeyIndState.empty S secb) :=
    { base := HaltedKindSimInvInst.empty _ C K b qStart qs secb_drv
      st_list := Dsl.PqxdhSimTypes.stListBounded.empty S 0 secb
      bundles_le_st := Nat.zero_le _, opks_le_st := Nat.zero_le _ }
  dsimp only [Prod.map, id_eq]
  obtain ⟨hSimEq, hSimInv⟩ := kindRed_simulateQ_1KeyReal_eq_and_inv smStep hP b qStart qep qs
    B_A 0 b.q_total 0 S.N_send_tot 0 (min qStart S.N_send_tot) (fun _ => 0) qs
    σ0 (SignalPqxdh.KeyIndState.empty S secb)
    hTot hSend hStMin hSess (by omega) (by omega) (by omega) (fun k _ => by omega) hInitInv
  dsimp only at hSimEq hSimInv; rw [hSimEq, bind_map_left]
  refine bind_congr_of_forall_mem_support _
    fun (p1 : (Bool × (BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes))) ×
      SignalPqxdh.KeyIndState S) hout => ?_
  rcases p1 with ⟨⟨b_out, σ_out⟩, st_out⟩
  rcases hSimInv ((b_out, σ_out), st_out) hout with ⟨qKi1, qSend1, qSt1, qSess1, hInvOut⟩
  dsimp only [Prod.map, id_eq]
  have hFinEq : (kindRedHalted subs b qStart qInst qep).finish.eval
      (.cons (drvKindHaltedEnc subs σ_out) (.cons b_out .nil)) =
      (bhKindRedWithHalted T.init (bhE2EStepLocalSmSessionTracked T C K qep decT encT)
        P C K).finish σ_out b_out := by
    let ρ_f : Env [drvKindHaltedTy subs, .bool] :=
      .cons (drvKindHaltedEnc subs σ_out) (.cons b_out .nil)
    have hfk := Dsl.HaltedStartSessionSim.finishKindClampedE_eval
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (σ := σ_out.1)
      b qStart (.fst .v0) .v1 ρ_f rfl hInvOut.base.insts_length_le
    dsimp only [kindRedHalted, bhKindRedWithHalted, Comp.eval, subs,
      Dsl.KindRedHaltedInst.mkKindSubprogramsHaltedClamped, ρ_f] at hfk ⊢
    rw [hfk]; rfl
  rw [hFinEq]

end Computational.Proofs.E2E.CompositionHaltedKindReal

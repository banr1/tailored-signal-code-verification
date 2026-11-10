/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.CouplingV1
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.SteerCoupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.CorrSend
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Eager
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Eager
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Inject
import ProofLib.SepLogic.WP.StepsCore
import LibsignalBinary.Proofs.SpqrV1.KemFailFindFacts -- shake: keep
public import Computational.Proofs.HeadlineV1.SignedRefineC -- shake: keep
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.StateInv -- shake: keep
import Computational.Proofs.SpqrV1Sync.TopLog
import LibsignalBinary.Proofs.SpqrV1Sync.CoinBridge
import LibsignalBinary.Proofs.SpqrV1.MlKemCorrectFacts
import VCVio.ProgramLogic.Unary.HoareTriple
import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip
import Computational.Proofs.CryptoGames.SM.LibsignalCorrNoInj
import Computational.Specifications.Session.ACD19.Ratchet.LibsignalSim
import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
import Computational.Proofs.SpqrV1Sync.SendTotal -- shake: keep

/-!
# Hidden-salt glue for the V1 headline

**Checked by Lean.** Proves the `DeliverForge` coupling, `KemFailFind` tracking reduction, and
evicted-wire spurious-key invariants behind `HiddenSaltBoundHolds` (`hiddenSaltTerm ≤
hiddenSaltBound`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSpqrV1
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

/-! ## `DeliverForge` triviality -/

/-- An uncompromised in-transit record is never trivial under any healing delay `Δ`. -/
theorem trivial_false_of_inTransit_uncomp {St Msg C : Type} [DecidableEq C]
    {s : SM.GameState St Msg C} {Q : Party} {c : C} {r : SM.Record Msg C} (Δ : ℕ)
    (htr : s.inTransit Q c = some r) (hcomp : s.comp.contains r.pos = false) :
    s.trivial Δ r.pos = false := by
  have hmem : r ∈ s.trans := List.mem_of_find?_eq_some htr
  have hany : s.trans.any (fun r' => r'.pos == r.pos) = true :=
    List.any_eq_true.mpr ⟨r, hmem, beq_self_eq_true _⟩
  have hmem_f : r.pos ∉ s.comp := by
    simpa using hcomp
  simp [SM.GameState.trivial, hmem_f, hany]

end CryptoGames.LibsignalSM.Proofs.Refinement

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal
  (Encaps1Total spqrV1Send_msg_len_lt spqrV1SessionB_sendCorrectQ)
open CryptoVerification.E2E (partyIdentityKey paramsIdsWithSpqr)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

variable {Pt PQ : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]

/-! ## `fig8ToDFImpl` and `deliverForgeHook` coupling -/

section DeliverForgeStepLemmas

open CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSM.Proofs.Refinement

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_inl_run (ℓ : ℕ) (n : unifSpec.Domain) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inl n)).run sent =
      (liftM (OracleSpec.query (spec := unifSpec +
        DeliverForge.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n)) >>=
        fun u => pure (u, sent)) := by
  simp [fig8ToDFImpl, StateT.run_lift, map_eq_bind_pure_comp]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_transmit_run (ℓ : ℕ) (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ)
    (r : Option (BitVec 256)) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inl (Q, m, r))))))).run sent =
      (DeliverForge.transmitQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q m r >>=
        fun res => pure (res, match res with | some c => c :: sent | none => sent)) := by
  simp only [fig8ToDFImpl, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  congr 1; funext res
  cases res <;> simp [StateT.run_modify]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_chall_run (ℓ : ℕ) (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ)
    (r : Option (BitVec 256)) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))))).run sent =
      (DeliverForge.challQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
        Q m₀ m₁ r >>=
        fun res => pure (res, match res with | some c => c :: sent | none => sent)) := by
  simp only [fig8ToDFImpl, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  congr 1; funext res
  cases res <;> simp [StateT.run_modify]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_deliver_run (ℓ : ℕ) (Q : Party) (c : Fig8C Pt) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inr (Q, c)))))).run sent =
      (DeliverForge.deliverQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c >>=
        fun res => pure (res, sent)) := by
  simp [fig8ToDFImpl, StateT.run_lift, map_eq_bind_pure_comp]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_inject_run (ℓ : ℕ) (Q : Party) (c : Fig8C Pt) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inr (.inl (.inr (Q, c))))).run sent =
      (DeliverForge.injectQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c >>=
        fun res => pure (res, sent)) := by
  simp [fig8ToDFImpl, StateT.run_lift, map_eq_bind_pure_comp]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fig8ToDFImpl_corr_run (ℓ : ℕ) (Q : Party) (sent : List (Fig8C Pt)) :
    (fig8ToDFImpl Pt ℓ (.inr (.inr Q))).run sent =
      (DeliverForge.corrQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q >>=
        fun res => pure (res, sent)) := by
  simp [fig8ToDFImpl, StateT.run_lift, map_eq_bind_pure_comp]

omit [Zero Pt] [SampleableType Pt] in
theorem deliverForgeHook_probe_run (ℓ : ℕ) (Q : Party) (c' : Fig8C Pt)
    (sent : List (Fig8C Pt)) :
    ((deliverForgeHook Pt ℓ).probe Q c').run sent =
      match sent.find? (fun c => sameWireFig8 c c') with
      | some c =>
          DeliverForge.deliverForgeQuery
            (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
            Q c c' >>= fun _ => pure ((), sent)
      | none => pure ((), sent) := by
  simp only [deliverForgeHook, StateT.run_bind, StateT.run_get, pure_bind]
  cases sent.find? (fun c => sameWireFig8 c c') with
  | none => simp [StateT.run_pure]
  | some c => simp [StateT.run_lift, map_eq_bind_pure_comp]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem fullImplDF_inr_inl_of_forgeWin_false
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (sameHdr : C → C → Bool) (cfg : SM.Config Msg)
    (q : (SM.spec St Msg Coins C).Domain)
    (s : DeliverForge.GameStateDF St Msg C) (hfw : s.forgeWin = false) :
    (DeliverForge.fullImplDF sm Δ qep sameHdr cfg (.inr (.inl q))).run s =
      ((SM.oracleImpl sm Δ qep cfg q).run s.base >>=
        fun z => pure (z.1, { s with base := z.2 })) := by
  change (DeliverForge.liftBaseImpl (SM.oracleImpl sm Δ qep cfg) DeliverForge.noneOutBase q).run s =
    _
  unfold DeliverForge.liftBaseImpl
  simp [hfw, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set]

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_inl
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (n : unifSpec.Domain)
    (sent : List (Fig8C Pt))
    (s : DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inl n)).run sent)).run s =
      ((fig8ImplH1 fig qepF (.inl n)).run s.base >>=
        fun z => pure ((z.1, sent), { s with base := z.2 })) := by
  rw [fig8ToDFImpl_inl_run]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  change ((liftM (OracleSpec.query (spec := unifSpec) n) :
      StateT (DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp _).run
        s >>=
    fun z => pure ((z.1, sent), z.2)) =
    ((liftM (OracleSpec.query (spec := unifSpec) n) :
      StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp _).run s.base >>=
    fun z => pure ((z.1, sent), { s with base := z.2 }))
  simp [StateT.run_monadLift]

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_transmit
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (sent : List (Fig8C Pt))
    (s : DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inl (Q, m, r))))))).run sent)).run s =
      ((SM.transmitImpl fig (2 + 1) qepF (Q, m, r)).run s.base >>=
        fun z => pure ((z.1, match z.1 with | some c => c :: sent | none => sent),
          { s with base := z.2 })) := by
  rw [fig8ToDFImpl_transmit_run]
  unfold DeliverForge.transmitQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [fullImplDF_inr_inl_of_forgeWin_false fig (2 + 1) qepF sameHdr SM.Config.h1
    (.inl (.inl (.inl (.inl (Q, m, r))))) s hfw]
  simp only [bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun z => ?_)
  rcases z with ⟨res, b'⟩
  cases res <;> rfl

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_chall
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (r : Option (BitVec 256))
    (sent : List (Fig8C Pt))
    (s : DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))))).run sent)).run s =
      ((SM.challImpl fig (2 + 1) qepF SM.Config.h1 (Q, m₀, m₁, r)).run s.base >>=
        fun z => pure ((z.1, match z.1 with | some c => c :: sent | none => sent),
          { s with base := z.2 })) := by
  rw [fig8ToDFImpl_chall_run]
  unfold DeliverForge.challQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [fullImplDF_inr_inl_of_forgeWin_false fig (2 + 1) qepF sameHdr SM.Config.h1
    (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) s hfw]
  simp only [bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun z => ?_)
  rcases z with ⟨res, b'⟩
  cases res <;> rfl

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_deliver
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (c : Fig8C Pt) (sent : List (Fig8C Pt))
    (s : DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inr (Q, c)))))).run sent)).run s =
      ((SM.deliverImpl fig SM.Config.h1 (Q, c)).run s.base >>=
        fun z => pure ((z.1, sent), { s with base := z.2 })) := by
  rw [fig8ToDFImpl_deliver_run]
  unfold DeliverForge.deliverQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [fullImplDF_inr_inl_of_forgeWin_false fig (2 + 1) qepF sameHdr SM.Config.h1
    (.inl (.inl (.inr (Q, c)))) s hfw]
  simp
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_inject
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (c : Fig8C Pt) (sent : List (Fig8C Pt))
    (s : DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inr (Q, c))))).run sent)).run s =
      ((SM.injectImpl fig (2 + 1) qepF SM.Config.h1 (Q, c)).run s.base >>=
        fun z => pure ((z.1, sent), { s with base := z.2 })) := by
  rw [fig8ToDFImpl_inject_run]
  unfold DeliverForge.injectQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [fullImplDF_inr_inl_of_forgeWin_false fig (2 + 1) qepF sameHdr SM.Config.h1
    (.inl (.inr (Q, c))) s hfw]
  simp
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_corr
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (sent : List (Fig8C Pt))
    (s : DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ (.inr (.inr Q))).run sent)).run s =
      ((SM.corrImpl Q).run s.base >>=
        fun z => pure ((z.1, sent), { s with base := z.2 })) := by
  rw [fig8ToDFImpl_corr_run]
  unfold DeliverForge.corrQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [fullImplDF_inr_inl_of_forgeWin_false fig (2 + 1) qepF sameHdr SM.Config.h1
    (.inr Q) s hfw]
  simp
  rfl

/-- Updates the recorded `sent` ciphertext list after a single Fig. 8 query. -/
def updSentFig8 (Pt : Type) (ℓ : ℕ)
    (q : (unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (res : (unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Range q)
    (sent : List (Fig8C Pt)) : List (Fig8C Pt) :=
  match q, res with
  | .inr (.inl (.inl (.inl (.inl _)))), some c => c :: sent
  | .inr (.inl (.inl (.inl (.inr _)))), some c => c :: sent
  | _, _ => sent

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem mem_updSentFig8_of_mem {ℓ : ℕ}
    (q : (unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (res : (unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Range q)
    {sent : List (Fig8C Pt)} {c₀ : Fig8C Pt} (hmem : c₀ ∈ sent) :
    c₀ ∈ updSentFig8 Pt ℓ q res sent := by
  rcases q with n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
  · exact hmem
  · cases res <;> simp [updSentFig8, hmem]
  · cases res <;> simp [updSentFig8, hmem]
  · exact hmem
  · exact hmem
  · exact hmem

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fullImplDF_fig8ToDFImpl_of_forgeWin_false
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (q : (unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (sent : List (Fig8C Pt))
    (s : DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfw : s.forgeWin = false) :
    (simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
      ((fig8ToDFImpl Pt ℓ q).run sent)).run s =
      ((fig8ImplH1 fig qepF q).run s.base >>=
        fun z => pure ((z.1, updSentFig8 Pt ℓ q z.1 sent), { s with base := z.2 })) := by
  rcases q with n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
  · exact simulateQ_fullImplDF_fig8ToDFImpl_inl fig qepF sameHdr n sent s
  · rw [simulateQ_fullImplDF_fig8ToDFImpl_transmit fig qepF sameHdr Q m r sent s hfw]
    refine congrArg (_ >>= ·) (funext fun z => ?_)
    rcases z with ⟨res, b'⟩
    cases res <;> rfl
  · rw [simulateQ_fullImplDF_fig8ToDFImpl_chall fig qepF sameHdr Q m₀ m₁ r sent s hfw]
    refine congrArg (_ >>= ·) (funext fun z => ?_)
    rcases z with ⟨res, b'⟩
    cases res <;> rfl
  · exact simulateQ_fullImplDF_fig8ToDFImpl_deliver fig qepF sameHdr Q c sent s hfw
  · exact simulateQ_fullImplDF_fig8ToDFImpl_inject fig qepF sameHdr Q c sent s hfw
  · exact simulateQ_fullImplDF_fig8ToDFImpl_corr fig qepF sameHdr Q sent s hfw

omit [Zero Pt] [SampleableType Pt] in
/-- While `s.forgeWin = false`, `deliverForgeHook.lift` couples with `fig8ImplH1` on `s.base`. -/
theorem deliverForgeHook_lift_bind_base_eq_of_forgeWin_false
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    {α : Type} (x : Fig8Comp Pt ℓ α) :
    ∀ (sent : List (Fig8C Pt))
      (s : DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      s.forgeWin = false →
      ((simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
          (((deliverForgeHook Pt ℓ).lift x).run sent)).run s >>=
        fun z => pure (z.1.1, z.2.base)) =
        (simulateQ (fig8ImplH1 fig qepF) x).run s.base := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro sent s _
    simp [deliverForgeHook]
  | query_bind q r ih =>
    intro sent s hfw
    change ((simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
        (((fig8ToDFImpl Pt ℓ q).run sent) >>=
          fun p => ((deliverForgeHook Pt ℓ).lift (r p.1)).run p.2)).run s >>=
        fun z => pure (z.1.1, z.2.base)) = _
    rw [simulateQ_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]
    rw [simulateQ_fullImplDF_fig8ToDFImpl_of_forgeWin_false fig qepF sameHdr q sent s hfw]
    simp only [bind_assoc, pure_bind]
    refine congrArg (_ >>= ·) (funext fun z => ?_)
    exact ih z.1 (updSentFig8 Pt ℓ q z.1 sent) { s with base := z.2 } hfw

omit [Zero Pt] [SampleableType Pt] in
theorem inTransit_ct_mem_updSentFig8
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ)
    (q : (unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Domain)
    (sent : List (Fig8C Pt))
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hsent : ∀ r ∈ s.trans, r.ct ∈ sent)
    (z : (unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)).Range q ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hz : z ∈ support ((fig8ImplH1 fig qepF q).run s)) :
    ∀ r ∈ z.2.trans, r.ct ∈ updSentFig8 Pt ℓ q z.1 sent := by
  have hep_trans : ∀ Q bad s₁,
      s.epMgmt (2 + 1) qepF Q bad = some s₁ → s₁.trans = s.trans := by
    intro Q bad s₁ hep
    unfold SM.GameState.epMgmt SM.GameState.leak at hep
    by_cases hs : Q.sendsIn (s.epoch Q + 1) = true
    · by_cases hq : qepF < s.epoch Q + 1
      · simp [hs, hq] at hep
      · cases bad <;> cases hsc : s.safeCh (2 + 1) Q <;>
          simp [hs, hq, hsc] at hep <;>
          (subst hep; rfl)
    · by_cases hq : qepF < s.epoch Q <;> simp [hs, hq] at hep
      subst hep; rfl
  rcases q with n | ((((⟨Q, m, ro⟩ | ⟨Q, m₀, m₁, ro⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
  · change z ∈ support ((liftM (OracleSpec.query (spec := unifSpec) n) :
        StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp _).run s) at hz
    simp only [StateT.run_monadLift, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact hsent
  · change z ∈ support ((SM.transmitImpl fig (2 + 1) qepF (Q, m, ro)).run s) at hz
    unfold SM.transmitImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hsent
    · simp only [StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hep : s.epMgmt (2 + 1) qepF Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hsent
      | some s₁ =>
        simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz
        intro r hr
        simp only [SM.GameState.record, List.mem_cons] at hr
        rcases hr with rfl | hr
        · simp [updSentFig8]
        · rw [hep_trans Q cb.2 s₁ hep] at hr
          exact List.mem_cons_of_mem _ (hsent r hr)
  · change z ∈ support ((SM.challImpl fig (2 + 1) qepF SM.Config.h1 (Q, m₀, m₁, ro)).run s) at hz
    unfold SM.challImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hsent
    · simp only [StateT.run_bind, StateT.run_monadLift, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hep : s.epMgmt (2 + 1) qepF Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hsent
      | some s₁ =>
        simp only [hep] at hz
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hsent
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz
          intro r hr
          simp only [SM.GameState.record, List.mem_cons] at hr
          rcases hr with rfl | hr
          · simp [updSentFig8]
          · rw [hep_trans Q cb.2 s₁ hep] at hr
            exact List.mem_cons_of_mem _ (hsent r hr)
  · change z ∈ support ((SM.deliverImpl fig SM.Config.h1 (Q, c)).run s) at hz
    unfold SM.deliverImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hsent
    · cases hin : s.inTransit Q.other c with
      | none =>
        simp only [hin, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hsent
      | some r₀ =>
        simp only [hin] at hz
        cases hrec : fig.receive (s.st Q) c with
        | none =>
          simp only [hrec] at hz
          split at hz <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz <;>
            (subst hz; exact hsent)
        | some res' =>
          rcases res' with ⟨st', t', i', m'⟩
          simp only [hrec] at hz
          split at hz <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz <;>
            (subst hz; intro r hr; exact hsent r (List.mem_of_mem_filter hr))
  · change z ∈ support ((SM.injectImpl fig (2 + 1) qepF SM.Config.h1 (Q, c)).run s) at hz
    unfold SM.injectImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hsent
    · cases hrec : fig.receive (s.st Q) c with
      | none =>
        simp only [hrec, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hsent
      | some res' =>
        rcases res' with ⟨st', t', i', m'⟩
        simp only [hrec] at hz
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hsent
        · split at hz
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz
            subst hz; intro r hr; exact hsent r (List.mem_of_mem_filter hr)
          · split at hz <;>
              simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hz <;>
              (subst hz; exact hsent)
  · change z ∈ support ((SM.corrImpl Q).run s) at hz
    unfold SM.corrImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz <;>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz <;>
      (subst hz; exact hsent)

omit [Zero Pt] [SampleableType Pt] in
theorem deliverForgeHook_lift_support_invariants
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    {α : Type} (x : Fig8Comp Pt ℓ α) :
    ∀ (sent : List (Fig8C Pt))
      (s : DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (z : (α × List (Fig8C Pt)) ×
        DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      s.forgeWin = false →
      z ∈ support
        ((simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
          (((deliverForgeHook Pt ℓ).lift x).run sent)).run s) →
      z.2.forgeWin = false ∧
      (z.1.1, z.2.base) ∈ support ((simulateQ (fig8ImplH1 fig qepF) x).run s.base) ∧
      (∀ c ∈ sent, c ∈ z.1.2) ∧
      ((∀ r ∈ s.base.trans, r.ct ∈ sent) → ∀ r ∈ z.2.base.trans, r.ct ∈ z.1.2) := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro sent s z hfw hz
    simp only [deliverForgeHook, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz ⊢
    subst hz
    exact ⟨hfw, rfl, fun _ hc => hc, fun htr => htr⟩
  | query_bind q r ih =>
    intro sent s z hfw hz
    change z ∈ support
      ((simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
        (((fig8ToDFImpl Pt ℓ q).run sent) >>=
          fun p => ((deliverForgeHook Pt ℓ).lift (r p.1)).run p.2)).run s) at hz
    rw [simulateQ_bind, StateT.run_bind,
      simulateQ_fullImplDF_fig8ToDFImpl_of_forgeWin_false fig qepF sameHdr q sent s hfw] at hz
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨z₀, hz₀, hz_cont⟩
    rcases ih z₀.1 (updSentFig8 Pt ℓ q z₀.1 sent) { s with base := z₀.2 } z hfw hz_cont with
      ⟨hfw', hsup', hsent', htr'⟩
    refine ⟨hfw', ?_, fun c hc => hsent' c (mem_updSentFig8_of_mem q z₀.1 hc),
      fun htr => htr' (inTransit_ct_mem_updSentFig8 fig qepF q sent s.base htr z₀ hz₀)⟩
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind]
    exact ⟨z₀, hz₀, hsup'⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem bind_eq_of_support_imp {α β γ : Type} (m : ProbComp α) (P : α → Prop)
    (proj : α → β) (f : α → ProbComp γ) (g : β → ProbComp γ)
    (hP : ∀ a ∈ support m, P a)
    (hfg : ∀ a, P a → f a = g (proj a)) :
    (m >>= f) = ((m >>= fun a => pure (proj a)) >>= g) := by
  induction m using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact hfg a (hP a (by simp))
  | query_bind t r ih =>
    simp only [bind_assoc]
    refine congrArg (_ >>= ·) (funext fun u => ?_)
    rw [ih u (fun a ha => hP a (by
      rw [MonadAttach.mem_support_bind]
      exact ⟨u, by simp, ha⟩))]
    simp only [bind_assoc]

/-- Coupling relation between `probeHook` and `deliverForgeHook` when no probe fires. -/
def df_noProbe_rel {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α)
    (mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α) :
    Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (s : DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
    s.forgeWin = false →
    ((simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
        ((mDF.run sC).run sent)).run s >>=
      fun z => pure (z.1.1, (z.2.base, false))) =
      ((mPr.run sC).run (s.base, false)) ∧
    ∀ z ∈ support
      ((simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
        ((mDF.run sC).run sent)).run s),
      z.2.forgeWin = false ∧
      (∀ c ∈ sent, c ∈ z.1.2) ∧
      ((∀ r ∈ s.base.trans, r.ct ∈ sent) → ∀ r ∈ z.2.base.trans, r.ct ∈ z.1.2)

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_pure {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (a : α) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr (pure a) (pure a) := by
  intro sC sent s hfw
  refine ⟨by simp, fun z hz => ?_⟩
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hfw, fun _ hc => hc, fun htr => htr⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_bind {PQ α β : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ} {sameHdr : Fig8C Pt → Fig8C Pt → Bool}
    {mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α}
    {kPr : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    {kDF : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) β}
    (hm : df_noProbe_rel fig qepF sameHdr mPr mDF)
    (hk : ∀ a, df_noProbe_rel fig qepF sameHdr (kPr a) (kDF a)) :
    df_noProbe_rel fig qepF sameHdr (mPr >>= kPr) (mDF >>= kDF) := by
  intro sC sent s hfw
  refine ⟨?_, ?_⟩
  · simp only [StateT.run_bind, simulateQ_bind, bind_assoc]
    rw [← (hm sC sent s hfw).1]
    exact bind_eq_of_support_imp
      ((simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
        ((mDF.run sC).run sent)).run s)
      (fun z => z.2.forgeWin = false)
      (fun z => (z.1.1, (z.2.base, false)))
      (fun z => (simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
        (((kDF z.1.1.1).run z.1.1.2).run z.1.2)).run z.2 >>=
          fun z' => pure (z'.1.1, (z'.2.base, false)))
      (fun r => ((kPr r.1.1).run r.1.2).run r.2)
      (fun z hz => ((hm sC sent s hfw).2 z hz).1)
      (fun z hfw' => (hk z.1.1.1 z.1.1.2 z.1.2 z.2 hfw').1)
  · intro z hz
    simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨z₀, hz₀, hz₁⟩
    rcases (hm sC sent s hfw).2 z₀ hz₀ with ⟨hfw₀, hsent₀, htr₀⟩
    rcases (hk z₀.1.1.1 z₀.1.1.2 z₀.1.2 z₀.2 hfw₀).2 z hz₁ with ⟨hfw₁, hsent₁, htr₁⟩
    exact ⟨hfw₁, fun c hc => hsent₁ c (hsent₀ c hc), fun htr => htr₁ (htr₀ htr)⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_get (PQ : Type)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr
      (get : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (LibsignalToModularSchemeSimState PQ Pt ℓ))
      (get : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) (LibsignalToModularSchemeSimState PQ Pt ℓ)) := by
  intro sC sent s hfw
  refine ⟨by simp, fun z hz => ?_⟩
  simp only [StateT.run_get, StateT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hfw, fun _ hc => hc, fun htr => htr⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_set {PQ : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr
      (set sC' : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) PUnit)
      (set sC' : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) PUnit) := by
  intro sC sent s hfw
  refine ⟨by simp, fun z hz => ?_⟩
  simp only [StateT.run_set, StateT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hfw, fun _ hc => hc, fun htr => htr⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_modify {PQ : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr
      (modify f : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) PUnit)
      (modify f : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) PUnit) := by
  intro sC sent s hfw
  refine ⟨by simp, fun z hz => ?_⟩
  simp only [StateT.run_modify, StateT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hfw, fun _ hc => hc, fun htr => htr⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_ite {PQ α : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ} {sameHdr : Fig8C Pt → Fig8C Pt → Bool} {P_cond : Prop} [Decidable P_cond]
    {tPr ePr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {tDF eDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α}
    (ht : df_noProbe_rel fig qepF sameHdr tPr tDF)
    (he : df_noProbe_rel fig qepF sameHdr ePr eDF) :
    df_noProbe_rel fig qepF sameHdr
      (if P_cond then tPr else ePr) (if P_cond then tDF else eDF) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift x).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) x).run gh.1 >>= fun p => pure (p.1, (p.2, gh.2))) :=
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem zoomB_probeHook_run {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((runOnBaseState (probeHook fig qepF) x).run sC).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) (x.run sC.base)).run gh.1 >>= fun r =>
        pure ((r.1.1, { sC with base := r.1.2 }), (r.2, gh.2))) := by
  change (((probeHook fig qepF).lift (x.run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh = _
  rw [StateT.run_bind, probeHook_lift_run]
  simp only [bind_assoc, pure_bind, StateT.run_pure]

omit [Zero Pt] [SampleableType Pt] in
theorem zoomB_deliverForgeHook_run {PQ α : Type}
    (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt)) :
    ((runOnBaseState (deliverForgeHook Pt ℓ) x).run sC).run sent =
      (((deliverForgeHook Pt ℓ).lift (x.run sC.base)).run sent >>= fun p =>
        pure ((p.1.1, { sC with base := p.1.2 }), p.2)) :=
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_zoomB {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr
      (runOnBaseState (probeHook fig qepF) x)
      (runOnBaseState (deliverForgeHook Pt ℓ) x) := by
  intro sC sent s hfw
  refine ⟨?_, ?_⟩
  · rw [zoomB_deliverForgeHook_run, zoomB_probeHook_run, simulateQ_bind, StateT.run_bind]
    simp only [simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    rw [← deliverForgeHook_lift_bind_base_eq_of_forgeWin_false fig qepF sameHdr (x.run sC.base)
      sent s hfw]
    simp only [bind_assoc, pure_bind]
  · intro z hz
    rw [zoomB_deliverForgeHook_run, simulateQ_bind, StateT.run_bind] at hz
    simp only [simulateQ_pure, StateT.run_pure, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨z₀, hz₀, rfl⟩
    rcases deliverForgeHook_lift_support_invariants fig qepF sameHdr (x.run sC.base) sent s z₀
      hfw hz₀ with ⟨hfw', _, hsent', htr'⟩
    exact ⟨hfw', hsent', htr'⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_liftC {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (x : Fig8Comp Pt ℓ α) :
    df_noProbe_rel (PQ := PQ) fig qepF sameHdr
      (LibsignalSimC.liftC (probeHook fig qepF) x)
      (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) x) := by
  intro sC sent s hfw
  unfold LibsignalSimC.liftC
  refine ⟨?_, ?_⟩
  · simp only [StateT.run_lift, probeHook_lift_run, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    rw [← deliverForgeHook_lift_bind_base_eq_of_forgeWin_false fig qepF sameHdr x sent s hfw]
    simp only [bind_assoc, pure_bind]
  · intro z hz
    simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨z₀, hz₀, rfl⟩
    rcases deliverForgeHook_lift_support_invariants fig qepF sameHdr x sent s z₀ hfw hz₀ with
      ⟨hfw', _, hsent', htr'⟩
    exact ⟨hfw', hsent', htr'⟩

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_guardC {PQ α : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ} {sameHdr : Fig8C Pt → Fig8C Pt → Bool}
    {mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    {mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) (Option α)}
    (hm : df_noProbe_rel fig qepF sameHdr mPr mDF) :
    df_noProbe_rel fig qepF sameHdr (LibsignalSimC.guardC mPr) (LibsignalSimC.guardC mDF) := by
  unfold LibsignalSimC.guardC
  refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC => ?_
  exact df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr none) hm

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_simSendC {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    df_noProbe_rel fig qepF sameHdr
      (LibsignalSimC.simSendC P qep fig (probeHook fig qepF) Q m₀ chal r)
      (LibsignalSimC.simSendC P qep fig (deliverForgeHook Pt ℓ) Q m₀ chal r) := by
  unfold LibsignalSimC.simSendC
  refine df_noProbe_rel_bind (df_noProbe_rel_zoomB (PQ := PQ) fig qepF sameHdr _) fun res => ?_
  cases res with
  | none => exact df_noProbe_rel_pure fig qepF sameHdr none
  | some w =>
    refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC => ?_
    exact df_noProbe_rel_bind (df_noProbe_rel_set fig qepF sameHdr _) fun _ =>
      df_noProbe_rel_pure fig qepF sameHdr (some w)

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_fwdAnswerC {PQ : Type} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    df_noProbe_rel fig qepF sameHdr
      (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c')
      (fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine df_noProbe_rel_bind (df_noProbe_rel_zoomB (PQ := PQ) fig qepF sameHdr _) fun res => ?_
  cases res with
  | none => exact df_noProbe_rel_zoomB (PQ := PQ) fig qepF sameHdr _
  | some r =>
    cases r with
    | accepted _ _ _ =>
      exact df_noProbe_rel_bind (df_noProbe_rel_modify fig qepF sameHdr _) fun _ =>
        df_noProbe_rel_zoomB (PQ := PQ) fig qepF sameHdr _
    | _ => exact df_noProbe_rel_zoomB (PQ := PQ) fig qepF sameHdr _

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_simCorrC {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    df_noProbe_rel fig qepF sameHdr
      (LibsignalSimC.simCorrC P encT (probeHook fig qepF) Dh Q)
      (LibsignalSimC.simCorrC P encT (deliverForgeHook Pt ℓ) Dh Q) := by
  unfold LibsignalSimC.simCorrC
  refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC => ?_
  refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
  refine df_noProbe_rel_bind (df_noProbe_rel_liftC fig qepF sameHdr _) fun res => ?_
  cases res with
  | none => exact df_noProbe_rel_pure fig qepF sameHdr _
  | some st =>
    exact df_noProbe_rel_bind (df_noProbe_rel_set fig qepF sameHdr _) fun _ =>
      df_noProbe_rel_pure fig qepF sameHdr _

omit [SampleableType Pt] in
theorem df_noProbe_rel_simRecvC_inject {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (Q : Party) (w : List (BitVec 8)) :
    df_noProbe_rel fig qepF sameHdr
      (LibsignalSimC.simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w false)
      (LibsignalSimC.simRecvC P encT decT qep fig fs (deliverForgeHook Pt ℓ) Q w false) := by
  unfold LibsignalSimC.simRecvC
  generalize (2 ^ 32 : ℕ) = maxI
  generalize (25000 : ℕ) = maxSkip
  refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC => ?_
  dsimp only
  refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
  refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
  refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
  refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact df_noProbe_rel_pure fig qepF sameHdr _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
    refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
    cases P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact df_noProbe_rel_pure fig qepF sameHdr _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
        unfold LibsignalSimC.fwdC
        refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC' => ?_
        cases (List.find? (fun wc => (wc.1 == w) && (Party.senderOf wc.2.1.1 == Q.other))
            sC.base.honest).map Prod.snd with
        | none =>
          exact df_noProbe_rel_fwdAnswerC qep fig fs qepF sameHdr Q w false (some ci)
            h.senderRatchetKey pq' _
        | some c =>
          simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact df_noProbe_rel_fwdAnswerC qep fig fs qepF sameHdr Q w false (some ci)
            h.senderRatchetKey pq' _
      | none =>
        dsimp only
        refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
        refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
        refine df_noProbe_rel_ite
          (df_noProbe_rel_bind (df_noProbe_rel_modify fig qepF sameHdr _) fun _ => ?_) ?_ <;>
        · refine df_noProbe_rel_ite (df_noProbe_rel_pure fig qepF sameHdr _) ?_
          cases decT h.senderRatchetKey with
          | none => exact df_noProbe_rel_pure fig qepF sameHdr _
          | some T =>
            refine df_noProbe_rel_ite ?_ ?_
            · unfold fwdEvictC
              refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC' => ?_
              simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              exact df_noProbe_rel_fwdAnswerC qep fig fs qepF sameHdr Q w false none
                h.senderRatchetKey pq' _
            · unfold LibsignalSimC.fwdC
              refine df_noProbe_rel_bind (df_noProbe_rel_get PQ fig qepF sameHdr) fun sC' => ?_
              cases (List.find? (fun wc => (wc.1 == w) && (Party.senderOf wc.2.1.1 == Q.other))
                  sC.base.honest).map Prod.snd with
              | none =>
                exact df_noProbe_rel_fwdAnswerC qep fig fs qepF sameHdr Q w false none
                  h.senderRatchetKey pq' _
              | some c =>
                simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                exact df_noProbe_rel_fwdAnswerC qep fig fs qepF sameHdr Q w false none
                  h.senderRatchetKey pq' _

def df_noProbe_rel_at {PQ α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (sameHdr : Fig8C Pt → Fig8C Pt → Bool)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α)
    (mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α) :
    Prop :=
  ∀ (sent : List (Fig8C Pt))
    (s : DeliverForge.GameStateDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
    s.forgeWin = false →
    ((simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
        ((mDF.run sC).run sent)).run s >>=
      fun z => pure (z.1.1, (z.2.base, false))) =
      ((mPr.run sC).run (s.base, false)) ∧
    ∀ z ∈ support
      ((simulateQ (DeliverForge.fullImplDF fig (2 + 1) qepF sameHdr SM.Config.h1)
        ((mDF.run sC).run sent)).run s),
      z.2.forgeWin = false ∧
      (∀ c ∈ sent, c ∈ z.1.2) ∧
      ((∀ r ∈ s.base.trans, r.ct ∈ sent) → ∀ r ∈ z.2.base.trans, r.ct ∈ z.1.2)

end DeliverForgeStepLemmas

section KemFailSimCoupling

open CryptoGames.LibsignalSM.Proofs.Refinement

omit [Zero Pt] [SampleableType Pt] in
theorem simulateQ_fig8ImplH1_liftM_probComp {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (m : ProbComp α)
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fig8ImplH1 fig qepF) (liftM m : Fig8Comp Pt ℓ α)).run s =
      (m >>= fun a => pure (a, s)) := by
  induction m using OracleComp.inductionOn with
  | pure a =>
    simp
  | query_bind n r ih =>
    change (simulateQ (fig8ImplH1 fig qepF)
      ((liftM (OracleSpec.query (spec := unifSpec) n) : Fig8Comp Pt ℓ _) >>=
        fun u => (liftM (r u) : Fig8Comp Pt ℓ α))).run s = _
    rw [simulateQ_bind, StateT.run_bind]
    change (((liftM (OracleSpec.query (spec := unifSpec) n) :
        StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp _).run s) >>=
      fun z => (simulateQ (fig8ImplH1 fig qepF) (liftM (r z.1) : Fig8Comp Pt ℓ α)).run z.2) = _
    simp only [StateT.run_monadLift, bind_assoc, pure_bind]
    refine congrArg (_ >>= ·) (funext fun u => ?_)
    exact ih u

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem kemCandValid_of_cand_eq {F : ShaCompress} {K : MlKem}
    {tr tr' : KemFailTrackState F} (h : tr'.cand = tr.cand) (hv : KemCandValid K tr) :
    KemCandValid K tr' := by
  intro p hp
  exact hv p (h ▸ hp)

omit [DecidableEq Pt] [SampleableType Pt] in
theorem runProbeStep_run {PQ PQC α : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (step : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) :
    (runProbeStep P ℓ Dh encPt encT decT idOf lam qep step).run (sC, gh, tr) =
      (((step.run sC).run gh) >>= fun z => pure (z.1.1, (z.1.2, z.2, tr))) :=
  rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem stateT_run_get_bind_prod3 {α β γ δ : Type}
    (f : α × β × γ → StateT (α × β × γ) ProbComp δ) (a : α) (b : β) (c : γ) :
    ((get >>= f).run (a, b, c)) = (f (a, b, c)).run (a, b, c) :=
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_pure_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (a : α)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift (pure a)).run gh = pure (a, gh) := by
  cases gh; rfl

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_bind_run {α β : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) (y : α → Fig8Comp Pt ℓ β)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift (x >>= y)).run gh =
      (((probeHook fig qepF).lift x).run gh >>=
        fun z => ((probeHook fig qepF).lift (y z.1)).run z.2) := by
  change ((simulateQ (fig8ImplH1 fig qepF) (x >>= y)).run gh.1 >>=
    fun z => pure (z.1, (z.2, gh.2))) =
    (((simulateQ (fig8ImplH1 fig qepF) x).run gh.1 >>= fun z => pure (z.1, (z.2, gh.2))) >>=
      fun z => (simulateQ (fig8ImplH1 fig qepF) (y z.1)).run z.2.1 >>=
        fun w => pure (w.1, (w.2, z.2.2)))
  rw [simulateQ_bind, StateT.run_bind, bind_assoc, bind_assoc]
  refine congrArg (_ >>= ·) (funext fun z => ?_)
  simp

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_liftM_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (m : ProbComp α)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift (liftM m : Fig8Comp Pt ℓ α)).run gh =
      (m >>= fun a => pure (a, gh)) := by
  change ((simulateQ (fig8ImplH1 fig qepF) (liftM m : Fig8Comp Pt ℓ α)).run gh.1 >>=
    fun z => pure (z.1, (z.2, gh.2))) = _
  rw [simulateQ_fig8ImplH1_liftM_probComp, bind_assoc]
  refine congrArg (m >>= ·) (funext fun a => ?_)
  cases gh; rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem zoomB_bind_run {PQ α β : Type}
    (H : Hook Pt ℓ (ProbeM Pt ℓ))
    (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    (((LibsignalSimC.runOnBaseState H x >>= f).run sC).run gh) =
      (((H.lift (x.run sC.base)).run gh) >>=
        fun z => ((f z.1.1).run { sC with base := z.1.2 }).run z.2) := by
  rw [StateT.run_bind]
  change ((H.lift (x.run sC.base) >>= fun z => pure (z.1, { sC with base := z.2 })).run gh >>=
    fun p => ((f p.1.1).run p.1.2).run p.2) = _
  rw [StateT.run_bind, bind_assoc]
  refine congrArg (_ >>= ·) (funext fun z => ?_)
  simp

omit [SampleableType Pt] in
theorem kemFailSendStep_cand_valid {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (z : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run
      (sC, gh, tr))) :
    (KemCandValid K tr → KemCandValid K z.2.2.2) ∧
    (∀ p, tr.cand = some p → z.2.2.2.cand = some p) := by
  unfold kemFailSendStep at hz
  rw [stateT_run_get_bind_prod3] at hz
  split at hz
  rcases Prod.mk.injEq _ _ _ _ |>.mp ‹(sC, gh, tr) = _› with ⟨rfl, hgh_tr⟩
  rcases Prod.mk.injEq _ _ _ _ |>.mp hgh_tr with ⟨rfl, rfl⟩
  split at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨id, fun _ hp => hp⟩
  · cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨id, fun _ hp => hp⟩
    | some s₁ =>
      simp only [hep] at hz
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨id, fun _ hp => hp⟩
      · cases r with
        | none =>
          rw [StateT.run_bind, MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨⟨rq, s_rq⟩, _, hz⟩
          rw [StateT.run_bind, StateT.run_pure, pure_bind] at hz
          cases hmk : mkPub P sC.base Q rq
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
               else sC.base.pn Q) with
          | none =>
            simp only [hmk, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨fun hv => kemCandValid_of_cand_eq rfl
                (stepKemFailSend_cand_valid P.C.F K tr Q rq hv),
              fun p hp => stepKemFailSend_cand_some_of_some P.C.F K tr Q rq p hp⟩
          | some pq_pub =>
            rcases pq_pub with ⟨pq', pub⟩
            simp only [hmk] at hz
            rw [StateT.run_bind, StateT.run_monadLift, MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨⟨⟨res, gh'⟩, s_lift⟩, _, hz⟩
            cases res <;>
              simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hz <;>
              subst hz
            · exact ⟨fun hv => kemCandValid_of_cand_eq rfl
                  (stepKemFailSend_cand_valid P.C.F K tr Q rq hv),
                fun p hp => stepKemFailSend_cand_some_of_some P.C.F K tr Q rq p hp⟩
            · exact ⟨stepKemFailSend_cand_valid P.C.F K tr Q rq,
                stepKemFailSend_cand_some_of_some P.C.F K tr Q rq⟩
        | some rq =>
          rw [StateT.run_bind, StateT.run_pure, pure_bind,
            StateT.run_bind, MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨⟨rc, s_rc⟩, _, hz⟩
          cases hmk : mkPub P sC.base Q rq
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
               else sC.base.pn Q) with
          | none =>
            simp only [hmk, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨fun hv => kemCandValid_of_cand_eq rfl
                (stepKemFailSend_cand_valid P.C.F K tr Q rq hv),
              fun p hp => stepKemFailSend_cand_some_of_some P.C.F K tr Q rq p hp⟩
          | some pq_pub =>
            rcases pq_pub with ⟨pq', pub⟩
            simp only [hmk] at hz
            rw [StateT.run_bind, StateT.run_monadLift, MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨⟨⟨res, gh'⟩, s_lift⟩, _, hz⟩
            cases res <;>
              simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hz <;>
              subst hz
            · exact ⟨fun hv => kemCandValid_of_cand_eq rfl
                  (stepKemFailSend_cand_valid P.C.F K tr Q rq hv),
                fun p hp => stepKemFailSend_cand_some_of_some P.C.F K tr Q rq p hp⟩
            · exact ⟨stepKemFailSend_cand_valid P.C.F K tr Q rq,
                stepKemFailSend_cand_some_of_some P.C.F K tr Q rq⟩

omit [SampleableType Pt] in
theorem kemFailSimImpl_cand_valid {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run
      (sC, gh, tr))) :
    (KemCandValid K tr → KemCandValid K z.2.2.2) ∧
    (∀ p, tr.cand = some p → z.2.2.2.cand = some p) := by
  rcases q_sm with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · change z ∈ support ((StateT.lift (OracleSpec.query (spec := unifSpec) n) :
        KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr)) at hz
    simp only [StateT.run_lift, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact ⟨id, fun _ hp => hp⟩
  · exact kemFailSendStep_cand_valid P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r sC gh tr z hz
  · exact kemFailSendStep_cand_valid P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r sC gh
      tr z hz
  · change z ∈ support ((do
        let ⟨sC, _, _⟩ ← get
        let revHonest := sC.base.honest.reverse
        let j? := revHonest.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
        let res ← runProbeStep P ℓ Dh encPt encT decT idOf lam qep
          (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (lFS P.C P.codec ℓ encT idOf 25000)
            (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w true))
        match res, j? with
        | some (.accepted _ _ _), some j =>
          modify fun ⟨sC', gh', tr⟩ => (sC', gh', stepKemFailDeliver P.C.F K tr Q j)
        | _, _ => pure ()
        return res : KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr)) at hz
    rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, runProbeStep_run,
      MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨_, hz₀, hz⟩
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz₀
    rcases hz₀ with ⟨⟨⟨res, sC'⟩, gh'⟩, _, rfl⟩
    rcases res with _ | r_acc
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨id, fun _ hp => hp⟩
    · cases r_acc with
      | rejected =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨id, fun _ hp => hp⟩
      | accepted t i pm =>
        cases hfind : List.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
            sC.base.honest.reverse with
        | none =>
          simp only [hfind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨id, fun _ hp => hp⟩
        | some j =>
          simp only [hfind, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨stepKemFailDeliver_cand_valid P.C.F K tr Q j,
            fun p hp => by rw [stepKemFailDeliver_cand_eq, hp]⟩
  · change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep _).run (sC, gh, tr)) at hz
    rw [runProbeStep_run] at hz
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact ⟨id, fun _ hp => hp⟩
  · change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep _).run (sC, gh, tr)) at hz
    rw [runProbeStep_run] at hz
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact ⟨id, fun _ hp => hp⟩

omit [SampleableType Pt] in
theorem simulateQ_kemFailSimImpl_cand_valid {PQ α : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
      α) :
    ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
      (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
      (tr : KemFailTrackState P.C.F)
      (z : α × (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F)),
      z ∈ support ((simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) oa).run
        (sC, gh, tr)) →
      (KemCandValid K tr → KemCandValid K z.2.2.2) ∧
      (∀ p, tr.cand = some p → z.2.2.2.cand = some p) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sC gh tr z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨id, fun _ hp => hp⟩
  | query_bind q_sm r ih =>
    intro sC gh tr z hz
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, sC₁, gh₁, tr₁⟩, h₁, h₂⟩
    rcases kemFailSimImpl_cand_valid P K ℓ Dh encPt encT decT idOf lam qep q_sm sC gh tr
      (u, sC₁, gh₁, tr₁) h₁ with ⟨hv₁, hs₁⟩
    rcases ih u sC₁ gh₁ tr₁ z h₂ with ⟨hv₂, hs₂⟩
    exact ⟨fun hv => hv₂ (hv₁ hv), fun p hp => hs₂ p (hs₁ p hp)⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem probComp_bind_congr {α β : Type} (m : ProbComp α) {f g : α → ProbComp β}
    (h : ∀ a, f a = g a) : (m >>= f) = (m >>= g) :=
  congrArg (m >>= ·) (funext h)

omit [SampleableType Pt] in
theorem kemFailSendStep_proj_eq_simSendC {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) :
    ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run (sC, gh, tr) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) =
    (((LibsignalSimC.guardC (LibsignalSimC.simSendC P qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
        Q m₀ chal r)).run sC).run gh) := by
  unfold kemFailSendStep
  rw [stateT_run_get_bind_prod3]
  split
  rcases Prod.mk.injEq _ _ _ _ |>.mp ‹(sC, gh, tr) = _› with ⟨rfl, hgh_tr⟩
  rcases Prod.mk.injEq _ _ _ _ |>.mp hgh_tr with ⟨rfl, rfl⟩
  unfold LibsignalSimC.guardC LibsignalSimC.simSendC
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  cases hstop : sC.base.stopped
  · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rw [zoomB_bind_run]
    unfold LibsignalSim.simSend
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    cases hwin : (sC.base.mir.win || !noBobSendInEpoch0 sC.base.mir Q)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
      | none =>
        simp only [StateT.run_pure, probeHook_lift_pure_run, pure_bind]
      | some s₁ =>
        cases hchal : (chal.isSome && !s₁.safeCh 3 Q)
        · simp only [hchal, Bool.false_eq_true, ↓reduceIte]
          cases r with
          | none =>
            rw [StateT.run_bind, StateT.run_monadLift,
              StateT.run_bind, probeHook_lift_bind_run]
            unfold LibsignalSim.coin LibsignalSim.liftQ
            rw [StateT.run_lift, probeHook_lift_bind_run, probeHook_lift_liftM_run]
            simp only [MonadLiftT.monadLift, probeHook_lift_pure_run, bind_assoc, pure_bind]
            generalize ($ᵗ BitVec 512 : ProbComp (BitVec 512)) = m512
            apply probComp_bind_congr
            intro rq
            generalize mkPub P sC.base Q rq _ = mkRes
            rcases mkRes with _ | ⟨pq', pub⟩
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
                probeHook_lift_pure_run, pure_bind]
            · cases chal <;>
              · rw [StateT.run_bind, StateT.run_monadLift,
                  StateT.run_bind, StateT.run_lift,
                  probeHook_lift_bind_run, probeHook_lift_bind_run]
                simp only [MonadLiftT.monadLift,
                  probeHook_lift_pure_run, bind_assoc, pure_bind]
                apply probComp_bind_congr
                intro ⟨res, gh'⟩
                cases res
                · simp [probeHook_lift_pure_run, StateT.run_set]
                · simp only [probeHook_lift_pure_run, LibsignalSim.putS, StateT.run_bind,
                    StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
                  cases (sC.kept Q).full <;> rfl
          | some rq =>
            rw [StateT.run_bind, StateT.run_pure, pure_bind,
              StateT.run_bind, StateT.run_map, StateT.run_monadLift,
              StateT.run_bind, StateT.run_pure, pure_bind,
              StateT.run_bind, StateT.run_map]
            unfold LibsignalSim.coin LibsignalSim.liftQ
            rw [StateT.run_lift, probeHook_lift_bind_run]
            simp only [MonadLiftT.monadLift, map_eq_bind_pure_comp,
              Function.comp_apply, bind_assoc, pure_bind]
            rw [probeHook_lift_bind_run, probeHook_lift_liftM_run, bind_assoc]
            simp only [probeHook_lift_pure_run, bind_assoc, pure_bind]
            generalize ($ᵗ BitVec 256 : ProbComp (BitVec 256)) = m256
            apply probComp_bind_congr
            intro rc
            generalize mkPub P sC.base Q rq _ = mkRes
            rcases mkRes with _ | ⟨pq', pub⟩
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
                probeHook_lift_pure_run, pure_bind]
            · cases chal <;>
              · rw [StateT.run_bind, StateT.run_monadLift,
                  StateT.run_bind, StateT.run_lift,
                  probeHook_lift_bind_run, probeHook_lift_bind_run]
                simp only [MonadLiftT.monadLift,
                  probeHook_lift_pure_run, bind_assoc, pure_bind]
                apply probComp_bind_congr
                intro ⟨res, gh'⟩
                cases res
                · simp [probeHook_lift_pure_run, StateT.run_set]
                · simp only [probeHook_lift_pure_run, LibsignalSim.putS, StateT.run_bind,
                    StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
                  cases (sC.kept Q).full <;> rfl
        · simp only [hchal, ↓reduceIte, StateT.run_pure, probeHook_lift_pure_run, pure_bind]
    · simp only [↓reduceIte, StateT.run_pure, probeHook_lift_pure_run, pure_bind]
  · simp only [Bool.true_or, ↓reduceIte, StateT.run_pure, pure_bind]

omit [SampleableType Pt] in
theorem kemFailSimImpl_proj_eq_simImplC {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) :
    ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run (sC, gh, tr) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) =
    (((LibsignalSimC.simImplC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
        Dh q_sm).run sC).run gh) := by
  rcases q_sm with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · change (((StateT.lift (OracleSpec.query (spec := unifSpec) n : ProbComp _) :
        KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr)) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) =
      (((StateT.lift ((probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)).lift
        (liftM (OracleSpec.query (spec := unifSpec) n : ProbComp _))) :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) _).run sC).run gh)
    rw [StateT.run_lift, bind_assoc, StateT.run_lift, StateT.run_bind,
      probeHook_lift_liftM_run, bind_assoc]
    simp only [pure_bind, StateT.run_pure]
  · exact kemFailSendStep_proj_eq_simSendC P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r
      sC gh tr
  · exact kemFailSendStep_proj_eq_simSendC P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
      sC gh tr
  · change (((do
        let ⟨sC, _, _⟩ ← get
        let revHonest := sC.base.honest.reverse
        let j? := revHonest.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
        let res ← runProbeStep P ℓ Dh encPt encT decT idOf lam qep
          (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (lFS P.C P.codec ℓ encT idOf 25000)
            (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w true))
        match res, j? with
        | some (.accepted _ _ _), some j =>
          modify fun ⟨sC', gh', tr⟩ => (sC', gh', stepKemFailDeliver P.C.F K tr Q j)
        | _, _ => pure ()
        return res : KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr)) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) = _
    rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, runProbeStep_run,
      bind_assoc, bind_assoc]
    refine (probComp_bind_congr _ fun ⟨⟨res, sC'⟩, gh'⟩ => ?_).trans (bind_pure _)
    rw [pure_bind]
    rcases res with _ | r_acc
    · simp
    · cases r_acc with
      | rejected => simp
      | accepted t i pm =>
        cases List.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
            sC.base.honest.reverse <;>
          simp [StateT.run_modify]
  · change ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep _).run (sC, gh, tr) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) = _
    rw [runProbeStep_run, bind_assoc]
    simp only [pure_bind, Prod.mk.eta, bind_pure]
    rfl
  · change ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep _).run (sC, gh, tr) >>=
      fun z => pure ((z.1, z.2.1), z.2.2.1)) = _
    rw [runProbeStep_run, bind_assoc]
    simp only [pure_bind, Prod.mk.eta, bind_pure]
    rfl

omit [SampleableType Pt] in
theorem simulateQ_kemFailSimImpl_proj_eq_simulateQ_simImplC {PQ α : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
      α) :
    ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
      (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
      (tr : KemFailTrackState P.C.F),
      ((simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) oa).run (sC, gh, tr) >>=
        fun z => pure ((z.1, z.2.1), z.2.2.1)) =
      (((simulateQ (LibsignalSimC.simImplC P encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000)
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
          Dh) oa).run sC).run gh) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sC gh tr
    rfl
  | query_bind q_sm r ih =>
    intro sC gh tr
    simp only [simulateQ_query_bind, StateT.run_bind, bind_assoc]
    have hstep :
        (StateT.run (liftM (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
            (OracleSpec.query q_sm).input)) (sC, gh, tr) >>=
          fun z => pure ((z.1, z.2.1), z.2.2.1)) =
        StateT.run (StateT.run (liftM (LibsignalSimC.simImplC P encT decT qep
            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (lFS P.C P.codec ℓ encT idOf 25000)
            (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
            Dh (OracleSpec.query q_sm).input)) sC) gh :=
      kemFailSimImpl_proj_eq_simImplC P K ℓ Dh encPt encT decT idOf lam qep q_sm sC gh tr
    rw [← hstep, bind_assoc]
    apply probComp_bind_congr
    intro ⟨u, sC₁, gh₁, tr₁⟩
    rw [pure_bind]
    exact ih u sC₁ gh₁ tr₁

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] in
theorem kemCandValid_initKemFailTrack (F : ShaCompress) (K : MlKem) (k : BitVec 256) :
    KemCandValid K (initKemFailTrack F k) := by
  intro _ h
  cases h

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] in
theorem honestFail_getD_of_kemCandValid {F : ShaCompress} (K : MlKem)
    (tr : KemFailTrackState F) (hv : KemCandValid K tr)
    (hsome : tr.cand.isSome = true) :
    let p := tr.cand.getD (List.Vector.replicate 64 0, List.Vector.replicate 32 0)
    K.honestExchangeFails p.1 p.2 = true := by
  cases h : tr.cand with
  | none => simp [h] at hsome
  | some p =>
    simp only [Option.getD_some]
    exact hv p h

omit [SampleableType Pt] in
/-- `hiddenSaltGame` has the same distribution as projecting the probe flag from `kemFailSimImpl`. -/
theorem hiddenSaltGame_eq_kemFailSimImpl_proj {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibsignalSM.LibAdv PQ (BitVec 512) ℓ) :
    hiddenSaltGame P ℓ Dh encPt encT decT idOf lam qep A = (do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let gh₀ := (SM.initState fig k b, false)
      let tr₀ := initKemFailTrack P.C.F pqrKey
      let z ←
        (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) A).run (sC₀, gh₀, tr₀)
      return z.2.2.1.2) := by
  unfold hiddenSaltGame LibsignalSimC.simRunCWith
  apply probComp_bind_congr; intro b
  apply probComp_bind_congr; intro k
  dsimp only
  rw [StateT.run_bind, bind_assoc, probeHook_lift_liftM_run, bind_assoc]
  apply probComp_bind_congr; intro pqrKey
  rw [pure_bind]
  dsimp only
  rw [StateT.run'_eq, StateT.run_map, map_eq_bind_pure_comp,
    ← simulateQ_kemFailSimImpl_proj_eq_simulateQ_simImplC P K ℓ Dh encPt encT decT idOf lam qep A
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b, false)
      (initKemFailTrack P.C.F pqrKey)]
  simp only [Function.comp_apply, bind_assoc, pure_bind]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evalDist_pure_bool_mono {b₁ b₂ : Bool} (h : b₁ = true → b₂ = true) :
    𝒟[(pure b₁ : ProbComp Bool)] {true} ≤ 𝒟[(pure b₂ : ProbComp Bool)] {true} := by
  cases hb₁ : b₁
  · simp
  · rw [h hb₁]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evalDist_pure_bool_le_add {b₁ b₂ b₃ : Bool}
    (h : b₁ = true → b₂ = true ∨ b₃ = true) :
    𝒟[(pure b₁ : ProbComp Bool)] {true} ≤
      𝒟[(pure b₂ : ProbComp Bool)] {true} + 𝒟[(pure b₃ : ProbComp Bool)] {true} := by
  cases hb₁ : b₁
  · simp
  · rcases h hb₁ with rfl | rfl
    · exact le_self_add
    · exact le_add_self

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evalDist_bind_mono_bool_of_support {α : Type} (p : ProbComp α)
    (f g : α → ProbComp Bool)
    (h : ∀ a ∈ support p, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) :
    𝒟[p >>= f] {true} ≤ 𝒟[p >>= g] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
    refine MeasureTheory.lintegral_mono fun u => ih u fun a ha => h a ?_
    rw [MonadAttach.mem_support_bind]
    exact ⟨u, by simp, ha⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evalDist_bind_le_add_bool_of_support {α : Type} (p : ProbComp α)
    (f g h : α → ProbComp Bool)
    (hle : ∀ a ∈ support p, 𝒟[f a] {true} ≤ 𝒟[g a] {true} + 𝒟[h a] {true}) :
    𝒟[p >>= f] {true} ≤ 𝒟[p >>= g] {true} + 𝒟[p >>= h] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact hle a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable,
        ← MeasureTheory.lintegral_add_left Measurable.of_discrete]
    refine MeasureTheory.lintegral_mono fun u => ih u fun a ha => hle a ?_
    rw [MonadAttach.mem_support_bind]
    exact ⟨u, by simp, ha⟩

omit [SampleableType Pt] in
/-- Bounds the probability that `kemFailSimImpl` records a candidate by `K.kemFailFindAdvantage`. -/
theorem evalDist_kemFailSimImpl_cand_isSome_le_kemFailFindAdvantage
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibsignalSM.LibAdv PQ (BitVec 512) ℓ) :
    𝒟[do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let gh₀ := (SM.initState fig k b, false)
      let tr₀ := initKemFailTrack P.C.F pqrKey
      let z ←
        (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) A).run (sC₀, gh₀, tr₀)
      return z.2.2.2.cand.isSome] {true} ≤
    K.kemFailFindAdvantage (redKemFailHiddenSalt P K ℓ Dh encPt encT decT idOf lam qep A) := by
  unfold MlKem.kemFailFindAdvantage MlKem.kemFailFindGame redKemFailHiddenSalt
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_mono_bool_of_support _ _ _ fun b _ => ?_
  refine evalDist_bind_mono_bool_of_support _ _ _ fun k _ => ?_
  refine evalDist_bind_mono_bool_of_support _ _ _ fun pqrKey _ => ?_
  refine evalDist_bind_mono_bool_of_support _ _ _ fun z hz => ?_
  apply evalDist_pure_bool_mono
  intro hsome
  have hv := (simulateQ_kemFailSimImpl_cand_valid P K ℓ Dh encPt encT decT idOf lam qep A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b, false)
    (initKemFailTrack P.C.F pqrKey) z hz).1 (kemCandValid_initKemFailTrack P.C.F K pqrKey)
  exact honestFail_getD_of_kemCandValid K z.2.2.2 hv hsome

omit [SampleableType Pt] in
/-- Splits `hiddenSaltTerm` into the candidate-free probe probability plus `K.kemFailFindAdvantage`. -/
theorem hiddenSaltTerm_le_cand_none_add_kemFailFindAdvantage
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibsignalSM.LibAdv PQ (BitVec 512) ℓ) :
    hiddenSaltTerm P ℓ Dh encPt encT decT idOf lam qep A ≤
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let gh₀ := (SM.initState fig k b, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) A).run (sC₀, gh₀, tr₀)
        return (z.2.2.1.2 && !z.2.2.2.cand.isSome)] {true} +
      K.kemFailFindAdvantage (redKemFailHiddenSalt P K ℓ Dh encPt encT decT idOf lam qep A) := by
  unfold hiddenSaltTerm
  rw [hiddenSaltGame_eq_kemFailSimImpl_proj P K ℓ Dh encPt encT decT idOf lam qep A]
  refine (evalDist_bind_le_add_bool_of_support _ _
    (fun b => do
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let gh₀ := (SM.initState fig k b, false)
      let tr₀ := initKemFailTrack P.C.F pqrKey
      let z ←
        (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) A).run (sC₀, gh₀, tr₀)
      return (z.2.2.1.2 && !z.2.2.2.cand.isSome))
    (fun b => do
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let gh₀ := (SM.initState fig k b, false)
      let tr₀ := initKemFailTrack P.C.F pqrKey
      let z ←
        (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) A).run (sC₀, gh₀, tr₀)
      return z.2.2.2.cand.isSome)
    ?_).trans (add_le_add le_rfl
      (evalDist_kemFailSimImpl_cand_isSome_le_kemFailFindAdvantage P K ℓ Dh encPt encT decT idOf
        lam qep A))
  intro b _
  refine evalDist_bind_le_add_bool_of_support _ _ _ _ fun k _ => ?_
  refine evalDist_bind_le_add_bool_of_support _ _ _ _ fun pqrKey _ => ?_
  refine evalDist_bind_le_add_bool_of_support _ _ _ _ fun z _ => ?_
  apply evalDist_pure_bool_le_add
  intro hfl
  cases hsome : z.2.2.2.cand.isSome
  · left; simp [hfl]
  · right; rfl

omit [Zero Pt] [SampleableType Pt] in
theorem df_noProbe_rel_at_flag_eq_false {PQ α : Type}
    {fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {qepF : ℕ} {sameHdr : Fig8C Pt → Fig8C Pt → Bool}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {mPr : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α}
    (h : df_noProbe_rel_at fig qepF sameHdr sC mPr mDF)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (w : (α × LibsignalToModularSchemeSimState PQ Pt ℓ) ×
      (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool))
    (hw : w ∈ support ((mPr.run sC).run (g, false))) :
    w.2.2 = false := by
  have heq := (h [] { base := g } rfl).1
  rw [← heq, MonadAttach.mem_support_bind] at hw
  rcases hw with ⟨z, _, hw⟩
  simp only [support_pure, Set.mem_singleton_iff] at hw
  subst hw
  rfl

omit [SampleableType Pt] in
theorem mem_support_simImplC_of_mem_support_kemFailSimImpl {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run
      (sC, gh, tr))) :
    ((z.1, z.2.1), z.2.2.1) ∈ support
      (((LibsignalSimC.simImplC P encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000)
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
          Dh q_sm).run sC).run gh) := by
  rw [← kemFailSimImpl_proj_eq_simImplC P K ℓ Dh encPt encT decT idOf lam qep q_sm sC gh tr,
      MonadAttach.mem_support_bind]
  exact ⟨z, hz, by simp⟩

omit [SampleableType Pt] in
theorem kemFailSimImpl_inl_state_eq {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (n : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inl n) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep (.inl n)).run
      (sC, gh, tr))) :
    z.2 = (sC, gh, tr) := by
  change z ∈ support ((StateT.lift (OracleSpec.query (spec := unifSpec) n) :
      KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr)) at hz
  simp only [StateT.run_lift, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at hz
  rcases hz with ⟨_, _, rfl⟩
  rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem simulateQ_fig8ToDFImpl_liftM_probComp {α : Type}
    (ℓ : ℕ) (m : ProbComp α) (sent : List (Fig8C Pt)) :
    (simulateQ (fig8ToDFImpl Pt ℓ) (liftM m : Fig8Comp Pt ℓ α)).run sent =
      ((liftM m : DeliverForge.AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
          (Fig8C Pt) α) >>= fun a => pure (a, sent)) := by
  induction m using OracleComp.inductionOn with
  | pure a =>
    simp
  | query_bind n r ih =>
    change (simulateQ (fig8ToDFImpl Pt ℓ)
      ((liftM (OracleSpec.query (spec := unifSpec) n) : Fig8Comp Pt ℓ _) >>=
        fun u => (liftM (r u) : Fig8Comp Pt ℓ α))).run sent =
      (((liftM (OracleSpec.query (spec := unifSpec) n) :
          DeliverForge.AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) _) >>=
        fun u => (liftM (r u) :
          DeliverForge.AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
            (Fig8C Pt) α)) >>=
        fun a => pure (a, sent))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    change ((fig8ToDFImpl Pt ℓ (.inl n)).run sent >>=
      fun z => (simulateQ (fig8ToDFImpl Pt ℓ) (liftM (r z.1) : Fig8Comp Pt ℓ α)).run z.2) = _
    rw [fig8ToDFImpl_inl_run, bind_assoc]
    refine congrArg (_ >>= ·) (funext fun u => ?_)
    rw [pure_bind]
    exact ih u

omit [Zero Pt] [SampleableType Pt] in
theorem deliverForgeHook_lift_liftM_run {α : Type}
    (ℓ : ℕ) (m : ProbComp α) (sent : List (Fig8C Pt)) :
    ((deliverForgeHook Pt ℓ).lift (liftM m : Fig8Comp Pt ℓ α)).run sent =
      ((liftM m : DeliverForge.AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
          (Fig8C Pt) α) >>= fun a => pure (a, sent)) :=
  simulateQ_fig8ToDFImpl_liftM_probComp ℓ m sent

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evalDist_bind_true_le_add_of_badCoin {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] {d₁ d₂ : ℝ≥0∞} (oa : ProbComp α) (bad : α → Bool)
    (hbad : 𝒟[oa] {a | bad a = true} ≤ d₁) (f : α → ProbComp Bool)
    (h : ∀ a, bad a = false → 𝒟[f a] {true} ≤ d₂) :
    𝒟[oa >>= f] {true} ≤ d₁ + d₂ := by
  have hc := (closeByRefines_bind_of_bad (d₂ := d₂) 0 oa bad hbad
    (fR := f) (fS := fun _ => pure false) (fWin := fun _ _ => pure false)
    (fEps0 := fun _ => pure false) fun a ha => by
      unfold CloseByRefines
      simp [h a ha]).1
  simpa [OracleComp.evalDist_bind_const] using hc

/-- Remaining union-bound slack across `w_rem` epoch-coin draws and at most `q` candidates per draw. -/
noncomputable def spurSlack {PQ PQC : Type} (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (q w_rem : ℕ) : ℝ≥0∞ :=
  ((q * w_rem : ℕ) : ℝ≥0∞) * spurUnit P.C.F encPt Dh

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spurSlack_step_le {PQ PQC : Type} (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (q : ℕ) {L_len w_rem : ℕ} (hL : L_len ≤ q) :
    (L_len : ℝ≥0∞) * spurUnit P.C.F encPt Dh + spurSlack P encPt Dh q w_rem ≤
      spurSlack P encPt Dh q (w_rem + 1) := by
  have h1 : (L_len : ℝ≥0∞) * spurUnit P.C.F encPt Dh ≤
      (q : ℝ≥0∞) * spurUnit P.C.F encPt Dh := by gcongr
  calc (L_len : ℝ≥0∞) * spurUnit P.C.F encPt Dh + spurSlack P encPt Dh q w_rem
      ≤ (q : ℝ≥0∞) * spurUnit P.C.F encPt Dh + spurSlack P encPt Dh q w_rem := by gcongr
    _ = spurSlack P encPt Dh q (w_rem + 1) := by
      unfold spurSlack
      push_cast
      ring

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem spurSlack_le_spuriousStepTerm {PQ PQC : Type} (P : Params PQ PQC)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q qep : ℕ)
    {w_rem : ℕ} (hw : w_rem ≤ qep) :
    spurSlack P encPt Dh q w_rem ≤ spuriousStepTerm P.C.F encPt Dh q qep := by
  unfold spurSlack LibsignalSim.spuriousStepTerm LibsignalSim.rootKdfSpuriousStepUnit spurUnit
  gcongr

/-- Number of sending epochs of `Q` in `[1, t]`. -/
def sentEpochsUpTo : Party → ℕ → ℕ
  | .A, t => (t + 1) / 2
  | .B, t => t / 2

/-- Remaining sending-epoch budget for the evicted-wire union bound. -/
def remSendEpochs {St Msg C : Type} (qep : ℕ) (mir : SM.GameState St Msg C) : ℕ :=
  qep - (sentEpochsUpTo .A (mir.epoch .A) + sentEpochsUpTo .B (mir.epoch .B))

theorem sentEpochsUpTo_mono (Q : Party) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) :
    sentEpochsUpTo Q t₁ ≤ sentEpochsUpTo Q t₂ := by
  cases Q <;> simp only [sentEpochsUpTo] <;> omega

theorem remSendEpochs_anti_epoch (qep : ℕ) {St Msg C : Type}
    (mir mir' : SM.GameState St Msg C)
    (hep : ∀ R, mir.epoch R ≤ mir'.epoch R) :
    remSendEpochs qep mir' ≤ remSendEpochs qep mir := by
  have hA := sentEpochsUpTo_mono .A (hep .A)
  have hB := sentEpochsUpTo_mono .B (hep .B)
  unfold remSendEpochs
  omega

theorem sentEpochsUpTo_succ_of_sendsIn (Q : Party) (t : ℕ)
    (hs : Q.sendsIn (t + 1) = true) :
    sentEpochsUpTo Q (t + 1) = sentEpochsUpTo Q t + 1 := by
  cases Q <;> simp only [Party.sendsIn, beq_iff_eq, sentEpochsUpTo] at hs ⊢ <;> omega

theorem sentEpochsUpTo_add_le {qep tA tB : ℕ} (hA : tA ≤ qep) (hB : tB ≤ qep) :
    sentEpochsUpTo .A tA + sentEpochsUpTo .B tB ≤ qep := by
  simp only [sentEpochsUpTo]
  omega

theorem remSendEpochs_new_send_epoch (qep : ℕ) {St Msg C : Type}
    (mir mir' : SM.GameState St Msg C) (Q : Party)
    (hs : Q.sendsIn (mir.epoch Q + 1) = true)
    (hQ_le : mir.epoch Q + 1 ≤ qep)
    (hother_le : mir.epoch Q.other ≤ qep)
    (hep' : mir'.epoch = Function.update mir.epoch Q (mir.epoch Q + 1)) :
    0 < remSendEpochs qep mir ∧
      remSendEpochs qep mir' = remSendEpochs qep mir - 1 := by
  have hsucc := sentEpochsUpTo_succ_of_sendsIn Q (mir.epoch Q) hs
  unfold remSendEpochs
  rw [hep']
  cases Q with
  | A =>
    rw [Function.update_self, Function.update_of_ne (by decide : Party.B ≠ Party.A), hsucc]
    have hsum : sentEpochsUpTo .A (mir.epoch .A) + 1 + sentEpochsUpTo .B (mir.epoch .B) ≤ qep := by
      rw [← hsucc]
      exact sentEpochsUpTo_add_le hQ_le hother_le
    omega
  | B =>
    rw [Function.update_self, Function.update_of_ne (by decide : Party.A ≠ Party.B), hsucc]
    have hsum :
        sentEpochsUpTo .A (mir.epoch .A) + (sentEpochsUpTo .B (mir.epoch .B) + 1) ≤ qep := by
      rw [← hsucc]
      exact sentEpochsUpTo_add_le hother_le hQ_le
    omega

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurInit_spurBadList_eq_false
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8))
    (sa sb : List (BitVec 8)) (epExp : ℕ → BitVec 256)
    (Q : Party) (w_acc : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F)
    (rk_base : Ratchet.RootKey) (T_base : Pt) :
    spurBadList P encPt Dh Q rk_base T_base
      (Proofs.Refinement.evictedSpurCandList P epExp w_acc
        (Proofs.Refinement.honestBeforeEpoch (initSimC (Pt := Pt) (ℓ := ℓ) sa sb).base.honest
          (Proofs.Refinement.evictAccEpoch (initSimC (Pt := Pt) (ℓ := ℓ) sa sb).base.mir Q)))
      (epExp ((initSimC (Pt := Pt) (ℓ := ℓ) sa sb).base.mir.epoch Q)) = false := by
  simp [initSimC, initSim, Proofs.Refinement.honestBeforeEpoch,
    Proofs.Refinement.evictedSpurCandList, spurBadList]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurInit_remSendEpochs
    (qep : ℕ) (sa sb : List (BitVec 8)) :
    remSendEpochs qep (initSimC (Pt := Pt) (ℓ := ℓ) sa sb).base.mir = qep := by
  simp [remSendEpochs, sentEpochsUpTo, initSimC, initSim]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAcceptPure_inject_not_accepted_invariants
    (qep : ℕ) (P_party : Party) (w : List (BitVec 8))
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (s : SimState (List (BitVec 8)) Pt ℓ)
    (hnot : ∀ t' i' pm',
      (onAcceptPure qep P_party w false t i m ci? T pq' s).1 ≠ some (.accepted t' i' pm')) :
    let s' := (onAcceptPure qep P_party w false t i m ci? T pq' s).2
    s'.honest = s.honest ∧ s'.pq = s.pq ∧ s'.chains = s.chains ∧ s'.mir.epoch = s.mir.epoch := by
  unfold onAcceptPure at hnot ⊢
  dsimp only at hnot ⊢
  simp only [Bool.false_eq_true, ↓reduceIte] at hnot ⊢
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · rename_i hle
    simp only [hle, ↓reduceIte] at hnot
    split
    · rename_i htriv
      simp only [htriv, ↓reduceIte] at hnot
      exact False.elim (hnot t i (some m) rfl)
    · exact ⟨rfl, rfl, rfl, rfl⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAnswerPure_inject_not_accepted_invariants
    (qep : ℕ) (P_party : Party) (w : List (BitVec 8))
    (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState (List (BitVec 8)) Pt ℓ)
    (hnot : ∀ t' i' pm',
      (onAnswerPure qep P_party w false ci? T pq' res s).1 ≠ some (.accepted t' i' pm')) :
    let s' := (onAnswerPure qep P_party w false ci? T pq' res s).2
    s'.honest = s.honest ∧ s'.pq = s.pq ∧ s'.chains = s.chains ∧ s'.mir.epoch = s.mir.epoch := by
  unfold onAnswerPure at hnot ⊢
  cases res with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some r =>
    cases r with
    | rejected => exact ⟨rfl, rfl, rfl, rfl⟩
    | accepted t i pm =>
      exact onAcceptPure_inject_not_accepted_invariants qep P_party w t i
        ((pm.map (·.2)).getD default) ci? T pq' s hnot

omit [SampleableType Pt] in
theorem fwdCPure_inject_not_accepted_invariants
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (P_party : Party) (w : List (BitVec 8)) (ci? : Option ℕ)
    (T : PublicKey) (pq' : List (BitVec 8)) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hnot : ∀ t' i' pm',
      (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a P_party w false ci? T pq' honestC c' x).1 ≠
        some (.accepted t' i' pm')) :
    let s' := (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a P_party w false ci? T pq'
      honestC c' x).2.1.base
    s'.honest = x.1.base.honest ∧ s'.pq = x.1.base.pq ∧
      s'.chains = x.1.base.chains ∧ s'.mir.epoch = x.1.base.mir.epoch := by
  have hc3a : fwdCPure P ℓ Dh encPt encT idOf lam qep c3a P_party w false ci? T pq' honestC c' x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false P_party w false ci? T pq' none c' x := by
    unfold fwdCPure
    cases honestC <;> simp [Bool.false_and, Bool.and_false]
  rw [hc3a] at hnot ⊢
  unfold fwdCPure at hnot ⊢
  dsimp only at hnot ⊢
  exact onAnswerPure_inject_not_accepted_invariants qep P_party w ci? T pq' _ x.1.base hnot

theorem kemFailSimImpl_deliver_run
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F) :
    let r := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)
    let j? := sC.base.honest.reverse.findIdx?
      (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let tr' := match r.1, j? with
      | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
      | _, _ => tr
    (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inl (.inr (Q, w)))))).run
      (sC, gh, tr) = pure (r.1, (r.2.1, r.2.2, tr')) := by
  dsimp only
  change (do
    let ⟨sC, _, _⟩ ← get
    let revHonest := sC.base.honest.reverse
    let j? := revHonest.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let res ← runProbeStep P ℓ Dh encPt encT decT idOf lam qep
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w true))
    match res, j? with
    | some (.accepted _ _ _), some j =>
      modify fun ⟨sC', gh', tr⟩ => (sC', gh', stepKemFailDeliver P.C.F K tr Q j)
    | _, _ => pure ()
    return res : KemFailSimM PQ Pt P.C.F ℓ _).run (sC, gh, tr) = _
  rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, runProbeStep_run,
    simRecvC_probe_run P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)]
  simp only [pure_bind]
  rcases (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)).1 with _ | r_acc
  · rfl
  · cases r_acc with
    | rejected => rfl
    | accepted t i pm =>
      cases sC.base.honest.reverse.findIdx?
          (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) <;>
        simp [StateT.run_modify]

open CryptoGames.LibsignalSM.Proofs.Correctness

/-- Refinement invariant combining `SimInvCX` with `spurBadList = false` outside receive-only epochs. -/
def EvictedSpurSimInv
    (P : Params (List (BitVec 8)) (BitVec 512))
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  ∃ x₀ s_R ec winBefore epExp,
    Proofs.Refinement.SimInvCX P InvPQ ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { g with win := false } ec winBefore epExp ∧
    ∀ Q w_acc rk_base T_base,
      inReceiveOnlyEpoch sC.base.mir Q = false →
      spurBadList P encPt Dh Q rk_base T_base
        (Proofs.Refinement.evictedSpurCandList P epExp w_acc
          (Proofs.Refinement.honestBeforeEpoch sC.base.honest
            (Proofs.Refinement.evictAccEpoch sC.base.mir Q)))
        (epExp (sC.base.mir.epoch Q)) = false

omit [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurSimInv_init_of_simInvCX
    (P : Params (List (BitVec 8)) (BitVec 512))
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (sa sb : List (BitVec 8))
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8))}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hsim : Proofs.Refinement.SimInvCX P InvPQ ℓ Dh encPt encT idOf lam qep q r
      x₀ s_R (initSimC sa sb) { g with win := false } ec winBefore epExp) :
    EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q r (initSimC sa sb) g :=
  ⟨x₀, s_R, ec, winBefore, epExp, hsim,
    fun Q w_acc rk_base T_base _ =>
      evictedSpurInit_spurBadList_eq_false P Dh encPt sa sb epExp Q w_acc rk_base T_base⟩

theorem evictedSpurSimInv_init
    (P : Params (List (BitVec 8)) (BitVec 512))
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hS : Proofs.Refinement.SpqrCLocal P.spqr q InvPQ)
    (b : Bool) (k : BitVec 256 × BitVec 256) (pqrKey : BitVec 256)
    (hcoll0 : ∃ eA₀ : BitVec 256, Dh.dh eA₀ Dh.base ≠ Dh.dh k.2 Dh.base) :
    EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q q
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b) := by
  rcases k with ⟨k_root, x₀⟩
  rcases hcoll0 with ⟨eA₀, hne⟩
  exact evictedSpurSimInv_init_of_simInvCX P InvPQ ℓ Dh encPt encT idOf lam qep q q
    (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (k_root, x₀) b)
    (Proofs.Refinement.simInvCX_init P InvPQ ℓ Dh encPt encT idOf lam qep q hX b k_root x₀ eA₀
      pqrKey hne hS)

theorem fwdPure_accepted_epoch_eq
    {PQ PQC : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (s : SimState PQ Pt ℓ) (Q : Party) (c' : Fig8C Pt)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {t' i' : ℕ} {pm : Option (LibsignalMsgPublicPart × Plain ℓ)}
    (hacc : (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
      SM.Config.h1 s Q c' g).1 = some (.accepted t' i' pm)) :
    t' = c'.1.1 := by
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  unfold fwdPure at hacc
  split at hacc
  · unfold Proofs.Refinement.deliverPure at hacc
    split at hacc
    · cases hacc
    · cases htr : g.inTransit Q.other c' with
      | none => rw [htr] at hacc; cases hacc
      | some r =>
        rw [htr] at hacc
        dsimp only at hacc
        cases hrcv : sm.receive (g.st Q) c' with
        | none => rw [hrcv] at hacc; cases hacc
        | some v =>
          rcases v with ⟨st', t₁, i₁, m'⟩
          rw [hrcv] at hacc
          cases hacc
          exact (lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
            (g.st Q) c' hrcv).1
  · unfold Proofs.Refinement.injectPure at hacc
    split at hacc
    · cases hacc
    · cases hrcv : sm.receive (g.st Q) c' with
      | none => rw [hrcv] at hacc; cases hacc
      | some v =>
        rcases v with ⟨st', t₁, i₁, m'⟩
        rw [hrcv] at hacc
        dsimp only at hacc
        split at hacc
        · cases hacc
        · split at hacc
          · cases hacc
            exact (lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
              (g.st Q) c' hrcv).1
          · cases hacc

theorem fwdCPure_inject_not_accepted_of_epoch_le
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ)
    (T : PublicKey) (pq' : List (BitVec 8)) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hsafe : x.1.base.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hep_le : x.1.base.mir.epoch Q ≤ c'.1.1) :
    ∀ t' i' pm',
      (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w false ci? T pq' honestC c' x).1 ≠
        some (.accepted t' i' pm') := by
  intro t' i' pm' hacc
  have hc3a : fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w false ci? T pq' honestC c' x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' none c' x := by
    unfold fwdCPure
    cases honestC <;> simp [Bool.false_and, Bool.and_false]
  rw [hc3a] at hacc
  unfold fwdCPure onAnswerPure at hacc
  dsimp only at hacc
  cases hz : (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
      SM.Config.h1 x.1.base Q c' x.2.1).1 with
  | none => rw [hz] at hacc; cases hacc
  | some r_res =>
    rw [hz] at hacc
    cases r_res with
    | rejected => cases hacc
    | accepted t₁ i₁ pm₁ =>
      have ht₁ : t₁ = c'.1.1 :=
        fwdPure_accepted_epoch_eq P ℓ Dh encPt encT idOf lam qep x.1.base Q c' x.2.1 hz
      have htriv_f : x.1.base.mir.trivial 3 ⟨Q.other, t₁, i₁⟩ = false :=
        Proofs.Refinement.trivial_false_of_newChain_inject hsafe hcomp Q ⟨Q.other, t₁, i₁⟩
          (by dsimp only; omega)
      unfold onAcceptPure at hacc
      dsimp only at hacc
      simp only [Bool.false_eq_true, ↓reduceIte, htriv_f] at hacc
      split at hacc <;> cases hacc

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAcceptPure_inject_some_invariants
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (t i : ℕ) (m : Plain ℓ) (ci : ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (s : SimState (List (BitVec 8)) Pt ℓ)
    (hsafe : s.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ s.mir.comp, SM.healedBy s.mir.tL 3 p.epoch = false)
    (hhist : Proofs.Refinement.SpqrHistoryInv P K s)
    (hreach : Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (s.pq Q) pq') :
    let s' := (onAcceptPure qep Q w false t i m (some ci) T pq' s).2
    s'.honest = s.honest ∧ s'.mir.epoch = s.mir.epoch ∧
      Proofs.Refinement.SpqrHistoryInv P K s' := by
  refine ⟨?_, ?_,
    Proofs.Refinement.spqrHistoryInv_onAcceptPure_some P K qep Q w false t i m ci T pq' s
      hhist hreach⟩
  · unfold onAcceptPure
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · split <;> rfl
  · unfold onAcceptPure
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · split
      · rename_i htriv
        have ht_le : (⟨Q.other, t, i⟩ : SM.Pos).epoch ≤ s.mir.epoch Q := by
          by_contra hnot_le
          have hge : s.mir.epoch Q ≤ (⟨Q.other, t, i⟩ : SM.Pos).epoch := by
            dsimp only at hnot_le ⊢; omega
          have hf := Proofs.Refinement.trivial_false_of_newChain_inject hsafe hcomp Q
            ⟨Q.other, t, i⟩ hge
          rw [htriv] at hf
          cases hf
        exact Proofs.Refinement.WP2A.I3.accept_epoch_eq_of_le s.mir Q () ⟨Q.other, t, i⟩ ht_le
      · rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAnswerPure_inject_some_invariants
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (ci : ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState (List (BitVec 8)) Pt ℓ)
    (hsafe : s.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ s.mir.comp, SM.healedBy s.mir.tL 3 p.epoch = false)
    (hhist : Proofs.Refinement.SpqrHistoryInv P K s)
    (hreach : Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (s.pq Q) pq') :
    let s' := (onAnswerPure qep Q w false (some ci) T pq' res s).2
    s'.honest = s.honest ∧ s'.mir.epoch = s.mir.epoch ∧
      Proofs.Refinement.SpqrHistoryInv P K s' := by
  unfold onAnswerPure
  cases res with
  | none => exact ⟨rfl, rfl, hhist⟩
  | some r =>
    cases r with
    | rejected => exact ⟨rfl, rfl, hhist⟩
    | accepted t i pm =>
      exact onAcceptPure_inject_some_invariants P K qep Q w t i
        ((pm.map (·.2)).getD default) ci T pq' s hsafe hcomp hhist hreach

omit [SampleableType Pt] in
theorem fwdCPure_inject_some_invariants
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8)) (ci : ℕ)
    (T : PublicKey) (pq' : List (BitVec 8)) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hsafe : x.1.base.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hhist : Proofs.Refinement.SpqrHistoryInv P K x.1.base)
    (hreach : Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (x.1.base.pq Q) pq') :
    let s' := (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w false (some ci) T pq'
      honestC c' x).2.1.base
    s'.honest = x.1.base.honest ∧ s'.mir.epoch = x.1.base.mir.epoch ∧
      Proofs.Refinement.SpqrHistoryInv P K s' := by
  have hc3a : fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w false (some ci) T pq' honestC c' x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false (some ci) T pq' none c' x := by
    unfold fwdCPure
    cases honestC <;> simp [Bool.false_and, Bool.and_false]
  rw [hc3a]
  unfold fwdCPure
  dsimp only
  exact onAnswerPure_inject_some_invariants P K qep Q w ci T pq' _ x.1.base hsafe hcomp hhist
    hreach

theorem fwdCPure_inject_none_invariants
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8))
    (T : PublicKey) (pq' : List (BitVec 8)) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hsafe : x.1.base.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hep_le : x.1.base.mir.epoch Q ≤ c'.1.1)
    (hhist : Proofs.Refinement.SpqrHistoryInv P K x.1.base) :
    let s' := (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w false none T pq'
      honestC c' x).2.1.base
    s'.honest = x.1.base.honest ∧ s'.mir.epoch = x.1.base.mir.epoch ∧
      Proofs.Refinement.SpqrHistoryInv P K s' := by
  have hnot_acc := fwdCPure_inject_not_accepted_of_epoch_le P ℓ Dh encPt encT idOf lam qep c3a
    Q w none T pq' honestC c' x hsafe hcomp hep_le
  obtain ⟨h1, h2, h3, h4⟩ := fwdCPure_inject_not_accepted_invariants P ℓ Dh encPt encT idOf lam
    qep c3a Q w none T pq' honestC c' x hnot_acc
  exact ⟨h1, h4, Proofs.Refinement.spqrHistoryInv_preserve_of_sub hhist h1
    (fun R => by rw [h2]; exact .refl _)
    (fun R t ht => by rwa [h3] at ht)⟩

theorem simRecvStepC_inject_preserves_spqrHistoryInv_and_epoch_of_simInvC
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC (List (BitVec 8)) Pt ℓ)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hhist : Proofs.Refinement.SpqrHistoryInv P K x.1.base) :
    let s' := (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w false x).2.1.base
    s'.honest = x.1.base.honest ∧ s'.mir.epoch = x.1.base.mir.epoch ∧
      Proofs.Refinement.SpqrHistoryInv P K s' := by
  rcases x with ⟨⟨s, kept, sent, snaps⟩, g, fl⟩
  unfold simRecvStepC simRecvStepCGen
  by_cases hst : s.stopped = true
  · simp [hst, hhist]
  simp only [hst, Bool.false_eq_true, ↓reduceIte]
  by_cases hwin : s.mir.win = true
  · simp [hwin, hhist]
  simp only [hwin, Bool.false_eq_true, ↓reduceIte]
  by_cases hdel : (false && (s.mir.inTransit Q.other w).isNone) = true
  · simp at hdel
  simp only [hdel, Bool.false_eq_true, ↓reduceIte]
  by_cases hinj : (!false && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w))) = true
  · simp at hinj; simp [hinj, hhist]
  have hsafe : s.mir.safeInj 3 = true := by
    revert hinj
    cases (s.mir.inTransit Q.other w).isSome <;> cases s.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  simp only [hinj, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : w.length < 9
  · simp [hlen, hhist]
  simp only [hlen, ↓reduceIte]
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact ⟨rfl, rfl, hhist⟩
  | some hb =>
    rcases hb with ⟨h, body⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · simp [haddr, hhist]
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    by_cases hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet = true
    · simp [hpan, hhist]
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    cases hspqr : P.spqr.recv (s.pq Q) h.pqRatchet with
    | error _ => exact ⟨rfl, rfl, hhist⟩
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      have hreach : Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (s.pq Q) pq' :=
        .recv (.refl _) (hspqr_eq ▸ hspqr)
      cases hci : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        split
        · exact ⟨rfl, rfl, hhist⟩
        · exact fwdCPure_inject_some_invariants P K ℓ Dh encPt encT idOf lam qep true Q w ci
            h.senderRatchetKey pq' _ _ (⟨s, kept, sent, snaps⟩, g, fl) hsafe hcomp hhist hreach
      | none =>
        dsimp only
        let x₁ : JointC (List (BitVec 8)) Pt ℓ :=
          if inReceiveOnlyEpoch s.mir Q || (Q == Party.A && (s.chains Q).any (·.key.isNone)) then
            ({ base := { s with amb := s.amb + 1, stopped := false },
                kept := kept, sent := sent, snaps := snaps }, g, fl)
          else (⟨s, kept, sent, snaps⟩, g, fl)
        have hx1 : x₁.1.base.honest = s.honest ∧ x₁.1.base.pq = s.pq ∧
            x₁.1.base.chains = s.chains ∧ x₁.1.base.mir = s.mir := by
          dsimp only [x₁]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
        have hhist1 : Proofs.Refinement.SpqrHistoryInv P K x₁.1.base :=
          Proofs.Refinement.spqrHistoryInv_preserve_of_sub hhist hx1.1
            (fun R => by rw [hx1.2.1]; exact .refl _)
            (fun R t ht => by rwa [hx1.2.2.1] at ht)
        split
        · exact ⟨rfl, rfl, hhist⟩
        · split
          · exact ⟨rfl, rfl, hhist⟩
          · split
            · exact ⟨hx1.1, congrArg (·.epoch) hx1.2.2.2, hhist1⟩
            · cases hT : decT h.senderRatchetKey with
              | none => exact ⟨hx1.1, congrArg (·.epoch) hx1.2.2.2, hhist1⟩
              | some T =>
                dsimp only
                let hc_opt : Option (Fig8C Pt) :=
                  (s.honest.find? fun (wc : List (BitVec 8) × Fig8C Pt) =>
                    wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
                let c_fb : Fig8C Pt :=
                  ((s.mir.epoch Q + 1, some T),
                    (h.counter.toNat + 1,
                      ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
                        effectiveHkdfSalt32 salt)))
                split
                · unfold fwdEvictCPure
                  simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                  obtain ⟨h1, h4, hhist2⟩ := fwdCPure_inject_none_invariants P K ℓ Dh encPt encT
                    idOf lam qep false Q w h.senderRatchetKey pq' none c_fb x₁
                    (hx1.2.2.2.symm ▸ hsafe) (hx1.2.2.2.symm ▸ hcomp)
                    (by rw [hx1.2.2.2]; dsimp only [c_fb]; omega) hhist1
                  exact ⟨h1.trans hx1.1, h4.trans (congrArg (·.epoch) hx1.2.2.2), hhist2⟩
                · rename_i hev_false
                  have hmk_ep : x₁.1.base.mir.epoch Q ≤
                      (match hc_opt with
                      | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else c_fb
                      | none => c_fb).1.1 := by
                    rw [hx1.2.2.2]
                    cases hfind : hc_opt with
                    | none => dsimp only [c_fb]; omega
                    | some c =>
                      change ¬(Option.map (fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) hc_opt ==
                          some true) = true at hev_false
                      rw [hfind] at hev_false
                      simp only [Option.map_some, beq_iff_eq, Option.some.injEq,
                        decide_eq_true_eq, not_ne_iff] at hev_false
                      dsimp only [c_fb]
                      split <;> [omega; (dsimp only; omega)]
                  obtain ⟨h1, h4, hhist2⟩ := fwdCPure_inject_none_invariants P K ℓ Dh encPt encT
                    idOf lam qep true Q w h.senderRatchetKey pq' _ _ x₁
                    (hx1.2.2.2.symm ▸ hsafe) (hx1.2.2.2.symm ▸ hcomp) hmk_ep hhist1
                  exact ⟨h1.trans hx1.1, h4.trans (congrArg (·.epoch) hx1.2.2.2), hhist2⟩

/-- Game-level SPQR history and remaining-epoch invariant for `kemFailSimImpl`. -/
structure EvictedSpurHistGameInv
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (qep w_rem : ℕ) (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) : Prop where
  hhist : Proofs.Refinement.SpqrHistoryInv P K sC.base
  hw_rem : remSendEpochs qep sC.base.mir ≤ w_rem

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_init
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (pqrKey : BitVec 256) (qep : ℕ) :
    EvictedSpurHistGameInv (Pt := Pt) (ℓ := ℓ) P K qep qep
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) :=
  ⟨(Proofs.Refinement.spqrHistoryInv_init P K
    (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)).2,
   (evictedSpurInit_remSendEpochs (Pt := Pt) (ℓ := ℓ) qep
    (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)).le⟩

omit [SampleableType Pt] in
theorem kemFailSimImpl_corr_flag_eq_false {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (z : Option (GhostState PQ) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q))).run (sC, (g, false), tr))) :
    z.2.2.1.2 = false :=
  df_noProbe_rel_at_flag_eq_false
    (df_noProbe_rel_guardC (df_noProbe_rel_simCorrC P encT
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)
      DeliverForge.sameHdrScheme Dh Q) sC)
    g ((z.1, z.2.1), z.2.2.1)
    (mem_support_simImplC_of_mem_support_kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q)) sC (g, false) tr z hz)

omit [SampleableType Pt] in
theorem kemFailSimImpl_inject_flag_eq_false {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (z : Option (SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inr (Q, w))))).run (sC, (g, false), tr))) :
    z.2.2.1.2 = false :=
  df_noProbe_rel_at_flag_eq_false
    (df_noProbe_rel_guardC (df_noProbe_rel_simRecvC_inject P encT decT qep
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000) (qep + 1)
      DeliverForge.sameHdrScheme Q w) sC)
    g ((z.1, z.2.1), z.2.2.1)
    (mem_support_simImplC_of_mem_support_kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inr (Q, w)))) sC (g, false) tr z hz)

omit [SampleableType Pt] in
theorem kemFailSimImpl_send_flag_eq_false {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_send : Party × Plain ℓ × Option (BitVec 512) ⊕
      Party × Plain ℓ × Plain ℓ × Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inl (.inl q_send)))) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inl (.inl q_send))))).run (sC, (g, false), tr))) :
    z.2.2.1.2 = false := by
  rcases q_send with ⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩
  · exact df_noProbe_rel_at_flag_eq_false
      (df_noProbe_rel_guardC (df_noProbe_rel_simSendC P qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)
        DeliverForge.sameHdrScheme Q m₀ none r) sC)
      g ((z.1, z.2.1), z.2.2.1)
      (mem_support_simImplC_of_mem_support_kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) sC (g, false) tr z hz)
  · exact df_noProbe_rel_at_flag_eq_false
      (df_noProbe_rel_guardC (df_noProbe_rel_simSendC P qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)
        DeliverForge.sameHdrScheme Q m₀ (some m₁) r) sC)
      g ((z.1, z.2.1), z.2.2.1)
      (mem_support_simImplC_of_mem_support_kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) sC (g, false) tr z hz)

omit [SampleableType Pt] in
theorem kemFailSimImpl_corr_preserves_evictedSpurHistGameInv
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep w_rem : ℕ)
    (Q : Party)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (z : Option (GhostState (List (BitVec 8))) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q))).run (sC, gh, tr))) :
    EvictedSpurHistGameInv P K qep w_rem z.2.1 := by
  change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q))).run
    (sC, gh, tr)) at hz
  rw [runProbeStep_run, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hw_step : (w.1.1, (w.1.2, w.2)) ∈ support
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) (sC, gh)) := by
    change (w.1.1, (w.1.2, w.2)) ∈ support
      ((((LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q)).run
        sC).run gh) >>= fun r => pure (r.1.1, (r.1.2, r.2)))
    rw [MonadAttach.mem_support_bind]
    exact ⟨w, hw, by simp⟩
  obtain ⟨hhon_eq, hpq_eq, hep_eq, _, _⟩ :=
    stepSimCNone_corr_invariants P ℓ Dh encPt encT decT idOf lam qep Q (sC, gh)
      (w.1.1, (w.1.2, w.2)) hw_step
  have hchains_ep : ∀ R,
      (w.1.2.base.chains R).map (·.epoch) = (sC.base.chains R).map (·.epoch) := by
    intro R
    rw [stepSimCNone_corr_eq_steer] at hw_step
    simp only [support_pure, Set.mem_singleton_iff] at hw_step
    have hbase : w.1.2.base = (simCorrPureCSteer P Dh encT Q (sC, gh)).2.1.base :=
      congrArg (·.2.1.base) hw_step
    rw [hbase]
    unfold simCorrPureCSteer
    dsimp only
    split
    · rfl
    · split
      · rfl
      · cases (corrPure Q gh.1).1 with
        | none => rfl
        | some figSt =>
          dsimp only
          split
          · cases figSt.γ with
            | pub _ => rfl
            | exp x =>
              dsimp only
              cases R with
              | A =>
                rw [Function.update_self]
                exact c8_map_epoch_resolve_list (sC.base.chains .A) (encT (Dh.dh x Dh.base))
              | B =>
                rw [Function.update_of_ne (by decide : Party.B ≠ Party.A)]
          · rfl
  refine ⟨Proofs.Refinement.spqrHistoryInv_preserve_of_sub hInv.hhist hhon_eq
    (fun R => by rw [hpq_eq]; exact .refl _)
    (fun R t ht => by rwa [hchains_ep R] at ht), ?_⟩
  have hrem : remSendEpochs qep w.1.2.base.mir = remSendEpochs qep sC.base.mir := by
    unfold remSendEpochs
    rw [hep_eq]
  exact hrem ▸ hInv.hw_rem

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_preserve_of_unchanged_pq_honest
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem} {qep w_rem : ℕ}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hhon : sC'.base.honest = sC.base.honest)
    (hpq : sC'.base.pq = sC.base.pq)
    (hchains : ∀ R t, t ∈ (sC'.base.chains R).map (·.epoch) →
      t ∈ (sC.base.chains R).map (·.epoch))
    (hep_le : ∀ R, sC.base.mir.epoch R ≤ sC'.base.mir.epoch R) :
    EvictedSpurHistGameInv P K qep w_rem sC' :=
  ⟨Proofs.Refinement.spqrHistoryInv_preserve_of_sub hInv.hhist hhon
    (fun R => by rw [hpq]; exact .refl _) hchains,
   (remSendEpochs_anti_epoch qep sC.base.mir sC'.base.mir hep_le).trans hInv.hw_rem⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_send_same_epoch
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    {qep w_rem : ℕ}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {Q : Party} {pq' : List (BitVec 8)} {rq : BitVec 512} {salt : Salt}
    {seed : BitVec 256} {i t : ℕ} {T : Pt} {pub : LibsignalMsgPublicPart} {m : Plain ℓ}
    {w_top : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F}
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hsender : Party.senderOf t = Q)
    (hspqr_send : P.spqr.send (sC.base.pq Q) rq = some (pq', salt, pub.pqmsg))
    (hpq' : sC'.base.pq = Function.update sC.base.pq Q pq')
    (hhon' : sC'.base.honest =
      (LibsignalSim.toWire
        ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
          seed (i, (t, some T)) (pub, m))),
       ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
          seed (i, (t, some T)) (pub, m)))) :: sC.base.honest)
    (hchains : ∀ R t', t' ∈ (sC'.base.chains R).map (·.epoch) →
      t' ∈ (sC.base.chains R).map (·.epoch))
    (hw_top : CryptoVerification.SpqrV1Sync.SendTotal.TopStateW P.C.F K (sC.base.pq Q) w_top)
    (hpqmsg : ∀ h body,
      (signalWireCodec P.codec).parse
        ((LibsignalSim.toWire
          ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
            seed (i, (t, some T)) (pub, m)))).take
          ((LibsignalSim.toWire
            ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
              seed (i, (t, some T)) (pub, m)))).length - 8)) = some (h, body) →
      h.pqRatchet = pub.pqmsg)
    (hord_old : ∀ w₀ c₀, (w₀, c₀) ∈ sC.base.honest → Party.senderOf c₀.1.1 = Q → c₀.1.1 ≤ t)
    (hep_le : ∀ R, sC.base.mir.epoch R ≤ sC'.base.mir.epoch R) :
    EvictedSpurHistGameInv P K qep w_rem sC' :=
  ⟨Proofs.Refinement.spqrHistoryInv_preserve_send hInv.hhist hhon' hpq' hchains
    hsender hw_top (hspqr_eq ▸ hspqr_send) hpqmsg hord_old,
   (remSendEpochs_anti_epoch qep sC.base.mir sC'.base.mir hep_le).trans hInv.hw_rem⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_send_new_epoch
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    {qep w_rem : ℕ}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {Q : Party} {pq' : List (BitVec 8)} {rq : BitVec 512} {salt : Salt}
    {seed : BitVec 256} {i t : ℕ} {T : Pt} {pub : LibsignalMsgPublicPart} {m : Plain ℓ}
    {w_top : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F}
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hsender : Party.senderOf t = Q)
    (hspqr_send : P.spqr.send (sC.base.pq Q) rq = some (pq', salt, pub.pqmsg))
    (hpq' : sC'.base.pq = Function.update sC.base.pq Q pq')
    (hhon' : sC'.base.honest =
      (LibsignalSim.toWire
        ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
          seed (i, (t, some T)) (pub, m))),
       ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
          seed (i, (t, some T)) (pub, m)))) :: sC.base.honest)
    (hchains : ∀ R t', t' ∈ (sC'.base.chains R).map (·.epoch) →
      t' ∈ (sC.base.chains R).map (·.epoch))
    (hw_top : CryptoVerification.SpqrV1Sync.SendTotal.TopStateW P.C.F K (sC.base.pq Q) w_top)
    (hpqmsg : ∀ h body,
      (signalWireCodec P.codec).parse
        ((LibsignalSim.toWire
          ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
            seed (i, (t, some T)) (pub, m)))).take
          ((LibsignalSim.toWire
            ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
              seed (i, (t, some T)) (pub, m)))).length - 8)) = some (h, body) →
      h.pqRatchet = pub.pqmsg)
    (hord_old : ∀ w₀ c₀, (w₀, c₀) ∈ sC.base.honest → Party.senderOf c₀.1.1 = Q → c₀.1.1 ≤ t)
    (hs : Q.sendsIn (sC.base.mir.epoch Q + 1) = true)
    (hQ_le : sC.base.mir.epoch Q + 1 ≤ qep)
    (hother_le : sC.base.mir.epoch Q.other ≤ qep)
    (hep' : sC'.base.mir.epoch = Function.update sC.base.mir.epoch Q (sC.base.mir.epoch Q + 1)) :
    0 < w_rem ∧ EvictedSpurHistGameInv P K qep (w_rem - 1) sC' := by
  obtain ⟨hpos, hrem_eq⟩ := remSendEpochs_new_send_epoch qep sC.base.mir sC'.base.mir Q
    hs hQ_le hother_le hep'
  have hw_pos : 0 < w_rem := lt_of_lt_of_le hpos hInv.hw_rem
  have hw_rem' : remSendEpochs qep sC'.base.mir ≤ w_rem - 1 := by
    have := hInv.hw_rem
    omega
  have hhist' := Proofs.Refinement.spqrHistoryInv_preserve_send hInv.hhist hhon' hpq' hchains
    hsender hw_top (hspqr_eq ▸ hspqr_send) hpqmsg hord_old
  exact ⟨hw_pos, hhist', hw_rem'⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_deliver_existing_chain
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem} {ℓ : ℕ}
    {qep w_rem : ℕ}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {Q : Party} {w_wire : List (BitVec 8)} {t i : ℕ} {m : Plain ℓ}
    {ci : ℕ} {k_ratchet : PublicKey} {pq' : List (BitVec 8)}
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hreach : Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (sC.base.pq Q) pq')
    (hbase : sC'.base = (onAcceptPure qep Q w_wire true t i m (some ci) k_ratchet pq' sC.base).2)
    (hep_le : ∀ R, sC.base.mir.epoch R ≤ sC'.base.mir.epoch R) :
    EvictedSpurHistGameInv P K qep w_rem sC' :=
  ⟨hbase ▸ Proofs.Refinement.spqrHistoryInv_onAcceptPure_some P K qep Q w_wire true t i m ci
    k_ratchet pq' sC.base hInv.hhist hreach,
   (remSendEpochs_anti_epoch qep sC.base.mir sC'.base.mir hep_le).trans hInv.hw_rem⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistGameInv_deliver_new_chain
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem} {ℓ : ℕ}
    {qep w_rem : ℕ}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {Q : Party} {w_wire w : List (BitVec 8)} {t i : ℕ} {m : Plain ℓ}
    {k_ratchet : PublicKey} {pq' : List (BitVec 8)}
    {c : Fig8C Pt} {h : SignalHeader} {body : List (BitVec 8)} {salt : Salt}
    {w_acc : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F}
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hc_mem : (w, c) ∈ sC.base.honest)
    (ht_eq : t = c.1.1)
    (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hw_acc : CryptoVerification.SpqrV1Sync.SendTotal.TopStateW P.C.F K (sC.base.pq Q) w_acc)
    (hrecv : (spqrV1SessionUniformCoins P.C.F K).recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hbase : sC'.base = (onAcceptPure qep Q w_wire true t i m none k_ratchet pq' sC.base).2)
    (hep_le : ∀ R, sC.base.mir.epoch R ≤ sC'.base.mir.epoch R) :
    EvictedSpurHistGameInv P K qep w_rem sC' :=
  ⟨hbase ▸ Proofs.Refinement.spqrHistoryInv_onAcceptPure_none P K qep Q w_wire true t i m
    k_ratchet pq' sC.base w c h body salt w_acc hInv.hhist hc_mem ht_eq hc_sender hparse hw_acc
    hrecv,
   (remSendEpochs_anti_epoch qep sC.base.mir sC'.base.mir hep_le).trans hInv.hw_rem⟩

section CorrSimInvCX

open CryptoGames.LibsignalSM.Proofs.Refinement

omit [SampleableType Pt] in
private def clearWin {ℓ : ℕ}
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
  { g with win := false }

omit [SampleableType Pt] in
private theorem fwdPure_of_win_true
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (s : SimState (List (BitVec 8)) Pt ℓ) (Q : Party) (c' : Fig8C Pt)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : g.win = true) :
    fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1 s Q c' g =
      (none, g) := by
  unfold fwdPure deliverPure injectPure
  split <;> simp [hwin]

omit [SampleableType Pt] in
private theorem fwdCPure_inject_of_fwdPure_not_accepted
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hno_acc : ∀ t i m,
      (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
        x.1.base Q c' x.2.1).1 ≠ some (.accepted t i m))
    (hg_eq :
      { (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
          x.1.base Q c' x.2.1).2 with win := false } =
        { x.2.1 with win := false }) :
    (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' honestC c' x).2.1 = x.1 ∧
    { (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' honestC c' x).2.2.1 with
      win := false } = { x.2.1 with win := false } := by
  have hplain :
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' honestC c' x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' none c' x := by
    unfold fwdCPure
    cases honestC <;> simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hplain]
  unfold fwdCPure
  dsimp only
  rcases hfwd :
      fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
        x.1.base Q c' x.2.1 with ⟨res8, g'⟩
  rw [hfwd] at hno_acc hg_eq
  cases res8 with
  | none =>
    unfold onAnswerPure
    exact ⟨rfl, hg_eq⟩
  | some r8 =>
    cases r8 with
    | accepted t i m => exact False.elim (hno_acc t i m rfl)
    | rejected =>
      unfold onAnswerPure
      exact ⟨rfl, hg_eq⟩

private theorem fwdCPure_inject_of_epoch_lt
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hsafe : x.1.base.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hhon : ∀ wc ∈ x.1.base.honest, wc.1 = LibsignalSim.toWire wc.2)
    (hw : LibsignalSim.toWire c' = w)
    (htr : (x.1.base.mir.inTransit Q.other w).isSome = false)
    (htriv_eq : ∀ pos, x.2.1.trivial 3 pos = x.1.base.mir.trivial 3 pos)
    (hep_lt : x.1.base.mir.epoch Q < c'.1.1) :
    (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq' honestC c' x).2.1 = x.1 ∧
    clearWin (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false ci? T pq'
      honestC c' x).2.2.1 = clearWin x.2.1 := by
  unfold clearWin
  have hfwd :=
    fwdPure_of_inTransit_false (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
      SM.Config.h1 x.1.base Q w c' x.2.1 hhon hw htr
  refine fwdCPure_inject_of_fwdPure_not_accepted P ℓ Dh encPt encT idOf lam qep Q w ci? T pq'
    honestC c' x ?_ ?_
  · intro t i m
    rw [hfwd]
    unfold injectPure
    split
    · simp
    · cases hrec : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (x.2.1.st Q) c' with
      | none => simp
      | some val =>
        rcases val with ⟨st', t', i', pm⟩
        rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
          (x.2.1.st Q) c' hrec with ⟨ht', _⟩
        dsimp only
        split
        · simp
        · have htriv_f : x.1.base.mir.trivial 3 ⟨Q.other, t', i'⟩ = false :=
            trivial_false_of_newChain_inject hsafe hcomp Q ⟨Q.other, t', i'⟩
              (by dsimp only; omega)
          rw [htriv_eq, htriv_f]
          simp
  · rw [hfwd]
    unfold injectPure
    split
    · rfl
    · cases hrec : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (x.2.1.st Q) c' with
      | none => rfl
      | some val =>
        rcases val with ⟨st', t', i', pm⟩
        rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
          (x.2.1.st Q) c' hrec with ⟨ht', _⟩
        dsimp only
        split
        · rfl
        · have htriv_f : x.1.base.mir.trivial 3 ⟨Q.other, t', i'⟩ = false :=
            trivial_false_of_newChain_inject hsafe hcomp Q ⟨Q.other, t', i'⟩
              (by dsimp only; omega)
          rw [htriv_eq, htriv_f]
          simp only [Bool.false_eq_true, ↓reduceIte]
          split <;> rfl

/-- Combined game-level and refinement invariant for `kemFailSimImpl`. -/
def EvictedSpurHistSimInv
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r w_rem : ℕ)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  EvictedSpurHistGameInv P K qep w_rem sC ∧
  EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q r sC g

theorem evictedSpurHistSimInv_init
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hS : Proofs.Refinement.SpqrCLocal P.spqr q InvPQ)
    (b : Bool) (k : BitVec 256 × BitVec 256) (pqrKey : BitVec 256)
    (hcoll0 : ∃ eA₀ : BitVec 256, Dh.dh eA₀ Dh.base ≠ Dh.dh k.2 Dh.base) :
    EvictedSpurHistSimInv P K InvPQ ℓ Dh encPt encT idOf lam qep q q qep
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b) :=
  ⟨evictedSpurHistGameInv_init P K pqrKey qep,
   evictedSpurSimInv_init P InvPQ ℓ Dh encPt encT idOf lam qep q hX hS b k pqrKey hcoll0⟩

theorem kemFailSimImpl_deliver_eq_simRecvStepC
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (Q : Party) (w : List (BitVec 8))
    {z : Option (SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F)}
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, gh, tr))) :
    (z.1, (z.2.1, z.2.2.1)) =
      Proofs.Refinement.simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh) := by
  rw [kemFailSimImpl_deliver_run, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictAccEpoch_le_of_inWin_false
    {s : SimState (List (BitVec 8)) Pt ℓ} {Q : Party}
    (hinwQ : inReceiveOnlyEpoch s.mir Q = false)
    (hep_adj : ∀ P,
      (inReceiveOnlyEpoch s.mir P = true → s.mir.epoch P ≤ s.mir.epoch P.other) ∧
      (inReceiveOnlyEpoch s.mir P = false → s.mir.epoch P ≤ s.mir.epoch P.other + 1))
    (R : Party) :
    Proofs.Refinement.evictAccEpoch s.mir R ≤ s.mir.epoch Q := by
  have hOO : Q.other.other = Q := by cases Q <;> rfl
  by_cases hRQ : R = Q
  · subst hRQ
    unfold Proofs.Refinement.evictAccEpoch
    rw [hinwQ]
    simp
  · have hRO : R = Q.other := by cases R <;> cases Q <;> first | contradiction | rfl
    subst hRO
    unfold Proofs.Refinement.evictAccEpoch
    split
    · rename_i hinwO
      have hle := (hep_adj Q.other).1 hinwO
      rwa [hOO] at hle
    · rename_i hinwO
      have hle := (hep_adj Q.other).2 (Bool.eq_false_iff.mpr hinwO)
      rw [hOO] at hle
      omega

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictAccEpoch_and_honestBeforeEpoch_new_epoch_send
    {s s' : SimState (List (BitVec 8)) Pt ℓ}
    {Q : Party} {w_new : List (BitVec 8)} {c_new : Fig8C Pt}
    (hinwQ : inReceiveOnlyEpoch s.mir Q = true)
    (hinwQ' : inReceiveOnlyEpoch s'.mir Q = false)
    (hep : s'.mir.epoch = Function.update s.mir.epoch Q (s.mir.epoch Q + 1))
    (hhon : s'.honest = (w_new, c_new) :: s.honest)
    (hc_ep : c_new.1.1 = s.mir.epoch Q + 1)
    (hother_le : s.mir.epoch Q.other ≤ s.mir.epoch Q + 1) :
    ∀ R,
      Proofs.Refinement.evictAccEpoch s'.mir R = Proofs.Refinement.evictAccEpoch s.mir R ∧
      Proofs.Refinement.honestBeforeEpoch s'.honest (Proofs.Refinement.evictAccEpoch s'.mir R) =
        Proofs.Refinement.honestBeforeEpoch s.honest (Proofs.Refinement.evictAccEpoch s.mir R) := by
  intro R
  have hev_eq : Proofs.Refinement.evictAccEpoch s'.mir R =
      Proofs.Refinement.evictAccEpoch s.mir R := by
    by_cases hRQ : R = Q
    · subst hRQ
      unfold Proofs.Refinement.evictAccEpoch
      rw [hinwQ', hinwQ, hep, Function.update_self]
      simp
    · unfold Proofs.Refinement.evictAccEpoch inReceiveOnlyEpoch
      rw [hep, Function.update_of_ne hRQ]
  refine ⟨hev_eq, ?_⟩
  have hev_le : Proofs.Refinement.evictAccEpoch s.mir R ≤ c_new.1.1 := by
    rw [hc_ep]
    by_cases hRQ : R = Q
    · subst hRQ; unfold Proofs.Refinement.evictAccEpoch; split <;> omega
    · have hRO : R = Q.other := by cases R <;> cases Q <;> first | contradiction | rfl
      subst hRO; unfold Proofs.Refinement.evictAccEpoch; split <;> omega
  rw [hhon, hev_eq]
  exact Proofs.Refinement.honestBeforeEpoch_cons_of_le s.honest w_new c_new
    (Proofs.Refinement.evictAccEpoch s.mir R) hev_le

omit [SampleableType Pt] in
theorem kemFailSendStep_run_of_guard_fail {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (hfail :
      (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true ∨
      sC.base.mir.epMgmt 3 qep Q r.isSome = none ∨
      ∃ s₁, sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁ ∧
        (chal.isSome && !s₁.safeCh 3 Q) = true) :
    (kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run (sC, gh, tr) =
      pure (none, (sC, gh, tr)) := by
  unfold kemFailSendStep
  rw [stateT_run_get_bind_prod3]
  rcases hfail with hg1 | hg2 | ⟨s₁, hep, hg3⟩
  · simp [hg1]
  · by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true
    · simp [hg1]
    · simp [hg1, hg2]
  · by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true
    · simp [hg1]
    · simp [hg1, hep, hg3]

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_transmitQuery_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ((probeHook fig (qep + 1)).lift (SM.transmitQuery Q m rc)).run (g, false) =
      if g.win then pure (none, (g, false))
      else SM.samIfNec rc >>= fun cb =>
        let z := transmitPure fig 3 (qep + 1) Q m cb.1 cb.2 g
        pure (z.1, (z.2, false)) := by
  rw [probeHook_lift_run, ← bind_pure (SM.transmitQuery Q m rc)]
  unfold fig8ImplH1
  rw [simulateQ_transmitQuery_run fig 3 (qep + 1) SM.Config.h1 Q m rc pure g]
  split <;> simp [simulateQ_pure, StateT.run_pure]

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_challQuery_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ((probeHook fig (qep + 1)).lift (SM.challQuery Q m₀ m₁ rc)).run (g, false) =
      if g.win then pure (none, (g, false))
      else SM.samIfNec rc >>= fun cb =>
        let z := challPure fig 3 (qep + 1) SM.Config.h1 Q m₀ m₁ cb.1 cb.2 g
        pure (z.1, (z.2, false)) := by
  rw [probeHook_lift_run, ← bind_pure (SM.challQuery Q m₀ m₁ rc)]
  unfold fig8ImplH1
  rw [simulateQ_challQuery_run fig 3 (qep + 1) SM.Config.h1 Q m₀ m₁ rc pure g]
  split <;> simp [simulateQ_pure, StateT.run_pure]

theorem kemFailSendStep_rc_isSome {r : Option (BitVec 512)} {rc : Option (BitVec 256)}
    (hrc : (r = none ∧ rc = none) ∨ (∃ rq c_cka, r = some rq ∧ rc = some c_cka)) :
    rc.isSome = r.isSome := by
  rcases hrc with ⟨rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ <;> rfl

theorem stateT_run_kemFailSend_coins_support {σ α : Type}
    (r : Option (BitVec 512)) (st : σ)
    (k : BitVec 512 → Option (BitVec 256) → StateT σ ProbComp α)
    (z : α × σ)
    (hz : z ∈ support ((do
      let rq ← match r with
        | some rq => pure rq
        | none => liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512))
      let rc : Option (BitVec 256) ← match r with
        | some _ => some <$> liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        | none => pure none
      k rq rc).run st)) :
    ∃ rq rc,
      ((r = none ∧ rc = none) ∨ (∃ rq' c_cka, r = some rq' ∧ rq = rq' ∧ rc = some c_cka)) ∧
      z ∈ support ((k rq rc).run st) := by
  cases r with
  | none =>
    simp only [StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      pure_bind, bind_assoc] at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨rq, _, hz⟩
    exact ⟨rq, none, Or.inl ⟨rfl, rfl⟩, hz⟩
  | some rq =>
    simp only [StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      map_eq_bind_pure_comp, Function.comp_apply, pure_bind, bind_assoc] at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨c_cka, _, hz⟩
    exact ⟨rq, some c_cka, Or.inr ⟨rq, c_cka, rfl, rfl, rfl⟩, hz⟩

omit [SampleableType Pt] in
theorem kemFailSendStep_of_fig8_win {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hg_win : g.win = true)
    (z : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run
      (sC, (g, false), tr))) :
    z.1 = none ∧ z.2.1 = sC ∧ z.2.2.1 = (g, false) := by
  by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r
      sC (g, false) tr (Or.inl hg1), support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl, rfl⟩
  cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
  | none =>
    rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r
      sC (g, false) tr (Or.inr (Or.inl hep)), support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl, rfl⟩
  | some s₁ =>
    by_cases hg3 : (chal.isSome && !s₁.safeCh 3 Q) = true
    · rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r
        sC (g, false) tr (Or.inr (Or.inr ⟨s₁, hep, hg3⟩)),
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl, rfl⟩
    have hg1_f : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false :=
      Bool.eq_false_iff.mpr hg1
    have hg3_f : (chal.isSome && !s₁.safeCh 3 Q) = false := Bool.eq_false_iff.mpr hg3
    unfold kemFailSendStep at hz
    rw [stateT_run_get_bind_prod3] at hz
    simp only [hg1_f, Bool.false_eq_true, ↓reduceIte, hep, hg3_f] at hz
    obtain ⟨rq, rc, _, hz⟩ := stateT_run_kemFailSend_coins_support r (sC, (g, false), tr) _ z hz
    cases hmk : mkPub P sC.base Q rq
        (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
         else sC.base.pn Q) with
    | none =>
      simp only [hmk, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl, rfl⟩
    | some pq_pub =>
      rcases pq_pub with ⟨pq', pub⟩
      simp only [hmk, StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
        bind_pure_comp, map_eq_bind_pure_comp, Function.comp_apply,
        bind_assoc, pure_bind] at hz
      rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨⟨res_f, gh'⟩, hz_fig, hz⟩
      have hz_fig_eq : (res_f, gh') = (none, (g, false)) := by
        cases chal with
        | none =>
          rw [probeHook_lift_transmitQuery_run, ite_eq_left hg_win, support_pure,
            Set.mem_singleton_iff] at hz_fig
          exact hz_fig
        | some m₁ =>
          rw [probeHook_lift_challQuery_run, ite_eq_left hg_win, support_pure,
            Set.mem_singleton_iff] at hz_fig
          exact hz_fig
      rcases Prod.mk.injEq _ _ _ _ |>.mp hz_fig_eq with ⟨rfl, rfl⟩
      simp only [StateT.run_bind, StateT.run_set, pure_bind] at hz
      have hz' : z = (none, (sC, (g, false),
          { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand })) := hz
      subst hz'; exact ⟨rfl, rfl, rfl⟩

omit [SampleableType Pt] in
theorem probeHook_lift_send_support
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (pub : LibsignalMsgPublicPart) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (rc : Option (BitVec 256))
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hg_win : g.win = false)
    (z_fig : Option (Fig8C Pt) ×
      (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool))
    (hz : z_fig ∈ support
      (((probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)).lift
        (match chal with
         | none => SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
         | some m₁ => SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc)).run
        (g, false))) :
    ∃ c_cka : BitVec 256,
      (rc = none ∨ rc = some c_cka) ∧
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let f8 := chal.elim
        (transmitPure fig 3 (qep + 1) Q (pub, m₀) c_cka rc.isSome g)
        (fun m₁ => challPure fig 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁)
          c_cka rc.isSome g)
      z_fig = (f8.1, (f8.2, false)) := by
  cases chal with
  | none =>
    rw [probeHook_lift_transmitQuery_run] at hz
    cases rc with
    | none =>
      simp only [hg_win, Bool.false_eq_true, ↓reduceIte, SM.samIfNec, bind_assoc, pure_bind] at hz
      rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨c_cka, _, hz⟩
      simp only [support_pure, Set.mem_singleton_iff] at hz
      exact ⟨c_cka, Or.inl rfl, hz⟩
    | some c_cka =>
      simp only [hg_win, Bool.false_eq_true, ↓reduceIte, SM.samIfNec, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      exact ⟨c_cka, Or.inr rfl, hz⟩
  | some m₁ =>
    rw [probeHook_lift_challQuery_run] at hz
    cases rc with
    | none =>
      simp only [hg_win, Bool.false_eq_true, ↓reduceIte, SM.samIfNec, bind_assoc, pure_bind] at hz
      rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨c_cka, _, hz⟩
      simp only [support_pure, Set.mem_singleton_iff] at hz
      exact ⟨c_cka, Or.inl rfl, hz⟩
    | some c_cka =>
      simp only [hg_win, Bool.false_eq_true, ↓reduceIte, SM.samIfNec, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      exact ⟨c_cka, Or.inr rfl, hz⟩

omit [SampleableType Pt] in
theorem kemFailSendStep_support_of_guards
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false)
    (hg_win : g.win = false)
    (z : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run
      (sC, (g, false), tr))) :
    ∃ (rq : BitVec 512) (c_cka : BitVec 256),
      (r = none ∨ r = some rq) ∧
      let pn :=
        if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
        else sC.base.pn Q
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let tr' := stepKemFailSend P.C.F K tr Q rq
      match mkPub P sC.base Q rq pn with
      | none => z = (none, (sC, (g, false), { tr with cand := tr'.cand }))
      | some (pq', pub) =>
        let f8 := chal.elim
          (transmitPure fig 3 (qep + 1) Q (pub, m₀) c_cka r.isSome g)
          (fun m₁ => challPure fig 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁)
            c_cka r.isSome g)
        match f8.1 with
        | none => z = (none, (sC, (f8.2, false), { tr with cand := tr'.cand }))
        | some c =>
          let w := toWire c
          let rec' : SM.Record (Plain ℓ) (List (BitVec 8)) :=
            ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
          let base' : SimState (List (BitVec 8)) Pt ℓ :=
            { sC.base with
              mir := s₁.record 3 Q () rec' chal.isSome
              pq := Function.update sC.base.pq Q pq'
              pn := Function.update sC.base.pn Q pn
              honest := (w, c) :: sC.base.honest }
          z = (some w,
            (cxSend P Dh encPt encT idOf lam Q sC base' (some w), (f8.2, false), tr')) := by
  unfold kemFailSendStep at hz
  rw [stateT_run_get_bind_prod3] at hz
  simp only [hg1, Bool.false_eq_true, ↓reduceIte, hep, hg3] at hz
  obtain ⟨rq, rc, hrc, hz⟩ := stateT_run_kemFailSend_coins_support r (sC, (g, false), tr) _ z hz
  have hrc_some : rc.isSome = r.isSome :=
    kemFailSendStep_rc_isSome (hrc.imp id fun ⟨rq', c_cka, hr1, _, hrc1⟩ => ⟨rq', c_cka, hr1, hrc1⟩)
  have hr_or : r = none ∨ r = some rq :=
    hrc.imp (·.1) fun ⟨_, _, hr1, hrq, _⟩ => hrq ▸ hr1
  cases hmk : mkPub P sC.base Q rq
      (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
       else sC.base.pn Q) with
  | none =>
    simp only [hmk, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hz
    refine ⟨rq, 0, hr_or, ?_⟩
    dsimp only
    rw [hmk, hz]
  | some pq_pub =>
    rcases pq_pub with ⟨pq', pub⟩
    simp only [hmk, StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      bind_pure_comp, map_eq_bind_pure_comp, Function.comp_apply,
      bind_assoc, pure_bind] at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨res_f, gh'⟩, hz_fig, hz⟩
    obtain ⟨c_cka, _, hz_fig_eq⟩ :=
      probeHook_lift_send_support P ℓ Dh encPt encT idOf lam qep Q pub m₀ chal rc g hg_win
        (res_f, gh') hz_fig
    rw [hrc_some] at hz_fig_eq
    rcases Prod.mk.injEq _ _ _ _ |>.mp hz_fig_eq with ⟨hres_eq, hgh_eq⟩
    subst hres_eq hgh_eq
    refine ⟨rq, c_cka, hr_or, ?_⟩
    dsimp only
    rw [hmk]
    dsimp only
    split
    · next hf8 =>
      simp only [hf8, StateT.run_bind, StateT.run_set, pure_bind] at hz
      exact hz
    · next c hf8 =>
      simp only [hf8, StateT.run_bind, StateT.run_set, pure_bind] at hz
      exact hz

omit [DecidableEq Pt] [SampleableType Pt] in
theorem simSendStep_eq_of_mkPub_some
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (rq : BitVec 512) (c_cka : BitVec 256)
    (s : SimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (pq' : List (BitVec 8)) (pub : LibsignalMsgPublicPart) (c : Fig8C Pt)
    (hmk : mkPub P s Q rq
      (if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q) =
      some (pq', pub))
    (hf8 : (chal.elim
      (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
        (pub, m₀) c_cka bad g)
      (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad g)).1 = some c) :
    let f8 := chal.elim
      (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
        (pub, m₀) c_cka bad g)
      (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad g)
    let pn := if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q
    let w := toWire c
    let rec' : SM.Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
    let base' : SimState (List (BitVec 8)) Pt ℓ :=
      { s with
        mir := s₁.record 3 Q () rec' chal.isSome
        pq := Function.update s.pq Q pq'
        pn := Function.update s.pn Q pn
        honest := (w, c) :: s.honest }
    simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka (s, g) =
      (some w, (base', f8.2)) := by
  unfold simSendStep
  cases chal with
  | none =>
    simp only [hmk, Option.elim] at hf8 ⊢
    cases h : transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
      (pub, m₀) c_cka bad g
    rw [h] at hf8; cases hf8; rfl
  | some m₁ =>
    simp only [hmk, Option.elim] at hf8 ⊢
    cases h : challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
      SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad g
    rw [h] at hf8; cases hf8; rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem mkPub_eq_some_of_spqrCLocal
    {P : Params (List (BitVec 8)) (BitVec 512)} {Inv : ℕ → List (BitVec 8) → Prop} {q r : ℕ}
    (hS : SpqrCLocal P.spqr q Inv) (hr : 0 < r)
    (s : SimState (List (BitVec 8)) Pt ℓ) (Q : Party) (rq : BitVec 512) (pn : BitVec 32)
    (hpq : InvB Inv q r (s.pq Q)) :
    ∃ pq' salt pqMsg,
      P.spqr.send (s.pq Q) rq = some (pq', salt, pqMsg) ∧
      mkPub P s Q rq pn =
        some (pq',
          ⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == Party.A && s.unackA then P.addrAB else none⟩) := by
  rcases Option.isSome_iff_exists.mp (spqrCLocal_total hS hr (s.pq Q) rq hpq) with
    ⟨⟨pq', salt, pqMsg⟩, hspqr⟩
  exact ⟨pq', salt, pqMsg, hspqr, by simp [mkPub, hspqr]⟩

theorem f8_send_eq_some_of_sameMeta
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (pub : LibsignalMsgPublicPart) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (c_cka : BitVec 256) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (s : SimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hmeta : SameMeta s_R s g)
    (hep_mir : s.mir.epMgmt 3 qep Q bad = some s₁)
    (hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true) :
    ∃ s_fig8₁,
      g.epMgmt 3 (qep + 1) Q bad = some s_fig8₁ ∧
      s_fig8₁.st = g.st ∧
      let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let m_enc : Plain ℓ := chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)
      let out := sm.send (g.st Q) (pub, m_enc) c_cka
      chal.elim
        (transmitPure sm 3 (qep + 1) Q (pub, m₀) c_cka bad g)
        (fun m₁ => challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad g) =
        (some out.2,
          s_fig8₁.record 3 Q out.1
            ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, (pub, m_enc), out.2⟩ chal.isSome) := by
  rcases hmeta.epMgmt_some Q qep bad hep_mir with
    ⟨_, s_fig8₁, _, hep_fig8, _, hst_fig8₁, hmeta₁⟩
  refine ⟨s_fig8₁, hep_fig8, hst_fig8₁, ?_⟩
  cases hchal : chal with
  | none =>
    unfold transmitPure
    rw [hep_fig8]
    dsimp only [Option.elim, Option.isSome]
    rw [hst_fig8₁]
  | some m₁ =>
    have hsafe_f : (!s_fig8₁.safeCh 3 Q) = false := by
      rw [hmeta₁.safeCh_fig8 3 Q, hsafeCh (by simp [hchal])]; rfl
    have hcond_f :
        (!s_fig8₁.safeCh 3 Q ||
          !(SM.Config.h1 (Msg := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s_fig8₁.epoch Q)) = false := by
      rw [hsafe_f]; rfl
    have hmb : (if g.b = true then (pub, m₁) else (pub, m₀)) =
        (pub, if s_R.b = true then m₁ else m₀) := by
      rw [← hmeta.hb]; cases s_R.b <;> rfl
    dsimp only [Option.elim, Option.isSome]
    unfold challPure
    rw [hep_fig8]
    dsimp only
    rw [hcond_f, ite_eq_right Bool.false_ne_true, hst_fig8₁]
    change (let m := if g.b = true then (pub, m₁) else (pub, m₀);
      let out := (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q) m c_cka;
      (some out.2,
        s_fig8₁.record 3 Q out.1
          ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, m, out.2⟩ true)) = _
    rw [hmb]

theorem kemFailSendStep_support_eq_simSendStep
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r_coin : Option (BitVec 512))
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hmeta : SameMeta s_R sC.base { g with win := false })
    (hpq : InvB Inv q r (sC.base.pq Q))
    (z : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin).run
      (sC, (g, false), tr))) :
    (z.1 = none ∧ z.2.1 = sC ∧ z.2.2.1 = (g, false)) ∨
    (g.win = false ∧
      SM.noBobSendInEpoch0 sC.base.mir Q = true ∧
      ∃ s₁, sC.base.mir.epMgmt 3 qep Q r_coin.isSome = some s₁ ∧
        (chal.isSome = true → s₁.safeCh 3 Q = true) ∧
        ∃ (rq : BitVec 512) (c_cka : BitVec 256),
          (r_coin = none ∨ r_coin = some rq) ∧
          let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r_coin.isSome s₁
            rq c_cka (sC.base, g)
          z = (res.1,
            (cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1, (res.2.2, false),
              stepKemFailSend P.C.F K tr Q rq))) := by
  by_cases hg_win : g.win = true
  · exact Or.inl (kemFailSendStep_of_fig8_win P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal
      r_coin sC g tr hg_win z hz)
  have hg_win_f : g.win = false := Bool.eq_false_iff.mpr hg_win
  have hg_clear : { g with win := false } = g := by cases g; simp_all
  rw [hg_clear] at hmeta
  by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin
      sC (g, false) tr (Or.inl hg1), support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact Or.inl ⟨rfl, rfl, rfl⟩
  have hg1_f : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false :=
    Bool.eq_false_iff.mpr hg1
  have hnoBob : SM.noBobSendInEpoch0 sC.base.mir Q = true := by
    revert hg1_f; cases sC.base.stopped <;> cases sC.base.mir.win <;>
      cases SM.noBobSendInEpoch0 sC.base.mir Q <;> simp
  cases hep : sC.base.mir.epMgmt 3 qep Q r_coin.isSome with
  | none =>
    rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin
      sC (g, false) tr (Or.inr (Or.inl hep)), support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact Or.inl ⟨rfl, rfl, rfl⟩
  | some s₁ =>
    by_cases hg3 : (chal.isSome && !s₁.safeCh 3 Q) = true
    · rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin
        sC (g, false) tr (Or.inr (Or.inr ⟨s₁, hep, hg3⟩)),
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl ⟨rfl, rfl, rfl⟩
    have hg3_f : (chal.isSome && !s₁.safeCh 3 Q) = false := Bool.eq_false_iff.mpr hg3
    have hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true := by
      intro hch; revert hg3_f; rw [hch]; cases s₁.safeCh 3 Q <;> simp
    obtain ⟨rq, c_cka, hr_or, hz_eq⟩ :=
      kemFailSendStep_support_of_guards P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin s₁
        sC g tr hg1_f hep hg3_f hg_win_f z hz
    set pn :=
      if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
      else sC.base.pn Q
    obtain ⟨pq', salt, pqMsg, _, hmk⟩ :=
      mkPub_eq_some_of_spqrCLocal hS hr sC.base Q rq pn hpq
    set pub : LibsignalMsgPublicPart :=
      ⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == Party.A && sC.base.unackA then P.addrAB else none⟩
    obtain ⟨s_fig8₁, _, _, hf8_eq⟩ :=
      f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ chal c_cka
        r_coin.isSome s₁ s_R sC.base g hmeta hep hsafeCh
    have hf8_1 : (chal.elim
        (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
          (pub, m₀) c_cka r_coin.isSome g)
        (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka r_coin.isSome g)).1 =
        some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
          (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka).2 :=
      congrArg Prod.fst hf8_eq
    have hsim_eq := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ chal
      r_coin.isSome s₁ rq c_cka sC.base g pq' pub _ hmk hf8_1
    dsimp only at hz_eq hsim_eq
    rw [hmk] at hz_eq
    dsimp only at hz_eq
    rw [hf8_1] at hz_eq
    dsimp only at hz_eq
    refine Or.inr ⟨hg_win_f, hnoBob, s₁, rfl, hsafeCh, rq, c_cka, hr_or, ?_⟩
    dsimp only
    rw [hsim_eq, hz_eq]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem lAead_enc_parse_pqRatchet
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hrt : RoundTrip.RtHyp P ℓ)
    (Q : Party) (unackA : Bool) (pq_st pq' : List (BitVec 8)) (rq : BitVec 512) (salt : HKDF.Salt)
    (seed : BitVec 256) (i t : ℕ) (T : Pt) (pub : LibsignalMsgPublicPart) (m : Plain ℓ)
    (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg)) :
    ∀ h body,
      (signalWireCodec P.codec).parse
        ((LibsignalSim.toWire
          ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
            seed (i, (t, some T)) (pub, m)))).take
          ((LibsignalSim.toWire
            ((t, some T), (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
              seed (i, (t, some T)) (pub, m)))).length - 8)) = some (h, body) →
      h.pqRatchet = pub.pqmsg := by
  intro h body hparse
  let c : Fig8C Pt :=
    ((t, some T),
      (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
        seed (i, (t, some T)) (pub, m)))
  set h_hdr := lHeader encT i (t, some T) pub
  set mk := deriveMessageKeys P.C.F (some pub.salt) (keyToBytes32 seed)
  set body_enc := ((cbcPkcs7EncryptOnly P.C.E ℓ).enc (mk.1.1, mk.1.2) m).toList.flatMap blockToBytesLE
  set ser := (signalWireCodec P.codec).encode h_hdr body_enc
  set tag := (hmacScheme P.C.F).tag mk.2 ((lIds idOf t).toList ++ ser)
  have hw_eq : toWire c = ser ++ tagBytes tag := rfl
  have htag_len : (tagBytes tag).length = 8 := length_tagBytes tag
  have hw_sub : (toWire c).length - 8 = ser.length := by
    rw [hw_eq, List.length_append, htag_len]; omega
  have htake : (toWire c).take ((toWire c).length - 8) = ser := by
    rw [hw_sub, hw_eq, List.take_left]
  have hparse_hdr :
      (signalWireCodec P.codec).parse ((toWire c).take ((toWire c).length - 8)) =
        some (h_hdr, body_enc) := by
    rw [htake]
    refine RoundTrip.RtHyp.parse hrt h_hdr body_enc rfl
      (Or.inr ⟨_, _, _, _, hspqr_send⟩) ?_ (RoundTrip.length_cbcBody _)
    change RoundTrip.SentAddrs P pub.addrs
    rw [haddrs_pub]
    cases Q <;> cases unackA
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
  change (signalWireCodec P.codec).parse ((toWire c).take ((toWire c).length - 8)) =
    some (h, body) at hparse
  rw [hparse_hdr] at hparse
  injection hparse with hpair
  rcases Prod.mk.inj hpair with ⟨rfl, _⟩
  rfl

omit [SampleableType Pt] [DecidableEq Pt] in
theorem lFig8_send_eq_lAead_not_inWin
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (epExp : ℕ → BitVec 256) (Q : Party) (st : Fig8St Pt) (t : ℕ)
    (hst_id : st.id = Q) (htcur : st.tcur = t) (hsends : Q.sendsIn t = true)
    (hTcur : st.curCkaMsg = some (Dh.dh (epExp t) Dh.base))
    (v : FSAEAD.RatchetSenderState (BitVec 256)) (hvS : st.vS = some v)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (c_cka : BitVec 256) :
    ∃ seed i,
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) c_cka).2 =
        ((t, some (Dh.dh (epExp t) Dh.base)),
          (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
            seed (i, (t, some (Dh.dh (epExp t) Dh.base))) (pub, m))) := by
  have hnot_succ : st.id.sendsIn (st.tcur + 1) = false := by
    rw [hst_id, htcur]
    exact sendsIn_succ_of_sendsIn Q t hsends
  unfold lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG
  dsimp only
  rw [hnot_succ, ite_eq_right Bool.false_ne_true, hvS, htcur, hTcur]
  exact ⟨_, _, rfl⟩

omit [SampleableType Pt] [DecidableEq Pt] in
theorem lFig8_send_eq_lAead_inWin
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (st : Fig8St Pt) (t : ℕ) (T_other : Pt)
    (hst_id : st.id = Q) (htcur : st.tcur + 1 = t) (hsends : Q.sendsIn t = true)
    (hγ : st.γ = .pub T_other)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (c_cka : BitVec 256) :
    ∃ seed,
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) c_cka).2 =
        ((t, some (Dh.dh c_cka Dh.base)),
          (1, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
            seed (1, (t, some (Dh.dh c_cka Dh.base))) (pub, m))) := by
  have hsends_succ : st.id.sendsIn (st.tcur + 1) = true := by
    rw [hst_id, htcur]; exact hsends
  unfold lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG dhScheme
  dsimp only
  rw [hsends_succ, ite_eq_left rfl, hγ, htcur]
  dsimp only
  rw [Nat.zero_add]
  exact ⟨_, rfl⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem accept_epoch_le {St Msg C : Type}
    (mir : SM.GameState St Msg C) (Q R : Party) (st' : St) (pos : SM.Pos) :
    mir.epoch R ≤ (mir.accept Q st' pos).epoch R := by
  unfold SM.GameState.accept SM.GameState.delete
  dsimp only
  by_cases hR : R = Q
  · subst hR; simp [Function.update_self]
  · simp [Function.update_of_ne hR]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAcceptPure_epoch_le {PQ : Type}
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) (R : Party) :
    s.mir.epoch R ≤ (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.mir.epoch R := by
  unfold onAcceptPure
  dsimp only
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · exact le_rfl
    · split
      · exact accept_epoch_le s.mir Q R () ⟨Q.other, t, i⟩
      · exact le_rfl
  · simp only [↓reduceIte]
    split
    · exact le_rfl
    · exact accept_epoch_le s.mir Q R () _

theorem evalCK_some_some_epoch_eq
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt)
    {t i : ℕ} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = some (some (t, i, pm))) :
    t = c'.1.1 := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  unfold predictReceiveWithSnapshots predictReceive at heval
  cases hk : Kept.eval (fig := fig) (fs := fs) c' (sC.kept Q) with
  | some r_k =>
    rw [hk] at heval
    cases heval
    unfold Kept.eval at hk
    cases hfull : (sC.kept Q).full with
    | some st =>
      rw [hfull] at hk
      simp only [Option.some.injEq, Option.map_eq_some_iff] at hk
      rcases hk with ⟨⟨st', t₁, i₁, pm₁⟩, hrcv, hpair⟩
      rcases Prod.mk.inj hpair with ⟨rfl, _⟩
      exact (lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam st c' hrcv).1
    | none =>
      rw [hfull] at hk
      simp only [Option.map_eq_some_iff] at hk
      rcases hk with ⟨v, _, x, _, hpair⟩
      exact (congrArg Prod.fst hpair).symm
  | none =>
    rw [hk] at heval
    cases hs : sentEval (fs := fs) sC.sent c c' with
    | some r_s =>
      rw [hs] at heval
      cases heval
      unfold sentEval at hs
      simp only [Option.map_eq_some_iff] at hs
      rcases hs with ⟨e, _, x, _, hpair⟩
      exact (congrArg Prod.fst hpair).symm
    | none =>
      rw [hs] at heval
      simp only [Option.orElse_none, Option.map_eq_some_iff] at heval
      rcases heval with ⟨seed, _, hdec⟩
      unfold kDecryptFig8 at hdec
      split at hdec
      · simp only [Option.some.injEq] at hdec
        exact (congrArg Prod.fst hdec).symm
      · cases hdec

private theorem fwdEvictCPure_deliver_eq_of_not_honest
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (T : PublicKey) (pq' : List (BitVec 8)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ)
    (hsafe_or : c3a = false → x.1.base.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hc'_not_hon : ∀ wc ∈ x.1.base.honest, wc.2 ≠ c')
    (htriv_eq : ∀ pos, x.2.1.trivial 3 pos = x.1.base.mir.trivial 3 pos)
    (hep_lt : x.1.base.mir.epoch Q < c'.1.1) :
    (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w true T pq' c' x).2.1 = x.1 ∧
    clearWin (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w true T pq' c' x).2.2.1 =
      clearWin x.2.1 := by
  unfold fwdEvictCPure
  split
  · exact ⟨rfl, rfl⟩
  · rename_i hnot_probe
    have hsafe : x.1.base.mir.safeInj 3 = true := by
      cases hc3a : c3a
      · exact hsafe_or hc3a
      · subst hc3a
        revert hnot_probe
        cases x.1.base.mir.safeInj 3 <;> simp
    have hfwd :
        fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
          x.1.base Q c' x.2.1 =
        injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
          Q c' x.2.1 := by
      unfold fwdPure
      have hany :
          x.1.base.honest.any
            (fun wc => decide (wc.2 = c') && (x.1.base.mir.inTransit Q.other wc.1).isSome) =
          false := by
        rw [List.any_eq_false]
        intro wc hwc
        simp [hc'_not_hon wc hwc]
      rw [hany]
      rfl
    unfold fwdCPure clearWin
    dsimp only
    rw [hfwd]
    unfold injectPure
    split
    · unfold onAnswerPure; exact ⟨rfl, rfl⟩
    · cases hrec :
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (x.2.1.st Q) c' with
      | none => unfold onAnswerPure; exact ⟨rfl, rfl⟩
      | some val =>
        rcases val with ⟨st', t', i', pm⟩
        rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
          (x.2.1.st Q) c' hrec with ⟨ht', _⟩
        dsimp only
        split
        · unfold onAnswerPure; exact ⟨rfl, rfl⟩
        · have htriv_f : x.1.base.mir.trivial 3 ⟨Q.other, t', i'⟩ = false :=
            trivial_false_of_newChain_inject hsafe hcomp Q ⟨Q.other, t', i'⟩
              (by dsimp only; omega)
          rw [htriv_eq, htriv_f]
          simp only [Bool.false_eq_true, ↓reduceIte]
          split <;> (unfold onAnswerPure; exact ⟨rfl, rfl⟩)

theorem fwdCPure_deliver_base_cases
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ) :
    let s' := (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w true ci? T pq' honestC c' x).2.1.base
    s' = x.1.base ∨
      ∃ i m, s' = (onAcceptPure qep Q w true c'.1.1 i m ci? T pq' x.1.base).2 := by
  have hplain :
      (let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
       let z := fwdPure fig 3 (qep + 1) SM.Config.h1 x.1.base Q c' x.2.1
       let a := onAnswerPure qep Q w true ci? T pq' z.1 x.1.base
       a.2) = x.1.base ∨
      ∃ i m,
        (let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
         let z := fwdPure fig 3 (qep + 1) SM.Config.h1 x.1.base Q c' x.2.1
         let a := onAnswerPure qep Q w true ci? T pq' z.1 x.1.base
         a.2) = (onAcceptPure qep Q w true c'.1.1 i m ci? T pq' x.1.base).2 := by
    dsimp only
    cases hz : (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        SM.Config.h1 x.1.base Q c' x.2.1).1 with
    | none => exact Or.inl rfl
    | some r8 =>
      cases r8 with
      | rejected => exact Or.inl rfl
      | accepted t₁ i₁ pm₁ =>
        have ht₁ : t₁ = c'.1.1 :=
          fwdPure_accepted_epoch_eq P ℓ Dh encPt encT idOf lam qep x.1.base Q c' x.2.1 hz
        subst ht₁
        exact Or.inr ⟨i₁, (pm₁.map (·.2)).getD default, rfl⟩
  unfold fwdCPure
  dsimp only
  cases honestC with
  | none => exact hplain
  | some c₀ =>
    dsimp only
    split
    · cases heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) P x.1 Q w c₀ c' with
      | none => exact Or.inl rfl
      | some ev =>
        cases ev with
        | none => exact Or.inl rfl
        | some tip =>
          rcases tip with ⟨t₁, i₁, pm₁⟩
          dsimp only
          have ht₁ : t₁ = c'.1.1 :=
            evalCK_some_some_epoch_eq P ℓ Dh encPt encT idOf lam x.1 Q w c₀ c' heval
          subst ht₁
          split
          · exact Or.inr ⟨i₁, pm₁.2, rfl⟩
          · exact Or.inl rfl
    · exact hplain

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAcceptPure_deliver_honest_and_mir {PQ : Type}
    (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    let s' := (onAcceptPure qep Q w true t i m ci? T pq' s).2
    s'.honest = s.honest ∧
      (s'.mir = s.mir ∨
        ∃ r, s.mir.inTransit Q.other w = some r ∧ s'.mir = s.mir.accept Q () r.pos) := by
  unfold onAcceptPure
  dsimp only
  simp only [↓reduceIte]
  cases htr : s.mir.inTransit Q.other w with
  | none => exact ⟨rfl, Or.inl rfl⟩
  | some r => exact ⟨rfl, Or.inr ⟨r, rfl, rfl⟩⟩

theorem simRecvStepC_deliver_honest_and_mir
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    let s' := (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)).2.1.base
    s'.honest = sC.base.honest ∧
      (s'.mir = sC.base.mir ∨
        ∃ r, sC.base.mir.inTransit Q.other w = some r ∧
          s'.mir = sC.base.mir.accept Q () r.pos) := by
  have hfwd : ∀ c3a ci? T pq' honestC c' (x : JointC (List (BitVec 8)) Pt ℓ),
      x.1.base.honest = sC.base.honest → x.1.base.mir = sC.base.mir →
      let s' :=
        (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w true ci? T pq' honestC c' x).2.1.base
      s'.honest = sC.base.honest ∧
        (s'.mir = sC.base.mir ∨
          ∃ r, sC.base.mir.inTransit Q.other w = some r ∧
            s'.mir = sC.base.mir.accept Q () r.pos) := by
    intro c3a ci? T pq' honestC c' x hhon hmir
    rcases fwdCPure_deliver_base_cases P ℓ Dh encPt encT idOf lam qep c3a Q w ci? T pq'
        honestC c' x with h1 | ⟨i₁, m₁, h2⟩
    · exact ⟨(congrArg (·.honest) h1).trans hhon, Or.inl ((congrArg (·.mir) h1).trans hmir)⟩
    · obtain ⟨hh, hm⟩ := onAcceptPure_deliver_honest_and_mir qep Q w c'.1.1 i₁ m₁ ci? T pq' x.1.base
      rw [hhon] at hh
      rw [hmir] at hm
      exact ⟨(congrArg (·.honest) h2).trans hh, (congrArg (·.mir) h2) ▸ hm⟩
  have hev_fwd : ∀ c3a T pq' c' (x : JointC (List (BitVec 8)) Pt ℓ),
      x.1.base.honest = sC.base.honest → x.1.base.mir = sC.base.mir →
      let s' := (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w true T pq' c' x).2.1.base
      s'.honest = sC.base.honest ∧
        (s'.mir = sC.base.mir ∨
          ∃ r, sC.base.mir.inTransit Q.other w = some r ∧
            s'.mir = sC.base.mir.accept Q () r.pos) := by
    intro c3a T pq' c' x hhon hmir
    unfold fwdEvictCPure
    dsimp only
    split
    · exact ⟨hhon, Or.inl hmir⟩
    · exact hfwd false none T pq' none c' x hhon hmir
  unfold simRecvStepC simRecvStepCGen
  by_cases hst : sC.base.stopped = true
  · simp [hst]
  simp only [hst, Bool.false_eq_true, ↓reduceIte]
  by_cases hwin : sC.base.mir.win = true
  · simp [hwin]
  simp only [hwin, Bool.false_eq_true, ↓reduceIte]
  by_cases htr : (sC.base.mir.inTransit Q.other w).isNone = true
  · simp [htr]
  simp only [htr, Bool.and_false, Bool.not_true, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : w.length < 9
  · simp [hlen]
  simp only [hlen, ↓reduceIte]
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact ⟨rfl, Or.inl rfl⟩
  | some hb =>
    rcases hb with ⟨h, body⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · simp [haddr]
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
    · simp [hpan]
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact ⟨rfl, Or.inl rfl⟩
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        split
        · exact ⟨rfl, Or.inl rfl⟩
        · exact hfwd true _ _ _ _ _ (sC, gh) rfl rfl
      | none =>
        dsimp only
        have hstop : sC.base.stopped = false := Bool.eq_false_iff.mpr hst
        have hs_stop : { sC.base with amb := sC.base.amb + 1, stopped := false } =
            { sC.base with amb := sC.base.amb + 1 } := by
          cases h_s : sC.base; rw [h_s] at hstop; subst hstop; rfl
        simp only [hs_stop]
        let x₁ : JointC (List (BitVec 8)) Pt ℓ :=
          if inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
            ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, gh)
          else (sC, gh)
        have hx1_hon : x₁.1.base.honest = sC.base.honest := by
          dsimp only [x₁]; split <;> rfl
        have hx1_mir : x₁.1.base.mir = sC.base.mir := by
          dsimp only [x₁]; split <;> rfl
        split
        · exact ⟨rfl, Or.inl rfl⟩
        · split
          · exact ⟨rfl, Or.inl rfl⟩
          · split
            · exact ⟨hx1_hon, Or.inl hx1_mir⟩
            · cases hT : decT h.senderRatchetKey with
              | none => dsimp only; exact ⟨hx1_hon, Or.inl hx1_mir⟩
              | some T =>
                dsimp only
                split
                · exact hev_fwd true _ _ _ x₁ hx1_hon hx1_mir
                · exact hfwd true none _ _ _ _ x₁ hx1_hon hx1_mir

/-- No-forgery invariant on evicted honest wires at party `Q`. -/
def EvictedOnlyNoForgeAt {PQ PQC : Type}
    (P : Params PQ PQC) (decT : PublicKey → Option Pt)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) : Prop :=
  ∀ w c h body pq' salt,
    (w, c) ∈ sC.base.honest →
    Party.senderOf c.1.1 = Q.other →
    (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body) →
    P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt) →
    (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) = none →
    c.1.1 ≠ sC.base.mir.epoch Q + 1 →
    inReceiveOnlyEpoch sC.base.mir Q = false →
    ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1) →
    sC.base.mir.safeInj 3 = false →
    ∀ T, decT h.senderRatchetKey = some T →
      fig.receive (g.st Q)
        ((sC.base.mir.epoch Q + 1, some T),
          (h.counter.toNat + 1,
            ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) = none

/-- Lazy-coin variant of `SimInvC` bounding honest and collision epochs by the current maximum epoch. -/
structure SimInvCLazy {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool)
    (epExp : ℕ → BitVec 256) : Prop where
  hmeta : SameMeta s_R s s_fig8
  hcomp : ∀ p ∈ s.mir.comp, SM.healedBy s.mir.tL 3 p.epoch = false
  hec : ValidEagerCoins s.mir ec
  hwinBefore : ∀ j < s.amb, winBefore j = false
  hamb : s.amb + r ≤ q
  hamb_strict : (0 < s.mir.epoch .A ∨ 0 < s.mir.epoch .B) → s.amb + r < q
  hidx_le : ∀ Q, s.mir.idx Q + r ≤ q
  hhon_len : s.honest.length + r ≤ q
  hep_le : ∀ Q, s.mir.epoch Q ≤ qep
  hep_adj : ∀ Q, (inReceiveOnlyEpoch s.mir Q = true → s.mir.epoch Q ≤ s.mir.epoch Q.other) ∧
    s.mir.epoch Q ≤ s.mir.epoch Q.other + 1
  hst_R : ∀ Q,
    s_R.st Q = expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s Q (s_fig8.st Q) (ec Q)
  hst_id : ∀ Q, (s_fig8.st Q).id = Q
  htcur : ∀ Q, (s_fig8.st Q).tcur = s.mir.epoch Q
  hepExp0 : epExp 0 = x₀
  hspur : ∀ Q, ∃ rk_base T_base,
    (inReceiveOnlyEpoch s.mir Q = true →
      (s_fig8.st Q).root = rk_base ∧
      (s_fig8.st Q).γ = .pub T_base ∧
      T_base ≠ 0 ∧
      epExp (s.mir.epoch Q + 1) = ec Q) ∧
    (inReceiveOnlyEpoch s.mir Q = false →
      (s_fig8.st Q).γ = .exp (epExp (s.mir.epoch Q)) ∧
      (0 < s.mir.epoch Q →
        (s_fig8.st Q).root =
          (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s.mir.epoch Q)) T_base))).1 ∧
        (s_fig8.st Q).curCkaMsg = some (Dh.dh (epExp (s.mir.epoch Q)) Dh.base)) ∧
      ∃ vS, (s_fig8.st Q).vS = some vS ∧ vS.lastIndex = s.mir.idx Q)
  hchainsA : ChainsEpochInvA (s.mir.epoch .A) (s.chains .A)
  hchainsA_ep : (s.chains .A).map (·.epoch) = epListA (s.mir.epoch .A / 2)
  hchainsB_ep : (s.chains .B).map (·.epoch) = epListB ((s.mir.epoch .B + 1) / 2)
  hchainsB_none : ∀ g ∈ s.chains .B, g.key.isNone = false
  hcorrB0 : (.B, 0) ∈ s.mir.corrs → ∀ g ∈ s.chains .A, g.key.isNone = false
  hchains_sync : ∀ Q g, g ∈ s.chains Q →
    g.epoch ≤ s.mir.epoch Q ∧
    Q.sendsIn g.epoch = false ∧
    (if g.key.isNone then some (encT (Dh.dh x₀ Dh.base)) else g.key) =
      some (encT (Dh.dh (epExp g.epoch) Dh.base)) ∧
    ∃ v, (s_fig8.st Q).vR g.epoch = some v ∧ ChainSync g v
  hhon : ∀ wc ∈ s.honest,
    HonestEntryInvC P Inv Dh encT epExp wc ∧
    wc.2.1.1 ≤ max (s.mir.epoch .A) (s.mir.epoch .B) ∧
    (Party.senderOf wc.2.1.1).sendsIn wc.2.1.1 = true ∧
    wc.2.1.1 ≤ s.mir.epoch (Party.senderOf wc.2.1.1)
  htrans_hon : ∀ rec_f ∈ s_fig8.trans,
    (LibsignalSim.toWire rec_f.ct, rec_f.ct) ∈ s.honest ∧
    rec_f.pos.sender = Party.senderOf rec_f.ct.1.1 ∧
    rec_f.pos.epoch = rec_f.ct.1.1 ∧
    rec_f.pos.idx = rec_f.ct.2.1
  hcoll : ∀ t₁ t₂,
    t₁ ≤ max (s.mir.epoch .A) (s.mir.epoch .B) →
    t₂ ≤ max (s.mir.epoch .A) (s.mir.epoch .B) →
    Dh.dh (epExp t₁) Dh.base = Dh.dh (epExp t₂) Dh.base → t₁ = t₂
  hpqInv : ∀ Q, Inv (s.pq Q)

/-- Extended lazy-coin refinement invariant on `LibsignalToModularSchemeSimState`. -/
structure SimInvCXLazy {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool)
    (epExp : ℕ → BitVec 256) : Prop where
  hsim : SimInvCLazy P (InvB Inv q r) ℓ Dh encPt encT qep q r x₀ s_R sC.base s_fig8 ec winBefore
    epExp
  huniq : PosUniq sC.base
  hkept : KeptInv P Dh encPt encT idOf lam sC s_fig8
  hidx : HonestIdxLe sC.base
  hsync : EpochSync P Dh encPt encT idOf sC.base.honest sC.sent sC.snaps s_fig8 epExp

omit [DecidableEq Pt] [SampleableType Pt] in
theorem simInvC_toLazy {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    {P : Params PQ PQC} {Inv : PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (h : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp) :
    SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp :=
  { h with
    hspur := fun Q => by
      rcases h.hspur Q with ⟨rk_base, T_base, h1, h2, _⟩
      exact ⟨rk_base, T_base, h1, h2⟩
    hhon := fun wc hwc => by
      rcases h.hhon wc hwc with ⟨h1, _, h3, h4⟩
      refine ⟨h1, ?_, h3, h4⟩
      cases hS : Party.senderOf wc.2.1.1 <;>
        [exact Nat.le_trans (hS ▸ h4) (Nat.le_max_left _ _);
         exact Nat.le_trans (hS ▸ h4) (Nat.le_max_right _ _)]
    hcoll := fun t₁ t₂ h₁ h₂ hdh => by
      have hle : ∀ R, s.mir.epoch R ≤ maxActiveEp s.mir R := fun R => by
        dsimp [maxActiveEp]; split <;> omega
      have hmax : max (s.mir.epoch .A) (s.mir.epoch .B) ≤
          max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) :=
        max_le_max (hle .A) (hle .B)
      exact h.hcoll t₁ t₂ (Nat.le_trans h₁ hmax) (Nat.le_trans h₂ hmax) hdh }

omit [DecidableEq Pt] [SampleableType Pt] in
theorem simInvCX_toLazy {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    {P : Params PQ PQC} {Inv : ℕ → PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {qep q r : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (h : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp) :
    SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp :=
  ⟨simInvC_toLazy h.hsim, h.huniq, h.hkept, h.hidx, h.hsync⟩

omit [DecidableEq Pt] [SampleableType Pt] in
theorem simInvCXLazy_mono_r
    {P : Params (List (BitVec 8)) (BitVec 512)}
    {Inv : ℕ → List (BitVec 8) → Prop} {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r r' : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8))}
    {sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (h : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hr : r' ≤ r) :
    SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R sC s_fig8 ec winBefore epExp := by
  refine ⟨?_, h.huniq, h.hkept, h.hidx, h.hsync⟩
  have hsim := h.hsim
  exact
    { hsim with
      hamb := by have := hsim.hamb; omega
      hamb_strict := fun hpos => by have := hsim.hamb_strict hpos; omega
      hidx_le := fun Q => by have := hsim.hidx_le Q; omega
      hhon_len := by have := hsim.hhon_len; omega
      hhon := hsim.hhon
      hpqInv := fun Q => InvB.mono hr (hsim.hpqInv Q) }

/-- Validity of the prior-accept SPQR witness `w_acc` at party `Q`. -/
def ValidEvictAccWitness
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem) {ℓ : ℕ}
    (s : SimState (List (BitVec 8)) Pt ℓ) (Q : Party)
    (w_acc : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F) : Prop :=
  1 ≤ Proofs.Refinement.evictAccEpoch s.mir Q →
    ∃ w_acc_wire c_acc h_acc body_acc pq_acc pq_acc' salt_acc,
      (w_acc_wire, c_acc) ∈ s.honest ∧
      c_acc.1.1 = Proofs.Refinement.evictAccEpoch s.mir Q ∧
      Party.senderOf c_acc.1.1 = Q.other ∧
      (signalWireCodec P.codec).parse (w_acc_wire.take (w_acc_wire.length - 8)) =
        some (h_acc, body_acc) ∧
      CryptoVerification.SpqrV1Sync.SendTotal.TopStateW P.C.F K pq_acc w_acc ∧
      (spqrV1SessionUniformCoins P.C.F K).recv pq_acc h_acc.pqRatchet = .ok (pq_acc', salt_acc) ∧
      Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) pq_acc (s.pq Q)

/-- Validity of the base root key and ratchet key witness `(rk_base, T_base)` at party `Q`. -/
def ValidSpurBase {PQ PQC : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (epExp : ℕ → BitVec 256)
    (Q : Party) (rk_base : Ratchet.RootKey) (T_base : Pt) : Prop :=
  (inReceiveOnlyEpoch s.mir Q = true →
    (s_fig8.st Q).root = rk_base ∧
    (s_fig8.st Q).γ = .pub T_base ∧
    T_base ≠ 0) ∧
  (inReceiveOnlyEpoch s.mir Q = false →
    (s_fig8.st Q).γ = .exp (epExp (s.mir.epoch Q)) ∧
    (0 < s.mir.epoch Q →
      (s_fig8.st Q).root =
        (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s.mir.epoch Q)) T_base))).1 ∧
      (s_fig8.st Q).curCkaMsg = some (Dh.dh (epExp (s.mir.epoch Q)) Dh.base)) ∧
    ∃ vS, (s_fig8.st Q).vS = some vS ∧ vS.lastIndex = s.mir.idx Q)

/-- Lazy-coin refinement invariant excluding spurious keys on evicted wires. -/
def EvictedSpurSimInvLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  ∃ x₀ s_R ec winBefore epExp,
    SimInvCXLazy P InvPQ ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { g with win := false } ec winBefore epExp ∧
    ∀ Q, ∃ w_acc rk_base T_base,
      ValidEvictAccWitness P K sC.base Q w_acc ∧
      ValidSpurBase P ℓ Dh encPt sC.base { g with win := false } epExp Q rk_base T_base ∧
      (inReceiveOnlyEpoch sC.base.mir Q = false →
        spurBadList P encPt Dh Q rk_base T_base
          (Proofs.Refinement.evictedSpurCandList P epExp w_acc
            (Proofs.Refinement.honestBeforeEpoch sC.base.honest
              (Proofs.Refinement.evictAccEpoch sC.base.mir Q)))
          (epExp (sC.base.mir.epoch Q)) = false)

/-- Combined game-level and lazy-coin refinement invariant for `kemFailSimImpl`. -/
def EvictedSpurHistSimInvLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r w_rem : ℕ)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  EvictedSpurHistGameInv P K qep w_rem sC ∧
  EvictedSpurSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r sC g

omit [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurSimInvLazy_mono_r
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem}
    {Inv : ℕ → List (BitVec 8) → Prop} {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r r' : ℕ}
    {sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (h : EvictedSpurSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r sC g)
    (hr : r' ≤ r) :
    EvictedSpurSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r' sC g := by
  rcases h with ⟨x₀, s_R, ec, winBefore, epExp, hsim, hno_spur⟩
  exact ⟨x₀, s_R, ec, winBefore, epExp, simInvCXLazy_mono_r hsim hr, hno_spur⟩

omit [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurHistSimInvLazy_mono_r
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem}
    {Inv : ℕ → List (BitVec 8) → Prop} {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r r' w_rem : ℕ}
    {sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (h : EvictedSpurHistSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r w_rem sC g)
    (hr : r' ≤ r) :
    EvictedSpurHistSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r' w_rem sC g :=
  ⟨h.1, evictedSpurSimInvLazy_mono_r h.2 hr⟩

omit [DecidableEq Pt] [SampleableType Pt] in
theorem mem_chains_evictAccEpoch_of_simInvCLazy {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    {P : Params PQ PQC} {Inv : PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r : ℕ}
    {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hsim : SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (hge : 1 ≤ Proofs.Refinement.evictAccEpoch s.mir Q) :
    Proofs.Refinement.evictAccEpoch s.mir Q ∈ (s.chains Q).map (·.epoch) := by
  unfold Proofs.Refinement.evictAccEpoch at hge ⊢
  cases hinw : inReceiveOnlyEpoch s.mir Q <;> rw [hinw] at hge
  · simp only [Bool.false_eq_true, ↓reduceIte] at hge ⊢
    have hQ_sends : Q.sendsIn (s.mir.epoch Q) = true := by simpa [inReceiveOnlyEpoch] using hinw
    have hrecv_pred : Q.sendsIn (s.mir.epoch Q - 1) = false := by
      cases Q <;> simp [Party.sendsIn] at hQ_sends ⊢ <;> omega
    exact mem_chains_epoch_of_adj Q (s.mir.epoch Q) (s.mir.epoch Q - 1) (s.chains Q)
      (fun hA => hA ▸ hsim.hchainsA_ep) (fun hB => hB ▸ hsim.hchainsB_ep)
      (by omega) (by omega) (by omega) hrecv_pred
  · simp only [↓reduceIte] at hge ⊢
    have hrecv_cur : Q.sendsIn (s.mir.epoch Q) = false := by simpa [inReceiveOnlyEpoch] using hinw
    exact mem_chains_epoch_of_adj Q (s.mir.epoch Q) (s.mir.epoch Q) (s.chains Q)
      (fun hA => hA ▸ hsim.hchainsA_ep) (fun hB => hB ▸ hsim.hchainsB_ep)
      (by omega) (by omega) (by omega) hrecv_cur

omit [DecidableEq Pt] [SampleableType Pt] in
theorem EvictedSpurHistSimInv.toLazy
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem}
    {InvPQ : ℕ → List (BitVec 8) → Prop}
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r w_rem : ℕ}
    {sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (h : EvictedSpurHistSimInv P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g) :
    EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨x₀, s_R, ec, winBefore, epExp, hsimCX, hno_spur⟩
  have hlazy := simInvCX_toLazy hsimCX
  refine ⟨x₀, s_R, ec, winBefore, epExp, hlazy, fun Q => ?_⟩
  rcases hlazy.hsim.hspur Q with ⟨rk_base, T_base, hinw_t, hinw_f⟩
  have hbase : ValidSpurBase P ℓ Dh encPt sC.base { g with win := false } epExp Q rk_base T_base :=
    ⟨fun hinw => ⟨(hinw_t hinw).1, (hinw_t hinw).2.1, (hinw_t hinw).2.2.1⟩, hinw_f⟩
  by_cases hact : 1 ≤ Proofs.Refinement.evictAccEpoch sC.base.mir Q
  · have hmem_ch := mem_chains_evictAccEpoch_of_simInvCLazy hlazy.hsim Q hact
    obtain ⟨w_acc_wire, c_acc, h_acc, body_acc, pq_acc, pq_acc', salt_acc, w_acc,
        hc_acc_mem, hc_acc_eq, hc_acc_sender, hparse_acc, hw_acc, hrecv_acc, hreach₀⟩ :=
      h.1.hhist.hchain_acc Q (Proofs.Refinement.evictAccEpoch sC.base.mir Q) hmem_ch hact
    refine ⟨w_acc, rk_base, T_base, fun _ => ⟨w_acc_wire, c_acc, h_acc, body_acc, pq_acc, pq_acc',
      salt_acc, hc_acc_mem, hc_acc_eq, hc_acc_sender, hparse_acc, hw_acc, hrecv_acc, hreach₀⟩,
      hbase, hno_spur Q w_acc rk_base T_base⟩
  · have ⟨n, _, hI⟩ : ∃ n, n + r ≤ q ∧ InvPQ n (sC.base.pq Q) := hlazy.hsim.hpqInv Q
    obtain ⟨w_top, _⟩ := hInv_top n _ hI
    exact ⟨w_top, rk_base, T_base, fun hge => absurd hge hact, hbase,
      hno_spur Q w_top rk_base T_base⟩

theorem not_mem_chains_epoch_of_findIdx_noneCLazy {PQ PQC : Type}
    [Inhabited PQ] [SampleableType PQC]
    {P : Params PQ PQC} {Inv : PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r : ℕ}
    {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hsim : SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt) (h : SignalHeader) (body : List (BitVec 8))
    (hc_mem : (w, c) ∈ s.honest)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hfind : (s.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) = none) :
    c.1.1 ∉ (s.chains Q).map (·.epoch) := by
  rcases hsim.hhon (w, c) hc_mem with ⟨hc_inv, _, _, _⟩
  have hc_ge1 : 1 ≤ c.1.1 := hc_inv.2.2.1
  rcases Proofs.Refinement.honestEntryInvC_eq_raw P Inv Dh encT epExp hc_inv hparse with
    ⟨_, hsrk, _, _⟩
  intro hmem_ep
  rcases List.mem_map.mp hmem_ep with ⟨g₀, hg₀, hep_eq⟩
  have hnone : g₀.key.isNone = false := by
    cases Q with
    | A =>
      cases hn : g₀.key.isNone
      · rfl
      · have h0 := hsim.hchainsA.1 g₀ hg₀ hn
        omega
    | B => exact hsim.hchainsB_none g₀ hg₀
  have hkey_sync := (hsim.hchains_sync Q g₀ hg₀).2.2.1
  simp only [hnone, Bool.false_eq_true, ↓reduceIte, hep_eq, ← hsrk] at hkey_sync
  have hnone_iff := List.findIdx?_eq_none_iff.mp hfind g₀ hg₀
  simp [hkey_sync] at hnone_iff

theorem mem_honestBeforeEpoch_of_evicted_simInvCLazy {PQ PQC : Type}
    [Inhabited PQ] [SampleableType PQC]
    {P : Params PQ PQC} {Inv : PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r : ℕ}
    {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hsim : SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (hinw : inReceiveOnlyEpoch s.mir Q = false)
    (w : List (BitVec 8)) (c : Fig8C Pt) (h : SignalHeader) (body : List (BitVec 8))
    (hc_mem : (w, c) ∈ s.honest)
    (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hfind : (s.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 ≠ s.mir.epoch Q + 1) :
    1 < s.mir.epoch Q ∧
      s.mir.epoch Q - 1 = Proofs.Refinement.evictAccEpoch s.mir Q ∧
      (w, c) ∈ Proofs.Refinement.honestBeforeEpoch s.honest
        (Proofs.Refinement.evictAccEpoch s.mir Q) := by
  have hc_not_mem := not_mem_chains_epoch_of_findIdx_noneCLazy hsim Q w c h body hc_mem hparse hfind
  rcases hsim.hhon (w, c) hc_mem with ⟨hc_inv, _, hc_sends, hc_le_sender⟩
  have hc_ge1 : 1 ≤ c.1.1 := hc_inv.2.2.1
  rw [hc_sender] at hc_sends hc_le_sender
  dsimp only at hc_sends hc_le_sender
  have hadj_other : s.mir.epoch Q.other ≤ s.mir.epoch Q + 1 := by
    have hadj := (hsim.hep_adj Q.other).2
    rwa [Party.other_other] at hadj
  have hc_le_Q : c.1.1 ≤ s.mir.epoch Q := by omega
  have hQ_sends : Q.sendsIn (s.mir.epoch Q) = true := by simpa [inReceiveOnlyEpoch] using hinw
  have hc_recv_Q : Q.sendsIn c.1.1 = false := by
    have h := c7_sendsIn_other_false_of_sendsIn hc_sends
    rwa [Party.other_other] at h
  have hc_ne_Q : c.1.1 ≠ s.mir.epoch Q := by
    intro heq; rw [heq, hQ_sends] at hc_recv_Q; cases hc_recv_Q
  have hc_ne_pred : c.1.1 ≠ s.mir.epoch Q - 1 := by
    intro heq
    have hmem := mem_chains_epoch_of_adj Q (s.mir.epoch Q) c.1.1 (s.chains Q)
      (fun hA => hA ▸ hsim.hchainsA_ep) (fun hB => hB ▸ hsim.hchainsB_ep)
      hc_ge1 hc_le_Q (by omega) hc_recv_Q
    exact hc_not_mem hmem
  have hlt : c.1.1 < s.mir.epoch Q - 1 := by omega
  have hgt1 : 1 < s.mir.epoch Q := by omega
  have hev_eq : s.mir.epoch Q - 1 = Proofs.Refinement.evictAccEpoch s.mir Q := by
    simp [Proofs.Refinement.evictAccEpoch, hinw]
  exact ⟨hgt1, hev_eq, List.mem_filter.mpr ⟨hc_mem, decide_eq_true (hev_eq ▸ hlt)⟩⟩

omit [SampleableType Pt] in
theorem lFig8_receive_evictedProbeRecord_isSome_eq_deliverForgeEvent_lazy
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (Q : Party) (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (salt : Salt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hbound : ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1)) :
    ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (Proofs.Refinement.evictedProbeRecord sC Q Dh epExp c w h salt)).isSome =
      Proofs.Refinement.EvictedDeliverForgeEvent P Dh encPt encT idOf sC s_fig8 Q epExp c w h
        salt := by
  have hsim := hinv.hsim
  have hst_id : (s_fig8.st Q).id = Q := hsim.hst_id Q
  have htcur : (s_fig8.st Q).tcur = sC.base.mir.epoch Q := hsim.htcur Q
  have hQ_recv : Q.sendsIn (sC.base.mir.epoch Q + 1) = false :=
    Proofs.Refinement.sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
  rcases hsim.hspur Q with ⟨_, _, _, hspur_notinw⟩
  rcases hspur_notinw hinw with ⟨hγ_Q, _, _⟩
  let p₁ := (rootPRNG P.C.F encPt).up (s_fig8.st Q).root
    (Dh.dh (epExp (sC.base.mir.epoch Q)) (Dh.dh (epExp c.1.1) Dh.base))
  let sk := FSAEAD.skipKeys (lChainPRG P.C.F) h.counter.toNat p₁.2 0 []
  let v' : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) :=
    ⟨((lChainPRG P.C.F h.counter.toNat).gen sk.1).1, h.counter.toNat + 1, sk.2⟩
  have heq :
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
        (Proofs.Refinement.evictedProbeRecord sC Q Dh epExp c w h salt) =
      (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (Proofs.Refinement.evictedMessageKey P encPt sC s_fig8 Q Dh epExp c h)
        (h.counter.toNat + 1, (sC.base.mir.epoch Q + 1, some (Dh.dh (epExp c.1.1) Dh.base)))
        ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)).map
        (fun pm =>
          ({ (s_fig8.st Q) with
              root := p₁.1,
              vR := Function.update (s_fig8.st Q).vR (sC.base.mir.epoch Q + 1) (some v'),
              γ := .pub (Dh.dh (epExp c.1.1) Dh.base),
              tcur := sC.base.mir.epoch Q + 1 },
            sC.base.mir.epoch Q + 1, h.counter.toNat + 1, pm)) := by
    unfold lFig8 SM.Construction.scheme SM.Construction.receive lFS dhScheme
      Proofs.Refinement.evictedProbeRecord Proofs.Refinement.evictedMessageKey
      Proofs.Refinement.evictedEpochStep Proofs.Refinement.evictedEpochSeed
    dsimp only
    rw [htcur]
    have hcond1 :
        ((s_fig8.st Q).id.sendsIn (sC.base.mir.epoch Q + 1) ||
          decide (sC.base.mir.epoch Q + 1 < sC.base.mir.epoch Q + 1)) = false := by
      rw [hst_id, hQ_recv]; simp
    simp only [hcond1, Bool.false_eq_true, ↓reduceIte, hγ_Q, Function.update_self]
    unfold FSAEAD.fromAEADPRG
    dsimp only
    have hlk : ([] : List (ℕ × BitVec 256)).lookup (h.counter.toNat + 1) = none := rfl
    have hcond_false :
        ¬ (h.counter.toNat + 1 ≤ 0 ∨ 25000 < h.counter.toNat + 1 - 0 - 1) := by
      intro hbad
      rcases hbad with hle | hgt
      · omega
      · exact hbound (Or.inl (by omega))
    have hsub1 : h.counter.toNat + 1 - 0 - 1 = h.counter.toNat := by omega
    have hsub2 : h.counter.toNat + 1 - 1 = h.counter.toNat := by omega
    rw [hlk, ite_eq_right hcond_false, hsub1, hsub2]
    cases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        ((lChainPRG P.C.F h.counter.toNat).gen
          (FSAEAD.skipKeys (lChainPRG P.C.F) h.counter.toNat
            ((rootPRNG P.C.F encPt).up (s_fig8.st Q).root
              (Dh.dh (epExp (sC.base.mir.epoch Q)) (Dh.dh (epExp c.1.1) Dh.base))).2 0 []).1).2
        (h.counter.toNat + 1, (sC.base.mir.epoch Q + 1, some (Dh.dh (epExp c.1.1) Dh.base)))
        ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) with
    | none => rfl
    | some pm => simp [Function.update_idem, v', sk, p₁]
  rw [heq]
  unfold Proofs.Refinement.EvictedDeliverForgeEvent
  exact Option.isSome_map

/-- `EvictedSpurHistSimInvLazy` implies `EvictedOnlyNoForgeAt` at every party. -/
theorem evictedOnlyNoForgeAt_of_evictedSpurHistSimInvLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    {InvPQ : ℕ → List (BitVec 8) → Prop}
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hdec : ∀ T, decT (encT T) = some T) (lam : Pt)
    {qep q r w_rem : ℕ}
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party)
    (hInv : EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g) :
    EvictedOnlyNoForgeAt P decT (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) sC g Q := by
  obtain ⟨x₀, s_R, ec, winBefore, epExp, hinv, hspur_lazy⟩ := hInv.2
  obtain ⟨w_acc, rk_base, T_base, hw_acc_valid, hbase_valid, hno_spur⟩ := hspur_lazy Q
  have ⟨n_top, _, hI_top⟩ : ∃ n, n + r ≤ q ∧ InvPQ n (sC.base.pq Q) := hinv.hsim.hpqInv Q
  obtain ⟨w_top, hw_top⟩ := hInv_top n_top _ hI_top
  intro w c h body pq' salt hmem hsender hparse hrecv hfind hepoch hinw hbound _ T hT
  rcases hinv.hsim.hhon (w, c) hmem with ⟨hhon_c, _, _, _⟩
  rcases Proofs.Refinement.honestEntryInvC_eq_raw P (Proofs.Refinement.InvB InvPQ q r) Dh encT
    epExp hhon_c hparse with ⟨_, hsrk, _, _⟩
  rw [hsrk, hdec] at hT
  injection hT with hT_eq
  subst hT_eq
  rw [hspqr_eq] at hrecv
  obtain ⟨hgt1, hev_eq, hc_before⟩ :=
    mem_honestBeforeEpoch_of_evicted_simInvCLazy hinv.hsim Q hinw w c h body hmem hsender hparse
      hfind hepoch
  have hact : 1 ≤ Proofs.Refinement.evictAccEpoch sC.base.mir Q := by omega
  obtain ⟨w_acc_wire, c_acc, h_acc, body_acc, pq_acc, pq_acc', salt_acc,
      hc_acc_mem, hc_acc_eq, hc_acc_sender, hparse_acc, hw_acc, hrecv_acc, hreach₀⟩ :=
    hw_acc_valid hact
  have hlt_ev : c.1.1 < Proofs.Refinement.evictAccEpoch sC.base.mir Q :=
    of_decide_eq_true (List.mem_filter.mp hc_before).2
  have hlt_acc : c.1.1 < c_acc.1.1 := by omega
  obtain ⟨pq_s₀, pq_s₀', pq_s₁, pq_s₁', r₀, r₁, salt₀, salt₁, w_s₀,
      hw_s₀, hsend₀, hreach_s, hsend₁⟩ :=
    hInv.1.hhist.hhon_ord w c h body w_acc_wire c_acc h_acc body_acc hmem hc_acc_mem
      (hsender.trans hc_acc_sender.symm) hlt_acc hparse hparse_acc
  obtain ⟨pre, pre_acc, hpre, hpre_acc, hle_acc⟩ :=
    Proofs.Refinement.spqrV1_sender_reachFrom_msgChainEpoch_le P.C.F K hw_s₀ hsend₀ hreach_s hsend₁
  obtain ⟨-, -, hsalt_acc⟩ :=
    Proofs.Refinement.spqrV1_prior_accept_reachFrom_recv_salt_eq P.C.F K hw_acc hw_top hrecv_acc
      hpre_acc hpre hle_acc hreach₀ (.refl _) hrecv
  have hmem_cand := Proofs.Refinement.mem_evictedSpurCandList_of_honest P epExp epExp w_acc
    (Proofs.Refinement.honestBeforeEpoch sC.base.honest
      (Proofs.Refinement.evictAccEpoch sC.base.mir Q))
    w c h body hc_before hparse rfl
  rw [← hsalt_acc] at hmem_cand
  have hrk : ({ g with win := false }.st Q).root =
      (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (sC.base.mir.epoch Q)) T_base))).1 :=
    ((hbase_valid.2 hinw).2.1 (by omega)).1
  have hisSome := lFig8_receive_evictedProbeRecord_isSome_eq_deliverForgeEvent_lazy
    P InvPQ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false } ec winBefore epExp
    hinv Q c w h salt hinw hbound
  cases hev : Proofs.Refinement.EvictedDeliverForgeEvent P Dh encPt encT idOf sC
      { g with win := false } Q epExp c w h salt
  · rw [hev] at hisSome
    exact Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp hisSome)
  · have hsingle := Proofs.Refinement.evictedDeliverForgeEvent_implies_spurBadSingle P Dh encPt
      encT idOf hid sC { g with win := false } Q epExp c w h body salt rk_base T_base hinw hrk
      hparse (Proofs.Refinement.honestEntryInvC_len_lt hhon_c) hev
    have hbad : spurBadList P encPt Dh Q rk_base T_base
        (Proofs.Refinement.evictedSpurCandList P epExp w_acc
          (Proofs.Refinement.honestBeforeEpoch sC.base.honest
            (Proofs.Refinement.evictAccEpoch sC.base.mir Q)))
        (epExp (sC.base.mir.epoch Q)) = true :=
      List.any_eq_true.mpr ⟨(w, salt, epExp c.1.1), hmem_cand, hsingle⟩
    rw [hno_spur hinw] at hbad
    cases hbad

/-- Forbidden DH point list for a fresh epoch-coin draw up to epoch frontier `M`. -/
def sendCoinCollPts (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256) (M : ℕ) : List Pt :=
  Dh.dh 0 Dh.base :: (List.range (M + 1)).map (fun t => Dh.dh (epExp t) Dh.base)

/-- Tests whether `Dh.dh rc Dh.base` collides with `sendCoinCollPts`. -/
def sendCoinCollBad (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256) (M : ℕ)
    (rc : BitVec 256) : Bool :=
  decide (Dh.dh rc Dh.base ∈ sendCoinCollPts Dh epExp M)

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem sendCoinCollPts_length (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256) (M : ℕ) :
    (sendCoinCollPts Dh epExp M).length = M + 2 := by
  simp [sendCoinCollPts]

omit [Zero Pt] [SampleableType Pt] in
theorem sendCoinCollBad_eq_false_imp (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256) (M : ℕ)
    {rc : BitVec 256} (h : sendCoinCollBad Dh epExp M rc = false) :
    rc ≠ 0 ∧ ∀ t ≤ M, Dh.dh rc Dh.base ≠ Dh.dh (epExp t) Dh.base := by
  unfold sendCoinCollBad sendCoinCollPts at h
  have hnot_mem : Dh.dh rc Dh.base ∉
      Dh.dh 0 Dh.base :: (List.range (M + 1)).map (fun t => Dh.dh (epExp t) Dh.base) :=
    of_decide_eq_false h
  refine ⟨?_, ?_⟩
  · intro hrc0
    subst hrc0
    exact hnot_mem List.mem_cons_self
  · intro t ht hdh
    apply hnot_mem
    refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t, List.mem_range.mpr (by omega), hdh.symm⟩)

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem honestEntryInvC_congr_epExp {PQ PQC : Type}
    {P : Params PQ PQC} {Inv : PQ → Prop} {Dh : DHFun (BitVec 256) Pt}
    {encT : Pt → PublicKey} {epExp₁ epExp₂ : ℕ → BitVec 256}
    {wc : List (BitVec 8) × Fig8C Pt}
    (h : HonestEntryInvC P Inv Dh encT epExp₁ wc)
    (heq : epExp₂ wc.2.1.1 = epExp₁ wc.2.1.1) :
    HonestEntryInvC P Inv Dh encT epExp₂ wc := by
  unfold HonestEntryInvC at h ⊢
  dsimp only at h ⊢
  rwa [heq]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem snapSync_congr_epExp {PQ : Type}
    {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encT : Pt → PublicKey}
    {K rk epExp₁ epExp₂ : ℕ → BitVec 256} {tFront : ℕ}
    {snap : Party × ℕ × GhostState PQ}
    (h : SnapSync C Dh encT K rk epExp₁ tFront snap)
    (heq : ∀ t ≤ tFront, epExp₂ t = epExp₁ t) :
    SnapSync C Dh encT K rk epExp₂ tFront snap := by
  rcases h with ⟨h1, h2, h3, ⟨j, hj, h4⟩, h5, h6⟩
  refine ⟨h1, h2, h3, ⟨j, hj, ?_⟩, ?_, ?_⟩
  · rwa [heq snap.2.1 h2]
  · intro rc_ch hrc
    rcases h5 rc_ch hrc with ⟨ep, hep, hsrk, hck, hmk⟩
    refine ⟨ep, hep, ?_, hck, hmk⟩
    rwa [heq ep (Nat.le_trans hep h2)]
  · intro hge2
    rcases h6 hge2 with ⟨rc_last, hlast, hsrk⟩
    refine ⟨rc_last, hlast, ?_⟩
    rwa [heq (snap.2.1 - 1) (by omega)]

omit [DecidableEq Pt] [SampleableType Pt] in
theorem epochSync_congr_epExp {PQ PQC : Type} {ℓ : ℕ}
    {P : Params PQ PQC} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {honest : List (List (BitVec 8) × Fig8C Pt)}
    {sent : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256))}
    {snaps : List (Party × ℕ × GhostState PQ)}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {epExp₁ epExp₂ : ℕ → BitVec 256}
    (h : EpochSync P Dh encPt encT idOf honest sent snaps s_fig8 epExp₁)
    (heq : ∀ t ≤ max (s_fig8.st .A).tcur (s_fig8.st .B).tcur, epExp₂ t = epExp₁ t) :
    EpochSync P Dh encPt encT idOf honest sent snaps s_fig8 epExp₂ := by
  intro hwin
  rcases h hwin with ⟨K, rk, hsync⟩
  refine ⟨K, rk,
    { hsync with
      hγ_exp := fun R hR => by
        have hle : (s_fig8.st R).tcur ≤ max (s_fig8.st .A).tcur (s_fig8.st .B).tcur := by
          cases R <;> [exact Nat.le_max_left _ _; exact Nat.le_max_right _ _]
        rw [heq (s_fig8.st R).tcur hle]
        exact hsync.hγ_exp R hR
      hStep := fun e he => by
        rw [heq e (by omega), heq (e + 1) (by omega)]
        exact hsync.hStep e he
      hsnaps := fun snap hsnap =>
        snapSync_congr_epExp (hsync.hsnaps snap hsnap) heq }⟩

omit [DecidableEq Pt] [SampleableType Pt] in
theorem inWin_true_epoch_other_eq {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    {P : Params PQ PQC} {Inv : PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    {Q : Party} (hinw : inReceiveOnlyEpoch s.mir Q = true) (hnoBob : SM.noBobSendInEpoch0 s.mir Q = true) :
    s.mir.epoch Q.other = s.mir.epoch Q ∧
    inReceiveOnlyEpoch s.mir Q.other = false ∧
    max (s.mir.epoch .A) (s.mir.epoch .B) = s.mir.epoch Q := by
  have hle1 : s.mir.epoch Q ≤ s.mir.epoch Q.other := (hinv.hep_adj Q).1 hinw
  have hle2 : s.mir.epoch Q.other ≤ s.mir.epoch Q + 1 := by
    have h := (hinv.hep_adj Q.other).2
    rwa [Party.other_other] at h
  rcases c7_sendsIn_succ_of_inWin_true s.mir Q hinw with ⟨_, hsends_succ⟩
  have hne_succ : s.mir.epoch Q.other ≠ s.mir.epoch Q + 1 := by
    intro heq
    have hrecv_other : Q.other.sendsIn (s.mir.epoch Q.other) = false := by
      rw [heq]
      exact c7_sendsIn_other_false_of_sendsIn hsends_succ
    have hinw_other : inReceiveOnlyEpoch s.mir Q.other = true := by simp [inReceiveOnlyEpoch, hrecv_other]
    have hle_back := (hinv.hep_adj Q.other).1 hinw_other
    rw [Party.other_other] at hle_back
    omega
  have hep_eq : s.mir.epoch Q.other = s.mir.epoch Q := by omega
  have hinw_other_f : inReceiveOnlyEpoch s.mir Q.other = false := by
    unfold inReceiveOnlyEpoch
    rw [hep_eq]
    unfold inReceiveOnlyEpoch at hinw
    revert hinw hnoBob
    cases Q <;> simp [Party.other, Party.sendsIn, SM.noBobSendInEpoch0] ; omega
  have hmax_eq : max (s.mir.epoch .A) (s.mir.epoch .B) = s.mir.epoch Q := by
    cases Q <;> simp [Party.other] at hep_eq <;> omega
  exact ⟨hep_eq, hinw_other_f, hmax_eq⟩

omit [DecidableEq Pt] [SampleableType Pt] in
theorem simInvCXLazy_recoin_inWin {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    {P : Params PQ PQC} {Inv : ℕ → PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {qep q r : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    {Q : Party} (hinw : inReceiveOnlyEpoch sC.base.mir Q = true) (hnoBob : SM.noBobSendInEpoch0 sC.base.mir Q = true)
    {rc : BitVec 256} (_hrc0 : rc ≠ 0)
    (hrc_coll : ∀ t ≤ max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B),
      Dh.dh rc Dh.base ≠ Dh.dh (epExp t) Dh.base) :
    let epExp' := Function.update epExp (sC.base.mir.epoch Q + 1) rc
    let ec_rc := Function.update ec Q rc
    let ghost_rc := expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) rc
    let s_R_rc := { s_R with st := Function.update s_R.st Q ghost_rc }
    SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R_rc sC s_fig8 ec_rc winBefore
      epExp' ∧
    (∀ R rk_base T_base,
      ValidSpurBase P ℓ Dh encPt sC.base s_fig8 epExp R rk_base T_base →
      ValidSpurBase P ℓ Dh encPt sC.base s_fig8 epExp' R rk_base T_base) ∧
    (∀ t₁ t₂,
      t₁ ≤ sC.base.mir.epoch Q + 1 →
      t₂ ≤ sC.base.mir.epoch Q + 1 →
      Dh.dh (epExp' t₁) Dh.base = Dh.dh (epExp' t₂) Dh.base → t₁ = t₂) := by
  intro epExp' ec_rc ghost_rc s_R_rc
  have hsim := hinv.hsim
  obtain ⟨hep_other, hinw_other, hmax_eq⟩ := inWin_true_epoch_other_eq hsim hinw hnoBob
  have hepExp'_eq : ∀ t ≤ sC.base.mir.epoch Q, epExp' t = epExp t := fun t ht => by
    dsimp [epExp']
    rw [Function.update_of_ne (by omega)]
  have hepExp'_succ : epExp' (sC.base.mir.epoch Q + 1) = rc := by
    dsimp [epExp']
    exact Function.update_self (sC.base.mir.epoch Q + 1) rc epExp
  have hcoll' : ∀ t₁ t₂,
      t₁ ≤ sC.base.mir.epoch Q + 1 →
      t₂ ≤ sC.base.mir.epoch Q + 1 →
      Dh.dh (epExp' t₁) Dh.base = Dh.dh (epExp' t₂) Dh.base → t₁ = t₂ := by
    intro t₁ t₂ ht₁ ht₂ hdh
    by_cases h1 : t₁ = sC.base.mir.epoch Q + 1
    · by_cases h2 : t₂ = sC.base.mir.epoch Q + 1
      · omega
      · exfalso
        have ht₂_le : t₂ ≤ max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B) := by omega
        rw [h1, hepExp'_succ, hepExp'_eq t₂ (by omega)] at hdh
        exact hrc_coll t₂ ht₂_le hdh
    · by_cases h2 : t₂ = sC.base.mir.epoch Q + 1
      · exfalso
        have ht₁_le : t₁ ≤ max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B) := by omega
        rw [h2, hepExp'_succ, hepExp'_eq t₁ (by omega)] at hdh
        exact hrc_coll t₁ ht₁_le hdh.symm
      · rw [hepExp'_eq t₁ (by omega), hepExp'_eq t₂ (by omega)] at hdh
        exact hsim.hcoll t₁ t₂ (by omega) (by omega) hdh
  have hbase_trans : ∀ R rk_base T_base,
      ValidSpurBase P ℓ Dh encPt sC.base s_fig8 epExp R rk_base T_base →
      ValidSpurBase P ℓ Dh encPt sC.base s_fig8 epExp' R rk_base T_base := by
    intro R rk_base T_base hbase
    have hR_le : sC.base.mir.epoch R ≤ sC.base.mir.epoch Q := by
      by_cases hRQ : R = Q
      · subst hRQ; exact le_rfl
      · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
        subst hRO; omega
    refine ⟨hbase.1, ?_⟩
    rw [hepExp'_eq (sC.base.mir.epoch R) hR_le]
    exact hbase.2
  refine ⟨⟨?_, hinv.huniq, hinv.hkept, hinv.hidx, ?_⟩, hbase_trans, hcoll'⟩
  · exact
      { hsim with
        hmeta := { hsim.hmeta with hb := hsim.hmeta.hb }
        hec := fun R hR => by
          dsimp [ec_rc]
          by_cases hRQ : R = Q
          · subst hRQ; rw [hinw] at hR; cases hR
          · rw [Function.update_of_ne hRQ]; exact hsim.hec R hR
        hst_R := fun R => by
          dsimp [s_R_rc, ghost_rc, ec_rc]
          by_cases hRQ : R = Q
          · subst hRQ; simp [Function.update_self]
          · simp [Function.update_of_ne hRQ, hsim.hst_R R]
        hepExp0 := by
          rw [hepExp'_eq 0 (Nat.zero_le _)]
          exact hsim.hepExp0
        hspur := fun R => by
          rcases hsim.hspur R with ⟨rk_base, T_base, hinw_t, hinw_f⟩
          have hb := hbase_trans R rk_base T_base
            ⟨fun h => ⟨(hinw_t h).1, (hinw_t h).2.1, (hinw_t h).2.2.1⟩, hinw_f⟩
          refine ⟨rk_base, T_base, fun hR => ?_, hb.2⟩
          by_cases hRQ : R = Q
          · subst hRQ
            refine ⟨(hb.1 hR).1, (hb.1 hR).2.1, (hb.1 hR).2.2, ?_⟩
            dsimp [ec_rc]
            rw [hepExp'_succ, Function.update_self]
          · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
            subst hRO
            rw [hinw_other] at hR
            cases hR
        hchains_sync := fun R g_ch hg => by
          rcases hsim.hchains_sync R g_ch hg with ⟨hgep, hgsend, hgkey, v, hvR, hsync⟩
          have hR_le : sC.base.mir.epoch R ≤ sC.base.mir.epoch Q := by
            by_cases hRQ : R = Q
            · subst hRQ; exact le_rfl
            · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
              subst hRO; omega
          rw [hepExp'_eq g_ch.epoch (Nat.le_trans hgep hR_le)]
          exact ⟨hgep, hgsend, hgkey, v, hvR, hsync⟩
        hhon := fun wc hwc => by
          rcases hsim.hhon wc hwc with ⟨h1, h2, h3, h4⟩
          have hle_Q : wc.2.1.1 ≤ sC.base.mir.epoch Q := by omega
          exact ⟨honestEntryInvC_congr_epExp h1 (hepExp'_eq wc.2.1.1 hle_Q), h2, h3, h4⟩
        hcoll := fun t₁ t₂ ht₁ ht₂ hdh =>
          hcoll' t₁ t₂ (by omega) (by omega) hdh }
  · refine epochSync_congr_epExp hinv.hsync fun t ht => ?_
    rw [hsim.htcur .A, hsim.htcur .B, hmax_eq] at ht
    exact hepExp'_eq t ht

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurCandList_congr_epExp {PQC : Type}
    (P : Params (List (BitVec 8)) PQC) {epExp₁ epExp₂ : ℕ → BitVec 256}
    (w_acc : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F)
    (honest : List (List (BitVec 8) × Fig8C Pt))
    (heq : ∀ wc ∈ honest, epExp₂ wc.2.1.1 = epExp₁ wc.2.1.1) :
    Proofs.Refinement.evictedSpurCandList P epExp₂ w_acc honest =
      Proofs.Refinement.evictedSpurCandList P epExp₁ w_acc honest := by
  unfold Proofs.Refinement.evictedSpurCandList
  refine List.filterMap_congr fun wc hwc => ?_
  rw [heq wc hwc]

set_option maxHeartbeats 800000 in
private theorem c7_simSendStep_preserves_simInvCLazy_at_ec
    (P : Params (List (BitVec 8)) (BitVec 512)) (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (_decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : BitVec 512)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (s : SimState (List (BitVec 8)) Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCLazy P (InvB Inv q r) ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hnoBob_mir : SM.noBobSendInEpoch0 s.mir Q = true)
    (hep_mir : s.mir.epMgmt 3 qep Q bad = some s₁)
    (hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true)
    (hcoll_next : ∀ t₁ t₂,
      t₁ ≤ max (s₁.epoch .A) (s₁.epoch .B) →
      t₂ ≤ max (s₁.epoch .A) (s₁.epoch .B) →
      Dh.dh (epExp t₁) Dh.base = Dh.dh (epExp t₂) Dh.base → t₁ = t₂) :
    let fR := chal.elim
      (transmitPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep Q m₀ rq bad s_R)
      (fun m₁ => challPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep SM.Config.h1 Q m₀ m₁ rq bad
        s_R)
    let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq (ec Q) (s, s_fig8)
    let ec' := if inReceiveOnlyEpoch s.mir Q then Function.update ec Q 0 else ec
    SimInvCLazy P (InvB Inv q (r - 1)) ℓ Dh encPt encT qep q (r - 1) x₀ fR.2 res.2.1 res.2.2 ec'
      winBefore epExp ∧
    (∀ R rk_b T_b,
      ValidSpurBase P ℓ Dh encPt s s_fig8 epExp R rk_b T_b →
      ValidSpurBase P ℓ Dh encPt res.2.1 res.2.2 epExp R rk_b T_b) ∧
    (PosUniq s → HonestIdxLe s → PosUniq res.2.1 ∧ HonestIdxLe res.2.1) ∧
    (∀ (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ), sC.base = s →
      KeptInv P Dh encPt encT idOf lam sC s_fig8 →
      EpochSync P Dh encPt encT idOf sC.base.honest sC.sent sC.snaps s_fig8 epExp →
      let sC' := cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1
      KeptInv P Dh encPt encT idOf lam sC' res.2.2 ∧
      EpochSync P Dh encPt encT idOf sC'.base.honest sC'.sent sC'.snaps res.2.2 epExp) := by
  intro fR res ec'
  rcases hinv.hmeta.epMgmt_some Q qep bad hep_mir with
    ⟨s_R₁, s_fig8₁, hep_R, hep_fig8, hst_R₁, hst_fig8₁, hmeta₁⟩
  set pn := if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q
  rcases Option.isSome_iff_exists.mp (spqrCLocal_total hS hr (s.pq Q) rq (hinv.hpqInv Q)) with
    ⟨⟨pq', salt, pqMsg⟩, hspqr⟩
  have hnp : P.spqr.sendPanics (s.pq Q) rq = false :=
    spqrCLocal_noSendPanic hS hr (s.pq Q) rq (hinv.hpqInv Q)
  have hpq'_inv : InvB Inv q (r - 1) pq' := InvB.send hS hr (hinv.hpqInv Q) hspqr
  set addrs := if Q == Party.A && s.unackA then P.addrAB else none
  set pub : LibsignalMsgPublicPart := ⟨pn, pqMsg, effectiveHkdfSalt32 salt, addrs⟩
  have hmk : LibsignalSim.mkPub (P := P) s Q rq pn = some (pq', pub) := by
    simp [LibsignalSim.mkPub, hspqr, pub, addrs]
  have hpub_pq : RoundTrip.SentPq P pub.pqmsg := Or.inr ⟨_, _, _, _, hspqr⟩
  have hpub_addr : RoundTrip.SentAddrs P pub.addrs := by
    change RoundTrip.SentAddrs P (if (Q == Party.A && s.unackA) = true then P.addrAB else none)
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  set m_enc : Plain ℓ := chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)
  set sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  set out_fig8 := sm.send (s_fig8.st Q) (pub, m_enc) (ec Q)
  set st_fig8' := out_fig8.1
  set c := out_fig8.2
  set w := LibsignalSim.toWire c
  set out_R := P.send (s_R.st Q) m_enc.toList rq
  set st_R' := out_R.1
  set w_R := out_R.2
  set rec_R : SM.Record (Plain ℓ) (List (BitVec 8)) :=
    ⟨⟨Q, s_R₁.epoch Q, s_R₁.idx Q + 1⟩, m_enc, w_R⟩
  set rec_mir : SM.Record (Plain ℓ) (List (BitVec 8)) :=
    ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
  set rec_fig8 : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
    ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, (pub, m_enc), c⟩
  set s_R' := s_R₁.record 3 Q st_R' rec_R chal.isSome
  set s_fig8' := s_fig8₁.record 3 Q st_fig8' rec_fig8 chal.isSome
  set s' : SimState (List (BitVec 8)) Pt ℓ :=
    { s with mir := s₁.record 3 Q () rec_mir chal.isSome,
             pq := Function.update s.pq Q pq',
             pn := Function.update s.pn Q pn,
             honest := (w, c) :: s.honest }
  have hfR_eq : fR = (some w_R, s_R') := by
    dsimp only [fR, s_R', rec_R, w_R, st_R', out_R, m_enc]
    cases hchal : chal with
    | none =>
      unfold transmitPure
      rw [hep_R]
      dsimp only [Option.elim, Option.isSome]
      rw [hst_R₁]
      rfl
    | some m₁ =>
      have hsafe_R : (!s_R₁.safeCh 3 Q) = false := by
        rw [hmeta₁.safeCh_R 3 Q, hsafeCh (by simp [hchal])]; rfl
      have hcond_R :
          (!s_R₁.safeCh 3 Q ||
            !(SM.Config.h1 (Msg := Plain ℓ)).challAllowedIn (s_R₁.epoch Q)) = false := by
        rw [hsafe_R]; rfl
      dsimp only [Option.elim, Option.isSome]
      unfold challPure
      rw [hep_R]
      dsimp only
      rw [hcond_R, ite_eq_right Bool.false_ne_true, hst_R₁]
      rfl
  have hres_c : ∀ (c_cka : BitVec 256),
      simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka (s, s_fig8) =
      let out := sm.send (s_fig8.st Q) (pub, m_enc) c_cka
      let w_c := LibsignalSim.toWire out.2
      let rec_m : SM.Record (Plain ℓ) (List (BitVec 8)) :=
        ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w_c⟩
      (some w_c,
        ({ s with mir := s₁.record 3 Q () rec_m chal.isSome,
                  pq := Function.update s.pq Q pq',
                  pn := Function.update s.pn Q pn,
                  honest := (w_c, out.2) :: s.honest },
         s_fig8₁.record 3 Q out.1
           ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, (pub, m_enc), out.2⟩ chal.isSome)) := by
    intro c_cka
    have hmk' : LibsignalSim.mkPub (P := P) s Q rq
        (if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q) =
        some (pq', pub) := hmk
    unfold simSendStep
    dsimp only
    rw [hmk']
    dsimp only [m_enc]
    cases hchal : chal with
    | none =>
      unfold transmitPure
      rw [hep_fig8]
      dsimp only [Option.elim, Option.isSome]
      rw [hst_fig8₁]
    | some m₁ =>
      have hsafe_f : (!s_fig8₁.safeCh 3 Q) = false := by
        rw [hmeta₁.safeCh_fig8 3 Q, hsafeCh (by simp [hchal])]; rfl
      have hcond_f :
          (!s_fig8₁.safeCh 3 Q ||
            !(SM.Config.h1 (Msg := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s_fig8₁.epoch Q)) = false := by
        rw [hsafe_f]; rfl
      have hmb : (if s_fig8.b = true then (pub, m₁) else (pub, m₀)) =
          (pub, if s_R.b = true then m₁ else m₀) := by
        rw [← hinv.hmeta.hb]
        cases s_R.b <;> rfl
      have hz_eq : challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad s_fig8 =
          let out := sm.send (s_fig8.st Q) (pub, if s_R.b = true then m₁ else m₀) c_cka
          (some out.2, s_fig8₁.record 3 Q out.1
            ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩,
              (pub, if s_R.b = true then m₁ else m₀), out.2⟩ true) := by
        unfold challPure
        rw [hep_fig8]
        dsimp only
        rw [hcond_f, ite_eq_right Bool.false_ne_true, hst_fig8₁]
        change (let m := if s_fig8.b = true then (pub, m₁) else (pub, m₀);
          let out := sm.send (s_fig8.st Q) m c_cka;
          (some out.2, s_fig8₁.record 3 Q out.1
            ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, m, out.2⟩ true)) = _
        rw [hmb]
      dsimp only [Option.elim, Option.isSome]
      rw [hz_eq]
  have hres_eq : res = (some w, (s', s_fig8')) := hres_c (ec Q)
  set spkKey := encT (Dh.dh x₀ Dh.base)
  have hs'_ep : s'.mir.epoch = s₁.epoch := rfl
  have hs'_idx_Q : s'.mir.idx Q = s₁.idx Q + 1 := by
    change Function.update s₁.idx Q (s₁.idx Q + 1) Q = s₁.idx Q + 1
    exact Function.update_self Q (s₁.idx Q + 1) s₁.idx
  have hcore :
      w_R = w ∧
      st_R' = toGhost P (resolveSim spkKey s') Q st_fig8' ∧
      inReceiveOnlyEpoch s'.mir Q = false ∧
      inReceiveOnlyEpoch s'.mir Q.other = inReceiveOnlyEpoch s.mir Q.other ∧
      Q.sendsIn (s₁.epoch Q) = true ∧
      1 ≤ s₁.epoch Q ∧
      s₁.epoch Q ≤ qep ∧
      s₁.epoch Q.other = s.mir.epoch Q.other ∧
      s₁.idx Q.other = s.mir.idx Q.other ∧
      (s₁.epoch Q = s.mir.epoch Q ∧ s₁.idx Q = s.mir.idx Q ∨
        s₁.epoch Q = s.mir.epoch Q + 1 ∧ s₁.idx Q = 0) ∧
      s'.mir.idx Q + (r - 1) ≤ q ∧
      (∀ R, s.mir.epoch R ≤ s'.mir.epoch R) ∧
      (∀ R, (inReceiveOnlyEpoch s'.mir R = true → s'.mir.epoch R ≤ s'.mir.epoch R.other) ∧
        s'.mir.epoch R ≤ s'.mir.epoch R.other + 1) ∧
      st_fig8'.id = Q ∧
      st_fig8'.tcur = s₁.epoch Q ∧
      st_fig8'.vR = (s_fig8.st Q).vR ∧
      c.1 = (s₁.epoch Q, some (Dh.dh (epExp (s₁.epoch Q)) Dh.base)) ∧
      c.2.1 = s₁.idx Q + 1 ∧
      HonestEntryInvC P (InvB Inv q (r - 1)) Dh encT epExp (w, c) ∧
      ChainsEpochInvA (s'.mir.epoch .A) (s.chains .A) ∧
      (s.chains .A).map (·.epoch) = epListA (s'.mir.epoch .A / 2) ∧
      (s.chains .B).map (·.epoch) = epListB ((s'.mir.epoch .B + 1) / 2) ∧
      (∃ rk_base T_base,
        (inReceiveOnlyEpoch s'.mir Q = true →
          st_fig8'.root = rk_base ∧ st_fig8'.γ = .pub T_base ∧ T_base ≠ 0 ∧
          epExp (s'.mir.epoch Q + 1) = ec' Q) ∧
        (inReceiveOnlyEpoch s'.mir Q = false →
          st_fig8'.γ = .exp (epExp (s'.mir.epoch Q)) ∧
          (0 < s'.mir.epoch Q →
            st_fig8'.root =
              (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s'.mir.epoch Q)) T_base))).1 ∧
            st_fig8'.curCkaMsg = some (Dh.dh (epExp (s'.mir.epoch Q)) Dh.base)) ∧
          ∃ vS, st_fig8'.vS = some vS ∧ vS.lastIndex = s'.mir.idx Q)) ∧
      (∀ rk_b T_b,
        ValidSpurBase P ℓ Dh encPt s s_fig8 epExp Q rk_b T_b →
        (inReceiveOnlyEpoch s'.mir Q = true →
          st_fig8'.root = rk_b ∧ st_fig8'.γ = .pub T_b ∧ T_b ≠ 0) ∧
        (inReceiveOnlyEpoch s'.mir Q = false →
          st_fig8'.γ = .exp (epExp (s'.mir.epoch Q)) ∧
          (0 < s'.mir.epoch Q →
            st_fig8'.root =
              (rootKdf P.C.F rk_b (encPt (Dh.dh (epExp (s'.mir.epoch Q)) T_b))).1 ∧
            st_fig8'.curCkaMsg = some (Dh.dh (epExp (s'.mir.epoch Q)) Dh.base)) ∧
          ∃ vS, st_fig8'.vS = some vS ∧ vS.lastIndex = s'.mir.idx Q)) := by
    cases hinw : inReceiveOnlyEpoch s.mir Q with
    | false =>
      rcases c7_sendsIn_of_inWin_false s.mir Q hnoBob_mir hinw with ⟨hsends, ht_ge1⟩
      have hsends_succ : Q.sendsIn (s.mir.epoch Q + 1) = false :=
        sendsIn_succ_of_sendsIn Q (s.mir.epoch Q) hsends
      rcases c7_epMgmt_of_sendsIn_succ_false s.mir 3 qep Q bad hsends_succ hep_mir with
        ⟨hs₁_eq, hep_le_qep⟩
      subst hs₁_eq
      have hpn_eq : pn = s.pn Q := ite_eq_right (not_not.mpr rfl)
      have hpn_upd : Function.update s.pn Q pn = s.pn := by
        rw [hpn_eq]; exact Function.update_eq_self Q s.pn
      rcases hinv.hspur Q with ⟨rk_base, T_base, _, hinw_f⟩
      rcases hinw_f hinw with ⟨hγ, hpos_ep, v, hvS, hv_last⟩
      rcases hpos_ep (by omega) with ⟨hroot, hTcur⟩
      have hidx_Q := hinv.hidx_le Q
      have hv_lt : v.lastIndex + 1 < 2 ^ 32 := by omega
      have hstep_fig8 := c7_lFig8_send_step_not_inWinC P (InvB Inv q (r - 1)) Dh encPt encT idOf
        lam hrt epExp Q (s_fig8.st Q) (s.mir.epoch Q) (hinv.hst_id Q) (hinv.htcur Q) ht_ge1 hsends
        hγ hTcur v hvS hv_lt pub m_enc (ec Q) s.unackA rfl hspqr
      rcases hstep_fig8 with
        ⟨hid', hroot', htcur', hγ', hTcur', hvR', ⟨v', hvS', hv'_last⟩, hc1, hc2, hhon_wc⟩
      have hT_pub : ((s_fig8.st Q).curCkaMsg.map encT).getD dummyKey =
          (KeyPair.generate P.C (epExp (s.mir.epoch Q))).publicKey := by
        rw [hTcur, Option.map_some, Option.getD_some, keyPair_generate_publicKey hX]
      have hsend_ghost := send_toGhost_eq P Dh encPt encT idOf lam hid
        (resolveSim spkKey s) Q (s_fig8.st Q) (hinv.hst_id Q) (hinv.htcur Q).symm
        (epExp (s.mir.epoch Q)) hγ v hvS (by omega) hT_pub
        (by rw [hinv.htcur Q]; exact hsends) m_enc rq pq' salt pqMsg hspqr hnp
        s'.mir (hinv.htcur Q).symm ((w, c) :: s.honest) (ec Q)
      have hst_R_eq : s_R.st Q = toGhost P (resolveSim spkKey s) Q (s_fig8.st Q) := by
        rw [hinv.hst_R Q, expectedGhost_of_inWin_false _ _ _ _ _ _ _ _ hinw]
      have hpub_eq : (⟨(resolveSim spkKey s).pn Q, pqMsg, effectiveHkdfSalt32 salt,
          if Q == Party.A && (resolveSim spkKey s).unackA then P.addrAB else none⟩ : LibsignalMsgPublicPart) =
          pub := by
        simp [pub, hpn_eq, resolveSim_pn, resolveSim_unackA, addrs]
      have hres_s'_eq :
          { (resolveSim spkKey s) with
              mir := s'.mir,
              pq := Function.update (resolveSim spkKey s).pq Q pq',
              honest := (w, c) :: s.honest } = resolveSim spkKey s' := by
        simp [s', resolveSim, hpn_upd]
      rw [← hst_R_eq] at hsend_ghost
      dsimp only at hsend_ghost
      rw [hpub_eq, hres_s'_eq] at hsend_ghost
      have hout_R_eq : out_R = (toGhost P (resolveSim spkKey s') Q st_fig8', w) := hsend_ghost
      have hw_R_eq : w_R = w := congrArg Prod.snd hout_R_eq
      have hst_R'_eq : st_R' = toGhost P (resolveSim spkKey s') Q st_fig8' :=
        congrArg Prod.fst hout_R_eq
      have hinw'_eq : ∀ R, inReceiveOnlyEpoch s'.mir R = inReceiveOnlyEpoch s.mir R := fun R => by
        dsimp [inReceiveOnlyEpoch]; rw [hs'_ep]
      refine ⟨hw_R_eq, hst_R'_eq, by rw [hinw'_eq Q, hinw], hinw'_eq Q.other,
        hsends, ht_ge1, hep_le_qep,
        rfl, rfl, Or.inl ⟨rfl, rfl⟩, ?_, fun _ => le_rfl, hinv.hep_adj, hid', htcur', hvR', hc1,
        ?_, hhon_wc, hinv.hchainsA, hinv.hchainsA_ep, hinv.hchainsB_ep,
        ⟨rk_base, T_base, ?_, ?_⟩, ?_⟩
      · rw [hs'_idx_Q]; omega
      · rw [hc2, hv_last]
      · intro h; rw [hinw'_eq Q, hinw] at h; cases h
      · intro _
        rw [hs'_ep, hs'_idx_Q]
        exact ⟨hγ', fun _ => ⟨by rw [hroot', hroot], hTcur'⟩, v', hvS', by rw [hv'_last, hv_last]⟩
      · intro rk_b T_b hbase_b
        rcases hbase_b.2 hinw with ⟨_, hpos_b, _⟩
        refine ⟨(fun h => by rw [hinw'_eq Q, hinw] at h; cases h), fun _ => ?_⟩
        rw [hs'_ep, hs'_idx_Q]
        exact ⟨hγ', fun hp => ⟨by rw [hroot', (hpos_b hp).1], hTcur'⟩, v', hvS',
          by rw [hv'_last, hv_last]⟩
    | true =>
      rcases c7_sendsIn_succ_of_inWin_true s.mir Q hinw with ⟨hrecv, hsends_succ⟩
      rcases c7_epMgmt_of_sendsIn_succ_true s.mir 3 qep Q bad hsends_succ hep_mir with
        ⟨hs₁_ep, hs₁_idx, _, _, _, _, hep_le_qep⟩
      have hs₁_ep_Q : s₁.epoch Q = s.mir.epoch Q + 1 := by
        rw [hs₁_ep, Function.update_self]
      have hs₁_ep_other : s₁.epoch Q.other = s.mir.epoch Q.other := by
        rw [hs₁_ep, Function.update_of_ne (Party.other_ne Q)]
      have hs₁_idx_Q : s₁.idx Q = 0 := by
        rw [hs₁_idx, Function.update_self]
      have hs₁_idx_other : s₁.idx Q.other = s.mir.idx Q.other := by
        rw [hs₁_idx, Function.update_of_ne (Party.other_ne Q)]
      have hpn_eq : pn = BitVec.ofNat 32 (s.mir.idx Q - 1) :=
        ite_eq_left (by omega)
      rcases hinv.hspur Q with ⟨rk_base, T_base, hinw_t, _⟩
      rcases hinw_t hinw with ⟨hroot, hγ, hT_ne0, hepExp_ec⟩
      have ht_ge1 : 1 ≤ s₁.epoch Q := by omega
      have hsends_s₁ : Q.sendsIn (s₁.epoch Q) = true := by
        rw [hs₁_ep_Q]; exact hsends_succ
      have hstep_fig8 := c7_lFig8_send_step_inWinC P (InvB Inv q (r - 1)) Dh encPt encT idOf lam
        hrt epExp Q (s_fig8.st Q) (s₁.epoch Q) T_base (hinv.hst_id Q)
        (by rw [hinv.htcur Q, hs₁_ep_Q]) ht_ge1 hsends_s₁ hγ pub m_enc (ec Q)
        (by rw [hs₁_ep_Q, hepExp_ec]) s.unackA rfl hspqr
      rcases hstep_fig8 with
        ⟨hid', hroot', htcur', hγ', hTcur', hvR', ⟨v', hvS', hv'_last⟩, hc1, hc2, hhon_wc⟩
      have hsend_ghost := send_withEager_toGhost_eq P Dh encPt encT idOf lam hX hid
        (resolveSim spkKey s) Q (s_fig8.st Q) (hinv.hst_id Q) (hinv.htcur Q).symm
        T_base hγ (by rw [hinv.htcur Q]; exact hrecv) pn m_enc rq pq' salt pqMsg hspqr hnp
        s'.mir (by rw [hs'_ep, hs₁_ep_Q, hinv.htcur Q])
        ((w, c) :: s.honest) (ec Q)
      have hst_R_eq : s_R.st Q =
          withEager (toGhost P (resolveSim spkKey s) Q (s_fig8.st Q))
            ((rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (ec Q) T_base)).1
            (some ⟨KeyPair.generate P.C (ec Q),
              ⟨((rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (ec Q) T_base)).2, 0⟩⟩)
            pn := by
        rw [hinv.hst_R Q, expectedGhost_of_inWin_true _ _ _ _ _ _ _ _ T_base hinw hγ, hpn_eq]
      have hpub_eq : (⟨pn, pqMsg, effectiveHkdfSalt32 salt,
          if Q == Party.A && (resolveSim spkKey s).unackA then P.addrAB else none⟩ : LibsignalMsgPublicPart) =
          pub := by
        simp [pub, resolveSim_unackA, addrs]
      have hres_s'_eq :
          { (resolveSim spkKey s) with
              mir := s'.mir,
              pq := Function.update (resolveSim spkKey s).pq Q pq',
              pn := Function.update (resolveSim spkKey s).pn Q pn,
              honest := (w, c) :: s.honest } = resolveSim spkKey s' := by
        simp [s', resolveSim]
      dsimp only at hsend_ghost
      rw [← hst_R_eq, hpub_eq, hres_s'_eq] at hsend_ghost
      have hout_R_eq : out_R = (toGhost P (resolveSim spkKey s') Q st_fig8', w) := hsend_ghost
      have hw_R_eq : w_R = w := congrArg Prod.snd hout_R_eq
      have hst_R'_eq : st_R' = toGhost P (resolveSim spkKey s') Q st_fig8' :=
        congrArg Prod.fst hout_R_eq
      have hinw'_Q : inReceiveOnlyEpoch s'.mir Q = false := by
        dsimp [inReceiveOnlyEpoch]; rw [hs'_ep, hsends_s₁]; rfl
      have hinw'_other : inReceiveOnlyEpoch s'.mir Q.other = inReceiveOnlyEpoch s.mir Q.other := by
        dsimp [inReceiveOnlyEpoch]; rw [hs'_ep, hs₁_ep_other]
      have hep_Q_le_other : s.mir.epoch Q ≤ s.mir.epoch Q.other := (hinv.hep_adj Q).1 hinw
      have hs₁_le_qep : s₁.epoch Q ≤ qep := by rw [hs₁_ep_Q]; exact hep_le_qep
      refine ⟨hw_R_eq, hst_R'_eq, hinw'_Q, hinw'_other, hsends_s₁, ht_ge1, hs₁_le_qep,
        hs₁_ep_other, hs₁_idx_other, Or.inr ⟨hs₁_ep_Q, hs₁_idx_Q⟩, ?_, ?_, ?_, hid', htcur', hvR',
        hc1, ?_, hhon_wc, ?_, ?_, ?_, ⟨rk_base, T_base, ?_, ?_⟩, ?_⟩
      · rw [hs'_idx_Q, hs₁_idx_Q]
        have := hinv.hidx_le Q
        omega
      · intro R
        rw [hs'_ep]
        by_cases hRQ : R = Q
        · subst hRQ; omega
        · rw [hs₁_ep, Function.update_of_ne hRQ]
      · intro R
        by_cases hRQ : R = Q
        · subst hRQ
          refine ⟨(fun h => by rw [hinw'_Q] at h; cases h), ?_⟩
          rw [hs'_ep, hs₁_ep_Q, hs₁_ep_other]
          omega
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          have hadj_O := (hinv.hep_adj Q.other).2
          rw [Party.other_other] at hadj_O
          rw [hs'_ep, Party.other_other, hs₁_ep_other, hs₁_ep_Q]
          exact ⟨fun _ => hadj_O, by omega⟩
      · rw [hc2, hs₁_idx_Q]
      · rw [hs'_ep]
        cases Q with
        | A =>
          rw [hs₁_ep_Q]
          exact chainsEpochInvA_send_step hinv.hchainsA hsends_succ
        | B =>
          change s₁.epoch .A = s.mir.epoch .A at hs₁_ep_other
          rw [hs₁_ep_other]
          exact hinv.hchainsA
      · rw [hs'_ep]
        cases Q with
        | A =>
          have hmod : (s.mir.epoch .A + 1) % 2 = 1 := by
            simpa [Party.sendsIn] using hsends_succ
          have hdiv : (s.mir.epoch .A + 1) / 2 = s.mir.epoch .A / 2 := by omega
          rw [hs₁_ep_Q, hdiv]
          exact hinv.hchainsA_ep
        | B =>
          change s₁.epoch .A = s.mir.epoch .A at hs₁_ep_other
          rw [hs₁_ep_other]
          exact hinv.hchainsA_ep
      · rw [hs'_ep]
        cases Q with
        | A =>
          change s₁.epoch .B = s.mir.epoch .B at hs₁_ep_other
          rw [hs₁_ep_other]
          exact hinv.hchainsB_ep
        | B =>
          have hmod : (s.mir.epoch .B + 1) % 2 = 0 := by
            simpa [Party.sendsIn] using hsends_succ
          have hdiv : (s.mir.epoch .B + 1 + 1) / 2 = (s.mir.epoch .B + 1) / 2 := by omega
          rw [hs₁_ep_Q, hdiv]
          exact hinv.hchainsB_ep
      · intro h; rw [hinw'_Q] at h; cases h
      · intro _
        rw [hs'_ep, hs'_idx_Q]
        refine ⟨hγ', fun _ => ⟨by rw [hroot', hroot], hTcur'⟩, v', hvS', ?_⟩
        rw [hv'_last, hs₁_idx_Q]
      · intro rk_b T_b hbase_b
        rcases hbase_b.1 hinw with ⟨hrk_b, hγ_b, _⟩
        have hTb : T_b = T_base := by
          rw [hγ] at hγ_b
          injection hγ_b with h; exact h.symm
        subst hTb
        refine ⟨(fun h => by rw [hinw'_Q] at h; cases h), fun _ => ?_⟩
        rw [hs'_ep, hs'_idx_Q]
        refine ⟨hγ', fun _ => ⟨by rw [hroot', hrk_b], hTcur'⟩, v', hvS', ?_⟩
        rw [hv'_last, hs₁_idx_Q]
  rcases hcore with ⟨hw_R_eq, hst_R'_eq, hinw'_Q, hinw'_other, hsends_s₁, ht_ge1,
    hep_le_qep, hs₁_ep_other, hs₁_idx_other, hs₁_cases, hidx_Q_bound, hep_mono, hep_adj', hid',
    htcur', hvR', hc1, hc2, hhon_wc, hchainsA', hchainsA_ep', hchainsB_ep', hspur'_Q, hbase'_Q⟩
  have hfR2 : fR.2 = s_R' := congrArg Prod.snd hfR_eq
  have hres21 : res.2.1 = s' := congrArg (fun x => x.2.1) hres_eq
  have hres22 : res.2.2 = s_fig8' := congrArg (fun x => x.2.2) hres_eq
  have hres1 : res.1 = some w := congrArg Prod.fst hres_eq
  rw [hfR2, hres21, hres22, hres1]
  have hc1_ep : c.1.1 = s₁.epoch Q := congrArg Prod.fst hc1
  have hsender_Q : Party.senderOf c.1.1 = Q := by
    rw [hc1_ep]; exact senderOf_eq_of_sendsIn hsends_s₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmeta' : SameMeta s_R' s' s_fig8' := by
      have hrec_R_eq : rec_R = ⟨⟨Q, s_R₁.epoch Q, s_R₁.idx Q + 1⟩, m_enc, w⟩ := by
        simp [rec_R, hw_R_eq]
      have hs'_eq : s' = {
          mir := s₁.record 3 Q () rec_mir chal.isSome,
          pq := Function.update s.pq Q pq', pn := Function.update s.pn Q pn,
          unackA := s.unackA, honest := (w, c) :: s.honest,
          chains := s.chains, amb := s.amb, stopped := false } := by
        simp [s', hinv.hmeta.hstop]
      change SameMeta (s_R₁.record 3 Q st_R' rec_R chal.isSome) s'
        (s_fig8₁.record 3 Q st_fig8'
          ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, (pub, m_enc), c⟩ chal.isSome)
      rw [hrec_R_eq, hs'_eq]
      exact hmeta₁.record_preserves Q st_R' st_fig8' m_enc m₀ (pub, m_enc) c chal.isSome
        (Function.update s.pq Q pq') (Function.update s.pn Q pn) s.unackA
        ((w, c) :: s.honest) s.chains s.amb
    have hcomp₁ : ∀ p ∈ s₁.comp, SM.healedBy s₁.tL 3 p.epoch = false :=
      comp_healedBy_false_epMgmt hinv.hcomp hep_mir
    have hcomp' : ∀ p ∈ s'.mir.comp, SM.healedBy s'.mir.tL 3 p.epoch = false :=
      comp_healedBy_false_record s₁ 3 Q () rec_mir chal.isSome rfl hcomp₁
    have hec' : ValidEagerCoins s'.mir ec' := by
      dsimp only [ec']
      cases hinw : inReceiveOnlyEpoch s.mir Q with
      | false =>
        rw [ite_eq_right Bool.false_ne_true]
        intro R hR
        by_cases hRQ : R = Q
        · subst hRQ; rw [hinw'_Q] at hR; exact hinv.hec R (hinw ▸ hR)
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO; rw [hinw'_other] at hR; exact hinv.hec Q.other hR
      | true =>
        rw [ite_eq_left rfl]
        exact (updateAllEagerCoins_send_inWin Q s.mir s'.mir ec hinw hinw'_Q hinw'_other
          hinv.hec).2
    exact
      { hmeta := hmeta'
        hcomp := hcomp'
        hec := hec'
        hwinBefore := hinv.hwinBefore
        hamb := by have := hinv.hamb; dsimp [s']; omega
        hamb_strict := by
          rintro (hA | hB)
          · by_cases hpos : 0 < s.mir.epoch .A ∨ 0 < s.mir.epoch .B
            · have := hinv.hamb_strict hpos; dsimp [s']; omega
            · have hA0 : s.mir.epoch .A = 0 := by omega
              have hB0 : s.mir.epoch .B = 0 := by omega
              have hQA : Q = .A := by
                cases Q with
                | A => rfl
                | B =>
                  change 0 < s₁.epoch .A at hA
                  change s₁.epoch .A = s.mir.epoch .A at hs₁_ep_other
                  rw [hs₁_ep_other] at hA; omega
              subst hQA
              have := hinv.hamb
              dsimp [s']; omega
          · have := hinv.hamb
            dsimp [s']; omega
        hidx_le := by
          intro R
          by_cases hRQ : R = Q
          · subst hRQ; exact hidx_Q_bound
          · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
            subst hRO
            have hidx_eq : s'.mir.idx Q.other = s.mir.idx Q.other := by
              change (Function.update s₁.idx Q (s₁.idx Q + 1)) Q.other = s.mir.idx Q.other
              rw [Function.update_of_ne (Party.other_ne Q), hs₁_idx_other]
            rw [hidx_eq]
            have := hinv.hidx_le Q.other
            omega
        hhon_len := by
          change (s.honest.length + 1) + (r - 1) ≤ q
          have := hinv.hhon_len
          omega
        hep_le := by
          intro R
          change s₁.epoch R ≤ qep
          by_cases hRQ : R = Q
          · subst hRQ; exact hep_le_qep
          · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
            subst hRO; rw [hs₁_ep_other]; exact hinv.hep_le Q.other
        hep_adj := hep_adj'
        hst_R := by
          intro R
          by_cases hRQ : R = Q
          · subst hRQ
            have hst_R'_self : s_R'.st R = st_R' := by
              change (Function.update s_R₁.st R st_R') R = st_R'
              exact Function.update_self R st_R' s_R₁.st
            have hst_f'_self : s_fig8'.st R = st_fig8' := by
              change (Function.update s_fig8₁.st R st_fig8') R = st_fig8'
              exact Function.update_self R st_fig8' s_fig8₁.st
            rw [hst_R'_self, hst_f'_self,
                expectedGhost_of_inWin_false _ _ _ _ _ _ _ _ hinw'_Q, hst_R'_eq]
          · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
            subst hRO
            have hst_R'_other : s_R'.st Q.other = s_R.st Q.other := by
              change (Function.update s_R₁.st Q st_R') Q.other = s_R.st Q.other
              rw [Function.update_of_ne (Party.other_ne Q), hst_R₁]
            have hst_f'_other : s_fig8'.st Q.other = s_fig8.st Q.other := by
              change (Function.update s_fig8₁.st Q st_fig8') Q.other = s_fig8.st Q.other
              rw [Function.update_of_ne (Party.other_ne Q), hst_fig8₁]
            have hec'_other : ec' Q.other = ec Q.other := by
              dsimp [ec']; split <;> simp [Function.update_of_ne (Party.other_ne Q)]
            have hidx'_other : s'.mir.idx Q.other = s.mir.idx Q.other := by
              change (Function.update s₁.idx Q (s₁.idx Q + 1)) Q.other = s.mir.idx Q.other
              rw [Function.update_of_ne (Party.other_ne Q), hs₁_idx_other]
            rw [hst_R'_other, hst_f'_other, hec'_other, hinv.hst_R Q.other]
            exact (c7_expectedGhost_congr P Dh encPt spkKey s' s Q.other (s_fig8.st Q.other)
              (ec Q.other) (Function.update_of_ne (Party.other_ne Q) pn s.pn) rfl (fun _ => rfl)
              (Function.update_of_ne (Party.other_ne Q) pq' s.pq) hs₁_ep_other hidx'_other).symm
        hst_id := by
          intro R
          by_cases hRQ : R = Q
          · subst hRQ
            change (Function.update s_fig8₁.st R st_fig8' R).id = R
            rw [Function.update_self, hid']
          · change (Function.update s_fig8₁.st Q st_fig8' R).id = R
            rw [Function.update_of_ne hRQ, hst_fig8₁]
            exact hinv.hst_id R
        htcur := by
          intro R
          by_cases hRQ : R = Q
          · subst hRQ
            change (Function.update s_fig8₁.st R st_fig8' R).tcur = s₁.epoch R
            rw [Function.update_self, htcur']
          · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
            subst hRO
            change (Function.update s_fig8₁.st Q st_fig8' Q.other).tcur = s₁.epoch Q.other
            rw [Function.update_of_ne (Party.other_ne Q), hst_fig8₁, hs₁_ep_other]
            exact hinv.htcur Q.other
        hepExp0 := hinv.hepExp0
        hspur := by
          intro R
          by_cases hRQ : R = Q
          · subst hRQ
            have hst_f'_self : s_fig8'.st R = st_fig8' := by
              change (Function.update s_fig8₁.st R st_fig8') R = st_fig8'
              exact Function.update_self R st_fig8' s_fig8₁.st
            rw [hst_f'_self]
            exact hspur'_Q
          · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
            subst hRO
            have hst_f'_other : s_fig8'.st Q.other = s_fig8.st Q.other := by
              change (Function.update s_fig8₁.st Q st_fig8') Q.other = s_fig8.st Q.other
              rw [Function.update_of_ne (Party.other_ne Q), hst_fig8₁]
            have hec'_other : ec' Q.other = ec Q.other := by
              dsimp [ec']; split <;> simp [Function.update_of_ne (Party.other_ne Q)]
            have hep'_other : s'.mir.epoch Q.other = s.mir.epoch Q.other := hs₁_ep_other
            have hidx'_other : s'.mir.idx Q.other = s.mir.idx Q.other := by
              change (Function.update s₁.idx Q (s₁.idx Q + 1)) Q.other = s.mir.idx Q.other
              rw [Function.update_of_ne (Party.other_ne Q), hs₁_idx_other]
            rcases hinv.hspur Q.other with ⟨rk_base, T_base, hinw_t, hinw_f⟩
            refine ⟨rk_base, T_base, ?_, ?_⟩
            · rw [hinw'_other, hst_f'_other, hep'_other, hec'_other]
              exact hinw_t
            · rw [hinw'_other, hst_f'_other, hep'_other, hidx'_other]
              exact hinw_f
        hchainsA := hchainsA'
        hchainsA_ep := hchainsA_ep'
        hchainsB_ep := hchainsB_ep'
        hchainsB_none := hinv.hchainsB_none
        hchains_sync := by
          intro R g hg
          rcases hinv.hchains_sync R g hg with ⟨hgep, hgsend, hgkey, v, hvR, hsync⟩
          have hvR_eq : (s_fig8'.st R).vR = (s_fig8.st R).vR := by
            by_cases hRQ : R = Q
            · subst hRQ
              change (Function.update s_fig8₁.st R st_fig8' R).vR = (s_fig8.st R).vR
              rw [Function.update_self, hvR']
            · change (Function.update s_fig8₁.st Q st_fig8' R).vR = (s_fig8.st R).vR
              rw [Function.update_of_ne hRQ, hst_fig8₁]
          exact ⟨Nat.le_trans hgep (hep_mono R), hgsend, hgkey, v, by rw [hvR_eq]; exact hvR,
            hsync⟩
        hhon := by
          intro wc hwc
          rcases List.mem_cons.mp hwc with rfl | hwc
          · have hle_max : s₁.epoch Q ≤ max (s'.mir.epoch .A) (s'.mir.epoch .B) := by
              rw [hs'_ep]
              cases Q <;> [exact Nat.le_max_left _ _; exact Nat.le_max_right _ _]
            refine ⟨hhon_wc, ?_, ?_, ?_⟩
            · rw [hc1_ep]; exact hle_max
            · rw [hsender_Q, hc1_ep]; exact hsends_s₁
            · rw [hsender_Q, hc1_ep]; exact le_rfl
          · rcases hinv.hhon wc hwc with ⟨h1, h2, h3, h4⟩
            have hmax_mono : max (s.mir.epoch .A) (s.mir.epoch .B) ≤
                max (s'.mir.epoch .A) (s'.mir.epoch .B) :=
              max_le_max (hep_mono .A) (hep_mono .B)
            exact ⟨h1, Nat.le_trans h2 hmax_mono, h3,
              Nat.le_trans h4 (hep_mono (Party.senderOf wc.2.1.1))⟩
        htrans_hon := by
          intro rec_f hrec
          have htrans_eq : s_fig8'.trans = rec_fig8 :: s_fig8.trans := by
            change rec_fig8 :: s_fig8₁.trans = rec_fig8 :: s_fig8.trans
            have htr : s_fig8₁.trans = s_fig8.trans := by
              unfold SM.GameState.epMgmt at hep_fig8
              split at hep_fig8
              · split at hep_fig8
                · cases hep_fig8
                · injection hep_fig8 with h; subst h; dsimp only; split <;> rfl
              · split at hep_fig8
                · cases hep_fig8
                · injection hep_fig8 with h; subst h; rfl
            rw [htr]
          rw [htrans_eq] at hrec
          rcases List.mem_cons.mp hrec with rfl | hrec
          · refine ⟨List.mem_cons_self, hsender_Q.symm, ?_, ?_⟩
            · change s_fig8₁.epoch Q = c.1.1
              rw [hmeta₁.hepoch_fig8, hc1_ep]
            · change s_fig8₁.idx Q + 1 = c.2.1
              rw [hmeta₁.hidx_fig8, hc2]
          · rcases hinv.htrans_hon rec_f hrec with ⟨h1, h2, h3, h4⟩
            exact ⟨List.mem_cons_of_mem _ h1, h2, h3, h4⟩
        hcoll := by
          intro t₁ t₂ h₁ h₂ hdh
          rw [hs'_ep] at h₁ h₂
          exact hcoll_next t₁ t₂ h₁ h₂ hdh
        hcorrB0 := by dsimp only [s']; exact hcorrB0_epMgmt_record hep_mir hinv.hcorrB0
        hpqInv := by
          intro R
          change InvB Inv q (r - 1) (Function.update s.pq Q pq' R)
          by_cases hRQ : R = Q
          · subst hRQ
            rw [Function.update_self]
            exact hpq'_inv
          · rw [Function.update_of_ne hRQ]
            exact InvB.mono (Nat.sub_le r 1) (hinv.hpqInv R) }
  · intro R rk_b T_b hbase_b
    by_cases hRQ : R = Q
    · subst hRQ
      have hst_f'_self : s_fig8'.st R = st_fig8' := by
        change (Function.update s_fig8₁.st R st_fig8') R = st_fig8'
        exact Function.update_self R st_fig8' s_fig8₁.st
      unfold ValidSpurBase
      rw [hst_f'_self]
      exact hbase'_Q rk_b T_b hbase_b
    · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
      subst hRO
      have hst_f'_other : s_fig8'.st Q.other = s_fig8.st Q.other := by
        change (Function.update s_fig8₁.st Q st_fig8') Q.other = s_fig8.st Q.other
        rw [Function.update_of_ne (Party.other_ne Q), hst_fig8₁]
      have hep'_other : s'.mir.epoch Q.other = s.mir.epoch Q.other := hs₁_ep_other
      have hidx'_other : s'.mir.idx Q.other = s.mir.idx Q.other := by
        change (Function.update s₁.idx Q (s₁.idx Q + 1)) Q.other = s.mir.idx Q.other
        rw [Function.update_of_ne (Party.other_ne Q), hs₁_idx_other]
      unfold ValidSpurBase at hbase_b ⊢
      rw [hinw'_other, hst_f'_other, hep'_other, hidx'_other]
      exact hbase_b
  · intro huniq hidx
    have hold_bound : ∀ wc ∈ s.honest, wc.2.1.1 = s₁.epoch Q → wc.2.2.1 ≤ s₁.idx Q := by
      intro wc hwc heq_ep
      have hle_old := (hinv.hhon wc hwc).2.2.2
      have hsend_wc : Party.senderOf wc.2.1.1 = Q := by
        rw [heq_ep, ← hc1_ep, hsender_Q]
      rw [hsend_wc, heq_ep] at hle_old
      rcases hs₁_cases with ⟨hep_eq, hidx_eq⟩ | ⟨hep_succ, _⟩
      · rw [hidx_eq]
        have h := hidx wc hwc (by rw [hsend_wc, heq_ep, hep_eq])
        rwa [hsend_wc] at h
      · omega
    refine ⟨?_, ?_⟩
    · intro wc₁ h₁ wc₂ h₂ ht hi
      rcases List.mem_cons.mp h₁ with rfl | h₁
      · rcases List.mem_cons.mp h₂ with rfl | h₂
        · rfl
        · exfalso
          have hle := hold_bound wc₂ h₂ (by rw [← ht, hc1_ep])
          dsimp only at hi
          rw [hc2] at hi
          omega
      · rcases List.mem_cons.mp h₂ with rfl | h₂
        · exfalso
          have hle := hold_bound wc₁ h₁ (by rw [ht, hc1_ep])
          dsimp only at hi
          rw [hc2] at hi
          omega
        · exact huniq wc₁ h₁ wc₂ h₂ ht hi
    · intro wc hwc ht
      rcases List.mem_cons.mp hwc with rfl | hwc
      · dsimp only
        rw [hsender_Q, hs'_idx_Q, hc2]
      · by_cases hRQ : Party.senderOf wc.2.1.1 = Q
        · rw [hRQ] at ht ⊢
          change wc.2.1.1 = s₁.epoch Q at ht
          have hle := hold_bound wc hwc ht
          rw [hs'_idx_Q]
          omega
        · have hRO : Party.senderOf wc.2.1.1 = Q.other := by
            cases Q <;> cases h : Party.senderOf wc.2.1.1 <;>
              first | exact absurd h hRQ | rfl
          have hep_O :
              s'.mir.epoch (Party.senderOf wc.2.1.1) = s.mir.epoch (Party.senderOf wc.2.1.1) := by
            rw [hRO]; exact hs₁_ep_other
          have hidx_O :
              s'.mir.idx (Party.senderOf wc.2.1.1) = s.mir.idx (Party.senderOf wc.2.1.1) := by
            rw [hRO]
            change (Function.update s₁.idx Q (s₁.idx Q + 1)) Q.other = s.mir.idx Q.other
            rw [Function.update_of_ne (Party.other_ne Q), hs₁_idx_other]
          rw [hep_O] at ht
          rw [hidx_O]
          exact hidx wc hwc ht
  · intro sC hsC hkept hsync
    set sC' := cxSend P Dh encPt encT idOf lam Q sC s' (some w)
    have hst_f' : s_fig8'.st = Function.update s_fig8.st Q
        ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q)
          (pub, m_enc) (ec Q)).1 := by
      funext R
      change Function.update s_fig8₁.st Q st_fig8' R = Function.update s_fig8.st Q st_fig8' R
      by_cases hRQ : R = Q
      · subst hRQ; simp
      · simp [Function.update_of_ne hRQ, hst_fig8₁]
    have hhonEp : ∀ wc ∈ s.honest, wc.2.1.1 ≤ (s_fig8.st (Party.senderOf wc.2.1.1)).tcur := by
      intro wc hwc
      rw [hinv.htcur]
      exact (hinv.hhon wc hwc).2.2.2
    refine ⟨keptInv_send hkept Q (hinv.hst_id Q) (pub, m_enc) (ec Q) hst_f' rfl, ?_⟩
    have hrc : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = true →
        epExp ((s_fig8.st Q).tcur + 1) = ec Q := by
      intro hsends_next
      rw [hinv.hst_id Q, hinv.htcur Q] at hsends_next
      rw [hinv.htcur Q]
      have hinw : inReceiveOnlyEpoch s.mir Q = true := by
        unfold inReceiveOnlyEpoch
        cases hs : Q.sendsIn (s.mir.epoch Q)
        · rfl
        · rw [sendsIn_succ_of_sendsIn Q (s.mir.epoch Q) hs] at hsends_next
          cases hsends_next
      rcases hinv.hspur Q with ⟨_, _, hinw_t, _⟩
      exact (hinw_t hinw).2.2.2
    rw [hsC] at hsync
    refine epochSync_send P Dh hDh encPt encT idOf lam hD hrt s.honest ((w, c) :: s.honest)
      sC.sent sC'.sent s_fig8 s_fig8' hsync hkept.hvR hinv.hst_id hhonEp Q (pub, m_enc) (ec Q)
      hrc hst_f' (fun _ => hinv.hmeta.hwin_fig8) ?_ ?_ hpub_pq hpub_addr
    · intro wc hwc
      rcases List.mem_cons.mp hwc with rfl | hwc
      · exact Or.inr rfl
      · exact Or.inl hwc
    · intro e he
      dsimp only [sC', cxSend, s', List.head?_cons] at he
      cases hkf : (sC.kept Q).full with
      | none =>
        rw [hkf] at he
        exact Or.inl he
      | some st₀ =>
        rw [hkf] at he
        dsimp only at he
        have hst₀ : st₀ = s_fig8.st Q := hkept.hfull Q st₀ hkf
        subst hst₀
        by_cases hsends_next : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = true
        · rw [hsends_next, ite_eq_left rfl] at he
          exact Or.inl he
        · have hsends_next_f : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = false :=
            Bool.eq_false_iff.mpr hsends_next
          rw [hsends_next_f, ite_eq_right Bool.false_ne_true] at he
          cases hvS : (s_fig8.st Q).vS with
          | none =>
            rw [hvS] at he
            exact Or.inl he
          | some v =>
            rw [hvS] at he
            rcases List.mem_cons.mp he with rfl | he
            · exact Or.inr ⟨hsends_next_f, rfl, rfl⟩
            · exact Or.inl he

theorem simSendStep_inWin_preserves_simInvCXLazy
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r' r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (hr : r' < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : BitVec 512) (c_cka : BitVec 256)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore
      epExp)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = true)
    (hnoBob : SM.noBobSendInEpoch0 sC.base.mir Q = true)
    (hep : sC.base.mir.epMgmt 3 qep Q bad = some s₁)
    (hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true)
    (hrc0 : c_cka ≠ 0)
    (hrc_coll : ∀ t ≤ max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B),
      Dh.dh c_cka Dh.base ≠ Dh.dh (epExp t) Dh.base) :
    let epExp' := Function.update epExp (sC.base.mir.epoch Q + 1) c_cka
    let ec_rc := Function.update ec Q c_cka
    let ghost_rc :=
      expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) sC.base Q (s_fig8.st Q) c_cka
    let s_R_rc := { s_R with st := Function.update s_R.st Q ghost_rc }
    let fR := chal.elim
      (transmitPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep Q m₀ rq bad s_R_rc)
      (fun m₁ => challPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep SM.Config.h1 Q m₀ m₁ rq bad
        s_R_rc)
    let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka
      (sC.base, s_fig8)
    let ec' := if inReceiveOnlyEpoch sC.base.mir Q then Function.update ec_rc Q 0 else ec_rc
    let sC' := cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1
    SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ fR.2 sC' res.2.2 ec' winBefore
      epExp' ∧
    (∀ R rk_b T_b,
      ValidSpurBase P ℓ Dh encPt sC.base s_fig8 epExp R rk_b T_b →
      ValidSpurBase P ℓ Dh encPt sC'.base res.2.2 epExp' R rk_b T_b) := by
  intro epExp' ec_rc ghost_rc s_R_rc fR res ec' sC'
  obtain ⟨hinv_rc, hbase_rc, hcoll_rc⟩ :=
    simInvCXLazy_recoin_inWin hinv hinw hnoBob hrc0 hrc_coll
  rcases c7_sendsIn_succ_of_inWin_true sC.base.mir Q hinw with ⟨_, hsends_succ⟩
  rcases c7_epMgmt_of_sendsIn_succ_true sC.base.mir 3 qep Q bad hsends_succ hep with
    ⟨hs₁_ep, _, _, _, _, _, _⟩
  obtain ⟨hep_other, _, _⟩ := inWin_true_epoch_other_eq hinv.hsim hinw hnoBob
  have hmax_s₁ : max (s₁.epoch .A) (s₁.epoch .B) ≤ sC.base.mir.epoch Q + 1 := by
    rw [hs₁_ep]
    cases Q <;> simp [Party.other, Function.update] at hep_other ⊢ <;> omega
  have hcoll_next : ∀ t₁ t₂,
      t₁ ≤ max (s₁.epoch .A) (s₁.epoch .B) →
      t₂ ≤ max (s₁.epoch .A) (s₁.epoch .B) →
      Dh.dh (epExp' t₁) Dh.base = Dh.dh (epExp' t₂) Dh.base → t₁ = t₂ :=
    fun t₁ t₂ ht₁ ht₂ hdh =>
      hcoll_rc t₁ t₂ (Nat.le_trans ht₁ hmax_s₁) (Nat.le_trans ht₂ hmax_s₁) hdh
  have hec_rc_Q : ec_rc Q = c_cka := Function.update_self Q c_cka ec
  have hpres := c7_simSendStep_preserves_simInvCLazy_at_ec P Inv ℓ Dh hDh encPt encT decT idOf
    hX hD hrt hid lam qep q r hS hq32 (Nat.zero_lt_of_lt hr) Q m₀ chal bad s₁ rq
    x₀ s_R_rc sC.base s_fig8 ec_rc winBefore epExp' hinv_rc.hsim hnoBob hep hsafeCh hcoll_next
  dsimp only at hpres
  rw [hec_rc_Q] at hpres
  have hbase : sC'.base = res.2.1 :=
    c7_cxSend_base P Dh encPt encT idOf lam Q sC res.2.1 res.1
  rcases hpres.2.2.1 hinv_rc.huniq hinv_rc.hidx with ⟨huniq', hidx'⟩
  rcases hpres.2.2.2 sC rfl hinv_rc.hkept hinv_rc.hsync with ⟨hkept', hsync'⟩
  have hcx : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ fR.2 sC' res.2.2 ec'
      winBefore epExp' :=
    ⟨hbase ▸ hpres.1, hbase ▸ huniq', hkept', hbase ▸ hidx', hsync'⟩
  refine ⟨simInvCXLazy_mono_r hcx (Nat.le_sub_one_of_lt hr), fun R rk_b T_b hb => ?_⟩
  rw [hbase]
  exact hpres.2.1 R rk_b T_b (hbase_rc R rk_b T_b hb)

theorem simSendStep_new_epoch_preserves_evictedSpurSimInvLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r' r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (hr : r' < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : BitVec 512) (c_cka : BitVec 256)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC g ec winBefore epExp)
    (hspur_lazy : ∀ R, ∃ w_acc rk_base T_base,
      ValidEvictAccWitness P K sC.base R w_acc ∧
      ValidSpurBase P ℓ Dh encPt sC.base g epExp R rk_base T_base ∧
      (inReceiveOnlyEpoch sC.base.mir R = false →
        spurBadList P encPt Dh R rk_base T_base
          (Proofs.Refinement.evictedSpurCandList P epExp w_acc
            (Proofs.Refinement.honestBeforeEpoch sC.base.honest
              (Proofs.Refinement.evictAccEpoch sC.base.mir R)))
          (epExp (sC.base.mir.epoch R)) = false))
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = true)
    (hnoBob : SM.noBobSendInEpoch0 sC.base.mir Q = true)
    (hep : sC.base.mir.epMgmt 3 qep Q bad = some s₁)
    (hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true)
    (w_acc_Q : CryptoVerification.SpqrV1Sync.SendTotal.TopWitness P.C.F)
    (rk_base_Q : Ratchet.RootKey) (T_base_Q : Pt)
    (hw_acc_Q : ValidEvictAccWitness P K sC.base Q w_acc_Q)
    (hbase_Q : ValidSpurBase P ℓ Dh encPt sC.base g epExp Q rk_base_Q T_base_Q)
    (hno_coll : sendCoinCollBad Dh epExp
      (max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B)) c_cka = false)
    (hno_spur_new : spurBadList P encPt Dh Q rk_base_Q T_base_Q
      (Proofs.Refinement.evictedSpurCandList P epExp w_acc_Q
        (Proofs.Refinement.honestBeforeEpoch sC.base.honest
          (Proofs.Refinement.evictAccEpoch sC.base.mir Q)))
      c_cka = false) :
    let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka (sC.base, g)
    let sC' := cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1
    EvictedSpurSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r' sC' res.2.2 := by
  intro res sC'
  obtain ⟨hrc0, hrc_coll⟩ := sendCoinCollBad_eq_false_imp Dh epExp
    (max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B)) hno_coll
  obtain ⟨hcx, hbase_pres⟩ := simSendStep_inWin_preserves_simInvCXLazy P Inv ℓ Dh hDh encPt encT
    decT idOf hX hD hrt hid lam qep q r' r hS hq32 hr Q m₀ chal bad s₁ rq c_cka
    x₀ s_R sC g ec winBefore epExp hinv hinw hnoBob hep hsafeCh hrc0 hrc_coll
  set epExp' := Function.update epExp (sC.base.mir.epoch Q + 1) c_cka
  have hres_win : { res.2.2 with win := false } = res.2.2 := by
    have hw := hcx.hsim.hmeta.hwin_fig8
    revert hw; cases res.2.2; simp_all
  rcases c7_sendsIn_succ_of_inWin_true sC.base.mir Q hinw with ⟨_, hsends_succ⟩
  rcases c7_epMgmt_of_sendsIn_succ_true sC.base.mir 3 qep Q bad hsends_succ hep with
    ⟨hs₁_ep, _, _, _, _, _, _⟩
  set pn :=
    if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
    else sC.base.pn Q
  obtain ⟨pq', salt, pqMsg, hspqr_send, hmk⟩ :=
    mkPub_eq_some_of_spqrCLocal hS (Nat.zero_lt_of_lt hr) sC.base Q rq pn (hinv.hsim.hpqInv Q)
  set pub : LibsignalMsgPublicPart :=
    ⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == Party.A && sC.base.unackA then P.addrAB else none⟩
  obtain ⟨_, _, _, hf8_eq⟩ :=
    f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ chal c_cka
      bad s₁ s_R sC.base g hinv.hsim.hmeta hep hsafeCh
  have hf8_1 : (chal.elim
      (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
        (pub, m₀) c_cka bad g)
      (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad g)).1 =
      some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
        (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka).2 :=
    congrArg Prod.fst hf8_eq
  have hsim_eq := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ chal
    bad s₁ rq c_cka sC.base g pq' pub _ hmk hf8_1
  have hbase : sC'.base = res.2.1 :=
    c7_cxSend_base P Dh encPt encT idOf lam Q sC res.2.1 res.1
  have hres_2_1 : res.2.1 = (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad
      s₁ rq c_cka (sC.base, g)).2.1 := rfl
  rw [hsim_eq] at hres_2_1
  rcases hbase_Q.1 hinw with ⟨_, hγ, _⟩
  obtain ⟨_, hc_aead⟩ :=
    lFig8_send_eq_lAead_inWin P ℓ Dh encPt encT idOf lam Q (g.st Q)
      (sC.base.mir.epoch Q + 1) T_base_Q (hinv.hsim.hst_id Q) (by rw [hinv.hsim.htcur Q])
      hsends_succ hγ pub (chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka
  have hc_ep :
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
        (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka).2.1.1 =
      sC.base.mir.epoch Q + 1 :=
    congrArg (·.1.1) hc_aead
  have hhon' : sC'.base.honest =
      (toWire ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
        (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka).2,
       ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
        (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka).2) ::
        sC.base.honest := by
    rw [hbase, hres_2_1]
  have hpq' : sC'.base.pq = Function.update sC.base.pq Q pq' := by
    rw [hbase, hres_2_1]
  have hep' :
      sC'.base.mir.epoch = Function.update sC.base.mir.epoch Q (sC.base.mir.epoch Q + 1) := by
    rw [hbase, hres_2_1]; exact hs₁_ep
  have hinwQ' : inReceiveOnlyEpoch sC'.base.mir Q = false := by
    unfold inReceiveOnlyEpoch; rw [hep', Function.update_self, hsends_succ]; rfl
  obtain ⟨hep_other, _, hmax_eq⟩ := inWin_true_epoch_other_eq hinv.hsim hinw hnoBob
  have hother_le : sC.base.mir.epoch Q.other ≤ sC.base.mir.epoch Q + 1 := by omega
  have hev_hon := evictAccEpoch_and_honestBeforeEpoch_new_epoch_send
    hinw hinwQ' hep' hhon' hc_ep hother_le
  have hreach_step : ∀ R,
      Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K)
        (sC.base.pq R) (sC'.base.pq R) := by
    intro R
    rw [hpq']
    by_cases hRQ : R = Q
    · subst hRQ
      rw [Function.update_self]
      exact .send (.refl _) (hspqr_eq ▸ hspqr_send)
    · rw [Function.update_of_ne hRQ]
      exact .refl _
  have hw_acc_pres : ∀ R w_a,
      ValidEvictAccWitness P K sC.base R w_a →
      ValidEvictAccWitness P K sC'.base R w_a := by
    intro R w_a hw_a hge
    rw [(hev_hon R).1] at hge ⊢
    obtain ⟨w_acc_wire, c_acc, h_acc, body_acc, pq_acc, pq_acc', salt_acc,
        hc_mem, hc_eq, hc_sender, hparse_acc, hw_top_a, hrecv_acc, hreach₀⟩ := hw_a hge
    refine ⟨w_acc_wire, c_acc, h_acc, body_acc, pq_acc, pq_acc', salt_acc,
      ?_, hc_eq, hc_sender, hparse_acc, hw_top_a, hrecv_acc,
      Proofs.Refinement.spqrReachFrom_trans hreach₀ (hreach_step R)⟩
    rw [hhon']
    exact List.mem_cons_of_mem _ hc_mem
  have hcand_eq : ∀ R w_a,
      Proofs.Refinement.evictedSpurCandList P epExp' w_a
        (Proofs.Refinement.honestBeforeEpoch sC.base.honest
          (Proofs.Refinement.evictAccEpoch sC.base.mir R)) =
      Proofs.Refinement.evictedSpurCandList P epExp w_a
        (Proofs.Refinement.honestBeforeEpoch sC.base.honest
          (Proofs.Refinement.evictAccEpoch sC.base.mir R)) := by
    intro R w_a
    refine evictedSpurCandList_congr_epExp P w_a _ fun wc hwc => ?_
    have hmem_hon : wc ∈ sC.base.honest := (List.mem_filter.mp hwc).1
    have hle_max : wc.2.1.1 ≤ max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B) :=
      (hinv.hsim.hhon wc hmem_hon).2.1
    dsimp [epExp']
    rw [Function.update_of_ne (by omega)]
  rw [← hres_win] at hcx hbase_pres
  refine ⟨x₀, _, _, winBefore, epExp', hcx, fun R => ?_⟩
  by_cases hRQ : R = Q
  · subst hRQ
    refine ⟨w_acc_Q, rk_base_Q, T_base_Q, hw_acc_pres R w_acc_Q hw_acc_Q,
      hbase_pres R rk_base_Q T_base_Q hbase_Q, fun _ => ?_⟩
    rw [(hev_hon R).2, hcand_eq R w_acc_Q, hep', Function.update_self]
    have hepExp'_succ : epExp' (sC.base.mir.epoch R + 1) = c_cka :=
      Function.update_self (sC.base.mir.epoch R + 1) c_cka epExp
    rw [hepExp'_succ]
    exact hno_spur_new
  · obtain ⟨w_acc_R, rk_b_R, T_b_R, hw_R, hb_R, hno_R⟩ := hspur_lazy R
    refine ⟨w_acc_R, rk_b_R, T_b_R, hw_acc_pres R w_acc_R hw_R,
      hbase_pres R rk_b_R T_b_R hb_R, fun hinwR' => ?_⟩
    have hinwR : inReceiveOnlyEpoch sC.base.mir R = false := by
      unfold inReceiveOnlyEpoch at hinwR' ⊢
      rwa [hep', Function.update_of_ne hRQ] at hinwR'
    have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
    have hepExp'_R : epExp' (sC.base.mir.epoch R) = epExp (sC.base.mir.epoch R) := by
      dsimp [epExp']
      rw [Function.update_of_ne (by subst hRO; omega)]
    rw [(hev_hon R).2, hcand_eq R w_acc_R, hep', Function.update_of_ne hRQ, hepExp'_R]
    exact hno_R hinwR

theorem kemFailSendStep_some_run_eq_bind_simSendStep
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (rq : BitVec 512)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q true = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false)
    (hg_win : g.win = false)
    (hmeta : SameMeta s_R sC.base g)
    (hpq : InvB Inv q r (sC.base.pq Q)) :
    (kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal (some rq)).run
      (sC, (g, false), tr) =
    (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
      let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal true s₁ rq c_cka
        (sC.base, g)
      pure (res.1,
        (cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1, (res.2.2, false),
          stepKemFailSend P.C.F K tr Q rq))) := by
  have hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true := by
    intro hch; revert hg3; rw [hch]; cases s₁.safeCh 3 Q <;> simp
  set pn :=
    if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
    else sC.base.pn Q
  obtain ⟨pq', salt, pqMsg, _, hmk⟩ :=
    mkPub_eq_some_of_spqrCLocal hS hr sC.base Q rq pn hpq
  set pub : LibsignalMsgPublicPart :=
    ⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == Party.A && sC.base.unackA then P.addrAB else none⟩
  unfold kemFailSendStep
  rw [stateT_run_get_bind_prod3]
  simp only [Option.isSome_some, hg1, Bool.false_eq_true, ↓reduceIte, hep, hg3,
    StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
    map_eq_bind_pure_comp, Function.comp_apply, pure_bind, bind_assoc]
  refine bind_congr fun c_cka => ?_
  obtain ⟨s_fig8₁, _, _, hf8_eq⟩ :=
    f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ chal c_cka
      true s₁ s_R sC.base g hmeta hep hsafeCh
  have hf8_1 : (chal.elim
      (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
        (pub, m₀) c_cka true g)
      (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka true g)).1 =
      some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
        (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka).2 :=
    congrArg Prod.fst hf8_eq
  have hsim_eq := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ chal
    true s₁ rq c_cka sC.base g pq' pub _ hmk hf8_1
  dsimp only [pn] at hmk hsim_eq ⊢
  rw [hmk]
  dsimp only
  cases chal with
  | none =>
    simp only [Option.elim] at hf8_eq hsim_eq ⊢
    rw [probeHook_lift_transmitQuery_run]
    simp only [hg_win, Bool.false_eq_true, ↓reduceIte, SM.samIfNec,
      StateT.run_monadLift, MonadLiftT.monadLift,
      StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, hf8_eq, hsim_eq]
    rfl
  | some m₁ =>
    simp only [Option.elim] at hf8_eq hsim_eq ⊢
    rw [probeHook_lift_challQuery_run]
    simp only [hg_win, Bool.false_eq_true, ↓reduceIte, SM.samIfNec,
      StateT.run_monadLift, MonadLiftT.monadLift,
      StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, hf8_eq, hsim_eq]
    rfl

theorem kemFailSendStep_none_run_eq_bind_simSendStep
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q false = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false)
    (hg_win : g.win = false)
    (hmeta : SameMeta s_R sC.base g)
    (hpq : InvB Inv q r (sC.base.pq Q)) :
    (kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal none).run
      (sC, (g, false), tr) =
    (($ᵗ BitVec 512 : ProbComp (BitVec 512)) >>= fun rq =>
      ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal false s₁ rq c_cka
          (sC.base, g)
        pure (res.1,
          (cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1, (res.2.2, false),
            stepKemFailSend P.C.F K tr Q rq))) := by
  have hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true := by
    intro hch; revert hg3; rw [hch]; cases s₁.safeCh 3 Q <;> simp
  set pn :=
    if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
    else sC.base.pn Q
  unfold kemFailSendStep
  rw [stateT_run_get_bind_prod3]
  simp only [Option.isSome_none, hg1, Bool.false_eq_true, ↓reduceIte, hep, hg3,
    StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
    pure_bind, bind_assoc]
  refine bind_congr fun rq => ?_
  obtain ⟨pq', salt, pqMsg, _, hmk⟩ :=
    mkPub_eq_some_of_spqrCLocal hS hr sC.base Q rq pn hpq
  set pub : LibsignalMsgPublicPart :=
    ⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == Party.A && sC.base.unackA then P.addrAB else none⟩
  dsimp only [pn] at hmk ⊢
  rw [hmk]
  dsimp only
  cases chal with
  | none =>
    rw [probeHook_lift_transmitQuery_run]
    simp only [hg_win, Bool.false_eq_true, ↓reduceIte, SM.samIfNec,
      StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      bind_assoc, pure_bind]
    refine bind_congr fun c_cka => ?_
    obtain ⟨_, _, _, hf8_eq⟩ :=
      f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ none c_cka
        false s₁ s_R sC.base g hmeta hep hsafeCh
    have hf8_1 : (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
        (pub, m₀) c_cka false g).1 =
        some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
          (pub, m₀) c_cka).2 :=
      congrArg Prod.fst hf8_eq
    have hsim_eq := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ none
      false s₁ rq c_cka sC.base g pq' pub _ hmk hf8_1
    simp only [Option.elim] at hf8_eq hsim_eq ⊢
    simp only [hf8_eq, hsim_eq, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    rfl
  | some m₁ =>
    rw [probeHook_lift_challQuery_run]
    simp only [hg_win, Bool.false_eq_true, ↓reduceIte, SM.samIfNec,
      StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      bind_assoc, pure_bind]
    refine bind_congr fun c_cka => ?_
    obtain ⟨_, _, _, hf8_eq⟩ :=
      f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ (some m₁) c_cka
        false s₁ s_R sC.base g hmeta hep hsafeCh
    have hf8_1 : (challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka false g).1 =
        some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
          (pub, if s_R.b then m₁ else m₀) c_cka).2 :=
      congrArg Prod.fst hf8_eq
    have hsim_eq := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁)
      false s₁ rq c_cka sC.base g pq' pub _ hmk hf8_1
    simp only [Option.elim] at hf8_eq hsim_eq ⊢
    simp only [hf8_eq, hsim_eq, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    rfl

/-- On a new sending epoch, `kemFailSendStep` preserves `EvictedSpurHistSimInvLazy` outside
`spurBadList` and `sendCoinCollBad`. -/
theorem kemFailSendStep_new_epoch_preserves_evictedSpurHistSimInvLazy_of_good_coin
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (Inv : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, Inv n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r' r w_rem : ℕ) (hS : SpqrCLocal P.spqr q Inv)
    (hq32 : q < 2 ^ 32) (hr : r' < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r_coin : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r w_rem sC g)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = true) :
    (∀ z ∈ support ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin).run
        (sC, (g, false), tr)),
      z.1 = none ∧ z.2.1 = sC ∧ z.2.2.1 = (g, false) ∧
      EvictedSpurHistSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r' w_rem z.2.1 z.2.2.1.1) ∨
    (0 < w_rem ∧
      ∃ (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
        (rk_base : Ratchet.RootKey) (T_base : Pt)
        (L : List (List (BitVec 8) × Salt × BitVec 256))
        (epExp : ℕ → BitVec 256),
        g.win = false ∧
        (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false ∧
        sC.base.mir.epMgmt 3 qep Q r_coin.isSome = some s₁ ∧
        (chal.isSome && !s₁.safeCh 3 Q) = false ∧
        L.length ≤ q ∧
        max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B) ≤ qep ∧
        ∀ rq c_cka,
          (spurBadList P encPt Dh Q rk_base T_base L c_cka ||
            sendCoinCollBad Dh epExp
              (max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B)) c_cka) = false →
          let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r_coin.isSome s₁ rq
            c_cka (sC.base, g)
          let sC' := cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1
          EvictedSpurHistSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r' (w_rem - 1)
            sC' res.2.2) := by
  obtain ⟨x₀, s_R, ec, winBefore, epExp, hinv, hspur_lazy⟩ := hInv.2
  by_cases hg_win : g.win = true
  · refine Or.inl fun z hz => ?_
    obtain ⟨hz1, hsC, hg⟩ := kemFailSendStep_of_fig8_win P K ℓ Dh encPt encT decT idOf lam qep Q
      m₀ chal r_coin sC g tr hg_win z hz
    refine ⟨hz1, hsC, hg, ?_⟩
    rw [hsC, congrArg Prod.fst hg]
    exact evictedSpurHistSimInvLazy_mono_r hInv (Nat.le_of_lt hr)
  have hg_win_f : g.win = false := Bool.eq_false_iff.mpr hg_win
  have hg_clear : { g with win := false } = g := by cases g; simp_all
  rw [hg_clear] at hinv hspur_lazy
  by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · refine Or.inl fun z hz => ?_
    rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin
      sC (g, false) tr (Or.inl hg1), support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, rfl, rfl, evictedSpurHistSimInvLazy_mono_r hInv (Nat.le_of_lt hr)⟩
  have hg1_f : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false :=
    Bool.eq_false_iff.mpr hg1
  have hnoBob : SM.noBobSendInEpoch0 sC.base.mir Q = true := by
    revert hg1_f; cases sC.base.stopped <;> cases sC.base.mir.win <;>
      cases SM.noBobSendInEpoch0 sC.base.mir Q <;> simp
  cases hep : sC.base.mir.epMgmt 3 qep Q r_coin.isSome with
  | none =>
    refine Or.inl fun z hz => ?_
    rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin
      sC (g, false) tr (Or.inr (Or.inl hep)), support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, rfl, rfl, evictedSpurHistSimInvLazy_mono_r hInv (Nat.le_of_lt hr)⟩
  | some s₁ =>
    by_cases hg3 : (chal.isSome && !s₁.safeCh 3 Q) = true
    · refine Or.inl fun z hz => ?_
      rw [kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin
        sC (g, false) tr (Or.inr (Or.inr ⟨s₁, hep, hg3⟩)),
        support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨rfl, rfl, rfl, evictedSpurHistSimInvLazy_mono_r hInv (Nat.le_of_lt hr)⟩
    have hg3_f : (chal.isSome && !s₁.safeCh 3 Q) = false := Bool.eq_false_iff.mpr hg3
    have hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true := by
      intro hch; revert hg3_f; rw [hch]; cases s₁.safeCh 3 Q <;> simp
    obtain ⟨w_acc_Q, rk_base_Q, T_base_Q, hw_acc_Q, hbase_Q, _⟩ := hspur_lazy Q
    set L := Proofs.Refinement.evictedSpurCandList P epExp w_acc_Q
      (Proofs.Refinement.honestBeforeEpoch sC.base.honest
        (Proofs.Refinement.evictAccEpoch sC.base.mir Q))
    have hL_len : L.length ≤ q := by
      have h1 := Proofs.Refinement.evictedSpurCandList_length_le P epExp w_acc_Q
        (Proofs.Refinement.honestBeforeEpoch sC.base.honest
          (Proofs.Refinement.evictAccEpoch sC.base.mir Q))
      have h2 : (Proofs.Refinement.honestBeforeEpoch sC.base.honest
          (Proofs.Refinement.evictAccEpoch sC.base.mir Q)).length ≤ sC.base.honest.length :=
        List.length_filter_le _ _
      have h3 := hinv.hsim.hhon_len
      dsimp only [L]
      omega
    have hmax_le_qep : max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B) ≤ qep :=
      max_le (hinv.hsim.hep_le .A) (hinv.hsim.hep_le .B)
    rcases c7_sendsIn_succ_of_inWin_true sC.base.mir Q hinw with ⟨_, hsends_succ⟩
    rcases c7_epMgmt_of_sendsIn_succ_true sC.base.mir 3 qep Q r_coin.isSome hsends_succ hep with
      ⟨hs₁_ep, _, _, _, _, _, hep_le_qep⟩
    have hw_pos : 0 < w_rem := by
      obtain ⟨hpos, _⟩ := remSendEpochs_new_send_epoch qep sC.base.mir s₁ Q
        hsends_succ hep_le_qep (hinv.hsim.hep_le Q.other) hs₁_ep
      exact lt_of_lt_of_le hpos hInv.1.hw_rem
    refine Or.inr ⟨hw_pos, s₁, rk_base_Q, T_base_Q, L, epExp, hg_win_f, hg1_f, rfl, hg3_f,
      hL_len, hmax_le_qep, fun rq c_cka hgood => ?_⟩
    simp only [Bool.or_eq_false_iff] at hgood
    rcases hgood with ⟨hno_spur_new, hno_coll⟩
    set pn :=
      if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
      else sC.base.pn Q
    obtain ⟨pq', salt, pqMsg, hspqr_send, hmk⟩ :=
      mkPub_eq_some_of_spqrCLocal hS (Nat.zero_lt_of_lt hr) sC.base Q rq pn (hinv.hsim.hpqInv Q)
    set pub : LibsignalMsgPublicPart :=
      ⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == Party.A && sC.base.unackA then P.addrAB else none⟩
    obtain ⟨_, _, _, hf8_eq⟩ :=
      f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ chal c_cka
        r_coin.isSome s₁ s_R sC.base g hinv.hsim.hmeta hep hsafeCh
    have hf8_1 : (chal.elim
        (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
          (pub, m₀) c_cka r_coin.isSome g)
        (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka r_coin.isSome g)).1 =
        some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
          (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka).2 :=
      congrArg Prod.fst hf8_eq
    have hsim_eq := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ chal
      r_coin.isSome s₁ rq c_cka sC.base g pq' pub _ hmk hf8_1
    set res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r_coin.isSome s₁ rq
      c_cka (sC.base, g)
    set sC' := cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1
    have hbase : sC'.base = res.2.1 :=
      c7_cxSend_base P Dh encPt encT idOf lam Q sC res.2.1 res.1
    have hres_2_1 : res.2.1 = _ := congrArg (·.2.1) hsim_eq
    rcases hbase_Q.1 hinw with ⟨_, hγ, _⟩
    obtain ⟨seed, hc_aead⟩ :=
      lFig8_send_eq_lAead_inWin P ℓ Dh encPt encT idOf lam Q (g.st Q)
        (sC.base.mir.epoch Q + 1) T_base_Q (hinv.hsim.hst_id Q) (by rw [hinv.hsim.htcur Q])
        hsends_succ hγ pub (chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka
    rcases hinv.hsim.hpqInv Q with ⟨n_pq, _, hI_pq⟩
    rcases hInv_top n_pq (sC.base.pq Q) hI_pq with ⟨w_top, hw_top⟩
    have hsender : Party.senderOf (sC.base.mir.epoch Q + 1) = Q := by
      cases Q <;> simp [Party.sendsIn, Party.senderOf] at hsends_succ ⊢ <;> omega
    have hpq' : sC'.base.pq = Function.update sC.base.pq Q pq' := by rw [hbase, hres_2_1]
    have hhon' : sC'.base.honest =
        (LibsignalSim.toWire
          ((sC.base.mir.epoch Q + 1, some (Dh.dh c_cka Dh.base)),
            (1, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
              seed (1, (sC.base.mir.epoch Q + 1, some (Dh.dh c_cka Dh.base)))
              (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)))),
         ((sC.base.mir.epoch Q + 1, some (Dh.dh c_cka Dh.base)),
            (1, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
              seed (1, (sC.base.mir.epoch Q + 1, some (Dh.dh c_cka Dh.base)))
              (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀))))) ::
          sC.base.honest := by
      rw [hbase, hres_2_1, ← hc_aead]
    have hep' :
        sC'.base.mir.epoch = Function.update sC.base.mir.epoch Q (sC.base.mir.epoch Q + 1) := by
      rw [hbase, hres_2_1]; exact hs₁_ep
    have hnew := evictedSpurHistGameInv_send_new_epoch hspqr_eq hInv.1 hsender hspqr_send hpq' hhon'
      (fun R t' ht' => by rwa [hbase, hres_2_1] at ht') hw_top
      (lAead_enc_parse_pqRatchet P ℓ encT idOf hrt Q sC.base.unackA (sC.base.pq Q) pq' rq salt
        seed 1 (sC.base.mir.epoch Q + 1) (Dh.dh c_cka Dh.base) pub
        (chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) rfl hspqr_send)
      (fun w₀ c₀ hmem hsender₀ =>
        Nat.le_succ_of_le (hsender₀ ▸ (hinv.hsim.hhon (w₀, c₀) hmem).2.2.2))
      hsends_succ hep_le_qep (hinv.hsim.hep_le Q.other) hep'
    refine ⟨hnew.2, simSendStep_new_epoch_preserves_evictedSpurSimInvLazy P K hspqr_eq Inv ℓ
      Dh hDh encPt encT decT idOf hX hD hrt hid lam qep q r' r hS hq32 hr Q m₀ chal r_coin.isSome
      s₁ rq c_cka x₀ s_R sC g ec winBefore epExp hinv hspur_lazy hinw hnoBob hep hsafeCh
      w_acc_Q rk_base_Q T_base_Q hw_acc_Q hbase_Q hno_coll hno_spur_new⟩

omit [DecidableEq Pt] [SampleableType Pt] in
theorem lFig8_receive_knownChain_accept {PQ PQC : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (st : Fig8St Pt) (epQ : ℕ)
    (g : GhostChain) (v : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hst_id : st.id = Q) (htcur : st.tcur = epQ)
    (hg_ep_le : g.epoch ≤ epQ) (hrecv : Q.sendsIn g.epoch = false)
    (hvR : st.vR g.epoch = some v) (hsync : ChainSync g v)
    (ctr : BitVec 32) (hrej : g.rejects (ctr.toNat + 1) = false)
    (T? : Option Pt) (pay : LibsignalCiphertextWithSalt32)
    {st' : Fig8St Pt} {t' i' : ℕ} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (hrec : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st
      ((g.epoch, T?), (ctr.toNat + 1, pay)) = some (st', t', i', pm)) :
    t' = g.epoch ∧ i' = ctr.toNat + 1 ∧
      ∃ v', st' = { st with vR := Function.update st.vR g.epoch (some v') } ∧
        ChainSync (g.accept (ctr.toNat + 1)) v' := by
  let r_dummy : RatchetState :=
    { rootKey := 0, senderChain := none, receiverChains := [⟨dummyKey, none, []⟩],
      previousCounter := 0, maxForwardJumps := 25000 }
  rcases exec_consumeMessageKey_accepts P.C.F r_dummy 0 dummyKey ctr .whisper rfl rfl hsync
      hrej with ⟨key, v', _, hsync', hfs⟩
  unfold lFig8 SM.Construction.scheme SM.Construction.receive lFS at hrec
  dsimp only at hrec
  have hcond1 : (st.id.sendsIn g.epoch || decide (st.tcur + 1 < g.epoch)) = false := by
    rw [hst_id, hrecv, htcur]
    simp only [Bool.false_or, decide_eq_false_iff_not]; omega
  have hcond2 : g.epoch ≠ st.tcur + 1 := by omega
  simp only [hcond1, hcond2, Bool.false_eq_true, ↓reduceIte, hvR] at hrec
  rw [hfs ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)) (g.epoch, T?) pay] at hrec
  cases hdec : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
      key (ctr.toNat + 1, (g.epoch, T?)) pay with
  | none => simp [hdec] at hrec
  | some pm₀ =>
    simp only [hdec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
    rcases hrec with ⟨hst', ht', hi', _⟩
    exact ⟨ht'.symm, hi'.symm, v', hst'.symm, hsync'⟩

omit [DecidableEq Pt] [SampleableType Pt] in
theorem lFig8_receive_newChain_accept {PQ PQC : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (st : Fig8St Pt) (epQ : ℕ) (x_prev : BitVec 256) (srk : PublicKey)
    (hst_id : st.id = Q) (htcur : st.tcur = epQ)
    (hrecv : Q.sendsIn (epQ + 1) = false) (hγ : st.γ = .exp x_prev)
    (ctr : BitVec 32)
    (hrej : (GhostChain.mk (some srk) (epQ + 1) 0 []).rejects (ctr.toNat + 1) = false)
    (T : Pt) (pay : LibsignalCiphertextWithSalt32)
    {st' : Fig8St Pt} {t' i' : ℕ} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (hrec : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st
      ((epQ + 1, some T), (ctr.toNat + 1, pay)) = some (st', t', i', pm)) :
    let p₁ := (rootPRNG P.C.F encPt).up st.root (Dh.dh x_prev T)
    let g_init : GhostChain := ⟨some srk, epQ + 1, 0, []⟩
    t' = epQ + 1 ∧ i' = ctr.toNat + 1 ∧
      ∃ v', st' = { st with root := p₁.1, vR := Function.update st.vR (epQ + 1) (some v'),
                            γ := .pub T, tcur := epQ + 1 } ∧
        ChainSync (g_init.accept (ctr.toNat + 1)) v' := by
  intro p₁ g_init
  let r_dummy : RatchetState :=
    { rootKey := 0, senderChain := none, receiverChains := [⟨dummyKey, none, []⟩],
      previousCounter := 0, maxForwardJumps := 25000 }
  let v_init : RatchetReceiverState (BitVec 256) (BitVec 256) := ⟨p₁.2, 0, []⟩
  have hsync_init : ChainSync g_init v_init := ChainSync.init (some srk) (epQ + 1) p₁.2
  rcases exec_consumeMessageKey_accepts P.C.F r_dummy 0 dummyKey ctr .whisper rfl rfl hsync_init
      hrej with ⟨key, v', _, hsync', hfs⟩
  unfold lFig8 SM.Construction.scheme SM.Construction.receive lFS dhScheme at hrec
  dsimp only at hrec
  have hcond1 : (st.id.sendsIn (epQ + 1) || decide (st.tcur + 1 < epQ + 1)) = false := by
    rw [hst_id, hrecv, htcur]; simp
  rw [hcond1, htcur] at hrec
  have hv_init_eq :
      (FSAEAD.fromAEADPRG ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec))
        (lChainPRG P.C.F) 25000).initReceiver
        ((rootPRNG P.C.F encPt).up st.root (Dh.dh x_prev T)).2 = v_init := rfl
  simp only [Bool.false_eq_true, ↓reduceIte, hγ, hv_init_eq,
    Function.update_self] at hrec
  rw [hfs ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)) (epQ + 1, some T) pay] at hrec
  cases hdec : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
      key (ctr.toNat + 1, (epQ + 1, some T)) pay with
  | none => simp [hdec] at hrec
  | some pm₀ =>
    simp only [hdec, Option.map_some, Option.some.injEq, Prod.mk.injEq,
      Function.update_idem] at hrec
    rcases hrec with ⟨hst', ht', hi', _⟩
    exact ⟨ht'.symm, hi'.symm, v', hst'.symm, hsync'⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem lFS_receive_idx_eq (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {v : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)}
    {a : Header Pt} {e : ℕ × LibsignalCiphertextWithSalt32}
    {x : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) × ℕ × (LibsignalMsgPublicPart × Plain ℓ)}
    (hrecv : (lFS C codec ℓ encT idOf 25000).receive v a e = some x) :
    x.2.1 = e.1 := by
  rcases e with ⟨i, ct⟩
  unfold lFS FSAEAD.fromAEADPRG at hrecv
  dsimp only at hrecv
  rcases hlk : v.skippedKeys.lookup i with _ | key
  · rw [hlk] at hrecv
    dsimp only at hrecv
    split_ifs at hrecv with hcond
    rw [Option.map_eq_some_iff] at hrecv
    rcases hrecv with ⟨_, _, rfl⟩
    rfl
  · rw [hlk, Option.map_eq_some_iff] at hrecv
    rcases hrecv with ⟨_, _, rfl⟩
    rfl

theorem evalCK_some_some_epoch_idx_eq
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt)
    {t i : ℕ} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = some (some (t, i, pm))) :
    t = c'.1.1 ∧ i = c'.2.1 := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  unfold predictReceiveWithSnapshots predictReceive at heval
  cases hk : Kept.eval (fig := fig) (fs := fs) c' (sC.kept Q) with
  | some r_k =>
    rw [hk] at heval
    cases heval
    unfold Kept.eval at hk
    cases hfull : (sC.kept Q).full with
    | some st =>
      rw [hfull] at hk
      simp only [Option.some.injEq, Option.map_eq_some_iff] at hk
      rcases hk with ⟨⟨st', t₁, i₁, pm₁⟩, hrcv, hpair⟩
      rcases Prod.mk.inj hpair with ⟨rfl, hpair2⟩
      rcases Prod.mk.inj hpair2 with ⟨rfl, _⟩
      exact lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam st c' hrcv
    | none =>
      rw [hfull] at hk
      simp only [Option.map_eq_some_iff] at hk
      rcases hk with ⟨v, _, x, hfs, hpair⟩
      rcases Prod.mk.inj hpair with ⟨rfl, hpair2⟩
      rcases Prod.mk.inj hpair2 with ⟨rfl, _⟩
      exact ⟨rfl, lFS_receive_idx_eq P.C P.codec ℓ encT idOf hfs⟩
  | none =>
    rw [hk] at heval
    cases hs : sentEval (fs := fs) sC.sent c c' with
    | some r_s =>
      rw [hs] at heval
      cases heval
      unfold sentEval at hs
      simp only [Option.map_eq_some_iff] at hs
      rcases hs with ⟨e, _, x, hfs, hpair⟩
      rcases Prod.mk.inj hpair with ⟨rfl, hpair2⟩
      rcases Prod.mk.inj hpair2 with ⟨rfl, _⟩
      exact ⟨rfl, lFS_receive_idx_eq P.C P.codec ℓ encT idOf hfs⟩
    | none =>
      rw [hs] at heval
      simp only [Option.orElse_none, Option.map_eq_some_iff] at heval
      rcases heval with ⟨seed, _, hdec⟩
      unfold kDecryptFig8 at hdec
      split at hdec
      · simp only [Option.some.injEq] at hdec
        rcases Prod.mk.inj hdec with ⟨rfl, hpair2⟩
        rcases Prod.mk.inj hpair2 with ⟨rfl, _⟩
        exact ⟨rfl, rfl⟩
      · cases hdec

omit [DecidableEq Pt] [SampleableType Pt] in
theorem simInvCLazy_inject_amb_reject
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ) (hr : 0 < r)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    {w0 : Bool} (hw0 : w0 = false) :
    let winBefore' := fun j =>
      if j = s.amb then w0
      else winBefore j
    SimInvCLazy P Inv ℓ Dh encPt encT qep q (r - 1) x₀
      s_R { s with amb := s.amb + 1 } s_fig8 ec winBefore' epExp := by
  intro winBefore'
  have hamb := hinv.hamb
  refine
    { hmeta := ⟨hinv.hmeta.hb, hinv.hmeta.hwin_R, hinv.hmeta.hwin_mir, hinv.hmeta.hwin_fig8,
        hinv.hmeta.hstop, hinv.hmeta.hepoch_R, hinv.hmeta.hepoch_fig8, hinv.hmeta.hidx_R,
        hinv.hmeta.hidx_fig8, hinv.hmeta.htL_R, hinv.hmeta.htL_fig8, hinv.hmeta.hchall_R,
        hinv.hmeta.hchall_fig8, hinv.hmeta.hcomp_R, hinv.hmeta.hcomp_fig8, hinv.hmeta.hcorrs_R,
        hinv.hmeta.hcorrs_fig8, hinv.hmeta.hmaxAcc_R, hinv.hmeta.hmaxAcc_fig8,
        hinv.hmeta.htrans_R, hinv.hmeta.htrans_fig8⟩
      hcomp := hinv.hcomp
      hec := hinv.hec
      hwinBefore := ?_
      hamb := by dsimp only; omega
      hamb_strict := fun hpos => by
        have hlt := hinv.hamb_strict hpos
        dsimp only; omega
      hidx_le := fun R => by
        have hle := hinv.hidx_le R
        dsimp only; omega
      hhon_len := by
        have hle := hinv.hhon_len
        dsimp only; omega
      hep_le := hinv.hep_le
      hep_adj := hinv.hep_adj
      hst_R := hinv.hst_R
      hst_id := hinv.hst_id
      htcur := hinv.htcur
      hepExp0 := hinv.hepExp0
      hspur := hinv.hspur
      hchainsA := hinv.hchainsA
      hchainsA_ep := hinv.hchainsA_ep
      hchainsB_ep := hinv.hchainsB_ep
      hchainsB_none := hinv.hchainsB_none
      hcorrB0 := hinv.hcorrB0
      hchains_sync := hinv.hchains_sync
      hhon := hinv.hhon
      htrans_hon := hinv.htrans_hon
      hcoll := hinv.hcoll
      hpqInv := hinv.hpqInv }
  intro j hj
  dsimp only [winBefore'] at hj ⊢
  by_cases h0 : j = s.amb
  · simp [h0, hw0]
  · simp only [h0, ↓reduceIte]
    exact hinv.hwinBefore j (by omega)

omit [DecidableEq Pt] [SampleableType Pt] in
theorem simInvCXLazy_inject_amb_reject
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (hr : 0 < r)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    {w0 : Bool} (hw0 : w0 = false) :
    let winBefore' := fun j =>
      if j = sC.base.amb then w0
      else winBefore j
    SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R
      { sC with base := { sC.base with amb := sC.base.amb + 1 } } s_fig8 ec winBefore' epExp := by
  intro winBefore'
  have hsimr := simInvCLazy_inject_amb_reject P (InvB Inv q r) ℓ Dh encPt encT qep q r hr x₀
    s_R sC.base s_fig8 ec winBefore epExp hinv.hsim hw0
  exact
    { hsim := { hsimr with hpqInv := fun R => InvB.mono (Nat.sub_le r 1) (hsimr.hpqInv R) }
      huniq := hinv.huniq
      hkept := ⟨hinv.hkept.hfull, hinv.hkept.hrs, hinv.hkept.hvR⟩
      hidx := hinv.hidx
      hsync := hinv.hsync }

theorem simInvCLazy_inject_known_accept
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (ci : ℕ) (g : GhostChain) (i : ℕ) (pq' : PQ)
    (hg_elem : (s.chains Q)[ci]? = some g)
    (v' : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hsync' : ChainSync (g.accept i) v')
    (pos : SM.Pos) (hpos_ep : pos.epoch = g.epoch)
    (hpq' : Inv pq') :
    let st' : Fig8St Pt :=
      { (s_fig8.st Q) with vR := Function.update (s_fig8.st Q).vR g.epoch (some v') }
    let mir' := s.mir.accept Q () pos
    let s' : SimState PQ Pt ℓ :=
      { s with
        mir := mir',
        pq := Function.update s.pq Q pq',
        unackA := s.unackA && Q != Party.A,
        chains := Function.update s.chains Q ((s.chains Q).modify ci (·.accept i)) }
    let s_fig8' := s_fig8.accept Q st' pos
    let s_R' :=
      s_R.accept Q (expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q)) pos
    SimInvCLazy P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec winBefore epExp := by
  intro st' mir' s' s_fig8' s_R'
  have hg_mem : g ∈ s.chains Q := List.mem_of_getElem? hg_elem
  rcases hinv.hchains_sync Q g hg_mem with ⟨hg_ep_le, hrecv, hg_key_sync, _⟩
  have hpos_le : pos.epoch ≤ s.mir.epoch Q := by rw [hpos_ep]; exact hg_ep_le
  have hmir_ep : mir'.epoch = s.mir.epoch := WP2A.I3.accept_epoch_eq_of_le s.mir Q () pos hpos_le
  have hmir_idx : mir'.idx = s.mir.idx := rfl
  have hinWin_eq : ∀ R, inReceiveOnlyEpoch mir' R = inReceiveOnlyEpoch s.mir R := by
    intro R; unfold inReceiveOnlyEpoch; rw [hmir_ep]
  have hmod_set : (s.chains Q).modify ci (·.accept i) = (s.chains Q).set ci (g.accept i) :=
    modify_eq_set_of_getElem? (s.chains Q) ci g (·.accept i) hg_elem
  have hchains_ep : ∀ R, (s'.chains R).map (·.epoch) = (s.chains R).map (·.epoch) := by
    intro R
    dsimp only [s']
    by_cases hR : R = Q
    · subst hR
      rw [Function.update_self, hmod_set]
      exact map_epoch_set_accept (s.chains R) ci g i hg_elem
    · rw [Function.update_of_ne hR]
  have hnodup : ((s.chains Q).map (·.epoch)).Nodup := by
    cases Q with
    | A => rw [hinv.hchainsA_ep]; exact epListA_nodup (s.mir.epoch .A / 2)
    | B => rw [hinv.hchainsB_ep]; exact epListB_nodup ((s.mir.epoch .B + 1) / 2)
  have hs'_eq : s' =
      { mir := s.mir.accept Q () pos,
        pq := Function.update s.pq Q pq', pn := s.pn, unackA := s.unackA && Q != Party.A,
        honest := s.honest,
        chains := Function.update s.chains Q ((s.chains Q).modify ci (·.accept i)),
        amb := s.amb, stopped := false } := by
    have hst : s.stopped = false := hinv.hmeta.hstop
    dsimp only [s', mir']
    rw [hst]
  refine
    { hmeta := by
        rw [hs'_eq]
        exact hinv.hmeta.accept_preserves Q _ st' pos _ _ _ _ _ _
      hcomp := comp_healedBy_false_accept s.mir 3 Q () pos hinv.hcomp
      hec := by
        intro R hR
        rw [hinWin_eq R] at hR
        exact hinv.hec R hR
      hwinBefore := hinv.hwinBefore
      hamb := by dsimp only [s']; have := hinv.hamb; omega
      hamb_strict := by
        intro hpos
        dsimp only [s'] at hpos ⊢
        rw [hmir_ep] at hpos
        have := hinv.hamb_strict hpos; omega
      hidx_le := by
        intro R; dsimp only [s', mir', SM.GameState.accept, SM.GameState.delete]
        have := hinv.hidx_le R; omega
      hhon_len := by dsimp only [s']; have := hinv.hhon_len; omega
      hep_le := by intro R; dsimp only [s']; rw [hmir_ep]; exact hinv.hep_le R
      hep_adj := by
        intro R; dsimp only [s']; rw [hinWin_eq R, hmir_ep]; exact hinv.hep_adj R
      hst_R := by
        intro R
        dsimp only [s_R', s_fig8', SM.GameState.accept, SM.GameState.delete]
        by_cases hR : R = Q
        · subst hR
          simp [Function.update_self]
        · simp only [Function.update_of_ne hR]
          rw [hinv.hst_R R]
          unfold expectedGhost
          have hresolve_R : (resolveSim (encT (Dh.dh x₀ Dh.base)) s').chains R =
              (resolveSim (encT (Dh.dh x₀ Dh.base)) s).chains R := by
            unfold resolveSim resolveSpkChains
            cases R <;> cases Q <;> try contradiction
            · simp [s']
            · simp [s']
          have hunack_R : (R == Party.A && s'.unackA) = (R == Party.A && s.unackA) := by
            cases R <;> cases Q <;> try contradiction
            · simp [s']
            · simp [s']
          have hmir_ep_R : mir'.epoch R = s.mir.epoch R := congrFun hmir_ep R
          have htoGhost_R : toGhost P (resolveSim (encT (Dh.dh x₀ Dh.base)) s') R (s_fig8.st R) =
              toGhost P (resolveSim (encT (Dh.dh x₀ Dh.base)) s) R (s_fig8.st R) := by
            unfold toGhost
            simp only [resolveSim_mir, resolveSim_pn, resolveSim_unackA, resolveSim_pq,
               hunack_R, hresolve_R]
            dsimp only [s']
            simp [hmir_ep_R, Function.update_of_ne hR]
          dsimp only [s']
          rw [hinWin_eq R, hmir_idx, htoGhost_R]
      hst_id := by
        intro R
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
        by_cases hR : R = Q
        · subst hR; simp [Function.update_self, st', hinv.hst_id R]
        · simp [Function.update_of_ne hR, hinv.hst_id R]
      htcur := by
        intro R
        dsimp only [s_fig8', s', SM.GameState.accept, SM.GameState.delete]
        rw [hmir_ep]
        by_cases hR : R = Q
        · subst hR; simp [Function.update_self, st', hinv.htcur R]
        · simp [Function.update_of_ne hR, hinv.htcur R]
      hepExp0 := hinv.hepExp0
      hspur := by
        intro R
        rcases hinv.hspur R with ⟨rk_base, T_base, h1, h2⟩
        refine ⟨rk_base, T_base, ?_, ?_⟩
        · intro hinw
          rw [hinWin_eq R] at hinw
          dsimp only [s_fig8', s', SM.GameState.accept, SM.GameState.delete]
          rw [hmir_ep]
          by_cases hR : R = Q
          · subst hR; simpa [Function.update_self, st'] using h1 hinw
          · simpa [Function.update_of_ne hR] using h1 hinw
        · intro hnot_inw
          rw [hinWin_eq R] at hnot_inw
          dsimp only [s_fig8', s', SM.GameState.accept, SM.GameState.delete]
          rw [hmir_ep, hmir_idx]
          by_cases hR : R = Q
          · subst hR; simpa [Function.update_self, st'] using h2 hnot_inw
          · simpa [Function.update_of_ne hR] using h2 hnot_inw
      hchainsA := by
        dsimp only [s']
        rw [hmir_ep]
        cases Q with
        | A =>
          rw [Function.update_self, hmod_set]
          exact chainsEpochInvA_set_accept hinv.hchainsA ci g i hg_elem
        | B =>
          rw [Function.update_of_ne (by decide : Party.A ≠ Party.B)]
          exact hinv.hchainsA
      hchainsA_ep := by
        rw [hchains_ep .A]
        dsimp only [s']
        rw [hmir_ep]
        exact hinv.hchainsA_ep
      hchainsB_ep := by
        rw [hchains_ep .B]
        dsimp only [s']
        rw [hmir_ep]
        exact hinv.hchainsB_ep
      hchainsB_none := by
        intro g₀ hg₀
        dsimp only [s'] at hg₀
        cases Q with
        | A =>
          rw [Function.update_of_ne (by decide : Party.B ≠ Party.A)] at hg₀
          exact hinv.hchainsB_none g₀ hg₀
        | B =>
          rw [Function.update_self, hmod_set] at hg₀
          rcases List.mem_or_eq_of_mem_set hg₀ with hg₀ | rfl
          · exact hinv.hchainsB_none g₀ hg₀
          · rw [accept_key]
            exact hinv.hchainsB_none g hg_mem
      hcorrB0 := by dsimp only [s', mir']; exact hcorrB0_accept_modify hinv.hcorrB0
      hchains_sync := by
        intro R g₀ hg₀
        dsimp only [s', s_fig8', SM.GameState.accept, SM.GameState.delete] at hg₀ ⊢
        rw [hmir_ep]
        by_cases hR : R = Q
        · subst hR
          rw [Function.update_self, hmod_set] at hg₀
          simp only [Function.update_self, st']
          rcases List.mem_iff_getElem?.mp hg₀ with ⟨j, hj⟩
          have hj_lt : j < (s.chains R).length := by
            have := (List.getElem?_eq_some_iff.mp hj).1
            simpa using this
          by_cases hj_ci : j = ci
          · subst hj_ci
            rw [List.getElem?_set_self hj_lt, Option.some.injEq] at hj
            subst hj
            have hacc_ep : (g.accept i).epoch = g.epoch := accept_epoch g i
            have hacc_key : (g.accept i).key = g.key := accept_key g i
            rw [hacc_ep, hacc_key]
            refine ⟨hg_ep_le, hrecv, hg_key_sync, v', ?_, hsync'⟩
            simp [Function.update_self]
          · rw [List.getElem?_set_ne (Ne.symm hj_ci)] at hj
            have hg₀_mem : g₀ ∈ s.chains R := List.mem_of_getElem? hj
            rcases hinv.hchains_sync R g₀ hg₀_mem with ⟨h1, h2, h3, v₀, hv₀, hsync₀⟩
            have hne_ep : g₀.epoch ≠ g.epoch :=
              nodup_distinct_epoch hnodup hg_elem j hj_lt hj_ci g₀ hj
            refine ⟨h1, h2, h3, v₀, ?_, hsync₀⟩
            rw [Function.update_of_ne hne_ep, hv₀]
        · rw [Function.update_of_ne hR] at hg₀
          simp only [Function.update_of_ne hR]
          exact hinv.hchains_sync R g₀ hg₀
      hhon := by
        intro wc hwc
        dsimp only [s'] at hwc ⊢
        rw [hmir_ep]
        exact hinv.hhon wc hwc
      htrans_hon := by
        intro rec_f hrec_f
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete] at hrec_f
        exact hinv.htrans_hon rec_f (List.mem_of_mem_filter hrec_f)
      hcoll := by
        intro t₁ t₂ ht₁ ht₂ hdh
        dsimp only [s'] at ht₁ ht₂
        rw [hmir_ep] at ht₁ ht₂
        exact hinv.hcoll t₁ t₂ ht₁ ht₂ hdh
      hpqInv := by
        intro R
        dsimp only [s']
        by_cases hR : R = Q
        · subst hR; simp [Function.update_self, hpq']
        · simp [Function.update_of_ne hR, hinv.hpqInv R] }

theorem simInvCXLazy_inject_known_accept
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (Q : Party) (ci : ℕ) (g : GhostChain) (i : ℕ) (pq' : PQ)
    (hg_elem : (sC.base.chains Q)[ci]? = some g)
    (v' : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hsync' : ChainSync (g.accept i) v')
    (pos : SM.Pos) (hpos_ep : pos.epoch = g.epoch)
    (hpq' : InvB Inv q r pq')
    (s' : SimState PQ Pt ℓ)
    (hs' : s' = { sC.base with
        mir := sC.base.mir.accept Q () pos,
        pq := Function.update sC.base.pq Q pq',
        unackA := sC.base.unackA && Q != Party.A,
        chains := Function.update sC.base.chains Q ((sC.base.chains Q).modify ci (·.accept i)) })
    (s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hs_fig8' : s_fig8' = s_fig8.accept Q
        { (s_fig8.st Q) with vR := Function.update (s_fig8.st Q).vR g.epoch (some v') } pos)
    (s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (hs_R' : s_R' = s_R.accept Q (expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q
        { (s_fig8.st Q) with vR := Function.update (s_fig8.st Q).vR g.epoch (some v') } (ec Q)) pos)
    (kept' : Party → Kept Pt)
    (hkept' : KeptInv P Dh encPt encT idOf lam { sC with base := s', kept := kept' } s_fig8')
    (hsync8' : EpochSync P Dh encPt encT idOf s'.honest sC.sent sC.snaps s_fig8' epExp) :
    SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R'
      { sC with base := s', kept := kept' } s_fig8' ec winBefore epExp := by
  subst hs' hs_fig8' hs_R'
  have hsimr := simInvCLazy_inject_known_accept P (InvB Inv q r) ℓ Dh encPt encT qep q r x₀ s_R
    sC.base s_fig8 ec winBefore epExp hinv.hsim Q ci g i pq' hg_elem v' hsync' pos hpos_ep hpq'
  dsimp only at hsimr
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  have hpos_le : pos.epoch ≤ sC.base.mir.epoch Q := by
    rw [hpos_ep]; exact (hinv.hsim.hchains_sync Q g hg_mem).1
  have hmir_ep : (sC.base.mir.accept Q () pos).epoch = sC.base.mir.epoch :=
    WP2A.I3.accept_epoch_eq_of_le sC.base.mir Q () pos hpos_le
  refine
    { hsim := { hsimr with hpqInv := fun R => InvB.mono (Nat.sub_le r 1) (hsimr.hpqInv R) }
      huniq := hinv.huniq
      hkept := hkept'
      hidx := ?_
      hsync := hsync8' }
  intro wc hwc hep
  dsimp only at hwc hep ⊢
  rw [hmir_ep] at hep
  exact hinv.hidx wc hwc hep

theorem epochSync_recv_new_lazy
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt)
    (hmem : (w, c) ∈ sC.base.honest) (hsnd : Party.senderOf c.1.1 = Q.other)
    (hhdr : c'.1 = c.1)
    (hnew : c.1.1 = (s_fig8.st Q).tcur + 1)
    (st' : Fig8St Pt) (res : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' =
      some (st', res))
    (honest' : List (List (BitVec 8) × Fig8C Pt))
    (s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hst : s_fig8'.st = Function.update s_fig8.st Q st')
    (hwin : s_fig8'.win = false → s_fig8.win = false)
    (hhon : ∀ wc ∈ honest', wc ∈ sC.base.honest) :
    EpochSync P Dh encPt encT idOf honest' sC.sent sC.snaps s_fig8' epExp := by
  intro hw'
  obtain ⟨K, rk, hK⟩ := hinv.hsync (hwin hw')
  have hle_other : c.1.1 ≤ (s_fig8.st Q.other).tcur := by
    have h1 := (hinv.hsim.hhon (w, c) hmem).2.2.2
    rw [hsnd, ← hinv.hsim.htcur Q.other] at h1
    exact h1
  have hgap_other : (s_fig8.st Q.other).tcur ≤ (s_fig8.st Q).tcur + 1 := by
    simpa [Party.other_other] using hK.hgap Q.other
  have ht_other : (s_fig8.st Q.other).tcur = (s_fig8.st Q.other.other).tcur + 1 := by
    rw [Party.other_other]; omega
  have ht_eq : (s_fig8.st Q.other).tcur = c.1.1 := by omega
  obtain ⟨_, x, hγ_other, hT_other, hup⟩ := hK.hahead Q.other ht_other
  rw [Party.other_other, ht_eq] at hup
  have hT_c : c.1.2 = some (Dh.dh x Dh.base) := by
    have h1 := hK.hhdr (w, c) hmem (by rw [hsnd, ht_eq])
    rw [hsnd, hT_other] at h1
    exact h1.symm
  have hc'_11 : c'.1.1 = c.1.1 := congrArg Prod.fst hhdr
  have hc'_12 : c'.1.2 = some (Dh.dh x Dh.base) := (congrArg Prod.snd hhdr).trans hT_c
  dsimp only [lFig8, SM.Construction.scheme, SM.Construction.receive] at hfig
  rw [hc'_11, hc'_12] at hfig
  split_ifs at hfig with hcond
  have hsends_Q : Q.sendsIn c.1.1 = false := by
    rw [hinv.hsim.hst_id Q] at hcond
    cases hq : Q.sendsIn c.1.1
    · rfl
    · simp [hq] at hcond
  simp only [hnew, Function.update_self] at hfig
  rw [← hnew] at hfig
  cases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive
      ((lFS P.C P.codec ℓ encT idOf 25000).initReceiver
        ((rootPRNG P.C.F encPt).up (s_fig8.st Q).root
          ((dhScheme Dh).receive (s_fig8.st Q).γ (Dh.dh x Dh.base)).2).2)
      c'.1 c'.2 with
  | none => simp [hfs] at hfig
  | some vim =>
    rcases vim with ⟨v', i, m⟩
    simp only [hfs, Option.some.injEq, Prod.mk.injEq] at hfig
    rcases hfig with ⟨hst', _⟩
    rw [hup] at hfs hst'
    have hrecv_v' : RecvAgrees P.C.F (K c.1.1) v' :=
      recvAgrees_receive P encT idOf (K c.1.1) ⟨K c.1.1, 0, []⟩ v' c'.1 c'.2 (i, m)
        ⟨rfl, fun _ h => by cases h⟩ hfs
    have hst_Q : s_fig8'.st Q = st' := by rw [hst, Function.update_self]
    have hst_other : s_fig8'.st Q.other = s_fig8.st Q.other := by
      rw [hst, Function.update_of_ne (Party.other_ne Q)]
    have hparty_dichotomy : ∀ P₀ R₀ : Party, P₀ = R₀ ∨ P₀.other = R₀ := by
      intro P₀ R₀; cases P₀ <;> cases R₀ <;> simp
    have htcur_all : ∀ R, (s_fig8'.st R).tcur = c.1.1 := by
      intro R
      rcases hparty_dichotomy Q R with rfl | rfl
      · rw [hst_Q, ← hst']
      · rw [hst_other, ht_eq]
    have hmax_old : max (s_fig8.st .A).tcur (s_fig8.st .B).tcur = c.1.1 := by
      cases Q with
      | A => have hB : (s_fig8.st .B).tcur = c.1.1 := ht_eq; omega
      | B => have hA : (s_fig8.st .A).tcur = c.1.1 := ht_eq; omega
    have hmax_new : max (s_fig8'.st .A).tcur (s_fig8'.st .B).tcur = c.1.1 := by
      simp [htcur_all]
    refine ⟨K, rk, ?_⟩
    refine
      { hhon := fun wc hwc => hK.hhon wc (hhon wc hwc)
        hhdr := ?_
        hsent := hK.hsent
        hrecv := ?_
        hsend := ?_
        hahead := ?_
        hequal := ?_
        hgap := ?_
        hvS := ?_
        hsent_ep := ?_
        hroot := ?_
        hγ_exp := ?_
        hStep := ?_
        hsnaps := ?_ }
    · intro wc hwc ht_wc
      by_cases hS : Party.senderOf wc.2.1.1 = Q
      · rw [hS, htcur_all Q] at ht_wc
        rw [← ht_wc, hsnd] at hS
        exact absurd hS (Party.other_ne Q)
      · have hne : s_fig8'.st (Party.senderOf wc.2.1.1) = s_fig8.st (Party.senderOf wc.2.1.1) := by
          rw [hst, Function.update_of_ne hS]
        rw [hne] at ht_wc ⊢
        exact hK.hhdr wc (hhon wc hwc) ht_wc
    · intro R t₀ v₀ hvR
      rcases hparty_dichotomy Q R with rfl | rfl
      · rw [hst_Q, ← hst'] at hvR
        dsimp only at hvR
        rw [Function.update_idem] at hvR
        by_cases ht₀ : t₀ = c.1.1
        · subst ht₀
          rw [Function.update_self, Option.some.injEq] at hvR
          subst hvR
          exact hrecv_v'
        · rw [Function.update_of_ne ht₀] at hvR
          exact hK.hrecv Q t₀ v₀ hvR
      · rw [hst_other] at hvR
        exact hK.hrecv Q.other t₀ v₀ hvR
    · intro R v₀ hvS hsends
      rcases hparty_dichotomy Q R with rfl | rfl
      · rw [htcur_all Q, hsends_Q] at hsends
        cases hsends
      · rw [hst_other] at hvS hsends ⊢
        exact hK.hsend Q.other v₀ hvS hsends
    · intro R h_ah
      rw [htcur_all R, htcur_all R.other] at h_ah
      omega
    · intro R _ hsends
      rcases hparty_dichotomy Q R with rfl | rfl
      · rw [htcur_all Q, hsends_Q] at hsends
        cases hsends
      · rw [Party.other_other, hst_other, hst_Q, ← hst']
        dsimp only
        have hdh_fst : ((dhScheme Dh).receive (s_fig8.st Q).γ (Dh.dh x Dh.base)).1 =
            .pub (Dh.dh x Dh.base) := by
          cases (s_fig8.st Q).γ <;> rfl
        rw [hdh_fst]
        exact ⟨rfl, x, hγ_other, rfl⟩
    · intro R
      rw [htcur_all R, htcur_all R.other]
      omega
    · intro R hsends
      rcases hparty_dichotomy Q R with rfl | rfl
      · rw [htcur_all Q, hsends_Q] at hsends
        cases hsends
      · rw [hst_other] at hsends ⊢
        exact hK.hvS Q.other hsends
    · intro e he
      have h1 := hK.hsent_ep e he
      rcases hparty_dichotomy Q (Party.senderOf e.1.1.1) with hS | hS
      · rw [← hS, htcur_all Q]
        rw [← hS] at h1
        omega
      · rw [← hS, hst_other]
        rw [← hS] at h1
        exact h1
    · intro R
      rcases hparty_dichotomy Q R with rfl | rfl
      · rw [hst_Q, ← hst']
        dsimp only
        rw [← ht_eq]
        exact hK.hroot Q.other
      · rw [hst_other]
        exact hK.hroot Q.other
    · intro R hsends
      rcases hparty_dichotomy Q R with rfl | rfl
      · rw [htcur_all Q, hsends_Q] at hsends
        cases hsends
      · rw [hst_other] at hsends ⊢
        exact hK.hγ_exp Q.other hsends
    · intro t₀ ht1
      rw [hmax_new] at ht1
      exact hK.hStep t₀ (by rw [hmax_old]; exact ht1)
    · intro snap hsnap
      rw [hmax_new]
      exact SnapSync.congr (hK.hsnaps snap hsnap) (by rw [hmax_old])
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem simInvCLazy_deliver_newChain_accept
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (hinw_Q : inReceiveOnlyEpoch s.mir Q = false)
    (hQ_recv : Q.sendsIn (s.mir.epoch Q + 1) = false)
    (hinw_other : inReceiveOnlyEpoch s.mir Q.other = false)
    (hep_other : s.mir.epoch Q.other = s.mir.epoch Q + 1)
    (i : ℕ) (pq' : PQ)
    (pos : SM.Pos) (hpos_ep : pos.epoch = s.mir.epoch Q + 1)
    (v' : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hsync' : ChainSync
      ((GhostChain.mk (some (encT (Dh.dh (epExp (s.mir.epoch Q + 1)) Dh.base)))
        (s.mir.epoch Q + 1) 0 []).accept i) v')
    (hT_ne0 : Dh.dh (epExp (s.mir.epoch Q + 1)) Dh.base ≠ 0)
    (hpq' : Inv pq') :
    let rc := epExp (s.mir.epoch Q + 2)
    let spkKey := encT (Dh.dh x₀ Dh.base)
    let t := s.mir.epoch Q + 1
    let T := Dh.dh (epExp t) Dh.base
    let srk := encT T
    let p₁ := (rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (epExp (s.mir.epoch Q)) T)
    let p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
    let g_init : GhostChain := ⟨some srk, t, 0, []⟩
    let st' : Fig8St Pt :=
      { (s_fig8.st Q) with
        root := p₁.1,
        vR := Function.update (s_fig8.st Q).vR t (some v'),
        γ := .pub T,
        tcur := t }
    let pn_new := BitVec.ofNat 32 (s.mir.idx Q - 1)
    let s' : SimState PQ Pt ℓ :=
      { s with
        mir := s.mir.accept Q () pos,
        pq := Function.update s.pq Q pq',
        unackA := s.unackA && Q != Party.A,
        chains := Function.update s.chains Q (pushChain (s.chains Q) (g_init.accept i)) }
    let s_fig8' := s_fig8.accept Q st' pos
    let s_R' :=
      s_R.accept Q
        (withEager (toGhost P (resolveSim spkKey s') Q st') p₂.1
          (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new)
        pos
    let ec' := Function.update ec Q rc
    SimInvCLazy P Inv ℓ Dh encPt encT qep q r x₀ s_R' s' s_fig8' ec' winBefore epExp := by
  intro rc spkKey t T srk p₁ p₂ g_init st' pn_new s' s_fig8' s_R' ec'
  have hne_other : Q.other ≠ Q := by cases Q <;> decide
  have hep'_Q : s'.mir.epoch Q = s.mir.epoch Q + 1 := by
    dsimp only [s', SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_self, hpos_ep]
  have hep'_other : s'.mir.epoch Q.other = s.mir.epoch Q.other := by
    dsimp only [s', SM.GameState.accept, SM.GameState.delete]
    simp [Function.update_of_ne hne_other]
  have hidx_eq : s'.mir.idx = s.mir.idx := rfl
  have hinw'_Q : inReceiveOnlyEpoch s'.mir Q = true := by
    unfold inReceiveOnlyEpoch; rw [hep'_Q, hQ_recv]; rfl
  have hinw'_other : inReceiveOnlyEpoch s'.mir Q.other = false := by
    unfold inReceiveOnlyEpoch at hinw_other ⊢; rw [hep'_other]; exact hinw_other
  have hmax_eq : max (s'.mir.epoch .A) (s'.mir.epoch .B) =
      max (s.mir.epoch .A) (s.mir.epoch .B) := by
    cases Q <;> {
      dsimp only [Party.other] at hep_other hep'_other
      rw [hep'_Q, hep'_other, hep_other]
      omega }
  have hchainsA_ep' : (s'.chains .A).map (·.epoch) = epListA (s'.mir.epoch .A / 2) := by
    dsimp only [s']
    by_cases hQA : Q = .A
    · subst hQA
      rw [Function.update_self, hep'_Q]
      have hmod : (s.mir.epoch .A + 1) % 2 = 0 := by
        change decide ((s.mir.epoch .A + 1) % 2 = 1) = false at hQ_recv
        rw [decide_eq_false_iff_not] at hQ_recv
        omega
      have hdiv : (s.mir.epoch .A + 1) / 2 = s.mir.epoch .A / 2 + 1 := by omega
      have hgep : (g_init.accept i).epoch = 2 * (s.mir.epoch .A / 2 + 1) := by
        rw [accept_epoch]; dsimp only [g_init, t]; omega
      rw [hdiv]
      exact pushChain_map_epoch_epListA (s.chains .A) (g_init.accept i)
        (s.mir.epoch .A / 2) hinv.hchainsA_ep hgep
    · have hAO : Party.A = Q.other := by cases Q <;> first | contradiction | rfl
      rw [Function.update_of_ne (Ne.symm hQA), hAO, hep'_other, ← hAO]
      exact hinv.hchainsA_ep
  have hchainsB_ep' : (s'.chains .B).map (·.epoch) = epListB ((s'.mir.epoch .B + 1) / 2) := by
    dsimp only [s']
    by_cases hQB : Q = .B
    · subst hQB
      rw [Function.update_self, hep'_Q]
      have hmod : (s.mir.epoch .B + 1) % 2 = 1 := by
        simp only [Party.sendsIn, beq_eq_false_iff_ne] at hQ_recv
        omega
      have hdiv : (s.mir.epoch .B + 1 + 1) / 2 = (s.mir.epoch .B + 1) / 2 + 1 := by omega
      have hgep : (g_init.accept i).epoch = 2 * ((s.mir.epoch .B + 1) / 2) + 1 := by
        rw [accept_epoch]; dsimp only [g_init, t]; omega
      rw [hdiv]
      exact pushChain_map_epoch_epListB (s.chains .B) (g_init.accept i)
        ((s.mir.epoch .B + 1) / 2) hinv.hchainsB_ep hgep
    · have hBO : Party.B = Q.other := by cases Q <;> first | contradiction | rfl
      rw [Function.update_of_ne (Ne.symm hQB), hBO, hep'_other, ← hBO]
      exact hinv.hchainsB_ep
  have hpos_AB : 0 < s.mir.epoch .A ∨ 0 < s.mir.epoch .B := by
    cases Q with
    | A => exact Or.inr (by change 0 < s.mir.epoch Party.A.other; omega)
    | B => exact Or.inl (by change 0 < s.mir.epoch Party.B.other; omega)
  refine
    { hmeta := by
        have hm := hinv.hmeta.accept_preserves Q
          (withEager (toGhost P (resolveSim spkKey s') Q st') p₂.1
            (some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩) pn_new) st' pos
          (Function.update s.pq Q pq') s.pn (s.unackA && Q != Party.A)
          s.honest (Function.update s.chains Q (pushChain (s.chains Q) (g_init.accept i))) s.amb
        dsimp only [s']
        rwa [hinv.hmeta.hstop]
      hcomp := comp_healedBy_false_accept s.mir 3 Q () pos hinv.hcomp
      hec := by
        intro R hR
        by_cases hRQ : R = Q
        · subst hRQ; rw [hinw'_Q] at hR; cases hR
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          dsimp only [ec']
          rw [Function.update_of_ne hRQ]
          exact hinv.hec Q.other hinw_other
      hwinBefore := hinv.hwinBefore
      hamb := hinv.hamb
      hamb_strict := fun _ => hinv.hamb_strict hpos_AB
      hidx_le := fun R => by have := hinv.hidx_le R; rw [hidx_eq]; omega
      hhon_len := by have := hinv.hhon_len; dsimp only [s']; omega
      hep_le := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ; rw [hep'_Q, ← hep_other]; exact hinv.hep_le R.other
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO; rw [hep'_other]; exact hinv.hep_le Q.other
      hep_adj := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ
          rw [hep'_Q, hep'_other, hep_other]
          exact ⟨fun _ => le_rfl, Nat.le_succ _⟩
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          have hQQ : Q.other.other = Q := by cases Q <;> rfl
          rw [hinw'_other, hep'_other, hQQ, hep'_Q, hep_other]
          exact ⟨(fun h => by cases h), Nat.le_succ _⟩
      hst_R := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ
          dsimp only [s_R', s_fig8', SM.GameState.accept, SM.GameState.delete, ec']
          simp only [Function.update_self]
          rw [expectedGhost_of_inWin_true P Dh encPt spkKey s' R st' rc T hinw'_Q rfl]
          rfl
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          dsimp only [s_R', s_fig8', SM.GameState.accept, SM.GameState.delete, ec']
          simp only [Function.update_of_ne hRQ, hinv.hst_R R]
          refine expectedGhost_congr_other P Dh encPt spkKey s s' R (s_fig8.st R) (ec R)
            ?_ rfl ?_ rfl ?_ ?_
          · subst hRO; exact hep'_other.symm
          · dsimp only [s']; rw [Function.update_of_ne hRQ]
          · dsimp only [s']; cases R <;> cases Q <;> simp at hRQ ⊢
          · dsimp only [s']; rw [Function.update_of_ne hRQ]
      hst_id := by
        intro R
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
        by_cases hRQ : R = Q
        · subst hRQ; simp [Function.update_self, st', hinv.hst_id R]
        · simp [Function.update_of_ne hRQ, hinv.hst_id R]
      htcur := by
        intro R
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
        by_cases hRQ : R = Q
        · subst hRQ; simp [Function.update_self, st', t, hep'_Q]
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          simp [Function.update_of_ne hRQ, hep'_other, hinv.htcur Q.other]
      hepExp0 := hinv.hepExp0
      hspur := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ
          refine ⟨p₁.1, T, ?_, ?_⟩
          · intro _
            dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete, ec', rc]
            simp only [Function.update_self, st', hep'_Q, t]
            exact ⟨trivial, trivial, hT_ne0, trivial⟩
          · intro h; rw [hinw'_Q] at h; cases h
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          rcases hinv.hspur Q.other with ⟨rk_base, T_base, _, hnotinw_O⟩
          have hst_O : s_fig8'.st Q.other = s_fig8.st Q.other := by
            dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
            simp [Function.update_of_ne hRQ]
          refine ⟨rk_base, T_base, ?_, ?_⟩
          · intro h; rw [hinw'_other] at h; cases h
          · intro _
            rw [hst_O, hep'_other, hidx_eq]
            exact hnotinw_O hinw_other
      hchainsA := by
        dsimp only [s']
        by_cases hQA : Q = .A
        · subst hQA
          rw [Function.update_self, hep'_Q]
          exact chainsEpochInvA_pushChain hinv.hchainsA hQ_recv (g_init.accept i)
            (accept_epoch g_init i) (by rw [accept_key]; rfl)
        · have hAO : Party.A = Q.other := by cases Q <;> first | contradiction | rfl
          rw [Function.update_of_ne (Ne.symm hQA), hAO, hep'_other, ← hAO]
          exact hinv.hchainsA
      hchainsA_ep := hchainsA_ep'
      hchainsB_ep := hchainsB_ep'
      hchainsB_none := by
        intro g' hg'
        dsimp only [s'] at hg'
        by_cases hQB : Q = .B
        · subst hQB
          rw [Function.update_self, pushChain_eq_drop_append, List.mem_append,
            List.mem_singleton] at hg'
          rcases hg' with hg' | rfl
          · exact hinv.hchainsB_none g' (List.mem_of_mem_drop hg')
          · rw [accept_key]; rfl
        · rw [Function.update_of_ne (Ne.symm hQB)] at hg'
          exact hinv.hchainsB_none g' hg'
      hchains_sync := by
        intro R g' hg'
        by_cases hRQ : R = Q
        · subst hRQ
          dsimp only [s'] at hg'
          rw [Function.update_self, pushChain_eq_drop_append, List.mem_append,
            List.mem_singleton] at hg'
          dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
          simp only [Function.update_self, hep'_Q]
          rcases hg' with hg'_drop | rfl
          · have hg'_mem := List.mem_of_mem_drop hg'_drop
            rcases hinv.hchains_sync R g' hg'_mem with ⟨hep_g', hrecv_g', hkey_g', v₀, hv₀, hsync₀⟩
            have hne_t : g'.epoch ≠ t := by dsimp only [t]; omega
            refine ⟨by omega, hrecv_g', hkey_g', v₀, ?_, hsync₀⟩
            simp [st', Function.update_of_ne hne_t, hv₀]
          · have hep_acc : (g_init.accept i).epoch = s.mir.epoch R + 1 := accept_epoch g_init i
            have hkey_acc : (g_init.accept i).key = some srk := accept_key g_init i
            rw [hep_acc, hkey_acc]
            refine ⟨le_rfl, hQ_recv, rfl, v', ?_, hsync'⟩
            simp [st', t, Function.update_self]
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          dsimp only [s'] at hg'
          rw [Function.update_of_ne hRQ] at hg'
          dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
          simp only [Function.update_of_ne hRQ, hep'_other]
          exact hinv.hchains_sync Q.other g' hg'
      hhon := by
        intro wc hwc
        rcases hinv.hhon wc hwc with ⟨hhon_wc, hle_M, hsends_wc, hle_ep⟩
        dsimp only [s']
        rw [hmax_eq]
        refine ⟨hhon_wc, hle_M, hsends_wc, ?_⟩
        by_cases hSQ : Party.senderOf wc.2.1.1 = Q
        · rw [hSQ, hep'_Q]; rw [hSQ] at hle_ep; omega
        · have hSO : Party.senderOf wc.2.1.1 = Q.other := by
            cases hS : Party.senderOf wc.2.1.1 <;> cases Q <;> simp_all [Party.other]
          rw [hSO, hep'_other]; rw [hSO] at hle_ep; exact hle_ep
      htrans_hon := by
        intro rec_f hrec_f
        dsimp only [s', s_fig8', SM.GameState.accept, SM.GameState.delete] at hrec_f ⊢
        exact hinv.htrans_hon rec_f (List.mem_of_mem_filter hrec_f)
      hcoll := by
        dsimp only [s']
        rw [hmax_eq]
        exact hinv.hcoll
      hcorrB0 := by
        dsimp only [s']
        exact hcorrB0_accept_pushChain (by rw [accept_key]; rfl) hinv.hcorrB0
      hpqInv := by
        intro R
        dsimp only [s']
        by_cases hRQ : R = Q
        · subst hRQ; rw [Function.update_self]; exact hpq'
        · rw [Function.update_of_ne hRQ]; exact hinv.hpqInv R }

theorem simInvCXLazy_deliver_newChain_accept
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (Q : Party) (hinw_Q : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hQ_recv : Q.sendsIn (sC.base.mir.epoch Q + 1) = false)
    (hinw_other : inReceiveOnlyEpoch sC.base.mir Q.other = false)
    (hep_other : sC.base.mir.epoch Q.other = sC.base.mir.epoch Q + 1)
    (i : ℕ) (pq' : PQ)
    (pos : SM.Pos) (hpos_ep : pos.epoch = sC.base.mir.epoch Q + 1)
    (v' : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hsync' : ChainSync
      ((GhostChain.mk (some (encT (Dh.dh (epExp (sC.base.mir.epoch Q + 1)) Dh.base)))
        (sC.base.mir.epoch Q + 1) 0 []).accept i) v')
    (hT_ne0 : Dh.dh (epExp (sC.base.mir.epoch Q + 1)) Dh.base ≠ 0)
    (hpq' : InvB Inv q r pq')
    (kept' : Party → Kept Pt)
    (s' : SimState PQ Pt ℓ)
    (hs' : s' =
      let t := sC.base.mir.epoch Q + 1
      let srk := encT (Dh.dh (epExp t) Dh.base)
      let g_init : GhostChain := ⟨some srk, t, 0, []⟩
      { sC.base with
        mir := sC.base.mir.accept Q () pos,
        pq := Function.update sC.base.pq Q pq',
        unackA := sC.base.unackA && Q != Party.A,
        chains :=
          Function.update sC.base.chains Q (pushChain (sC.base.chains Q) (g_init.accept i)) })
    (s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hs_fig8' : s_fig8' =
      let t := sC.base.mir.epoch Q + 1
      let T := Dh.dh (epExp t) Dh.base
      let p₁ := (rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (epExp (sC.base.mir.epoch Q)) T)
      let st' : Fig8St Pt :=
        { (s_fig8.st Q) with
          root := p₁.1,
          vR := Function.update (s_fig8.st Q).vR t (some v'),
          γ := .pub T,
          tcur := t }
      s_fig8.accept Q st' pos)
    (hkept' : KeptInv P Dh encPt encT idOf lam { sC with base := s', kept := kept' } s_fig8')
    (hsync8' : EpochSync P Dh encPt encT idOf s'.honest sC.sent sC.snaps s_fig8' epExp) :
    ∃ s_R' ec',
      SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R'
        { sC with base := s', kept := kept' } s_fig8' ec' winBefore epExp := by
  subst hs' hs_fig8'
  have hsim' := simInvCLazy_deliver_newChain_accept P (InvB Inv q r) Dh encPt encT qep q r x₀
    hinv.hsim Q hinw_Q hQ_recv hinw_other hep_other i pq' pos hpos_ep v' hsync' hT_ne0 hpq'
  refine ⟨_, _,
    { hsim := hsim'
      huniq := hinv.huniq
      hkept := hkept'
      hidx := ?_
      hsync := hsync8' }⟩
  intro wc hwc hep_wc
  have hle_ep := (hinv.hsim.hhon wc hwc).2.2.2
  by_cases hSQ : Party.senderOf wc.2.1.1 = Q
  · exfalso
    have hep'_Q : (sC.base.mir.accept Q () pos).epoch Q = sC.base.mir.epoch Q + 1 := by
      dsimp only [SM.GameState.accept, SM.GameState.delete]
      simp [Function.update_self, hpos_ep]
    dsimp only at hep_wc
    rw [hSQ] at hle_ep hep_wc
    rw [hep'_Q] at hep_wc
    omega
  · have hep'_ne : (sC.base.mir.accept Q () pos).epoch (Party.senderOf wc.2.1.1) =
        sC.base.mir.epoch (Party.senderOf wc.2.1.1) := by
      dsimp only [SM.GameState.accept, SM.GameState.delete]
      simp [Function.update_of_ne hSQ]
    dsimp only at hep_wc
    rw [hep'_ne] at hep_wc
    exact hinv.hidx wc hwc hep_wc

omit [SampleableType Pt] in
theorem fwdCPure_of_win_true
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : List (BitVec 8)) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ) (hwin : x.2.1.win = true) :
    (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c' x).2.1 = x.1 ∧
    (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c' x).2.2.1 =
      x.2.1 := by
  have hplain :
      (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' none c' x).2.1 = x.1 ∧
      (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' none c' x).2.2.1 =
        x.2.1 := by
    unfold fwdCPure
    dsimp only
    rw [fwdPure_of_win_true P ℓ Dh encPt encT idOf lam qep x.1.base Q c' x.2.1 hwin]
    unfold onAnswerPure
    exact ⟨rfl, rfl⟩
  cases honestC with
  | none => exact hplain
  | some c₀ =>
    unfold fwdCPure
    dsimp only
    split
    · cases predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) P x.1 Q w c₀ c' with
      | none => exact ⟨rfl, rfl⟩
      | some ev =>
        cases ev with
        | none => exact ⟨rfl, rfl⟩
        | some tip =>
          rcases tip with ⟨t₁, i₁, pm₁⟩
          dsimp only
          have hdel : deliverPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
              SM.Config.h1 Q c₀ x.2.1 = (none, x.2.1) := by
            unfold deliverPure; simp [hwin]
          rw [hdel]
          exact ⟨rfl, rfl⟩
    · exact hplain

private theorem fwdCPure_plain_deliver_eq_of_not_honest
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (c' : Fig8C Pt) (x : JointC (List (BitVec 8)) Pt ℓ)
    (hsafe : x.1.base.mir.safeInj 3 = true)
    (hcomp : ∀ p ∈ x.1.base.mir.comp, SM.healedBy x.1.base.mir.tL 3 p.epoch = false)
    (hc'_not_hon : ∀ wc ∈ x.1.base.honest, wc.2 ≠ c')
    (htriv_eq : ∀ pos, x.2.1.trivial 3 pos = x.1.base.mir.trivial 3 pos)
    (hep_lt : x.1.base.mir.epoch Q < c'.1.1) :
    (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w true ci? T pq' none c' x).2.1 = x.1 ∧
    clearWin (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w true ci? T pq' none c' x).2.2.1 =
      clearWin x.2.1 := by
  have hfwd :
      fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
        x.1.base Q c' x.2.1 =
      injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
        Q c' x.2.1 := by
    unfold fwdPure
    have hany :
        x.1.base.honest.any
          (fun wc => decide (wc.2 = c') && (x.1.base.mir.inTransit Q.other wc.1).isSome) =
        false := by
      rw [List.any_eq_false]
      intro wc hwc
      simp [hc'_not_hon wc hwc]
    rw [hany]
    rfl
  unfold fwdCPure clearWin
  dsimp only
  rw [hfwd]
  unfold injectPure
  split
  · unfold onAnswerPure; exact ⟨rfl, rfl⟩
  · cases hrec :
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (x.2.1.st Q) c' with
    | none => unfold onAnswerPure; exact ⟨rfl, rfl⟩
    | some val =>
      rcases val with ⟨st', t', i', pm⟩
      rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
        (x.2.1.st Q) c' hrec with ⟨ht', _⟩
      dsimp only
      split
      · unfold onAnswerPure; exact ⟨rfl, rfl⟩
      · have htriv_f : x.1.base.mir.trivial 3 ⟨Q.other, t', i'⟩ = false :=
          trivial_false_of_newChain_inject hsafe hcomp Q ⟨Q.other, t', i'⟩
            (by dsimp only; omega)
        rw [htriv_eq, htriv_f]
        simp only [Bool.false_eq_true, ↓reduceIte]
        split <;> (unfold onAnswerPure; exact ⟨rfl, rfl⟩)

theorem simRecvStepCGen_deliver_knownChain_preserves_simInvCXLazy
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q r' r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hr : r' < r)
    (Q : Party) (w : List (BitVec 8)) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false }
      ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    {pq' : List (BitVec 8)} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    {ci : ℕ}
    (hfind : (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) = some ci)
    (hrej_f : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false) :
    let i := h.counter.toNat + 1
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let honestC :=
      (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    let ch := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
    let c_mk : Fig8C Pt :=
      match honestC with
      | some c₀ =>
        if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀
        else ((ch.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
      | none => ((ch.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    let r_out := fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true (some ci)
      h.senderRatchetKey pq' honestC c_mk (sC, g, false)
    ∃ s_R' ec' winBefore',
      SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
        r_out.2.1 { r_out.2.2.1 with win := false } ec' winBefore' epExp := by
  intro i ser tag honestC ch c_mk r_out
  have hinv_mono := simInvCXLazy_mono_r hinv (Nat.le_of_lt hr)
  cases hg_win : g.win
  · have hg_eq0 : { g with win := false } = g := by cases g; subst hg_win; rfl
    rw [hg_eq0] at hinv
    have hmeta := hinv.hsim.hmeta
    have hpq' : InvB Inv q r pq' := InvB.recv hS (hinv.hsim.hpqInv Q) hspqr
    rcases deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp
      (max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B)) hmeta hinv.huniq
      (fun wc hwc => ⟨(hinv.hsim.hhon wc hwc).1, (hinv.hsim.hhon wc hwc).2.1⟩)
      (fun rec_f hrec =>
        ⟨(hinv.hsim.htrans_hon rec_f hrec).1, (hinv.hsim.htrans_hon rec_f hrec).2.1⟩)
      hinv.hsim.hcoll Q w htr_mir with
      ⟨_, c, r_fig8, hc_mem, hc_sender, hr_fig8, hpos_fig8, hhonC, hfwd_c⟩
    rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp (hinv.hsim.hhon (w, c) hc_mem).1
      hparse with ⟨_, hsrk, hctr, hc_raw⟩
    rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
      ⟨ch', hch_elem', hch_key'⟩
    have hch_eq : ch = ch' := by simp [ch, hch_elem']
    have hch_elem : (sC.base.chains Q)[ci]? = some ch := by rw [hch_eq, hch_elem']
    have hch_key : ch.key = some h.senderRatchetKey := by rw [hch_eq, hch_key']
    have hch_mem : ch ∈ sC.base.chains Q := List.mem_of_getElem? hch_elem
    rcases hinv.hsim.hchains_sync Q ch hch_mem with
      ⟨hch_ep_le, hch_recv, hch_key_sync, v_old, hvR, hsync_old⟩
    have hch_none : ch.key.isNone = false := by rw [hch_key]; rfl
    rw [hch_none] at hch_key_sync
    simp only [Bool.false_eq_true, ↓reduceIte, hch_key] at hch_key_sync
    have hdh : Dh.dh (epExp ch.epoch) Dh.base = Dh.dh (epExp c.1.1) Dh.base :=
      hinj ((Option.some.inj hch_key_sync).symm.trans hsrk)
    have hle_ch : ch.epoch ≤ max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B) := by
      cases Q <;>
        [exact le_trans hch_ep_le (le_max_left _ _); exact le_trans hch_ep_le (le_max_right _ _)]
    have hch_ep : ch.epoch = c.1.1 :=
      hinv.hsim.hcoll ch.epoch c.1.1 hle_ch (hinv.hsim.hhon (w, c) hc_mem).2.1 hdh
    have hdec_srk : decT h.senderRatchetKey = some (Dh.dh (epExp c.1.1) Dh.base) := by
      rw [hsrk, hdec]
    let c' : Fig8C Pt := ((ch.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    have hc1 : c.1 = (ch.epoch, decT h.senderRatchetKey) := by
      rw [hch_ep, hdec_srk]; exact congrArg Prod.fst hc_raw
    have hc21 : c.2.1 = i := hctr.symm
    have hc_decomp : c = ((ch.epoch, decT h.senderRatchetKey), (i, c.2.2)) := by
      rcases c with ⟨c1, c21, c22⟩
      dsimp only at hc1 hc21 ⊢
      rw [hc1, hc21]
    have hpos_mir_eq : r_mir.pos = ⟨Q.other, ch.epoch, i⟩ := by
      have hr_mem : r_fig8 ∈ g.trans := List.mem_of_find?_eq_some hr_fig8
      rcases hinv.hsim.htrans_hon r_fig8 hr_mem with ⟨_, hpos_s, hpos_e, hpos_i⟩
      have hpred := List.find?_some hr_fig8
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
      rcases hpred with ⟨_, hct_eq⟩
      rw [← hpos_fig8]
      cases hr_pos : r_fig8.pos
      simp only [hr_pos] at hpos_s hpos_e hpos_i ⊢
      rw [hct_eq] at hpos_s hpos_e hpos_i
      rw [hpos_s, hc_sender, hpos_e, ← hch_ep, hpos_i, hc21]
    have hpos_ep : r_mir.pos.epoch = ch.epoch := by rw [hpos_mir_eq]
    have hold : ch.epoch ≤ (g.st Q).tcur := by rw [hinv.hsim.htcur Q]; exact hch_ep_le
    have haccept_step : ∀ (c_acc : Fig8C Pt) (st' : Fig8St Pt) (pm : LibsignalMsgPublicPart × Plain ℓ),
        c_acc = ((ch.epoch, decT h.senderRatchetKey), (i, c_acc.2.2)) →
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c_acc =
          some (st', ch.epoch, i, pm) →
        let s' : SimState (List (BitVec 8)) Pt ℓ :=
          { sC.base with
            mir := sC.base.mir.accept Q () r_mir.pos,
            pq := Function.update sC.base.pq Q pq',
            unackA := sC.base.unackA && Q != Party.A,
            chains := Function.update sC.base.chains Q ((sC.base.chains Q).modify ci (·.accept i)) }
        let kept' := Function.update sC.kept Q
          (Kept.recv (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (fs := lFS P.C P.codec ℓ encT idOf 25000) c_acc (sC.kept Q))
        let g' := g.accept Q st' r_mir.pos
        ∃ s_R' ec' winBefore',
          SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
            { sC with base := s', kept := kept' } { g' with win := false } ec' winBefore'
            epExp := by
      intro c_acc st' pm hc_acc hfig_acc s' kept' g'
      have hrec_raw : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q)
          ((ch.epoch, decT h.senderRatchetKey), (h.counter.toNat + 1, c_acc.2.2)) =
          some (st', ch.epoch, i, pm) := by
        rw [← hc_acc]; exact hfig_acc
      rcases lFig8_receive_knownChain_accept P ℓ Dh encPt encT idOf lam Q (g.st Q)
        (sC.base.mir.epoch Q) ch v_old (hinv.hsim.hst_id Q) (hinv.hsim.htcur Q) hch_ep_le hch_recv
        hvR hsync_old h.counter hrej_f (decT h.senderRatchetKey) c_acc.2.2 hrec_raw with
        ⟨_, _, v', hst', hsync'⟩
      have hkept' : KeptInv P Dh encPt encT idOf lam { sC with base := s', kept := kept' } g' :=
        keptInv_recv_accept hinv.hkept Q (hinv.hsim.hst_id Q) c_acc st' (ch.epoch, i, pm)
          hfig_acc rfl rfl
      have hacc_ep : c_acc.1.1 = ch.epoch := by rw [hc_acc]
      have hsync8' : EpochSync P Dh encPt encT idOf s'.honest sC.sent sC.snaps g' epExp :=
        epochSync_recv_old P Dh encPt encT idOf lam _ _ _ _ _ hinv.hsync Q c_acc st'
          (ch.epoch, i, pm) hfig_acc (hacc_ep ▸ hold) rfl (fun hw => hw) (fun _ hwc => hwc)
      have hg'_win : { g' with win := false } = g' := by
        cases g; subst hg_win; rfl
      rw [hg'_win]
      let s_R' := s_R.accept Q
        (expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q)) r_mir.pos
      have hinv_sub1 : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R'
          { sC with base := s', kept := kept' } g' ec winBefore epExp := by
        subst hst'
        exact simInvCXLazy_inject_known_accept P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC g
          ec winBefore epExp hinv Q ci ch i pq' hch_elem v' hsync' r_mir.pos hpos_ep hpq'
          s' rfl g' rfl s_R' rfl kept' hkept' hsync8'
      exact ⟨s_R', ec, winBefore,
        simInvCXLazy_mono_r hinv_sub1 (Nat.le_sub_one_of_lt hr)⟩
    dsimp only [r_out, c_mk, honestC]
    rw [hhonC]
    dsimp only
    by_cases hsalt : c.2.2.2 = effectiveHkdfSalt32 salt
    · simp only [hsalt, ↓reduceIte]
      unfold fwdCPure
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.and_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      rw [hfwd_c]
      unfold deliverPure
      simp only [hg_win, Bool.false_eq_true, ↓reduceIte, hr_fig8, SM.Config.h1, Bool.false_and]
      cases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c with
      | none =>
        unfold onAnswerPure
        dsimp only
        exact ⟨s_R, ec, winBefore, hinv_mono⟩
      | some val =>
        rcases val with ⟨st', t', i', pm⟩
        rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam (g.st Q) c hfig with
          ⟨ht', hi'⟩
        rw [← hch_ep] at ht'
        rw [hc21] at hi'
        subst ht' hi'
        unfold onAnswerPure onAcceptPure
        simp only [↓reduceIte, htr_mir, hpos_fig8]
        exact haccept_step c st' pm hc_decomp hfig
    · simp only [hsalt, ↓reduceIte]
      have hc_ne : c ≠ c' := fun heq => hsalt (congrArg (fun z : Fig8C Pt => z.2.2.2) heq)
      have hc_ne_dec : decide (c ≠ c') = true := decide_eq_true hc_ne
      change ∃ s_R' ec' winBefore',
        SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
          (fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true (some ci) h.senderRatchetKey pq'
            (some c) c' (sC, g, false)).2.1
          { (fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true (some ci) h.senderRatchetKey pq'
            (some c) c' (sC, g, false)).2.2.1 with win := false } ec' winBefore' epExp
      unfold fwdCPure
      dsimp only
      cases hsafe : sC.base.mir.safeInj 3 with
      | false =>
        simp only [hc_ne_dec, Bool.not_false, Bool.and_self, ↓reduceIte]
        cases heval : predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' with
        | none =>
          dsimp only; exact ⟨s_R, ec, winBefore, hinv_mono⟩
        | some ev =>
          cases ev with
          | none =>
            dsimp only; exact ⟨s_R, ec, winBefore, hinv_mono⟩
          | some tip =>
            rcases tip with ⟨t_ev, i_ev, pm_ev⟩
            rcases evalCK_some_some_epoch_idx_eq P ℓ Dh encPt encT idOf lam sC Q w c c' heval with
              ⟨ht_ev, hi_ev⟩
            dsimp only [c'] at ht_ev hi_ev
            subst ht_ev hi_ev
            dsimp only
            unfold deliverPure
            simp only [hg_win, Bool.false_eq_true, ↓reduceIte, hr_fig8, SM.Config.h1,
              Bool.false_and]
            cases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c with
            | none =>
              dsimp only; exact ⟨s_R, ec, winBefore, hinv_mono⟩
            | some val =>
              rcases val with ⟨st', t', i', pm⟩
              rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam (g.st Q) c
                hfig with ⟨ht', hi'⟩
              rw [← hch_ep] at ht'
              rw [hc21] at hi'
              subst ht' hi'
              unfold onAcceptPure
              simp only [↓reduceIte, htr_mir, hpos_fig8]
              exact haccept_step c st' pm hc_decomp hfig
      | true =>
        simp only [hc_ne_dec, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        have hc'_not_hon : ∀ wc ∈ sC.base.honest, wc.2 ≠ c' := by
          intro wc hwc heq
          have hwc1 : wc.1 = w := by
            rw [(hinv.hsim.hhon wc hwc).1.1, heq]
            exact toWire_raw_eq w hlen ch.epoch (decT h.senderRatchetKey) i (effectiveHkdfSalt32 salt)
          have hwc_mem : (w, c') ∈ sC.base.honest := by rwa [← hwc1, ← heq]
          have hc_eq := honestEntryInvC_unique P (InvB Inv q r) Dh encT hinj epExp
            sC.base hinv.huniq hc_mem hwc_mem (hinv.hsim.hhon (w, c) hc_mem).1
            (hinv.hsim.hhon (w, c') hwc_mem).1
            (hinv.hsim.hcoll c.1.1 c'.1.1 (hinv.hsim.hhon (w, c) hc_mem).2.1
              (hinv.hsim.hhon (w, c') hwc_mem).2.1)
          exact hc_ne hc_eq
        have hfwd_c' :
            fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
              sC.base Q c' g =
            injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
              Q c' g := by
          unfold fwdPure
          have hany :
              sC.base.honest.any
                (fun wc => decide (wc.2 = c') && (sC.base.mir.inTransit Q.other wc.1).isSome) =
              false := by
            rw [List.any_eq_false]
            intro wc hwc
            simp [hc'_not_hon wc hwc]
          rw [hany]; rfl
        have htr_fig8' : (g.inTransit Q.other c').isSome = false := by
          cases htr_f : g.inTransit Q.other c' with
          | none => rfl
          | some r_f =>
            exfalso
            have hr_mem : r_f ∈ g.trans := List.mem_of_find?_eq_some htr_f
            have hpred := List.find?_some htr_f
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
            have hhon_f := (hinv.hsim.htrans_hon r_f hr_mem).1
            exact hc'_not_hon _ hhon_f hpred.2
        have hguard_fig8 :
            (g.win || (g.inTransit Q.other c').isSome || !(g.safeInj 3)) = false := by
          rw [hg_win, htr_fig8', hmeta.safeInj_fig8, hsafe]; rfl
        rw [hfwd_c']
        unfold injectPure
        simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte]
        cases hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' with
        | none =>
          unfold onAnswerPure; dsimp only; exact ⟨s_R, ec, winBefore, hinv_mono⟩
        | some val =>
          rcases val with ⟨st', t', i', pm⟩
          rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam (g.st Q) c'
            hfig' with ⟨ht', hi'⟩
          dsimp only [c'] at ht' hi'
          subst ht' hi'
          have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < ch.epoch) := by
            have := hinv.hsim.hep_le Q; omega
          simp only [hnot_gt_fig8, ↓reduceIte]
          by_cases htriv : g.trivial 3 ⟨Q.other, ch.epoch, i⟩ = true
          · simp only [htriv, ↓reduceIte]
            unfold onAnswerPure onAcceptPure
            simp only [↓reduceIte, htr_mir, ← hpos_mir_eq]
            exact haccept_step c' st' pm rfl hfig'
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
            unfold onAnswerPure
            dsimp only
            exact ⟨s_R, ec, winBefore, hinv_mono⟩
  · have hwin := fwdCPure_of_win_true P ℓ Dh encPt encT idOf lam qep true Q w true (some ci)
      h.senderRatchetKey pq' honestC c_mk (sC, g, false) hg_win
    dsimp only [r_out]
    rw [hwin.1, hwin.2]
    exact ⟨s_R, ec, winBefore, hinv_mono⟩

theorem simRecvStepC_deliver_preserves_simInvCXLazy
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q r' r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hr : r' < r)
    (Q : Party) (w : List (BitVec 8)) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false }
      ec winBefore epExp) :
    let out := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
    ∃ s_R' ec' winBefore',
      SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
        out.2.1 { out.2.2.1 with win := false } ec' winBefore' epExp := by
  have hinv_mono := simInvCXLazy_mono_r hinv (Nat.le_of_lt hr)
  have hstop := hinv.hsim.hmeta.hstop
  have hwin_mir := hinv.hsim.hmeta.hwin_mir
  unfold simRecvStepC simRecvStepCGen
  simp only [hstop, hwin_mir, Bool.false_eq_true, ↓reduceIte, Bool.true_and, Bool.not_true,
    Bool.false_and]
  cases htr_mir : sC.base.mir.inTransit Q.other w with
  | none =>
    simp only [Option.isNone_none, ↓reduceIte]
    exact ⟨s_R, ec, winBefore, hinv_mono⟩
  | some r_mir =>
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : w.length < 9
    · simp only [hlen, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
    simp only [hlen, ↓reduceIte]
    cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
    | none => exact ⟨s_R, ec, winBefore, hinv_mono⟩
    | some hb =>
      rcases hb with ⟨h, body⟩
      dsimp only
      by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
      · simp only [haddr, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
      simp only [haddr, Bool.false_eq_true, ↓reduceIte]
      by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
      · simp only [hpan, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
      simp only [hpan, Bool.false_eq_true, ↓reduceIte]
      cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
      | error _ => exact ⟨s_R, ec, winBefore, hinv_mono⟩
      | ok ps =>
        rcases ps with ⟨pq', salt⟩
        dsimp only
        cases hfind : (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) with
        | some ci =>
          dsimp only
          by_cases hrej :
              ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = true
          · simp only [hrej, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
          simp only [hrej, Bool.false_eq_true, ↓reduceIte]
          exact simRecvStepCGen_deliver_knownChain_preserves_simInvCXLazy P Inv ℓ Dh encPt encT
            decT idOf hinj hdec lam qep q r' r hS hr Q w x₀ s_R sC g ec winBefore epExp hinv
            htr_mir hlen hparse hspqr hfind (Bool.eq_false_iff.mpr hrej)
        | none =>
          dsimp only
          have hs_stop : { sC.base with amb := sC.base.amb + 1, stopped := false } =
              { sC.base with amb := sC.base.amb + 1 } := by
            cases h_s : sC.base; rw [h_s] at hstop; subst hstop; rfl
          simp only [hs_stop]
          split
          · exact ⟨s_R, ec, winBefore, hinv_mono⟩
          · split
            · exact ⟨s_R, ec, winBefore, hinv_mono⟩
            · rename_i hnot_ev_match hnot_zero
              have hinv_amb : ∃ winBefore_amb,
                  SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R
                    { sC with base := { sC.base with amb := sC.base.amb + 1 } }
                    { g with win := false } ec winBefore_amb epExp :=
                ⟨_, simInvCXLazy_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r
                  (Nat.zero_lt_of_lt hr) x₀ s_R sC { g with win := false } ec winBefore epExp
                  hinv rfl⟩
              obtain ⟨winBefore_amb, hinv_amb⟩ := hinv_amb
              let x₁ : JointC (List (BitVec 8)) Pt ℓ :=
                if inReceiveOnlyEpoch sC.base.mir Q ||
                    (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
                  ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, g, false)
                else (sC, g, false)
              have hx₁_inv_sub1 : ∃ winBefore₁,
                  SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R x₁.1
                    { x₁.2.1 with win := false } ec winBefore₁ epExp := by
                dsimp only [x₁]
                split
                · exact ⟨winBefore_amb, hinv_amb⟩
                · exact ⟨winBefore, simInvCXLazy_mono_r hinv (Nat.sub_le r 1)⟩
              obtain ⟨winBefore₁, hinv₁_sub1⟩ := hx₁_inv_sub1
              have hinv₁ := simInvCXLazy_mono_r hinv₁_sub1 (Nat.le_sub_one_of_lt hr)
              have hx1_hon : x₁.1.base.honest = sC.base.honest := by dsimp only [x₁]; split <;> rfl
              have hx1_mir : x₁.1.base.mir = sC.base.mir := by dsimp only [x₁]; split <;> rfl
              have hx1_pq : x₁.1.base.pq = sC.base.pq := by dsimp only [x₁]; split <;> rfl
              have hx1_chains : x₁.1.base.chains = sC.base.chains := by
                dsimp only [x₁]; split <;> rfl
              have hx1_unack : x₁.1.base.unackA = sC.base.unackA := by
                dsimp only [x₁]; split <;> rfl
              have hx1_kept : x₁.1.kept = sC.kept := by dsimp only [x₁]; split <;> rfl
              have hx1_sent : x₁.1.sent = sC.sent := by dsimp only [x₁]; split <;> rfl
              have hx1_snaps : x₁.1.snaps = sC.snaps := by dsimp only [x₁]; split <;> rfl
              have hx1_g : x₁.2.1 = g := by dsimp only [x₁]; split <;> rfl
              split
              · exact ⟨s_R, ec, winBefore₁, hinv₁⟩
              · rename_i hnot_bound
                simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hnot_bound
                have hinw_Q : inReceiveOnlyEpoch sC.base.mir Q = false := Bool.eq_false_iff.mpr hnot_bound.1.1
                cases hT : decT h.senderRatchetKey with
                | none => dsimp only; exact ⟨s_R, ec, winBefore₁, hinv₁⟩
                | some T =>
                  dsimp only
                  let i := h.counter.toNat + 1
                  let ser := w.take (w.length - 8)
                  let tag := bytesToWord64LE (w.drop (w.length - 8))
                  let c_fb : Fig8C Pt :=
                    ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
                  rcases deliver_inTransit_syncC P (InvB Inv q r) Dh encT hinj epExp
                    (max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B)) hinv.hsim.hmeta hinv.huniq
                    (fun wc hwc => ⟨(hinv.hsim.hhon wc hwc).1, (hinv.hsim.hhon wc hwc).2.1⟩)
                    (fun rec_f hrec => ⟨(hinv.hsim.htrans_hon rec_f hrec).1,
                      (hinv.hsim.htrans_hon rec_f hrec).2.1⟩)
                    hinv.hsim.hcoll Q w htr_mir with
                    ⟨_, c, r_fig8, hc_mem, hc_sender, hr_fig8, hpos_fig8, hhonC, hfwd_c⟩
                  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp
                    (hinv.hsim.hhon (w, c) hc_mem).1 hparse with ⟨_, hsrk, hctr, hc_raw⟩
                  split
                  · rename_i hev_true
                    have hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1 := by
                      change (((sC.base.honest.find? fun wc =>
                          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                        fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true at hev_true
                      rw [hhonC] at hev_true
                      simpa using hev_true
                    have hc_fb_not_hon : ∀ wc ∈ x₁.1.base.honest, wc.2 ≠ c_fb := by
                      intro wc hwc heq
                      rw [hx1_hon] at hwc
                      have hwc1 : wc.1 = w := by
                        rw [(hinv.hsim.hhon wc hwc).1.1, heq]
                        exact toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T) i
                          (effectiveHkdfSalt32 salt)
                      have hwc_mem : (w, c_fb) ∈ sC.base.honest := by rwa [← hwc1, ← heq]
                      have hc_eq := honestEntryInvC_unique P (InvB Inv q r) Dh encT hinj epExp
                        sC.base hinv.huniq hc_mem hwc_mem (hinv.hsim.hhon (w, c) hc_mem).1
                        (hinv.hsim.hhon (w, c_fb) hwc_mem).1
                        (hinv.hsim.hcoll c.1.1 c_fb.1.1 (hinv.hsim.hhon (w, c) hc_mem).2.1
                          (hinv.hsim.hhon (w, c_fb) hwc_mem).2.1)
                      exact hepoch (congrArg (fun z : Fig8C Pt => z.1.1) hc_eq)
                    have htriv₁ : ∀ pos, x₁.2.1.trivial 3 pos = x₁.1.base.mir.trivial 3 pos := by
                      intro pos
                      rw [hx1_g, hx1_mir]
                      exact hinv.hsim.hmeta.trivial_fig8 3 pos
                    have hev := fwdEvictCPure_deliver_eq_of_not_honest P ℓ Dh encPt encT idOf lam
                      qep true Q w h.senderRatchetKey pq' c_fb x₁ (fun h => by cases h)
                      (hx1_mir.symm ▸ hinv.hsim.hcomp) hc_fb_not_hon htriv₁
                      (by rw [hx1_mir]; dsimp only [c_fb]; omega)
                    change ∃ s_R' ec' winBefore',
                      SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
                        (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep true Q w true
                          h.senderRatchetKey pq' c_fb x₁).2.1
                        (clearWin (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep true Q w true
                          h.senderRatchetKey pq' c_fb x₁).2.2.1) ec' winBefore' epExp
                    rw [hev.1, hev.2]
                    exact ⟨s_R, ec, winBefore₁, hinv₁⟩
                  · rename_i hev_false
                    have hepoch : c.1.1 = sC.base.mir.epoch Q + 1 := by
                      change ¬((((sC.base.honest.find? fun wc =>
                          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                        fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
                        at hev_false
                      rw [hhonC] at hev_false
                      simp only [Option.map_some, beq_iff_eq, Option.some.injEq,
                        decide_eq_true_eq, not_ne_iff] at hev_false
                      exact hev_false
                    let honestC := (sC.base.honest.find? fun wc =>
                      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
                    let c_mk : Fig8C Pt :=
                      match honestC with
                      | some c₀ => if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀ else c_fb
                      | none => c_fb
                    let r_out := fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true none
                      h.senderRatchetKey pq' honestC c_mk x₁
                    change ∃ s_R' ec' winBefore',
                      SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
                        r_out.2.1 { r_out.2.2.1 with win := false } ec' winBefore' epExp
                    cases hg_win : g.win
                    · have hg_eq0 : { g with win := false } = g := by cases g; subst hg_win; rfl
                      rw [hx1_g, hg_eq0] at hinv₁_sub1
                      have hr_fig8' : g.inTransit Q.other c = some r_fig8 := hr_fig8
                      have hpq' : InvB Inv q (r - 1) pq' :=
                        InvB.mono (Nat.sub_le r 1) (InvB.recv hS (hinv.hsim.hpqInv Q) hspqr)
                      have hT_eq : T = Dh.dh (epExp (sC.base.mir.epoch Q + 1)) Dh.base := by
                        rw [hsrk, hepoch, hdec] at hT
                        exact Option.some.inj hT.symm
                      have hT_ne0 : Dh.dh (epExp (sC.base.mir.epoch Q + 1)) Dh.base ≠ 0 := by
                        intro h0
                        apply hnot_zero
                        rw [hT, hT_eq, h0]
                        simp
                      have hsrk_ep :
                          h.senderRatchetKey =
                            encT (Dh.dh (epExp (sC.base.mir.epoch Q + 1)) Dh.base) := by
                        rw [← hepoch]; exact hsrk
                      have hQ_recv : Q.sendsIn (sC.base.mir.epoch Q + 1) = false :=
                        sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw_Q
                      have hQQ : Q.other.other = Q := by cases Q <;> rfl
                      have hep_other : sC.base.mir.epoch Q.other = sC.base.mir.epoch Q + 1 := by
                        have h1 : sC.base.mir.epoch Q + 1 ≤ sC.base.mir.epoch Q.other := by
                          rw [← hepoch, ← hc_sender]; exact (hinv.hsim.hhon (w, c) hc_mem).2.2.2
                        have h2 : sC.base.mir.epoch Q.other ≤ sC.base.mir.epoch Q + 1 := by
                          have := (hinv.hsim.hep_adj Q.other).2
                          rwa [hQQ] at this
                        omega
                      have hinw_other : inReceiveOnlyEpoch sC.base.mir Q.other = false := by
                        rw [Bool.eq_false_iff]
                        intro hinw_O
                        have := (hinv.hsim.hep_adj Q.other).1 hinw_O
                        rw [hQQ] at this
                        omega
                      have hc1 : c.1 = (sC.base.mir.epoch Q + 1, some T) := by
                        rw [← hepoch, hT_eq, ← hepoch]; exact congrArg Prod.fst hc_raw
                      have hc21 : c.2.1 = i := hctr.symm
                      have hc221 : c.2.2.1 = (ser, tag) :=
                        congrArg (fun z : Fig8C Pt => z.2.2.1) hc_raw
                      have hc_decomp :
                          c = ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), c.2.2.2))) := by
                        rcases c with ⟨c1, c21, c221, c222⟩
                        dsimp only at hc1 hc21 hc221 ⊢
                        rw [hc1, hc21, hc221]
                      have hpos_mir_ep : r_mir.pos.epoch = sC.base.mir.epoch Q + 1 := by
                        have hr_mem : r_fig8 ∈ g.trans := List.mem_of_find?_eq_some hr_fig8
                        have hpos_e := (hinv.hsim.htrans_hon r_fig8 hr_mem).2.2.1
                        have hpred := List.find?_some hr_fig8
                        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
                        rw [← hpos_fig8, hpos_e, hpred.2, hepoch]
                      have hjump : ¬ 25000 < i - 1 := hnot_bound.1.2
                      let g_init : GhostChain :=
                        ⟨some h.senderRatchetKey, sC.base.mir.epoch Q + 1, 0, []⟩
                      have hrej_init : g_init.rejects i = false := by
                        rw [g_init_rejects_eq (some h.senderRatchetKey) (sC.base.mir.epoch Q + 1) i
                          (by dsimp only [i]; omega) (by dsimp only [i]; omega)]
                        exact decide_eq_false hjump
                      rcases hinv.hsim.hspur Q with ⟨_, _, _, hspur_notinw⟩
                      rcases hspur_notinw hinw_Q with ⟨hγ_Q, _, _⟩
                      have haccept_new : ∀ (st' : Fig8St Pt) (pm : LibsignalMsgPublicPart × Plain ℓ),
                          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c =
                            some (st', sC.base.mir.epoch Q + 1, i, pm) →
                          let s' : SimState (List (BitVec 8)) Pt ℓ :=
                            { x₁.1.base with
                              mir := x₁.1.base.mir.accept Q () r_mir.pos,
                              pq := Function.update x₁.1.base.pq Q pq',
                              unackA := x₁.1.base.unackA && Q != Party.A,
                              chains := Function.update x₁.1.base.chains Q
                                (pushChain (x₁.1.base.chains Q) (g_init.accept i)) }
                          let kept' := Function.update x₁.1.kept Q
                            (Kept.recv (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
                              (fs := lFS P.C P.codec ℓ encT idOf 25000) c (x₁.1.kept Q))
                          let g' := g.accept Q st' r_mir.pos
                          ∃ s_R' ec' winBefore',
                            SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
                              { x₁.1 with base := s', kept := kept' }
                              { g' with win := false } ec' winBefore' epExp := by
                        intro st' pm hfig s' kept' g'
                        have hrec_raw :
                            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q)
                              ((sC.base.mir.epoch Q + 1, some T),
                                (h.counter.toNat + 1, ((ser, tag), c.2.2.2))) =
                              some (st', sC.base.mir.epoch Q + 1, i, pm) := by
                          rw [← hc_decomp]; exact hfig
                        rcases lFig8_receive_newChain_accept P ℓ Dh encPt encT idOf lam Q (g.st Q)
                          (sC.base.mir.epoch Q) (epExp (sC.base.mir.epoch Q)) h.senderRatchetKey
                          (hinv.hsim.hst_id Q) (hinv.hsim.htcur Q) hQ_recv hγ_Q h.counter
                          hrej_init T ((ser, tag), c.2.2.2) hrec_raw with
                          ⟨_, _, v', hst', hsync'⟩
                        have hkept' :
                            KeptInv P Dh encPt encT idOf lam
                              { x₁.1 with base := s', kept := kept' } g' :=
                          keptInv_recv_accept hinv₁_sub1.hkept Q (hinv.hsim.hst_id Q) c st'
                            (sC.base.mir.epoch Q + 1, i, pm) hfig rfl rfl
                        have hnew_tcur : c.1.1 = (g.st Q).tcur + 1 := by
                          rw [hinv.hsim.htcur Q]; exact hepoch
                        have hsync8' :
                            EpochSync P Dh encPt encT idOf s'.honest x₁.1.sent x₁.1.snaps g'
                              epExp :=
                          epochSync_recv_new_lazy P Inv Dh encPt encT idOf lam qep q (r - 1) x₀ s_R
                            x₁.1 g ec winBefore₁ epExp hinv₁_sub1 Q w c c (hx1_hon.symm ▸ hc_mem)
                            hc_sender rfl hnew_tcur st' (sC.base.mir.epoch Q + 1, i, pm) hfig
                            s'.honest g' rfl (fun h => h) (fun _ hwc => hwc)
                        have hg'_win : { g' with win := false } = g' := by
                          cases g; subst hg_win; rfl
                        rw [hg'_win]
                        have hsync'_srk : ChainSync
                            ((GhostChain.mk
                              (some (encT (Dh.dh (epExp (x₁.1.base.mir.epoch Q + 1)) Dh.base)))
                              (x₁.1.base.mir.epoch Q + 1) 0 []).accept i) v' := by
                          rw [hx1_mir, ← hsrk_ep]; exact hsync'
                        obtain ⟨s_R', ec', hinv_new⟩ :=
                          simInvCXLazy_deliver_newChain_accept P Inv Dh encPt encT idOf lam qep q
                            (r - 1) x₀ s_R x₁.1 g ec winBefore₁ epExp hinv₁_sub1 Q
                            (hx1_mir.symm ▸ hinw_Q) (hx1_mir.symm ▸ hQ_recv)
                            (hx1_mir.symm ▸ hinw_other) (hx1_mir.symm ▸ hep_other) i pq'
                            r_mir.pos (hx1_mir.symm ▸ hpos_mir_ep) v' hsync'_srk
                            (hx1_mir.symm ▸ hT_ne0) hpq' kept' s'
                            (by dsimp only [s', g_init]; rw [hx1_mir, hsrk_ep])
                            g'
                            (by dsimp only [g']; rw [hst', hx1_mir, ← hT_eq])
                            hkept' hsync8'
                        exact ⟨s_R', ec', winBefore₁,
                          simInvCXLazy_mono_r hinv_new (Nat.le_sub_one_of_lt hr)⟩
                      have hfwd_c1 :
                          fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
                            SM.Config.h1 x₁.1.base Q c g =
                          deliverPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
                            SM.Config.h1 Q c g := by
                        have h := hfwd_c (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3
                          (qep + 1) SM.Config.h1
                        rw [hg_eq0] at h
                        unfold fwdPure at h ⊢
                        rw [hx1_hon, hx1_mir]
                        exact h
                      have htr_x1 : x₁.1.base.mir.inTransit Q.other w = some r_mir := by
                        rw [hx1_mir]; exact htr_mir
                      dsimp only [r_out, c_mk, honestC]
                      rw [hhonC]
                      dsimp only
                      by_cases hsalt : c.2.2.2 = effectiveHkdfSalt32 salt
                      · simp only [hsalt, ↓reduceIte]
                        unfold fwdCPure
                        simp only [ne_eq, not_true_eq_false, decide_false, Bool.and_false,
                          Bool.false_and, Bool.false_eq_true, ↓reduceIte, hx1_g]
                        rw [hfwd_c1]
                        unfold deliverPure
                        simp only [hg_win, Bool.false_eq_true, ↓reduceIte, hr_fig8', SM.Config.h1,
                          Bool.false_and]
                        cases hfig :
                            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive
                              (g.st Q) c with
                        | none =>
                          unfold onAnswerPure
                          dsimp only
                          rw [← hx1_g]
                          exact ⟨s_R, ec, winBefore₁, hinv₁⟩
                        | some val =>
                          rcases val with ⟨st', t', i', pm⟩
                          rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam
                            (g.st Q) c hfig with ⟨ht', hi'⟩
                          rw [hepoch] at ht'
                          rw [hc21] at hi'
                          subst ht' hi'
                          unfold onAnswerPure onAcceptPure
                          dsimp only
                          rw [htr_x1, hpos_fig8]
                          dsimp only
                          exact haccept_new st' pm hfig
                      · simp only [hsalt, ↓reduceIte]
                        have hc_ne : c ≠ c_fb :=
                          fun heq => hsalt (congrArg (fun z : Fig8C Pt => z.2.2.2) heq)
                        have hc_ne_dec : decide (c ≠ c_fb) = true := decide_eq_true hc_ne
                        change ∃ s_R' ec' winBefore',
                          SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
                            (fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true none
                              h.senderRatchetKey pq' (some c) c_fb x₁).2.1
                            { (fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true none
                              h.senderRatchetKey pq' (some c) c_fb x₁).2.2.1 with win := false }
                            ec' winBefore' epExp
                        cases hsafe : x₁.1.base.mir.safeInj 3 with
                        | false =>
                          unfold fwdCPure
                          simp only [hc_ne_dec, hsafe, Bool.not_false, Bool.and_self, ↓reduceIte,
                            hx1_g]
                          cases heval :
                              predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
                                (fs := lFS P.C P.codec ℓ encT idOf 25000) P x₁.1 Q w c c_fb with
                          | none =>
                            dsimp only; rw [← hx1_g]; exact ⟨s_R, ec, winBefore₁, hinv₁⟩
                          | some ev =>
                            cases ev with
                            | none =>
                              dsimp only; exact ⟨s_R, ec, winBefore₁, hinv₁⟩
                            | some tip =>
                              rcases tip with ⟨t_ev, i_ev, pm_ev⟩
                              rcases evalCK_some_some_epoch_idx_eq P ℓ Dh encPt encT idOf lam x₁.1
                                Q w c c_fb heval with ⟨ht_ev, hi_ev⟩
                              dsimp only [c_fb] at ht_ev hi_ev
                              subst ht_ev hi_ev
                              dsimp only
                              unfold deliverPure
                              simp only [hg_win, Bool.false_eq_true, ↓reduceIte, hr_fig8',
                                SM.Config.h1, Bool.false_and]
                              cases hfig :
                                  (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive
                                    (g.st Q) c with
                              | none =>
                                dsimp only; rw [← hx1_g]; exact ⟨s_R, ec, winBefore₁, hinv₁⟩
                              | some val =>
                                rcases val with ⟨st', t', i', pm⟩
                                rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf
                                  lam (g.st Q) c hfig with ⟨ht', hi'⟩
                                rw [hepoch] at ht'
                                rw [hc21] at hi'
                                subst ht' hi'
                                unfold onAcceptPure
                                dsimp only
                                rw [htr_x1, hpos_fig8]
                                dsimp only
                                exact haccept_new st' pm hfig
                        | true =>
                          have hc_fb_not_hon : ∀ wc ∈ x₁.1.base.honest, wc.2 ≠ c_fb := by
                            intro wc hwc heq
                            rw [hx1_hon] at hwc
                            have hwc1 : wc.1 = w := by
                              rw [(hinv.hsim.hhon wc hwc).1.1, heq]
                              exact toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T) i
                                (effectiveHkdfSalt32 salt)
                            have hwc_mem : (w, c_fb) ∈ sC.base.honest := by rwa [← hwc1, ← heq]
                            have hc_eq := honestEntryInvC_unique P (InvB Inv q r) Dh encT hinj epExp
                              sC.base hinv.huniq hc_mem hwc_mem (hinv.hsim.hhon (w, c) hc_mem).1
                              (hinv.hsim.hhon (w, c_fb) hwc_mem).1
                              (hinv.hsim.hcoll c.1.1 c_fb.1.1 (hinv.hsim.hhon (w, c) hc_mem).2.1
                                (hinv.hsim.hhon (w, c_fb) hwc_mem).2.1)
                            exact hc_ne hc_eq
                          have htriv₁ :
                              ∀ pos, x₁.2.1.trivial 3 pos = x₁.1.base.mir.trivial 3 pos := by
                            intro pos; rw [hx1_g, hx1_mir]; exact hinv.hsim.hmeta.trivial_fig8 3 pos
                          have hplain_eq :
                              fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true none
                                h.senderRatchetKey pq' (some c) c_fb x₁ =
                              fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w true none
                                h.senderRatchetKey pq' none c_fb x₁ := by
                            unfold fwdCPure
                            simp [hsafe]
                          rw [hplain_eq]
                          have hpres := fwdCPure_plain_deliver_eq_of_not_honest P ℓ Dh encPt encT
                            idOf lam qep Q w none h.senderRatchetKey pq' c_fb x₁ hsafe
                            (hx1_mir.symm ▸ hinv.hsim.hcomp) hc_fb_not_hon htriv₁
                            (by rw [hx1_mir]; dsimp only [c_fb]; omega)
                          unfold clearWin at hpres
                          rw [hpres.1, hpres.2]
                          exact ⟨s_R, ec, winBefore₁, hinv₁⟩
                    · have hwin := fwdCPure_of_win_true P ℓ Dh encPt encT idOf lam qep true Q w true
                        none h.senderRatchetKey pq' honestC c_mk x₁ (by rw [hx1_g]; exact hg_win)
                      dsimp only [r_out]
                      rw [hwin.1, hwin.2]
                      exact ⟨s_R, ec, winBefore₁, hinv₁⟩

theorem kemFailSimImpl_deliver_preserves_simInvCXLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q r' r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hr : r' < r)
    (Q : Party) (w : List (BitVec 8)) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false }
      ec winBefore epExp)
    (z : Option (SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false), tr))) :
    ∃ s_R' ec' winBefore',
      SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
        z.2.1 { z.2.2.1.1 with win := false } ec' winBefore' epExp := by
  have heq := kemFailSimImpl_deliver_eq_simRecvStepC P K ℓ Dh encPt encT decT idOf lam qep
    sC (g, false) tr Q w hz
  have hsC_eq : z.2.1 =
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.1 :=
    congrArg (·.2.1) heq
  have hg_eq : z.2.2.1.1 =
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.2.1 :=
    congrArg (·.2.2.1) heq
  rw [hsC_eq, hg_eq]
  exact simRecvStepC_deliver_preserves_simInvCXLazy P Inv ℓ Dh encPt encT decT idOf hinj hdec lam
    qep q r' r hS hr Q w x₀ s_R sC g ec winBefore epExp hinv

theorem simRecvStepC_deliver_epoch_cases_of_simInvCXLazy
    (P : Params (List (BitVec 8)) (BitVec 512))
    {InvPQ : ℕ → List (BitVec 8) → Prop} (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8))}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (hsim : SimInvCXLazy P InvPQ ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
      { gh.1 with win := false } ec winBefore epExp) :
    let s' := (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)).2.1.base
    s'.honest = sC.base.honest ∧
      (s'.mir.epoch = sC.base.mir.epoch ∨
        (inReceiveOnlyEpoch sC.base.mir Q = false ∧
         inReceiveOnlyEpoch s'.mir Q = true ∧
         s'.mir.epoch = Function.update sC.base.mir.epoch Q (sC.base.mir.epoch Q + 1))) := by
  obtain ⟨hhon, hmir_cases⟩ :=
    simRecvStepC_deliver_honest_and_mir P ℓ Dh encPt encT decT idOf lam qep Q w sC gh
  refine ⟨hhon, ?_⟩
  rcases hmir_cases with hmir | ⟨r_mir, htr_mir, hmir⟩
  · exact Or.inl (congrArg (·.epoch) hmir)
  · have hmir_mem : r_mir ∈ sC.base.mir.trans := List.mem_of_find?_eq_some htr_mir
    have hmir_pred := List.find?_some htr_mir
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmir_pred
    have hmap_mem :
        (r_mir.pos, w) ∈
          ({ gh.1 with win := false }).trans.map
            (fun r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) =>
              (r.pos, LibsignalSim.toWire r.ct)) := by
      rw [← hsim.hsim.hmeta.htrans_fig8, ← hmir_pred.2]
      exact List.mem_map_of_mem hmir_mem
    rw [List.mem_map] at hmap_mem
    rcases hmap_mem with ⟨r₀, hr₀, hpair₀⟩
    have hpos₀ : r₀.pos = r_mir.pos := congrArg Prod.fst hpair₀
    rcases hsim.hsim.htrans_hon r₀ hr₀ with ⟨hc_mem, hsender₀, hep₀, _⟩
    have hc_sender : Party.senderOf r₀.ct.1.1 = Q.other := by
      rw [← hsender₀, hpos₀, hmir_pred.1]
    have hpos_ep : r_mir.pos.epoch = r₀.ct.1.1 := by rw [← hpos₀, hep₀]
    have hc_le_other : r₀.ct.1.1 ≤ sC.base.mir.epoch Q.other := by
      have h1 := (hsim.hsim.hhon _ hc_mem).2.2.2
      rwa [hc_sender] at h1
    have hother_le : sC.base.mir.epoch Q.other ≤ sC.base.mir.epoch Q + 1 := by
      have h := (hsim.hsim.hep_adj Q.other).2; cases Q <;> exact h
    have hep_acc :
        (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)).2.1.base.mir.epoch =
          Function.update sC.base.mir.epoch Q (max (sC.base.mir.epoch Q) r_mir.pos.epoch) := by
      rw [hmir]; rfl
    by_cases hle : r_mir.pos.epoch ≤ sC.base.mir.epoch Q
    · refine Or.inl ?_
      rw [hep_acc, Nat.max_eq_left hle, Function.update_eq_self]
    · have heq_ep : r_mir.pos.epoch = sC.base.mir.epoch Q + 1 := by omega
      have hmax_eq : max (sC.base.mir.epoch Q) r_mir.pos.epoch = sC.base.mir.epoch Q + 1 := by
        omega
      have hsender_ep : Party.senderOf (sC.base.mir.epoch Q + 1) = Q.other := by
        rwa [← heq_ep, hpos_ep]
      have hinw_f : inReceiveOnlyEpoch sC.base.mir Q = false := by
        unfold inReceiveOnlyEpoch
        revert hsender_ep
        generalize sC.base.mir.epoch Q = n
        cases Q <;> unfold Party.senderOf Party.other Party.sendsIn <;>
          split <;> intro h <;> cases h <;> simp_all <;> omega
      have hinw_t :
          inReceiveOnlyEpoch
            (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)).2.1.base.mir Q =
            true := by
        unfold inReceiveOnlyEpoch
        rw [hep_acc, hmax_eq, Function.update_self]
        revert hsender_ep
        generalize sC.base.mir.epoch Q = n
        cases Q <;> unfold Party.senderOf Party.other Party.sendsIn <;>
          split <;> intro h <;> cases h <;> simp_all
      exact Or.inr ⟨hinw_f, hinw_t, by rw [hep_acc, hmax_eq]⟩

theorem simRecvStepC_deliver_preserves_evictedSpurHistGameInv_of_simInvCXLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    {InvPQ : ℕ → List (BitVec 8) → Prop} (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT) (lam : Pt)
    (qep q r w_rem : ℕ)
    (hInv_top : ∀ n st, InvPQ n st →
      ∃ w_top, CryptoVerification.SpqrV1Sync.SendTotal.TopStateW P.C.F K st w_top)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hEx : EvictedSpurSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r sC gh.1) :
    EvictedSpurHistGameInv P K qep w_rem
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, gh)).2.1 := by
  rcases hEx with ⟨x₀, s_R, ec, winBefore, epExp, hsim, _⟩
  unfold simRecvStepC simRecvStepCGen
  by_cases hst : sC.base.stopped = true
  · simp [hst, hInv]
  simp only [hst, Bool.false_eq_true, ↓reduceIte]
  by_cases hwin : sC.base.mir.win = true
  · simp [hwin, hInv]
  simp only [hwin, Bool.false_eq_true, ↓reduceIte]
  cases htr_mir : sC.base.mir.inTransit Q.other w with
  | none => simp [hInv]
  | some r_mir =>
    simp only [Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    rcases deliver_inTransit_mem hsim.hsim.hmeta
      (fun r hr => ⟨(hsim.hsim.htrans_hon r hr).1, (hsim.hsim.htrans_hon r hr).2.1⟩)
      Q w htr_mir with ⟨c, hc_mem, hc_sender⟩
    have hhonC := honestC_eq_some_of_memC P (InvB InvPQ q r) Dh encT hinj epExp
      (max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B)) sC.base hsim.huniq Q w c
      hc_mem hc_sender (fun wc hwc => ⟨(hsim.hsim.hhon wc hwc).1, (hsim.hsim.hhon wc hwc).2.1⟩)
      hsim.hsim.hcoll
    by_cases hlen : w.length < 9
    · simp [hlen, hInv]
    simp only [hlen, ↓reduceIte]
    cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
    | none => exact hInv
    | some hb =>
      rcases hb with ⟨h, body⟩
      dsimp only
      by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
      · simp [haddr, hInv]
      simp only [haddr, Bool.false_eq_true, ↓reduceIte]
      by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
      · simp [hpan, hInv]
      simp only [hpan, Bool.false_eq_true, ↓reduceIte]
      cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
      | error _ => exact hInv
      | ok ps =>
        rcases ps with ⟨pq', salt⟩
        dsimp only
        have hreach : Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (sC.base.pq Q) pq' :=
          .recv (.refl _) (hspqr_eq ▸ hspqr)
        rcases hsim.hsim.hpqInv Q with ⟨n_q, _, hInv_q⟩
        rcases hInv_top n_q (sC.base.pq Q) hInv_q with ⟨w_acc, hw_acc⟩
        cases hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
        | some ci =>
          dsimp only
          split
          · exact hInv
          · rcases fwdCPure_deliver_base_cases P ℓ Dh encPt encT idOf lam qep true Q w (some ci)
              h.senderRatchetKey pq' _ _ (sC, gh) with hbase_eq | ⟨i₁, m₁, hbase_eq⟩
            · exact evictedSpurHistGameInv_preserve_of_unchanged_pq_honest hInv
                (congrArg (·.honest) hbase_eq) (congrArg (·.pq) hbase_eq)
                (fun R t ht => by rwa [hbase_eq] at ht) (fun R => by rw [hbase_eq])
            · exact evictedSpurHistGameInv_deliver_existing_chain hInv hreach hbase_eq
                (fun R => hbase_eq ▸
                  onAcceptPure_epoch_le qep Q w true _ i₁ m₁ (some ci) h.senderRatchetKey pq'
                    sC.base R)
        | none =>
          dsimp only
          have hstop : sC.base.stopped = false := Bool.eq_false_iff.mpr hst
          have hs_stop : { sC.base with amb := sC.base.amb + 1, stopped := false } =
              { sC.base with amb := sC.base.amb + 1 } := by
            cases h_s : sC.base; rw [h_s] at hstop; subst hstop; rfl
          simp only [hs_stop]
          let x₁ : JointC (List (BitVec 8)) Pt ℓ :=
            if inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
              ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, gh)
            else (sC, gh)
          have hx1 : x₁.1.base.honest = sC.base.honest ∧ x₁.1.base.pq = sC.base.pq ∧
              x₁.1.base.chains = sC.base.chains ∧ x₁.1.base.mir = sC.base.mir := by
            dsimp only [x₁]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
          have hInv₁ : EvictedSpurHistGameInv P K qep w_rem x₁.1 :=
            evictedSpurHistGameInv_preserve_of_unchanged_pq_honest hInv hx1.1 hx1.2.1
              (fun R t ht => by rwa [hx1.2.2.1] at ht) (fun R => by rw [hx1.2.2.2])
          split
          · exact hInv
          · split
            · exact hInv
            · split
              · exact hInv₁
              · cases hT : decT h.senderRatchetKey with
                | none => dsimp only; exact hInv₁
                | some T =>
                  dsimp only
                  let c_fb : Fig8C Pt :=
                    ((sC.base.mir.epoch Q + 1, some T),
                      (h.counter.toNat + 1,
                        ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
                  split
                  · rename_i hev_true
                    have hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1 := by
                      change (((sC.base.honest.find? fun wc =>
                          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                        fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true at hev_true
                      rw [hhonC] at hev_true
                      simpa using hev_true
                    have hc_fb_not_hon : ∀ wc ∈ x₁.1.base.honest, wc.2 ≠ c_fb := by
                      intro wc hwc heq
                      rw [hx1.1] at hwc
                      have hwc1 : wc.1 = w := by
                        rw [(hsim.hsim.hhon wc hwc).1.1, heq]
                        exact toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T)
                          (h.counter.toNat + 1) (effectiveHkdfSalt32 salt)
                      have hwc_mem : (w, c_fb) ∈ sC.base.honest := by
                        rwa [← hwc1, ← heq]
                      have hc_eq := honestEntryInvC_unique P (InvB InvPQ q r) Dh encT hinj epExp
                        sC.base hsim.huniq hc_mem hwc_mem (hsim.hsim.hhon (w, c) hc_mem).1
                        (hsim.hsim.hhon (w, c_fb) hwc_mem).1
                        (hsim.hsim.hcoll c.1.1 c_fb.1.1 (hsim.hsim.hhon (w, c) hc_mem).2.1
                          (hsim.hsim.hhon (w, c_fb) hwc_mem).2.1)
                      exact hepoch (congrArg (fun x : Fig8C Pt => x.1.1) hc_eq)
                    have htriv₁ : ∀ pos, x₁.2.1.trivial 3 pos = x₁.1.base.mir.trivial 3 pos := by
                      intro pos
                      have hmeta_triv := hsim.hsim.hmeta.trivial_fig8 3 pos
                      have hx1_g : x₁.2.1 = gh.1 := by dsimp only [x₁]; split <;> rfl
                      rw [hx1_g, hx1.2.2.2]
                      exact hmeta_triv
                    have hev := fwdEvictCPure_deliver_eq_of_not_honest P ℓ Dh encPt encT idOf lam
                      qep true Q w h.senderRatchetKey pq' c_fb x₁ (fun h => by cases h)
                      (hx1.2.2.2.symm ▸ hsim.hsim.hcomp) hc_fb_not_hon htriv₁
                      (by rw [hx1.2.2.2]; dsimp only [c_fb]; omega)
                    change EvictedSpurHistGameInv P K qep w_rem
                      (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep true Q w true h.senderRatchetKey
                        pq' c_fb x₁).2.1
                    rw [hev.1]
                    exact hInv₁
                  · rename_i hev_false
                    have hepoch : c.1.1 = sC.base.mir.epoch Q + 1 := by
                      change ¬((((sC.base.honest.find? fun wc =>
                          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                        fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
                        at hev_false
                      rw [hhonC] at hev_false
                      simp only [Option.map_some, beq_iff_eq, Option.some.injEq,
                        decide_eq_true_eq, not_ne_iff] at hev_false
                      exact hev_false
                    let honestC := (sC.base.honest.find? fun wc =>
                      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
                    let c_mk : Fig8C Pt :=
                      match honestC with
                      | some c₀ => if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀ else c_fb
                      | none => c_fb
                    have hc_mk_ep : c_mk.1.1 = c.1.1 := by
                      dsimp only [c_mk, honestC]
                      rw [hhonC]
                      dsimp only
                      split
                      · rfl
                      · exact hepoch.symm
                    change EvictedSpurHistGameInv P K qep w_rem
                      (fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w true none h.senderRatchetKey
                        pq' honestC c_mk x₁).2.1
                    rcases fwdCPure_deliver_base_cases P ℓ Dh encPt encT idOf lam qep true Q w none
                        h.senderRatchetKey pq' honestC c_mk x₁ with hbase_eq | ⟨i₁, m₁, hbase_eq⟩
                    · exact evictedSpurHistGameInv_preserve_of_unchanged_pq_honest hInv₁
                        (congrArg (·.honest) hbase_eq) (congrArg (·.pq) hbase_eq)
                        (fun R t ht => by rwa [hbase_eq] at ht) (fun R => by rw [hbase_eq])
                    · exact evictedSpurHistGameInv_deliver_new_chain hInv₁ (hx1.1.symm ▸ hc_mem)
                        hc_mk_ep hc_sender hparse (hx1.2.1.symm ▸ hw_acc)
                        (hx1.2.1.symm ▸ hspqr_eq ▸ hspqr) hbase_eq
                        (fun R => hbase_eq ▸
                          onAcceptPure_epoch_le qep Q w true _ i₁ m₁ none h.senderRatchetKey pq'
                            x₁.1.base R)

omit [DecidableEq Pt] [SampleableType Pt] in
theorem validSpurBase_of_inWin_false_and_root_eq {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    {P : Params PQ PQC} {Inv : PQ → Prop} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r' : ℕ}
    {x₀ : BitVec 256}
    {s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s s' : SimState PQ Pt ℓ}
    {s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec' : Party → BitVec 256} {winBefore' : ℕ → Bool} {epExp : ℕ → BitVec 256}
    {R : Party} {rk_base : Ratchet.RootKey} {T_base : Pt}
    (hsim' : SimInvCLazy P Inv ℓ Dh encPt encT qep q r' x₀ s_R' s' s_fig8' ec' winBefore' epExp)
    (hbase : ValidSpurBase P ℓ Dh encPt s s_fig8 epExp R rk_base T_base)
    (hinw : inReceiveOnlyEpoch s.mir R = false)
    (hinw' : inReceiveOnlyEpoch s'.mir R = false)
    (hep : s'.mir.epoch R = s.mir.epoch R)
    (hroot : (s_fig8'.st R).root = (s_fig8.st R).root) :
    ValidSpurBase P ℓ Dh encPt s' s_fig8' epExp R rk_base T_base := by
  rcases hsim'.hspur R with ⟨_, _, _, hinw_f'⟩
  rcases hinw_f' hinw' with ⟨hγ', hpos', hvS'⟩
  refine ⟨fun h => (by rw [hinw'] at h; cases h), fun _ => ⟨hγ', fun h0 => ?_, hvS'⟩⟩
  have hpos0 := hpos' h0
  rw [hroot, hep] at hpos0 ⊢
  exact ⟨((hbase.2 hinw).2.1 (hep ▸ h0)).1, hpos0.2⟩

omit [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurSimInvLazy_party_of_inWin_true
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem}
    {InvPQ : ℕ → List (BitVec 8) → Prop}
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r' : ℕ}
    {x₀ : BitVec 256}
    {s_R' : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8))}
    {sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {g' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec' : Party → BitVec 256} {winBefore' : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hhist' : Proofs.Refinement.SpqrHistoryInv P K sC'.base)
    (hsim' : SimInvCXLazy P InvPQ ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
      sC' { g' with win := false } ec' winBefore' epExp)
    (R : Party) (hinw' : inReceiveOnlyEpoch sC'.base.mir R = true) :
    ∃ w_acc rk_base T_base,
      ValidEvictAccWitness P K sC'.base R w_acc ∧
      ValidSpurBase P ℓ Dh encPt sC'.base { g' with win := false } epExp R rk_base T_base ∧
      (inReceiveOnlyEpoch sC'.base.mir R = false →
        spurBadList P encPt Dh R rk_base T_base
          (Proofs.Refinement.evictedSpurCandList P epExp w_acc
            (Proofs.Refinement.honestBeforeEpoch sC'.base.honest
              (Proofs.Refinement.evictAccEpoch sC'.base.mir R)))
          (epExp (sC'.base.mir.epoch R)) = false) := by
  rcases hsim'.hsim.hspur R with ⟨rk_base, T_base, hinw_t, hinw_f⟩
  have hbase : ValidSpurBase P ℓ Dh encPt sC'.base { g' with win := false } epExp R
      rk_base T_base :=
    ⟨fun h => ⟨(hinw_t h).1, (hinw_t h).2.1, (hinw_t h).2.2.1⟩, hinw_f⟩
  have hvac : ∀ w_acc,
      inReceiveOnlyEpoch sC'.base.mir R = false →
        spurBadList P encPt Dh R rk_base T_base
          (Proofs.Refinement.evictedSpurCandList P epExp w_acc
            (Proofs.Refinement.honestBeforeEpoch sC'.base.honest
              (Proofs.Refinement.evictAccEpoch sC'.base.mir R)))
          (epExp (sC'.base.mir.epoch R)) = false := by
    intro _ h; rw [hinw'] at h; cases h
  by_cases hact : 1 ≤ Proofs.Refinement.evictAccEpoch sC'.base.mir R
  · have hmem_ch := mem_chains_evictAccEpoch_of_simInvCLazy hsim'.hsim R hact
    obtain ⟨w_acc_wire, c_acc, h_acc, body_acc, pq_acc, pq_acc', salt_acc, w_acc,
        hc_acc_mem, hc_acc_eq, hc_acc_sender, hparse_acc, hw_acc, hrecv_acc, hreach₀⟩ :=
      hhist'.hchain_acc R (Proofs.Refinement.evictAccEpoch sC'.base.mir R) hmem_ch hact
    exact ⟨w_acc, rk_base, T_base, fun _ => ⟨w_acc_wire, c_acc, h_acc, body_acc, pq_acc, pq_acc',
      salt_acc, hc_acc_mem, hc_acc_eq, hc_acc_sender, hparse_acc, hw_acc, hrecv_acc, hreach₀⟩,
      hbase, hvac w_acc⟩
  · have ⟨n, _, hI⟩ : ∃ n, n + r' ≤ q ∧ InvPQ n (sC'.base.pq R) := hsim'.hsim.hpqInv R
    obtain ⟨w_top, _⟩ := hInv_top n _ hI
    exact ⟨w_top, rk_base, T_base, fun hge => absurd hge hact, hbase, hvac w_top⟩

omit [DecidableEq Pt] [SampleableType Pt] in
theorem evictedSpurSimInvLazy_of_step
    {P : Params (List (BitVec 8)) (BitVec 512)} {K : MlKem}
    {InvPQ : ℕ → List (BitVec 8) → Prop}
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r' : ℕ}
    {x₀ : BitVec 256}
    {s_R' : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8))}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ}
    {g g' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec' : Party → BitVec 256} {winBefore' : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hhist' : Proofs.Refinement.SpqrHistoryInv P K sC'.base)
    (hsim' : SimInvCXLazy P InvPQ ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
      sC' { g' with win := false } ec' winBefore' epExp)
    (hspur_lazy : ∀ R, ∃ w_acc rk_base T_base,
      ValidEvictAccWitness P K sC.base R w_acc ∧
      ValidSpurBase P ℓ Dh encPt sC.base { g with win := false } epExp R rk_base T_base ∧
      (inReceiveOnlyEpoch sC.base.mir R = false →
        spurBadList P encPt Dh R rk_base T_base
          (Proofs.Refinement.evictedSpurCandList P epExp w_acc
            (Proofs.Refinement.honestBeforeEpoch sC.base.honest
              (Proofs.Refinement.evictAccEpoch sC.base.mir R)))
          (epExp (sC.base.mir.epoch R)) = false))
    (hpres : ∀ R, inReceiveOnlyEpoch sC'.base.mir R = false →
      sC'.base.mir.epoch R = sC.base.mir.epoch R ∧
      (∀ wc ∈ sC.base.honest, wc ∈ sC'.base.honest) ∧
      Proofs.Refinement.honestBeforeEpoch sC'.base.honest
        (Proofs.Refinement.evictAccEpoch sC'.base.mir R) =
      Proofs.Refinement.honestBeforeEpoch sC.base.honest
        (Proofs.Refinement.evictAccEpoch sC.base.mir R) ∧
      Corr.SpqrReachFrom (spqrV1SessionUniformCoins P.C.F K) (sC.base.pq R) (sC'.base.pq R) ∧
      (∀ rk_b T_b,
        ValidSpurBase P ℓ Dh encPt sC.base { g with win := false } epExp R rk_b T_b →
        ValidSpurBase P ℓ Dh encPt sC'.base { g' with win := false } epExp R rk_b T_b)) :
    EvictedSpurSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r' sC' g' := by
  refine ⟨x₀, s_R', ec', winBefore', epExp, hsim', fun R => ?_⟩
  by_cases hinw' : inReceiveOnlyEpoch sC'.base.mir R = false
  · obtain ⟨hep, hhon_sub, hhon_before, hreach, hbase_pres⟩ := hpres R hinw'
    have hinw : inReceiveOnlyEpoch sC.base.mir R = false := by
      unfold inReceiveOnlyEpoch at hinw' ⊢; rwa [hep] at hinw'
    have hev_eq : Proofs.Refinement.evictAccEpoch sC'.base.mir R =
        Proofs.Refinement.evictAccEpoch sC.base.mir R := by
      unfold Proofs.Refinement.evictAccEpoch; rw [hinw', hinw, hep]
    obtain ⟨w_acc, rk_base, T_base, hw_acc, hbase, hno_spur⟩ := hspur_lazy R
    refine ⟨w_acc, rk_base, T_base, ?_, hbase_pres rk_base T_base hbase, fun _ => ?_⟩
    · intro hge
      rw [hev_eq] at hge ⊢
      obtain ⟨w_acc_wire, c_acc, h_acc, body_acc, pq_acc, pq_acc', salt_acc,
          hc_mem, hc_eq, hc_sender, hparse_acc, hw_top_a, hrecv_acc, hreach₀⟩ := hw_acc hge
      exact ⟨w_acc_wire, c_acc, h_acc, body_acc, pq_acc, pq_acc', salt_acc,
        hhon_sub _ hc_mem, hc_eq, hc_sender, hparse_acc, hw_top_a, hrecv_acc,
        Proofs.Refinement.spqrReachFrom_trans hreach₀ hreach⟩
    · rw [hhon_before, hep]
      exact hno_spur hinw
  · exact evictedSpurSimInvLazy_party_of_inWin_true hInv_top hhist' hsim' R
      (Bool.eq_true_of_not_eq_false hinw')

theorem simCorrPureC_preserves_simInvCLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r' r : ℕ) (hr : r' ≤ r)
    (Q : Party) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore
      epExp)
    (hguard_f :
      (!(sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) =
        false) :
    let s := sC.base
    let figSt := s_fig8.st Q
    let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match figSt.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    let s' : SimState (List (BitVec 8)) Pt ℓ :=
      { s with mir := s.mir.afterCorr Q, chains := chains }
    SimInvCLazy P (InvB Inv q r') ℓ Dh encPt encT qep q r' x₀ (s_R.afterCorr Q) s'
      (s_fig8.afterCorr Q) ec winBefore epExp := by
  intro s figSt chains s'
  have hcorr_mir : s.mir.corrAllowed Q = true := by
    revert hguard_f; cases s.mir.corrAllowed Q <;> simp
  have hinw_mir : inReceiveOnlyEpoch s.mir Q = false := by
    revert hguard_f; cases inReceiveOnlyEpoch s.mir Q <;> simp
  have hB0 : Q = .B → s.mir.epoch .B = 0 → figSt.γ = .exp x₀ := by
    intro hQB hep0
    subst hQB
    rcases hinv.hsim.hspur .B with ⟨_, _, _, hnot_inw⟩
    have hγ := (hnot_inw hinw_mir).1
    rw [hep0, hinv.hsim.hepExp0] at hγ
    exact hγ
  have hres_eq : resolveSim (encT (Dh.dh x₀ Dh.base)) s' =
      { resolveSim (encT (Dh.dh x₀ Dh.base)) s with mir := s.mir.afterCorr Q } :=
    resolveSim_afterCorr_B_epoch0 Dh encT (encT (Dh.dh x₀ Dh.base)) s Q figSt x₀ rfl hB0
  have hchains_ep : ∀ R, (chains R).map (·.epoch) = (s.chains R).map (·.epoch) := by
    intro R
    dsimp only [chains]
    split
    · cases figSt.γ with
      | pub _ => rfl
      | exp x =>
        dsimp only
        cases R with
        | A =>
          rw [Function.update_self]
          exact c8_map_epoch_resolve_list (s.chains .A) (encT (Dh.dh x Dh.base))
        | B =>
          rw [Function.update_of_ne (by decide : Party.B ≠ Party.A)]
    · rfl
  exact
    { hmeta := hinv.hsim.hmeta.afterCorr_preserves Q chains
      hcomp := comp_healedBy_false_afterCorr s.mir 3 Q hcorr_mir hinv.hsim.hcomp
      hec := hinv.hsim.hec
      hwinBefore := hinv.hsim.hwinBefore
      hamb := by have := hinv.hsim.hamb; dsimp [s', s]; omega
      hamb_strict := fun h => by have := hinv.hsim.hamb_strict h; dsimp [s', s]; omega
      hidx_le := fun R => by
        change sC.base.mir.idx R + r' ≤ q
        have := hinv.hsim.hidx_le R; omega
      hhon_len := by have := hinv.hsim.hhon_len; dsimp [s', s]; omega
      hep_le := hinv.hsim.hep_le
      hep_adj := hinv.hsim.hep_adj
      hst_R := by
        intro R
        change s_R.st R =
          expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' R (s_fig8.st R) (ec R)
        rw [hinv.hsim.hst_R R]
        refine c8_expectedGhost_congr P Dh encPt (encT (Dh.dh x₀ Dh.base)) s s' R
          (s_fig8.st R) (ec R) rfl ?_ (fun _ => rfl) rfl rfl rfl
        rw [hres_eq]
      hst_id := hinv.hsim.hst_id
      htcur := hinv.hsim.htcur
      hepExp0 := hinv.hsim.hepExp0
      hspur := hinv.hsim.hspur
      hchainsA := by
        dsimp only [s', chains]
        split
        · cases figSt.γ with
          | pub _ => exact hinv.hsim.hchainsA
          | exp x =>
            dsimp only
            rw [Function.update_self]
            exact chainsEpochInvA_resolve hinv.hsim.hchainsA (encT (Dh.dh x Dh.base))
        · exact hinv.hsim.hchainsA
      hchainsA_ep := by
        change (chains .A).map (·.epoch) = epListA (s.mir.epoch .A / 2)
        rw [hchains_ep .A]
        exact hinv.hsim.hchainsA_ep
      hchainsB_ep := by
        change (chains .B).map (·.epoch) = epListB ((s.mir.epoch .B + 1) / 2)
        rw [hchains_ep .B]
        exact hinv.hsim.hchainsB_ep
      hchainsB_none := by
        have hB : chains .B = s.chains .B := by
          dsimp only [chains]
          split
          · cases figSt.γ with
            | pub _ => rfl
            | exp _ => simp
          · rfl
        dsimp only [s']
        rw [hB]
        exact hinv.hsim.hchainsB_none
      hchains_sync := by
        intro R g' hg'
        by_cases hcond : (Q == Party.B && s.mir.epoch Party.B == 0) = true
        · simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          rcases hcond with ⟨hQB, hep0⟩
          have hγ0 : figSt.γ = .exp x₀ := hB0 hQB hep0
          have hchains_eq : chains = Function.update s.chains Party.A ((s.chains Party.A).map
              fun g => if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) }
                else g) := by
            simp [chains, hQB, hep0, hγ0]
          cases R with
          | B =>
            change g' ∈ chains .B at hg'
            rw [hchains_eq, Function.update_of_ne (by decide : Party.B ≠ Party.A)] at hg'
            exact hinv.hsim.hchains_sync .B g' hg'
          | A =>
            change g' ∈ chains .A at hg'
            rw [hchains_eq, Function.update_self, List.mem_map] at hg'
            rcases hg' with ⟨g, hg, rfl⟩
            rcases hinv.hsim.hchains_sync .A g hg with ⟨hgep, hgsend, hgkey, v, hvR, hsync⟩
            have heq_ep :
                (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) }
                  else g).epoch = g.epoch := by split <;> rfl
            have heq_key :
                (if (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) }
                    else g).key.isNone then
                  some (encT (Dh.dh x₀ Dh.base))
                else (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) }
                    else g).key) =
                (if g.key.isNone then some (encT (Dh.dh x₀ Dh.base)) else g.key) := by
              cases hk : g.key <;> simp [hk]
            have hsync' :
                ChainSync (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) }
                  else g) v := by
              split
              · exact ⟨hsync.last_eq, hsync.last_lt, hsync.nodup_skipped,
                  hsync.len_skipped, hsync.mem_skipped, hsync.skippedKeys_le⟩
              · exact hsync
            rw [heq_ep, heq_key]
            exact ⟨hgep, hgsend, hgkey, v, hvR, hsync'⟩
        · have hchains_eq : chains = s.chains := ite_eq_right hcond
          change g' ∈ chains R at hg'
          rw [hchains_eq] at hg'
          exact hinv.hsim.hchains_sync R g' hg'
      hhon := hinv.hsim.hhon
      htrans_hon := hinv.hsim.htrans_hon
      hcoll := hinv.hsim.hcoll
      hcorrB0 := hcorrB0_afterCorr hB0 hinv.hsim.hcorrB0
      hpqInv := fun R => InvB.mono hr (hinv.hsim.hpqInv R) }

theorem simCorrPureC_preserves_simInvCXLazy_of_guard_false
    (P : Params (List (BitVec 8)) (BitVec 512)) (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r' r : ℕ) (hq32 : q < 2 ^ 32) (hr : r' ≤ r)
    (Q : Party) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore
      epExp)
    (hguard_f :
      (!(sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) =
        false) :
    let s := sC.base
    let figSt := s_fig8.st Q
    let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match figSt.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    let g_snap := toGhost (P := P) { s with chains := chains } Q figSt
    let s' : SimState (List (BitVec 8)) Pt ℓ :=
      { s with mir := s.mir.afterCorr Q, chains := chains }
    let sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
      { sC with base := s',
                kept := Function.update sC.kept Q (Kept.ofSt figSt),
                snaps := (Q, s.mir.epoch Q, g_snap) :: sC.snaps }
    SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ (s_R.afterCorr Q) sC'
      (s_fig8.afterCorr Q) ec winBefore epExp := by
  intro s figSt chains g_snap s' sC'
  have hinw_mir : inReceiveOnlyEpoch s.mir Q = false := by
    revert hguard_f; cases inReceiveOnlyEpoch s.mir Q <;> simp
  have hnospk_mir : SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q = true := by
    revert hguard_f; cases SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q <;> simp
  refine ⟨simCorrPureC_preserves_simInvCLazy P Inv ℓ Dh encPt encT idOf lam qep q r' r hr Q x₀ s_R
      sC s_fig8 ec winBefore epExp hinv hguard_f,
    hinv.huniq,
    c8_keptInv_corr P Dh encPt encT idOf lam Q sC s' ((Q, s.mir.epoch Q, g_snap) :: sC.snaps)
      s_fig8 hinv.hkept rfl (fun _ _ => rfl),
    hinv.hidx, ?_⟩
  intro hwin'
  rcases hinv.hsync hwin' with ⟨K, rk, hK⟩
  refine ⟨K, rk, { hK with hsnaps := ?_ }⟩
  intro snap hsnap
  rcases List.mem_cons.mp hsnap with rfl | hsnap
  · have hsends_Q : Q.sendsIn (s.mir.epoch Q) = true := by
      unfold inReceiveOnlyEpoch at hinw_mir
      simpa using hinw_mir
    have hchains_Q : chains Q = s.chains Q := by
      cases Q with
      | A => dsimp [chains]
      | B =>
        dsimp [chains]
        split
        · cases figSt.γ with
          | pub _ => rfl
          | exp _ => simp
        · rfl
    have hno_none_Q : ∀ g ∈ s.chains Q, g.key.isNone = false := by
      cases Q with
      | B => exact hinv.hsim.hchainsB_none
      | A =>
        have h10 : 10 ≤ s.mir.epoch .A := by
          unfold SM.noAliceCorrWhileAliceBelowEpoch10 at hnospk_mir
          simpa using hnospk_mir
        exact chainsEpochInvA_no_none hinv.hsim.hchainsA h10
    rcases hinv.hsim.hspur Q with ⟨rk_base, T_base, _, hnot_inw⟩
    rcases hnot_inw hinw_mir with ⟨hγ_Q, _, vS, hvS, _⟩
    have hidx_Q_lt : vS.lastIndex < 2 ^ 32 := by
      have := hinv.hsim.hidx_le Q
      omega
    have hsend_Q : vS.chainKey = lChainAt P.C.F (K (s.mir.epoch Q)) vS.lastIndex := by
      have h := hK.hsend Q vS hvS (by rw [hinv.hsim.htcur Q]; exact hsends_Q)
      rwa [hinv.hsim.htcur Q] at h
    refine ⟨hsends_Q, ?_, ?_, ?_, ?_, ?_⟩
    · change s.mir.epoch Q ≤ max (s_fig8.st .A).tcur (s_fig8.st .B).tcur
      rw [hinv.hsim.htcur .A, hinv.hsim.htcur .B]
      cases Q with
      | A => exact Nat.le_max_left _ _
      | B => exact Nat.le_max_right _ _
    · change figSt.root = rk (s.mir.epoch Q)
      rw [← hinv.hsim.htcur Q]
      exact hK.hroot Q
    · refine ⟨vS.lastIndex, hidx_Q_lt, ?_⟩
      dsimp only [g_snap, toGhost, figSt, s]
      rw [hγ_Q, hvS]
      dsimp only
      rw [hsend_Q]
    · intro rc_ch hrc_ch
      dsimp only [g_snap, toGhost] at hrc_ch
      rw [hchains_Q, List.mem_map] at hrc_ch
      rcases hrc_ch with ⟨g, hg, rfl⟩
      rcases hinv.hsim.hchains_sync Q g hg with ⟨hgep, _, hgkey, v, hvR, hsync_g⟩
      have hnone_g : g.key.isNone = false := hno_none_Q g hg
      rw [hnone_g, ite_eq_right Bool.false_ne_true] at hgkey
      rcases hK.hrecv Q g.epoch v hvR with ⟨hv_ck, hv_sk⟩
      change ∃ ep ≤ s.mir.epoch Q, _
      refine ⟨g.epoch, hgep, ?_, ?_, ?_⟩
      · dsimp only [figSt]
        rw [hvR, hgkey]
        rfl
      · refine ⟨v.lastIndex, hsync_g.last_lt, ?_⟩
        dsimp only [figSt]
        rw [hvR]
        dsimp only
        rw [hv_ck]
      · intro mk hmk
        dsimp only [figSt] at hmk
        rw [hvR] at hmk
        dsimp only at hmk
        rw [List.mem_filterMap] at hmk
        rcases hmk with ⟨j, hj, hmap_j⟩
        cases hlk : v.skippedKeys.lookup j with
        | none => rw [hlk] at hmap_j; cases hmap_j
        | some seed =>
          rw [hlk, Option.map_some, Option.some.injEq] at hmap_j
          subst hmap_j
          dsimp only
          rcases hsync_g.mem_skipped j hj with ⟨hj1, hj_le, _⟩
          have hj_lt : j - 1 < 2 ^ 32 := by have := hsync_g.last_lt; omega
          have hctr : (BitVec.ofNat 32 (j - 1)).toNat + 1 = j := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj_lt]
            omega
          have hseed : seed = lSeedAt P.C.F (K g.epoch) j :=
            hv_sk (j, seed) (c8_mem_of_lookup hlk)
          rw [hctr, hseed]
    · intro h2
      have h2' : 2 ≤ sC.base.mir.epoch Q := h2
      have hlast_ep : ((s.chains Q).map (·.epoch)).getLast? = some (s.mir.epoch Q - 1) := by
        dsimp only [s]
        cases Q with
        | A =>
          rw [hinv.hsim.hchainsA_ep, c8_epListA_getLast]
          congr 1
          have hmod : sC.base.mir.epoch .A % 2 = 1 := by
            simpa [Party.sendsIn, s] using hsends_Q
          omega
        | B =>
          have hmod : sC.base.mir.epoch .B % 2 = 0 := by
            simpa [Party.sendsIn, s] using hsends_Q
          rw [hinv.hsim.hchainsB_ep, c8_epListB_getLast (by omega)]
          congr 1
          omega
      rw [List.getLast?_map, Option.map_eq_some_iff] at hlast_ep
      rcases hlast_ep with ⟨g_last, hglast, hg_ep⟩
      have hmem_last : g_last ∈ s.chains Q := List.mem_of_getLast? hglast
      rcases hinv.hsim.hchains_sync Q g_last hmem_last with
        ⟨_, _, hgkey_last, v_last, hvR_last, _⟩
      have hnone_last : g_last.key.isNone = false := hno_none_Q g_last hmem_last
      rw [hnone_last, ite_eq_right Bool.false_ne_true, hg_ep] at hgkey_last
      dsimp only [g_snap, toGhost, figSt]
      rw [hchains_Q, List.getLast?_map, hglast, Option.map_some]
      refine ⟨_, rfl, ?_⟩
      rw [hvR_last]
      dsimp only
      rw [hgkey_last]
      rfl
  · exact hK.hsnaps snap hsnap

theorem kemFailSimImpl_corr_preserves_simInvCXLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r' r : ℕ) (hq32 : q < 2 ^ 32) (hr : r' ≤ r)
    (Q : Party) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false }
      ec winBefore epExp)
    (z : Option (GhostState (List (BitVec 8))) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q))).run (sC, (g, false), tr))) :
    z.2.1.base.honest = sC.base.honest ∧
    z.2.1.base.mir.epoch = sC.base.mir.epoch ∧
    z.2.1.base.pq = sC.base.pq ∧
    z.2.2.1.1.st = g.st ∧
    ∃ s_R' ec' winBefore',
      SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
        z.2.1 { z.2.2.1.1 with win := false } ec' winBefore' epExp := by
  change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q))).run
    (sC, (g, false), tr)) at hz
  rw [runProbeStep_run, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hw_step : (w.1.1, (w.1.2, w.2)) ∈ support
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) (sC, (g, false))) := by
    change (w.1.1, (w.1.2, w.2)) ∈ support
      ((((LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q)).run
        sC).run (g, false)) >>= fun r => pure (r.1.1, (r.1.2, r.2)))
    rw [MonadAttach.mem_support_bind]
    exact ⟨w, hw, by simp⟩
  rw [c8_stepSimCNone_corr_eq, support_pure, Set.mem_singleton_iff] at hw_step
  have hstop := hinv.hsim.hmeta.hstop
  have hwin_mir := hinv.hsim.hmeta.hwin_mir
  by_cases hguard :
      (!(sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) =
        true
  · have hcorr_eq : c8_simCorrPureC P Dh encT Q (sC, (g, false)) = (none, (sC, (g, false))) := by
      unfold c8_simCorrPureC
      dsimp only
      rw [hstop, ite_eq_right Bool.false_ne_true, hwin_mir, Bool.false_or, hguard,
        ite_eq_left rfl]
    rw [hcorr_eq] at hw_step
    have hsC_eq : w.1.2 = sC := congrArg (·.2.1) hw_step
    have hg_eq : w.2.1 = g := congrArg (·.2.2.1) hw_step
    dsimp only
    rw [hsC_eq, hg_eq]
    exact ⟨rfl, rfl, rfl, rfl, s_R, ec, winBefore, simInvCXLazy_mono_r hinv hr⟩
  · have hguard_f :
        (!(sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) =
          false := Bool.eq_false_iff.mpr hguard
    cases hg_win : g.win
    · have hg_eq0 : { g with win := false } = g := by cases g; simp_all
      rw [hg_eq0] at hinv
      have hcorr_fig8 := hinv.hsim.hmeta.corrAllowed_fig8 Q
      have hcorr_mir : sC.base.mir.corrAllowed Q = true := by
        revert hguard_f; cases sC.base.mir.corrAllowed Q <;> simp
      have hcorrPure_fig8 : corrPure Q g = (some (g.st Q), g.afterCorr Q) := by
        unfold corrPure
        rw [hg_win, hcorr_fig8, hcorr_mir]
        rfl
      have hcorr_eq : (c8_simCorrPureC P Dh encT Q (sC, (g, false))).2 =
          (let s := sC.base
           let figSt := g.st Q
           let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
               match figSt.γ with
               | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
                   if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
               | _ => s.chains
             else s.chains
           let g_snap := toGhost (P := P) { s with chains := chains } Q figSt
           ({ sC with base := { s with mir := s.mir.afterCorr Q, chains := chains },
                      kept := Function.update sC.kept Q (Kept.ofSt figSt),
                      snaps := (Q, s.mir.epoch Q, g_snap) :: sC.snaps },
            g.afterCorr Q, false)) := by
        unfold c8_simCorrPureC
        dsimp only
        rw [hstop, ite_eq_right Bool.false_ne_true, hwin_mir, Bool.false_or, hguard_f,
          ite_eq_right Bool.false_ne_true, hcorrPure_fig8]
        rfl
      have hsC_eq : w.1.2 = (c8_simCorrPureC P Dh encT Q (sC, (g, false))).2.1 :=
        congrArg (·.2.1) hw_step
      have hg_eq : w.2.1 = (c8_simCorrPureC P Dh encT Q (sC, (g, false))).2.2.1 :=
        congrArg (·.2.2.1) hw_step
      have hg_after_eq : { g.afterCorr Q with win := false } = g.afterCorr Q := by
        unfold SM.GameState.afterCorr SM.GameState.leak; cases g; simp_all
      dsimp only
      rw [hsC_eq, hg_eq, hcorr_eq, hg_after_eq]
      exact ⟨rfl, rfl, rfl, rfl, s_R.afterCorr Q, ec, winBefore,
        simCorrPureC_preserves_simInvCXLazy_of_guard_false P Inv ℓ Dh encPt encT idOf lam qep q r' r
          hq32 hr Q x₀ s_R sC g ec winBefore epExp hinv hguard_f⟩
    · have hcorrPure_fig8 : corrPure Q g = (none, g) := by
        unfold corrPure
        rw [hg_win]
        rfl
      have hcorr_eq : c8_simCorrPureC P Dh encT Q (sC, (g, false)) = (none, (sC, (g, false))) := by
        unfold c8_simCorrPureC
        dsimp only
        rw [hstop, ite_eq_right Bool.false_ne_true, hwin_mir, Bool.false_or, hguard_f,
          ite_eq_right Bool.false_ne_true, hcorrPure_fig8]
      rw [hcorr_eq] at hw_step
      have hsC_eq : w.1.2 = sC := congrArg (·.2.1) hw_step
      have hg_eq : w.2.1 = g := congrArg (·.2.2.1) hw_step
      dsimp only
      rw [hsC_eq, hg_eq]
      exact ⟨rfl, rfl, rfl, rfl, s_R, ec, winBefore, simInvCXLazy_mono_r hinv hr⟩

/-- `corr` queries of `kemFailSimImpl` preserve `EvictedSpurHistSimInvLazy` with probe flag `false`. -/
theorem evictedSpurHistSimInvLazy_corr_step
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r' r w_rem : ℕ)
    (hq32 : q < 2 ^ 32) (hr : r' ≤ r)
    (Q : Party) (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g)
    (z : Option (GhostState (List (BitVec 8))) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q))).run (sC, (g, false), tr)))
    (_hcand : z.2.2.2.cand = none) :
    z.2.2.1.2 = false ∧
    EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r' w_rem
      z.2.1 z.2.2.1.1 := by
  have hfl := kemFailSimImpl_corr_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep Q sC g tr z hz
  have hgame' := kemFailSimImpl_corr_preserves_evictedSpurHistGameInv P K ℓ Dh encPt encT decT idOf
    lam qep w_rem Q sC (g, false) tr hInv.1 z hz
  rcases hInv.2 with ⟨x₀, s_R, ec, winBefore, epExp, hsim, hspur_lazy⟩
  obtain ⟨hhon, hep, hpq, hst, s_R', ec', winBefore', hsim'⟩ :=
    kemFailSimImpl_corr_preserves_simInvCXLazy P K InvPQ ℓ Dh encPt encT decT idOf lam qep q r' r
      hq32 hr Q x₀ s_R sC g tr ec winBefore epExp hsim z hz
  refine ⟨hfl, hgame', evictedSpurSimInvLazy_of_step hInv_top hgame'.hhist hsim' hspur_lazy ?_⟩
  intro R hinw'
  have hepR : z.2.1.base.mir.epoch R = sC.base.mir.epoch R := congrFun hep R
  have hinw : inReceiveOnlyEpoch sC.base.mir R = false := by
    unfold inReceiveOnlyEpoch at hinw' ⊢; rwa [hepR] at hinw'
  have hev_eq : Proofs.Refinement.evictAccEpoch z.2.1.base.mir R =
      Proofs.Refinement.evictAccEpoch sC.base.mir R := by
    unfold Proofs.Refinement.evictAccEpoch; rw [hinw', hinw, hepR]
  refine ⟨hepR, fun _ h => hhon ▸ h, by rw [hhon, hev_eq], by rw [hpq]; exact .refl _,
    fun rk_b T_b hb => validSpurBase_of_inWin_false_and_root_eq hsim'.hsim hb hinw hinw' hepR ?_⟩
  change (z.2.2.1.1.st R).root = (g.st R).root
  rw [hst]

omit [DecidableEq Pt] [SampleableType Pt] in
theorem lFig8_receive_root_eq_of_tcur_eq {PQ PQC : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (st st' : Fig8St Pt) (c : Fig8C Pt) {t' i' : ℕ} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (hrec : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c =
      some (st', t', i', pm))
    (htcur : st'.tcur = st.tcur) :
    st'.root = st.root := by
  unfold lFig8 SM.Construction.scheme SM.Construction.receive at hrec
  dsimp only at hrec
  split at hrec
  · cases hrec
  · by_cases heq : c.1.1 = st.tcur + 1
    · rw [ite_eq_left heq] at hrec
      cases hc12 : c.1.2 with
      | none => rw [hc12] at hrec; cases hrec
      | some Tn =>
        rw [hc12] at hrec
        dsimp only at hrec
        split at hrec
        · cases hrec
        · split at hrec
          · cases hrec
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrec
            have htc : st'.tcur = c.1.1 := by rw [← hrec.1]
            omega
    · rw [ite_eq_right heq] at hrec
      dsimp only at hrec
      split at hrec
      · cases hrec
      · split at hrec
        · cases hrec
        · simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          rw [← hrec.1]

omit [SampleableType Pt] in
theorem deliverPure_root_eq_of_tcur_eq {PQ PQC : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (c : Fig8C Pt)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (R : Party)
    (htcur : ((deliverPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      SM.Config.h1 Q c g).2.st R).tcur = (g.st R).tcur) :
    ((deliverPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      SM.Config.h1 Q c g).2.st R).root = (g.st R).root := by
  revert htcur
  unfold deliverPure
  split
  · intro _; rfl
  · cases g.inTransit Q.other c with
    | none => intro _; rfl
    | some rec_f =>
      dsimp only
      cases hrec : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c with
      | none =>
        dsimp only
        split <;> (intro _; rfl)
      | some val =>
        rcases val with ⟨st', t', i', pm⟩
        dsimp only
        split <;>
        · unfold SM.GameState.accept SM.GameState.delete
          dsimp only
          by_cases hRQ : R = Q
          · subst hRQ
            rw [Function.update_self]
            exact lFig8_receive_root_eq_of_tcur_eq P ℓ Dh encPt encT idOf lam
              (g.st R) st' c hrec
          · rw [Function.update_of_ne hRQ]
            intro _; rfl

omit [SampleableType Pt] in
theorem injectPure_root_eq_of_tcur_eq {PQ PQC : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (c : Fig8C Pt)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (R : Party)
    (htcur : ((injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      3 (qep + 1) SM.Config.h1 Q c g).2.st R).tcur = (g.st R).tcur) :
    ((injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      3 (qep + 1) SM.Config.h1 Q c g).2.st R).root = (g.st R).root := by
  revert htcur
  unfold injectPure
  split
  · intro _; rfl
  · cases hrec : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c with
    | none => intro _; rfl
    | some val =>
      rcases val with ⟨st', t', i', pm⟩
      dsimp only
      split
      · intro _; rfl
      · split
        · unfold SM.GameState.accept
          dsimp only
          by_cases hRQ : R = Q
          · subst hRQ
            rw [Function.update_self]
            exact lFig8_receive_root_eq_of_tcur_eq P ℓ Dh encPt encT idOf lam
              (g.st R) st' c hrec
          · rw [Function.update_of_ne hRQ]
            intro _; rfl
        · split <;> (intro _; rfl)

omit [SampleableType Pt] in
theorem fwdPure_root_eq_of_tcur_eq {PQ PQC : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (s : SimState PQ Pt ℓ) (Q : Party) (c : Fig8C Pt)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (R : Party)
    (htcur : ((fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      3 (qep + 1) SM.Config.h1 s Q c g).2.st R).tcur = (g.st R).tcur) :
    ((fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      3 (qep + 1) SM.Config.h1 s Q c g).2.st R).root = (g.st R).root := by
  revert htcur
  unfold fwdPure
  split
  · exact deliverPure_root_eq_of_tcur_eq P ℓ Dh encPt encT idOf lam Q c g R
  · exact injectPure_root_eq_of_tcur_eq P ℓ Dh encPt encT idOf lam qep Q c g R

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAcceptPure_pq_cases {PQ : Type}
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.pq = s.pq ∨
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.pq = Function.update s.pq Q pq' := by
  unfold onAcceptPure
  dsimp only
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
  · simp only [↓reduceIte]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAnswerPure_pq_cases {PQ : Type}
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (s : SimState PQ Pt ℓ) :
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.pq = s.pq ∨
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.pq = Function.update s.pq Q pq' := by
  unfold onAnswerPure
  cases res with
  | none => exact Or.inl rfl
  | some r8 =>
    cases r8 with
    | rejected => exact Or.inl rfl
    | accepted t₁ i₁ pm₁ =>
      exact onAcceptPure_pq_cases qep Q w isDel t₁ i₁ _ ci? T pq' s

omit [SampleableType Pt] in
theorem fwdCPure_pq_cases_and_root_eq
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : List (BitVec 8)) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ) :
    let out := fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c' x
    (out.2.1.base.pq = x.1.base.pq ∨ out.2.1.base.pq = Function.update x.1.base.pq Q pq') ∧
    (∀ R, (out.2.2.1.st R).tcur = (x.2.1.st R).tcur →
      (out.2.2.1.st R).root = (x.2.1.st R).root) := by
  have hplain :
      let out := fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' none c' x
      (out.2.1.base.pq = x.1.base.pq ∨ out.2.1.base.pq = Function.update x.1.base.pq Q pq') ∧
      (∀ R, (out.2.2.1.st R).tcur = (x.2.1.st R).tcur →
        (out.2.2.1.st R).root = (x.2.1.st R).root) := by
    unfold fwdCPure
    dsimp only
    exact ⟨onAnswerPure_pq_cases qep Q w isDel ci? T pq' _ x.1.base,
      fun R htc => fwdPure_root_eq_of_tcur_eq P ℓ Dh encPt encT idOf lam qep x.1.base Q c'
        x.2.1 R htc⟩
  cases honestC with
  | none => exact hplain
  | some c₀ =>
    unfold fwdCPure
    dsimp only
    split
    · cases predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) P x.1 Q w c₀ c' with
      | none => exact ⟨Or.inl rfl, fun _ _ => rfl⟩
      | some ev =>
        cases ev with
        | none => exact ⟨Or.inl rfl, fun _ _ => rfl⟩
        | some tip =>
          rcases tip with ⟨t₁, i₁, pm₁⟩
          dsimp only
          split
          · exact ⟨onAcceptPure_pq_cases qep Q w true t₁ i₁ pm₁.2 ci? T pq' x.1.base,
              fun R htc => deliverPure_root_eq_of_tcur_eq P ℓ Dh encPt encT idOf lam Q c₀
                x.2.1 R htc⟩
          · exact ⟨Or.inl rfl,
              fun R htc => deliverPure_root_eq_of_tcur_eq P ℓ Dh encPt encT idOf lam Q c₀
                x.2.1 R htc⟩
    · exact hplain

omit [SampleableType Pt] in
theorem fwdEvictCPure_pq_cases_and_root_eq
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : List (BitVec 8)) (c' : Fig8C Pt)
    (x : JointC (List (BitVec 8)) Pt ℓ) :
    let out := fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel T pq' c' x
    (out.2.1.base.pq = x.1.base.pq ∨ out.2.1.base.pq = Function.update x.1.base.pq Q pq') ∧
    (∀ R, (out.2.2.1.st R).tcur = (x.2.1.st R).tcur →
      (out.2.2.1.st R).root = (x.2.1.st R).root) := by
  unfold fwdEvictCPure
  split
  · exact ⟨Or.inl rfl, fun _ _ => rfl⟩
  · exact fwdCPure_pq_cases_and_root_eq P ℓ Dh encPt encT idOf lam qep false Q w isDel none
      T pq' none c' x

omit [SampleableType Pt] in
theorem simRecvStepC_pq_reach_and_root_eq_of_tcur_eq
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    let out := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w isDel (sC, gh)
    (∀ R, Corr.SpqrReachFrom P.spqr (sC.base.pq R) (out.2.1.base.pq R)) ∧
    (∀ R, (out.2.2.1.st R).tcur = (gh.1.st R).tcur →
      (out.2.2.1.st R).root = (gh.1.st R).root) := by
  have hrefl : (∀ R, Corr.SpqrReachFrom P.spqr (sC.base.pq R) (sC.base.pq R)) ∧
      (∀ R, (gh.1.st R).tcur = (gh.1.st R).tcur → (gh.1.st R).root = (gh.1.st R).root) :=
    ⟨fun _ => .refl _, fun _ _ => rfl⟩
  unfold simRecvStepC simRecvStepCGen
  by_cases hst : sC.base.stopped = true
  · simp [hst, Corr.SpqrReachFrom.refl]
  simp only [hst, Bool.false_eq_true, ↓reduceIte]
  by_cases hwin : sC.base.mir.win = true
  · simp [hwin, Corr.SpqrReachFrom.refl]
  simp only [hwin, Bool.false_eq_true, ↓reduceIte]
  by_cases hdel : (isDel && (sC.base.mir.inTransit Q.other w).isNone) = true
  · simp [hdel, Corr.SpqrReachFrom.refl]
  simp only [hdel, Bool.false_eq_true, ↓reduceIte]
  by_cases hinj : (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w))) = true
  · simp [hinj, Corr.SpqrReachFrom.refl]
  simp only [hinj, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : w.length < 9
  · simp [hlen, Corr.SpqrReachFrom.refl]
  simp only [hlen, ↓reduceIte]
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact hrefl
  | some hb =>
    rcases hb with ⟨h, body⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · simp [haddr, Corr.SpqrReachFrom.refl]
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
    · simp [hpan, Corr.SpqrReachFrom.refl]
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact hrefl
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      have hpq_reach : ∀ (pq_post : Party → List (BitVec 8)),
          (pq_post = sC.base.pq ∨ pq_post = Function.update sC.base.pq Q pq') →
          ∀ R, Corr.SpqrReachFrom P.spqr (sC.base.pq R) (pq_post R) := by
        intro pq_post hcases R
        rcases hcases with hpq | hpq
        · rw [hpq]; exact .refl _
        · rw [hpq]
          by_cases hRQ : R = Q
          · subst hRQ; rw [Function.update_self]; exact .recv (.refl _) hspqr
          · rw [Function.update_of_ne hRQ]; exact .refl _
      cases (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        split
        · exact hrefl
        · obtain ⟨hpq, hroot⟩ := fwdCPure_pq_cases_and_root_eq P ℓ Dh encPt encT
            idOf lam qep true Q w isDel (some ci) h.senderRatchetKey pq' _ _ (sC, gh)
          exact ⟨hpq_reach _ hpq, hroot⟩
      | none =>
        dsimp only
        let x₁ : JointC (List (BitVec 8)) Pt ℓ :=
          if inReceiveOnlyEpoch sC.base.mir Q ||
              (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
            ({ sC with base :=
                { sC.base with amb := sC.base.amb + 1, stopped := false } }, gh)
          else (sC, gh)
        have hx1_pq : x₁.1.base.pq = sC.base.pq := by
          dsimp only [x₁]; split <;> rfl
        have hx1_g : x₁.2.1 = gh.1 := by dsimp only [x₁]; split <;> rfl
        have hrefl₁ :
            (∀ R, Corr.SpqrReachFrom P.spqr (sC.base.pq R) (x₁.1.base.pq R)) ∧
            (∀ R, (x₁.2.1.st R).tcur = (gh.1.st R).tcur →
              (x₁.2.1.st R).root = (gh.1.st R).root) := by
          rw [hx1_pq, hx1_g]; exact hrefl
        split
        · exact hrefl
        · split
          · exact hrefl
          · split
            · exact hrefl₁
            · cases decT h.senderRatchetKey with
              | none => exact hrefl₁
              | some T =>
                dsimp only
                split
                · obtain ⟨hpq, hroot⟩ := fwdEvictCPure_pq_cases_and_root_eq P ℓ Dh
                    encPt encT idOf lam qep true Q w isDel h.senderRatchetKey pq' _ x₁
                  rw [hx1_pq] at hpq
                  rw [hx1_g] at hroot
                  exact ⟨hpq_reach _ hpq, hroot⟩
                · obtain ⟨hpq, hroot⟩ := fwdCPure_pq_cases_and_root_eq P ℓ Dh encPt
                    encT idOf lam qep true Q w isDel none h.senderRatchetKey pq' _ _ x₁
                  rw [hx1_pq] at hpq
                  rw [hx1_g] at hroot
                  exact ⟨hpq_reach _ hpq, hroot⟩

private theorem simRecvStepCGen_inject_knownChain_preserves_simInvCXLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (lam : Pt) (qep q r' r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hr : r' < r)
    (Q : Party) (w : List (BitVec 8)) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false }
      ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    {pq' : List (BitVec 8)} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    {ci : ℕ}
    (hfind : (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) = some ci)
    (hrej_f :
      ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false) :
    let i := h.counter.toNat + 1
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let honestC :=
      (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    let ch := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
    let c_mk : Fig8C Pt :=
      match honestC with
      | some c₀ =>
        if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀
        else ((ch.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
      | none => ((ch.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    let r_out := fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false (some ci)
      h.senderRatchetKey pq' honestC c_mk (sC, g, false)
    ∃ s_R' ec' winBefore',
      SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
        r_out.2.1 { r_out.2.2.1 with win := false } ec' winBefore' epExp := by
  intro i ser tag honestC ch c_mk r_out
  cases hg_win : g.win
  · have hg_eq0 : { g with win := false } = g := by cases g; simp_all
    rw [hg_eq0] at hinv
    have hmeta := hinv.hsim.hmeta
    have hpq' : InvB Inv q r pq' :=
      InvB.recv hS (hinv.hsim.hpqInv Q) hspqr
    have htr_mir : (sC.base.mir.inTransit Q.other w).isSome = false := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> simp
    have hsafe_mir : sC.base.mir.safeInj 3 = true := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;>
        cases sC.base.mir.safeInj 3 <;> simp
    have himg : ratchetKeyAdmissible P.codec decT encT w = true := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;>
        cases sC.base.mir.safeInj 3 <;> cases ratchetKeyAdmissible P.codec decT encT w <;> simp
    rcases lOnImage_some_of_parse P decT encT w h body himg hlen hparse with ⟨T, hdecT, hencT⟩
    rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
      ⟨ch', hch_elem', hch_key'⟩
    have hch_eq : ch = ch' := by simp [ch, hch_elem']
    have hch_elem : (sC.base.chains Q)[ci]? = some ch := by rw [hch_eq, hch_elem']
    have hch_key : ch.key = some h.senderRatchetKey := by rw [hch_eq, hch_key']
    have hch_mem : ch ∈ sC.base.chains Q := List.mem_of_getElem? hch_elem
    rcases hinv.hsim.hchains_sync Q ch hch_mem with
      ⟨hch_ep_le, hch_recv, hch_key_sync, v_old, hvR, hsync_old⟩
    have hch_none : ch.key.isNone = false := by rw [hch_key]; rfl
    rw [hch_none] at hch_key_sync
    simp only [Bool.false_eq_true, ↓reduceIte, hch_key] at hch_key_sync
    have hsrk_eq : h.senderRatchetKey = encT (Dh.dh (epExp ch.epoch) Dh.base) :=
      Option.some.inj hch_key_sync
    let c : Fig8C Pt := ((ch.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    have hmkC : c_mk = c := by
      refine mkC_eq_raw_of_honest_epochC P (InvB Inv q r) Dh encT decT hinj epExp sC.base Q w h body
        (sC.base.pq Q) pq' salt ch.epoch hdecT hencT
        (fun wc hwc => (hinv.hsim.hhon wc hwc).1) hparse hspqr hpan ?_ (hinv.hsim.hpqInv Q)
      intro wc hwc hwc_w _
      rcases wc with ⟨w₀, c₀⟩
      dsimp only at hwc_w ⊢
      subst w₀
      rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp
        (hinv.hsim.hhon (w, c₀) hwc).1 hparse with ⟨_, hsrk₀, _, _⟩
      have hdh : Dh.dh (epExp c₀.1.1) Dh.base = Dh.dh (epExp ch.epoch) Dh.base :=
        hinj (hsrk₀.symm.trans hsrk_eq)
      have hle_g : ch.epoch ≤ max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B) := by
        cases Q <;>
          [exact le_trans hch_ep_le (le_max_left _ _); exact le_trans hch_ep_le (le_max_right _ _)]
      exact hinv.hsim.hcoll c₀.1.1 ch.epoch (hinv.hsim.hhon (w, c₀) hwc).2.1 hle_g hdh
    have htoWire : LibsignalSim.toWire c = w :=
      toWire_raw_eq w hlen ch.epoch (decT h.senderRatchetKey) i (effectiveHkdfSalt32 salt)
    have hfwd : fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
        sC.base Q c g =
        injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          SM.Config.h1 Q c g :=
      fwdPure_of_inTransit_false _ 3 (qep + 1) SM.Config.h1 sC.base Q w c g
        (fun wc hwc => (hinv.hsim.hhon wc hwc).1.1) htoWire htr_mir
    have htr_fig8 : (g.inTransit Q.other c).isSome = false :=
      inTransit_fig8_isSome_of_toWire hmeta Q w c htoWire htr_mir
    have hguard_fig8 : (g.win || (g.inTransit Q.other c).isSome || !(g.safeInj 3)) = false := by
      rw [hmeta.hwin_fig8, htr_fig8, hmeta.safeInj_fig8, hsafe_mir]; rfl
    let pos : SM.Pos := ⟨Q.other, ch.epoch, i⟩
    let mir' := sC.base.mir.accept Q () pos
    cases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c with
    | none =>
      have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          SM.Config.h1 Q c g = (some .rejected, g) := by
        unfold injectPure; simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig]
      have hnot_acc :
          r_out.2.1 = sC ∧ { r_out.2.2.1 with win := false } = { g with win := false } := by
        refine fwdCPure_inject_of_fwdPure_not_accepted P ℓ Dh encPt encT idOf lam qep Q w (some ci)
          h.senderRatchetKey pq' honestC c_mk (sC, g, false) ?_ ?_
        · intro t' i' m'; dsimp only; rw [hmkC, hfwd, hinj_fig8]; simp
        · dsimp only; rw [hmkC, hfwd, hinj_fig8]
      rw [hnot_acc.1, hnot_acc.2, hg_eq0]
      exact ⟨s_R, ec, winBefore, simInvCXLazy_mono_r hinv (Nat.le_of_lt hr)⟩
    | some res_fig =>
      rcases res_fig with ⟨st', t', i', pub, m⟩
      have hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c =
          some (st', t', i', pub, m) := hfig
      rcases lFig8_receive_knownChain_accept P ℓ Dh encPt encT idOf lam Q (g.st Q)
        (sC.base.mir.epoch Q) ch v_old (hinv.hsim.hst_id Q) (hinv.hsim.htcur Q) hch_ep_le hch_recv
        hvR hsync_old h.counter hrej_f (decT h.senderRatchetKey) ((ser, tag), effectiveHkdfSalt32 salt)
        hfig' with ⟨ht', hi', v', hst', hsync'⟩
      subst ht' hi'
      have hnot_gt : ¬ (qep + 1 < ch.epoch) := by have := hinv.hsim.hep_le Q; omega
      have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < ch.epoch) := by omega
      by_cases htriv : sC.base.mir.trivial 3 pos = true
      · let s' : SimState (List (BitVec 8)) Pt ℓ :=
          { sC.base with
            mir := mir',
            pq := Function.update sC.base.pq Q pq',
            unackA := sC.base.unackA && Q != Party.A,
            chains :=
              Function.update sC.base.chains Q ((sC.base.chains Q).modify ci (·.accept i)) }
        let kept' := Function.update sC.kept Q
          (Kept.recv (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (fs := lFS P.C P.codec ℓ encT idOf 25000) c (sC.kept Q))
        let sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ := { sC with base := s', kept := kept' }
        let g' := g.accept Q st' pos
        let st_R' := expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q)
        let s_R' := s_R.accept Q st_R' pos
        have htriv_fig8 : g.trivial 3 pos = true := by rw [hmeta.trivial_fig8, htriv]
        have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
            SM.Config.h1 Q c g = (some (.accepted ch.epoch i (some (pub, m))), g') := by
          unfold injectPure
          simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig', hnot_gt_fig8,
            show g.trivial 3 ⟨Q.other, ch.epoch, h.counter.toNat + 1⟩ = true from htriv_fig8]
          rfl
        have hr_out : r_out = (some (.accepted ch.epoch i (some m)), (sC', g', false)) := by
          dsimp only [r_out]
          have hplain :
              fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false (some ci)
                h.senderRatchetKey pq' honestC c_mk (sC, g, false) =
              fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false (some ci)
                h.senderRatchetKey pq' none c_mk (sC, g, false) := by
            unfold fwdCPure
            cases honestC <;> simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          rw [hplain, hmkC]
          unfold fwdCPure
          dsimp only
          rw [hfwd, hinj_fig8]
          unfold onAnswerPure onAcceptPure
          simp only [hnot_gt, show sC.base.mir.trivial 3 ⟨Q.other, ch.epoch, i⟩ = true from htriv,
            ↓reduceIte]
          rfl
        have hg'_win : { g' with win := false } = g' := by
          unfold g' SM.GameState.accept SM.GameState.delete; cases g; simp_all
        have hold : ch.epoch ≤ (g.st Q).tcur := by
          rw [hinv.hsim.htcur Q]; exact hch_ep_le
        have hkept' : KeptInv P Dh encPt encT idOf lam sC' g' :=
          keptInv_recv_accept hinv.hkept Q (hinv.hsim.hst_id Q) c st' _ hfig' rfl rfl
        have hsync8' : EpochSync P Dh encPt encT idOf s'.honest sC.sent sC.snaps g' epExp :=
          epochSync_recv_old P Dh encPt encT idOf lam _ _ _ _ _ hinv.hsync Q c st' _ hfig' hold rfl
            (fun hw => hw) (fun _ hwc => hwc)
        have hinv_sub1 : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' g'
            ec winBefore epExp := by
          subst hst'
          exact simInvCXLazy_inject_known_accept P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC g
            ec winBefore epExp hinv Q ci ch i pq' hch_elem v' hsync' pos rfl hpq' s' rfl g' rfl
            s_R' rfl kept' hkept' hsync8'
        rw [hr_out]
        dsimp only
        rw [hg'_win]
        exact ⟨s_R', ec, winBefore,
          simInvCXLazy_mono_r hinv_sub1 (Nat.le_sub_one_of_lt hr)⟩
      · have htriv_f : sC.base.mir.trivial 3 pos = false := Bool.eq_false_iff.mpr htriv
        have htriv_fig8 : g.trivial 3 pos = false := by rw [hmeta.trivial_fig8, htriv_f]
        have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
            SM.Config.h1 Q c g = (some .rejected, { g with win := true }) := by
          unfold injectPure
          simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig', hnot_gt_fig8,
            show g.trivial 3 ⟨Q.other, ch.epoch, h.counter.toNat + 1⟩ = false from htriv_fig8]
          rfl
        have hnot_acc :
            r_out.2.1 = sC ∧ { r_out.2.2.1 with win := false } = { g with win := false } := by
          refine fwdCPure_inject_of_fwdPure_not_accepted P ℓ Dh encPt encT idOf lam qep Q w
            (some ci) h.senderRatchetKey pq' honestC c_mk (sC, g, false) ?_ ?_
          · intro t' i' m'; dsimp only; rw [hmkC, hfwd, hinj_fig8]; simp
          · dsimp only; rw [hmkC, hfwd, hinj_fig8]
        rw [hnot_acc.1, hnot_acc.2, hg_eq0]
        exact ⟨s_R, ec, winBefore, simInvCXLazy_mono_r hinv (Nat.le_of_lt hr)⟩
  · have hfwd_win := fwdPure_of_win_true P ℓ Dh encPt encT idOf lam qep sC.base Q c_mk g hg_win
    have hnot_acc :
        r_out.2.1 = sC ∧ { r_out.2.2.1 with win := false } = { g with win := false } := by
      refine fwdCPure_inject_of_fwdPure_not_accepted P ℓ Dh encPt encT idOf lam qep Q w (some ci)
        h.senderRatchetKey pq' honestC c_mk (sC, g, false) ?_ ?_
      · intro t' i' m'; dsimp only; rw [hfwd_win]; simp
      · dsimp only; rw [hfwd_win]
    rw [hnot_acc.1, hnot_acc.2]
    exact ⟨s_R, ec, winBefore, simInvCXLazy_mono_r hinv (Nat.le_of_lt hr)⟩

theorem kemFailSimImpl_inject_preserves_simInvCXLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (lam : Pt) (qep q r' r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hr : r' < r)
    (Q : Party) (w : List (BitVec 8)) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false }
      ec winBefore epExp)
    (z : Option (SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inr (Q, w))))).run (sC, (g, false), tr))) :
    ∃ s_R' ec' winBefore',
      SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
        z.2.1 { z.2.2.1.1 with win := false } ec' winBefore' epExp := by
  change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000)
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false))).run
    (sC, (g, false), tr)) at hz
  rw [runProbeStep_run, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w_out, hw_out, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hw_step : (w_out.1.1, (w_out.1.2, w_out.2)) ∈ support
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) (sC, (g, false))) := by
    change (w_out.1.1, (w_out.1.2, w_out.2)) ∈ support
      ((((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000)
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false)).run
        sC).run (g, false)) >>= fun r => pure (r.1.1, (r.1.2, r.2)))
    rw [MonadAttach.mem_support_bind]
    exact ⟨w_out, hw_out, by simp⟩
  rw [stepSimCNone_inject_eq, support_pure, Set.mem_singleton_iff,
    simRecvStepC_eq_gen_false P ℓ Dh encPt encT decT idOf lam qep Q w false (sC, g, false)
      (Or.inl rfl)] at hw_step
  have hsC_eq : w_out.1.2 =
      (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, g, false)).2.1 :=
    congrArg (·.2.1) hw_step
  have hg_eq : w_out.2.1 =
      (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, g, false)).2.2.1 :=
    congrArg (·.2.2.1) hw_step
  change ∃ s_R' ec' winBefore',
    SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R' w_out.1.2
      (clearWin w_out.2.1) ec' winBefore' epExp
  rw [hsC_eq, hg_eq]
  have hinv_mono := simInvCXLazy_mono_r hinv (Nat.le_of_lt hr)
  have hstop := hinv.hsim.hmeta.hstop
  have hwin_mir := hinv.hsim.hmeta.hwin_mir
  unfold simRecvStepCGen
  simp only [hstop, hwin_mir, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.not_false,
    Bool.true_and]
  by_cases hguard :
      ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w)) = true
  · simp only [hguard, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
  simp only [hguard, Bool.false_eq_true, ↓reduceIte]
  have hguard_f :
      ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w)) = false := Bool.eq_false_iff.mpr hguard
  by_cases hlen : w.length < 9
  · simp only [hlen, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
  simp only [hlen, ↓reduceIte]
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact ⟨s_R, ec, winBefore, hinv_mono⟩
  | some hb =>
    rcases hb with ⟨h, body⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · simp only [haddr, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
    · simp only [hpan, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    have hpan_f : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false :=
      Bool.eq_false_iff.mpr hpan
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact ⟨s_R, ec, winBefore, hinv_mono⟩
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases hfind : (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        by_cases hrej :
            ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = true
        · simp only [hrej, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
        simp only [hrej, Bool.false_eq_true, ↓reduceIte]
        exact simRecvStepCGen_inject_knownChain_preserves_simInvCXLazy P Inv ℓ Dh encPt encT decT
          idOf hinj lam qep q r' r hS hr Q w x₀ s_R sC g ec winBefore epExp hinv hguard_f hlen
          hparse hspqr hpan_f hfind (Bool.eq_false_iff.mpr hrej)
      | none =>
        dsimp only
        have hs_stop : { sC.base with amb := sC.base.amb + 1, stopped := false } =
            { sC.base with amb := sC.base.amb + 1 } := by
          cases h_s : sC.base; rw [h_s] at hstop; subst hstop; rfl
        simp only [hs_stop]
        have htr_mir : (sC.base.mir.inTransit Q.other w).isSome = false := by
          revert hguard_f; cases (sC.base.mir.inTransit Q.other w).isSome <;> simp
        have hsafe_mir : sC.base.mir.safeInj 3 = true := by
          revert hguard_f; cases (sC.base.mir.inTransit Q.other w).isSome <;>
            cases sC.base.mir.safeInj 3 <;> simp
        let x₁ : JointC (List (BitVec 8)) Pt ℓ :=
          if inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
            ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, g, false)
          else (sC, g, false)
        have hx₁_inv : ∃ winBefore₁,
            SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R x₁.1
              (clearWin x₁.2.1) ec winBefore₁ epExp := by
          dsimp only [x₁]
          split
          · exact ⟨_, simInvCXLazy_mono_r
              (simInvCXLazy_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r
                (Nat.zero_lt_of_lt hr) x₀ s_R sC { g with win := false } ec winBefore epExp hinv
                rfl)
              (Nat.le_sub_one_of_lt hr)⟩
          · exact ⟨winBefore, hinv_mono⟩
        obtain ⟨winBefore₁, hinv₁⟩ := hx₁_inv
        have htriv₁ : ∀ pos, x₁.2.1.trivial 3 pos = x₁.1.base.mir.trivial 3 pos := by
          intro pos; exact hinv₁.hsim.hmeta.trivial_fig8 3 pos
        have hhon₁ : ∀ wc ∈ x₁.1.base.honest, wc.1 = LibsignalSim.toWire wc.2 :=
          fun wc hwc => (hinv₁.hsim.hhon wc hwc).1.1
        have hmir₁ : x₁.1.base.mir = sC.base.mir := by dsimp only [x₁]; split <;> rfl
        split
        · exact ⟨s_R, ec, winBefore, hinv_mono⟩
        · split
          · exact ⟨s_R, ec, winBefore, hinv_mono⟩
          · split
            · exact ⟨s_R, ec, winBefore₁, hinv₁⟩
            · cases hdec_srk : decT h.senderRatchetKey with
              | none => dsimp only; exact ⟨s_R, ec, winBefore₁, hinv₁⟩
              | some T =>
                dsimp only
                split
                · rename_i hev_true
                  unfold fwdEvictCPure
                  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                  have hraw_w :
                      LibsignalSim.toWire
                        ((sC.base.mir.epoch Q + 1, some T),
                          (h.counter.toNat + 1,
                            ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
                              effectiveHkdfSalt32 salt))) = w :=
                    toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T) (h.counter.toNat + 1)
                      (effectiveHkdfSalt32 salt)
                  have hpres := fwdCPure_inject_of_epoch_lt P ℓ Dh encPt encT idOf lam qep Q w none
                    h.senderRatchetKey pq' none
                    ((sC.base.mir.epoch Q + 1, some T),
                      (h.counter.toNat + 1,
                        ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
                    x₁ (hmir₁ ▸ hsafe_mir) (hmir₁ ▸ hinv.hsim.hcomp) hhon₁ hraw_w
                    (hmir₁ ▸ htr_mir) htriv₁ (by rw [hmir₁]; dsimp only; omega)
                  rw [hpres.1, hpres.2]
                  exact ⟨s_R, ec, winBefore₁, hinv₁⟩
                · rename_i hev_false
                  have hev_f :
                      ((((sC.base.honest.find? fun wc =>
                          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                        fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = false :=
                    Bool.eq_false_iff.mpr hev_false
                  let honestC := (sC.base.honest.find? fun wc =>
                    wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
                  let c_mk : Fig8C Pt :=
                    match honestC with
                    | some c =>
                      if c.2.2.2 = effectiveHkdfSalt32 salt then c
                      else ((sC.base.mir.epoch Q + 1, some T),
                        (h.counter.toNat + 1,
                          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
                    | none =>
                      ((sC.base.mir.epoch Q + 1, some T),
                        (h.counter.toNat + 1,
                          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
                  have hc_mk_props :
                      LibsignalSim.toWire c_mk = w ∧ sC.base.mir.epoch Q < c_mk.1.1 := by
                    dsimp only [c_mk, honestC]
                    cases hfind_hon : sC.base.honest.find?
                        (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
                    | none =>
                      simp only [Option.map]
                      exact ⟨toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T)
                        (h.counter.toNat + 1) (effectiveHkdfSalt32 salt), by omega⟩
                    | some wc =>
                      rcases wc with ⟨w_c, c_h⟩
                      simp only [Option.map]
                      split
                      · have hmem := List.mem_of_find?_eq_some hfind_hon
                        have hpred := List.find?_some hfind_hon
                        simp only [Bool.and_eq_true, beq_iff_eq] at hpred
                        have hw_eq : LibsignalSim.toWire c_h = w := by
                          rw [← hpred.1]
                          exact (hinv.hsim.hhon (w_c, c_h) hmem).1.1.symm
                        simp only [hfind_hon, Option.map_some, beq_eq_false_iff_ne, Ne,
                          Option.some.injEq, decide_eq_true_eq] at hev_f
                        have hc_ep : c_h.1.1 = sC.base.mir.epoch Q + 1 :=
                          Decidable.of_not_not hev_f
                        exact ⟨hw_eq, by omega⟩
                      · dsimp only
                        exact ⟨toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T)
                          (h.counter.toNat + 1) (effectiveHkdfSalt32 salt), by omega⟩
                  have hpres := fwdCPure_inject_of_epoch_lt P ℓ Dh encPt encT idOf lam qep Q w none
                    h.senderRatchetKey pq' honestC c_mk x₁ (hmir₁ ▸ hsafe_mir)
                    (hmir₁ ▸ hinv.hsim.hcomp) hhon₁ hc_mk_props.1 (hmir₁ ▸ htr_mir) htriv₁
                    (hmir₁ ▸ hc_mk_props.2)
                  change ∃ s_R' ec' winBefore',
                    SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
                      (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false none
                        h.senderRatchetKey pq' honestC c_mk x₁).2.1
                      (clearWin (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false none
                        h.senderRatchetKey pq' honestC c_mk x₁).2.2.1)
                      ec' winBefore' epExp
                  rw [hpres.1, hpres.2]
                  exact ⟨s_R, ec, winBefore₁, hinv₁⟩

/-- `inject` queries of `kemFailSimImpl` preserve `EvictedSpurHistSimInvLazy` with probe flag `false`. -/
theorem evictedSpurHistSimInvLazy_inject_step
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (_hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r' r w_rem : ℕ) (hS : Proofs.Refinement.SpqrCLocal P.spqr q InvPQ)
    (hr : r' < r)
    (Q : Party) (w : List (BitVec 8)) (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g)
    (z : Option (SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inr (Q, w))))).run (sC, (g, false), tr)))
    (_hcand : z.2.2.2.cand = none) :
    z.2.2.1.2 = false ∧
    EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r' w_rem
      z.2.1 z.2.2.1.1 := by
  have hfl := kemFailSimImpl_inject_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep Q w sC g
    tr z hz
  rcases hInv.2 with ⟨x₀, s_R, ec, winBefore, epExp, hsim, hspur_lazy⟩
  obtain ⟨s_R', ec', winBefore', hsim'⟩ :=
    kemFailSimImpl_inject_preserves_simInvCXLazy P K InvPQ ℓ Dh encPt encT decT idOf hinj lam qep q
      r' r hS hr Q w x₀ s_R sC g tr ec winBefore epExp hsim z hz
  change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000)
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false))).run
    (sC, (g, false), tr)) at hz
  rw [runProbeStep_run, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w_out, hw_out, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hw_step : (w_out.1.1, (w_out.1.2, w_out.2)) ∈ support
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) (sC, (g, false))) := by
    change (w_out.1.1, (w_out.1.2, w_out.2)) ∈ support
      ((((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000)
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false)).run
        sC).run (g, false)) >>= fun r => pure (r.1.1, (r.1.2, r.2)))
    rw [MonadAttach.mem_support_bind]
    exact ⟨w_out, hw_out, by simp⟩
  rw [stepSimCNone_inject_eq, support_pure, Set.mem_singleton_iff] at hw_step
  have hsC_eq : w_out.1.2 =
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w false (sC, (g, false))).2.1 :=
    congrArg (·.2.1) hw_step
  have hg_eq : w_out.2.1 =
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w false (sC, (g, false))).2.2.1 :=
    congrArg (·.2.2.1) hw_step
  obtain ⟨hhon_eq, hep_eq, hhist'⟩ :=
    simRecvStepC_inject_preserves_spqrHistoryInv_and_epoch_of_simInvC P K hspqr_eq ℓ Dh encPt encT
      decT idOf lam qep Q w (sC, (g, false)) hsim.hsim.hcomp hInv.1.hhist
  obtain ⟨hreach_pq, hroot_eq⟩ :=
    simRecvStepC_pq_reach_and_root_eq_of_tcur_eq P ℓ Dh encPt encT decT idOf lam qep Q w false
      sC (g, false)
  have hgame' : EvictedSpurHistGameInv P K qep w_rem w_out.1.2 := by
    refine ⟨hsC_eq ▸ hhist', ?_⟩
    have hrem : remSendEpochs qep w_out.1.2.base.mir = remSendEpochs qep sC.base.mir := by
      unfold remSendEpochs; rw [hsC_eq, hep_eq]
    exact hrem ▸ hInv.1.hw_rem
  refine ⟨hfl, hgame', evictedSpurSimInvLazy_of_step hInv_top hgame'.hhist hsim' hspur_lazy ?_⟩
  intro R hinw'
  have hepR : w_out.1.2.base.mir.epoch R = sC.base.mir.epoch R := by
    rw [hsC_eq]; exact congrFun hep_eq R
  have hhon : w_out.1.2.base.honest = sC.base.honest := by
    rw [hsC_eq]; exact hhon_eq
  have hinw : inReceiveOnlyEpoch sC.base.mir R = false := by
    unfold inReceiveOnlyEpoch at hinw' ⊢; rwa [hepR] at hinw'
  have hev_eq : Proofs.Refinement.evictAccEpoch w_out.1.2.base.mir R =
      Proofs.Refinement.evictAccEpoch sC.base.mir R := by
    unfold Proofs.Refinement.evictAccEpoch; rw [hinw', hinw, hepR]
  refine ⟨hepR, fun _ h => hhon ▸ h, by rw [hhon, hev_eq], ?_,
    fun rk_b T_b hb => validSpurBase_of_inWin_false_and_root_eq hsim'.hsim hb hinw hinw' hepR ?_⟩
  · rw [hsC_eq]; exact hspqr_eq ▸ hreach_pq R
  · change (w_out.2.1.st R).root = (g.st R).root
    rw [hg_eq]
    apply hroot_eq R
    have htc1 : (w_out.2.1.st R).tcur = w_out.1.2.base.mir.epoch R := hsim'.hsim.htcur R
    have htc0 : (g.st R).tcur = sC.base.mir.epoch R := hsim.hsim.htcur R
    rw [← hg_eq, htc1, htc0, hepR]

theorem evictedSpurSimInvLazy_deliver_step
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q r' r w_rem : ℕ) (hS : SpqrCLocal P.spqr q InvPQ) (hr : r' < r)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hEx : EvictedSpurSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r sC g)
    (z : Option (SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false), tr))) :
    EvictedSpurSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r' z.2.1 z.2.2.1.1 := by
  have heq := kemFailSimImpl_deliver_eq_simRecvStepC P K ℓ Dh encPt encT decT idOf lam qep
    sC (g, false) tr Q w hz
  have hsC_eq : z.2.1 =
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.1 :=
    congrArg (·.2.1) heq
  have hg_eq : z.2.2.1.1 =
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.2.1 :=
    congrArg (·.2.2.1) heq
  have hgame' : EvictedSpurHistGameInv P K qep w_rem z.2.1 := by
    rw [hsC_eq]
    exact simRecvStepC_deliver_preserves_evictedSpurHistGameInv_of_simInvCXLazy P K hspqr_eq ℓ Dh
      encPt encT decT idOf hinj lam qep q r w_rem hInv_top Q w sC (g, false) hInv hEx
  rcases hEx with ⟨x₀, s_R, ec, winBefore, epExp, hsim, hspur_lazy⟩
  obtain ⟨s_R', ec', winBefore', hsim'⟩ :=
    kemFailSimImpl_deliver_preserves_simInvCXLazy P K InvPQ ℓ Dh encPt encT decT idOf hinj hdec lam
      qep q r' r hS hr Q w x₀ s_R sC g tr ec winBefore epExp hsim z hz
  obtain ⟨hhon_eq, hep_cases⟩ :=
    simRecvStepC_deliver_epoch_cases_of_simInvCXLazy P ℓ Dh encPt encT decT idOf lam qep q r Q w
      sC (g, false) hsim
  obtain ⟨hreach_pq, hroot_eq⟩ :=
    simRecvStepC_pq_reach_and_root_eq_of_tcur_eq P ℓ Dh encPt encT decT idOf lam qep Q w true
      sC (g, false)
  refine evictedSpurSimInvLazy_of_step hInv_top hgame'.hhist hsim' hspur_lazy ?_
  intro R hinw'
  have hhon : z.2.1.base.honest = sC.base.honest := by rw [hsC_eq]; exact hhon_eq
  have hepR : z.2.1.base.mir.epoch R = sC.base.mir.epoch R := by
    rw [hsC_eq] at hinw' ⊢
    rcases hep_cases with hep_eq | ⟨_, hinwQ_t, hep_upd⟩
    · exact congrFun hep_eq R
    · have hRQ : R ≠ Q := by intro h; subst h; rw [hinwQ_t] at hinw'; cases hinw'
      rw [hep_upd, Function.update_of_ne hRQ]
  have hinw : inReceiveOnlyEpoch sC.base.mir R = false := by
    unfold inReceiveOnlyEpoch at hinw' ⊢; rwa [hepR] at hinw'
  have hev_eq : Proofs.Refinement.evictAccEpoch z.2.1.base.mir R =
      Proofs.Refinement.evictAccEpoch sC.base.mir R := by
    unfold Proofs.Refinement.evictAccEpoch; rw [hinw', hinw, hepR]
  refine ⟨hepR, fun _ h => hhon ▸ h, by rw [hhon, hev_eq], ?_,
    fun rk_b T_b hb => validSpurBase_of_inWin_false_and_root_eq hsim'.hsim hb hinw hinw' hepR ?_⟩
  · rw [hsC_eq]; exact hspqr_eq ▸ hreach_pq R
  · change (z.2.2.1.1.st R).root = (g.st R).root
    rw [hg_eq]
    apply hroot_eq R
    have htc1 : (z.2.2.1.1.st R).tcur = z.2.1.base.mir.epoch R := hsim'.hsim.htcur R
    have htc0 : (g.st R).tcur = sC.base.mir.epoch R := hsim.hsim.htcur R
    rw [← hg_eq, htc1, htc0, hepR]

/-- `deliver` queries of `kemFailSimImpl` preserve `EvictedSpurHistSimInvLazy`. -/
theorem evictedSpurHistSimInvLazy_deliver_step
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q r' r w_rem : ℕ) (hS : SpqrCLocal P.spqr q InvPQ) (hr : r' < r)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g)
    (z : Option (SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false), tr)))
    (_hcand : z.2.2.2.cand = none) :
    EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r' w_rem
      z.2.1 z.2.2.1.1 := by
  have heq := kemFailSimImpl_deliver_eq_simRecvStepC P K ℓ Dh encPt encT decT idOf lam qep
    sC (g, false) tr Q w hz
  have hsC_eq : z.2.1 =
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.1 :=
    congrArg (·.2.1) heq
  exact ⟨by
    rw [hsC_eq]
    exact simRecvStepC_deliver_preserves_evictedSpurHistGameInv_of_simInvCXLazy P K hspqr_eq ℓ Dh
      encPt encT decT idOf hinj lam qep q r w_rem hInv_top Q w sC (g, false) hInv.1 hInv.2,
    evictedSpurSimInvLazy_deliver_step P K hspqr_eq InvPQ hInv_top ℓ Dh encPt encT decT idOf hinj
      hdec lam qep q r' r w_rem hS hr Q w sC g tr hInv.1 hInv.2 z hz⟩

omit [SampleableType Pt] [DecidableEq Pt] in
theorem lFig8_send_not_inWin_indep_coin
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (st : Fig8St Pt) (t : ℕ)
    (hst_id : st.id = Q) (htcur : st.tcur = t) (hsends : Q.sendsIn t = true)
    (pm : LibsignalMsgPublicPart × Plain ℓ) (c₁ c₂ : BitVec 256) :
    (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st pm c₁ =
    (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st pm c₂ := by
  have hnot_succ : st.id.sendsIn (st.tcur + 1) = false := by
    rw [hst_id, htcur]
    exact sendsIn_succ_of_sendsIn Q t hsends
  unfold lFig8 SM.Construction.scheme SM.Construction.send
  dsimp only
  rw [hnot_succ]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- Same-epoch sends in `kemFailSendStep` preserve `EvictedSpurHistSimInvLazy`. -/
theorem kemFailSendStep_same_epoch_preserves_evictedSpurHistSimInvLazy
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (Inv : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, Inv n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r' r w_rem : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32)
    (hr : r' < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r_coin : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r w_rem sC g)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (z : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin).run
      (sC, (g, false), tr))) :
    EvictedSpurHistSimInvLazy P K Inv ℓ Dh encPt encT idOf lam qep q r' w_rem z.2.1 z.2.2.1.1 := by
  have hr0 : 0 < r := Nat.zero_lt_of_lt hr
  rcases hInv.2 with ⟨x₀, s_R, ec, winBefore, epExp, hinv, hspur_lazy⟩
  rcases kemFailSendStep_support_eq_simSendStep P K Inv ℓ Dh encPt encT decT idOf lam qep q r hS
      hr0 Q m₀ chal r_coin s_R sC g tr hinv.hsim.hmeta (hinv.hsim.hpqInv Q) z hz with
    ⟨_, hsC_eq, hg_eq⟩ | ⟨hg_win_f, hnoBob, s₁, hep, hsafeCh, rq, c_cka, _, hz_eq⟩
  · have hg1_eq : z.2.2.1.1 = g := congrArg Prod.fst hg_eq
    rw [hsC_eq, hg1_eq]
    exact ⟨hInv.1, x₀, s_R, ec, winBefore, epExp,
      simInvCXLazy_mono_r hinv (Nat.le_of_lt hr), hspur_lazy⟩
  · have hg_clear : { g with win := false } = g := by cases g; simp_all
    rw [hg_clear] at hinv hspur_lazy
    rcases c7_sendsIn_of_inWin_false sC.base.mir Q hnoBob hinw with ⟨hsends, ht_ge1⟩
    have hsends_succ : Q.sendsIn (sC.base.mir.epoch Q + 1) = false :=
      sendsIn_succ_of_sendsIn Q (sC.base.mir.epoch Q) hsends
    rcases c7_epMgmt_of_sendsIn_succ_false sC.base.mir 3 qep Q r_coin.isSome hsends_succ hep with
      ⟨rfl, _⟩
    set pn :=
      if sC.base.mir.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
      else sC.base.pn Q
    obtain ⟨pq', salt, pqMsg, hspqr_send, hmk⟩ :=
      mkPub_eq_some_of_spqrCLocal hS hr0 sC.base Q rq pn (hinv.hsim.hpqInv Q)
    set pub : LibsignalMsgPublicPart :=
      ⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == Party.A && sC.base.unackA then P.addrAB else none⟩
    obtain ⟨s_fig8₁_c, hep_fig8_c, hst_fig8_c, hf8_c⟩ :=
      f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ chal c_cka
        r_coin.isSome sC.base.mir s_R sC.base g hinv.hsim.hmeta hep hsafeCh
    obtain ⟨s_fig8₁, hep_fig8, _, hf8_ec⟩ :=
      f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ chal (ec Q)
        r_coin.isSome sC.base.mir s_R sC.base g hinv.hsim.hmeta hep hsafeCh
    have hs_fig8₁_eq : s_fig8₁_c = s_fig8₁ :=
      Option.some.inj (hep_fig8_c.symm.trans hep_fig8)
    have hsend_coin_eq := lFig8_send_not_inWin_indep_coin P ℓ Dh encPt encT idOf lam Q (g.st Q)
      (sC.base.mir.epoch Q) (hinv.hsim.hst_id Q) (hinv.hsim.htcur Q) hsends
      (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka (ec Q)
    have hf8_1_c : (chal.elim
        (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
          (pub, m₀) c_cka r_coin.isSome g)
        (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka r_coin.isSome g)).1 =
        some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
          (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka).2 :=
      congrArg Prod.fst hf8_c
    have hf8_1_ec : (chal.elim
        (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
          (pub, m₀) (ec Q) r_coin.isSome g)
        (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          SM.Config.h1 Q (pub, m₀) (pub, m₁) (ec Q) r_coin.isSome g)).1 =
        some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
          (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) (ec Q)).2 :=
      congrArg Prod.fst hf8_ec
    have hsim_c := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ chal
      r_coin.isSome sC.base.mir rq c_cka sC.base g pq' pub _ hmk hf8_1_c
    have hsim_ec := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ chal
      r_coin.isSome sC.base.mir rq (ec Q) sC.base g pq' pub _ hmk hf8_1_ec
    have hcka_eq :
        simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r_coin.isSome sC.base.mir rq c_cka
          (sC.base, g) =
        simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r_coin.isSome sC.base.mir rq (ec Q)
          (sC.base, g) := by
      rw [hsim_c, hsim_ec, hf8_c, hf8_ec, hs_fig8₁_eq, hsend_coin_eq]
    dsimp only at hz_eq
    rw [hcka_eq] at hz_eq
    subst hz_eq
    dsimp only
    have hpres := c7_simSendStep_preserves_simInvCLazy_at_ec P Inv ℓ Dh hDh encPt encT decT idOf
      hX hD hrt hid lam qep q r hS hq32 hr0 Q m₀ chal r_coin.isSome sC.base.mir rq
      x₀ s_R sC.base g ec winBefore epExp hinv.hsim hnoBob hep hsafeCh hinv.hsim.hcoll
    set res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r_coin.isSome sC.base.mir rq
      (ec Q) (sC.base, g)
    set sC' := cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1
    have hbase : sC'.base = res.2.1 :=
      c7_cxSend_base P Dh encPt encT idOf lam Q sC res.2.1 res.1
    rcases hpres.2.2.1 hinv.huniq hinv.hidx with ⟨huniq', hidx'⟩
    rcases hpres.2.2.2 sC rfl hinv.hkept hinv.hsync with ⟨hkept', hsync'⟩
    have hcx_sub1 : SimInvCXLazy P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ _ sC' res.2.2 _
        winBefore epExp :=
      ⟨hbase ▸ hpres.1, hbase ▸ huniq', hkept', hbase ▸ hidx', hsync'⟩
    have hres_win : { res.2.2 with win := false } = res.2.2 := by
      have hw := hcx_sub1.hsim.hmeta.hwin_fig8
      revert hw; cases res.2.2; simp_all
    have hcx := simInvCXLazy_mono_r (hres_win.symm ▸ hcx_sub1) (Nat.le_sub_one_of_lt hr)
    have hres_2_1 : res.2.1 = _ := congrArg (·.2.1) hsim_ec
    obtain ⟨_, _, _, hinw_f⟩ := hinv.hsim.hspur Q
    rcases hinw_f hinw with ⟨_, hpos_ep, v, hvS, _⟩
    rcases hpos_ep (by omega) with ⟨_, hTcur⟩
    obtain ⟨seed, i, hc_aead⟩ :=
      lFig8_send_eq_lAead_not_inWin P ℓ Dh encPt encT idOf lam epExp Q (g.st Q)
        (sC.base.mir.epoch Q) (hinv.hsim.hst_id Q) (hinv.hsim.htcur Q) hsends hTcur v hvS
        pub (chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) (ec Q)
    rcases hinv.hsim.hpqInv Q with ⟨n_pq, _, hI_pq⟩
    rcases hInv_top n_pq (sC.base.pq Q) hI_pq with ⟨w_top, hw_top⟩
    have hsender : Party.senderOf (sC.base.mir.epoch Q) = Q := by
      cases Q <;> simp [Party.sendsIn, Party.senderOf] at hsends ⊢ <;> omega
    have hpq' : sC'.base.pq = Function.update sC.base.pq Q pq' := by rw [hbase, hres_2_1]
    have hep' : sC'.base.mir.epoch = sC.base.mir.epoch := by rw [hbase, hres_2_1]; rfl
    have hhon' : sC'.base.honest =
        (LibsignalSim.toWire
          ((sC.base.mir.epoch Q, some (Dh.dh (epExp (sC.base.mir.epoch Q)) Dh.base)),
            (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
              seed (i, (sC.base.mir.epoch Q, some (Dh.dh (epExp (sC.base.mir.epoch Q)) Dh.base)))
              (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)))),
         ((sC.base.mir.epoch Q, some (Dh.dh (epExp (sC.base.mir.epoch Q)) Dh.base)),
            (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
              seed (i, (sC.base.mir.epoch Q, some (Dh.dh (epExp (sC.base.mir.epoch Q)) Dh.base)))
              (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀))))) ::
          sC.base.honest := by
      rw [hbase, hres_2_1, ← hc_aead]
    have hgame' : EvictedSpurHistGameInv P K qep w_rem sC' :=
      evictedSpurHistGameInv_send_same_epoch hspqr_eq hInv.1 hsender hspqr_send hpq' hhon'
        (fun R t' ht' => by rwa [hbase, hres_2_1] at ht') hw_top
        (lAead_enc_parse_pqRatchet P ℓ encT idOf hrt Q sC.base.unackA (sC.base.pq Q) pq' rq salt
          seed i (sC.base.mir.epoch Q) (Dh.dh (epExp (sC.base.mir.epoch Q)) Dh.base) pub
          (chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) rfl hspqr_send)
        (fun w₀ c₀ hmem hsender₀ => hsender₀ ▸ (hinv.hsim.hhon (w₀, c₀) hmem).2.2.2)
        (fun R => by rw [hep'])
    refine ⟨hgame', evictedSpurSimInvLazy_of_step hInv_top hgame'.hhist hcx hspur_lazy ?_⟩
    intro R hinw'
    have hepR : sC'.base.mir.epoch R = sC.base.mir.epoch R := congrFun hep' R
    have hinwR : inReceiveOnlyEpoch sC.base.mir R = false := by
      unfold inReceiveOnlyEpoch at hinw' ⊢; rwa [hepR] at hinw'
    have hev_eq : Proofs.Refinement.evictAccEpoch sC'.base.mir R =
        Proofs.Refinement.evictAccEpoch sC.base.mir R := by
      unfold Proofs.Refinement.evictAccEpoch; rw [hinw', hinwR, hepR]
    have hev_le : Proofs.Refinement.evictAccEpoch sC.base.mir R ≤ sC.base.mir.epoch Q :=
      evictAccEpoch_le_of_inWin_false hinw
        (fun P => ⟨(hinv.hsim.hep_adj P).1, fun _ => (hinv.hsim.hep_adj P).2⟩) R
    refine ⟨hepR, fun _ h => by rw [hhon']; exact List.mem_cons_of_mem _ h, ?_, ?_,
      fun rk_b T_b hb => ?_⟩
    · rw [hhon', hev_eq]
      exact Proofs.Refinement.honestBeforeEpoch_cons_of_le sC.base.honest _ _
        (Proofs.Refinement.evictAccEpoch sC.base.mir R) hev_le
    · rw [hpq']
      by_cases hRQ : R = Q
      · subst hRQ; rw [Function.update_self]; exact .send (.refl _) (hspqr_eq ▸ hspqr_send)
      · rw [Function.update_of_ne hRQ]; exact .refl _
    · rw [hres_win, hbase]
      exact hpres.2.1 R rk_b T_b hb

end CorrSimInvCX

end KemFailSimCoupling

end CryptoVerification.LibsignalSession.HeadlineV1

namespace CryptoVerification.E2E.Signed

open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs
open CBC

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

end CryptoVerification.E2E.Signed

namespace CryptoVerification.LibsignalSession.HeadlineV1

section MoveCompat

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal
  (Encaps1Total spqrV1Send_msg_len_lt spqrV1SessionB_sendCorrectQ)
open CryptoVerification.E2E (partyIdentityKey paramsIdsWithSpqr)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs
open CryptoGames.LibsignalSM.Proofs.Refinement
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

section MoveCompatNoSamplePt

variable {Pt : Type} [DecidableEq Pt] [Zero Pt]

theorem evalDist_kemFailSimImpl_cand_some_eq_zero {PQ α : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
      α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    {p : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 32}
    (hcand : tr.cand = some p) :
    𝒟[(simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) oa).run (sC, gh, tr) >>=
      fun z => pure (z.2.2.1.2 && !z.2.2.2.cand.isSome)] {true} = 0 := by
  have hcongr :
      𝒟[(simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) oa).run (sC, gh, tr) >>=
        fun z => pure (z.2.2.1.2 && !z.2.2.2.cand.isSome)] =
      𝒟[(simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) oa).run (sC, gh, tr) >>=
        fun _ => (pure false : ProbComp Bool)] := by
    refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
    have hz_cand := (simulateQ_kemFailSimImpl_cand_valid P K ℓ Dh encPt encT decT idOf lam qep oa
      sC gh tr z hz).2 p hcand
    simp [hz_cand]
  rw [hcongr, OracleComp.evalDist_bind_const]
  simp

end MoveCompatNoSamplePt

section MoveCompatWithSamplePt

open CryptoGames.LibsignalSM.Proofs.Correctness

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

omit [DecidableEq Pt] [SampleableType Pt] in
private theorem c8_simInvCX_mono_r {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r r' : ℕ)
    (hle : r' ≤ r) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : Proofs.Refinement.SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp) :
    Proofs.Refinement.SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R sC s_fig8 ec winBefore epExp :=
  { hinv with
    hsim :=
      { hinv.hsim with
        hamb := by have := hinv.hsim.hamb; omega
        hamb_strict := fun h => by have := hinv.hsim.hamb_strict h; omega
        hidx_le := fun Q => by have := hinv.hsim.hidx_le Q; omega
        hhon_len := by have := hinv.hsim.hhon_len; omega
        hhon := hinv.hsim.hhon
        hpqInv := fun Q => Proofs.Refinement.InvB.mono hle (hinv.hsim.hpqInv Q) } }

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
private theorem evictedSpurSimInv_spurBadList_congr {ℓ : ℕ}
    {P : Params (List (BitVec 8)) (BitVec 512)}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {sC sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ} {epExp : ℕ → BitVec 256}
    (hhon : sC'.base.honest = sC.base.honest)
    (hep : sC'.base.mir.epoch = sC.base.mir.epoch)
    (hno_spur : ∀ Q w_acc rk_base T_base,
      inReceiveOnlyEpoch sC.base.mir Q = false →
      spurBadList P encPt Dh Q rk_base T_base
        (Proofs.Refinement.evictedSpurCandList P epExp w_acc
          (Proofs.Refinement.honestBeforeEpoch sC.base.honest
            (Proofs.Refinement.evictAccEpoch sC.base.mir Q)))
        (epExp (sC.base.mir.epoch Q)) = false) :
    ∀ Q w_acc rk_base T_base,
      inReceiveOnlyEpoch sC'.base.mir Q = false →
      spurBadList P encPt Dh Q rk_base T_base
        (Proofs.Refinement.evictedSpurCandList P epExp w_acc
          (Proofs.Refinement.honestBeforeEpoch sC'.base.honest
            (Proofs.Refinement.evictAccEpoch sC'.base.mir Q)))
        (epExp (sC'.base.mir.epoch Q)) = false := by
  intro Q w_acc rk_base T_base hinw'
  have hinw : inReceiveOnlyEpoch sC.base.mir Q = false := by
    unfold inReceiveOnlyEpoch at hinw' ⊢
    rwa [hep] at hinw'
  have hev : Proofs.Refinement.evictAccEpoch sC'.base.mir Q =
      Proofs.Refinement.evictAccEpoch sC.base.mir Q := by
    unfold Proofs.Refinement.evictAccEpoch inReceiveOnlyEpoch
    rw [hep]
  rw [hhon, hev, hep]
  exact hno_spur Q w_acc rk_base T_base hinw


omit [SampleableType Pt] in
private theorem evictedSpurSimInv_corr_of_simInvCX
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r' r : ℕ)
    (Q : Party) (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hEx : EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q r sC g)
    (hsim_corr : ∀ x₀ s_R ec winBefore epExp,
      Proofs.Refinement.SimInvCX P InvPQ ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC
        { g with win := false } ec winBefore epExp →
      ∀ z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
          (.inr (.inr Q))).run (sC, (g, false), tr)),
        z.2.2.2.cand = none →
        ∃ s_R' ec' winBefore',
          Proofs.Refinement.SimInvCX P InvPQ ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
            z.2.1 { z.2.2.1.1 with win := false } ec' winBefore' epExp)
    (z : Option (GhostState (List (BitVec 8))) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q))).run (sC, (g, false), tr)))
    (hcand : z.2.2.2.cand = none) :
    EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q r' z.2.1 z.2.2.1.1 := by
  rcases hEx with ⟨x₀, s_R, ec, winBefore, epExp, hsim, hno_spur⟩
  obtain ⟨s_R', ec', winBefore', hsim'⟩ := hsim_corr x₀ s_R ec winBefore epExp hsim z hz hcand
  change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q))).run
    (sC, (g, false), tr)) at hz
  rw [runProbeStep_run, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hw_step : (w.1.1, (w.1.2, w.2)) ∈ support
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) (sC, (g, false))) := by
    change (w.1.1, (w.1.2, w.2)) ∈ support
      ((((LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q)).run
        sC).run (g, false)) >>= fun r => pure (r.1.1, (r.1.2, r.2)))
    rw [MonadAttach.mem_support_bind]
    exact ⟨w, hw, by simp⟩
  obtain ⟨hhon_eq, _, hep_eq, _, _⟩ :=
    stepSimCNone_corr_invariants P ℓ Dh encPt encT decT idOf lam qep Q (sC, (g, false))
      (w.1.1, (w.1.2, w.2)) hw_step
  exact ⟨x₀, s_R', ec', winBefore', epExp, hsim',
    evictedSpurSimInv_spurBadList_congr hhon_eq hep_eq hno_spur⟩

private theorem kemFailSimImpl_inject_preserves_evictedSpurHistGameInv_of_simInvCX
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    {InvPQ : ℕ → List (BitVec 8) → Prop} (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q r w_rem : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistGameInv P K qep w_rem sC)
    (hEx : EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q r sC gh.1)
    (z : Option (SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inr (Q, w))))).run (sC, gh, tr))) :
    EvictedSpurHistGameInv P K qep w_rem z.2.1 := by
  rcases hEx with ⟨x₀, s_R, ec, winBefore, epExp, hsim, _⟩
  change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000)
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false))).run
    (sC, gh, tr)) at hz
  rw [runProbeStep_run, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w_out, hw_out, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hw_step : (w_out.1.1, (w_out.1.2, w_out.2)) ∈ support
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) (sC, gh)) := by
    change (w_out.1.1, (w_out.1.2, w_out.2)) ∈ support
      ((((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000)
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false)).run
        sC).run gh) >>= fun r => pure (r.1.1, (r.1.2, r.2)))
    rw [MonadAttach.mem_support_bind]
    exact ⟨w_out, hw_out, by simp⟩
  rw [stepSimCNone_inject_eq, support_pure, Set.mem_singleton_iff] at hw_step
  have hbase_eq : w_out.1.2.base =
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w false (sC, gh)).2.1.base := by
    rw [← hw_step]
  obtain ⟨_, hep_eq, hhist'⟩ :=
    simRecvStepC_inject_preserves_spqrHistoryInv_and_epoch_of_simInvC P K hspqr_eq ℓ Dh encPt encT
      decT idOf lam qep Q w (sC, gh) hsim.hsim.hcomp hInv.hhist
  refine ⟨hbase_eq.symm ▸ hhist', ?_⟩
  have hrem : remSendEpochs qep w_out.1.2.base.mir = remSendEpochs qep sC.base.mir := by
    unfold remSendEpochs
    rw [hbase_eq, hep_eq]
  exact hrem ▸ hInv.hw_rem

private theorem simCorrPureC_preserves_simInvC
    (P : Params (List (BitVec 8)) (BitVec 512)) (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r' r : ℕ) (hr : r' ≤ r)
    (Q : Party) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard_f :
      (!(sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) =
        false) :
    let s := sC.base
    let figSt := s_fig8.st Q
    let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match figSt.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    let s' : SimState (List (BitVec 8)) Pt ℓ :=
      { s with mir := s.mir.afterCorr Q, chains := chains }
    SimInvC P (InvB Inv q r') ℓ Dh encPt encT qep q r' x₀ (s_R.afterCorr Q) s'
      (s_fig8.afterCorr Q) ec winBefore epExp := by
  intro s figSt chains s'
  have hcorr_mir : s.mir.corrAllowed Q = true := by
    revert hguard_f; cases s.mir.corrAllowed Q <;> simp
  have hinw_mir : inReceiveOnlyEpoch s.mir Q = false := by
    revert hguard_f; cases inReceiveOnlyEpoch s.mir Q <;> simp
  have hB0 : Q = .B → s.mir.epoch .B = 0 → figSt.γ = .exp x₀ := by
    intro hQB hep0
    subst hQB
    rcases hinv.hsim.hspur .B with ⟨_, _, _, hnot_inw, _⟩
    have hγ := (hnot_inw hinw_mir).1
    rw [hep0, hinv.hsim.hepExp0] at hγ
    exact hγ
  have hres_eq : resolveSim (encT (Dh.dh x₀ Dh.base)) s' =
      { resolveSim (encT (Dh.dh x₀ Dh.base)) s with mir := s.mir.afterCorr Q } :=
    resolveSim_afterCorr_B_epoch0 Dh encT (encT (Dh.dh x₀ Dh.base)) s Q figSt x₀ rfl hB0
  have hchains_ep : ∀ R, (chains R).map (·.epoch) = (s.chains R).map (·.epoch) := by
    intro R
    dsimp only [chains]
    split
    · cases figSt.γ with
      | pub _ => rfl
      | exp x =>
        dsimp only
        cases R with
        | A =>
          rw [Function.update_self]
          exact c8_map_epoch_resolve_list (s.chains .A) (encT (Dh.dh x Dh.base))
        | B =>
          rw [Function.update_of_ne (by decide : Party.B ≠ Party.A)]
    · rfl
  exact
    { hmeta := hinv.hsim.hmeta.afterCorr_preserves Q chains
      hcomp := comp_healedBy_false_afterCorr s.mir 3 Q hcorr_mir hinv.hsim.hcomp
      hec := hinv.hsim.hec
      hwinBefore := hinv.hsim.hwinBefore
      hamb := by have := hinv.hsim.hamb; dsimp [s', s]; omega
      hamb_strict := fun h => by have := hinv.hsim.hamb_strict h; dsimp [s', s]; omega
      hidx_le := fun R => by
        change sC.base.mir.idx R + r' ≤ q
        have := hinv.hsim.hidx_le R; omega
      hhon_len := by have := hinv.hsim.hhon_len; dsimp [s', s]; omega
      hep_le := hinv.hsim.hep_le
      hep_adj := hinv.hsim.hep_adj
      hst_R := by
        intro R
        change s_R.st R =
          expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' R (s_fig8.st R) (ec R)
        rw [hinv.hsim.hst_R R]
        refine c8_expectedGhost_congr P Dh encPt (encT (Dh.dh x₀ Dh.base)) s s' R
          (s_fig8.st R) (ec R) rfl ?_ (fun _ => rfl) rfl rfl rfl
        rw [hres_eq]
      hst_id := hinv.hsim.hst_id
      htcur := hinv.hsim.htcur
      hepExp0 := hinv.hsim.hepExp0
      hspur := by
        intro R
        rcases hinv.hsim.hspur R with ⟨rk_base, T_base, h1, h2, h3⟩
        refine ⟨rk_base, T_base, h1, h2, ?_⟩
        intro wc hwc hsend hep_le hnot_mem
        rw [show s'.chains = chains from rfl, hchains_ep R] at hnot_mem
        exact h3 wc hwc hsend hep_le hnot_mem
      hchainsA := by
        dsimp only [s', chains]
        split
        · cases figSt.γ with
          | pub _ => exact hinv.hsim.hchainsA
          | exp x =>
            dsimp only
            rw [Function.update_self]
            exact chainsEpochInvA_resolve hinv.hsim.hchainsA (encT (Dh.dh x Dh.base))
        · exact hinv.hsim.hchainsA
      hchainsA_ep := by
        change (chains .A).map (·.epoch) = epListA (s.mir.epoch .A / 2)
        rw [hchains_ep .A]
        exact hinv.hsim.hchainsA_ep
      hchainsB_ep := by
        change (chains .B).map (·.epoch) = epListB ((s.mir.epoch .B + 1) / 2)
        rw [hchains_ep .B]
        exact hinv.hsim.hchainsB_ep
      hchainsB_none := by
        have hB : chains .B = s.chains .B := by
          dsimp only [chains]
          split
          · cases figSt.γ with
            | pub _ => rfl
            | exp _ => simp
          · rfl
        dsimp only [s']
        rw [hB]
        exact hinv.hsim.hchainsB_none
      hchains_sync := by
        intro R g' hg'
        by_cases hcond : (Q == Party.B && s.mir.epoch Party.B == 0) = true
        · simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          rcases hcond with ⟨hQB, hep0⟩
          have hγ0 : figSt.γ = .exp x₀ := hB0 hQB hep0
          have hchains_eq : chains = Function.update s.chains Party.A ((s.chains Party.A).map
              fun g => if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) }
                else g) := by
            simp [chains, hQB, hep0, hγ0]
          cases R with
          | B =>
            change g' ∈ chains .B at hg'
            rw [hchains_eq, Function.update_of_ne (by decide : Party.B ≠ Party.A)] at hg'
            exact hinv.hsim.hchains_sync .B g' hg'
          | A =>
            change g' ∈ chains .A at hg'
            rw [hchains_eq, Function.update_self, List.mem_map] at hg'
            rcases hg' with ⟨g, hg, rfl⟩
            rcases hinv.hsim.hchains_sync .A g hg with ⟨hgep, hgsend, hgkey, v, hvR, hsync⟩
            have heq_ep :
                (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) }
                  else g).epoch = g.epoch := by split <;> rfl
            have heq_key :
                (if (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) }
                    else g).key.isNone then
                  some (encT (Dh.dh x₀ Dh.base))
                else (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) }
                    else g).key) =
                (if g.key.isNone then some (encT (Dh.dh x₀ Dh.base)) else g.key) := by
              cases hk : g.key <;> simp [hk]
            have hsync' :
                ChainSync (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) }
                  else g) v := by
              split
              · exact ⟨hsync.last_eq, hsync.last_lt, hsync.nodup_skipped,
                  hsync.len_skipped, hsync.mem_skipped, hsync.skippedKeys_le⟩
              · exact hsync
            rw [heq_ep, heq_key]
            exact ⟨hgep, hgsend, hgkey, v, hvR, hsync'⟩
        · have hchains_eq : chains = s.chains := ite_eq_right hcond
          change g' ∈ chains R at hg'
          rw [hchains_eq] at hg'
          exact hinv.hsim.hchains_sync R g' hg'
      hhon := hinv.hsim.hhon
      htrans_hon := hinv.hsim.htrans_hon
      hcoll := hinv.hsim.hcoll
      hcorrB0 := hcorrB0_afterCorr hB0 hinv.hsim.hcorrB0
      hpqInv := fun R => InvB.mono hr (hinv.hsim.hpqInv R) }

private theorem simCorrPureC_preserves_simInvCX_of_guard_false
    (P : Params (List (BitVec 8)) (BitVec 512)) (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r' r : ℕ) (hq32 : q < 2 ^ 32) (hr : r' ≤ r)
    (Q : Party) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hguard_f :
      (!(sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) =
        false) :
    let s := sC.base
    let figSt := s_fig8.st Q
    let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match figSt.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    let g_snap := toGhost (P := P) { s with chains := chains } Q figSt
    let s' : SimState (List (BitVec 8)) Pt ℓ :=
      { s with mir := s.mir.afterCorr Q, chains := chains }
    let sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
      { sC with base := s',
                kept := Function.update sC.kept Q (Kept.ofSt figSt),
                snaps := (Q, s.mir.epoch Q, g_snap) :: sC.snaps }
    SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ (s_R.afterCorr Q) sC'
      (s_fig8.afterCorr Q) ec winBefore epExp := by
  intro s figSt chains g_snap s' sC'
  have hinw_mir : inReceiveOnlyEpoch s.mir Q = false := by
    revert hguard_f; cases inReceiveOnlyEpoch s.mir Q <;> simp
  have hnospk_mir : SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q = true := by
    revert hguard_f; cases SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q <;> simp
  refine ⟨simCorrPureC_preserves_simInvC P Inv ℓ Dh encPt encT idOf lam qep q r' r hr Q x₀ s_R
      sC s_fig8 ec winBefore epExp hinv hguard_f,
    hinv.huniq,
    c8_keptInv_corr P Dh encPt encT idOf lam Q sC s' ((Q, s.mir.epoch Q, g_snap) :: sC.snaps)
      s_fig8 hinv.hkept rfl (fun _ _ => rfl),
    hinv.hidx, ?_⟩
  intro hwin'
  rcases hinv.hsync hwin' with ⟨K, rk, hK⟩
  refine ⟨K, rk, { hK with hsnaps := ?_ }⟩
  intro snap hsnap
  rcases List.mem_cons.mp hsnap with rfl | hsnap
  · have hsends_Q : Q.sendsIn (s.mir.epoch Q) = true := by
      unfold inReceiveOnlyEpoch at hinw_mir
      simpa using hinw_mir
    have hchains_Q : chains Q = s.chains Q := by
      cases Q with
      | A => dsimp [chains]
      | B =>
        dsimp [chains]
        split
        · cases figSt.γ with
          | pub _ => rfl
          | exp _ => simp
        · rfl
    have hno_none_Q : ∀ g ∈ s.chains Q, g.key.isNone = false := by
      cases Q with
      | B => exact hinv.hsim.hchainsB_none
      | A =>
        have h10 : 10 ≤ s.mir.epoch .A := by
          unfold SM.noAliceCorrWhileAliceBelowEpoch10 at hnospk_mir
          simpa using hnospk_mir
        exact chainsEpochInvA_no_none hinv.hsim.hchainsA h10
    rcases hinv.hsim.hspur Q with ⟨rk_base, T_base, _, hnot_inw, _⟩
    rcases hnot_inw hinw_mir with ⟨hγ_Q, _, vS, hvS, hvS_last⟩
    have hidx_Q_lt : vS.lastIndex < 2 ^ 32 := by
      have := hinv.hsim.hidx_le Q
      omega
    have hsend_Q : vS.chainKey = lChainAt P.C.F (K (s.mir.epoch Q)) vS.lastIndex := by
      have h := hK.hsend Q vS hvS (by rw [hinv.hsim.htcur Q]; exact hsends_Q)
      rwa [hinv.hsim.htcur Q] at h
    refine ⟨hsends_Q, ?_, ?_, ?_, ?_, ?_⟩
    · change s.mir.epoch Q ≤ max (s_fig8.st .A).tcur (s_fig8.st .B).tcur
      rw [hinv.hsim.htcur .A, hinv.hsim.htcur .B]
      cases Q with
      | A => exact Nat.le_max_left _ _
      | B => exact Nat.le_max_right _ _
    · change figSt.root = rk (s.mir.epoch Q)
      rw [← hinv.hsim.htcur Q]
      exact hK.hroot Q
    · refine ⟨vS.lastIndex, hidx_Q_lt, ?_⟩
      dsimp only [g_snap, toGhost, figSt, s]
      rw [hγ_Q, hvS]
      dsimp only
      rw [hsend_Q]
    · intro rc_ch hrc_ch
      dsimp only [g_snap, toGhost] at hrc_ch
      rw [hchains_Q, List.mem_map] at hrc_ch
      rcases hrc_ch with ⟨g, hg, rfl⟩
      rcases hinv.hsim.hchains_sync Q g hg with ⟨hgep, _, hgkey, v, hvR, hsync_g⟩
      have hnone_g : g.key.isNone = false := hno_none_Q g hg
      rw [hnone_g, ite_eq_right Bool.false_ne_true] at hgkey
      rcases hK.hrecv Q g.epoch v hvR with ⟨hv_ck, hv_sk⟩
      change ∃ ep ≤ s.mir.epoch Q, _
      refine ⟨g.epoch, hgep, ?_, ?_, ?_⟩
      · dsimp only [figSt]
        rw [hvR, hgkey]
        rfl
      · refine ⟨v.lastIndex, hsync_g.last_lt, ?_⟩
        dsimp only [figSt]
        rw [hvR]
        dsimp only
        rw [hv_ck]
      · intro mk hmk
        dsimp only [figSt] at hmk
        rw [hvR] at hmk
        dsimp only at hmk
        rw [List.mem_filterMap] at hmk
        rcases hmk with ⟨j, hj, hmap_j⟩
        cases hlk : v.skippedKeys.lookup j with
        | none => rw [hlk] at hmap_j; cases hmap_j
        | some seed =>
          rw [hlk, Option.map_some, Option.some.injEq] at hmap_j
          subst hmap_j
          dsimp only
          rcases hsync_g.mem_skipped j hj with ⟨hj1, hj_le, _⟩
          have hj_lt : j - 1 < 2 ^ 32 := by have := hsync_g.last_lt; omega
          have hctr : (BitVec.ofNat 32 (j - 1)).toNat + 1 = j := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj_lt]
            omega
          have hseed : seed = lSeedAt P.C.F (K g.epoch) j :=
            hv_sk (j, seed) (c8_mem_of_lookup hlk)
          rw [hctr, hseed]
    · intro h2
      have h2' : 2 ≤ sC.base.mir.epoch Q := h2
      have hlast_ep : ((s.chains Q).map (·.epoch)).getLast? = some (s.mir.epoch Q - 1) := by
        dsimp only [s]
        cases Q with
        | A =>
          rw [hinv.hsim.hchainsA_ep, c8_epListA_getLast]
          congr 1
          have hmod : sC.base.mir.epoch .A % 2 = 1 := by
            simpa [Party.sendsIn, s] using hsends_Q
          omega
        | B =>
          have hmod : sC.base.mir.epoch .B % 2 = 0 := by
            simpa [Party.sendsIn, s] using hsends_Q
          rw [hinv.hsim.hchainsB_ep, c8_epListB_getLast (by omega)]
          congr 1
          omega
      rw [List.getLast?_map, Option.map_eq_some_iff] at hlast_ep
      rcases hlast_ep with ⟨g_last, hglast, hg_ep⟩
      have hmem_last : g_last ∈ s.chains Q := List.mem_of_getLast? hglast
      rcases hinv.hsim.hchains_sync Q g_last hmem_last with
        ⟨_, _, hgkey_last, v_last, hvR_last, _⟩
      have hnone_last : g_last.key.isNone = false := hno_none_Q g_last hmem_last
      rw [hnone_last, ite_eq_right Bool.false_ne_true, hg_ep] at hgkey_last
      dsimp only [g_snap, toGhost, figSt]
      rw [hchains_Q, List.getLast?_map, hglast, Option.map_some]
      refine ⟨_, rfl, ?_⟩
      rw [hvR_last]
      dsimp only
      rw [hgkey_last]
      rfl
  · exact hK.hsnaps snap hsnap

private theorem kemFailSimImpl_corr_preserves_simInvCX
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r' r : ℕ) (hq32 : q < 2 ^ 32) (hr : r' ≤ r)
    (Q : Party) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false }
      ec winBefore epExp)
    (z : Option (GhostState (List (BitVec 8))) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q))).run (sC, (g, false), tr))) :
    ∃ s_R' ec' winBefore',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
        z.2.1 { z.2.2.1.1 with win := false } ec' winBefore' epExp := by
  change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q))).run
    (sC, (g, false), tr)) at hz
  rw [runProbeStep_run, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w, hw, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hw_step : (w.1.1, (w.1.2, w.2)) ∈ support
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) (sC, (g, false))) := by
    change (w.1.1, (w.1.2, w.2)) ∈ support
      ((((LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q)).run
        sC).run (g, false)) >>= fun r => pure (r.1.1, (r.1.2, r.2)))
    rw [MonadAttach.mem_support_bind]
    exact ⟨w, hw, by simp⟩
  rw [c8_stepSimCNone_corr_eq, support_pure, Set.mem_singleton_iff] at hw_step
  have hstop := hinv.hsim.hmeta.hstop
  have hwin_mir := hinv.hsim.hmeta.hwin_mir
  by_cases hguard :
      (!(sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) =
        true
  · have hcorr_eq : c8_simCorrPureC P Dh encT Q (sC, (g, false)) = (none, (sC, (g, false))) := by
      unfold c8_simCorrPureC
      dsimp only
      rw [hstop, ite_eq_right Bool.false_ne_true, hwin_mir, Bool.false_or, hguard,
        ite_eq_left rfl]
    rw [hcorr_eq] at hw_step
    have hsC_eq : w.1.2 = sC := congrArg (·.2.1) hw_step
    have hg_eq : w.2.1 = g := congrArg (·.2.2.1) hw_step
    dsimp only
    rw [hsC_eq, hg_eq]
    exact ⟨s_R, ec, winBefore,
      c8_simInvCX_mono_r P Inv ℓ Dh encPt encT idOf lam qep q r r' hr x₀ s_R sC
        { g with win := false } ec winBefore epExp hinv⟩
  · have hguard_f :
        (!(sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) =
          false := Bool.eq_false_iff.mpr hguard
    cases hg_win : g.win
    · have hg_eq0 : { g with win := false } = g := by cases g; simp_all
      rw [hg_eq0] at hinv
      have hcorr_fig8 := hinv.hsim.hmeta.corrAllowed_fig8 Q
      have hcorr_mir : sC.base.mir.corrAllowed Q = true := by
        revert hguard_f; cases sC.base.mir.corrAllowed Q <;> simp
      have hcorrPure_fig8 : corrPure Q g = (some (g.st Q), g.afterCorr Q) := by
        unfold corrPure
        rw [hg_win, hcorr_fig8, hcorr_mir]
        rfl
      have hcorr_eq : (c8_simCorrPureC P Dh encT Q (sC, (g, false))).2 =
          (let s := sC.base
           let figSt := g.st Q
           let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
               match figSt.γ with
               | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
                   if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
               | _ => s.chains
             else s.chains
           let g_snap := toGhost (P := P) { s with chains := chains } Q figSt
           ({ sC with base := { s with mir := s.mir.afterCorr Q, chains := chains },
                      kept := Function.update sC.kept Q (Kept.ofSt figSt),
                      snaps := (Q, s.mir.epoch Q, g_snap) :: sC.snaps },
            g.afterCorr Q, false)) := by
        unfold c8_simCorrPureC
        dsimp only
        rw [hstop, ite_eq_right Bool.false_ne_true, hwin_mir, Bool.false_or, hguard_f,
          ite_eq_right Bool.false_ne_true, hcorrPure_fig8]
        rfl
      have hsC_eq : w.1.2 = (c8_simCorrPureC P Dh encT Q (sC, (g, false))).2.1 :=
        congrArg (·.2.1) hw_step
      have hg_eq : w.2.1 = (c8_simCorrPureC P Dh encT Q (sC, (g, false))).2.2.1 :=
        congrArg (·.2.2.1) hw_step
      have hg_after_eq : { g.afterCorr Q with win := false } = g.afterCorr Q := by
        unfold SM.GameState.afterCorr SM.GameState.leak; cases g; simp_all
      dsimp only
      rw [hsC_eq, hg_eq, hcorr_eq, hg_after_eq]
      exact ⟨s_R.afterCorr Q, ec, winBefore,
        simCorrPureC_preserves_simInvCX_of_guard_false P Inv ℓ Dh encPt encT idOf lam qep q r' r
          hq32 hr Q x₀ s_R sC g ec winBefore epExp hinv hguard_f⟩
    · have hcorrPure_fig8 : corrPure Q g = (none, g) := by
        unfold corrPure
        rw [hg_win]
        rfl
      have hcorr_eq : c8_simCorrPureC P Dh encT Q (sC, (g, false)) = (none, (sC, (g, false))) := by
        unfold c8_simCorrPureC
        dsimp only
        rw [hstop, ite_eq_right Bool.false_ne_true, hwin_mir, Bool.false_or, hguard_f,
          ite_eq_right Bool.false_ne_true, hcorrPure_fig8]
      rw [hcorr_eq] at hw_step
      have hsC_eq : w.1.2 = sC := congrArg (·.2.1) hw_step
      have hg_eq : w.2.1 = g := congrArg (·.2.2.1) hw_step
      dsimp only
      rw [hsC_eq, hg_eq]
      exact ⟨s_R, ec, winBefore,
        c8_simInvCX_mono_r P Inv ℓ Dh encPt encT idOf lam qep q r r' hr x₀ s_R sC
          { g with win := false } ec winBefore epExp hinv⟩

private theorem evictedSpurSimInv_corr_uncond
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r' r : ℕ) (hq32 : q < 2 ^ 32) (hr : r' ≤ r)
    (Q : Party) (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hEx : EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q r sC g)
    (z : Option (GhostState (List (BitVec 8))) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q))).run (sC, (g, false), tr)))
    (hcand : z.2.2.2.cand = none) :
    EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q r' z.2.1 z.2.2.1.1 :=
  evictedSpurSimInv_corr_of_simInvCX P K InvPQ ℓ Dh encPt encT decT idOf lam qep q r' r Q sC g tr
    hEx (fun x₀ s_R ec winBefore epExp hsim z' hz' _ =>
      kemFailSimImpl_corr_preserves_simInvCX P K InvPQ ℓ Dh encPt encT decT idOf lam qep q r' r
        hq32 hr Q x₀ s_R sC g tr ec winBefore epExp hsim z' hz')
    z hz hcand

/-- `corr` queries of `kemFailSimImpl` preserve `EvictedSpurHistSimInv` with probe flag `false`. -/
theorem evictedSpurHistSimInv_corr_step
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r' r w_rem : ℕ)
    (hq32 : q < 2 ^ 32) (hr : r' ≤ r)
    (Q : Party) (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistSimInv P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g)
    (z : Option (GhostState (List (BitVec 8))) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inr Q))).run (sC, (g, false), tr)))
    (hcand : z.2.2.2.cand = none) :
    z.2.2.1.2 = false ∧
    EvictedSpurHistSimInv P K InvPQ ℓ Dh encPt encT idOf lam qep q r' w_rem z.2.1 z.2.2.1.1 :=
  ⟨kemFailSimImpl_corr_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep Q sC g tr z hz,
   kemFailSimImpl_corr_preserves_evictedSpurHistGameInv P K ℓ Dh encPt encT decT idOf lam qep
     w_rem Q sC (g, false) tr hInv.1 z hz,
   evictedSpurSimInv_corr_uncond P K InvPQ ℓ Dh encPt encT decT idOf lam qep q r' r hq32 hr Q sC g
     tr hInv.2 z hz hcand⟩

private theorem simRecvStepCGen_inject_knownChain_preserves_simInvCX
    (P : Params (List (BitVec 8)) (BitVec 512))
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r' r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hr : r' < r)
    (Q : Party) (w : List (BitVec 8)) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false }
      ec winBefore epExp)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : List (BitVec 8)} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    {ci : ℕ}
    (hfind : (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) = some ci)
    (hrej_f : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = false) :
    let i := h.counter.toNat + 1
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let honestC :=
      (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    let ch := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
    let c_mk : Fig8C Pt :=
      match honestC with
      | some c₀ =>
        if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀
        else ((ch.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
      | none => ((ch.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    let r_out := fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false (some ci)
      h.senderRatchetKey pq' honestC c_mk (sC, g, false)
    ∃ s_R' ec' winBefore',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
        r_out.2.1 { r_out.2.2.1 with win := false } ec' winBefore' epExp := by
  intro i ser tag honestC ch c_mk r_out
  cases hg_win : g.win
  · have hg_eq0 : { g with win := false } = g := by cases g; simp_all
    rw [hg_eq0] at hinv
    have hmeta := hinv.hsim.hmeta
    have hpq' : InvB Inv q r pq' := InvB.recv hS (hinv.hsim.hpqInv Q) hspqr
    have htr_mir : (sC.base.mir.inTransit Q.other w).isSome = false := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> simp
    have hsafe_mir : sC.base.mir.safeInj 3 = true := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;>
        cases sC.base.mir.safeInj 3 <;> simp
    have himg : ratchetKeyAdmissible P.codec decT encT w = true := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;>
        cases sC.base.mir.safeInj 3 <;> cases ratchetKeyAdmissible P.codec decT encT w <;> simp
    rcases lOnImage_some_of_parse P decT encT w h body himg hlen hparse with ⟨T, hdecT, hencT⟩
    have hT : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
      rw [hdecT, Option.map_some, Option.getD_some, hencT]
    rcases getElem?_of_findIdx_ghost (sC.base.chains Q) h.senderRatchetKey ci hfind with
      ⟨ch', hch_elem', hch_key'⟩
    have hch_eq : ch = ch' := by simp [ch, hch_elem']
    have hch_elem : (sC.base.chains Q)[ci]? = some ch := by rw [hch_eq, hch_elem']
    have hch_key : ch.key = some h.senderRatchetKey := by rw [hch_eq, hch_key']
    have hch_mem : ch ∈ sC.base.chains Q := List.mem_of_getElem? hch_elem
    rcases hinv.hsim.hchains_sync Q ch hch_mem with ⟨hch_ep_le, _, hch_key_sync, _⟩
    have hch_none : ch.key.isNone = false := by rw [hch_key]; rfl
    rw [hch_none] at hch_key_sync
    simp only [Bool.false_eq_true, ↓reduceIte, hch_key] at hch_key_sync
    have hsrk_eq : h.senderRatchetKey = encT (Dh.dh (epExp ch.epoch) Dh.base) :=
      Option.some.inj hch_key_sync
    let c : Fig8C Pt := ((ch.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    have hmkC : c_mk = c := by
      refine mkC_eq_raw_of_honest_epochC P (InvB Inv q r) Dh encT decT hinj epExp sC.base Q w h body
        (sC.base.pq Q) pq' salt ch.epoch hdecT hencT
        (fun wc hwc => (hinv.hsim.hhon wc hwc).1) hparse hspqr hpan ?_ (hinv.hsim.hpqInv Q)
      intro wc hwc hwc_w _
      rcases wc with ⟨w₀, c₀⟩
      dsimp only at hwc_w ⊢
      subst w₀
      rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp
        (hinv.hsim.hhon (w, c₀) hwc).1 hparse with ⟨_, hsrk₀, _, _⟩
      have hdh : Dh.dh (epExp c₀.1.1) Dh.base = Dh.dh (epExp ch.epoch) Dh.base :=
        hinj (hsrk₀.symm.trans hsrk_eq)
      have hle_g : ch.epoch ≤ max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B) := by
        have h1 : ch.epoch ≤ maxActiveEp sC.base.mir Q := by
          refine le_trans hch_ep_le ?_; unfold maxActiveEp; omega
        cases Q <;> [exact le_trans h1 (le_max_left _ _); exact le_trans h1 (le_max_right _ _)]
      exact hinv.hsim.hcoll c₀.1.1 ch.epoch (hinv.hsim.hhon (w, c₀) hwc).2.1 hle_g hdh
    have htoWire : LibsignalSim.toWire c = w :=
      toWire_raw_eq w hlen ch.epoch (decT h.senderRatchetKey) i (effectiveHkdfSalt32 salt)
    have hfwd : fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
        sC.base Q c g =
        injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          SM.Config.h1 Q c g :=
      fwdPure_of_inTransit_false _ 3 (qep + 1) SM.Config.h1 sC.base Q w c g
        (fun wc hwc => (hinv.hsim.hhon wc hwc).1.1) htoWire htr_mir
    have htr_fig8 : (g.inTransit Q.other c).isSome = false :=
      inTransit_fig8_isSome_of_toWire hmeta Q w c htoWire htr_mir
    have hguard_fig8 : (g.win || (g.inTransit Q.other c).isSome || !(g.safeInj 3)) = false := by
      rw [hmeta.hwin_fig8, htr_fig8, hmeta.safeInj_fig8, hsafe_mir]; rfl
    let pos : SM.Pos := ⟨Q.other, ch.epoch, i⟩
    let mir' := sC.base.mir.accept Q () pos
    have hmir_ep : mir'.epoch = sC.base.mir.epoch :=
      WP2A.I3.accept_epoch_eq_of_le sC.base.mir Q () pos hch_ep_le
    have hstep_0 := (receive_knownChain_expectedGhost_eqC P (InvB Inv q r) ℓ Dh encPt encT
      hinj idOf lam hid qep q r x₀ s_R sC.base g ec winBefore epExp hinv.hsim Q w hlen h body
      hparse haddrs pq' salt hspqr hpan ci hfind (decT h.senderRatchetKey) hT
      mir' hmir_ep rfl 0).2 hrej_f
    dsimp only at hstep_0
    cases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c with
    | none =>
      have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          SM.Config.h1 Q c g = (some .rejected, g) := by
        unfold injectPure; simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig]
      have hnot_acc :
          r_out.2.1 = sC ∧ { r_out.2.2.1 with win := false } = { g with win := false } := by
        refine fwdCPure_inject_of_fwdPure_not_accepted P ℓ Dh encPt encT idOf lam qep Q w (some ci)
          h.senderRatchetKey pq' honestC c_mk (sC, g, false) ?_ ?_
        · intro t' i' m'; dsimp only; rw [hmkC, hfwd, hinj_fig8]; simp
        · dsimp only; rw [hmkC, hfwd, hinj_fig8]
      rw [hnot_acc.1, hnot_acc.2, hg_eq0]
      exact ⟨s_R, ec, winBefore,
        c8_simInvCX_mono_r P Inv ℓ Dh encPt encT idOf lam qep q r r' (Nat.le_of_lt hr) x₀ s_R sC g
          ec winBefore epExp hinv⟩
    | some res_fig =>
      rcases res_fig with ⟨st', t', i', pub, m⟩
      have hfig' : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c =
          some (st', t', i', pub, m) := hfig
      rw [hfig'] at hstep_0
      rcases hstep_0 with ⟨ht', hi', _, ⟨v', hst', hsync'⟩, _⟩
      subst ht' hi'
      have hnot_gt : ¬ (qep + 1 < ch.epoch) := by have := hinv.hsim.hep_le Q; omega
      have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < ch.epoch) := by omega
      by_cases htriv : sC.base.mir.trivial 3 pos = true
      · let s' : SimState (List (BitVec 8)) Pt ℓ :=
          { sC.base with
            mir := mir',
            pq := Function.update sC.base.pq Q pq',
            unackA := sC.base.unackA && Q != Party.A,
            chains := Function.update sC.base.chains Q ((sC.base.chains Q).modify ci (·.accept i)) }
        let kept' := Function.update sC.kept Q
          (Kept.recv (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (fs := lFS P.C P.codec ℓ encT idOf 25000) c (sC.kept Q))
        let sC' : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ := { sC with base := s', kept := kept' }
        let g' := g.accept Q st' pos
        let st_R' := expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q)
        let s_R' := s_R.accept Q st_R' pos
        have htriv_fig8 : g.trivial 3 pos = true := by rw [hmeta.trivial_fig8, htriv]
        have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
            SM.Config.h1 Q c g = (some (.accepted ch.epoch i (some (pub, m))), g') := by
          unfold injectPure
          simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig',
            show ¬ (qep + 1 + 1 < ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch)
              from hnot_gt_fig8,
            show g.trivial 3 ⟨Q.other, ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch,
              h.counter.toNat + 1⟩ = true from htriv_fig8]
          rfl
        have hr_out : r_out = (some (.accepted ch.epoch i (some m)), (sC', g', false)) := by
          dsimp only [r_out]
          have hplain :
              fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false (some ci)
                h.senderRatchetKey pq' honestC c_mk (sC, g, false) =
              fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false (some ci)
                h.senderRatchetKey pq' none c_mk (sC, g, false) := by
            unfold fwdCPure
            cases honestC <;> simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          rw [hplain, hmkC]
          unfold fwdCPure
          dsimp only
          rw [hfwd, hinj_fig8]
          unfold onAnswerPure onAcceptPure
          simp only [hnot_gt, show sC.base.mir.trivial 3 ⟨Q.other, ch.epoch, i⟩ = true from htriv,
            ↓reduceIte]
          rfl
        have hg'_win : { g' with win := false } = g' := by
          unfold g' SM.GameState.accept SM.GameState.delete; cases g; simp_all
        obtain ⟨_, _, _, v_old, hvR, _⟩ := hinv.hsim.hchains_sync Q ch hch_mem
        have hold : ch.epoch ≤ (g.st Q).tcur :=
          ((hinv.hkept.hvR Q ch.epoch).mp (by simp [hvR])).1
        have hkept' : KeptInv P Dh encPt encT idOf lam sC' g' :=
          keptInv_recv_accept hinv.hkept Q (hinv.hsim.hst_id Q) c st' _ hfig' rfl rfl
        have hsync8' : EpochSync P Dh encPt encT idOf s'.honest sC.sent sC.snaps g' epExp :=
          epochSync_recv_old P Dh encPt encT idOf lam _ _ _ _ _ hinv.hsync Q c st' _ hfig' hold rfl
            (fun hw => hw) (fun _ hwc => hwc)
        have hinv_sub1 : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' g'
            ec winBefore epExp := by
          subst hst'
          exact simInvCX_inject_known_accept P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC g
            ec winBefore epExp hinv Q ci ch i pq' hch_elem v' hsync' pos rfl hpq' s' rfl g' rfl
            s_R' rfl kept' hkept' hsync8'
        rw [hr_out]
        dsimp only
        rw [hg'_win]
        exact ⟨s_R', ec, winBefore,
          c8_simInvCX_mono_r P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) r'
            (Nat.le_sub_one_of_lt hr) x₀ s_R' sC' g' ec winBefore epExp hinv_sub1⟩
      · have htriv_f : sC.base.mir.trivial 3 pos = false := Bool.eq_false_iff.mpr htriv
        have htriv_fig8 : g.trivial 3 pos = false := by rw [hmeta.trivial_fig8, htriv_f]
        have hinj_fig8 : injectPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
            SM.Config.h1 Q c g = (some .rejected, { g with win := true }) := by
          unfold injectPure
          simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig',
            show ¬ (qep + 1 + 1 < ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch)
              from hnot_gt_fig8,
            show g.trivial 3 ⟨Q.other, ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch,
              h.counter.toNat + 1⟩ = false from htriv_fig8]
          rfl
        have hnot_acc :
            r_out.2.1 = sC ∧ { r_out.2.2.1 with win := false } = { g with win := false } := by
          refine fwdCPure_inject_of_fwdPure_not_accepted P ℓ Dh encPt encT idOf lam qep Q w
            (some ci) h.senderRatchetKey pq' honestC c_mk (sC, g, false) ?_ ?_
          · intro t' i' m'; dsimp only; rw [hmkC, hfwd, hinj_fig8]; simp
          · dsimp only; rw [hmkC, hfwd, hinj_fig8]
        rw [hnot_acc.1, hnot_acc.2, hg_eq0]
        exact ⟨s_R, ec, winBefore,
          c8_simInvCX_mono_r P Inv ℓ Dh encPt encT idOf lam qep q r r' (Nat.le_of_lt hr) x₀ s_R sC g
            ec winBefore epExp hinv⟩
  · have hfwd_win := fwdPure_of_win_true P ℓ Dh encPt encT idOf lam qep sC.base Q c_mk g hg_win
    have hnot_acc :
        r_out.2.1 = sC ∧ { r_out.2.2.1 with win := false } = { g with win := false } := by
      refine fwdCPure_inject_of_fwdPure_not_accepted P ℓ Dh encPt encT idOf lam qep Q w (some ci)
        h.senderRatchetKey pq' honestC c_mk (sC, g, false) ?_ ?_
      · intro t' i' m'; dsimp only; rw [hfwd_win]; simp
      · dsimp only; rw [hfwd_win]
    rw [hnot_acc.1, hnot_acc.2]
    exact ⟨s_R, ec, winBefore,
      c8_simInvCX_mono_r P Inv ℓ Dh encPt encT idOf lam qep q r r' (Nat.le_of_lt hr) x₀ s_R sC
        { g with win := false } ec winBefore epExp hinv⟩

private theorem kemFailSimImpl_inject_preserves_simInvCX
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r' r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hr : r' < r)
    (Q : Party) (w : List (BitVec 8)) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false }
      ec winBefore epExp)
    (z : Option (SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inr (Q, w))))).run (sC, (g, false), tr))) :
    ∃ s_R' ec' winBefore',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
        z.2.1 { z.2.2.1.1 with win := false } ec' winBefore' epExp := by
  change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000)
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false))).run
    (sC, (g, false), tr)) at hz
  rw [runProbeStep_run, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w_out, hw_out, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hw_step : (w_out.1.1, (w_out.1.2, w_out.2)) ∈ support
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) (sC, (g, false))) := by
    change (w_out.1.1, (w_out.1.2, w_out.2)) ∈ support
      ((((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000)
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false)).run
        sC).run (g, false)) >>= fun r => pure (r.1.1, (r.1.2, r.2)))
    rw [MonadAttach.mem_support_bind]
    exact ⟨w_out, hw_out, by simp⟩
  rw [stepSimCNone_inject_eq, support_pure, Set.mem_singleton_iff,
    simRecvStepC_eq_gen_false P ℓ Dh encPt encT decT idOf lam qep Q w false (sC, g, false)
      (Or.inl rfl)] at hw_step
  have hsC_eq : w_out.1.2 =
      (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, g, false)).2.1 :=
    congrArg (·.2.1) hw_step
  have hg_eq : w_out.2.1 =
      (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, g, false)).2.2.1 :=
    congrArg (·.2.2.1) hw_step
  change ∃ s_R' ec' winBefore',
    SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R' w_out.1.2
      (clearWin w_out.2.1) ec' winBefore' epExp
  rw [hsC_eq, hg_eq]
  have hinv_mono :=
    c8_simInvCX_mono_r P Inv ℓ Dh encPt encT idOf lam qep q r r' (Nat.le_of_lt hr) x₀ s_R sC
      { g with win := false } ec winBefore epExp hinv
  have hstop := hinv.hsim.hmeta.hstop
  have hwin_mir := hinv.hsim.hmeta.hwin_mir
  unfold simRecvStepCGen
  simp only [hstop, hwin_mir, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.not_false,
    Bool.true_and]
  by_cases hguard :
      ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w)) = true
  · simp only [hguard, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
  simp only [hguard, Bool.false_eq_true, ↓reduceIte]
  have hguard_f :
      ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w)) = false := Bool.eq_false_iff.mpr hguard
  by_cases hlen : w.length < 9
  · simp only [hlen, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
  simp only [hlen, ↓reduceIte]
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact ⟨s_R, ec, winBefore, hinv_mono⟩
  | some hb =>
    rcases hb with ⟨h, body⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · simp only [haddr, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    have haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true := by
      revert haddr; cases addressCheckPasses h.addresses (P.expectedAddrs Q) <;> simp
    by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
    · simp only [hpan, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    have hpan_f : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false :=
      Bool.eq_false_iff.mpr hpan
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact ⟨s_R, ec, winBefore, hinv_mono⟩
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases hfind : (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        by_cases hrej :
            ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = true
        · simp only [hrej, ↓reduceIte]; exact ⟨s_R, ec, winBefore, hinv_mono⟩
        simp only [hrej, Bool.false_eq_true, ↓reduceIte]
        exact simRecvStepCGen_inject_knownChain_preserves_simInvCX P Inv ℓ Dh encPt encT decT idOf
          hinj hid lam qep q r' r hS hr Q w x₀ s_R sC g ec winBefore epExp hinv hguard_f hlen hparse
          haddrs hspqr hpan_f hfind (Bool.eq_false_iff.mpr hrej)
      | none =>
        dsimp only
        have hs_stop : { sC.base with amb := sC.base.amb + 1, stopped := false } =
            { sC.base with amb := sC.base.amb + 1 } := by
          cases h_s : sC.base; rw [h_s] at hstop; subst hstop; rfl
        simp only [hs_stop]
        have htr_mir : (sC.base.mir.inTransit Q.other w).isSome = false := by
          revert hguard_f; cases (sC.base.mir.inTransit Q.other w).isSome <;> simp
        have hsafe_mir : sC.base.mir.safeInj 3 = true := by
          revert hguard_f; cases (sC.base.mir.inTransit Q.other w).isSome <;>
            cases sC.base.mir.safeInj 3 <;> simp
        let x₁ : JointC (List (BitVec 8)) Pt ℓ :=
          if inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
            ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, g, false)
          else (sC, g, false)
        have hx₁_inv : ∃ winBefore₁,
            SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R x₁.1
              (clearWin x₁.2.1) ec winBefore₁ epExp := by
          dsimp only [x₁]
          split
          · exact ⟨_, c8_simInvCX_mono_r P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) r'
              (Nat.le_sub_one_of_lt hr) x₀ s_R _ { g with win := false } ec _ epExp
              (simInvCX_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r
                (Nat.zero_lt_of_lt hr) x₀ s_R sC { g with win := false } ec winBefore epExp hinv
                rfl)⟩
          · exact ⟨winBefore, hinv_mono⟩
        obtain ⟨winBefore₁, hinv₁⟩ := hx₁_inv
        have htriv₁ : ∀ pos, x₁.2.1.trivial 3 pos = x₁.1.base.mir.trivial 3 pos := by
          intro pos
          have := hinv₁.hsim.hmeta.trivial_fig8 3 pos
          exact this
        have hhon₁ : ∀ wc ∈ x₁.1.base.honest, wc.1 = LibsignalSim.toWire wc.2 :=
          fun wc hwc => (hinv₁.hsim.hhon wc hwc).1.1
        have hmir₁ : x₁.1.base.mir = sC.base.mir := by dsimp only [x₁]; split <;> rfl
        split
        · exact ⟨s_R, ec, winBefore, hinv_mono⟩
        · split
          · exact ⟨s_R, ec, winBefore, hinv_mono⟩
          · split
            · exact ⟨s_R, ec, winBefore₁, hinv₁⟩
            · cases hdec_srk : decT h.senderRatchetKey with
              | none => dsimp only; exact ⟨s_R, ec, winBefore₁, hinv₁⟩
              | some T =>
                dsimp only
                split
                · rename_i hev_true
                  unfold fwdEvictCPure
                  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                  have hraw_w :
                      LibsignalSim.toWire
                        ((sC.base.mir.epoch Q + 1, some T),
                          (h.counter.toNat + 1,
                            ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))),
                              effectiveHkdfSalt32 salt))) = w :=
                    toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T) (h.counter.toNat + 1)
                      (effectiveHkdfSalt32 salt)
                  have hpres := fwdCPure_inject_of_epoch_lt P ℓ Dh encPt encT idOf lam qep Q w none
                    h.senderRatchetKey pq' none
                    ((sC.base.mir.epoch Q + 1, some T),
                      (h.counter.toNat + 1,
                        ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
                    x₁ (hmir₁ ▸ hsafe_mir) (hmir₁ ▸ hinv.hsim.hcomp) hhon₁ hraw_w
                    (hmir₁ ▸ htr_mir) htriv₁ (by rw [hmir₁]; dsimp only; omega)
                  rw [hpres.1, hpres.2]
                  exact ⟨s_R, ec, winBefore₁, hinv₁⟩
                · rename_i hev_false
                  have hev_f :
                      ((((sC.base.honest.find? fun wc =>
                          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                        fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = false :=
                    Bool.eq_false_iff.mpr hev_false
                  let honestC := (sC.base.honest.find? fun wc =>
                    wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
                  let c_mk : Fig8C Pt :=
                    match honestC with
                    | some c =>
                      if c.2.2.2 = effectiveHkdfSalt32 salt then c
                      else ((sC.base.mir.epoch Q + 1, some T),
                        (h.counter.toNat + 1,
                          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
                    | none =>
                      ((sC.base.mir.epoch Q + 1, some T),
                        (h.counter.toNat + 1,
                          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
                  have hc_mk_props :
                      LibsignalSim.toWire c_mk = w ∧ sC.base.mir.epoch Q < c_mk.1.1 := by
                    dsimp only [c_mk, honestC]
                    cases hfind_hon : sC.base.honest.find?
                        (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
                    | none =>
                      simp only [Option.map]
                      exact ⟨toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T)
                        (h.counter.toNat + 1) (effectiveHkdfSalt32 salt), by omega⟩
                    | some wc =>
                      rcases wc with ⟨w_c, c_h⟩
                      simp only [Option.map]
                      split
                      · have hmem := List.mem_of_find?_eq_some hfind_hon
                        have hpred := List.find?_some hfind_hon
                        simp only [Bool.and_eq_true, beq_iff_eq] at hpred
                        have hw_eq : LibsignalSim.toWire c_h = w := by
                          rw [← hpred.1]
                          exact (hinv.hsim.hhon (w_c, c_h) hmem).1.1.symm
                        simp only [hfind_hon, Option.map_some, beq_eq_false_iff_ne, Ne,
                          Option.some.injEq, decide_eq_true_eq] at hev_f
                        have hc_ep : c_h.1.1 = sC.base.mir.epoch Q + 1 :=
                          Decidable.of_not_not hev_f
                        exact ⟨hw_eq, by omega⟩
                      · dsimp only
                        exact ⟨toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T)
                          (h.counter.toNat + 1) (effectiveHkdfSalt32 salt), by omega⟩
                  have hpres := fwdCPure_inject_of_epoch_lt P ℓ Dh encPt encT idOf lam qep Q w none
                    h.senderRatchetKey pq' honestC c_mk x₁ (hmir₁ ▸ hsafe_mir)
                    (hmir₁ ▸ hinv.hsim.hcomp) hhon₁ hc_mk_props.1 (hmir₁ ▸ htr_mir) htriv₁
                    (hmir₁ ▸ hc_mk_props.2)
                  change ∃ s_R' ec' winBefore',
                    SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R'
                      (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false none
                        h.senderRatchetKey pq' honestC c_mk x₁).2.1
                      (clearWin (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w false none
                        h.senderRatchetKey pq' honestC c_mk x₁).2.2.1)
                      ec' winBefore' epExp
                  rw [hpres.1, hpres.2]
                  exact ⟨s_R, ec, winBefore₁, hinv₁⟩

private theorem evictedSpurSimInv_inject_of_simInvCX
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r' r : ℕ) (hS : Proofs.Refinement.SpqrCLocal P.spqr q InvPQ) (hr : r' < r)
    (Q : Party) (w : List (BitVec 8)) (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hhist : Proofs.Refinement.SpqrHistoryInv P K sC.base)
    (hEx : EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q r sC g)
    (z : Option (SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inr (Q, w))))).run (sC, (g, false), tr)))
    (_hcand : z.2.2.2.cand = none) :
    EvictedSpurSimInv P InvPQ ℓ Dh encPt encT idOf lam qep q r' z.2.1 z.2.2.1.1 := by
  rcases hEx with ⟨x₀, s_R, ec, winBefore, epExp, hsim, hno_spur⟩
  obtain ⟨s_R', ec', winBefore', hsim'⟩ :=
    kemFailSimImpl_inject_preserves_simInvCX P K InvPQ ℓ Dh encPt encT decT idOf hinj hid lam qep q
      r' r hS hr Q w x₀ s_R sC g tr ec winBefore epExp hsim z hz
  change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000)
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false))).run
    (sC, (g, false), tr)) at hz
  rw [runProbeStep_run, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨w_out, hw_out, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hw_step : (w_out.1.1, (w_out.1.2, w_out.2)) ∈ support
      (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) (sC, (g, false))) := by
    change (w_out.1.1, (w_out.1.2, w_out.2)) ∈ support
      ((((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000)
          (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false)).run
        sC).run (g, false)) >>= fun r => pure (r.1.1, (r.1.2, r.2)))
    rw [MonadAttach.mem_support_bind]
    exact ⟨w_out, hw_out, by simp⟩
  rw [stepSimCNone_inject_eq, support_pure, Set.mem_singleton_iff] at hw_step
  have hbase_eq : w_out.1.2.base =
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w false (sC, (g, false))).2.1.base := by
    rw [← hw_step]
  obtain ⟨hhon_eq, hep_eq, _⟩ :=
    simRecvStepC_inject_preserves_spqrHistoryInv_and_epoch_of_simInvC P K hspqr_eq ℓ Dh encPt encT
      decT idOf lam qep Q w (sC, (g, false)) hsim.hsim.hcomp hhist
  exact ⟨x₀, s_R', ec', winBefore', epExp, hsim',
    evictedSpurSimInv_spurBadList_congr ((congrArg (·.honest) hbase_eq).trans hhon_eq)
      ((congrArg (·.mir.epoch) hbase_eq).trans hep_eq) hno_spur⟩

/-- `inject` queries of `kemFailSimImpl` preserve `EvictedSpurHistSimInv` with probe flag `false`. -/
theorem evictedSpurHistSimInv_inject_step
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hinj : Function.Injective encT)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r' r w_rem : ℕ) (hS : Proofs.Refinement.SpqrCLocal P.spqr q InvPQ)
    (hr : r' < r)
    (Q : Party) (w : List (BitVec 8)) (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistSimInv P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g)
    (z : Option (SM.RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
      (.inr (.inl (.inr (Q, w))))).run (sC, (g, false), tr)))
    (hcand : z.2.2.2.cand = none) :
    z.2.2.1.2 = false ∧
    EvictedSpurHistSimInv P K InvPQ ℓ Dh encPt encT idOf lam qep q r' w_rem z.2.1 z.2.2.1.1 :=
  ⟨kemFailSimImpl_inject_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep Q w sC g tr z hz,
   kemFailSimImpl_inject_preserves_evictedSpurHistGameInv_of_simInvCX P K hspqr_eq ℓ Dh encPt
     encT decT idOf lam qep q r w_rem Q w sC (g, false) tr hInv.1 hInv.2 z hz,
   evictedSpurSimInv_inject_of_simInvCX P K hspqr_eq InvPQ ℓ Dh encPt encT decT idOf hinj hid lam
     qep q r' r hS hr Q w sC g tr hInv.1.hhist hInv.2 z hz hcand⟩

/-- `EvictedSpurHistSimInv` implies `EvictedOnlyNoForgeAt` at every party. -/
theorem evictedOnlyNoForgeAt_of_evictedSpurHistSimInv
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    {InvPQ : ℕ → List (BitVec 8) → Prop}
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hdec : ∀ T, decT (encT T) = some T) (lam : Pt)
    {qep q r w_rem : ℕ}
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party)
    (hInv : EvictedSpurHistSimInv P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g) :
    EvictedOnlyNoForgeAt P decT (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) sC g Q := by
  obtain ⟨x₀, s_R, ec, winBefore, epExp, hinv, hno_spur⟩ := hInv.2
  obtain ⟨w_acc, rk_base, T_base, -, -, hev_false⟩ :=
    Proofs.Refinement.evictedDeliverForgeEvent_eq_false_of_simInvC_and_spqrHistoryInv
      P K (fun pq ⟨n, _, hI⟩ => hInv_top n pq hI) Dh encPt encT idOf hid sC
      { g with win := false } Q hinv.hsim hInv.1.hhist
  intro w c h body pq' salt hmem hsender hparse hrecv hfind hepoch hinw hbound _ T hT
  rcases hinv.hsim.hhon (w, c) hmem with ⟨hhon_c, _, _, _⟩
  rcases Proofs.Refinement.honestEntryInvC_eq_raw P (Proofs.Refinement.InvB InvPQ q r) Dh encT
    epExp hhon_c hparse with ⟨_, hsrk, _, _⟩
  rw [hsrk, hdec] at hT
  injection hT with hT_eq
  subst hT_eq
  rw [hspqr_eq] at hrecv
  have hev := hev_false (hno_spur Q w_acc rk_base T_base hinw) w c h body pq' salt hmem hsender
    hparse hrecv hfind hepoch hinw
  have hisSome := Proofs.Refinement.lFig8_receive_evictedProbeRecord_isSome_eq_deliverForgeEvent
    P InvPQ Dh encPt encT idOf lam qep q r x₀ s_R sC { g with win := false } ec winBefore epExp
    hinv Q c w h salt hinw hbound
  rw [hev] at hisSome
  exact Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp hisSome)

end MoveCompatWithSamplePt

end MoveCompat

end CryptoVerification.LibsignalSession.HeadlineV1

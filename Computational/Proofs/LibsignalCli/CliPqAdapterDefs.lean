/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1
public import Computational.Proofs.SpecLemmas.Game.StatementPq
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import LibsignalBinary.Proofs.SignalSession.PqStep
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionSMProofDefs
import Computational.Proofs.ReductionDsl.SM.GameCosted
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

/-!
# Adapter coupling definitions and invariants for `cliPqExp`

**Checked by Lean.** Defines the polymorphic E2E driver, composed `L_bh` adapter handlers, and
state-coupling invariants (`CliKeyIndStateRel`, `CliAdapterKeyIndInv`, `CliAdapterInstRel`,
`CliAdapterDrvRel`, `cliAdapterStepCoupled`) for `cliPqExp`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-! ## Polymorphic E2E driver and `L_bh` unfolding -/

/-- Polymorphic model-state E2E driver oracle implementation over `BHE2EDrvState S ℓ`
parameterized over a `KeyInd` handler `ki`. -/
def cliE2EDrvImplWith {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ) ProbComp) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let σ ← get
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return .noneResp
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return .noneResp
    else
      let (kr, st') ← liftM ((ki kq).run σ.st)
      set (bhE2EMirror { σ with st := st' } kq kr)
      return kr
  | .inr (.inl (.inr (.startDR sid))) => do
    let σ ← get
    let (idx?, σ') ← liftM (compositionLocalStart ki C K (some σ.b) σ sid)
    set σ'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σ ← get
    let (sr, σ') ← liftM (bhE2EStepLocalSm C K qep decT encT σ i sq)
    set σ'
    return bhUnpackSmResp sq sr

/-- Polymorphic model-state E2E experiment parameterized over `ki` and `secb : Bool`. -/
def cliE2EExpWithKi (secb : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', σ) ← (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT) B).run
    { b := b, st := SignalPqxdh.KeyIndState.empty S secb }
  if !allTestedSessionsFresh P σ.st then $ᵗ Bool
  else return (b' == b || bhE2EDrvWon σ b)

theorem cliPqExp_eq_runCliDriver (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (ℓ qep : ℕ) {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (A : CliGameAdversary S ℓ (BitVec 512)) :
    cliPqExpProj S run X W ℓ qep decT encT A = (do
      let P := modelPrims X W
      let b ← $ᵗ Bool
      let ((b', ds), st) ←
        (runCliDriver S ℓ P run W qep decT encT bhNoExtWithSpqr (fun _ _ _ _ _ => some b) A).run
          (SignalPqxdh.KeyIndState.empty S true)
      if !allTestedSessionsFresh P st then $ᵗ Bool
      else return (b' == b || driverSomeInstanceWon ds b)) := rfl

/-- Single-step query implementation running `L_bh`'s shallow handler followed by `cliE2EDrvImplWith`. -/
def cliAdapterStepImplWith {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhGameSpec S ℓ (BitVec 512))
      (StateT (CliAdapterState S) (StateT (BHE2EDrvState S ℓ) ProbComp)) := fun q =>
  StateT.mk fun σ_ad =>
    simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
      ((bhShallowAdapterImpl S ℓ (BitVec 512) q).run σ_ad)

theorem simulateQ_cliE2EDrvImplWith_adapter_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} {α : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (oa : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) α)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
      ((simulateQ (bhShallowAdapterImpl S ℓ (BitVec 512)) oa).run σ_ad)).run σ_e2e =
    (((simulateQ (cliAdapterStepImplWith P ki C K qep decT encT) oa).run σ_ad).run σ_e2e) := by
  induction oa using OracleComp.inductionOn generalizing σ_ad σ_e2e with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, simulateQ_bind, StateT.run_bind, run_simulateQ_query_bind,
      StateT.run_bind]
    refine bind_congr fun ⟨⟨r, σ_ad'⟩, σ_e2e'⟩ => ?_
    exact ih r σ_ad' σ_e2e'

/-- Combined query implementation over `cliGameSpec` running `cliAdapterStepImplWith` on each query. -/
def cliComposedAdapterImplWith {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (cliGameSpec S ℓ (BitVec 512))
      (StateT (CliAdapterState S) (StateT (BHE2EDrvState S ℓ) ProbComp)) := fun q =>
  match q with
  | .inl (.inl (.inl n)) =>
    cliAdapterStepImplWith P ki C K qep decT encT (.inl n)
  | .inl (.inl (.inr kq)) =>
    cliAdapterStepImplWith P ki C K qep decT encT (.inr (.inl (.inl kq)))
  | .inl (.inr cq) =>
    cliAdapterStepImplWith P ki C K qep decT encT (.inr (.inl (.inr cq)))
  | .inr dq =>
    cliAdapterStepImplWith P ki C K qep decT encT (.inr (.inr dq))

theorem simulateQ_cliAdapterStepImplWith_bhAdvRun {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    simulateQ (cliAdapterStepImplWith P ki C K qep decT encT) (cliGameAdversaryReassoc A) =
      simulateQ (cliComposedAdapterImplWith P ki C K qep decT encT) A.run := by
  unfold cliGameAdversaryReassoc
  generalize A.run = oa
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]
  | query_bind q mx ih =>
    rcases q with ((n | kq) | cq) | dq <;> {
      simp only [simulateQ_bind, simulateQ_query, OracleSpec.query_def,
        cliComposedAdapterImplWith, ih]
      rfl
    }

theorem simulateQ_cliE2EDrvImplWith_L_bh_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (σ_e2e : BHE2EDrvState S ℓ) :
    (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
      ((L_bh decT encT).eval (fun _ => cliGameAdversaryReassoc A) ())).run σ_e2e =
    (fun p => (p.1.1, p.2)) <$>
      (((simulateQ (cliComposedAdapterImplWith P ki C K qep decT encT) A.run).run
        (cliAdapterInitState S)).run σ_e2e) := by
  have hEval :
      (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => cliGameAdversaryReassoc A) () =
      Prod.fst <$>
        ((simulateQ (bhShallowAdapterImpl S ℓ (BitVec 512)) (cliGameAdversaryReassoc A)).run
          (cliAdapterInitState S)) := by
    dsimp [BhShallowRed.eval, L_bh]
    simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  rw [hEval]
  simp only [map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure]
  rw [simulateQ_cliE2EDrvImplWith_adapter_run, simulateQ_cliAdapterStepImplWith_bhAdvRun]

/-! ## Coupling invariants -/

/-- Entry-by-entry relation on `spkBundles` ignoring the `revealed : Bool` flag. -/
def CliSpkBundleRel (p₁ p₂ : (ℕ × ℕ) × SignalPqxdh.SpkBundleEntry) : Prop :=
  p₁.1 = p₂.1 ∧
  p₁.2.spkSk = p₂.2.spkSk ∧
  p₁.2.spkPk = p₂.2.spkPk ∧
  p₁.2.spkSig = p₂.2.spkSig ∧
  p₁.2.pqspkSk = p₂.2.pqspkSk ∧
  p₁.2.pqspkPk = p₂.2.pqspkPk ∧
  p₁.2.pqspkSig = p₂.2.pqspkSig

@[refl]
theorem CliSpkBundleRel.refl (p : (ℕ × ℕ) × SignalPqxdh.SpkBundleEntry) :
    CliSpkBundleRel p p := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Coupling relation between `KeyIndState` in `cliPqExp` and in `cliE2EExpWithKi`: all fields
agree except `revealed` on `spkBundles`. -/
structure CliKeyIndStateRel {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (st_cli st_e2e : SignalPqxdh.KeyIndState S) : Prop where
  secb_cli : st_cli.secb = true
  secb_e2e : st_e2e.secb = true
  principals_eq : st_cli.principals = st_e2e.principals
  spkBundles_rel : List.Forall₂ CliSpkBundleRel st_cli.spkBundles st_e2e.spkBundles
  opkEntries_eq : st_cli.opkEntries = st_e2e.opkEntries
  sessions_eq : st_cli.sessions = st_e2e.sessions
  respSessions_eq : st_cli.respSessions = st_e2e.respSessions
  usedRecvOPK_eq : st_cli.usedRecvOPK = st_e2e.usedRecvOPK
  usedRecvNoOPK_eq : st_cli.usedRecvNoOPK = st_e2e.usedRecvNoOPK
  usedKyberTriples_eq : st_cli.seenKyberBaseKeys = st_e2e.seenKyberBaseKeys
  roCache_eq : st_cli.roCache = st_e2e.roCache
  advKeys_eq : st_cli.advKeys = st_e2e.advKeys
  tested_spkRevealed : ∀ s ∈ st_cli.sessions, s.tested = true →
    SignalPqxdh.isSpkRevealed P st_cli.spkBundles s.peerSpkPk = true ∧
    SignalPqxdh.isSpkRevealed P st_e2e.spkBundles s.peerSpkPk = true
  resp_not_tested : ∀ r ∈ st_cli.respSessions, r.tested = false

theorem cliKeyIndStateRel_empty (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives) :
    CliKeyIndStateRel P (SignalPqxdh.KeyIndState.empty S true)
      (SignalPqxdh.KeyIndState.empty S true) where
  secb_cli := rfl
  secb_e2e := rfl
  principals_eq := rfl
  spkBundles_rel := List.Forall₂.nil
  opkEntries_eq := rfl
  sessions_eq := rfl
  respSessions_eq := rfl
  usedRecvOPK_eq := rfl
  usedRecvNoOPK_eq := rfl
  usedKyberTriples_eq := rfl
  roCache_eq := rfl
  advKeys_eq := rfl
  tested_spkRevealed := fun _ h => False.elim (List.not_mem_nil h)
  resp_not_tested := fun _ h => False.elim (List.not_mem_nil h)

private theorem cli_list_all_eq_of_mem {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp [List.all_cons, h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem cli_list_any_eq_of_getElem?_rel {α β : Type} (l₁ : List α) (l₂ : List β)
    {p : α → Bool} {q : β → Bool} (hlen : l₁.length = l₂.length)
    (hrel : ∀ (i : ℕ) a b, l₁[i]? = some a → l₂[i]? = some b → p a = q b) :
    l₁.any p = l₂.any q := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a tl₁ ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons b tl₂ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp [List.any_cons, hrel 0 a b rfl rfl,
        ih tl₂ hlen (fun i a' b' ha hb => hrel (i + 1) a' b' ha hb)]

theorem bhComposedClean_eq_of_cliKeyIndStateRel {S : SignalPqxdh.Setup}
    {P : SignalPqxdh.Primitives} {st_cli st_e2e : SignalPqxdh.KeyIndState S}
    (hRel : CliKeyIndStateRel P st_cli st_e2e) :
    allTestedSessionsFresh P st_cli = allTestedSessionsFresh P st_e2e := by
  unfold allTestedSessionsFresh
  rw [← hRel.principals_eq, ← hRel.sessions_eq, ← hRel.respSessions_eq]
  have hSess :
      (st_cli.sessions.all fun s =>
        !s.tested || SignalPqxdh.isKeyIndInitStillFresh P true st_cli.principals
          st_cli.spkBundles st_cli.respSessions s) =
      (st_cli.sessions.all fun s =>
        !s.tested || SignalPqxdh.isKeyIndInitStillFresh P true st_cli.principals
          st_e2e.spkBundles st_cli.respSessions s) := by
    refine cli_list_all_eq_of_mem st_cli.sessions _ _ fun s hs => ?_
    cases htest : s.tested
    · rfl
    · obtain ⟨hRev1, hRev2⟩ := hRel.tested_spkRevealed s hs htest
      simp only [Bool.not_true, Bool.false_or, SignalPqxdh.isKeyIndInitStillFresh,
        SignalPqxdh.keyIndInitCorruptionClause, ↓reduceIte, hRev1, hRev2]
  have hResp :
      (st_cli.respSessions.all fun r =>
        !r.tested || SignalPqxdh.isKeyIndRespStillFresh P true st_cli.principals
          st_cli.spkBundles st_cli.sessions r) =
      (st_cli.respSessions.all fun r =>
        !r.tested || SignalPqxdh.isKeyIndRespStillFresh P true st_cli.principals
          st_e2e.spkBundles st_cli.sessions r) := by
    refine cli_list_all_eq_of_mem st_cli.respSessions _ _ fun r hr => ?_
    rw [hRel.resp_not_tested r hr]
    rfl
  rw [hSess, hResp]

/-- Well-formedness and 1-key / real-HKDF transcript invariant on `(st, ds)` in `cliPqExp`. -/
structure CliAdapterKeyIndInv (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (W : PEParams)
    (st : SignalPqxdh.KeyIndState S) (ds : ModelDriverState S ℓ) : Prop where
  prins_wf : ∀ u e, (u, e) ∈ st.principals →
    e.secIKA0.length = 32 ∧
    e.ikAPk = P.x25519Base e.secIKA0 ∧
    e.ikAPk = vecU8 (keyPairOf W.C (u8Vec 32 e.secIKA0)).publicKey.bytes ∧
    e.ikAPk.length = 32 ∧
    e.secIKAsign = e.secIKA0 ∧
    e.ikSignPk = e.ikAPk
  prins_uniq : ∀ idx₁ idx₂ e₁ e₂,
    (idx₁, e₁) ∈ st.principals → (idx₂, e₂) ∈ st.principals → idx₁ = idx₂ →
    e₁.secIKA0 = e₂.secIKA0 ∧ e₁.ikAPk = e₂.ikAPk ∧
    e₁.secIKAsign = e₂.secIKAsign ∧ e₁.ikSignPk = e₂.ikSignPk
  spk_wf : ∀ idx b, (idx, b) ∈ st.spkBundles →
    b.spkSk.length = 32 ∧
    b.spkPk = P.x25519Base b.spkSk ∧
    b.spkPk = vecU8 (keyPairOf W.C (u8Vec 32 b.spkSk)).publicKey.bytes ∧
    b.spkPk.length = 32 ∧
    b.pqspkPk.length = 1568 ∧
    b.pqspkSk.length = 3168 ∧
    b.spkSig.length = 64 ∧
    b.pqspkSig.length = 64
  spk_uniq : ∀ idx₁ idx₂ b₁ b₂,
    (idx₁, b₁) ∈ st.spkBundles → (idx₂, b₂) ∈ st.spkBundles → idx₁ = idx₂ →
    b₁.spkSk = b₂.spkSk ∧ b₁.spkPk = b₂.spkPk ∧
    b₁.pqspkPk = b₂.pqspkPk ∧ b₁.pqspkSk = b₂.pqspkSk ∧
    b₁.spkSig = b₂.spkSig ∧ b₁.pqspkSig = b₂.pqspkSig
  opk_wf : ∀ idx o, (idx, o) ∈ st.opkEntries →
    o.opkSk.length = 32 ∧
    o.opkPk = P.x25519Base o.opkSk ∧
    o.opkPk = vecU8 (keyPairOf W.C (u8Vec 32 o.opkSk)).publicKey.bytes ∧
    o.opkPk.length = 32
  opk_uniq : ∀ idx₁ idx₂ o₁ o₂,
    (idx₁, o₁) ∈ st.opkEntries → (idx₂, o₂) ∈ st.opkEntries → idx₁ = idx₂ →
    o₁.opkSk = o₂.opkSk ∧ o₁.opkPk = o₂.opkPk
  ds_prins : ∀ u ik, (u, ik) ∈ ds.prins →
    ∃ e, (u.val, e) ∈ st.principals ∧ ik = e.ikAPk
  prins_ds : ∀ idx e, (idx, e) ∈ st.principals →
    ∃ u, (u, e.ikAPk) ∈ ds.prins
  ds_bundles : ∀ slot spkB pqspkB, (slot, (spkB, pqspkB)) ∈ ds.bundles →
    ∃ e b, (slot.1.val, e) ∈ st.principals ∧
      ((slot.1.val, slot.2.val), b) ∈ st.spkBundles ∧
      spkB = b.spkPk ∧ pqspkB = b.pqspkPk
  ds_opks : ∀ slot opkPk, (slot, opkPk) ∈ ds.opks →
    ∃ oe, ((slot.1.val, slot.2.1.val, slot.2.2.val), oe) ∈ st.opkEntries ∧
      opkPk = oe.opkPk
  sessions_wf : ∀ s ∈ st.sessions,
    s.drKeyReal.rootKey.length = 32 ∧
    s.drKeyReal.chainKey.length = 32 ∧
    s.drKeyReal.pqrKey.length = 32 ∧
    s.drKeyRand.rootKey.length = 32 ∧
    s.drKeyRand.chainKey.length = 32 ∧
    s.drKeyRand.pqrKey.length = 32
  sessions_uniq : ∀ s₁ s₂, s₁ ∈ st.sessions → s₂ ∈ st.sessions → s₁.sid = s₂.sid →
    s₁.peerSpkPk = s₂.peerSpkPk ∧ s₁.drKeyReal = s₂.drKeyReal ∧ s₁.hdr = s₂.hdr
  roCache_nil : st.roCache = []
  respSessions_wf : ∀ r ∈ st.respSessions,
    r.drKeyReal.rootKey.length = 32 ∧
    r.drKeyReal.chainKey.length = 32 ∧
    r.drKeyReal.pqrKey.length = 32 ∧
    r.drKeyRand.rootKey.length = 32 ∧
    r.drKeyRand.chainKey.length = 32 ∧
    r.drKeyRand.pqrKey.length = 32
  initTapes_wf : ∀ sid u_init bnd t_init, (sid, u_init, bnd, t_init) ∈ ds.initTapes →
    (∃ sEntry ∈ st.sessions, sEntry.sid = sid) ∧
    (∃ uEntry, (u_init.val, uEntry) ∈ st.principals) ∧
    bhDrvSessionInitPrin? sid = some u_init ∧
    bnd.spkSig.length = 64 ∧ bnd.pqspkSig.length = 64
  initTapes_uniq : ∀ sid u₁ b₁ t₁ u₂ b₂ t₂,
    (sid, u₁, b₁, t₁) ∈ ds.initTapes →
    (sid, u₂, b₂, t₂) ∈ ds.initTapes →
    u₁ = u₂ ∧ b₁ = b₂ ∧ t₁ = t₂
  sends_wf : ∀ sid bnd hdr, (sid, bnd, hdr) ∈ ds.sends →
    (∃ sEntry ∈ st.sessions, sEntry.sid = sid ∧ sEntry.peerSpkPk = bnd.spkB ∧ sEntry.hdr = hdr) ∧
    (∃ u_init t_init uEntry, (sid, u_init, bnd, t_init) ∈ ds.initTapes ∧
      (u_init.val, uEntry) ∈ st.principals ∧ hdr.ikAPk = uEntry.ikAPk) ∧
    hdr.spkId = bnd.spkId ∧ hdr.pqspkId = bnd.pqspkId ∧
    hdr.opkId? = bnd.opkB?.map Prod.fst ∧
    bnd.spkSig.length = 64 ∧ bnd.pqspkSig.length = 64 ∧
    hdr.ikAPk.length = 32 ∧ hdr.ekAPk.length = 32 ∧ hdr.kemCt.length = 1568 ∧
    (P.sigVerify bnd.ikB (SignalPqxdh.encodeEC bnd.spkB) bnd.spkSig &&
      P.sigVerify bnd.ikB (SignalPqxdh.encodeKEM bnd.pqspkB) bnd.pqspkSig) = true ∧
    (∀ sid' u_init bnd' t_init sEntry uIdx uEntry,
      (sid', u_init, bnd', t_init) ∈ ds.initTapes →
      sid' = sid →
      sEntry ∈ st.sessions →
      sEntry.sid = sid →
      (uIdx, uEntry) ∈ st.principals →
      uIdx = u_init.val →
      ∃ ss : SignalPqxdh.Bytes,
        P.kemEncaps bnd'.pqspkB (tapeKemCoins t_init) = some (ss, hdr.kemCt) ∧
        hdr.ekAPk = P.x25519Base (tapeEkASk t_init) ∧
        let dh1 := P.x25519 uEntry.secIKA0 bnd'.spkB
        let dh2 := P.x25519 (tapeEkASk t_init) bnd'.ikB
        let dh3 := P.x25519 (tapeEkASk t_init) bnd'.spkB
        let dh4? := bnd'.opkB?.map (fun (_, opkPk) => P.x25519 (tapeEkASk t_init) opkPk)
        sEntry.drKeyReal = P.hkdfDerive96 (SignalPqxdh.buildSecrets dh1 dh2 dh3 dh4? ss))

theorem cliAdapterKeyIndInv_empty (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (W : PEParams) :
    CliAdapterKeyIndInv S (ℓ := ℓ) P W (SignalPqxdh.KeyIndState.empty S true) {} where
  prins_wf := fun _ _ h => False.elim (List.not_mem_nil h)
  prins_uniq := fun _ _ _ _ h => False.elim (List.not_mem_nil h)
  spk_wf := fun _ _ h => False.elim (List.not_mem_nil h)
  spk_uniq := fun _ _ _ _ h => False.elim (List.not_mem_nil h)
  opk_wf := fun _ _ h => False.elim (List.not_mem_nil h)
  opk_uniq := fun _ _ _ _ h => False.elim (List.not_mem_nil h)
  ds_prins := fun _ _ h => False.elim (List.not_mem_nil h)
  prins_ds := fun _ _ h => False.elim (List.not_mem_nil h)
  ds_bundles := fun _ _ _ h => False.elim (List.not_mem_nil h)
  ds_opks := fun _ _ h => False.elim (List.not_mem_nil h)
  sessions_wf := fun _ h => False.elim (List.not_mem_nil h)
  sessions_uniq := fun _ _ h => False.elim (List.not_mem_nil h)
  roCache_nil := rfl
  respSessions_wf := fun _ h => False.elim (List.not_mem_nil h)
  initTapes_wf := fun _ _ _ _ h => False.elim (List.not_mem_nil h)
  initTapes_uniq := fun _ _ _ _ _ _ _ h => False.elim (List.not_mem_nil h)
  sends_wf := fun _ _ _ h => False.elim (List.not_mem_nil h)

/-- Transcript entry coupling relation between CLI `Record` `r_cli` and model `Record` `r_m`. -/
def CliAdapterTransEntryRel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (bobAccepted : Bool) (sid : SignalPqxdh.SessionId S) (hdr : SignalPqxdh.HandshakeHdr)
    (r_cli : SM.Record (Plain ℓ) Bytes) (r_m : SM.Record (Plain ℓ) Bytes) : Prop :=
  r_cli.pos = r_m.pos ∧
  r_cli.msg = r_m.msg ∧
  ((r_cli.ct = [] ∧ r_m.ct = []) ∨
   (r_m.ct ≠ [] ∧
    bhDecodePreKeyMsgE r_m.ct = none ∧
    (∀ body, r_m.ct ≠ wireWhisper :: body) ∧
    (r_m.ct.length ≤ 1_000_300 ∧ r_m.ct.length + 2048 < 2 ^ 32) ∧
    (r_cli.pos.sender = .A →
      bhWireInnerBytes r_cli.ct = some r_m.ct ∧
      (!bobAccepted →
        r_cli.ct = wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId sid) hdr r_m.ct).bytes)) ∧
    (r_cli.pos.sender = .B → r_cli.ct = wireWhisper :: r_m.ct)))

theorem cliAdapterTransEntryRel_of_bobAccepted_true {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {bobAccepted : Bool} {sid : SignalPqxdh.SessionId S} {hdr : SignalPqxdh.HandshakeHdr}
    {r_cli : SM.Record (Plain ℓ) Bytes} {r_m : SM.Record (Plain ℓ) Bytes}
    (h : CliAdapterTransEntryRel bobAccepted sid hdr r_cli r_m) :
    CliAdapterTransEntryRel true sid hdr r_cli r_m := by
  refine ⟨h.1, h.2.1, h.2.2.imp id (fun h2 =>
    ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, fun hA => ⟨(h2.2.2.2.2.1 hA).1, ?_⟩, h2.2.2.2.2.2⟩)⟩
  intro hnot
  cases hnot

/-- Domain and `pqRatchetState` size invariant for an active CLI party state `(x, g)`. -/
def CliPartyActiveInv (W : PEParams) (d0 : PqParty) (x : RecordExtras) (g : GhostState Bytes)
    (_q_rem : ℕ) : Prop :=
  PqxdhPartyInSpecDomain W { d0 with session := some (x, g) } ∧
  lastResortUses { d0 with session := some (x, g) } < 2 ^ 25 ∧
  g.Aligned ∧
  g.session.pqRatchetState.length ≤ 286196

/-- Per-instance coupling relation across the CLI driver, model E2E driver, and shallow adapter. -/
structure CliAdapterInstRel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (q_rem : ℕ)
    (st_cli : SignalPqxdh.KeyIndState S) (ds_cli : ModelDriverState S ℓ)
    (bi : ModelDriverInstance S ℓ) (d : BHModelInst S ℓ) (im im_e2e : ModelDriverInstanceMeta S)
    (inst : BHAdapterInstMeta S) (ack : Bool) : Prop where
  im_eq : im = im_e2e
  sid_eq : bi.sid = d.sid ∧ inst.sid = d.sid
  hdr_eq : bi.hdr = d.hdr ∧ inst.hdr = d.hdr
  idB_eq : bi.idBBytes = inst.idB ∧ d.idA = bhIdKeyOf d.hdr.ikAPk ∧ d.idB = bhIdKeyOf bi.idBBytes
  respSlot_eq : bi.respSlot.1 = inst.u_resp
  /-- The promotion-time responder slot recorded in the meta matches `bi.respSlot` (`DEV-C17`). -/
  respMeta_eq : im.respPrin = some bi.respSlot.1 ∧ im.respSpkIdx = some bi.respSlot.2
  regIdA_eq : bi.meA.regId = bhInitRegId d.sid ∧ inst.bobRemoteRegId = bhInitRegId d.sid
  regIdB_eq : bi.meB.regId = BitVec.ofNat 32 inst.u_resp.val
  aliceAcked_false : inst.aliceAcked = false
  idA_pub_eq : bhIdKeyOf d.hdr.ikAPk = ⟨(keyPairOf W.C bi.meA.idPriv).publicKey⟩
  idB_pub_eq : bhIdKeyOf bi.idBBytes = ⟨(keyPairOf W.C bi.meB.idPriv).publicKey⟩
  extrasB_eq : bhInstExtrasB inst = bhRecvExtrasOfHdr bi.meA bi.meB d.hdr
  stB0_empty : bi.stB0 = { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
  resp_bundle_rel :
    ∃ (bEntry : SignalPqxdh.SpkBundleEntry),
      ((bi.respSlot.1.val, bi.respSlot.2.val), bEntry) ∈ st_cli.spkBundles ∧
      d.spkCoins = bhBytesWord bEntry.spkSk ∧
      keyPairOf W.C bi.keysB.spkPriv = KeyPair.generate W.C (bhBytesWord bEntry.spkSk) ∧
      u8Vec 3168 bEntry.pqspkSk = bi.keysB.kpkSec ∧
      cliPqSigsOf st_cli bi = (cliPqSig64 bEntry.spkSig, cliPqSig64 bEntry.pqspkSig)
  handshake_rel :
    ∃ (bundleE : PreKeyBundleFields) (dk : SignalPqxdh.DRKey) (aliceCoins : BitVec 256)
      (u_init : Fin S.N_id) (bnd : SignalPqxdh.PreKeyBundleInput)
      (t_init : List.Vector (BitVec 8) 160) (ss : SignalPqxdh.Bytes),
      let P := modelPrims X W
      let kS := bhKeySOf dk aliceCoins
      let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB
      bhInstExtrasA inst =
        initiatorRecordExtras bi.meA bundleE ⟨u8Vec 32 d.hdr.ekAPk⟩ (u8Vec 1568 d.hdr.kemCt) ∧
      (d.sid, u_init, bnd, t_init) ∈ ds_cli.initTapes ∧
      (∀ bEntry, ((bi.respSlot.1.val, bi.respSlot.2.val), bEntry) ∈ st_cli.spkBundles →
        bnd.pqspkB = bEntry.pqspkPk ∧
        P.kemEncaps bEntry.pqspkPk (tapeKemCoins t_init) = some (ss, d.hdr.kemCt) ∧
        (P.kemDecaps bEntry.pqspkSk d.hdr.kemCt = some ss →
          ∀ inner : Bytes,
            let m := bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner
            m.spkId = bi.keysB.spkId ∧
            m.kpkId = bi.keysB.kpkId ∧
            SignalPqxdh.Model.acceptKeys P (acceptInput W bi.meB bi.keysB m) = some dk)) ∧
      (∀ gs_cli gs_m, bi.gs = some gs_cli → d.gs = some gs_m → !im.ikACorrAtAccept →
        !im.bobAccepted →
        gs_m.st .B = (sessionSchemeFixedSpk P_v1 ℓ d.spkCoins).initB kS)
  gs_rel :
    match bi.gs, d.gs with
    | some gs_cli, some gs_m =>
      gs_cli.b = gs_m.b ∧
      (if im.ikACorrAtAccept then
        gs_cli.win = gs_m.win
      else
        im.bobAccepted = inst.bobAccepted ∧
        gs_cli.win = gs_m.win ∧
        gs_cli.epoch = gs_m.epoch ∧
        gs_cli.idx = gs_m.idx ∧
        gs_cli.maxAcc = gs_m.maxAcc ∧
        gs_cli.chall = gs_m.chall ∧
        gs_cli.comp = gs_m.comp ∧
        gs_cli.tL = gs_m.tL ∧
        gs_cli.leaks = gs_m.leaks ∧
        gs_cli.corrs = gs_m.corrs ∧
        List.Forall₂ (CliAdapterTransEntryRel im.bobAccepted d.sid d.hdr) gs_cli.trans gs_m.trans ∧
        (gs_m.st .A).session.pendingPreKey = !ack ∧
        (gs_m.st .B).session.pendingPreKey = false ∧
        (gs_m.st .A).session.localIdentity = d.idA ∧
        (!im.bobAccepted → ack = false) ∧
        (!im.bobAccepted → gs_m.epoch .A ≤ 1) ∧
        (!im.bobAccepted → gs_m.epoch .B = 0) ∧
        (!im.bobAccepted → ∀ r ∈ gs_m.trans, r.pos.sender = .A) ∧
        (!im.bobAccepted → ∀ pos ∈ gs_m.comp, pos.sender = .A) ∧
        (!im.bobAccepted → gs_m.tL = none) ∧
        (im.bobAccepted → 0 < (gs_m.st .B).epoch) ∧
        gs_cli.st .A = bhBinStateOfParty inst (gs_m.st .A) ∧
        (!im.bobAccepted → gs_cli.st .B = bi.stB0) ∧
        (im.bobAccepted → gs_cli.st .B = bhBinStateOfParty inst (gs_m.st .B)) ∧
        (gs_m.st .A).party = .A ∧
        (gs_m.st .B).party = .B ∧
        CliPartyActiveInv W (cliPqDirA bi) (bhInstExtrasA inst) (gs_m.st .A) q_rem ∧
        (im.bobAccepted →
          CliPartyActiveInv W (cliPqxdhDirBobAfterAccept bi (cliPqSigsOf st_cli bi))
            (bhInstExtrasB inst) (gs_m.st .B) q_rem))
    | _, _ => False

/-- Full driver coupling relation between `(ds_cli, st_cli)` in `cliPqExp` and `(σ_ad, σ_e2e)` in
`cliComposedAdapterImplWith`. -/
structure CliAdapterDrvRel (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (b : Bool) (qStart : ℕ) (qs_rem : ℕ → ℕ)
    (st_cli : SignalPqxdh.KeyIndState S) (ds_cli : ModelDriverState S ℓ)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) : Prop where
  b_eq : σ_e2e.b = b
  st_rel : CliKeyIndStateRel (modelPrims X W) st_cli σ_e2e.st
  ki_inv : CliAdapterKeyIndInv S (modelPrims X W) W st_cli ds_cli
  base_e2e_eq : ds_cli.toModelDriverBase = σ_e2e.toModelDriverBase
  base_ad_eq : σ_ad.2.2 = ds_cli.toModelDriverBase
  corrPrins_eq : ds_cli.corrPrins = σ_e2e.corrPrins
  revealedSpks_eq : ds_cli.revealedSpks = σ_e2e.revealedSpks
  insts_len_le : ds_cli.bhInsts.length ≤ qStart
  insts_len_eq : ds_cli.bhInsts.length = σ_e2e.insts.length
  meta_cli_len_eq : ds_cli.instMeta.length = ds_cli.bhInsts.length
  meta_e2e_len_eq : σ_e2e.instMeta.length = σ_e2e.insts.length
  ad_none_of_ge : ∀ i, σ_e2e.insts.length ≤ i → σ_ad.1 i = none ∧ σ_ad.2.1 i = false
  insts_rel : ∀ i (h_cli : i < ds_cli.bhInsts.length) (h_e2e : i < σ_e2e.insts.length)
    (h_mb : i < ds_cli.instMeta.length) (h_me : i < σ_e2e.instMeta.length),
    ∃ inst : BHAdapterInstMeta S,
      σ_ad.1 i = some inst ∧
      CliAdapterInstRel X W (qs_rem i) st_cli ds_cli
        ds_cli.bhInsts[i] σ_e2e.insts[i] ds_cli.instMeta[i] σ_e2e.instMeta[i]
        inst (σ_ad.2.1 i)

theorem cliAdapterDrvRel_init (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (b : Bool) (qStart : ℕ) (qs_rem : ℕ → ℕ) :
    CliAdapterDrvRel S ℓ X W b qStart qs_rem
      (SignalPqxdh.KeyIndState.empty S true) {}
      (cliAdapterInitState S)
      { b := b, st := SignalPqxdh.KeyIndState.empty S true } where
  b_eq := rfl
  st_rel := cliKeyIndStateRel_empty S (modelPrims X W)
  ki_inv := cliAdapterKeyIndInv_empty S (modelPrims X W) W
  base_e2e_eq := rfl
  base_ad_eq := rfl
  corrPrins_eq := rfl
  revealedSpks_eq := rfl
  insts_len_le := Nat.zero_le qStart
  insts_len_eq := rfl
  meta_cli_len_eq := rfl
  meta_e2e_len_eq := rfl
  ad_none_of_ge := fun _ _ => ⟨rfl, rfl⟩
  insts_rel := fun _ h => False.elim (Nat.not_lt_zero _ h)

theorem CliAdapterDrvRel.instMeta_eq {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e) :
    ds_cli.instMeta = σ_e2e.instMeta := by
  have hlen : ds_cli.instMeta.length = σ_e2e.instMeta.length :=
    hRel.meta_cli_len_eq.trans (hRel.insts_len_eq.trans hRel.meta_e2e_len_eq.symm)
  refine List.ext_getElem hlen fun i hi_mb hi_me => ?_
  have hi_cli : i < ds_cli.bhInsts.length := hRel.meta_cli_len_eq ▸ hi_mb
  have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
  exact (hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me).choose_spec.2.im_eq

theorem bhDrvWon_eq_bhE2EDrvWon_of_cliRel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e) :
    driverSomeInstanceWon ds_cli b = bhE2EDrvWon σ_e2e b := by
  unfold driverSomeInstanceWon bhE2EDrvWon
  refine cli_list_any_eq_of_getElem?_rel ds_cli.bhInsts σ_e2e.insts hRel.insts_len_eq ?_
  intro i bi d hbi hd
  have hi_cli : i < ds_cli.bhInsts.length := by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hbi
    cases hbi
  have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
  have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
  have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
  obtain ⟨inst, _, hInstRel⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
  have hbi_eq : ds_cli.bhInsts[i] = bi := Option.some.inj ((List.getElem?_eq_getElem hi_cli).symm.trans hbi)
  have hd_eq : σ_e2e.insts[i] = d := Option.some.inj ((List.getElem?_eq_getElem hi_e2e).symm.trans hd)
  have hgs := hInstRel.gs_rel
  rw [hbi_eq, hd_eq] at hgs
  cases hgs_cli : bi.gs with
  | none =>
    rw [hgs_cli] at hgs
    exact False.elim hgs
  | some gs_cli =>
    cases hgs_m : d.gs with
    | none => rw [hgs_cli, hgs_m] at hgs; cases hgs
    | some gs_m =>
      rw [hgs_cli, hgs_m] at hgs
      dsimp only
      by_cases im_corr : (ds_cli.instMeta[i]).ikACorrAtAccept = true
      · simp only [im_corr, ↓reduceIte] at hgs
        rw [hgs.1, hgs.2]
      · have hnot : (ds_cli.instMeta[i]).ikACorrAtAccept = false := by
          cases hc : (ds_cli.instMeta[i]).ikACorrAtAccept <;> simp_all
        simp only [hnot, Bool.false_eq_true, ↓reduceIte] at hgs
        rw [hgs.1, hgs.2.2.1]

/-- Step-level exact coupling between a CLI driver computation `c_cli` and an adapter+E2E
computation `c_ad`. -/
def cliAdapterStepCoupled {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (b : Bool) (qStart' : ℕ) (qs_rem' : ℕ → ℕ)
    (c_cli : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S))
    (c_ad : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ)) : Prop :=
  ∃ μ : ProbComp
      (((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) ×
       ((α × CliAdapterState S) × BHE2EDrvState S ℓ)),
    CryptoGames.Lazy.DEq (Prod.fst <$> μ) c_cli ∧
    CryptoGames.Lazy.DEq (Prod.snd <$> μ) c_ad ∧
    ∀ x y, (x, y) ∈ support μ →
      x.1.1 = y.1.1 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem' x.2 x.1.2 y.1.2 y.2

theorem cliAdapterStepCoupled_ret {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    (r : α) (st_cli' : SignalPqxdh.KeyIndState S) (ds_cli' : ModelDriverState S ℓ)
    (σ_ad' : CliAdapterState S) (σ_e2e' : BHE2EDrvState S ℓ)
    (hRel' : CliAdapterDrvRel S ℓ X W b qStart' qs_rem' st_cli' ds_cli' σ_ad' σ_e2e') :
    cliAdapterStepCoupled X W b qStart' qs_rem'
      (pure ((r, ds_cli'), st_cli'))
      (pure ((r, σ_ad'), σ_e2e')) := by
  refine ⟨pure (((r, ds_cli'), st_cli'), ((r, σ_ad'), σ_e2e')), ?_, ?_, ?_⟩
  · simp [CryptoGames.Lazy.DEq]
  · simp [CryptoGames.Lazy.DEq]
  · intro x y hmem
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨rfl, hRel'⟩

theorem cliAdapterStepCoupled_of_deq {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    {c_cli c_cli' : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)}
    {c_ad c_ad' : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ)}
    (hCoupled : cliAdapterStepCoupled X W b qStart' qs_rem' c_cli' c_ad')
    (h_cli : CryptoGames.Lazy.DEq c_cli c_cli')
    (h_ad : CryptoGames.Lazy.DEq c_ad c_ad') :
    cliAdapterStepCoupled X W b qStart' qs_rem' c_cli c_ad := by
  rcases hCoupled with ⟨μ, h1, h2, hsupp⟩
  exact ⟨μ, h1.trans h_cli.symm, h2.trans h_ad.symm, hsupp⟩

end CryptoVerification.E2E

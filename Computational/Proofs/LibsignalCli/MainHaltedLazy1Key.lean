/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.MainHaltedKeyInd
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore
public import Computational.Proofs.E2E.TagSync1KeyReal
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.SignalWireRoundTrip
import VCVio.EvalDist.Monad.Basic

/-!
# Lazy-vs-Exact 1-Key Prefix Equivalence for Tracked and Halted Drivers

**Checked by Lean.** Proves tag-synchronized lazy `DRKey` coupling at creation index `k` for
`SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P` on per-session tracked and halted prefix experiments.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped ENNReal BigOperators
open OracleComp OracleSpec

namespace Computational.Proofs.LibsignalCli.MainHaltedLazy1Key

open Computational.Proofs.LibsignalCli.MainHaltedKeyInd (BHE2EDrvStateTracked
  bhE2EStepLocalSmTracked bhE2EStepLocalSmTracked_with_st)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (BHDrvPrefixKeyBitGen
  ModelDriverKeyBitGen SessionHaltTracker bhComposedPostObs
  bhComposedPostObsSessionTracked bhE2EDrvImplGenWithSessionTracked
  bhE2EDrvImplPrefixWithSessionTracked bhE2ELocalStartGenWithSessionTracked
  bhE2EStepLocalSmSessionTracked bhFinishStartSpkGen bhMkPrefixExact
  bhMkPrefixLazy bhPrefixExactFullExpWithSessionTracked
  bhPrefixLazyFullExpWithSessionTracked coinLogSessionTracker
  oracleImplRSessionTracked)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoGames.SM (GameState initState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (BHE2EDrvState BHE2ESmResp BHModelInst Bytes
  DrvInst DrvState DrvTagSyncInv1KeyReal KeyInd1KeyLazyState ModelDriverBase
  ModelDriverInstanceMeta SampledSessionKey allTestedSessionsFresh bhBytesWord
  bhDecodePreKeyMsgE bhDrvKiQueryOk bhE2EDrvInstClean
  bhE2EDrvWon bhE2EGuard bhE2EInstIkACorr bhE2EMirror bhExpectedPreKeyMsg
  bhHdrOfPreKeyMsg bhIdKeyOf bhInitRegId bhIsBobAcceptSMResp bhIsBobRecvSMQuery
  bhKeySOf bhNoOpkRespPromoted bhPackSmResp bhTargetGameSpec
  bhUnpackSmResp composedClean configRefuseEarlyBobCorr drvMirror
  evalDist_sampleDRKey96_keySOf_eq_select_keyS
  evalDist_simulateQ_pqxdhKeyIndImpl1KeyReal_false_eq_tagImpl keySOf
  kioFullImpl kioKind lengths_of_mem_support_sampleDRKey96 paramsIdsWithSpqr
  pqxdhKeyIndTagImpl1KeyReal pqxdhKeyIndTagImpl1KeyReal_non_test_sync
  pqxdhKeyIndTagImpl1KeyReal_testSession_of_not_fresh prob_bind_congr_of_support
  sessionSchemeFixedSpk shortCiphertext
  signalPqxdh_pqxdhKeyIndImpl1KeyReal_eq simulateQ_kioFullImpl_kioKind
  simulateQ_kioFullImpl_liftM_run tagImpl1KeyReal_startDR_steps wirePrekey)
section TrackedPrefixLazy1Key
variable {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}

@[simp] private theorem stateT_run_lift_tr {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) : (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp] private theorem stateT_run_liftM_tr {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) : (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

private abbrev BHKioDrvMTracked (τ : Type) (S : SignalPqxdh.Setup) (ℓ : ℕ) (M : Type → Type) :=
  StateT (BHE2EDrvState S ℓ × List τ) M

@[simp] private theorem bhKioDrvMTracked_run_liftM {M : Type → Type} [Monad M]
    [MonadLiftT ProbComp M] {α : Type} (mx : ProbComp α) (σH : BHE2EDrvState S ℓ × List τ) :
    (liftM mx : BHKioDrvMTracked τ S ℓ M α).run σH = ((liftM mx : M α) >>= fun x => pure (x, σH)) := rfl

private def bhToDrvInstLocal (d : BHModelInst S ℓ) : DrvInst S ℓ :=
  { sid := d.sid, hdr := d.hdr, idA := d.idA, idB := d.idB, spkCoins := d.spkCoins, gs := d.gs }

private def bhToDrvStateLocal (σ : BHE2EDrvState S ℓ) : DrvState S ℓ :=
  { insts := σ.insts.map bhToDrvInstLocal, prins := σ.prins, sends := σ.sends,
    bundles := σ.bundles.map (fun (idx, (spkB, _)) => (idx, spkB)) }

private theorem bhToDrvStateLocal_bhE2EMirror (σ : BHE2EDrvState S ℓ)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) :
    bhToDrvStateLocal (bhE2EMirror σ q r) = drvMirror (bhToDrvStateLocal σ) q r := by
  cases q <;> cases r <;> rfl

private theorem drvMirror_revealSpkSk_local (ds : DrvState S ℓ) (u : Fin S.N_id) (j' : Fin S.N_recv)
    (r : SignalPqxdh.KeyIndResponse) : drvMirror ds (.revealSpkSk u j') r = ds := by
  cases r <;> rfl

private theorem bhDrvKiQueryOk_ne_testSession_local (P : SignalPqxdh.Primitives)
    (base : ModelDriverBase S) (kq : SignalPqxdh.KeyIndQuery S)
    (hOk : bhDrvKiQueryOk P base kq = true) : ∀ sid, kq ≠ .testSession sid := by
  intro sid h; subst h; simp [bhDrvKiQueryOk] at hOk

private def bhFinishStartSpkSuccLocal (C : Crypto) (K : MlKem) (σ : BHE2EDrvState S ℓ)
    (sid : SignalPqxdh.SessionId S) (hdr : SignalPqxdh.HandshakeHdr)
    (bnd : SignalPqxdh.PreKeyBundleInput) (uj : Fin S.N_id × Fin S.N_recv)
    (spkSk : SignalPqxdh.Bytes) (kb : SampledSessionKey × Bool) : Option ℕ × BHE2EDrvState S ℓ :=
  let idA := bhIdKeyOf hdr.ikAPk; let idB := bhIdKeyOf bnd.ikB; let spkCoins := bhBytesWord spkSk
  let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
    ℓ spkCoins
  let inst : BHModelInst S ℓ :=
    { sid, hdr, idA, idB, spkCoins, gs := some (initState sch.sendPart kb.1 kb.2) }
  let im : ModelDriverInstanceMeta S :=
    { respPrin := some uj.1, respSpkIdx := some uj.2, instOpkId? := hdr.opkId? }
  (some σ.insts.length, { σ with insts := σ.insts ++ [inst], instMeta := σ.instMeta ++ [im] })

private theorem bhFinishStartSpkGen_eq_succ_local (C : Crypto) (K : MlKem) (σ : BHE2EDrvState S ℓ)
    (sid : SignalPqxdh.SessionId S) {hdr : SignalPqxdh.HandshakeHdr}
    {bnd : SignalPqxdh.PreKeyBundleInput} {u : Fin S.N_id} {j' : Fin S.N_recv}
    (hG : bhE2EGuard σ sid = some (hdr, bnd, (u, j'))) {dk : SignalPqxdh.DRKey}
    (hdk : dk ∈ support SignalPqxdh.sampleDRKey96) {spkSk : SignalPqxdh.Bytes}
    (hspk : spkSk.length = 32) (kb : SampledSessionKey × Bool) :
    bhFinishStartSpkGen C K σ sid (.drKeyResp dk) (.spkSkResp spkSk) kb =
      bhFinishStartSpkSuccLocal C K σ sid hdr bnd (u, j') spkSk kb := by
  rcases lengths_of_mem_support_sampleDRKey96 hdk with ⟨hrk, hck, hpqr⟩
  unfold bhFinishStartSpkGen bhFinishStartSpkSuccLocal; simp [hG, hrk, hck, hpqr, hspk]

def bhRefuseCorruptIK (ims : List (ModelDriverInstanceMeta S))
    (kq : SignalPqxdh.KeyIndQuery S) : Bool :=
  match kq with | .corruptIK u => bhNoOpkRespPromoted ims u | _ => false

/-- Parameterized tracked E2E driver implementation for a fixed `mkKeyBit` and arbitrary `smImpl`. -/
def bhE2EDrvImplGenWithTracked (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (mkKeyBit : ModelDriverKeyBitGen) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ × List τ) ProbComp) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let σH ← get; let σ := σH.1
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then return .noneResp
    else if bhRefuseCorruptIK σ.instMeta kq then return .noneResp
    else
      let (kr, st') ← liftM ((ki kq).run σ.st)
      set (bhE2EMirror { σ with st := st' } kq kr, σH.2); return kr
  | .inr (.inl (.inr (.startDR sid))) => do
    let σH ← get
    let (idx?, σH') ← liftM (bhE2ELocalStartGenWithSessionTracked initTrack ki C K mkKeyBit σH sid)
    set σH'; return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σH ← get
    let (sr, σH') ← liftM (bhE2EStepLocalSmTracked initTrack smImpl σH i sq)
    set σH'; return bhUnpackSmResp sq sr

/-- Parameterized tracked E2E driver implementation for a prefix generator `mkP`. -/
def bhE2EDrvImplPrefixWithTracked (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (mkP : BHDrvPrefixKeyBitGen) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ × List τ) ProbComp) := fun q =>
  StateT.mk fun σH =>
    (bhE2EDrvImplGenWithTracked initTrack smImpl ki P C K (mkP σH.1.insts.length) q).run σH

private theorem bhE2EDrvImplPrefixWithTracked_run_eq_gen (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (mkP : BHDrvPrefixKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) :
    (bhE2EDrvImplPrefixWithTracked initTrack smImpl ki P C K mkP q).run σH =
      (bhE2EDrvImplGenWithTracked initTrack smImpl ki P C K
        (mkP σH.1.insts.length) q).run σH := rfl

/-- Exact per-session tracked prefix experiment for hybrid step `k`. -/
def bhPrefixExactFullExpWithTracked (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool :=
  (simulateQ (bhE2EDrvImplPrefixWithTracked initTrack smImpl ki P C K
      (bhMkPrefixExact k b_k)) B).run ({}, []) >>=
    bhComposedPostObsSessionTracked P

/-- Lazy per-session tracked prefix experiment for hybrid step `k`. -/
def bhPrefixLazyFullExpWithTracked (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) : ProbComp Bool :=
  (simulateQ (bhE2EDrvImplPrefixWithTracked initTrack smImpl ki P C K
      (bhMkPrefixLazy k b_k)) B).run ({}, []) >>=
    bhComposedPostObsSessionTracked P

private def bhKioKeyIndTracked {M : Type → Type} [Monad M] (P : SignalPqxdh.Primitives)
    (kio : (q : SignalPqxdh.KeyIndQuery S) → M SignalPqxdh.KeyIndResponse)
    (kq : SignalPqxdh.KeyIndQuery S) : BHKioDrvMTracked τ S ℓ M SignalPqxdh.KeyIndResponse := do
  let σH ← get; let σ := σH.1
  if !bhDrvKiQueryOk P σ.toModelDriverBase kq then return .noneResp
  else if bhRefuseCorruptIK σ.instMeta kq then return .noneResp
  else
    let kr ← StateT.lift (kio kq)
    modify fun σH => (bhE2EMirror σH.1 kq kr, σH.2); return kr

private def bhKioStartGenTracked {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (initTrack : SampledSessionKey → τ) (C : Crypto) (K : MlKem)
    (kio : (q : SignalPqxdh.KeyIndQuery S) → M SignalPqxdh.KeyIndResponse)
    (mkKB : ModelDriverKeyBitGen) (sid : SignalPqxdh.SessionId S) :
    BHKioDrvMTracked τ S ℓ M (Option ℕ) := do
  let σH ← get
  match bhE2EGuard σH.1 sid with
  | none => return none
  | some (_, _, (u, j)) =>
    let kr1 ← StateT.lift (kio (.testSession sid))
    let kr2 ← StateT.lift (kio (.revealSpkSk u j))
    let kb ← liftM (mkKB kr1 kr2)
    let (idx?, σ') := bhFinishStartSpkGen C K σH.1 sid kr1 kr2 kb
    set (σ', if idx?.isSome then σH.2 ++ [initTrack kb.1] else σH.2); return idx?

private def bhKioSmTracked {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    BHKioDrvMTracked τ S ℓ M
      ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) := do
  let σH ← get
  let (sr, σH') ← liftM (bhE2EStepLocalSmTracked initTrack smImpl σH i sq)
  set σH'; return bhUnpackSmResp sq sr

private def bhKioImplGenTracked {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (kio : (q : SignalPqxdh.KeyIndQuery S) → M SignalPqxdh.KeyIndResponse)
    (mkKB : ModelDriverKeyBitGen) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (BHKioDrvMTracked τ S ℓ M) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => bhKioKeyIndTracked P kio kq
  | .inr (.inl (.inr (.startDR sid))) => bhKioStartGenTracked initTrack C K kio mkKB sid
  | .inr (.inr ⟨i, sq⟩) => bhKioSmTracked initTrack smImpl i sq

private def bhKioImplPrefixTracked {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (kio : (q : SignalPqxdh.KeyIndQuery S) → M SignalPqxdh.KeyIndResponse)
    (mkP : BHDrvPrefixKeyBitGen) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (BHKioDrvMTracked τ S ℓ M) := fun q =>
  StateT.mk fun σH =>
    (bhKioImplGenTracked initTrack smImpl P C K kio (mkP σH.1.insts.length) q).run σH

private theorem bhKioImplPrefixTracked_run_eq_gen {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (kio : (q : SignalPqxdh.KeyIndQuery S) → M SignalPqxdh.KeyIndResponse)
    (mkP : BHDrvPrefixKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) :
    (bhKioImplPrefixTracked initTrack smImpl P C K kio mkP q).run σH =
      (bhKioImplGenTracked initTrack smImpl P C K kio (mkP σH.1.insts.length) q).run σH := rfl

private theorem bhE2EMirror_with_st_tr
    (σ : BHE2EDrvState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    bhE2EMirror { σ with st := st } kq kr = { bhE2EMirror σ kq kr with st := st } := by
  cases kq <;> cases r : kr <;> rfl

private theorem bhFinishStartSpkGen_with_st_tr
    (C : Crypto) (K : MlKem) (σ : BHE2EDrvState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (kb : SampledSessionKey × Bool) :
    bhFinishStartSpkGen C K { σ with st := st } sid kr1 kr2 kb =
      let (idx?, σ') := bhFinishStartSpkGen C K σ sid kr1 kr2 kb
      (idx?, { σ' with st := st }) := by
  unfold bhFinishStartSpkGen
  have hG : bhE2EGuard { σ with st := st } sid = bhE2EGuard σ sid := rfl
  rw [hG]
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    cases kr1 <;> cases kr2 <;> try rfl
    dsimp only; split_ifs <;> rfl

private theorem bhE2EDrvImplGenWithTracked_step_eq_bhKioImplGenTracked
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (mkKB : ModelDriverKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) (st : SignalPqxdh.KeyIndState S) :
    (bhE2EDrvImplGenWithTracked initTrack smImpl ki P C K mkKB q).run
        ({ σH.1 with st := st }, σH.2) =
      (fun ((r, σH'), st') => (r, ({ σH'.1 with st := st' }, σH'.2))) <$>
        (((bhKioImplGenTracked initTrack smImpl P C K ki mkKB q).run σH).run st) := by
  rcases σH with ⟨σ, logs⟩
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · dsimp only [bhE2EDrvImplGenWithTracked, bhKioImplGenTracked]
    simp only [bhKioDrvMTracked_run_liftM, stateT_run_liftM_tr, StateT.run_bind,
      StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  · dsimp only [bhE2EDrvImplGenWithTracked, bhKioImplGenTracked, bhKioKeyIndTracked]
    have hBase : ({ σ with st := st } : BHE2EDrvState S ℓ).toModelDriverBase = σ.toModelDriverBase := rfl
    have hRefEq : bhRefuseCorruptIK ({ σ with st := st } : BHE2EDrvState S ℓ).instMeta kq =
        bhRefuseCorruptIK σ.instMeta kq := rfl
    by_cases hOk : bhDrvKiQueryOk P σ.toModelDriverBase kq = true
    · by_cases hRef : bhRefuseCorruptIK σ.instMeta kq = true
      · simp only [hBase, hRefEq, hOk, hRef, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_def, pure_bind]
      · have hRefF : bhRefuseCorruptIK σ.instMeta kq = false := Bool.eq_false_iff.mpr hRef
        simp only [hBase, hRefEq, hOk, hRefF, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, stateT_run_lift_tr, stateT_run_liftM_tr,
          StateT.run_set, StateT.run_modify, StateT.run_pure,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, bhE2EMirror_with_st_tr]
    · have hOkF : bhDrvKiQueryOk P σ.toModelDriverBase kq = false := Bool.eq_false_iff.mpr hOk
      simp only [hBase, hOkF, Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
        StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, pure_bind]
  · dsimp only [bhE2EDrvImplGenWithTracked, bhKioImplGenTracked, bhKioStartGenTracked,
      bhE2ELocalStartGenWithSessionTracked]
    have hG : bhE2EGuard { σ with st := st } sid = bhE2EGuard σ sid := rfl
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM_tr, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, hG]
    cases bhE2EGuard σ sid with
    | none =>
      simp only [StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def, pure_bind]
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      simp only [stateT_run_lift_tr, bhKioDrvMTracked_run_liftM, stateT_run_liftM_tr,
        StateT.run_bind, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp,
        Function.comp_def, bind_assoc, pure_bind, bhFinishStartSpkGen_with_st_tr]
  · dsimp only [bhE2EDrvImplGenWithTracked, bhKioImplGenTracked, bhKioSmTracked]
    simp only [StateT.run_bind, StateT.run_get, bhKioDrvMTracked_run_liftM,
      stateT_run_liftM_tr, StateT.run_set, StateT.run_pure,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rw [bhE2EStepLocalSmTracked_with_st initTrack smImpl (σ, logs) st i sq]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

private theorem simulateQ_bhE2EDrvImplPrefixWithTracked_eq_bhKioImplPrefixTracked {α : Type}
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (mkP : BHDrvPrefixKeyBitGen)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvState S ℓ × List τ) (st : SignalPqxdh.KeyIndState S) :
    (simulateQ (bhE2EDrvImplPrefixWithTracked initTrack smImpl ki P C K mkP) oa).run
        ({ σH.1 with st := st }, σH.2) =
      (fun ((r, σH'), st') => (r, ({ σH'.1 with st := st' }, σH'.2))) <$>
        (((simulateQ (bhKioImplPrefixTracked initTrack smImpl P C K ki mkP) oa).run σH).run st) := by
  induction oa using OracleComp.inductionOn generalizing σH st with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, StateT.run_bind,
      bhE2EDrvImplPrefixWithTracked_run_eq_gen, bhKioImplPrefixTracked_run_eq_gen]
    have hlen : ({ σH.1 with st := st } : BHE2EDrvState S ℓ).insts.length = σH.1.insts.length := rfl
    rw [hlen, bhE2EDrvImplGenWithTracked_step_eq_bhKioImplGenTracked]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    congr 1; funext p; rcases p with ⟨⟨r, σH'⟩, st'⟩
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using ih r σH' st'

private theorem simulateQ_bhKioImplGenTracked_kioKind_step {St : Type}
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (kioImpl : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT St ProbComp))
    (mkKB : ModelDriverKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) (st : St) :
    (simulateQ (kioFullImpl kioImpl)
      ((bhKioImplGenTracked initTrack smImpl P C K (kioKind S) mkKB q).run σH)).run st =
    ((bhKioImplGenTracked initTrack smImpl P C K kioImpl mkKB q).run σH).run st := by
  rcases σH with ⟨σ, logs⟩
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · dsimp only [bhKioImplGenTracked]
    simp only [bhKioDrvMTracked_run_liftM, stateT_run_liftM_tr, simulateQ_bind, StateT.run_bind,
      simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    rw [simulateQ_kioFullImpl_liftM_run kioImpl (query (spec := unifSpec) n) st]
    rfl
  · dsimp only [bhKioImplGenTracked, bhKioKeyIndTracked]
    by_cases hOk : bhDrvKiQueryOk P σ.toModelDriverBase kq = true
    · by_cases hRef : bhRefuseCorruptIK σ.instMeta kq = true
      · simp only [hOk, hRef, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, simulateQ_pure]
      · have hRefF : bhRefuseCorruptIK σ.instMeta kq = false := Bool.eq_false_iff.mpr hRef
        simp only [hOk, hRefF, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, stateT_run_lift_tr, StateT.run_modify, StateT.run_pure,
          bind_assoc, pure_bind, simulateQ_bind, simulateQ_kioFullImpl_kioKind, simulateQ_pure]
    · have hOkF : bhDrvKiQueryOk P σ.toModelDriverBase kq = false := Bool.eq_false_iff.mpr hOk
      simp only [hOkF, Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
        StateT.run_pure, pure_bind, simulateQ_pure]
  · dsimp only [bhKioImplGenTracked, bhKioStartGenTracked]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bhE2EGuard σ sid with
    | none => simp only [StateT.run_pure, simulateQ_pure]
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      simp only [stateT_run_lift_tr, bhKioDrvMTracked_run_liftM, stateT_run_liftM_tr,
        StateT.run_bind, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, simulateQ_bind,
        simulateQ_kioFullImpl_kioKind, simulateQ_pure]
      refine bind_congr fun ⟨kr1, st1⟩ => bind_congr fun ⟨kr2, st2⟩ => ?_
      rw [simulateQ_kioFullImpl_liftM_run kioImpl (mkKB kr1 kr2) st2]
      simp only [stateT_run_lift_tr, bind_assoc, pure_bind]
  · dsimp only [bhKioImplGenTracked, bhKioSmTracked]
    simp only [StateT.run_bind, StateT.run_get, bhKioDrvMTracked_run_liftM, stateT_run_liftM_tr,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure]
    rw [simulateQ_kioFullImpl_liftM_run kioImpl
      (bhE2EStepLocalSmTracked initTrack smImpl (σ, logs) i sq) st]
    simp only [stateT_run_lift_tr, bind_assoc, pure_bind]

private theorem simulateQ_bhKioImplPrefixTracked_kioKind_run {α St : Type}
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (kioImpl : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT St ProbComp))
    (mkP : BHDrvPrefixKeyBitGen)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvState S ℓ × List τ) (st : St) :
    (simulateQ (kioFullImpl kioImpl)
      ((simulateQ (bhKioImplPrefixTracked initTrack smImpl P C K (kioKind S) mkP) oa).run σH)).run st =
    (((simulateQ (bhKioImplPrefixTracked initTrack smImpl P C K kioImpl mkP) oa).run σH).run st) := by
  induction oa using OracleComp.inductionOn generalizing σH st with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    simp only [simulateQ_bind, StateT.run_bind, bhKioImplPrefixTracked_run_eq_gen,
      simulateQ_bhKioImplGenTracked_kioKind_step]
    exact bind_congr fun p => ih p.1.1 p.1.2 p.2

private theorem bhE2EGuard_eq_some_props_tr
    {σ : BHE2EDrvState S ℓ} {sid : SignalPqxdh.SessionId S}
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u : Fin S.N_id} {j' : Fin S.N_recv}
    (hG : bhE2EGuard σ sid = some (hdr, bnd, (u, j'))) :
    (sid, bnd, hdr) ∈ (bhToDrvStateLocal σ).sends ∧
    (∃ pk, ((u, j'), pk) ∈ (bhToDrvStateLocal σ).bundles) ∧
    (∀ d ∈ (bhToDrvStateLocal σ).insts, d.hdr.ekAPk ≠ hdr.ekAPk) := by
  unfold bhE2EGuard at hG
  by_cases h1 : (σ.insts.any (fun d => d.sid == sid)) = true
  · simp [h1] at hG
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hG
    cases hs : σ.sends.find? (fun (s, _, _) => s == sid) with
    | none => simp [hs] at hG
    | some se =>
      rcases se with ⟨sid0, bnd0, hdr0⟩
      rw [hs] at hG; dsimp only at hG
      by_cases h2 : (σ.insts.any (fun d => d.hdr.ekAPk == hdr0.ekAPk)) = true
      · simp [h2] at hG
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hG
        cases hb : σ.bundles.find? (fun ((_, j), (spkB, pqspkB)) =>
            spkB == bnd0.spkB && pqspkB == bnd0.pqspkB &&
            hdr0.spkId == UInt32.ofNat j.val &&
            hdr0.pqspkId == UInt32.ofNat j.val) with
        | none => simp [hb] at hG
        | some be =>
          rcases be with ⟨⟨u0, j0⟩, ⟨spkB0, pqspkB0⟩⟩
          rw [hb] at hG; dsimp only at hG
          split_ifs at hG with h3
          simp only [Option.some.injEq, Prod.mk.injEq] at hG
          rcases hG with ⟨rfl, rfl, rfl, rfl⟩
          have hsid0 : sid0 = sid := beq_iff_eq.mp (by simpa using List.find?_some hs)
          subst hsid0
          refine ⟨List.mem_of_find?_eq_some hs, ⟨spkB0, ?_⟩, fun d hd hEq => ?_⟩
          · dsimp only [bhToDrvStateLocal]
            exact List.mem_map.mpr ⟨((u0, j0), (spkB0, pqspkB0)), List.mem_of_find?_eq_some hb, rfl⟩
          · dsimp only [bhToDrvStateLocal] at hd
            rcases List.mem_map.mp hd with ⟨d0, hd0, rfl⟩
            exact h2 (List.any_eq_true.mpr ⟨d0, hd0, beq_iff_eq.mpr hEq⟩)

private theorem drvTagSyncInv1KeyReal_congr_state
    {P : SignalPqxdh.Primitives} {ds1 ds2 : DrvState S ℓ} {lst : KeyInd1KeyLazyState S}
    (h : DrvTagSyncInv1KeyReal P ds1 lst)
    (hsends : ds2.sends = ds1.sends)
    (hbundles : ds2.bundles = ds1.bundles)
    (hinsts : ∀ d1 ∈ ds1.insts, ∃ d2 ∈ ds2.insts, d2.hdr.ekAPk = d1.hdr.ekAPk) :
    DrvTagSyncInv1KeyReal P ds2 lst where
  core := h.core
  sends_sess x hx := h.sends_sess x (hsends ▸ hx)
  bundles_spk b hb := h.bundles_spk b (hbundles ▸ hb)
  cache_insts k hk := by
    rcases h.cache_insts k hk with ⟨d1, hd1, e, he, hk_eq, hek_eq⟩
    rcases hinsts d1 hd1 with ⟨d2, hd2, hd2_eq⟩
    exact ⟨d2, hd2, e, he, hk_eq, hd2_eq.trans hek_eq⟩

private theorem runTracked_preserves_tagSync
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives) (σ : BHE2EDrvState S ℓ) (logs : List τ)
    (i : ℕ) (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (hi : σ.insts[i]? = some d)
    (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (lst : KeyInd1KeyLazyState S) (hSync : DrvTagSyncInv1KeyReal P (bhToDrvStateLocal σ) lst)
    {p : BHE2ESmResp ℓ × BHE2EDrvStateTracked τ S ℓ}
    (hp : p ∈ support (do
      let tr₀ := (logs[i]?).getD (initTrack default)
      let ((r, gs'), log') ← ((smImpl d q').run gs).run tr₀
      let accepted := bhIsBobAcceptSMResp q' r
      let im' := if !im.bobAccepted && accepted then
          { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
        else im
      let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                         instMeta := σ.instMeta.set i im' }
      return (bhPackSmResp q' r, (σ1, logs.set i log')))) :
    DrvTagSyncInv1KeyReal P (bhToDrvStateLocal p.2.1) lst := by
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
  rcases hp with ⟨⟨⟨r, gs'⟩, log'⟩, _, rfl⟩
  refine drvTagSyncInv1KeyReal_congr_state hSync rfl rfl fun d1 hd1 => ?_
  dsimp only [bhToDrvStateLocal] at hd1 ⊢
  rcases List.mem_map.mp hd1 with ⟨d0, hd0, rfl⟩
  rcases List.mem_iff_getElem.mp hd0 with ⟨idx, hidx, rfl⟩
  by_cases hEqIdx : i = idx
  · subst hEqIdx
    have hd_eq : σ.insts[i] = d := Option.some.inj ((List.getElem?_eq_getElem hidx).symm.trans hi)
    have hidx' : i < (σ.insts.set i { d with gs := some gs' }).length := by simpa using hidx
    refine ⟨bhToDrvInstLocal { d with gs := some gs' },
      List.mem_map.mpr ⟨{ d with gs := some gs' },
        List.mem_iff_getElem.mpr ⟨i, hidx', by simp⟩, rfl⟩, ?_⟩
    simp [bhToDrvInstLocal, hd_eq]
  · have hidx' : idx < (σ.insts.set i { d with gs := some gs' }).length := by simpa using hidx
    exact ⟨bhToDrvInstLocal σ.insts[idx],
      List.mem_map.mpr ⟨σ.insts[idx],
        List.mem_iff_getElem.mpr ⟨idx, hidx', by simp [List.getElem_set_ne hEqIdx]⟩, rfl⟩, rfl⟩

private theorem bhE2EStepLocalSmTracked_preserves_tagSync1KeyReal
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) (lst : KeyInd1KeyLazyState S)
    (hSync : DrvTagSyncInv1KeyReal P (bhToDrvStateLocal σH.1) lst)
    {p : BHE2ESmResp ℓ × BHE2EDrvStateTracked τ S ℓ}
    (hp : p ∈ support (bhE2EStepLocalSmTracked initTrack smImpl σH i sq)) :
    DrvTagSyncInv1KeyReal P (bhToDrvStateLocal p.2.1) lst := by
  rcases σH with ⟨σ, logs⟩
  unfold bhE2EStepLocalSmTracked at hp
  dsimp only at hp
  by_cases hClean : (!bhE2EDrvInstClean σ i) = true
  · simp only [hClean, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hSync
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte] at hp
    cases hi : σ.insts[i]? with
    | none => simp only [hi, support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hSync
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => simp only [hi, him, support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hSync
      | some im =>
        simp only [hi, him] at hp
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp only [hCorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
          subst hp; exact hSync
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hp
          cases hd : d.gs with
          | none => simp only [hd, support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hSync
          | some gs =>
            simp only [hd] at hp
            have hRun := fun q' => runTracked_preserves_tagSync initTrack smImpl P σ logs i d im gs
              hi q' lst hSync (p := p)
            rcases sq with (((q1 | q2) | ⟨pty, c⟩) | ⟨pty, c⟩) | q5
            · exact hRun _ hp
            · exact hRun _ hp
            · cases pty with
              | A =>
                dsimp only at hp; split_ifs at hp
                · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hSync
                · exact hRun _ hp
              | B =>
                dsimp only at hp; split_ifs at hp
                · cases hDec : bhDecodePreKeyMsgE c <;> simp only [hDec] at hp
                  · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hSync
                  · split_ifs at hp
                    · exact hRun _ hp
                    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hSync
                · cases hDec : bhDecodePreKeyMsgE c <;> simp only [hDec] at hp
                  · exact hRun _ hp
                  · split_ifs at hp
                    · exact hRun _ hp
                    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hSync
            · cases pty with
              | A =>
                dsimp only at hp; split_ifs at hp
                · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hSync
                · exact hRun _ hp
              | B =>
                dsimp only at hp; split_ifs at hp
                · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hSync
                · cases hDec : bhDecodePreKeyMsgE c <;> simp only [hDec] at hp
                  · exact hRun _ hp
                  · split_ifs at hp
                    · exact hRun _ hp
                    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hSync
            · exact hRun _ hp

private theorem bhKioKeyIndTracked_tagImpl1KeyReal_sync
    (P : SignalPqxdh.Primitives) (kq : SignalPqxdh.KeyIndQuery S)
    (σH : BHE2EDrvState S ℓ × List τ) (lst : KeyInd1KeyLazyState S)
    (hSync : DrvTagSyncInv1KeyReal P (bhToDrvStateLocal σH.1) lst)
    (rc2 : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)) :
    ((bhKioKeyIndTracked P (pqxdhKeyIndTagImpl1KeyReal false false S P) kq).run σH).run
        { lst with randCache := rc2 } =
      (fun (r_σ, l1) => (r_σ, { l1 with randCache := rc2 })) <$>
        ((bhKioKeyIndTracked P (pqxdhKeyIndTagImpl1KeyReal false false S P) kq).run σH).run lst ∧
    ∀ r σH' l1, ((r, σH'), l1) ∈ support
        (((bhKioKeyIndTracked P (pqxdhKeyIndTagImpl1KeyReal false false S P) kq).run σH).run lst) →
      DrvTagSyncInv1KeyReal P (bhToDrvStateLocal σH'.1) l1 ∧ l1.randCache = lst.randCache := by
  rcases σH with ⟨σ, logs⟩
  unfold bhKioKeyIndTracked
  by_cases hOk : bhDrvKiQueryOk P σ.toModelDriverBase kq = true
  · by_cases hRef : bhRefuseCorruptIK σ.instMeta kq = true
    · simp only [hOk, hRef, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, map_pure,
        support_pure, Set.mem_singleton_iff]
      refine ⟨trivial, fun r σH' l1 hEq => ?_⟩
      rcases Prod.mk.inj hEq with ⟨hEq1, rfl⟩
      rcases Prod.mk.inj hEq1 with ⟨rfl, rfl⟩
      exact ⟨hSync, rfl⟩
    · have hRefF : bhRefuseCorruptIK σ.instMeta kq = false := Bool.eq_false_iff.mpr hRef
      have hNe := bhDrvKiQueryOk_ne_testSession_local P σ.toModelDriverBase kq hOk
      have ⟨hRunEq, hInv⟩ :=
        pqxdhKeyIndTagImpl1KeyReal_non_test_sync false P kq hNe (bhToDrvStateLocal σ) lst hSync rc2
      simp only [hOk, hRefF, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, stateT_run_lift_tr, StateT.run_modify,
        StateT.run_pure, bind_assoc, pure_bind, hRunEq]
      refine ⟨by simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind],
        fun r σH' l1 hMem => ?_⟩
      rw [support_bind] at hMem
      rcases Set.mem_iUnion₂.mp hMem with ⟨⟨r0, l0⟩, hMem0, hEq⟩
      rw [support_pure, Set.mem_singleton_iff] at hEq
      rcases Prod.mk.inj hEq with ⟨hEq1, rfl⟩
      rcases Prod.mk.inj hEq1 with ⟨rfl, rfl⟩
      rw [bhToDrvStateLocal_bhE2EMirror]
      exact hInv r l1 hMem0
  · have hOkF : bhDrvKiQueryOk P σ.toModelDriverBase kq = false := Bool.eq_false_iff.mpr hOk
    simp only [hOkF, Bool.not_false, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_pure, pure_bind, map_pure, support_pure, Set.mem_singleton_iff]
    refine ⟨trivial, fun r σH' l1 hEq => ?_⟩
    rcases Prod.mk.inj hEq with ⟨hEq1, rfl⟩
    rcases Prod.mk.inj hEq1 with ⟨rfl, rfl⟩
    exact ⟨hSync, rfl⟩

private theorem bhKioSmTracked_tagImpl1KeyReal_sync
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) (lst : KeyInd1KeyLazyState S)
    (hSync : DrvTagSyncInv1KeyReal P (bhToDrvStateLocal σH.1) lst)
    (rc2 : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)) :
    ((bhKioSmTracked (M := StateT (KeyInd1KeyLazyState S) ProbComp) initTrack smImpl i sq).run σH).run
        { lst with randCache := rc2 } =
      (fun (r_σ, l1) => (r_σ, { l1 with randCache := rc2 })) <$>
        ((bhKioSmTracked (M := StateT (KeyInd1KeyLazyState S) ProbComp) initTrack smImpl i sq).run σH).run lst ∧
    ∀ r σH' l1, ((r, σH'), l1) ∈ support
        (((bhKioSmTracked (M := StateT (KeyInd1KeyLazyState S) ProbComp) initTrack smImpl i sq).run σH).run lst) →
      DrvTagSyncInv1KeyReal P (bhToDrvStateLocal σH'.1) l1 ∧ l1.randCache = lst.randCache := by
  unfold bhKioSmTracked
  simp only [StateT.run_bind, StateT.run_get, bhKioDrvMTracked_run_liftM,
    stateT_run_liftM_tr, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
  refine ⟨by simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind],
    fun r σH' l1 hMem => ?_⟩
  rw [support_bind] at hMem
  rcases Set.mem_iUnion₂.mp hMem with ⟨⟨sr, σH1⟩, hSm, hEq⟩
  rw [support_pure, Set.mem_singleton_iff] at hEq
  rcases Prod.mk.inj hEq with ⟨hEq1, rfl⟩
  rcases Prod.mk.inj hEq1 with ⟨rfl, rfl⟩
  exact ⟨bhE2EStepLocalSmTracked_preserves_tagSync1KeyReal initTrack smImpl P i sq σH l1 hSync hSm,
    rfl⟩

@[simp]
private theorem bhFinishStartSpkGen_noneResp_tr
    (C : Crypto) (K : MlKem) (σ : BHE2EDrvState S ℓ)
    (sid : SignalPqxdh.SessionId S) (kr2 : SignalPqxdh.KeyIndResponse)
    (kb : SampledSessionKey × Bool) :
    bhFinishStartSpkGen C K σ sid .noneResp kr2 kb = (none, σ) := by
  unfold bhFinishStartSpkGen; cases bhE2EGuard σ sid <;> rfl

private theorem bhKioStartGenTracked_tagImpl1KeyReal_of_not_fresh
    (initTrack : SampledSessionKey → τ) (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (mkKB : ModelDriverKeyBitGen)
    (sid : SignalPqxdh.SessionId S) (σH : BHE2EDrvState S ℓ × List τ) (lst : KeyInd1KeyLazyState S)
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u : Fin S.N_id} {j' : Fin S.N_recv}
    (hG : bhE2EGuard σH.1 sid = some (hdr, bnd, (u, j')))
    (hNotFresh : (!SignalPqxdh.isKeyIndSessionTestable lst.base sid) = true)
    (rc : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)) :
    ((bhKioStartGenTracked initTrack C K
        (pqxdhKeyIndTagImpl1KeyReal false false S P) mkKB sid).run σH).run
        { lst with randCache := rc } =
      (do
        let (kr2, l1) ←
          (pqxdhKeyIndTagImpl1KeyReal false false S P (.revealSpkSk u j')).run
            { lst with randCache := rc }
        let _ ← mkKB .noneResp kr2
        pure ((none, σH), l1)) := by
  rcases σH with ⟨σ, logs⟩
  have hTest := pqxdhKeyIndTagImpl1KeyReal_testSession_of_not_fresh false P sid lst hNotFresh rc
  unfold bhKioStartGenTracked
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hG, stateT_run_lift_tr,
    bind_assoc, hTest]
  simp only [pure_bind, StateT.run_bind, bhKioDrvMTracked_run_liftM, stateT_run_liftM_tr,
    StateT.run_set, StateT.run_pure, bind_assoc, bhFinishStartSpkGen_noneResp_tr,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

private theorem bhKioStartGenTracked_tagImpl1KeyReal_of_bhE2EGuard
    (initTrack : SampledSessionKey → τ) (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (sid : SignalPqxdh.SessionId S) (σH : BHE2EDrvState S ℓ × List τ) (lst : KeyInd1KeyLazyState S)
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u : Fin S.N_id} {j' : Fin S.N_recv}
    (hSync : DrvTagSyncInv1KeyReal P (bhToDrvStateLocal σH.1) lst)
    (hG : bhE2EGuard σH.1 sid = some (hdr, bnd, (u, j')))
    (hFresh : (!SignalPqxdh.isKeyIndSessionTestable lst.base sid) = false) :
    ∃ (rootKey spkSk : SignalPqxdh.Bytes) (base_after : SignalPqxdh.KeyIndState S),
      spkSk.length = 32 ∧
      (∀ (mkKB : ModelDriverKeyBitGen) (rc : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)),
        lst.randCache.map Prod.fst = rc.map Prod.fst →
        ((bhKioStartGenTracked initTrack C K
            (pqxdhKeyIndTagImpl1KeyReal false false S P) mkKB sid).run σH).run
            { lst with randCache := rc } =
          (do
            let dk ← SignalPqxdh.sampleDRKey96
            let kb ← mkKB (.drKeyResp dk) (.spkSkResp spkSk)
            let (res, σ') := bhFinishStartSpkSuccLocal C K σH.1 sid hdr bnd (u, j') spkSk kb
            pure ((res, (σ', σH.2 ++ [initTrack kb.1])),
              { base := base_after, randCache := (rootKey, dk) :: rc }))) ∧
      (∀ dk ∈ support SignalPqxdh.sampleDRKey96, ∀ (kb : SampledSessionKey × Bool),
        DrvTagSyncInv1KeyReal P
          (bhToDrvStateLocal (bhFinishStartSpkSuccLocal C K σH.1 sid hdr bnd (u, j') spkSk kb).2)
          { base := base_after, randCache := (rootKey, dk) :: lst.randCache }) := by
  rcases σH with ⟨σ, logs⟩
  rcases bhE2EGuard_eq_some_props_tr hG with ⟨hsend, hbnd, hinst⟩
  rcases tagImpl1KeyReal_startDR_steps P sid (bhToDrvStateLocal σ) lst hSync hsend hbnd hinst hFresh with
    ⟨rootKey, spkSk, base_t, base_after, hSpkLen, hTestRun, hRevRun, hSyncAfter⟩
  refine ⟨rootKey, spkSk, base_after, hSpkLen, ?_, ?_⟩
  · intro mkKB rc hrc
    unfold bhKioStartGenTracked
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hG, stateT_run_lift_tr, bind_assoc]
    rw [hTestRun rc hrc]
    simp only [bind_assoc, pure_bind, StateT.run_bind, stateT_run_lift_tr]
    refine prob_bind_congr_of_support SignalPqxdh.sampleDRKey96 _ _ (fun dk hdk => ?_)
    rw [hRevRun ((rootKey, dk) :: rc)]
    simp only [pure_bind, stateT_run_lift_tr, bhKioDrvMTracked_run_liftM,
      stateT_run_liftM_tr, StateT.run_bind, StateT.run_set, StateT.run_pure, bind_assoc,
      bhFinishStartSpkGen_eq_succ_local C K σ sid hG hdk hSpkLen]
    refine bind_congr fun kb => ?_
    simp [bhFinishStartSpkSuccLocal]
  · intro dk hdk kb
    let inst_new : BHModelInst S ℓ :=
      { sid := sid, hdr := hdr, idA := bhIdKeyOf hdr.ikAPk, idB := bhIdKeyOf bnd.ikB,
        spkCoins := bhBytesWord spkSk,
        gs := some (initState (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
            (bhIdKeyOf hdr.ikAPk) (bhIdKeyOf bnd.ikB)) ℓ
          (bhBytesWord spkSk)).sendPart kb.1 kb.2) }
    exact hSyncAfter dk hdk
      (bhToDrvStateLocal (bhFinishStartSpkSuccLocal C K σ sid hdr bnd (u, j') spkSk kb).2)
      (bhToDrvInstLocal inst_new)
      rfl rfl
      (by dsimp [bhToDrvStateLocal, bhFinishStartSpkSuccLocal, inst_new]
          rw [List.map_append, List.map_singleton])
      rfl

set_option maxHeartbeats 400000 in
private theorem evalDist_bhKioImplPrefixTracked_tagImpl1KeyReal_Lazy_eq_Exact {α : Type}
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (k : ℕ) (b_k : Bool)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvState S ℓ × List τ) (lst : KeyInd1KeyLazyState S)
    (rc2 : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (hSync : DrvTagSyncInv1KeyReal P (bhToDrvStateLocal σH.1) lst)
    (hCache : lst.randCache.map Prod.fst = rc2.map Prod.fst)
    (obs : (α × (BHE2EDrvState S ℓ × List τ)) × KeyInd1KeyLazyState S → ProbComp Bool)
    (hObs : ∀ x l rc, obs (x, { l with randCache := rc }) = obs (x, l)) :
    𝒟[(((simulateQ (bhKioImplPrefixTracked initTrack smImpl P C K
        (pqxdhKeyIndTagImpl1KeyReal false false S P)
        (bhMkPrefixLazy k b_k)) oa).run σH).run lst) >>= obs] =
    𝒟[(((simulateQ (bhKioImplPrefixTracked initTrack smImpl P C K
        (pqxdhKeyIndTagImpl1KeyReal false false S P)
        (bhMkPrefixExact k b_k)) oa).run σH).run { lst with randCache := rc2 }) >>= obs] := by
  induction oa using OracleComp.inductionOn generalizing σH lst rc2 with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact congrArg (fun z => 𝒟[z]) (hObs (x, σH) lst rc2).symm
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      bhKioImplPrefixTracked_run_eq_gen, bhKioImplPrefixTracked_run_eq_gen, bind_assoc, bind_assoc]
    rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
    · dsimp only [bhKioImplGenTracked]
      simp only [bhKioDrvMTracked_run_liftM, stateT_run_liftM_tr, StateT.run_bind,
        StateT.run_pure, bind_assoc, pure_bind]
      exact OracleComp.evalDist_bind_congr_of_support _ _ _
        (fun x _ => ih x σH lst rc2 hSync hCache)
    · dsimp only [bhKioImplGenTracked]
      have ⟨hRunEq, hInv⟩ := bhKioKeyIndTracked_tagImpl1KeyReal_sync P kq σH lst hSync rc2
      rw [hRunEq]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun p hMem => ?_)
      rcases p with ⟨⟨r, σH'⟩, l1⟩
      rcases hInv r σH' l1 hMem with ⟨hSync', hl1_rc⟩
      exact ih r σH' l1 rc2 hSync' (by rw [hl1_rc, hCache])
    · dsimp only [bhKioImplGenTracked]
      cases hG : bhE2EGuard σH.1 sid with
      | none =>
        unfold bhKioStartGenTracked
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hG, StateT.run_pure]
        exact ih none σH lst rc2 hSync hCache
      | some val =>
        rcases val with ⟨hdr, bnd, ⟨u, j'⟩⟩
        cases hNotFresh : (!SignalPqxdh.isKeyIndSessionTestable lst.base sid) with
        | true =>
          have hL := bhKioStartGenTracked_tagImpl1KeyReal_of_not_fresh initTrack P C K
            (bhMkPrefixLazy k b_k σH.1.insts.length) sid σH lst hG hNotFresh lst.randCache
          have hR := bhKioStartGenTracked_tagImpl1KeyReal_of_not_fresh initTrack P C K
            (bhMkPrefixExact k b_k σH.1.insts.length) sid σH lst hG hNotFresh rc2
          have hLst : { lst with randCache := lst.randCache } = lst := rfl
          rw [hLst] at hL
          rw [hL, hR]
          have ⟨hRevEq, hRevInv⟩ := pqxdhKeyIndTagImpl1KeyReal_non_test_sync false P
            (.revealSpkSk u j') (fun _ h => by nomatch h) (bhToDrvStateLocal σH.1) lst hSync rc2
          rw [hRevEq]
          simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun p hMem => ?_)
          rcases p with ⟨kr2, l1⟩
          rcases hRevInv kr2 l1 hMem with ⟨hSync', hl1_rc⟩
          rw [drvMirror_revealSpkSk_local] at hSync'
          have hMkEq : bhMkPrefixLazy k b_k σH.1.insts.length .noneResp kr2 =
              bhMkPrefixExact k b_k σH.1.insts.length .noneResp kr2 := rfl
          rw [hMkEq]
          exact OracleComp.evalDist_bind_congr_of_support _ _ _
            (fun _ _ => ih none σH l1 rc2 hSync' (by rw [hl1_rc, hCache]))
        | false =>
          rcases bhKioStartGenTracked_tagImpl1KeyReal_of_bhE2EGuard initTrack P C K sid σH lst
              hSync hG hNotFresh with ⟨rootKey, spkSk, base_after, hSpkLen, hRun, hSyncAfter⟩
          have hL := hRun (bhMkPrefixLazy k b_k σH.1.insts.length) lst.randCache rfl
          have hR := hRun (bhMkPrefixExact k b_k σH.1.insts.length) rc2 hCache
          have hLst : { lst with randCache := lst.randCache } = lst := rfl
          rw [hLst] at hL
          rw [hL, hR]
          simp only [bind_assoc, pure_bind]
          by_cases hSlot : (σH.1.insts.length == k) = true
          · have hLazyDk : ∀ dk ∈ support SignalPqxdh.sampleDRKey96,
                bhMkPrefixLazy k b_k σH.1.insts.length (.drKeyResp dk) (.spkSkResp spkSk) =
                  (do
                    let _ ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
                    let k_fresh ← ($ᵗ SampledSessionKey : ProbComp SampledSessionKey)
                    return (k_fresh, b_k)) := by
              intro dk hdk
              rcases lengths_of_mem_support_sampleDRKey96 hdk with ⟨hrk, hck, hpqr⟩
              unfold bhMkPrefixLazy; simp [hrk, hck, hpqr, hSpkLen, hSlot]
            have hExactDk : ∀ dk : SignalPqxdh.DRKey,
                bhMkPrefixExact k b_k σH.1.insts.length (.drKeyResp dk) (.spkSkResp spkSk) =
                  (do
                    let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
                    return (bhKeySOf dk ac, b_k)) := by
              intro dk; unfold bhMkPrefixExact; simp [hSlot]
            let cont : SampledSessionKey → ProbComp Bool := fun k_fresh =>
              let p := bhFinishStartSpkSuccLocal C K σH.1 sid hdr bnd (u, j') spkSk (k_fresh, b_k)
              (((simulateQ (bhKioImplPrefixTracked initTrack smImpl P C K
                (pqxdhKeyIndTagImpl1KeyReal false false S P)
                (bhMkPrefixExact k b_k)) (mx p.1)).run (p.2, σH.2 ++ [initTrack k_fresh])).run
                  { base := base_after, randCache := (rootKey, default) :: rc2 }) >>= obs
            let stepRun (mkP : BHDrvPrefixKeyBitGen) (kb : SampledSessionKey × Bool)
                (rc : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)) : ProbComp Bool :=
              let p := bhFinishStartSpkSuccLocal C K σH.1 sid hdr bnd (u, j') spkSk kb
              (((simulateQ (bhKioImplPrefixTracked initTrack smImpl P C K
                (pqxdhKeyIndTagImpl1KeyReal false false S P) mkP) (mx p.1)).run
                  (p.2, σH.2 ++ [initTrack kb.1])).run
                  { base := base_after, randCache := rc }) >>= obs
            have hL_step : ∀ dk ∈ support SignalPqxdh.sampleDRKey96,
                𝒟[bhMkPrefixLazy k b_k σH.1.insts.length (.drKeyResp dk) (.spkSkResp spkSk) >>=
                  fun kb => stepRun (bhMkPrefixLazy k b_k) kb ((rootKey, dk) :: lst.randCache)] =
                𝒟[($ᵗ SampledSessionKey : ProbComp SampledSessionKey) >>= cont] := by
              intro dk hdk; rw [hLazyDk dk hdk]
              simp only [bind_assoc, pure_bind, OracleComp.evalDist_bind_const]
              refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k_fresh _ => ?_)
              exact ih _ _ { base := base_after, randCache := (rootKey, dk) :: lst.randCache }
                ((rootKey, default) :: rc2) (hSyncAfter dk hdk (k_fresh, b_k)) (by simp [hCache])
            have hLHS :
                𝒟[SignalPqxdh.sampleDRKey96 >>= fun dk =>
                  bhMkPrefixLazy k b_k σH.1.insts.length (.drKeyResp dk) (.spkSkResp spkSk) >>=
                  fun kb => stepRun (bhMkPrefixLazy k b_k) kb ((rootKey, dk) :: lst.randCache)] =
                𝒟[($ᵗ SampledSessionKey : ProbComp SampledSessionKey) >>= cont] := by
              rw [OracleComp.evalDist_bind_congr_of_support _ _ _ hL_step,
                OracleComp.evalDist_bind_const]
            have hR_step : ∀ dk ∈ support SignalPqxdh.sampleDRKey96,
                𝒟[bhMkPrefixExact k b_k σH.1.insts.length (.drKeyResp dk) (.spkSkResp spkSk) >>=
                  fun kb => stepRun (bhMkPrefixExact k b_k) kb ((rootKey, dk) :: rc2)] =
                𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ac => cont (bhKeySOf dk ac)] := by
              intro dk hdk; rw [hExactDk dk]; simp only [bind_assoc, pure_bind]
              refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ac _ => ?_)
              let p := bhFinishStartSpkSuccLocal C K σH.1 sid hdr bnd (u, j') spkSk
                (bhKeySOf dk ac, b_k)
              have h1 := ih p.1 (p.2, σH.2 ++ [initTrack (bhKeySOf dk ac)])
                { base := base_after, randCache := (rootKey, dk) :: lst.randCache }
                ((rootKey, dk) :: rc2) (hSyncAfter dk hdk _) (by simp [hCache])
              have h2 := ih p.1 (p.2, σH.2 ++ [initTrack (bhKeySOf dk ac)])
                { base := base_after, randCache := (rootKey, dk) :: lst.randCache }
                ((rootKey, default) :: rc2) (hSyncAfter dk hdk _) (by simp [hCache])
              exact h1.symm.trans h2
            change 𝒟[SignalPqxdh.sampleDRKey96 >>= fun dk =>
                bhMkPrefixLazy k b_k σH.1.insts.length (.drKeyResp dk) (.spkSkResp spkSk) >>=
                fun kb => stepRun (bhMkPrefixLazy k b_k) kb ((rootKey, dk) :: lst.randCache)] =
              𝒟[SignalPqxdh.sampleDRKey96 >>= fun dk =>
                bhMkPrefixExact k b_k σH.1.insts.length (.drKeyResp dk) (.spkSkResp spkSk) >>=
                fun kb => stepRun (bhMkPrefixExact k b_k) kb ((rootKey, dk) :: rc2)]
            rw [hLHS, OracleComp.evalDist_bind_congr_of_support _ _ _ hR_step]
            have hKeySOf : bhKeySOf = keySOf := rfl
            change 𝒟[($ᵗ SampledSessionKey : ProbComp SampledSessionKey) >>= cont] =
              𝒟[SignalPqxdh.sampleDRKey96 >>= fun dk =>
                ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ac => cont (bhKeySOf dk ac)]
            rw [hKeySOf]
            have hAssoc :
                (SignalPqxdh.sampleDRKey96 >>= fun dk =>
                  ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ac => cont (keySOf dk ac)) =
                ((do
                  let dk ← SignalPqxdh.sampleDRKey96
                  let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
                  return keySOf dk ac) >>= cont) := by
              simp only [bind_assoc, pure_bind]
            rw [hAssoc, evalDist_bind_of_discrete, evalDist_bind_of_discrete,
              evalDist_sampleDRKey96_keySOf_eq_select_keyS, bind_pure]
          · have hSlotF : (σH.1.insts.length == k) = false := Bool.eq_false_iff.mpr hSlot
            have hEqNotSlot : ∀ dk : SignalPqxdh.DRKey,
                bhMkPrefixLazy k b_k σH.1.insts.length (.drKeyResp dk) (.spkSkResp spkSk) =
                  bhMkPrefixExact k b_k σH.1.insts.length (.drKeyResp dk) (.spkSkResp spkSk) := by
              intro dk; unfold bhMkPrefixLazy bhMkPrefixExact; simp [hSlotF]
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun dk hdk => ?_)
            rw [hEqNotSlot dk]
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kb _ => ?_)
            exact ih _ _ { base := base_after, randCache := (rootKey, dk) :: lst.randCache }
              ((rootKey, dk) :: rc2) (hSyncAfter dk hdk kb) (by simp [hCache])
    · dsimp only [bhKioImplGenTracked]
      have ⟨hRunEq, hInv⟩ :=
        bhKioSmTracked_tagImpl1KeyReal_sync initTrack smImpl P i sq σH lst hSync rc2
      rw [hRunEq]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun p hMem => ?_)
      rcases p with ⟨⟨r, σH'⟩, l1⟩
      rcases hInv r σH' l1 hMem with ⟨hSync', hl1_rc⟩
      exact ih r σH' l1 rc2 hSync' (by rw [hl1_rc, hCache])

private theorem evalDist_bhPrefixLazyFullExpWithTracked_e2e1KeyReal_eq
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhPrefixLazyFullExpWithTracked initTrack smImpl
        (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P) P C K k b_k B] =
      𝒟[bhPrefixExactFullExpWithTracked initTrack smImpl
        (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P) P C K k b_k B] := by
  let g : (Bool × (BHE2EDrvState S ℓ × List τ)) → Bool → ProbComp Bool :=
    fun ⟨b', σH⟩ clean =>
      if !clean then $ᵗ Bool
      else return (if bhE2EDrvWon σH.1 true then true
        else if bhE2EDrvWon σH.1 false then false else b')
  let oa_lazy :=
    (simulateQ (bhKioImplPrefixTracked initTrack smImpl P C K (kioKind S)
      (bhMkPrefixLazy k b_k)) B).run ({}, [])
  let oa_exact :=
    (simulateQ (bhKioImplPrefixTracked initTrack smImpl P C K (kioKind S)
      (bhMkPrefixExact k b_k)) B).run ({}, [])
  have hInit : (({} : BHE2EDrvState S ℓ), ([] : List τ)) =
      ({ ({} : BHE2EDrvState S ℓ) with st := SignalPqxdh.KeyIndState.empty S false }, []) := rfl
  have hCleanEq : allTestedSessionsFresh (S := S) P = composedClean (S := S) P := rfl
  have h1 :
      𝒟[bhPrefixLazyFullExpWithTracked initTrack smImpl
          (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P) P C K k b_k B] =
        𝒟[(simulateQ (kioFullImpl (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P)) oa_lazy).run
            (SignalPqxdh.KeyIndState.empty S false) >>= fun (a, st) => g a (composedClean P st)] := by
    unfold bhPrefixLazyFullExpWithTracked bhComposedPostObsSessionTracked bhComposedPostObs
    have hRun := simulateQ_bhE2EDrvImplPrefixWithTracked_eq_bhKioImplPrefixTracked initTrack smImpl
      (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P) P C K (bhMkPrefixLazy k b_k) B
      ({}, []) (SignalPqxdh.KeyIndState.empty S false)
    dsimp only at hRun
    rw [hRun, ← simulateQ_bhKioImplPrefixTracked_kioKind_run]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, hCleanEq]
    rfl
  have h2 := evalDist_simulateQ_pqxdhKeyIndImpl1KeyReal_false_eq_tagImpl P oa_lazy g
  have h3 :
      𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndTagImpl1KeyReal false false S P)) oa_lazy).run
          (KeyInd1KeyLazyState.empty S) >>= fun (a, lst) => g a (composedClean P lst.base)] =
        𝒟[(((simulateQ (bhKioImplPrefixTracked initTrack smImpl P C K
            (pqxdhKeyIndTagImpl1KeyReal false false S P)
            (bhMkPrefixLazy k b_k)) B).run ({}, [])).run (KeyInd1KeyLazyState.empty S)) >>=
            fun (a, lst) => g a (composedClean P lst.base)] := by
    rw [simulateQ_bhKioImplPrefixTracked_kioKind_run]
  have h4 := evalDist_bhKioImplPrefixTracked_tagImpl1KeyReal_Lazy_eq_Exact initTrack smImpl P C K
    k b_k B ({}, []) (KeyInd1KeyLazyState.empty S) (KeyInd1KeyLazyState.empty S).randCache
    (DrvTagSyncInv1KeyReal.empty P) rfl
    (fun (a, lst) => g a (composedClean P lst.base)) (fun _ _ _ => rfl)
  have h5 :
      𝒟[(((simulateQ (bhKioImplPrefixTracked initTrack smImpl P C K
          (pqxdhKeyIndTagImpl1KeyReal false false S P)
          (bhMkPrefixExact k b_k)) B).run ({}, [])).run (KeyInd1KeyLazyState.empty S)) >>=
          fun (a, lst) => g a (composedClean P lst.base)] =
        𝒟[(simulateQ (kioFullImpl (pqxdhKeyIndTagImpl1KeyReal false false S P)) oa_exact).run
            (KeyInd1KeyLazyState.empty S) >>=
              fun (a, lst) => g a (composedClean P lst.base)] := by
    rw [simulateQ_bhKioImplPrefixTracked_kioKind_run]
  have h6 := (evalDist_simulateQ_pqxdhKeyIndImpl1KeyReal_false_eq_tagImpl P oa_exact g).symm
  have h7 :
      𝒟[(simulateQ (kioFullImpl (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P)) oa_exact).run
          (SignalPqxdh.KeyIndState.empty S false) >>= fun (a, st) => g a (composedClean P st)] =
        𝒟[bhPrefixExactFullExpWithTracked initTrack smImpl
          (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P) P C K k b_k B] := by
    unfold bhPrefixExactFullExpWithTracked bhComposedPostObsSessionTracked bhComposedPostObs
    have hRun := simulateQ_bhE2EDrvImplPrefixWithTracked_eq_bhKioImplPrefixTracked initTrack smImpl
      (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S P) P C K (bhMkPrefixExact k b_k) B
      ({}, []) (SignalPqxdh.KeyIndState.empty S false)
    dsimp only at hRun
    rw [hRun, ← simulateQ_bhKioImplPrefixTracked_kioKind_run]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, hCleanEq]
    rfl
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

private def bhNormSigPkGen (P : SignalPqxdh.Primitives) : SignalPqxdh.Primitives :=
  { P with sigPkGen := P.x25519Base }

private theorem signalPqxdh_pqxdhKeyIndImpl1KeyReal_normSigPkGen
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives) :
    SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P =
      CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S (bhNormSigPkGen P) := by
  have h1 : SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P =
      SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (bhNormSigPkGen P) := by
    funext q; cases q <;> rfl
  exact h1.trans (signalPqxdh_pqxdhKeyIndImpl1KeyReal_eq S (bhNormSigPkGen P) rfl)

private theorem bhE2EDrvImplPrefixWithTracked_normSigPkGen
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (mkP : BHDrvPrefixKeyBitGen) :
    bhE2EDrvImplPrefixWithTracked initTrack smImpl ki P C K mkP =
      bhE2EDrvImplPrefixWithTracked initTrack smImpl ki (bhNormSigPkGen P) C K mkP := by
  have hOk : bhDrvKiQueryOk (S := S) P = bhDrvKiQueryOk (S := S) (bhNormSigPkGen P) := by
    funext base kq; cases kq <;> rfl
  funext q; unfold bhE2EDrvImplPrefixWithTracked bhE2EDrvImplGenWithTracked; simp only [hOk]

/-- Unconditional lazy-vs-exact prefix equivalence at `SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P`
for arbitrary per-session tracked `(τ, initTrack, smImpl)`. -/
theorem evalDist_bhPrefixLazyFullExpWithTracked_1KeyReal_eq_bhPrefixExactFullExpWithTracked
    (initTrack : SampledSessionKey → τ)
    (smImpl : BHModelInst S ℓ →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhPrefixLazyFullExpWithTracked initTrack smImpl
        (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K k b_k B] =
      𝒟[bhPrefixExactFullExpWithTracked initTrack smImpl
        (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K k b_k B] := by
  have hObs : bhComposedPostObsSessionTracked (τ := τ) (S := S) (ℓ := ℓ) P =
      bhComposedPostObsSessionTracked (bhNormSigPkGen P) := rfl
  have hL :
      bhPrefixLazyFullExpWithTracked initTrack smImpl
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K k b_k B =
        bhPrefixLazyFullExpWithTracked initTrack smImpl
          (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S (bhNormSigPkGen P))
          (bhNormSigPkGen P) C K k b_k B := by
    unfold bhPrefixLazyFullExpWithTracked
    rw [signalPqxdh_pqxdhKeyIndImpl1KeyReal_normSigPkGen,
      bhE2EDrvImplPrefixWithTracked_normSigPkGen, hObs]
  have hR :
      bhPrefixExactFullExpWithTracked initTrack smImpl
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K k b_k B =
        bhPrefixExactFullExpWithTracked initTrack smImpl
          (CryptoVerification.E2E.pqxdhKeyIndImpl1KeyReal S (bhNormSigPkGen P))
          (bhNormSigPkGen P) C K k b_k B := by
    unfold bhPrefixExactFullExpWithTracked
    rw [signalPqxdh_pqxdhKeyIndImpl1KeyReal_normSigPkGen,
      bhE2EDrvImplPrefixWithTracked_normSigPkGen, hObs]
  rw [hL, hR]
  exact evalDist_bhPrefixLazyFullExpWithTracked_e2e1KeyReal_eq initTrack smImpl
    (bhNormSigPkGen P) C K k b_k B

end TrackedPrefixLazy1Key

private theorem bhE2EStepLocalSmSessionTracked_eq_tracked
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i q =
      bhE2EStepLocalSmTracked T.init
        (fun d => oracleImplRSessionTracked T
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
            d.idA d.idB) ℓ d.spkCoins)
          (2 + 1) qep (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ)
            decT encT))
        σH i q := by
  unfold bhE2EStepLocalSmSessionTracked bhE2EStepLocalSmTracked
  rcases σH with ⟨σ, tracks⟩; dsimp only
  split_ifs with hClean; · rfl
  cases σ.insts[i]? <;> cases σ.instMeta[i]? <;> rfl

private theorem bhE2EDrvImplPrefixWithSessionTracked_eq_tracked
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (mkP : BHDrvPrefixKeyBitGen) :
    bhE2EDrvImplPrefixWithSessionTracked T ki P C K qep decT encT mkP =
      bhE2EDrvImplPrefixWithTracked T.init
        (fun d => oracleImplRSessionTracked T
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
            d.idA d.idB) ℓ d.spkCoins)
          (2 + 1) qep (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ)
            decT encT))
        ki P C K mkP := by
  funext q; ext σH
  dsimp only [bhE2EDrvImplPrefixWithSessionTracked, bhE2EDrvImplPrefixWithTracked]
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · rfl
  · cases kq <;> rfl
  · rfl
  · dsimp only [bhE2EDrvImplGenWithSessionTracked, bhE2EDrvImplGenWithTracked]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, bhE2EStepLocalSmSessionTracked_eq_tracked]

/-- Unconditional lazy-vs-exact prefix equivalence directly on
`MainHaltedPrefixCore.bhPrefixLazyFullExpWithSessionTracked` and
`MainHaltedPrefixCore.bhPrefixExactFullExpWithSessionTracked`. -/
theorem evalDist_bhPrefixLazyFullExpWithSessionTracked_1KeyReal_eq_bhPrefixExactFullExpWithSessionTracked
    {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhPrefixLazyFullExpWithSessionTracked T S
        (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K qep decT encT k b_k B] =
      𝒟[bhPrefixExactFullExpWithSessionTracked T S
        (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K qep decT encT k b_k B] := by
  simp only [bhPrefixLazyFullExpWithSessionTracked, bhPrefixExactFullExpWithSessionTracked,
    bhE2EDrvImplPrefixWithSessionTracked_eq_tracked]
  exact evalDist_bhPrefixLazyFullExpWithTracked_1KeyReal_eq_bhPrefixExactFullExpWithTracked T.init
    (fun d => oracleImplRSessionTracked T (sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins)
      (2 + 1) qep (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT))
    P C K k b_k B

/-- Unconditional lazy-vs-exact prefix equivalence at `coinLogSessionTracker badLog`. -/
theorem evalDist_bhPrefixLazyFullExpWithHalted_1KeyReal_eq_bhPrefixExactFullExpWithHalted
    {ℓ : ℕ} (badLog : List (BitVec 512) → Bool) (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (k : ℕ) (b_k : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhPrefixLazyFullExpWithSessionTracked (coinLogSessionTracker badLog) S
        (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K qep decT encT k b_k B] =
      𝒟[bhPrefixExactFullExpWithSessionTracked (coinLogSessionTracker badLog) S
        (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) P C K qep decT encT k b_k B] :=
  evalDist_bhPrefixLazyFullExpWithSessionTracked_1KeyReal_eq_bhPrefixExactFullExpWithSessionTracked
    (coinLogSessionTracker badLog) S P C K qep decT encT k b_k B

end Computational.Proofs.LibsignalCli.MainHaltedLazy1Key

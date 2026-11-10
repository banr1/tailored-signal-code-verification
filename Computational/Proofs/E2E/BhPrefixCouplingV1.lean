/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.BhKindCouplingV1
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers
public import Computational.Proofs.SpecLemmas.Composition.ModelLazyCond
public import Computational.Proofs.E2E.ComposedPrefixHelpers
public import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.GameHop.GlobalHybrid
import Computational.Proofs.E2E.ComposedPrefixTagSync
import Computational.Proofs.ReductionDsl.Bridge
import VCVio.EvalDist.Monad.Basic

/-!
# Prefix-hybrid driver and `bhPrefixRed` factorization for the binary harness

**Checked by Lean.**

Defines the parameterized prefix driver (`bhE2EDrvImplGen`, `bhE2EDrvImplPrefix`), the `kio`-factored
driver (`bhKioImplGen`, `bhKioImplPrefix`) for lazy `DRKey` replacement, and the `bhPlugExt`
Stage-1/Stage-2 coupling invariants (`BHPrefixPlugInv`, `BHMidEval1Props`) for `bhPrefixRed`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Prefix CryptoVerification.E2E.Signed
  ReductionDsl
open Proofs.SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security Proofs.SignalPqxdh.Security

namespace CryptoVerification.E2E

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}

@[simp]
private theorem stateT_run_lift {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem stateT_run_liftM {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

/-! ## Parameterized model-state prefix driver -/

section PrefixDriver

def bhFinishStartSpkKB {S : SignalPqxdh.Setup} {ℓ : ℕ} (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (hdr : SignalPqxdh.HandshakeHdr) (bnd : SignalPqxdh.PreKeyBundleInput)
    (uj : Fin S.N_id × Fin S.N_recv)
    (spkSk : SignalPqxdh.Bytes) (kb : SampledSessionKey × Bool) :
    Option ℕ × BHE2EDrvState S ℓ :=
  if spkSk.length == 32 then
    let idA := bhIdKeyOf hdr.ikAPk; let idB := bhIdKeyOf bnd.ikB
    let spkCoins := bhBytesWord spkSk
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr idA idB) ℓ spkCoins
    let gs := some (SM.initState sch.sendPart kb.1 kb.2)
    let inst : BHModelInst S ℓ := { sid, hdr, idA, idB, spkCoins, gs }
    let im : ModelDriverInstanceMeta S :=
      { respPrin := some uj.1, respSpkIdx := some uj.2, instOpkId? := hdr.opkId? }
    (some σ.insts.length,
     { σ with insts := σ.insts ++ [inst], instMeta := σ.instMeta ++ [im] })
  else (none, σ)

theorem bhFinishStartSpkGen_drKey_eq_KB {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (σ : BHE2EDrvState S ℓ)
    (sid : SignalPqxdh.SessionId S)
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u : Fin S.N_id} {j : Fin S.N_recv}
    (hG : bhE2EGuard σ sid = some (hdr, bnd, (u, j)))
    {dk : SignalPqxdh.DRKey} (hdk : dk ∈ support SignalPqxdh.sampleDRKey96)
    (spkSk : SignalPqxdh.Bytes) (kb : SampledSessionKey × Bool) :
    bhFinishStartSpkGen C K σ sid (.drKeyResp dk) (.spkSkResp spkSk) kb =
      bhFinishStartSpkKB C K σ sid hdr bnd (u, j) spkSk kb := by
  rcases lengths_of_mem_support_sampleDRKey96 hdk with ⟨hrk, hck, hpqr⟩
  unfold bhFinishStartSpkGen bhFinishStartSpkKB
  simp [hG, hrk, hck, hpqr]

def bhMkKeyBitConst (b : Bool) : ModelDriverKeyBitGen := fun kr1 _ => do
  let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
  let dk := match kr1 with | .drKeyResp dk => dk | _ => default
  return (bhKeySOf dk ac, b)

def bhMkPrefixHyb (k : ℕ) : BHDrvPrefixKeyBitGen :=
  fun len kr1 _ => do
    let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    let dk := match kr1 with | .drKeyResp dk => dk | _ => default
    return (bhKeySOf dk ac, decide (len < k))

theorem bhMkPrefixExact_true_eq_bhMkPrefixHyb_succ (k : ℕ) :
    bhMkPrefixExact k true = bhMkPrefixHyb (k + 1) := by
  funext len kr1 kr2
  unfold bhMkPrefixExact bhMkPrefixHyb
  have h : (if len == k then true else decide (len < k)) = decide (len < k + 1) := by
    by_cases h1 : len = k <;> (simp [h1]; try omega)
  rw [h]; rfl

theorem bhMkPrefixExact_false_eq_bhMkPrefixHyb (k : ℕ) :
    bhMkPrefixExact k false = bhMkPrefixHyb k := by
  funext len kr1 kr2
  unfold bhMkPrefixExact bhMkPrefixHyb
  have h : (if len == k then false else decide (len < k)) = decide (len < k) := by
    by_cases h1 : len = k <;> simp [h1]
  rw [h]; rfl

theorem bhFinishStartSpkGen_bhMkKeyBitConst_eq (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (b : Bool) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse) :
    (bhMkKeyBitConst b kr1 kr2 >>= fun kb => pure (bhFinishStartSpkGen C K σ sid kr1 kr2 kb)) =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun ac =>
        pure (bhE2EFinishStartSpk C K (some b) σ sid kr1 kr2 ac)) := by
  unfold bhMkKeyBitConst bhFinishStartSpkGen bhE2EFinishStartSpk
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun ac => ?_
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    cases kr1 <;> cases kr2 <;> rfl

end PrefixDriver

/-! ## Endpoint bit invariants -/

section PrefixEndpoints

def BHAllInstsBit {S : SignalPqxdh.Setup} {ℓ : ℕ} (b : Bool) (σ : BHE2EDrvState S ℓ) : Prop :=
  ∀ d ∈ σ.insts, ∀ gs, d.gs = some gs → gs.b = b

theorem bhAllInstsBit_empty {S : SignalPqxdh.Setup} {ℓ : ℕ} (b : Bool) :
    BHAllInstsBit b ({} : BHE2EDrvState S ℓ) := by
  rintro _ ⟨⟩

theorem bhE2EDrvWon_not_of_allInstsBit {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {b : Bool} {σ : BHE2EDrvState S ℓ} (h : BHAllInstsBit b σ) :
    bhE2EDrvWon σ (!b) = false := by
  unfold bhE2EDrvWon
  rw [List.any_eq_false]
  intro d hd
  cases hgs : d.gs with
  | none => simp
  | some gs =>
    have hb : gs.b = b := h d hd gs hgs
    cases b <;> simp [hb]

set_option maxHeartbeats 800000 in
theorem bhE2EStepLocalSm_preserves_allInstsBit
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : Bool) (σ : BHE2EDrvState S ℓ) (hσ : BHAllInstsBit b σ)
    (i : ℕ) (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {p : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hp : p ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    BHAllInstsBit b p.2 := by
  unfold bhE2EStepLocalSm at hp
  by_cases hClean : (!bhE2EDrvInstClean σ i) = true
  · simp only [hClean, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact hσ
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte] at hp
    cases hi : σ.insts[i]? with
    | none =>
      rw [hi] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hσ
    | some d =>
      rw [hi] at hp
      cases him : σ.instMeta[i]? with
      | none =>
        rw [him] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact hσ
      | some im =>
        rw [him] at hp; dsimp only at hp
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp only [hCorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
          subst hp; exact hσ
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hp
          cases hd : d.gs with
          | none =>
            rw [hd] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
            subst hp; exact hσ
          | some gs =>
            rw [hd] at hp; dsimp only at hp
            have hRunStd : ∀ q',
                p ∈ support (do
                  let (r, gs') ← (SM.oracleImplR
                    (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                      ℓ d.spkCoins)
                    (2 + 1) qep
                    (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT) q').run gs
                  let accepted := bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  return (bhPackSmResp q' r,
                    { σ with insts := σ.insts.set i { d with gs := some gs' },
                             instMeta := σ.instMeta.set i im' })) →
                BHAllInstsBit b p.2 := by
              intro q' hq'
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hq'
              rcases hq' with ⟨⟨r, gs'⟩, hsm, rfl⟩
              have hgs_b : gs.b = b := hσ d (List.mem_of_getElem? hi) gs hd
              have hgs'_b : gs'.b = b :=
                (oracleImplR_preserves_b _ _ _ _ q' gs hsm).trans hgs_b
              intro d' hd' gs_d' hgs_d'
              rcases List.mem_or_eq_of_mem_set hd' with hd'_old | rfl
              · exact hσ d' hd'_old gs_d' hgs_d'
              · simp only [Option.some.injEq] at hgs_d'
                subst hgs_d'
                exact hgs'_b
            rcases sq with (((q1 | q2) | ⟨pt, c⟩) | ⟨pt, c⟩) | q5
            · exact hRunStd _ hp
            · exact hRunStd _ hp
            · cases pt with
              | A =>
                dsimp only at hp
                split_ifs at hp
                · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hσ
                · exact hRunStd _ hp
              | B =>
                dsimp only at hp
                split_ifs at hp with hAcc
                · cases hdec : bhDecodePreKeyMsgE c with
                  | none =>
                    rw [hdec] at hp
                    simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hσ
                  | some m =>
                    rw [hdec] at hp; dsimp only at hp
                    split_ifs at hp
                    · exact hRunStd _ hp
                    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hσ
                · cases hdec : bhDecodePreKeyMsgE c with
                  | none =>
                    rw [hdec] at hp; exact hRunStd _ hp
                  | some m =>
                    rw [hdec] at hp; dsimp only at hp
                    split_ifs at hp
                    · exact hRunStd _ hp
                    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hσ
            · cases pt with
              | A =>
                dsimp only at hp
                split_ifs at hp
                · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hσ
                · exact hRunStd _ hp
              | B =>
                dsimp only at hp
                split_ifs at hp with hAcc
                · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hσ
                · cases hdec : bhDecodePreKeyMsgE c with
                  | none =>
                    rw [hdec] at hp; exact hRunStd _ hp
                  | some m =>
                    rw [hdec] at hp; dsimp only at hp
                    split_ifs at hp
                    · exact hRunStd _ hp
                    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact hσ
            · exact hRunStd _ hp

set_option maxHeartbeats 800000 in
theorem bhE2EStepLocalSm_with_b (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (b' : Bool) (i : ℕ)
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSm C K qep decT encT { σ with b := b' } i q =
      (fun p => (p.1, { p.2 with b := b' })) <$>
        bhE2EStepLocalSm C K qep decT encT σ i q := by
  unfold bhE2EStepLocalSm
  have hCleanEq : bhE2EDrvInstClean { σ with b := b' } i = bhE2EDrvInstClean σ i := rfl
  rw [hCleanEq]
  by_cases hClean : (!bhE2EDrvInstClean σ i) = true
  · simp [hClean]
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte]
    cases hi : σ.insts[i]? with
    | none =>
      have hi' : ({ σ with b := b' } : BHE2EDrvState S ℓ).insts[i]? = none := hi
      simp [hi']
    | some d =>
      have hi' : ({ σ with b := b' } : BHE2EDrvState S ℓ).insts[i]? = some d := hi
      cases him : σ.instMeta[i]? with
      | none =>
        have him' : ({ σ with b := b' } : BHE2EDrvState S ℓ).instMeta[i]? = none := him
        simp [hi', him']
      | some im =>
        have him' : ({ σ with b := b' } : BHE2EDrvState S ℓ).instMeta[i]? = some im := him
        have hCorrEq : bhE2EInstIkACorr { σ with b := b' } d = bhE2EInstIkACorr σ d := rfl
        simp only [hi', him', hCorrEq]
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d) = true
        · simp [hCorr]
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
          cases hd : d.gs with
          | none => simp
          | some gs =>
            dsimp only
            have hRunStd : ∀ q',
                (do
                  let (r, gs') ← (SM.oracleImplR
                    (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                      ℓ d.spkCoins)
                    (2 + 1) qep
                    (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT) q').run gs
                  let accepted := bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  return (bhPackSmResp q' r,
                    { σ with b := b',
                             insts := σ.insts.set i { d with gs := some gs' },
                             instMeta := σ.instMeta.set i im' })) =
                (fun p => (p.1, { p.2 with b := b' })) <$>
                  (do
                    let (r, gs') ← (SM.oracleImplR
                      (sessionSchemeFixedSpk
                        (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                        ℓ d.spkCoins)
                      (2 + 1) qep
                      (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT) q').run gs
                    let accepted := bhIsBobAcceptSMResp q' r
                    let im' := if !im.bobAccepted && accepted then
                        { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                      else im
                    return (bhPackSmResp q' r,
                      { σ with insts := σ.insts.set i { d with gs := some gs' },
                               instMeta := σ.instMeta.set i im' })) := by
              intro q'
              simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
            rcases q with (((q1 | q2) | ⟨p, c⟩) | ⟨p, c⟩) | q5
            · exact hRunStd _
            · exact hRunStd _
            · cases p with
              | A =>
                dsimp only
                split_ifs
                · simp
                · exact hRunStd _
              | B =>
                dsimp only
                split_ifs with hAcc
                · cases bhDecodePreKeyMsgE c with
                  | none => simp
                  | some m =>
                    dsimp only
                    split_ifs
                    · exact hRunStd _
                    · simp
                · cases bhDecodePreKeyMsgE c with
                  | none => exact hRunStd _
                  | some m =>
                    dsimp only
                    split_ifs
                    · exact hRunStd _
                    · simp
            · cases p with
              | A =>
                dsimp only
                split_ifs
                · simp
                · exact hRunStd _
              | B =>
                dsimp only
                split_ifs with hAcc
                · simp
                · cases bhDecodePreKeyMsgE c with
                  | none => exact hRunStd _
                  | some m =>
                    dsimp only
                    split_ifs
                    · exact hRunStd _
                    · simp
            · exact hRunStd _

end PrefixEndpoints

/-! ## Lazy `DRKey` replacement -/

section PrefixLazy

def bhToDrvInst (d : BHModelInst S ℓ) : DrvInst S ℓ :=
  { sid := d.sid, hdr := d.hdr, idA := d.idA, idB := d.idB, spkCoins := d.spkCoins, gs := d.gs }

def bhToDrvState (σ : BHE2EDrvState S ℓ) : DrvState S ℓ :=
  { insts := σ.insts.map bhToDrvInst
    prins := σ.prins
    bundles := σ.bundles.map (fun (idx, (spkB, _)) => (idx, spkB))
    sends := σ.sends }

@[simp]
theorem bhToDrvState_empty : bhToDrvState ({} : BHE2EDrvState S ℓ) = {} := rfl

theorem bhToDrvState_bhE2EMirror (σ : BHE2EDrvState S ℓ)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) :
    bhToDrvState (bhE2EMirror σ q r) = drvMirror (bhToDrvState σ) q r := by
  cases q <;> cases r <;> rfl

theorem drvMirror_revealSpkSk (ds : DrvState S ℓ) (u : Fin S.N_id) (j' : Fin S.N_recv)
    (r : SignalPqxdh.KeyIndResponse) :
    drvMirror ds (.revealSpkSk u j') r = ds := by
  cases r <;> rfl

theorem bhDrvKiQueryOk_ne_testSession (P : SignalPqxdh.Primitives) (base : ModelDriverBase S)
    (kq : SignalPqxdh.KeyIndQuery S) (hOk : bhDrvKiQueryOk P base kq = true) :
    ∀ sid, kq ≠ .testSession sid := by
  intro sid h
  subst h
  simp [bhDrvKiQueryOk] at hOk

abbrev BHKioDrvM (S : SignalPqxdh.Setup) (ℓ : ℕ) (M : Type → Type) :=
  StateT (BHE2EDrvState S ℓ) M

@[simp]
private theorem bhKioDrvM_run_liftM {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    {α : Type} (mx : ProbComp α) (σ : BHE2EDrvState S ℓ) :
    (liftM mx : BHKioDrvM S ℓ M α).run σ = ((liftM mx : M α) >>= fun x => pure (x, σ)) := rfl

def bhKioKeyInd {M : Type → Type} [Monad M]
    (P : SignalPqxdh.Primitives)
    (kio : (q : SignalPqxdh.KeyIndQuery S) → M SignalPqxdh.KeyIndResponse)
    (kq : SignalPqxdh.KeyIndQuery S) :
    BHKioDrvM S ℓ M SignalPqxdh.KeyIndResponse := do
  let σ ← get
  if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
    return .noneResp
  else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
    return .noneResp
  else
    let kr ← StateT.lift (kio kq)
    modify fun σ => bhE2EMirror σ kq kr
    return kr

def bhKioStartGen {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (kio : (q : SignalPqxdh.KeyIndQuery S) → M SignalPqxdh.KeyIndResponse)
    (mkKB : ModelDriverKeyBitGen)
    (sid : SignalPqxdh.SessionId S) :
    BHKioDrvM S ℓ M (Option ℕ) := do
  let σ ← get
  match bhE2EGuard σ sid with
  | none => return none
  | some (_, _, (u, j)) =>
    let kr1 ← StateT.lift (kio (.testSession sid))
    let kr2 ← StateT.lift (kio (.revealSpkSk u j))
    let kb ← liftM (mkKB kr1 kr2)
    let (idx?, σ') := bhFinishStartSpkGen C K σ sid kr1 kr2 kb
    set σ'
    return idx?

def bhKioSm {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    BHKioDrvM S ℓ M ((SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) := do
  let σ ← get
  let (sr, σ') ← liftM (bhE2EStepLocalSm C K qep decT encT σ i sq)
  set σ'
  return bhUnpackSmResp sq sr

def bhKioImplGen {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (kio : (q : SignalPqxdh.KeyIndQuery S) → M SignalPqxdh.KeyIndResponse)
    (mkKB : ModelDriverKeyBitGen) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (BHKioDrvM S ℓ M) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => bhKioKeyInd P kio kq
  | .inr (.inl (.inr (.startDR sid))) => bhKioStartGen C K kio mkKB sid
  | .inr (.inr ⟨i, sq⟩) => bhKioSm C K qep decT encT i sq

def bhKioImplPrefix {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (kio : (q : SignalPqxdh.KeyIndQuery S) → M SignalPqxdh.KeyIndResponse)
    (mkP : BHDrvPrefixKeyBitGen) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (BHKioDrvM S ℓ M) := fun q =>
  StateT.mk fun σ =>
    (bhKioImplGen P C K qep decT encT kio (mkP σ.insts.length) q).run σ

@[simp]
theorem bhKioImplPrefix_run_eq_gen {M : Type → Type} [Monad M] [MonadLiftT ProbComp M]
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (kio : (q : SignalPqxdh.KeyIndQuery S) → M SignalPqxdh.KeyIndResponse)
    (mkP : BHDrvPrefixKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ) :
    (bhKioImplPrefix P C K qep decT encT kio mkP q).run σ =
      (bhKioImplGen P C K qep decT encT kio (mkP σ.insts.length) q).run σ := rfl

private theorem simulateQ_bhKioImplGen_kioKind_step {St : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (kioImpl : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT St ProbComp))
    (mkKB : ModelDriverKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ) (st : St) :
    (simulateQ (kioFullImpl kioImpl)
      ((bhKioImplGen P C K qep decT encT (kioKind S) mkKB q).run σ)).run st =
    ((bhKioImplGen P C K qep decT encT kioImpl mkKB q).run σ).run st := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · dsimp only [bhKioImplGen]
    simp only [bhKioDrvM_run_liftM, stateT_run_liftM, simulateQ_bind, StateT.run_bind,
      simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    rw [simulateQ_kioFullImpl_liftM_run kioImpl (query (spec := unifSpec) n) st]
    rfl
  · dsimp only [bhKioImplGen, bhKioKeyInd]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hOk : (!bhDrvKiQueryOk P σ.toModelDriverBase kq) = true
    · simp only [hOk, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    · simp only [hOk, Bool.false_eq_true, ↓reduceIte]
      cases kq <;> dsimp only <;> split_ifs <;>
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
          stateT_run_lift, StateT.run_modify, bind_assoc, pure_bind, simulateQ_bind,
          simulateQ_kioFullImpl_kioKind, simulateQ_pure]
  · dsimp only [bhKioImplGen, bhKioStartGen]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bhE2EGuard σ sid with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      simp only [stateT_run_lift, bhKioDrvM_run_liftM, stateT_run_liftM, StateT.run_bind,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, simulateQ_bind,
        simulateQ_kioFullImpl_kioKind, simulateQ_pure]
      refine bind_congr fun ⟨kr1, st1⟩ => bind_congr fun ⟨kr2, st2⟩ => ?_
      rw [simulateQ_kioFullImpl_liftM_run kioImpl (mkKB kr1 kr2) st2]
      simp only [stateT_run_lift, bind_assoc, pure_bind]
  · dsimp only [bhKioImplGen, bhKioSm]
    simp only [StateT.run_bind, StateT.run_get, bhKioDrvM_run_liftM, stateT_run_liftM,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure]
    rw [simulateQ_kioFullImpl_liftM_run kioImpl (bhE2EStepLocalSm C K qep decT encT σ i sq) st]
    simp only [stateT_run_lift, bind_assoc, pure_bind]

theorem simulateQ_bhKioImplPrefix_kioKind_run {α St : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (kioImpl : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT St ProbComp))
    (mkP : BHDrvPrefixKeyBitGen)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) (st : St) :
    (simulateQ (kioFullImpl kioImpl)
      ((simulateQ (bhKioImplPrefix P C K qep decT encT (kioKind S) mkP) oa).run σ)).run st =
    (((simulateQ (bhKioImplPrefix P C K qep decT encT kioImpl mkP) oa).run σ).run st) := by
  induction oa using OracleComp.inductionOn generalizing σ st with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    simp only [simulateQ_bind, StateT.run_bind, bhKioImplPrefix_run_eq_gen,
      simulateQ_bhKioImplGen_kioKind_step]
    exact bind_congr fun p => ih p.1.1 p.1.2 p.2

def bhFinishStartSpkSucc {S : SignalPqxdh.Setup} {ℓ : ℕ} (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (hdr : SignalPqxdh.HandshakeHdr) (bnd : SignalPqxdh.PreKeyBundleInput)
    (uj : Fin S.N_id × Fin S.N_recv)
    (spkSk : SignalPqxdh.Bytes) (kb : SampledSessionKey × Bool) :
    Option ℕ × BHE2EDrvState S ℓ :=
  let idA := bhIdKeyOf hdr.ikAPk; let idB := bhIdKeyOf bnd.ikB
  let spkCoins := bhBytesWord spkSk
  let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
  let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr idA idB) ℓ spkCoins
  let gs := some (SM.initState sch.sendPart kb.1 kb.2)
  let inst : BHModelInst S ℓ := { sid, hdr, idA, idB, spkCoins, gs }
  let im : ModelDriverInstanceMeta S :=
    { respPrin := some uj.1, respSpkIdx := some uj.2, instOpkId? := hdr.opkId? }
  (some σ.insts.length,
   { σ with insts := σ.insts ++ [inst], instMeta := σ.instMeta ++ [im] })

theorem bhFinishStartSpkGen_eq_succ
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (σ : BHE2EDrvState S ℓ)
    (sid : SignalPqxdh.SessionId S)
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u : Fin S.N_id} {j' : Fin S.N_recv}
    (hG : bhE2EGuard σ sid = some (hdr, bnd, (u, j')))
    {dk : SignalPqxdh.DRKey} (hdk : dk ∈ support SignalPqxdh.sampleDRKey96)
    {spkSk : SignalPqxdh.Bytes} (hspk : spkSk.length = 32) (kb : SampledSessionKey × Bool) :
    bhFinishStartSpkGen C K σ sid (.drKeyResp dk) (.spkSkResp spkSk) kb =
      bhFinishStartSpkSucc C K σ sid hdr bnd (u, j') spkSk kb := by
  rw [bhFinishStartSpkGen_drKey_eq_KB C K σ sid hG hdk spkSk kb]
  unfold bhFinishStartSpkKB bhFinishStartSpkSucc
  simp [hspk]

end PrefixLazy

/-! ## `bhPlugExt` and Stage-1 factorization -/

section PrefixFactorization

@[simp]
theorem bhUnpackSmResp_bhPackSmResp {ℓ : ℕ} {PQC : Type}
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Domain)
    (r : (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Range q) :
    bhUnpackSmResp q (bhPackSmResp q r) = r := by
  rcases q with (((_ | _) | _) | _) | _ <;> rfl

def bhPlugExtInst {S : SignalPqxdh.Setup} {ℓ : ℕ} (gs_ext : ExtState ℓ)
    (d : BHModelInst S ℓ) : BHModelInst S ℓ :=
  match d.gs with | some _ => d | none => { d with gs := some gs_ext }

def bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ} (gs_ext : ExtState ℓ)
    (σ : BHE2EDrvState S ℓ) : BHE2EDrvState S ℓ :=
  { σ with insts := σ.insts.map (bhPlugExtInst gs_ext) }

@[simp] theorem bhPlugExtInst_sid {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (d : BHModelInst S ℓ) :
    (bhPlugExtInst gs_ext d).sid = d.sid := by unfold bhPlugExtInst; cases d.gs <;> rfl

@[simp] theorem bhPlugExtInst_hdr {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (d : BHModelInst S ℓ) :
    (bhPlugExtInst gs_ext d).hdr = d.hdr := by unfold bhPlugExtInst; cases d.gs <;> rfl

@[simp] theorem bhPlugExtInst_of_some {S : SignalPqxdh.Setup} {ℓ : ℕ} (gs_ext : ExtState ℓ)
    (d : BHModelInst S ℓ) (gs : ExtState ℓ) (h : d.gs = some gs) :
    bhPlugExtInst gs_ext d = d := by simp [bhPlugExtInst, h]

@[simp] theorem bhPlugExtInst_of_none {S : SignalPqxdh.Setup} {ℓ : ℕ} (gs_ext : ExtState ℓ)
    (d : BHModelInst S ℓ) (h : d.gs = none) :
    bhPlugExtInst gs_ext d = { d with gs := some gs_ext } := by simp [bhPlugExtInst, h]

@[simp] theorem getElem?_insts_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (i : ℕ) :
    (bhPlugExt gs_ext σ).insts[i]? = (σ.insts[i]?).map (bhPlugExtInst gs_ext) := by
  simp [bhPlugExt]

@[simp] theorem bhE2EGuard_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    bhE2EGuard (bhPlugExt gs_ext σ) sid = bhE2EGuard σ sid := by
  simp [bhE2EGuard, bhPlugExt, List.any_map, Function.comp_def]

@[simp] theorem bhE2EMirror_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) :
    bhE2EMirror (bhPlugExt gs_ext σ) q r = bhPlugExt gs_ext (bhE2EMirror σ q r) := by
  cases q <;> cases r <;> rfl

@[simp] theorem bhE2EDrvInstClean_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (i : ℕ) :
    bhE2EDrvInstClean (bhPlugExt gs_ext σ) i = bhE2EDrvInstClean σ i := by
  unfold bhE2EDrvInstClean
  rw [getElem?_insts_bhPlugExt]
  have hm : (bhPlugExt gs_ext σ).instMeta[i]? = σ.instMeta[i]? := rfl
  have hr : (bhPlugExt gs_ext σ).revealedSpks = σ.revealedSpks := rfl
  rw [hm, hr]
  cases σ.insts[i]? <;> cases σ.instMeta[i]? <;> simp

@[simp] theorem bhE2EInstIkACorr_bhPlugExtInst {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (d : BHModelInst S ℓ) :
    bhE2EInstIkACorr σ (bhPlugExtInst gs_ext d) = bhE2EInstIkACorr σ d := by
  unfold bhE2EInstIkACorr; simp

@[simp] theorem bhE2EInstIkACorr_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (d : BHModelInst S ℓ) :
    bhE2EInstIkACorr (bhPlugExt gs_ext σ) d = bhE2EInstIkACorr σ d := rfl

private theorem list_any_or_and_const' {α : Type} (l : List α) (f g : α → Bool) (c : Bool) :
    l.any (fun x => f x || (g x && c)) = (l.any f || (l.any g && c)) := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.any_cons, ih]
    cases f a <;> cases g a <;> cases c <;> cases tl.any f <;> cases tl.any g <;> rfl

theorem bhE2EDrvWon_bhPlugExt {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (gs_ext : ExtState ℓ) (σ : BHE2EDrvState S ℓ) (b : Bool) :
    bhE2EDrvWon (bhPlugExt gs_ext σ) b =
      (bhE2EDrvWon σ b || (σ.insts.any (fun d => d.gs.isNone) && (gs_ext.b == b && gs_ext.win))) := by
  unfold bhE2EDrvWon bhPlugExt; rw [List.any_map]
  have hpoint : ((fun d : BHModelInst S ℓ =>
      match d.gs with | some gs => gs.b == b && gs.win | none => false) ∘ bhPlugExtInst gs_ext) =
      (fun d : BHModelInst S ℓ =>
        (match d.gs with | some gs => gs.b == b && gs.win | none => false) ||
          (d.gs.isNone && (gs_ext.b == b && gs_ext.win))) := by
    funext d; cases hgs : d.gs <;> simp [bhPlugExtInst, hgs]
  exact (congr_arg σ.insts.any hpoint).trans (list_any_or_and_const' σ.insts _ _ _)

def BHAllInstsSome {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : BHE2EDrvState S ℓ) : Prop :=
  ∀ d ∈ σ.insts, d.gs ≠ none

theorem bhAllInstsSome_empty {S : SignalPqxdh.Setup} {ℓ : ℕ} :
    BHAllInstsSome ({} : BHE2EDrvState S ℓ) := by
  rintro _ ⟨⟩

def BHOnlyInstKNone {S : SignalPqxdh.Setup} {ℓ : ℕ} (k : ℕ) (σ : BHE2EDrvState S ℓ) : Prop :=
  ∀ i d, σ.insts[i]? = some d → d.gs = none → i = k

theorem bhOnlyInstKNone_of_allInstsSome_mapIdx {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (σ : BHE2EDrvState S ℓ) (h : BHAllInstsSome σ) :
    BHOnlyInstKNone k
      { σ with insts := σ.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d) } := by
  intro i d' hi hnone
  rw [List.getElem?_mapIdx] at hi
  rcases Option.map_eq_some_iff.mp hi with ⟨d, hd, rfl⟩
  by_cases hik : i = k
  · exact hik
  · simp only [hik, ↓reduceIte] at hnone
    exact False.elim (h d (List.mem_of_getElem? hd) hnone)

theorem bhOnlyInstKNone_append_some {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ} (h : BHOnlyInstKNone k σ)
    (d₀ : BHModelInst S ℓ) (im₀ : ModelDriverInstanceMeta S) (st' : SignalPqxdh.KeyIndState S)
    (hd₀ : d₀.gs ≠ none) :
    BHOnlyInstKNone k { σ with st := st', insts := σ.insts ++ [d₀], instMeta := σ.instMeta ++ [im₀] } := by
  intro i d hi hnone
  by_cases hlt : i < σ.insts.length
  · rw [List.getElem?_append_left hlt] at hi
    exact h i d hi hnone
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
    have hik : i - σ.insts.length = 0 := by
      by_contra hne
      have hge : 1 ≤ i - σ.insts.length := Nat.pos_of_ne_zero hne
      rw [List.getElem?_eq_none (by simp; omega)] at hi
      nomatch hi
    rw [hik] at hi
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact False.elim (hd₀ hnone)

theorem bhOnlyInstKNone_set_some {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ} (h : BHOnlyInstKNone k σ)
    (j : ℕ) (d₀ : BHModelInst S ℓ) (im₀ : ModelDriverInstanceMeta S) (hd₀ : d₀.gs ≠ none) :
    BHOnlyInstKNone k { σ with insts := σ.insts.set j d₀, instMeta := σ.instMeta.set j im₀ } := by
  intro i d hi hnone
  rw [List.getElem?_set] at hi
  by_cases hji : j = i
  · subst hji
    simp only [↓reduceIte] at hi
    rcases Option.ite_none_right_eq_some.mp hi with ⟨_, hEq⟩
    injection hEq with hEq'
    subst hEq'
    exact False.elim (hd₀ hnone)
  · simp only [hji, ↓reduceIte] at hi
    exact h i d hi hnone

set_option maxHeartbeats 800000 in
theorem bhE2EStepLocalSm_preserves_allInstsSome
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (hσ : BHAllInstsSome σ)
    (i : ℕ) (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {p : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hp : p ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    BHAllInstsSome p.2 ∧ p.2.paused = σ.paused := by
  unfold bhE2EStepLocalSm at hp
  by_cases hClean : (!bhE2EDrvInstClean σ i) = true
  · simp only [hClean, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hσ, rfl⟩
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte] at hp
    cases hi : σ.insts[i]? with
    | none =>
      rw [hi] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨hσ, rfl⟩
    | some d =>
      rw [hi] at hp
      cases him : σ.instMeta[i]? with
      | none =>
        rw [him] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact ⟨hσ, rfl⟩
      | some im =>
        rw [him] at hp; dsimp only at hp
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp only [hCorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
          subst hp; exact ⟨hσ, rfl⟩
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hp
          cases hd : d.gs with
          | none =>
            rw [hd] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
            subst hp; exact ⟨hσ, rfl⟩
          | some gs =>
            rw [hd] at hp; dsimp only at hp
            have hRunStd : ∀ q',
                p ∈ support (do
                  let (r, gs') ← (SM.oracleImplR
                    (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                      ℓ d.spkCoins)
                    (2 + 1) qep
                    (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT) q').run gs
                  let accepted := bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  return (bhPackSmResp q' r,
                    { σ with insts := σ.insts.set i { d with gs := some gs' },
                             instMeta := σ.instMeta.set i im' })) →
                BHAllInstsSome p.2 ∧ p.2.paused = σ.paused := by
              intro q' hq'
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hq'
              rcases hq' with ⟨⟨r, gs'⟩, _, rfl⟩
              refine ⟨fun d' hd' => ?_, rfl⟩
              rcases List.mem_or_eq_of_mem_set hd' with hd'_old | rfl
              · exact hσ d' hd'_old
              · simp
            rcases sq with (((q1 | q2) | ⟨pt, c⟩) | ⟨pt, c⟩) | q5
            · exact hRunStd _ hp
            · exact hRunStd _ hp
            · cases pt with
              | A =>
                dsimp only at hp
                split_ifs at hp
                · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨hσ, rfl⟩
                · exact hRunStd _ hp
              | B =>
                dsimp only at hp
                split_ifs at hp with hAcc
                · cases hdec : bhDecodePreKeyMsgE c with
                  | none =>
                    rw [hdec] at hp
                    simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨hσ, rfl⟩
                  | some m =>
                    rw [hdec] at hp; dsimp only at hp
                    split_ifs at hp
                    · exact hRunStd _ hp
                    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨hσ, rfl⟩
                · cases hdec : bhDecodePreKeyMsgE c with
                  | none =>
                    rw [hdec] at hp; exact hRunStd _ hp
                  | some m =>
                    rw [hdec] at hp; dsimp only at hp
                    split_ifs at hp
                    · exact hRunStd _ hp
                    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨hσ, rfl⟩
            · cases pt with
              | A =>
                dsimp only at hp
                split_ifs at hp
                · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨hσ, rfl⟩
                · exact hRunStd _ hp
              | B =>
                dsimp only at hp
                split_ifs at hp with hAcc
                · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨hσ, rfl⟩
                · cases hdec : bhDecodePreKeyMsgE c with
                  | none =>
                    rw [hdec] at hp; exact hRunStd _ hp
                  | some m =>
                    rw [hdec] at hp; dsimp only at hp
                    split_ifs at hp
                    · exact hRunStd _ hp
                    · simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact ⟨hσ, rfl⟩
            · exact hRunStd _ hp

set_option maxHeartbeats 800000 in
theorem bhE2EStepLocalSm_with_paused (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (paused' : Bool) (i : ℕ)
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSm C K qep decT encT { σ with paused := paused' } i q =
      (fun p => (p.1, { p.2 with paused := paused' })) <$>
        bhE2EStepLocalSm C K qep decT encT σ i q := by
  unfold bhE2EStepLocalSm
  have hCleanEq : bhE2EDrvInstClean { σ with paused := paused' } i = bhE2EDrvInstClean σ i := rfl
  rw [hCleanEq]
  by_cases hClean : (!bhE2EDrvInstClean σ i) = true
  · simp [hClean]
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte]
    cases hi : σ.insts[i]? with
    | none =>
      have hi' : ({ σ with paused := paused' } : BHE2EDrvState S ℓ).insts[i]? = none := hi
      simp [hi']
    | some d =>
      have hi' : ({ σ with paused := paused' } : BHE2EDrvState S ℓ).insts[i]? = some d := hi
      cases him : σ.instMeta[i]? with
      | none =>
        have him' : ({ σ with paused := paused' } : BHE2EDrvState S ℓ).instMeta[i]? = none := him
        simp [hi', him']
      | some im =>
        have him' : ({ σ with paused := paused' } : BHE2EDrvState S ℓ).instMeta[i]? = some im := him
        have hCorrEq : bhE2EInstIkACorr { σ with paused := paused' } d = bhE2EInstIkACorr σ d := rfl
        simp only [hi', him', hCorrEq]
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d) = true
        · simp [hCorr]
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
          cases hd : d.gs with
          | none => simp
          | some gs =>
            dsimp only
            have hRunStd : ∀ q',
                (do
                  let (r, gs') ← (SM.oracleImplR
                    (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                      ℓ d.spkCoins)
                    (2 + 1) qep
                    (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT) q').run gs
                  let accepted := bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  return (bhPackSmResp q' r,
                    { σ with paused := paused',
                             insts := σ.insts.set i { d with gs := some gs' },
                             instMeta := σ.instMeta.set i im' })) =
                (fun p => (p.1, { p.2 with paused := paused' })) <$>
                  (do
                    let (r, gs') ← (SM.oracleImplR
                      (sessionSchemeFixedSpk
                        (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                        ℓ d.spkCoins)
                      (2 + 1) qep
                      (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT) q').run gs
                    let accepted := bhIsBobAcceptSMResp q' r
                    let im' := if !im.bobAccepted && accepted then
                        { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                      else im
                    return (bhPackSmResp q' r,
                      { σ with insts := σ.insts.set i { d with gs := some gs' },
                               instMeta := σ.instMeta.set i im' })) := by
              intro q'
              simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
            rcases q with (((q1 | q2) | ⟨p, c⟩) | ⟨p, c⟩) | q5
            · exact hRunStd _
            · exact hRunStd _
            · cases p with
              | A =>
                dsimp only
                split_ifs
                · simp
                · exact hRunStd _
              | B =>
                dsimp only
                split_ifs with hAcc
                · cases bhDecodePreKeyMsgE c with
                  | none => simp
                  | some m =>
                    dsimp only
                    split_ifs
                    · exact hRunStd _
                    · simp
                · cases bhDecodePreKeyMsgE c with
                  | none => exact hRunStd _
                  | some m =>
                    dsimp only
                    split_ifs
                    · exact hRunStd _
                    · simp
            · cases p with
              | A =>
                dsimp only
                split_ifs
                · simp
                · exact hRunStd _
              | B =>
                dsimp only
                split_ifs with hAcc
                · simp
                · cases bhDecodePreKeyMsgE c with
                  | none => exact hRunStd _
                  | some m =>
                    dsimp only
                    split_ifs
                    · exact hRunStd _
                    · simp
            · exact hRunStd _

@[simp]
theorem bhComposedPostObs_with_paused (P : SignalPqxdh.Primitives)
    (b' : Bool) (σ : BHE2EDrvState S ℓ) (paused0 : Bool) :
    bhComposedPostObs P (b', { σ with paused := paused0 }) =
      bhComposedPostObs P (b', σ) := rfl

theorem bhMkPrefixLazy_eq_const_false_of_gt (k len : ℕ) (b_k : Bool) (hgt : k < len) :
    bhMkPrefixLazy k b_k len = bhMkKeyBitConst false := by
  funext kr1 kr2
  have hne : (len == k) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hlt : decide (len < k) = false := decide_eq_false (by omega)
  unfold bhMkPrefixLazy bhMkKeyBitConst
  simp only [hne, hlt, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  refine bind_congr fun ac => ?_
  cases kr1 <;> cases kr2 <;> rfl

@[simp]
theorem bhStage1ToProb_pure {α : Type} (x : α) :
    stageOneAsProbComp (ℓ := ℓ) (PQC := BitVec 512) (pure x) = pure x := rfl

@[simp]
theorem bhStage1ToProb_bind {α β : Type}
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
    (f : α → OracleComp (unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β) :
    stageOneAsProbComp (ℓ := ℓ) (oa >>= f) =
      (stageOneAsProbComp (ℓ := ℓ) oa >>= fun x => stageOneAsProbComp (ℓ := ℓ) (f x)) := by
  unfold stageOneAsProbComp
  exact simulateQ_bind _ oa f

theorem bhPlugExt_mapIdx_bhFinishStartSpkGen_eq
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (σ : BHE2EDrvState S ℓ) (hAll : BHAllInstsSome σ)
    (st2 : SignalPqxdh.KeyIndState S) (sid : SignalPqxdh.SessionId S)
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u : Fin S.N_id} {j : Fin S.N_recv}
    (hG : bhE2EGuard σ sid = some (hdr, bnd, (u, j)))
    (dk : SignalPqxdh.DRKey) (spkSk : SignalPqxdh.Bytes)
    (hLen : (dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
      dk.pqrKey.length == 32 && spkSk.length == 32) = true)
    (ac : BitVec 256) (k_fresh : SampledSessionKey) (b_k : Bool) :
    let σ_true := (bhE2EFinishStartSpk C K (some true) { σ with st := st2 } sid
      (.drKeyResp dk) (.spkSkResp spkSk) ac).2
    let k := σ.insts.length
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    let gs0 := SM.initState
      (sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr (bhIdKeyOf hdr.ikAPk) (bhIdKeyOf bnd.ikB))
        ℓ (bhBytesWord spkSk)).sendPart k_fresh b_k
    let σ_p : BHE2EDrvState S ℓ :=
      { σ_true with
        insts := σ_true.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d),
        paused := true }
    let σ_lazy := (bhFinishStartSpkGen C K { σ with st := st2 } sid
      (.drKeyResp dk) (.spkSkResp spkSk) (k_fresh, b_k)).2
    bhPlugExt gs0 σ_p = { σ_lazy with paused := true } := by
  intro σ_true k spqr gs0 σ_p σ_lazy
  have hTrue : σ_true =
      { σ with st := st2,
               insts := σ.insts ++ [{
                 sid := sid, hdr := hdr,
                 idA := bhIdKeyOf hdr.ikAPk, idB := bhIdKeyOf bnd.ikB,
                 spkCoins := bhBytesWord spkSk,
                 gs := some (SM.initState (sessionSchemeFixedSpk
                   (paramsIdsWithSpqr C spqr (bhIdKeyOf hdr.ikAPk) (bhIdKeyOf bnd.ikB))
                   ℓ (bhBytesWord spkSk)).sendPart (bhKeySOf dk ac) true) }],
               instMeta := σ.instMeta ++
                 [{ respPrin := some u, respSpkIdx := some j, instOpkId? := hdr.opkId? }] } := by
    dsimp only [σ_true, bhE2EFinishStartSpk, spqr]
    simp [bhE2EGuard_with_st, hG, hLen]
  have hLazy : σ_lazy =
      { σ with st := st2,
               insts := σ.insts ++ [{
                 sid := sid, hdr := hdr,
                 idA := bhIdKeyOf hdr.ikAPk, idB := bhIdKeyOf bnd.ikB,
                 spkCoins := bhBytesWord spkSk,
                 gs := some gs0 }],
               instMeta := σ.instMeta ++
                 [{ respPrin := some u, respSpkIdx := some j, instOpkId? := hdr.opkId? }] } := by
    dsimp only [σ_lazy, bhFinishStartSpkGen, gs0, spqr]
    simp [bhE2EGuard_with_st, hG, hLen]
  dsimp only [bhPlugExt, σ_p]
  rw [hTrue, hLazy]
  congr 1
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_mapIdx]
  by_cases hlt : i < k
  · have hik : i ≠ k := by omega
    rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
    cases hi : σ.insts[i]? with
    | none => rfl
    | some d =>
      have hd_some : d.gs ≠ none := hAll d (List.mem_of_getElem? hi)
      cases hgs : d.gs with
      | none => exact False.elim (hd_some hgs)
      | some gs => simp [hik, bhPlugExtInst, hgs]
  · by_cases heq : i = k
    · subst heq
      rw [List.getElem?_append_right (le_refl k), List.getElem?_append_right (le_refl k),
        Nat.sub_self]
      simp [bhPlugExtInst, gs0]
    · have hgt : k + 1 ≤ i := by omega
      rw [List.getElem?_eq_none (by simp [k]; omega), List.getElem?_eq_none (by simp [k]; omega)]
      rfl

abbrev bhDefaultPrefixCtx : BHPrefixCtx :=
  { idA := bhIdKeyOf [], idB := bhIdKeyOf [], spkCoins := 0 }

/-! ## Wire-filtering factorization and `BHPrefixPlugInv` -/

def bhFilterSmQuery {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    Option (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
  match q with
  | .inl (.inl (.inr (.A, c))) =>
    if (bhDecodePreKeyMsgE c).isSome then none else some q
  | .inl (.inr (.A, c)) =>
    if (bhDecodePreKeyMsgE c).isSome then none else some q
  | .inl (.inl (.inr (.B, c))) =>
    if !im.bobAccepted then
      match bhDecodePreKeyMsgE c with
      | some m =>
        if c == wirePrekey ::
            (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes then
          some (.inl (.inl (.inr (.B, m.inner))))
        else none
      | none => none
    else
      match bhDecodePreKeyMsgE c with
      | some m =>
        if bhHdrOfPreKeyMsg m == d.hdr then
          some (.inl (.inl (.inr (.B, m.inner))))
        else none
      | none => some (.inl (.inl (.inr (.B, c))))
  | .inl (.inr (.B, c)) =>
    if !im.bobAccepted then none
    else
      match bhDecodePreKeyMsgE c with
      | some m =>
        if bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
           decide (m.inner.length + 2048 < 2 ^ 32) then
          some (.inl (.inr (.B, m.inner)))
        else none
      | none => some (.inl (.inr (.B, c)))
  | _ => some q

theorem bhIsBobRecvSMQuery_of_bhFilterSmQuery {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {d : BHModelInst S ℓ} {im : ModelDriverInstanceMeta S}
    {q q' : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (h : bhFilterSmQuery d im q = some q') :
    bhIsBobRecvSMQuery q' = bhIsBobRecvSMQuery q := by
  rcases q with (((q1 | q2) | ⟨p, c⟩) | ⟨p, c⟩) | q5
  · injection h with h'; subst h'; rfl
  · injection h with h'; subst h'; rfl
  · cases p with
    | A =>
      dsimp only [bhFilterSmQuery] at h
      split_ifs at h
      injection h with h'; subst h'; rfl
    | B =>
      dsimp only [bhFilterSmQuery] at h
      split_ifs at h
      · cases hdec : bhDecodePreKeyMsgE c <;> rw [hdec] at h
        · nomatch h
        · dsimp only at h
          split_ifs at h
          injection h with h'; subst h'; rfl
      · cases hdec : bhDecodePreKeyMsgE c <;> rw [hdec] at h
        · injection h with h'; subst h'; rfl
        · dsimp only at h
          split_ifs at h
          injection h with h'; subst h'; rfl
  · cases p with
    | A =>
      dsimp only [bhFilterSmQuery] at h
      split_ifs at h
      injection h with h'; subst h'; rfl
    | B =>
      dsimp only [bhFilterSmQuery] at h
      split_ifs at h
      cases hdec : bhDecodePreKeyMsgE c <;> rw [hdec] at h
      · injection h with h'; subst h'; rfl
      · dsimp only at h
        split_ifs at h
        injection h with h'; subst h'; rfl
  · injection h with h'; subst h'; rfl

set_option maxHeartbeats 800000 in
theorem bhE2EStepLocalSm_eq_filter
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSm C K qep decT encT σ i q =
      if !bhE2EDrvInstClean σ i then
        pure ((none, none, none), σ)
      else
        match σ.insts[i]?, σ.instMeta[i]? with
        | some d, some im =>
          if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d then
            let im' := { im with bobAccepted := true, ikACorrAtAccept := true }
            pure ((none, none, none), { σ with instMeta := σ.instMeta.set i im' })
          else
            match d.gs, bhFilterSmQuery d im q with
            | some gs, some q' => do
              let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
              let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
              let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
              let (r, gs') ← (SM.oracleImplR sch (2 + 1) qep cfg q').run gs
              let accepted := bhIsBobAcceptSMResp q' r
              let im' := if !im.bobAccepted && accepted then
                  { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                else im
              let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                 instMeta := σ.instMeta.set i im' }
              return (bhPackSmResp q' r, σ1)
            | _, _ => pure ((none, none, none), σ)
        | _, _ => pure ((none, none, none), σ) := by
  unfold bhE2EStepLocalSm
  by_cases hClean : (!bhE2EDrvInstClean σ i) = true
  · simp [hClean]
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte]
    cases σ.insts[i]? with
    | none => rfl
    | some d =>
      cases σ.instMeta[i]? with
      | none => rfl
      | some im =>
        dsimp only
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d) = true
        · simp [hCorr]
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
          cases d.gs with
          | none => rfl
          | some gs =>
            rcases q with (((q1 | q2) | ⟨p, c⟩) | ⟨p, c⟩) | q5
            · rfl
            · rfl
            · cases p with
              | A =>
                dsimp only [bhFilterSmQuery]
                split_ifs <;> rfl
              | B =>
                dsimp only [bhFilterSmQuery]
                split_ifs
                · cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some m => dsimp only; split_ifs <;> rfl
                · cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some m => dsimp only; split_ifs <;> rfl
            · cases p with
              | A =>
                dsimp only [bhFilterSmQuery]
                split_ifs <;> rfl
              | B =>
                dsimp only [bhFilterSmQuery]
                split_ifs
                · rfl
                · cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some m => dsimp only; split_ifs <;> rfl
            · rfl

theorem checkExtSm_eval_eq_filter
    (k : ℕ) (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhShallowCheckExtSm k σ i sq =
      if i != k || !bhE2EDrvInstClean σ k then
        .inl (.inr (none, none, none))
      else
        match σ.insts[k]?, σ.instMeta[k]? with
        | some d, some im =>
          if !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d then
            .inl (.inr (none, none, none))
          else
            match bhFilterSmQuery d im sq with
            | some sq' => .inr sq'
            | none => .inl (.inr (none, none, none))
        | _, _ => .inl (.inr (none, none, none)) := by
  dsimp only [bhShallowCheckExtSm]
  by_cases h1 : (i != k || !bhE2EDrvInstClean σ k) = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases σ.insts[k]? with
    | none => rfl
    | some d =>
      cases σ.instMeta[k]? with
      | none => rfl
      | some im =>
        dsimp only
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp [hCorr]
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
          rcases sq with (((q1 | q2) | ⟨p, c⟩) | ⟨p, c⟩) | q5
          · rfl
          · rfl
          · cases p with
            | A =>
              dsimp only [bhFilterSmQuery]
              split_ifs <;> rfl
            | B =>
              dsimp only [bhFilterSmQuery]
              split_ifs
              · cases bhDecodePreKeyMsgE c with
                | none => rfl
                | some m => dsimp only; split_ifs <;> rfl
              · cases bhDecodePreKeyMsgE c with
                | none => rfl
                | some m => dsimp only; split_ifs <;> rfl
          · cases p with
            | A =>
              dsimp only [bhFilterSmQuery]
              split_ifs <;> rfl
            | B =>
              dsimp only [bhFilterSmQuery]
              split_ifs
              · rfl
              · cases bhDecodePreKeyMsgE c with
                | none => rfl
                | some m => dsimp only; split_ifs <;> rfl
          · rfl

@[simp]
theorem bhComposedPostObs_with_b (P : SignalPqxdh.Primitives)
    (b' : Bool) (σ : BHE2EDrvState S ℓ) (b0 : Bool) :
    bhComposedPostObs P (b', { σ with b := b0 }) = bhComposedPostObs P (b', σ) := rfl

/-- State invariant on `σ : BHE2EDrvState S ℓ` during Stage 2 of `bhPrefixRed` after pausing at
instance `k`. -/
structure BHPrefixPlugInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (idA idB : IdentityKey) (s : BitVec 256) (σ : BHE2EDrvState S ℓ) : Prop where
  only_k : BHOnlyInstKNone k σ
  params_none : ∀ d ∈ σ.insts, d.gs = none →
    d.idA = idA ∧ d.idB = idB ∧ d.spkCoins = s
  inst_k_none : ∃ d, σ.insts[k]? = some d ∧ d.gs = none
  paused_true : σ.paused = true

theorem BHPrefixPlugInv.any_isNone_true {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ) :
    σ.insts.any (fun d => d.gs.isNone) = true := by
  rcases h.inst_k_none with ⟨d, hk, hd⟩
  exact List.any_eq_true.mpr ⟨d, List.mem_of_getElem? hk, by simp [hd]⟩

theorem bhPrefixPlugInv_with_b {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ) (b0 : Bool) :
    BHPrefixPlugInv k idA idB s { σ with b := b0 } :=
  ⟨h.only_k, h.params_none, h.inst_k_none, h.paused_true⟩

theorem bhPrefixPlugInv_with_st {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ) (st' : SignalPqxdh.KeyIndState S) :
    BHPrefixPlugInv k idA idB s { σ with st := st' } :=
  ⟨h.only_k, h.params_none, h.inst_k_none, h.paused_true⟩

theorem bhPrefixPlugInv_set_instMeta {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ) (i : ℕ) (im' : ModelDriverInstanceMeta S) :
    BHPrefixPlugInv k idA idB s { σ with instMeta := σ.instMeta.set i im' } :=
  ⟨h.only_k, h.params_none, h.inst_k_none, h.paused_true⟩

theorem bhPrefixPlugInv_bhE2EMirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ)
    (st' : SignalPqxdh.KeyIndState S)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) :
    BHPrefixPlugInv k idA idB s (bhE2EMirror { σ with st := st' } q r) where
  only_k i d hi hnone := by
    have hinsts : (bhE2EMirror { σ with st := st' } q r).insts = σ.insts := by
      cases q <;> cases r <;> rfl
    rw [hinsts] at hi
    exact h.only_k i d hi hnone
  params_none d hd hnone := by
    have hinsts : (bhE2EMirror { σ with st := st' } q r).insts = σ.insts := by
      cases q <;> cases r <;> rfl
    rw [hinsts] at hd
    exact h.params_none d hd hnone
  inst_k_none := by
    have hinsts : (bhE2EMirror { σ with st := st' } q r).insts = σ.insts := by
      cases q <;> cases r <;> rfl
    rw [hinsts]
    exact h.inst_k_none
  paused_true := by
    have hpaused : (bhE2EMirror { σ with st := st' } q r).paused = σ.paused := by
      cases q <;> cases r <;> rfl
    rw [hpaused]
    exact h.paused_true

theorem bhPrefixPlugInv_append_some {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ)
    (d₀ : BHModelInst S ℓ) (im₀ : ModelDriverInstanceMeta S) (st' : SignalPqxdh.KeyIndState S)
    (hd₀ : d₀.gs ≠ none) :
    BHPrefixPlugInv k idA idB s
      { σ with st := st', insts := σ.insts ++ [d₀], instMeta := σ.instMeta ++ [im₀] } where
  only_k := bhOnlyInstKNone_append_some h.only_k d₀ im₀ st' hd₀
  params_none d hd hnone := by
    rcases List.mem_append.mp hd with hd | hd
    · exact h.params_none d hd hnone
    · rw [List.mem_singleton.mp hd] at hnone
      exact False.elim (hd₀ hnone)
  inst_k_none := by
    rcases h.inst_k_none with ⟨d, hk, hd⟩
    have hlt : k < σ.insts.length := (List.getElem?_eq_some_iff.mp hk).1
    exact ⟨d, by rw [List.getElem?_append_left hlt]; exact hk, hd⟩
  paused_true := h.paused_true

theorem bhPrefixPlugInv_set_some {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256} {σ : BHE2EDrvState S ℓ}
    (h : BHPrefixPlugInv k idA idB s σ)
    (j : ℕ) (d₀ : BHModelInst S ℓ) (im₀ : ModelDriverInstanceMeta S) (hd₀ : d₀.gs ≠ none)
    (hj : ∀ d, σ.insts[j]? = some d → d.gs ≠ none) :
    BHPrefixPlugInv k idA idB s
      { σ with insts := σ.insts.set j d₀, instMeta := σ.instMeta.set j im₀ } where
  only_k := bhOnlyInstKNone_set_some h.only_k j d₀ im₀ hd₀
  params_none d hd hnone := by
    rcases List.mem_or_eq_of_mem_set hd with hd | rfl
    · exact h.params_none d hd hnone
    · exact False.elim (hd₀ hnone)
  inst_k_none := by
    rcases h.inst_k_none with ⟨d, hk, hd⟩
    have hjk : j ≠ k := fun heq => hj d (heq ▸ hk) hd
    exact ⟨d, by rw [List.getElem?_set_ne hjk]; exact hk, hd⟩
  paused_true := h.paused_true

theorem bhPlugExt_set_none_of_onlyInstKNone {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ} (hOnly : BHOnlyInstKNone k σ)
    (gs_ext gs_ext' : ExtState ℓ)
    {i : ℕ} {d : BHModelInst S ℓ} (hi : σ.insts[i]? = some d) (hd : d.gs = none)
    (im' : ModelDriverInstanceMeta S) :
    { bhPlugExt gs_ext σ with
        insts := (bhPlugExt gs_ext σ).insts.set i { d with gs := some gs_ext' },
        instMeta := σ.instMeta.set i im' } =
      bhPlugExt gs_ext' { σ with instMeta := σ.instMeta.set i im' } := by
  have hik : i = k := hOnly i d hi hd
  subst hik
  have hinsts :
      (bhPlugExt gs_ext σ).insts.set i { d with gs := some gs_ext' } =
        (bhPlugExt gs_ext' σ).insts := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_set]
    by_cases hji : i = j
    · subst hji
      rcases List.getElem?_eq_some_iff.mp hi with ⟨hlt, hdi⟩
      simp [bhPlugExt, hlt, hdi, bhPlugExtInst, hd]
    · simp only [hji, ↓reduceIte, bhPlugExt, List.getElem?_map]
      cases hj : σ.insts[j]? with
      | none => rfl
      | some dj =>
        simp only [Option.map_some, Option.some.injEq]
        cases hgs : dj.gs with
        | some gs_j => simp [bhPlugExtInst, hgs]
        | none =>
          exfalso
          exact hji (hOnly j dj hj hgs).symm
  cases σ
  simp only [bhPlugExt, BHE2EDrvState.mk.injEq, true_and, and_true]
  exact hinsts

theorem bhPrefixPlugInv_init {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (σ' : BHE2EDrvState S ℓ) (hAll : BHAllInstsSome σ') (hk : k < σ'.insts.length) :
    let ctx : BHPrefixCtx := match σ'.insts[k]? with
      | some d => { idA := d.idA, idB := d.idB, spkCoins := d.spkCoins }
      | none => bhDefaultPrefixCtx
    let σ_p : BHE2EDrvState S ℓ :=
      { σ' with
        insts := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d),
        paused := true }
    BHPrefixPlugInv k ctx.idA ctx.idB ctx.spkCoins σ_p := by
  intro ctx σ_p
  have hOnly : BHOnlyInstKNone k σ_p := by
    intro i d' hi hnone
    exact bhOnlyInstKNone_of_allInstsSome_mapIdx k σ' hAll i d' hi hnone
  refine ⟨hOnly, fun d' hd' hnone => ?_, ?_, rfl⟩
  · rcases List.mem_iff_getElem?.mp hd' with ⟨i, hi⟩
    have hik : i = k := hOnly i d' hi hnone
    subst hik
    dsimp only [σ_p] at hi
    rw [List.getElem?_mapIdx] at hi
    rcases Option.map_eq_some_iff.mp hi with ⟨d, hd, rfl⟩
    simp [ctx, hd]
  · refine ⟨{ σ'.insts[k] with gs := none }, ?_, rfl⟩
    dsimp only [σ_p]
    rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hk]
    simp

/-- Stage-1 output invariant for `bhPrefixRed`: either `.done _ σ'` has `σ'.paused = false`, or
`.paused _ c _ σ_p cont` satisfies `BHPrefixPlugInv` and the query bound on `cont`. -/
def BHMidStage1Props {S : SignalPqxdh.Setup} {ℓ : ℕ} (k q : ℕ) :
    Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ) (BHE2EDrvState S ℓ) BHPrefixCtx → Prop
  | .done _ σ' => σ'.paused = false
  | .paused _ c _ σ_p cont =>
    BHPrefixPlugInv k c.idA c.idB c.spkCoins σ_p ∧
    (∀ v, (cont v).IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) q)

def BHMidEval1Props {S : SignalPqxdh.Setup} {ℓ : ℕ} (k qTot : ℕ)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool (Option ℕ)
      (BHE2EDrvState S ℓ) BHPrefixCtx) : Prop :=
  match o.2 with
  | .done _ σ' => σ'.paused = false
  | .paused _ c _ σ_p cont =>
    o.1 = c ∧
    BHPrefixPlugInv k o.1.idA o.1.idB o.1.spkCoins σ_p ∧
    (∀ v, (cont v).IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512))) qTot)

@[simp]
theorem simulateQ_implExt_query_inl_run
    (Z : Crypto) (spqr : Spqr Bytes (BitVec 512)) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256)
    (n : ℕ) (gs_ext : ExtState ℓ) :
    (simulateQ (implExt Z spqr ℓ qep decT encT idA idB s)
      (query (spec := unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (Sum.inl n))).run gs_ext =
    ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u => pure (u, gs_ext)) := by
  simp [implExt]

@[simp]
theorem bhE2EInstIkACorr_with_gs (σ : BHE2EDrvState S ℓ) (d : BHModelInst S ℓ)
    (gs? : Option (ExtState ℓ)) :
    bhE2EInstIkACorr σ { d with gs := gs? } = bhE2EInstIkACorr σ d := rfl

@[simp]
theorem bhFilterSmQuery_with_gs (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (gs? : Option (ExtState ℓ))
    (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhFilterSmQuery { d with gs := gs? } im sq = bhFilterSmQuery d im sq := rfl

@[simp]
theorem simulateQ_implExt_query_inr_run
    (C : Crypto) (spqr : Spqr Bytes (BitVec 512)) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (s : BitVec 256)
    (sq' : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (gs_ext : ExtState ℓ) :
    (simulateQ (implExt C spqr ℓ qep decT encT idA idB s)
      (query (spec := unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (.inr sq'))).run gs_ext =
    (SM.oracleImplR (sessionSchemeFixedSpk
      (paramsIdsWithSpqr C spqr idA idB) ℓ s)
      (2 + 1) qep (configRefuseEarlyBobCorr decT encT) sq').run gs_ext := by
  simp [implExt]

def bhComposedPostObsPlug {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (b_k : Bool) :
    (Bool × BHE2EDrvState S ℓ) × ExtState ℓ → ProbComp Bool :=
  fun ⟨⟨b', σ⟩, gs_ext⟩ =>
    if !allTestedSessionsFresh P σ.st then do
      let coin ← ($ᵗ Bool : ProbComp Bool)
      return coin
    else
      let w1 := bhE2EDrvWon σ true || ((b_k == true) && gs_ext.win)
      let w0 := bhE2EDrvWon σ false || ((b_k == false) && gs_ext.win)
      return (if w1 then true else if w0 then false else b')

theorem bhComposedPostObs_bhPlugExt_eq {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (b_k : Bool) {k : ℕ} {idA idB : IdentityKey} {s : BitVec 256}
    (b' : Bool) (σ' : BHE2EDrvState S ℓ) (gs_ext : ExtState ℓ)
    (h : BHPrefixPlugInv k idA idB s σ') (hb : gs_ext.b = b_k) :
    bhComposedPostObsPlug P b_k ((b', σ'), gs_ext) =
      bhComposedPostObs P (b', bhPlugExt gs_ext σ') := by
  unfold bhComposedPostObsPlug bhComposedPostObs
  have hAny : σ'.insts.any (fun d => d.gs.isNone) = true := h.any_isNone_true
  have hSt : (bhPlugExt gs_ext σ').st = σ'.st := rfl
  simp [bhE2EDrvWon_bhPlugExt, hAny, hb, hSt]

def bhPrefixRedPost {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (flip b' : Bool)
    (σ : BHE2EDrvState S ℓ) : ProbComp Bool :=
  if !allTestedSessionsFresh P σ.st then do
    let coin ← ($ᵗ Bool : ProbComp Bool)
    return (coin ^^ flip)
  else
    let out := if bhE2EDrvWon σ true then true else if bhE2EDrvWon σ false then false else b'
    pure (out ^^ flip)

end PrefixFactorization

end CryptoVerification.E2E


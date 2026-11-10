/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1
public import Computational.Proofs.E2E.ComposedKeyIndHop
import Computational.Proofs.ReductionDsl.SM.GameCosted
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.Theorem8And12Statements
import VCVio.EvalDist.Monad.Basic

/-!
# State-field independence lemmas for `bhKindRed`

**Checked by Lean.**

Proves independence of `BHE2EDrvState` predicates and local SM steps (`bhE2EFinishStartSpk`,
`bhE2EStepLocalSm`) from the external `KeyIndState` and challenge-bit fields used by `bhKindRed`.
-/

@[expose] public section

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E ReductionDsl

namespace CryptoVerification.E2E

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}

abbrev bhKindDummySt (S : SignalPqxdh.Setup) : SignalPqxdh.KeyIndState S :=
  SignalPqxdh.KeyIndState.empty S false

@[simp]
theorem bhE2EDrvInstClean_with_st (σ : BHE2EDrvState S ℓ) (st' : SignalPqxdh.KeyIndState S)
    (i : ℕ) : bhE2EDrvInstClean { σ with st := st' } i = bhE2EDrvInstClean σ i := rfl

@[simp]
theorem bhE2EDrvWon_with_st (σ : BHE2EDrvState S ℓ) (st' : SignalPqxdh.KeyIndState S) (b : Bool) :
    bhE2EDrvWon { σ with st := st' } b = bhE2EDrvWon σ b := rfl

@[simp]
theorem bhE2EGuard_with_st (σ : BHE2EDrvState S ℓ) (st' : SignalPqxdh.KeyIndState S)
    (sid : SignalPqxdh.SessionId S) :
    bhE2EGuard { σ with st := st' } sid = bhE2EGuard σ sid := rfl

@[simp]
theorem bhE2EInstIkACorr_with_st (σ : BHE2EDrvState S ℓ) (st' : SignalPqxdh.KeyIndState S)
    (d : BHModelInst S ℓ) :
    bhE2EInstIkACorr { σ with st := st' } d = bhE2EInstIkACorr σ d := rfl

@[simp]
theorem bhE2EMirror_with_st (σ : BHE2EDrvState S ℓ) (st' : SignalPqxdh.KeyIndState S)
    (q : SignalPqxdh.KeyIndQuery S) (r : SignalPqxdh.KeyIndResponse) :
    bhE2EMirror { σ with st := st' } q r = { bhE2EMirror σ q r with st := st' } := rfl

@[simp]
theorem bhE2EFinishStartSpk_with_st (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (bMode? : Option Bool) (σ : BHE2EDrvState S ℓ) (st' : SignalPqxdh.KeyIndState S)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    bhE2EFinishStartSpk C K bMode? { σ with st := st' } sid kr1 kr2 ac =
      let p := bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac
      (p.1, { p.2 with st := st' }) := by
  unfold bhE2EFinishStartSpk
  simp only [bhE2EGuard_with_st]
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    cases kr1 <;> cases kr2 <;> try rfl
    dsimp only
    split_ifs <;> rfl

theorem bhE2EFinishStartSpk_st_eq (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (bMode? : Option Bool) (σ : BHE2EDrvState S ℓ)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    (bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac).2.st = σ.st := by
  unfold bhE2EFinishStartSpk
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    cases kr1 <;> cases kr2 <;> try rfl
    dsimp only
    split_ifs <;> rfl

theorem bhE2EFinishStartSpk_b_eq (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (bMode? : Option Bool) (σ : BHE2EDrvState S ℓ) (b0 : Bool) (hb : σ.b = b0)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256) :
    let p := bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac
    (p.1, { p.2 with b := b0 }) = p := by
  subst hb
  unfold bhE2EFinishStartSpk
  cases bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    cases kr1 <;> cases kr2 <;> try rfl
    dsimp only
    split_ifs <;> rfl

theorem bhE2EStepLocalSm_with_st (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (st' : SignalPqxdh.KeyIndState S) (i : ℕ)
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSm C K qep decT encT { σ with st := st' } i q =
      (fun p => (p.1, { p.2 with st := st' })) <$>
        bhE2EStepLocalSm C K qep decT encT σ i q := by
  unfold bhE2EStepLocalSm
  simp only [bhE2EDrvInstClean_with_st]
  by_cases hClean : (!bhE2EDrvInstClean σ i) = true
  · simp [hClean]
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte]
    cases hi : σ.insts[i]? with
    | none => simp
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => simp
      | some im =>
        simp only [bhE2EInstIkACorr_with_st]
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
                    { σ with st := st',
                             insts := σ.insts.set i { d with gs := some gs' },
                             instMeta := σ.instMeta.set i im' })) =
                (fun p => (p.1, { p.2 with st := st' })) <$>
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

theorem bhE2EStepLocalSm_preserves_b (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    (fun p => (p.1, { p.2 with b := σ.b })) <$>
        bhE2EStepLocalSm C K qep decT encT σ i q =
      bhE2EStepLocalSm C K qep decT encT σ i q := by
  unfold bhE2EStepLocalSm
  by_cases hClean : (!bhE2EDrvInstClean σ i) = true
  · simp [hClean]
  · simp only [hClean, Bool.false_eq_true, ↓reduceIte]
    cases hi : σ.insts[i]? with
    | none => simp
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => simp
      | some im =>
        dsimp only
        by_cases hCorr : (!im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d) = true
        · simp [hCorr]
        · simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
          cases hd : d.gs with
          | none => simp
          | some gs =>
            dsimp only
            have hRunStd : ∀ q',
                (fun p : BHE2ESmResp ℓ × BHE2EDrvState S ℓ => (p.1, { p.2 with b := σ.b })) <$>
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
                               instMeta := σ.instMeta.set i im' })) =
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
private theorem stateT_run_mk {M : Type → Type} {σ α : Type} (f : σ → M (α × σ)) (s : σ) :
    (StateT.mk f : StateT σ M α).run s = f s := rfl

@[simp]
private theorem stateT_run_lift {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem stateT_run_liftM {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem bhE2EDrvWon_with_b (σ : BHE2EDrvState S ℓ) (b' b : Bool) :
    bhE2EDrvWon { σ with b := b' } b = bhE2EDrvWon σ b := rfl

end CryptoVerification.E2E


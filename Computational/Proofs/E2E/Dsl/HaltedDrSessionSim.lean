/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.DrSessionSim -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrSessionSimAux -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrSessionSimRecvSteps -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.LocalSessionStep -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp -- proof-setup: allow-public-import

/-!
# Online-Halted Double Ratchet Session Simulator

Constructs the per-session halted Double Ratchet step simulator `haltedStepLocalSmGenC` over
`atomicE2EOps`, shared between `KindRedHalted` and `PrefixRedHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.HaltedDrSessionSim

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ops Ty Var Env Expr Comp Iface atomicSig atomicE2EOps
  atomicBaseSamplers B U32 U64 BV256 BV512 PlainT recvResultT recvResultEnc bits
  partyToBool boolToParty bytesToWordLE spqrMsgPayloadSuffix
  e2eKeyIndTargetIface e2eSessionTargetIface)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (RecvResult GameState)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight)
open CryptoVerification.E2E (Bytes BHE2EDrvState BHModelInst BHE2ESmResp SampledSessionKey
  ModelDriverInstanceMeta bhE2EDrvInstClean bhE2EInstIkACorr bhIsBobRecvSMQuery
  bhIsBobAcceptSMResp bhPackSmResp paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr)
open CryptoVerification.E2E.Costed (E2EPureOp e2eSig e2eOps GhostStT smQT smQenc smRT)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmReachBounded)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (KemFailTrackState KemFailSessionTrack initKemFailSessionTrack
   stepKemFailSend stepKemFailDeliver)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp
  (SmEpochBounded epMgmt_eq_of_epoch_lt injectR_run_eq_of_smEpochBounded)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (liftTy liftVal liftVal_heq)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore
  (SessionHaltTracker oracleImplRSessionTracked bhE2EStepLocalSmSessionTracked
   bhE2EStepLocalSmSessionTracked_eq_filter bhFilterSmQuery)
open Computational.Proofs.E2E.Dsl.M2Interfaces (e2eGsTy e2eGsEnc smQdec_smQenc)
open Computational.Proofs.E2E.Dsl.M3Interfaces (e2eDrvStateTy e2eDrvStateEnc e2eModelInstTy
  e2eModelInstEnc e2eInstMetaTy e2eInstMetaEnc e2eInstMetaDec_e2eInstMetaEnc
  packSmRespEnc DrvMetaAligned DrvSessionsBounded)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (v eLet eCaseOpt eCaseSum eAny isSomeE orE
  env_get_zero env_get_succ)
open Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch
  (prepLocalSmCtxTy prepLocalSmInTy prepLocalSmOutTy finishLocalSmInTy
   prepLocalSmE2EE finishLocalSmE2EE prepLocalSmE2EE_size finishLocalSmE2EE_size
   prepLocalSmE2EE_cost finishLocalSmE2EE_cost
   prepLocalSmE2EE_eval finishLocalSmE2EE_eval)

/-! ## Shared atomic state types -/

@[expose, reducible] def drvTy (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.drvTy S ℓ Pt

theorem drvTy_denote_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    (drvTy S ℓ Pt).denote = (e2eDrvStateTy S ℓ).denote :=
  rfl

@[expose, reducible] def drvEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (σ : BHE2EDrvState S ℓ) : (drvTy S ℓ Pt).denote :=
  Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.drvEnc σ

theorem liftVal_e2eDrvStateEnc_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (σ : BHE2EDrvState S ℓ) :
    liftVal (Pt := Pt) (e2eDrvStateEnc σ) = drvEnc σ :=
  Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.liftVal_e2eDrvStateEnc_eq σ

@[expose, reducible] def kemFailSessionTracker {ℓ : ℕ} (C : Crypto) (K : MlKem) :
    SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes
      SampledSessionKey (KemFailSessionTrack C.F Bytes) :=
  Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.kemFailSessionTracker (ℓ := ℓ) C K

@[simp] theorem kemFailSessionTracker_init {ℓ : ℕ} (C : Crypto) (K : MlKem)
    (k : SampledSessionKey) :
    (kemFailSessionTracker (ℓ := ℓ) C K).init k = initKemFailSessionTrack C.F Bytes k.2.2 :=
  rfl

theorem kemFailSessionTracker_eq_witness {ℓ : ℕ} (C : Crypto) (K : MlKem) :
    kemFailSessionTracker (ℓ := ℓ) C K =
      Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.kemFailSessionTracker (ℓ := ℓ) C.F K :=
  rfl

/-! ## Per-session halted step simulator -/

section AtomicHaltedSessionSim

abbrev kemCoinsT := Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.kemCoinsT
abbrev kemSentEntryT := Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.kemSentEntryT
abbrev kemTrackT := Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.kemTrackT
abbrev honestWireEntryT := Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.honestWireEntryT
abbrev sessHTy := Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.sessHTy

@[expose, reducible] def kemCoinsBridgeAtomicEnc {ℓ : ℕ} {Pt : Type}
    (c : CryptoVerification.SpqrV1Sync.Braid.Coins) : (kemCoinsT ℓ Pt).denote :=
  Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.kemCoinsBridgeAtomicEnc c

@[expose, reducible] def kemTrackBridgeAtomicEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (tr : KemFailTrackState F) : (kemTrackT ℓ Pt).denote :=
  Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.kemTrackBridgeAtomicEnc tr

@[expose, reducible] def sessHEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (st : KemFailSessionTrack F Bytes) : (sessHTy ℓ Pt).denote :=
  Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.sessHEnc st

abbrev KemBridgeTrackInv := Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.KemBridgeTrackInv

theorem kemBridgeTrackInv_mono {F : ShaCompress} {K : MlKem} {q₁ q₂ : ℕ}
    {st : KemFailSessionTrack F Bytes} (hq : q₁ ≤ q₂) (h : KemBridgeTrackInv F K q₁ st) :
    KemBridgeTrackInv F K q₂ st :=
  Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.kemBridgeTrackInv_mono hq h

abbrev gsAtomicTy := Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.gsAtomicTy

@[expose, reducible] def gsAtomicEnc {ℓ : ℕ} {Pt : Type}
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) : (gsAtomicTy ℓ Pt).denote :=
  Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.gsAtomicEnc gs

abbrev trArgAtomicTy := Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.trArgAtomicTy
abbrev chArgAtomicTy := Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.chArgAtomicTy
abbrev smRecvTailTy := Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.smRecvTailTy

@[expose, reducible] def smRecvTailEnc {ℓ : ℕ} {Pt : Type}
    (x : (Party × Bytes) ⊕ ((Party × Bytes) ⊕ Party)) : (smRecvTailTy ℓ Pt).denote :=
  Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.smRecvTailEnc x

@[expose, reducible] def smRecvTailToSpec {ℓ : ℕ} {PQC : Type}
    (x : (Party × Bytes) ⊕ ((Party × Bytes) ⊕ Party)) :
    (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Domain :=
  Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.smRecvTailToSpec x

abbrev atomicSmRT := Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.atomicSmRT
abbrev atomicSmQT := Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.atomicSmQT

@[expose, reducible] def packAtomicSmRespEnc {ℓ : ℕ} {Pt : Type}
    (br : BHE2ESmResp ℓ) : (atomicSmRT ℓ Pt).denote :=
  Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.packAtomicSmRespEnc br

theorem liftVal_packSmRespEnc_eq {ℓ : ℕ} {Pt : Type} (br : BHE2ESmResp ℓ) :
    liftVal (Pt := Pt) (packSmRespEnc br) = packAtomicSmRespEnc (Pt := Pt) br :=
  Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.liftVal_packSmRespEnc_eq br

theorem liftVal_smQenc_eq {ℓ : ℕ} {Pt : Type}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    liftVal (Pt := Pt) (smQenc (ℓ := ℓ) sq) =
      _root_.ReductionDsl.smQenc (ℓ := ℓ) (Pt := Pt) sq :=
  Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.liftVal_smQenc_eq sq

private theorem map_set_eq {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : ℕ) (x : α), (l.set i x).map f = (l.map f).set i (f x)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | a :: as, i + 1, x => congrArg (f a :: ·) (map_set_eq f as i x)

private theorem bits_le_succ (n : ℕ) : bits n ≤ n + 1 :=
  Nat.add_le_add_right (Nat.log_le_self 2 n) 1

private theorem bits_mono {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b :=
  Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem bits_min_succ_le_log (qep M : ℕ) :
    bits (min qep M + 1) ≤ Nat.log 2 qep + 2 := by
  unfold bits
  have hlt : qep < 2 ^ (Nat.log 2 qep + 1) := Nat.lt_pow_succ_log_self (by decide) qep
  have hpos : 1 ≤ 2 ^ (Nat.log 2 qep + 1) := Nat.one_le_pow _ 2 (by decide)
  have hm : min qep M + 1 < 2 ^ (Nat.log 2 qep + 2) := by
    rw [Nat.pow_succ]
    have := Nat.min_le_left qep M
    omega
  have hlog : Nat.log 2 (min qep M + 1) < Nat.log 2 qep + 2 :=
    Nat.log_lt_of_lt_pow (by omega) hm
  omega

private theorem map_liftP_eq {S₀ : Sig} {ι : Type} {T : OracleSpec ι}
    (I₀ : Iface S₀ T) {α β : Type} (f : α → β) (m : ProbComp α) :
    f <$> I₀.liftP m = I₀.liftP (f <$> m) := by
  simp [Iface.liftP, map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure]

private theorem liftP_pure_eq {S₀ : Sig} {ι : Type} {T : OracleSpec ι}
    (I₀ : Iface S₀ T) {α : Type} (x : α) :
    I₀.liftP (pure x) = pure x := by
  simp [Iface.liftP, simulateQ_pure]

private theorem liftP_bind_pure_eq {S₀ : Sig} {ι : Type} {T : OracleSpec ι}
    (I₀ : Iface S₀ T) {α β : Type} (m : ProbComp α) (f : α → β) :
    (I₀.liftP m >>= fun a => pure (f a)) = I₀.liftP (f <$> m) := by
  simp [Iface.liftP, map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure]

private theorem eval_bind_ret {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {a b : Ty S₀}
    (e : Expr O Γ a) (c : Comp O I₀ (a :: Γ) b) (ρ : Env Γ) :
    (Comp.bind (.ret e) c).eval ρ = c.eval (.cons (e.eval ρ) ρ) := by
  simp [Comp.eval]

@[simp] private theorem env_get_zero_loc {S₀ : Sig} {Γ : List (Ty S₀)} {t : Ty S₀}
    (x : t.denote) (ρ : Env Γ) : (Env.cons x ρ).get .zero = x := rfl

@[simp] private theorem env_get_succ_loc {S₀ : Sig} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (x : u.denote) (ρ : Env Γ) (v : Var Γ t) : (Env.cons x ρ).get (.succ v) = ρ.get v := rfl

private theorem eval_caseSum_inr {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {a b c : Ty S₀}
    (cInl : Comp O I₀ (a :: .sum a b :: Γ) c)
    (cInr : Comp O I₀ (b :: .sum a b :: Γ) c)
    (y : b.denote) (ρ : Env Γ) :
    (Comp.caseSum .v0 cInl cInr).eval (.cons (.inr y) ρ) =
      cInr.eval (.cons y (.cons (.inr y) ρ)) := rfl

/-- Bundle of lifted expression helpers, bounded list accessors, and single-session halted DR step arms. -/
structure HaltedDrStepOps (ℓ : ℕ) (Pt : Type) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) where
  appLiftE : ∀ {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))},
    Expr (e2eOps ℓ P C K decT encT) [a] b → Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) b)
  appLiftE_cost : ∀ {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (f : Expr (e2eOps ℓ P C K decT encT) [a] b) (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a)),
    (appLiftE f argE).cost ≤ argE.cost + f.cost + 1
  appLiftE_size : ∀ {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (f : Expr (e2eOps ℓ P C K decT encT) [a] b) (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a)),
    (appLiftE f argE).size ≤ argE.size + f.size + 1
  appLiftE_eval : ∀ {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (f : Expr (e2eOps ℓ P C K decT encT) [a] b) (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (ρ : Env Γ) (x : a.denote), argE.eval ρ = liftVal (Pt := Pt) x →
    (appLiftE f argE).eval ρ = liftVal (Pt := Pt) (f.eval (.cons x .nil))
  listGetOptE : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)},
    ℕ → Expr (atomicE2EOps ℓ P C K decT encT) Γ (.list t) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat → Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt t)
  listGetOptE_cost : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)} (N : ℕ)
    (lE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.list t)) (iE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat),
    (listGetOptE N lE iE).cost ≤ lE.cost + iE.cost + 18 * N + 15
  listGetOptE_size : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)} (N : ℕ)
    (lE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.list t)) (iE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat),
    (listGetOptE N lE iE).size ≤ lE.size + iE.size + 40 + bits N
  listGetOptE_eval : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)} (N : ℕ)
    (lE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.list t))
    (iE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat) (ρ : Env Γ),
    (lE.eval ρ).length ≤ N → (listGetOptE N lE iE).eval ρ = (lE.eval ρ)[iE.eval ρ]?
  listSetE : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)},
    ℕ → Expr (atomicE2EOps ℓ P C K decT encT) Γ (.list t) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat → Expr (atomicE2EOps ℓ P C K decT encT) Γ t →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (.list t)
  listSetE_cost : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)} (N : ℕ)
    (lE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.list t))
    (iE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat) (xE : Expr (atomicE2EOps ℓ P C K decT encT) Γ t),
    (listSetE N lE iE xE).cost ≤ lE.cost + iE.cost + xE.cost + 23 * N + 15
  listSetE_size : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)} (N : ℕ)
    (lE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.list t))
    (iE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat) (xE : Expr (atomicE2EOps ℓ P C K decT encT) Γ t),
    (listSetE N lE iE xE).size ≤ lE.size + iE.size + xE.size + 45 + bits N
  listSetE_eval : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)} (N : ℕ)
    (lE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.list t))
    (iE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat) (xE : Expr (atomicE2EOps ℓ P C K decT encT) Γ t)
    (ρ : Env Γ), (lE.eval ρ).length ≤ N → (listSetE N lE iE xE).eval ρ = (lE.eval ρ).set (iE.eval ρ) (xE.eval ρ)
  initTrackZeroE : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}, Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt)
  initTrackZeroE_cost : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}, (initTrackZeroE (Γ := Γ)).cost ≤ 3510
  initTrackZeroE_size : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}, (initTrackZeroE (Γ := Γ)).size ≤ 120
  initTrackZeroE_eval : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} (ρ : Env Γ),
    (initTrackZeroE (Γ := Γ)).eval ρ = sessHEnc (initKemFailSessionTrack C.F Bytes 0#256)
  initTrackZero_inv : ∀ (q : ℕ), KemBridgeTrackInv C.F K q (initKemFailSessionTrack C.F Bytes 0#256)
  trArmC : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T),
    I.smp = atomicBaseSamplers ℓ Pt → ℕ → ℕ → ∀ {Γ : List (Ty (atomicSig ℓ Pt))},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (trArgAtomicTy ℓ Pt) →
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ (.prod (atomicSmRT ℓ Pt) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt)))
  trArmC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (trArgAtomicTy ℓ Pt)) (w : I.Tag → ℕ),
    (trArmC I hsmp q qep gsE shE argE).queries w (fun _ => 0) = 0
  trArmC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (trArgAtomicTy ℓ Pt)),
    (trArmC I hsmp q qep gsE shE argE).cost ≤
      gsE.cost + shE.cost + argE.cost + 525 * q + 10 * (ℓ / 32 + 1) + bits (qep + 1) + 6500000
  trArmC_size : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (trArgAtomicTy ℓ Pt)),
    (trArmC I hsmp q qep gsE shE argE).size ≤
      gsE.size + shE.size + argE.size + 25 * bits (q + 1) + 5 * bits (qep + 1) + 30000
  trArmC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (trArgAtomicTy ℓ Pt))
    (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (sh : KemFailSessionTrack C.F Bytes)
    (Q : Party) (m : Plain ℓ) (optR : Option (BitVec 512)),
    SmReachBounded C K q gs → KemBridgeTrackInv C.F K q sh →
    gsE.eval ρ = gsAtomicEnc gs → shE.eval ρ = sessHEnc sh → argE.eval ρ = (partyToBool Q, (m, optR)) →
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
      .inl (.inl (.inl (.inl (Q, m, optR))))
    (trArmC I hsmp q qep gsE shE argE).eval ρ =
      I.liftP ((fun out => (packAtomicSmRespEnc (Pt := Pt) (bhPackSmResp sq out.1.1),
        (gsAtomicEnc out.1.2, sessHEnc out.2))) <$>
        (((oracleImplRSessionTracked (kemFailSessionTracker C K) sm (2 + 1) qep cfg sq).run gs).run sh))

  chArmC : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T),
    I.smp = atomicBaseSamplers ℓ Pt → ℕ → ℕ → ∀ {Γ : List (Ty (atomicSig ℓ Pt))},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt) →
      Expr (atomicE2EOps ℓ P C K decT encT) Γ (chArgAtomicTy ℓ Pt) →
      Comp (atomicE2EOps ℓ P C K decT encT) I Γ
        (.prod (atomicSmRT ℓ Pt) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt)))
  chArmC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (chArgAtomicTy ℓ Pt)) (w : I.Tag → ℕ),
    (chArmC I hsmp q qep gsE shE argE).queries w (fun _ => 0) = 0
  chArmC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (chArgAtomicTy ℓ Pt)),
    (chArmC I hsmp q qep gsE shE argE).cost ≤
      gsE.cost + shE.cost + argE.cost + 525 * q + 10 * (ℓ / 32 + 1) + bits (qep + 1) + 6500000
  chArmC_size : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (chArgAtomicTy ℓ Pt)),
    (chArmC I hsmp q qep gsE shE argE).size ≤
      gsE.size + shE.size + argE.size + 25 * bits (q + 1) + 5 * bits (qep + 1) + 30000
  chArmC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (chArgAtomicTy ℓ Pt))
    (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (sh : KemFailSessionTrack C.F Bytes)
    (Q : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512)),
    SmReachBounded C K q gs → KemBridgeTrackInv C.F K q sh →
    gsE.eval ρ = gsAtomicEnc gs → shE.eval ρ = sessHEnc sh →
    argE.eval ρ = (partyToBool Q, (m0, (m1, optR))) →
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
      .inl (.inl (.inl (.inr (Q, m0, m1, optR))))
    (chArmC I hsmp q qep gsE shE argE).eval ρ =
      I.liftP ((fun out => (packAtomicSmRespEnc (Pt := Pt) (bhPackSmResp sq out.1.1),
        (gsAtomicEnc out.1.2, sessHEnc out.2))) <$>
        (((oracleImplRSessionTracked (kemFailSessionTracker C K) sm (2 + 1) qep cfg sq).run gs).run sh))
  recvTailC : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T),
    I.smp = atomicBaseSamplers ℓ Pt → ℕ → ℕ → ∀ {Γ : List (Ty (atomicSig ℓ Pt))},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (smRecvTailTy ℓ Pt) →
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (atomicSmRT ℓ Pt) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt)))
  recvTailC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (tailE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smRecvTailTy ℓ Pt)) (w : I.Tag → ℕ),
    (recvTailC I hsmp q qep gsE shE tailE).queries w (fun _ => 0) = 0
  recvTailC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (tailE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smRecvTailTy ℓ Pt)),
    (recvTailC I hsmp q qep gsE shE tailE).cost ≤
      gsE.cost + shE.cost + tailE.cost + 525 * q + 10 * (ℓ / 32 + 1) + bits (qep + 1) + 5200000
  recvTailC_size : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (tailE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smRecvTailTy ℓ Pt)),
    (recvTailC I hsmp q qep gsE shE tailE).size ≤
      gsE.size + shE.size + tailE.size + 55 * bits (q + 1) + 5 * bits (qep + 1) + 81000
  recvTailC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (tailE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smRecvTailTy ℓ Pt))
    (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (sh : KemFailSessionTrack C.F Bytes)
    (tail : (Party × Bytes) ⊕ ((Party × Bytes) ⊕ Party)),
    SmReachBounded C K q gs → KemBridgeTrackInv C.F K q sh →
    gsE.eval ρ = gsAtomicEnc gs → shE.eval ρ = sessHEnc sh → tailE.eval ρ = smRecvTailEnc tail →
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    let sq := smRecvTailToSpec tail
    (recvTailC I hsmp q qep gsE shE tailE).eval ρ =
      I.liftP ((fun out => (packAtomicSmRespEnc (Pt := Pt) (bhPackSmResp sq out.1.1),
        (gsAtomicEnc out.1.2, sessHEnc out.2))) <$>
        (((oracleImplRSessionTracked (kemFailSessionTracker C K) sm (2 + 1) qep cfg sq).run gs).run sh))

@[expose] def haltedStepLocalSmCost (ℓ : ℕ)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) : ℕ :=
  300 * min qStart b.q_total + 350 * b.q_total +
    550 * qInst + 10 * (ℓ / 32) + Nat.log 2 qep + 6520010

theorem haltedStepLocalSmCost_le (ℓ : ℕ)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    haltedStepLocalSmCost ℓ b qStart qInst qep ≤
      650 * b.q_total + 800 * qInst + 10 * ℓ + 4 * Nat.log 2 qep + 19000000 := by
  have hdiv : ℓ / 32 ≤ ℓ := Nat.div_le_self ℓ 32
  have hmin : min qStart b.q_total ≤ b.q_total := Nat.min_le_right _ _
  unfold haltedStepLocalSmCost
  omega

@[expose] def haltedStepLocalSmSize
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) : ℕ :=
  10 * bits (min qStart b.q_total) + 4 * bits b.q_total +
    105 * bits (qInst + 1) + 15 * bits (min qep (qInst + 4) + 1) + 145000

theorem haltedStepLocalSmSize_le (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ) :
    haltedStepLocalSmSize b qStart qInst qep ≤
      500000 + 500 * bits (CryptoVerification.E2E.bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  obtain ⟨hb, _, _, hqInst, _, _, _, _, _, _, _, _⟩ :=
    Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.params_bits_le_budget
      S b qStart qDR qInst qep ℓ
  have hMinB : bits (min qStart b.q_total) ≤ bits b.q_total := bits_mono (Nat.min_le_right _ _)
  have hQepC : bits (min qep (qInst + 4) + 1) ≤
      bits (CryptoVerification.E2E.bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
    apply bits_mono
    rw [Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.bhE2ECostBudget_eq_factors]
    have hw : qInst + 1 ≤
        Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.e2ePerStepWeightedFactor
          S b qStart qInst qep ℓ := by
      unfold Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.e2ePerStepWeightedFactor; omega
    have hmul : 1024 * (qInst + 1) ≤
        (2 ^ 10 * (b.q_total + qStart + qDR + 1)) *
          Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.e2ePerStepWeightedFactor
            S b qStart qInst qep ℓ := Nat.mul_le_mul (by omega) hw
    have hmin : min qep (qInst + 4) ≤ qInst + 4 := Nat.min_le_right _ _
    omega
  unfold haltedStepLocalSmSize
  omega

/-- Per-session halted Double Ratchet step computation over `atomicE2EOps`, parametric in the target interface. -/
@[expose] def haltedStepLocalSmGenC {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (ops : HaltedDrStepOps ℓ Pt P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (atomicSig ℓ Pt) T)
    (hsmp : I₀.smp = atomicBaseSamplers ℓ Pt)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (atomicSmQT ℓ Pt)) :
    Comp (atomicE2EOps ℓ P C K decT encT) I₀ Γ
      (.prod (atomicSmRT ℓ Pt) (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)))) :=
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let qepC := min qep (qInst + 4)
  let topT : Ty (atomicSig ℓ Pt) :=
    .prod (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) (.prod .nat (atomicSmQT ℓ Pt))
  let prepOutAT : Ty (atomicSig ℓ Pt) := liftTy (Pt := Pt) (prepLocalSmOutTy S ℓ)
  let activeT : Ty (atomicSig ℓ Pt) :=
    .prod (gsAtomicTy ℓ Pt) (.prod (atomicSmQT ℓ Pt) (liftTy (Pt := Pt) (prepLocalSmCtxTy S ℓ)))
  let stepOutT : Ty (atomicSig ℓ Pt) :=
    .prod (atomicSmRT ℓ Pt) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))
  .bind (.ret (.pair σHE (.pair idxE sqE)))
    (.bind (.ret (ops.appLiftE (prepLocalSmE2EE (S := S) nInst b.q_total b.q_total)
        (.pair (.fst (.fst .v0)) (.snd .v0))))
      (.caseSum .v0
        (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.fst .v2)))))
        (.bind (.ret (.caseOpt
            (ops.listGetOptE nInst (.snd (.fst .v2)) (.fst (.snd .v2)))
            ops.initTrackZeroE
            .v0))
          (.bind
            (.caseSum (.fst (.snd .v1))
              (ops.trArmC I₀ hsmp qInst qepC (.fst .v2) .v1 .v0)
              (.caseSum .v0
                (ops.chArmC I₀ hsmp qInst qepC (.fst .v3) .v2 .v0)
                (ops.recvTailC I₀ hsmp qInst qepC (.fst .v3) .v2 .v0)))
            (let finishArgE : Expr (atomicE2EOps ℓ P C K decT encT)
                 (stepOutT :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ)
                 (liftTy (Pt := Pt) (finishLocalSmInTy S ℓ)) :=
               .pair (.fst (.fst .v4))
                 (.pair (.fst (.snd .v4))
                   (.pair (.snd (.snd .v2))
                     (.pair (.fst (.snd .v2))
                       (.pair (.fst .v0) (.fst (.snd .v0))))))
             .ret (.pair (.fst .v0)
               (.pair (ops.appLiftE (finishLocalSmE2EE (S := S) nInst) finishArgE)
                 (ops.listSetE nInst (.snd (.fst .v4)) (.fst (.snd .v4))
                   (.snd (.snd .v0))))))))))

theorem haltedStepLocalSmGenC_queries {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (ops : HaltedDrStepOps ℓ Pt P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (atomicSig ℓ Pt) T)
    (hsmp : I₀.smp = atomicBaseSamplers ℓ Pt)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (atomicSmQT ℓ Pt))
    (w : I₀.Tag → ℕ) :
    (haltedStepLocalSmGenC ops I₀ hsmp b qStart qInst qep σHE idxE sqE).queries w (fun _ => 0) = 0 := by
  simp [haltedStepLocalSmGenC, Comp.queries, ops.trArmC_queries, ops.chArmC_queries,
    ops.recvTailC_queries]

theorem haltedStepLocalSmGenC_cost {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (ops : HaltedDrStepOps ℓ Pt P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (atomicSig ℓ Pt) T) (hsmp : I₀.smp = atomicBaseSamplers ℓ Pt)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (atomicSmQT ℓ Pt)) :
    (haltedStepLocalSmGenC ops I₀ hsmp b qStart qInst qep σHE idxE sqE).cost ≤
      σHE.cost + idxE.cost + sqE.cost + haltedStepLocalSmCost ℓ b qStart qInst qep := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let qepC := min qep (qInst + 4)
  let topT : Ty (atomicSig ℓ Pt) := .prod (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) (.prod .nat (atomicSmQT ℓ Pt))
  let prepOutAT : Ty (atomicSig ℓ Pt) := liftTy (Pt := Pt) (prepLocalSmOutTy S ℓ)
  let activeT : Ty (atomicSig ℓ Pt) :=
    .prod (gsAtomicTy ℓ Pt) (.prod (atomicSmQT ℓ Pt) (liftTy (Pt := Pt) (prepLocalSmCtxTy S ℓ)))
  let stepOutT : Ty (atomicSig ℓ Pt) := .prod (atomicSmRT ℓ Pt) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))
  let chTailT : Ty (atomicSig ℓ Pt) := .sum (chArgAtomicTy ℓ Pt) (smRecvTailTy ℓ Pt)
  have hPrep := ops.appLiftE_cost (prepLocalSmE2EE (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nInst b.q_total b.q_total)
    (.pair (.fst (.fst .v0)) (.snd .v0) : Expr _ (topT :: Γ) _)
  have hPrepInner := prepLocalSmE2EE_cost (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nInst b.q_total b.q_total
  have hGet := ops.listGetOptE_cost nInst
    (.snd (.fst .v2) : Expr _ (activeT :: prepOutAT :: topT :: Γ) _) (.fst (.snd .v2))
  have hInit := ops.initTrackZeroE_cost (Γ := activeT :: prepOutAT :: topT :: Γ)
  have hTr := ops.trArmC_cost I₀ hsmp qInst qepC
    (.fst .v2 : Expr _ (trArgAtomicTy ℓ Pt :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) _) .v1 .v0
  have hCh := ops.chArmC_cost I₀ hsmp qInst qepC
    (.fst .v3 : Expr _ (chArgAtomicTy ℓ Pt :: chTailT :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) _) .v2 .v0
  have hRecv := ops.recvTailC_cost I₀ hsmp qInst qepC
    (.fst .v3 : Expr _ (smRecvTailTy ℓ Pt :: chTailT :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) _) .v2 .v0
  have hFin := ops.appLiftE_cost (finishLocalSmE2EE (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nInst)
    (.pair (.fst (.fst .v4)) (.pair (.fst (.snd .v4)) (.pair (.snd (.snd .v2))
      (.pair (.fst (.snd .v2)) (.pair (.fst .v0) (.fst (.snd .v0)))))) :
      Expr _ (stepOutT :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) _)
  have hFinInner := finishLocalSmE2EE_cost (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nInst
  have hSet := ops.listSetE_cost nInst
    (.snd (.fst .v4) : Expr _ (stepOutT :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) _)
    (.fst (.snd .v4)) (.snd (.snd .v0))
  have hnInst : nInst ≤ min qStart b.q_total := by
    dsimp only [nInst]; omega
  have hBitsQep := bits_min_succ_le_log qep (qInst + 4)
  dsimp only [haltedStepLocalSmGenC, haltedStepLocalSmCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, nInst, qepC]
    at hPrep hPrepInner hGet hTr hCh hRecv hFin hFinInner hSet hnInst ⊢
  omega

theorem haltedStepLocalSmGenC_size {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (ops : HaltedDrStepOps ℓ Pt P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (atomicSig ℓ Pt) T) (hsmp : I₀.smp = atomicBaseSamplers ℓ Pt)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (atomicSmQT ℓ Pt)) :
    (haltedStepLocalSmGenC ops I₀ hsmp b qStart qInst qep σHE idxE sqE).size ≤
      σHE.size + idxE.size + sqE.size + haltedStepLocalSmSize b qStart qInst qep := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let qepC := min qep (qInst + 4)
  let topT : Ty (atomicSig ℓ Pt) := .prod (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) (.prod .nat (atomicSmQT ℓ Pt))
  let prepOutAT : Ty (atomicSig ℓ Pt) := liftTy (Pt := Pt) (prepLocalSmOutTy S ℓ)
  let activeT : Ty (atomicSig ℓ Pt) :=
    .prod (gsAtomicTy ℓ Pt) (.prod (atomicSmQT ℓ Pt) (liftTy (Pt := Pt) (prepLocalSmCtxTy S ℓ)))
  let stepOutT : Ty (atomicSig ℓ Pt) := .prod (atomicSmRT ℓ Pt) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))
  let chTailT : Ty (atomicSig ℓ Pt) := .sum (chArgAtomicTy ℓ Pt) (smRecvTailTy ℓ Pt)
  have hPrep := ops.appLiftE_size (prepLocalSmE2EE (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nInst b.q_total b.q_total)
    (.pair (.fst (.fst .v0)) (.snd .v0) : Expr _ (topT :: Γ) _)
  have hPrepInner := prepLocalSmE2EE_size (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nInst b.q_total b.q_total
  have hGet := ops.listGetOptE_size nInst
    (.snd (.fst .v2) : Expr _ (activeT :: prepOutAT :: topT :: Γ) _) (.fst (.snd .v2))
  have hInit := ops.initTrackZeroE_size (Γ := activeT :: prepOutAT :: topT :: Γ)
  have hTr := ops.trArmC_size I₀ hsmp qInst qepC
    (.fst .v2 : Expr _ (trArgAtomicTy ℓ Pt :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) _) .v1 .v0
  have hCh := ops.chArmC_size I₀ hsmp qInst qepC
    (.fst .v3 : Expr _ (chArgAtomicTy ℓ Pt :: chTailT :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) _) .v2 .v0
  have hRecv := ops.recvTailC_size I₀ hsmp qInst qepC
    (.fst .v3 : Expr _ (smRecvTailTy ℓ Pt :: chTailT :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) _) .v2 .v0
  have hFin := ops.appLiftE_size (finishLocalSmE2EE (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nInst)
    (.pair (.fst (.fst .v4)) (.pair (.fst (.snd .v4)) (.pair (.snd (.snd .v2))
      (.pair (.fst (.snd .v2)) (.pair (.fst .v0) (.fst (.snd .v0)))))) :
      Expr _ (stepOutT :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) _)
  have hFinInner := finishLocalSmE2EE_size (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nInst
  have hSet := ops.listSetE_size nInst
    (.snd (.fst .v4) : Expr _ (stepOutT :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) _)
    (.fst (.snd .v4)) (.snd (.snd .v0))
  have hnInst : bits nInst ≤ bits (min qStart b.q_total) :=
    bits_mono (by dsimp only [nInst]; omega)
  dsimp only [haltedStepLocalSmGenC, haltedStepLocalSmSize, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, nInst, qepC]
    at hPrep hPrepInner hGet hTr hCh hRecv hFin hFinInner hSet hnInst ⊢
  omega

private theorem oracleImplRSessionTracked_qepClamp_eq {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qInst qep : ℕ)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (sh₀ : KemFailSessionTrack C.F Bytes)
    (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hEpoch : SmEpochBounded qInst gs) :
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
    (((oracleImplRSessionTracked (kemFailSessionTracker C K)
        sm (2 + 1) (min qep (qInst + 4)) cfg q').run gs).run sh₀) =
      (((oracleImplRSessionTracked (kemFailSessionTracker C K)
        sm (2 + 1) qep cfg q').run gs).run sh₀) := by
  intro sm cfg
  by_cases hle : qep ≤ qInst + 4
  · rw [Nat.min_eq_left hle]
  · have hq₁ : qInst + 1 ≤ min qep (qInst + 4) := by omega
    have hq₂ : qInst + 1 ≤ qep := by omega
    rw [kemFailSessionTracker_eq_witness C K,
      Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.oracleImplRSessionTracked_eq_oracleImplRTrackHalted
        C.F K sm (2 + 1) (min qep (qInst + 4)) cfg,
      Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.oracleImplRSessionTracked_eq_oracleImplRTrackHalted
        C.F K sm (2 + 1) qep cfg]
    rcases q' with (((⟨Q, m, optR⟩ | ⟨Q, m0, m1, optR⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
    · have hQ₁ : gs.epoch Q + 1 ≤ min qep (qInst + 4) :=
        Nat.le_trans (Nat.add_le_add_right (hEpoch.gs_epoch_le Q) 1) hq₁
      have hQ₂ : gs.epoch Q + 1 ≤ qep :=
        Nat.le_trans (Nat.add_le_add_right (hEpoch.gs_epoch_le Q) 1) hq₂
      change ((Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.transmitRTrackHalted
          C.F K sm (2 + 1) (min qep (qInst + 4)) cfg (Q, m, optR)).run gs).run sh₀ =
        ((Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.transmitRTrackHalted
          C.F K sm (2 + 1) qep cfg (Q, m, optR)).run gs).run sh₀
      refine congrArg (StateT.run · sh₀) ?_
      unfold Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.transmitRTrackHalted
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hok : !(cfg.sendOK gs Q)
      · simp only [hok, ↓reduceIte]
      · simp only [hok, Bool.false_eq_true, ↓reduceIte]
        by_cases hwin : gs.win
        · simp only [hwin, ↓reduceIte]
        · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
          refine congrArg (StateT.run · gs) (bind_congr fun x => ?_)
          rw [epMgmt_eq_of_epoch_lt gs (2 + 1) (min qep (qInst + 4)) qep Q x.2 hQ₁ hQ₂]
    · have hQ₁ : gs.epoch Q + 1 ≤ min qep (qInst + 4) :=
        Nat.le_trans (Nat.add_le_add_right (hEpoch.gs_epoch_le Q) 1) hq₁
      have hQ₂ : gs.epoch Q + 1 ≤ qep :=
        Nat.le_trans (Nat.add_le_add_right (hEpoch.gs_epoch_le Q) 1) hq₂
      change ((Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.challRTrackHalted
          C.F K sm (2 + 1) (min qep (qInst + 4)) cfg (Q, m0, m1, optR)).run gs).run sh₀ =
        ((Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.challRTrackHalted
          C.F K sm (2 + 1) qep cfg (Q, m0, m1, optR)).run gs).run sh₀
      refine congrArg (StateT.run · sh₀) ?_
      unfold Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.challRTrackHalted
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hok : !(cfg.sendOK gs Q)
      · simp only [hok, ↓reduceIte]
      · simp only [hok, Bool.false_eq_true, ↓reduceIte]
        by_cases hwin : gs.win
        · simp only [hwin, ↓reduceIte]
        · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
          refine congrArg (StateT.run · gs) (bind_congr fun x => ?_)
          rw [epMgmt_eq_of_epoch_lt gs (2 + 1) (min qep (qInst + 4)) qep Q x.2 hQ₁ hQ₂]
    · rfl
    · change ((CryptoGames.SM.injectR sm (2 + 1) (min qep (qInst + 4)) cfg (Q, w)).run gs >>=
          fun a => pure (a, sh₀)) =
        ((CryptoGames.SM.injectR sm (2 + 1) qep cfg (Q, w)).run gs >>= fun a => pure (a, sh₀))
      rw [injectR_run_eq_of_smEpochBounded
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ (2 + 1) (min qep (qInst + 4)) qep qInst spkCoins cfg (Q, w) hEpoch
        (Nat.le_succ_of_le hq₁) (Nat.le_succ_of_le hq₂)]
    · rfl

set_option maxHeartbeats 400000 in
theorem haltedStepLocalSmGenC_eval {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (ops : HaltedDrStepOps ℓ Pt P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (atomicSig ℓ Pt) T)
    (hsmp : I₀.smp = atomicBaseSamplers ℓ Pt)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (atomicSmQT ℓ Pt))
    (ρ : Env Γ)
    (σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes))
    (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hσH : σHE.eval ρ = (drvEnc σH.1, σH.2.map sessHEnc))
    (hidx : idxE.eval ρ = i)
    (hsq : sqE.eval ρ = _root_.ReductionDsl.smQenc (ℓ := ℓ) (Pt := Pt) sq)
    (hInstLen : σH.1.insts.length ≤ min qStart (min b.q_total S.N_send_tot))
    (hMeta : DrvMetaAligned σH.1)
    (hCorrLen : σH.1.corrPrins.length ≤ b.q_total)
    (hRevLen : σH.1.revealedSpks.length ≤ b.q_total)
    (hPrinLen : σH.1.prins.length ≤ b.q_total)
    (hSess : DrvSessionsBounded C K qInst σH.1)
    (hEpoch : ∀ d ∈ σH.1.insts, ∀ gs ∈ d.gs, SmEpochBounded qInst gs)
    (hTrLen : σH.2.length ≤ min qStart (min b.q_total S.N_send_tot))
    (hTrInv : ∀ st ∈ σH.2, KemBridgeTrackInv C.F K qInst st) :
    (haltedStepLocalSmGenC ops I₀ hsmp b qStart qInst qep σHE idxE sqE).eval ρ =
      I₀.liftP
        ((fun out => (packAtomicSmRespEnc (Pt := Pt) out.1, (drvEnc out.2.1, out.2.2.map sessHEnc))) <$>
          bhE2EStepLocalSmSessionTracked (kemFailSessionTracker C K) C K qep decT encT σH i sq) := by
  rcases σH with ⟨σ, tracks⟩
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let qepC := min qep (qInst + 4)
  have hMetaLen : σ.instMeta.length ≤ nInst := hMeta.trans_le hInstLen
  have hTracksMapLen : (tracks.map (sessHEnc (ℓ := ℓ) (Pt := Pt))).length ≤ nInst := by
    simp only [List.length_map]; exact hTrLen
  rw [bhE2EStepLocalSmSessionTracked_eq_filter]
  unfold haltedStepLocalSmGenC
  dsimp only
  rw [eval_bind_ret, show (Expr.pair σHE (.pair idxE sqE)).eval ρ =
      ((drvEnc (Pt := Pt) σ, tracks.map (sessHEnc (ℓ := ℓ) (Pt := Pt))),
       (i, _root_.ReductionDsl.smQenc (ℓ := ℓ) (Pt := Pt) sq)) by
    simp [Expr.eval, hσH, hidx, hsq]]
  let topT : Ty (atomicSig ℓ Pt) :=
    .prod (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))) (.prod .nat (atomicSmQT ℓ Pt))
  let ρ₁ : Env (topT :: Γ) :=
    .cons ((drvEnc (Pt := Pt) σ, tracks.map (sessHEnc (ℓ := ℓ) (Pt := Pt))),
      (i, _root_.ReductionDsl.smQenc (ℓ := ℓ) (Pt := Pt) sq)) ρ
  have hPrepArg :
      (Expr.pair (.fst (.fst .v0)) (.snd .v0) :
        Expr (atomicE2EOps ℓ P C K decT encT) (topT :: Γ)
          (liftTy (Pt := Pt) (prepLocalSmInTy S ℓ))).eval ρ₁ =
      liftVal (Pt := Pt) (t := prepLocalSmInTy S ℓ) (e2eDrvStateEnc σ, (i, smQenc sq)) := by
    dsimp only [ρ₁, Expr.eval, Expr.v0, env_get_zero_loc]
    change (drvEnc σ, (i, _root_.ReductionDsl.smQenc sq)) =
      (liftVal (Pt := Pt) (e2eDrvStateEnc σ),
       (i, liftVal (Pt := Pt) (smQenc sq)))
    rw [liftVal_e2eDrvStateEnc_eq, liftVal_smQenc_eq]
  have hPrepEval := ops.appLiftE_eval
    (prepLocalSmE2EE (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nInst b.q_total b.q_total)
    (.pair (.fst (.fst .v0)) (.snd .v0)) ρ₁ (e2eDrvStateEnc σ, (i, smQenc sq)) hPrepArg
  rw [prepLocalSmE2EE_eval nInst b.q_total b.q_total σ i sq
    hInstLen hMeta hCorrLen hRevLen hPrinLen] at hPrepEval
  rw [eval_bind_ret]
  change (Comp.caseSum _ _ _).eval (.cons ((ops.appLiftE _ _).eval ρ₁) ρ₁) = _
  rw [hPrepEval]
  let prepOutAT : Ty (atomicSig ℓ Pt) := liftTy (Pt := Pt) (prepLocalSmOutTy S ℓ)
  let activeT : Ty (atomicSig ℓ Pt) :=
    .prod (gsAtomicTy ℓ Pt)
      (.prod (atomicSmQT ℓ Pt) (liftTy (Pt := Pt) (prepLocalSmCtxTy S ℓ)))
  have hEarlyExit : ∀ (cInr : Comp (atomicE2EOps ℓ P C K decT encT) I₀
        (activeT :: prepOutAT :: topT :: Γ)
        (.prod (atomicSmRT ℓ Pt) (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt)))))
      (σ' : BHE2EDrvState S ℓ),
      (Comp.caseSum .v0
        (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.fst .v2)))))
        cInr).eval
        (.cons (liftVal (Pt := Pt) (t := prepLocalSmOutTy S ℓ)
          (.inl (packSmRespEnc (none, none, none), e2eDrvStateEnc σ'))) ρ₁) =
      I₀.liftP ((fun out => (packAtomicSmRespEnc (Pt := Pt) out.1, (drvEnc out.2.1, out.2.2.map sessHEnc))) <$>
        (pure ((none, none, none), (σ', tracks)) : ProbComp _)) := by
    intro cInr σ'
    let inlVal : (liftTy (Pt := Pt) (.prod (smRT GhostStT) (e2eDrvStateTy S ℓ))).denote :=
      (liftVal (Pt := Pt) (packSmRespEnc (none, none, none)), liftVal (Pt := Pt) (e2eDrvStateEnc σ'))
    change (Comp.caseSum .v0
        (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.fst .v2)))))
        cInr).eval (.cons (.inl inlVal) ρ₁) = _
    dsimp only [Comp.eval, Expr.eval, Expr.v0, Expr.v2, Env.get, ρ₁, inlVal]
    simp only [liftVal_packSmRespEnc_eq, liftVal_e2eDrvStateEnc_eq,
      map_eq_bind_pure_comp, Function.comp_def, pure_bind, liftP_pure_eq]
    rfl
  by_cases hcl : (!bhE2EDrvInstClean σ i) = true
  · simp only [hcl, ↓reduceIte]
    exact hEarlyExit _ σ
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte]
    cases hd : σ.insts[i]? with
    | none =>
      dsimp only
      exact hEarlyExit _ σ
    | some d =>
      cases him : σ.instMeta[i]? with
      | none =>
        dsimp only
        exact hEarlyExit _ σ
      | some im =>
        dsimp only
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp only [hcorr, ↓reduceIte]
          exact hEarlyExit _ _
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte]
          cases hgs : d.gs with
          | none =>
            dsimp only
            exact hEarlyExit _ σ
          | some gs =>
            cases hflt : bhFilterSmQuery d im sq with
            | none =>
              dsimp only
              exact hEarlyExit _ σ
            | some q' =>
              dsimp only
              let activeVal : activeT.denote :=
                (gsAtomicEnc gs,
                 (liftVal (Pt := Pt) (t := smQT) (smQenc q'),
                  (liftVal (Pt := Pt) (e2eModelInstEnc d),
                   (liftVal (Pt := Pt) (e2eInstMetaEnc im),
                    liftVal (Pt := Pt) (t := .bool) (bhE2EInstIkACorr σ d)))))
              let ρ₃ : Env (activeT :: prepOutAT :: topT :: Γ) :=
                .cons activeVal (.cons (.inr activeVal) ρ₁)
              change (Comp.caseSum .v0 _ _).eval (.cons (.inr activeVal) ρ₁) = _
              rw [eval_caseSum_inr, eval_bind_ret]
              have hSh0Eval :
                  (Expr.caseOpt (ops.listGetOptE nInst (.snd (.fst .v2)) (.fst (.snd .v2)))
                    ops.initTrackZeroE .v0).eval ρ₃ =
                  sessHEnc (ℓ := ℓ) (Pt := Pt)
                    ((tracks[i]?).getD ((kemFailSessionTracker (ℓ := ℓ) C K).init default)) := by
                dsimp only [Expr.eval]
                rw [ops.listGetOptE_eval nInst _ _ ρ₃
                  (by simp only [ρ₃, ρ₁, Expr.eval, Expr.v2, Env.get]; exact hTracksMapLen)]
                simp only [ρ₃, ρ₁, Expr.eval, Expr.v2, Env.get]
                rw [List.getElem?_map]
                cases hti : tracks[i]? with
                | none => dsimp only [Option.map, Option.getD]; rw [ops.initTrackZeroE_eval]; rfl
                | some sh => rfl
              change (Comp.bind _ _).eval (.cons ((Expr.caseOpt _ _ _).eval ρ₃) ρ₃) = _
              rw [hSh0Eval]
              set sh₀ := (tracks[i]?).getD ((kemFailSessionTracker (ℓ := ℓ) C K).init default)
              have hReach : SmReachBounded C K qInst gs := hSess d (List.mem_of_getElem? hd) gs hgs
              have hGsEpoch : SmEpochBounded qInst gs := hEpoch d (List.mem_of_getElem? hd) gs hgs
              have hSh0Inv : KemBridgeTrackInv C.F K qInst sh₀ := by
                dsimp only [sh₀]
                cases hti : tracks[i]? with
                | none => exact ops.initTrackZero_inv qInst
                | some sh => exact hTrInv sh (List.mem_of_getElem? hti)
              let ρ₄ : Env (sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) := .cons (sessHEnc sh₀) ρ₃
              set sm := sessionSchemeFixedSpk
                (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins
              set cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
              set mRun := ((oracleImplRSessionTracked (kemFailSessionTracker C K)
                sm (2 + 1) qep cfg q').run gs).run sh₀
              have hStepEval :
                  (Comp.caseSum (.fst (.snd .v1))
                    (ops.trArmC I₀ hsmp qInst qepC (.fst .v2) .v1 .v0)
                    (.caseSum .v0
                      (ops.chArmC I₀ hsmp qInst qepC (.fst .v3) .v2 .v0)
                      (ops.recvTailC I₀ hsmp qInst qepC (.fst .v3) .v2 .v0))).eval ρ₄ =
                  I₀.liftP ((fun out => (packAtomicSmRespEnc (Pt := Pt) (bhPackSmResp q' out.1.1),
                    (gsAtomicEnc out.1.2, sessHEnc out.2))) <$> mRun) := by
                have hClamp := oracleImplRSessionTracked_qepClamp_eq
                  (Pt := Pt) C K d.idA d.idB d.spkCoins decT encT qInst qep gs sh₀ q' hGsEpoch
                dsimp only [mRun] at hClamp ⊢; rw [← hClamp]
                have hqfEval : (Expr.fst (.snd .v1) : Expr (atomicE2EOps ℓ P C K decT encT) _ _).eval ρ₄ =
                    _root_.ReductionDsl.smQenc (ℓ := ℓ) (Pt := Pt) q' := by
                  dsimp only [ρ₄, ρ₃, activeVal, Expr.eval, Expr.v1, env_get_zero_loc, env_get_succ_loc]
                  exact liftVal_smQenc_eq q'
                dsimp only [Comp.eval]; rw [hqfEval]
                rcases q' with (((⟨Q, m, optR⟩ | ⟨Q, m0, m1, optR⟩) | dl) | ij) | cr
                · exact ops.trArmC_eval I₀ hsmp qInst qepC (.fst .v2) .v1 .v0
                    (.cons (partyToBool Q, (m, optR)) ρ₄) d.idA d.idB d.spkCoins gs sh₀ Q m optR
                    hReach hSh0Inv rfl rfl rfl
                · exact ops.chArmC_eval I₀ hsmp qInst qepC (.fst .v3) .v2 .v0
                    (.cons (partyToBool Q, (m0, (m1, optR)))
                      (.cons (t := .sum (chArgAtomicTy ℓ Pt) (smRecvTailTy ℓ Pt))
                        (Sum.inl (partyToBool Q, (m0, (m1, optR)))) ρ₄))
                    d.idA d.idB d.spkCoins gs sh₀ Q m0 m1 optR hReach hSh0Inv rfl rfl rfl
                · exact ops.recvTailC_eval I₀ hsmp qInst qepC (.fst .v3) .v2 .v0
                    (.cons (smRecvTailEnc (.inl dl)) (.cons (t := .sum (chArgAtomicTy ℓ Pt) (smRecvTailTy ℓ Pt))
                      (Sum.inr (smRecvTailEnc (.inl dl))) ρ₄))
                    d.idA d.idB d.spkCoins gs sh₀ (.inl dl) hReach hSh0Inv rfl rfl rfl
                · exact ops.recvTailC_eval I₀ hsmp qInst qepC (.fst .v3) .v2 .v0
                    (.cons (smRecvTailEnc (.inr (.inl ij))) (.cons (t := .sum (chArgAtomicTy ℓ Pt) (smRecvTailTy ℓ Pt))
                      (Sum.inr (smRecvTailEnc (.inr (.inl ij)))) ρ₄))
                    d.idA d.idB d.spkCoins gs sh₀ (.inr (.inl ij)) hReach hSh0Inv rfl rfl rfl
                · exact ops.recvTailC_eval I₀ hsmp qInst qepC (.fst .v3) .v2 .v0
                    (.cons (smRecvTailEnc (.inr (.inr cr))) (.cons (t := .sum (chArgAtomicTy ℓ Pt) (smRecvTailTy ℓ Pt))
                      (Sum.inr (smRecvTailEnc (.inr (.inr cr)))) ρ₄))
                    d.idA d.idB d.spkCoins gs sh₀ (.inr (.inr cr)) hReach hSh0Inv rfl rfl rfl
              change ((Comp.caseSum _ _ _).eval ρ₄ >>= fun v => pure ((Expr.pair _ _).eval (.cons v ρ₄))) = _
              rw [hStepEval, liftP_bind_pure_eq]
              simp only [Functor.map_map, map_bind, map_pure]; congr 1
              rw [map_eq_bind_pure_comp]; refine bind_congr fun ⟨⟨r, gs'⟩, tr'⟩ => ?_
              dsimp only [Function.comp_def]; congr 1
              let stepOutT : Ty (atomicSig ℓ Pt) := .prod (atomicSmRT ℓ Pt) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))
              let ρ₅ : Env (stepOutT :: sessHTy ℓ Pt :: activeT :: prepOutAT :: topT :: Γ) :=
                .cons (packAtomicSmRespEnc (Pt := Pt) (bhPackSmResp q' r),
                  (gsAtomicEnc gs', sessHEnc tr')) ρ₄
              have hFinArg :
                  (Expr.pair (.fst (.fst .v4))
                    (.pair (.fst (.snd .v4))
                      (.pair (.snd (.snd .v2))
                        (.pair (.fst (.snd .v2))
                          (.pair (.fst .v0) (.fst (.snd .v0)))))) :
                    Expr (atomicE2EOps ℓ P C K decT encT) _
                      (liftTy (Pt := Pt) (finishLocalSmInTy S ℓ))).eval ρ₅ =
                  liftVal (Pt := Pt) (t := finishLocalSmInTy S ℓ)
                    (e2eDrvStateEnc σ, (i, ((e2eModelInstEnc d, (e2eInstMetaEnc im, bhE2EInstIkACorr σ d)),
                      (smQenc q', (packSmRespEnc (bhPackSmResp q' r), e2eGsEnc gs'))))) := by
                dsimp only [ρ₅, ρ₄, ρ₃, ρ₁, activeVal, Expr.eval, Expr.v0, Expr.v2, Expr.v4,
                  env_get_zero_loc, env_get_succ_loc, gsAtomicEnc]
                change (drvEnc σ, (i, ((liftVal (Pt := Pt) (e2eModelInstEnc d),
                    (liftVal (Pt := Pt) (e2eInstMetaEnc im),
                     liftVal (Pt := Pt) (t := .bool) (bhE2EInstIkACorr σ d))),
                    (liftVal (Pt := Pt) (t := smQT) (smQenc q'),
                     (packAtomicSmRespEnc (Pt := Pt) (bhPackSmResp q' r),
                      liftVal (Pt := Pt) (e2eGsEnc gs')))))) =
                  (liftVal (Pt := Pt) (e2eDrvStateEnc σ),
                   (i, ((liftVal (Pt := Pt) (e2eModelInstEnc d),
                     (liftVal (Pt := Pt) (e2eInstMetaEnc im),
                      liftVal (Pt := Pt) (t := .bool) (bhE2EInstIkACorr σ d))),
                     (liftVal (Pt := Pt) (t := smQT) (smQenc q'),
                      (liftVal (Pt := Pt) (packSmRespEnc (bhPackSmResp q' r)),
                       liftVal (Pt := Pt) (e2eGsEnc gs'))))))
                rw [liftVal_e2eDrvStateEnc_eq, liftVal_packSmRespEnc_eq]
              have hFinEval := ops.appLiftE_eval
                (finishLocalSmE2EE (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K)
                  (decT := decT) (encT := encT) nInst)
                _ ρ₅ _ hFinArg
              rw [finishLocalSmE2EE_eval nInst σ i d im (bhE2EInstIkACorr σ d) q' r gs'
                hInstLen hMetaLen, liftVal_e2eDrvStateEnc_eq] at hFinEval
              have hSetEval := ops.listSetE_eval nInst
                (.snd (.fst .v4)) (.fst (.snd .v4)) (.snd (.snd .v0)) ρ₅
                (by simp only [ρ₅, ρ₄, ρ₃, ρ₁, Expr.eval, Expr.v4, Env.get]; exact hTracksMapLen)
              dsimp only [Expr.eval]
              change (_, ((ops.appLiftE _ _).eval ρ₅, (ops.listSetE _ _ _ _).eval ρ₅)) = _
              rw [hFinEval, hSetEval]
              simp only [ρ₅, ρ₄, ρ₃, ρ₁, Expr.eval, Expr.v0, Expr.v4, Env.get]
              rw [map_set_eq (sessHEnc (ℓ := ℓ) (Pt := Pt)) tracks i tr']

theorem haltedStepLocalSmGenC_eval_of_simInv {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (ops : HaltedDrStepOps ℓ Pt P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (atomicSig ℓ Pt) T)
    (hsmp : I₀.smp = atomicBaseSamplers ℓ Pt)
    {TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop}
    (hImp : ∀ q st, TrackInv q st → KemBridgeTrackInv C.F K q st)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    {qKiDone qStartDone qInstDone : ℕ}
    {σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)}
    (hInv : Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.HaltedSimInv
      TrackInv C K b qStart qInst qKiDone qStartDone qInstDone σH)
    (hInstLen : σH.1.insts.length ≤ min qStart (min b.q_total S.N_send_tot))
    (hEpoch : ∀ d ∈ σH.1.insts, ∀ gs ∈ d.gs, SmEpochBounded qInst gs)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod (drvTy S ℓ Pt) (.list (sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (atomicSmQT ℓ Pt))
    (ρ : Env Γ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hσH : σHE.eval ρ = (drvEnc σH.1, σH.2.map sessHEnc))
    (hidx : idxE.eval ρ = i)
    (hsq : sqE.eval ρ = _root_.ReductionDsl.smQenc (ℓ := ℓ) (Pt := Pt) sq) :
    (haltedStepLocalSmGenC ops I₀ hsmp b qStart qInst qep σHE idxE sqE).eval ρ =
      I₀.liftP
        ((fun out => (packAtomicSmRespEnc (Pt := Pt) out.1, (drvEnc out.2.1, out.2.2.map sessHEnc))) <$>
          bhE2EStepLocalSmSessionTracked
            (Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.kemFailSessionTracker C.F K)
            C K qep decT encT σH i sq) := by
  have hMir := hInv.mirror_full
  exact haltedStepLocalSmGenC_eval ops I₀ hsmp b qStart qInst qep σHE idxE sqE ρ σH i sq
    hσH hidx hsq hInstLen hInv.metaAligned hMir.corrPrins_le hMir.revSpks_le hMir.prins_le
    (hInv.sessions.mono hInv.dr_le) hEpoch (hInv.tracks_len ▸ hInstLen)
    (fun st hst => kemBridgeTrackInv_mono hInv.dr_le (hImp qInstDone st (hInv.tracks_inv st hst)))

/-! ## Concrete step wiring -/

theorem oracleImplRSessionTracked_recvTail_eq_trackHalted {ℓ : ℕ} {RCoins : Type}
    [SampleableType RCoins] (C : Crypto) (K : MlKem)
    (sm : CryptoGames.SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (qep : ℕ) (cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (tail : (Party × Bytes) ⊕ ((Party × Bytes) ⊕ Party)) :
    oracleImplRSessionTracked (kemFailSessionTracker (ℓ := ℓ) C K) sm (2 + 1) qep cfg
        (smRecvTailToSpec (ℓ := ℓ) tail) =
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.oracleImplRTrackHalted
        C.F K sm 3 qep cfg (smRecvTailToSpec (ℓ := ℓ) tail) :=
  Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch.oracleImplRSessionTracked_recvTail_eq_trackHalted
    C K sm qep cfg tail

@[expose] def mkHaltedDrStepOps {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (trArmC : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T),
      I.smp = atomicBaseSamplers ℓ Pt → ℕ → ℕ → ∀ {Γ : List (Ty (atomicSig ℓ Pt))},
      Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt) → Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt) →
      Expr (atomicE2EOps ℓ P C K decT encT) Γ (trArgAtomicTy ℓ Pt) →
      Comp (atomicE2EOps ℓ P C K decT encT) I Γ (.prod (atomicSmRT ℓ Pt) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))))
    (trArmC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
      (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
      (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
      (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
      (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (trArgAtomicTy ℓ Pt)) (w : I.Tag → ℕ),
      (trArmC I hsmp q qep gsE shE argE).queries w (fun _ => 0) = 0)
    (trArmC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
      (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
      (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
      (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
      (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (trArgAtomicTy ℓ Pt)),
      (trArmC I hsmp q qep gsE shE argE).cost ≤
        gsE.cost + shE.cost + argE.cost + 525 * q + 10 * (ℓ / 32 + 1) + bits (qep + 1) + 6500000)
    (trArmC_size : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
      (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
      (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
      (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
      (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (trArgAtomicTy ℓ Pt)),
      (trArmC I hsmp q qep gsE shE argE).size ≤
        gsE.size + shE.size + argE.size + 25 * bits (q + 1) + 5 * bits (qep + 1) + 30000)
    (trArmC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
      (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
      (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
      (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
      (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (trArgAtomicTy ℓ Pt))
      (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
      (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (sh : KemFailSessionTrack C.F Bytes)
      (Q : Party) (m : Plain ℓ) (optR : Option (BitVec 512)),
      SmReachBounded C K q gs → KemBridgeTrackInv C.F K q sh →
      gsE.eval ρ = gsAtomicEnc gs → shE.eval ρ = sessHEnc sh → argE.eval ρ = (partyToBool Q, (m, optR)) →
      let sm := sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
      let cfg := configRefuseEarlyBobCorr decT encT
      let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
        .inl (.inl (.inl (.inl (Q, m, optR))))
      (trArmC I hsmp q qep gsE shE argE).eval ρ =
        I.liftP ((fun out => (packAtomicSmRespEnc (Pt := Pt) (bhPackSmResp sq out.1.1),
          (gsAtomicEnc out.1.2, sessHEnc out.2))) <$>
          (((oracleImplRSessionTracked (kemFailSessionTracker C K) sm (2 + 1) qep cfg sq).run gs).run sh)))
    (chArmC : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T),
      I.smp = atomicBaseSamplers ℓ Pt → ℕ → ℕ → ∀ {Γ : List (Ty (atomicSig ℓ Pt))},
      Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt) → Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt) →
      Expr (atomicE2EOps ℓ P C K decT encT) Γ (chArgAtomicTy ℓ Pt) →
      Comp (atomicE2EOps ℓ P C K decT encT) I Γ (.prod (atomicSmRT ℓ Pt) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))))
    (chArmC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
      (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
      (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
      (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
      (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (chArgAtomicTy ℓ Pt)) (w : I.Tag → ℕ),
      (chArmC I hsmp q qep gsE shE argE).queries w (fun _ => 0) = 0)
    (chArmC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
      (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
      (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
      (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
      (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (chArgAtomicTy ℓ Pt)),
      (chArmC I hsmp q qep gsE shE argE).cost ≤
        gsE.cost + shE.cost + argE.cost + 525 * q + 10 * (ℓ / 32 + 1) + bits (qep + 1) + 6500000)
    (chArmC_size : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
      (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
      (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
      (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
      (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (chArgAtomicTy ℓ Pt)),
      (chArmC I hsmp q qep gsE shE argE).size ≤
        gsE.size + shE.size + argE.size + 25 * bits (q + 1) + 5 * bits (qep + 1) + 30000)
    (chArmC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
      (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
      (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
      (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
      (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (chArgAtomicTy ℓ Pt))
      (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
      (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) (sh : KemFailSessionTrack C.F Bytes)
      (Q : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512)),
      SmReachBounded C K q gs → KemBridgeTrackInv C.F K q sh →
      gsE.eval ρ = gsAtomicEnc gs → shE.eval ρ = sessHEnc sh →
      argE.eval ρ = (partyToBool Q, (m0, (m1, optR))) →
      let sm := sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
      let cfg := configRefuseEarlyBobCorr decT encT
      let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
        .inl (.inl (.inl (.inr (Q, m0, m1, optR))))
      (chArmC I hsmp q qep gsE shE argE).eval ρ =
        I.liftP ((fun out => (packAtomicSmRespEnc (Pt := Pt) (bhPackSmResp sq out.1.1),
          (gsAtomicEnc out.1.2, sessHEnc out.2))) <$>
          (((oracleImplRSessionTracked (kemFailSessionTracker C K) sm (2 + 1) qep cfg sq).run gs).run sh))) :
    HaltedDrStepOps ℓ Pt P C K decT encT where
  appLiftE := Computational.Proofs.E2E.Dsl.HaltedDrSessionSimAux.appLiftE
  appLiftE_cost f argE := Nat.le_of_eq (Computational.Proofs.E2E.Dsl.HaltedDrSessionSimAux.appLiftE_cost f argE)
  appLiftE_size f argE := Nat.le_of_eq (Computational.Proofs.E2E.Dsl.HaltedDrSessionSimAux.appLiftE_size f argE)
  appLiftE_eval := Computational.Proofs.E2E.Dsl.HaltedDrSessionSimAux.appLiftE_eval
  listGetOptE := Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter.atomicListGetOptE
  listGetOptE_cost := Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter.atomicListGetOptE_cost
  listGetOptE_size := Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter.atomicListGetOptE_size
  listGetOptE_eval := Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter.atomicListGetOptE_eval
  listSetE := Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter.atomicListSetE
  listSetE_cost := Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter.atomicListSetE_cost
  listSetE_size := Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter.atomicListSetE_size
  listSetE_eval := Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter.atomicListSetE_eval
  initTrackZeroE := Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.initKemFailSessionTrackAtomicE
    (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    ((Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.e2eEmbed
      ℓ (Pt := Pt) P C K decT encT).pureE (.bv256Lit 0#256) .unit)
  initTrackZeroE_cost := by
    intro Γ
    have hc := Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.initKemFailSessionTrackAtomicE_cost_le
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ)
      ((Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.e2eEmbed
        ℓ (Pt := Pt) P C K decT encT).pureE (.bv256Lit 0#256) .unit)
    have h0 : ((Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.e2eEmbed
        ℓ (Pt := Pt) P C K decT encT).pureE (.bv256Lit 0#256) (.unit : Expr _ Γ _)).cost = 3 := rfl
    omega
  initTrackZeroE_size := by
    intro Γ
    have hs := Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.initKemFailSessionTrackAtomicE_size_le
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ)
      ((Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.e2eEmbed
        ℓ (Pt := Pt) P C K decT encT).pureE (.bv256Lit 0#256) .unit)
    have h0 : ((Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.e2eEmbed
        ℓ (Pt := Pt) P C K decT encT).pureE (.bv256Lit 0#256) (.unit : Expr _ Γ _)).size = 34 := rfl
    omega
  initTrackZeroE_eval ρ :=
    Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.initKemFailSessionTrackAtomicE_eval
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT) _ ρ 0#256 rfl
  initTrackZero_inv q := kemBridgeTrackInv_mono (Nat.zero_le q)
    (Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl.kemBridgeTrackInv_init C.F K 0 (by decide) 0#256)
  trArmC := trArmC
  trArmC_queries := trArmC_queries
  trArmC_cost := trArmC_cost
  trArmC_size := trArmC_size
  trArmC_eval := trArmC_eval
  chArmC := chArmC
  chArmC_queries := chArmC_queries
  chArmC_cost := chArmC_cost
  chArmC_size := chArmC_size
  chArmC_eval := chArmC_eval
  recvTailC := Computational.Proofs.E2E.Dsl.HaltedDrSessionSimRecvSteps.haltedDrRecvTailC
  recvTailC_queries := Computational.Proofs.E2E.Dsl.HaltedDrSessionSimRecvSteps.haltedDrRecvTailC_queries_zero
  recvTailC_cost := by
    intro ι T I hsmp q qep Γ gsE shE tailE
    exact Nat.le_trans (Computational.Proofs.E2E.Dsl.HaltedDrSessionSimRecvSteps.haltedDrRecvTailC_cost_le
      I hsmp q qep gsE shE tailE) (by omega)
  recvTailC_size := by
    intro ι T I hsmp q qep Γ gsE shE tailE
    have hs := Computational.Proofs.E2E.Dsl.HaltedDrSessionSimRecvSteps.haltedDrRecvTailC_size_le
      I hsmp q qep gsE shE tailE
    have hbq : bits q ≤ bits (q + 1) := bits_mono (Nat.le_succ q)
    have hbqep : bits qep ≤ bits (qep + 1) := bits_mono (Nat.le_succ qep)
    omega
  recvTailC_eval := by
    intro ι T I hsmp q qep Γ gsE shE tailE ρ idA idB spkCoins gs sh tail hReach hInv hgs hsh htail
    have h := (Computational.Proofs.E2E.Dsl.HaltedDrSessionSimRecvSteps.haltedDrRecvTailC_eval_and_inv
      I hsmp q qep gsE shE tailE ρ idA idB spkCoins gs sh tail hReach hInv hgs hsh htail).1
    have hTail : Computational.Proofs.E2E.Dsl.HaltedDrSessionSimRecvSteps.smRecvTailToSpec
          (ℓ := ℓ) (PQC := BitVec 512) tail = smRecvTailToSpec (ℓ := ℓ) (PQC := BitVec 512) tail := by
      cases tail with
      | inl _ => rfl
      | inr s => cases s <;> rfl
    dsimp only; rw [h, map_liftP_eq, hTail, ← oracleImplRSessionTracked_recvTail_eq_trackHalted]; rfl

end AtomicHaltedSessionSim

end Computational.Proofs.E2E.Dsl.HaltedDrSessionSim

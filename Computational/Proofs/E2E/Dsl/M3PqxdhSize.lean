/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.PqxdhSim -- proof-setup: allow-public-import

/-!
# Compositional Syntax-Size Bound for `pqxdh1KeyRealStepC`

Proves closed-form `Comp.size` bounds for `pqxdh1KeyRealStepC`, its fuel-clamped variant, and
the standalone `pqxdhTestStepC` and `pqxdhRevealSpkStepC` handlers, linear in `bits` of the setup
replication bounds and `bits nAdv`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.M3PqxdhSize

open _root_.ReductionDsl (Ty Ops Var Expr Comp Iface UniformSamplerTag bits)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open SignalPqxdh (Setup Primitives)
open CryptoVerification.E2E.Costed (E2EUnifBase E2EPureOp E2ECryptoOp e2eSig
  e2eOps PB PU32 FinT drKeyT bundleT hdrT sidT keyIndQT keyIndRT)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v
  eLet eCaseOpt eCaseSum eFind eAny eMap bindV letV caseOptV findMV anyMV
  stepAIface mkStepAPqxdhHooks
  e2ePrincipalEntryTy e2eSpkBundleEntryTy e2eOpkEntryTy e2eInitiatorEntryTy e2eRespEntryTy
  e2eKeyIndStateTy
  orE isSomeE isNoneE optMapE nat2EqE nat3EqE nat4EqE
  finValE sidKeyE sidEqE optEqByE optPu32EqE optPb32EqE
  peSec0 peIkPk peSecSign peSignPk peCorr peSetCorrE
  beSpkSk beSpkPk beSpkSig bePqSk bePqPk bePqSig beRev beSetRevE
  oeSk oePk oeCons oeSetConsE
  bndIkB bndSpkId bndSpkB bndSpkSig bndOpkB bndPqId bndPqB bndPqSig
  hdrIkA hdrEkA hdrSpkId hdrOpkId hdrPqId hdrKemCt
  ieSid ieHonPeer iePeerIk iePeerSpk iePeerOpk iePeerPq ieSpkHon ieOpkHon iePqHon
  ieEkSk ieFresh ieReal ieRand ieHdr ieTested ieRev ieSetTestedE ieSetRevE ieSetRandE
  reSid reIk reSpk reOpk rePq reHdr reSendHon reReal reRand reTested reRev
  reSetTestedE reSetRevE reSetRandE
  stSecb stPrin stSpk stOpk stSess stResp stUsedOpk stUsedNoOpk stSeen stRo stAdv
  setPrinE setSpkE setOpkE setSessE setRespE setAdvE setAcceptOpkE setAcceptNoOpkE
  rNoneE rInitPrinE rPkE rCorrE rBundleE rHdrE rInitUnfreshE rAcceptFreshE rDrKeyE rSpkSkE rsE
  encECWideE encKEME zero32E dhNonZeroE dhOptNonZeroE buildSecretsE
  checkSeenE checkSeenEFuel isTestableE isTestableEFuel
  sBytes32C sRandom64C sDrKey96C sKemKeyGenC
  findHonestC findHonestCFuel isAdvRegC isGameSpkC isGameSpkCFuel isGameOpkC isGameOpkCFuel
  koskBundleOkC koskBundleOkCFuel koskSenderOkC koskSenderOkCFuel
  resolveSigPkC resolveSigPkCFuel honestPeerC honestPeerCFuel checkProvC checkProvCFuel optPow8C
  partnerC partnerRandKeyC partnerRandKeyCFuel recordRespC recordRespCFuel
  accIkSk accSpkSk accOpkSk accPqSk accTp accRp accHdr
  acceptKeysC)
open Computational.Proofs.E2E.Dsl.PqxdhSimBranches (natEqE
  initPrin1KeyB initPrin1KeyBFuel corruptB corruptBFuel
  genSpkB genSpkBFuel genOpkB genOpkBFuel
  initiateC initiateCFuel initiateOpkB initiateOpkBFuel initiateNoOpkB initiateNoOpkBFuel
  acceptOpkB acceptOpkBFuel acceptNoOpkB acceptNoOpkBFuel
  testB testBFuel ro1KeyRealB revealDh1KeyRealB revealB revealBFuel registerB
  revealSpkB revealSpkBFuel)
open Computational.Proofs.E2E.Dsl.PqxdhSim (pqxdh1KeyRealBodyG pqxdh1KeyRealStepG
  pqxdh1KeyRealStepC pqxdh1KeyRealBodyClampedG pqxdh1KeyRealStepClampedG pqxdh1KeyRealStepClampedC
  pqxdhTestStepG pqxdhTestStepC pqxdhRevealSpkStepG pqxdhRevealSpkStepC)

/-- Closed-form `Comp.size` budget for `pqxdh1KeyRealStepC`. -/
@[expose] def pqxdh1KeyRealStepSize (S : Setup) (nAdv : ℕ) : ℕ :=
  24 * bits S.N_id + 12 * bits S.N_spk_tot + 10 * bits S.N_opk_tot +
    10 * bits S.N_send_tot + 12 * bits S.N_recv_tot + 8 * bits nAdv + 20000

/-- Closed-form `Comp.size` budget for `pqxdh1KeyRealStepClampedC`. -/
@[expose] def pqxdh1KeyRealStepClampedSize (S : Setup) (nAdv : ℕ) : ℕ :=
  24 * bits (min nAdv S.N_id) + 12 * bits (min nAdv S.N_spk_tot) +
    10 * bits (min nAdv S.N_opk_tot) + 10 * bits (min nAdv S.N_send_tot) +
    12 * bits (min nAdv S.N_recv_tot) + 8 * bits nAdv + 20000

@[expose] def pqxdhTestStepSize (S : Setup) (nFuel : ℕ) : ℕ :=
  3 * bits (min nFuel S.N_send_tot) + 3 * bits (min nFuel S.N_recv_tot) + 3850

@[expose] def pqxdhRevealSpkStepSize (S : Setup) (nFuel : ℕ) : ℕ :=
  2 * bits (min nFuel S.N_spk_tot) + 250

section SizeLemmas

variable {ℓ : ℕ} {S : Setup} {Pt : Type} {P : Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
  {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
  {I : Iface (e2eSig ℓ) T} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}

/-! ## Binder, Primitive, and Projection `.size` Identities -/

@[local simp] private theorem size_v {Δ : List (Ty (e2eSig ℓ))} [Ext Γ Δ] {τ : Ty (e2eSig ℓ)}
    (x : Var Γ τ) : (v (O := O) (Δ := Δ) x).size = 1 := by
  simp [v, Expr.size]

@[local simp] private theorem size_eLet {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ τ) (k : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    (eLet e k).size = e.size + (k .zero).size + 1 := rfl

@[local simp] private theorem size_eCaseOpt {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (n : Expr O Γ υ) (s : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    (eCaseOpt e n s).size = e.size + n.size + (s .zero).size + 1 := by
  simp only [eCaseOpt, Expr.size]

@[local simp] private theorem size_eCaseSum {α β υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.sum α β))
    (l : Var (α :: Γ) α → Expr O (α :: Γ) υ) (r : Var (β :: Γ) β → Expr O (β :: Γ) υ) :
    (eCaseSum e l r).size = e.size + (l .zero).size + (r .zero).size + 1 := by
  simp only [eCaseSum, Expr.size]

@[local simp] private theorem size_eFind {τ : Ty (e2eSig ℓ)} (n : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Expr O (τ :: Γ) .bool) :
    (eFind n l p).size = l.size + (p .zero).size + bits n + 1 := by
  simp only [eFind, Expr.size]

@[local simp] private theorem size_eAny {τ : Ty (e2eSig ℓ)} (n : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Expr O (τ :: Γ) .bool) :
    (eAny n l p).size = l.size + (p .zero).size + bits n + 1 := by
  simp only [eAny, Expr.size]

@[local simp] private theorem size_eMap {τ υ : Ty (e2eSig ℓ)} (n : ℕ)
    (l : Expr O Γ (.list τ)) (f : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    (eMap n l f).size = l.size + (f .zero).size + bits n + 1 := by
  simp only [eMap, Expr.size]

@[local simp] private theorem size_bindV {τ υ : Ty (e2eSig ℓ)}
    (c : Comp O I Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    (bindV c k).size = c.size + (k .zero).size + 1 := rfl

@[local simp] private theorem size_letV {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    (letV (I := I) e k).size = e.size + (k .zero).size + 2 := by
  simp only [letV, Comp.size]; omega

@[local simp] private theorem size_caseOptV {τ υ : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt τ)) (n : Comp O I Γ υ) (s : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    (caseOptV e n s).size = e.size + n.size + (s .zero).size + 1 := by
  simp only [caseOptV, Comp.size]

@[local simp] private theorem size_findMV {τ : Ty (e2eSig ℓ)} (n : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp O I (τ :: Γ) .bool) :
    (findMV n l p).size = l.size + (p .zero).size + bits n + 1 := by
  simp only [findMV, Comp.size]

@[local simp] private theorem size_anyMV {τ : Ty (e2eSig ℓ)} (n : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp O I (τ :: Γ) .bool) :
    (anyMV n l p).size = l.size + (p .zero).size + bits n + 1 := by
  simp only [anyMV, Comp.size]

@[local simp] private theorem size_pureOp_loc (o : E2EPureOp)
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) o e).size =
      e.size + o.opSize + 1 := rfl

@[local simp] private theorem size_cryptoOp_loc (o : E2ECryptoOp)
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    (e2eCryptoOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) o e).size =
      e.size + 1 := rfl

@[local simp] private theorem size_hooks_pureOp (o : E2EPureOp)
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    ((mkStepAPqxdhHooks ℓ P C K decT encT I₀).pureOp o e).size = e.size + o.opSize + 1 := rfl

@[local simp] private theorem size_hooks_callPrim (o : E2ECryptoOp)
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    ((mkStepAPqxdhHooks ℓ P C K decT encT I₀).callPrim o e).size = e.size + 2 := rfl

@[local simp] private theorem size_hooks_sampBv256 :
    ((mkStepAPqxdhHooks ℓ P C K decT encT I₀).sampBv256 (Γ := Γ)).size = 2 := rfl

@[local simp] private theorem sz_peSec0 (e : Expr O Γ e2ePrincipalEntryTy) :
    (peSec0 e).size = e.size + 1 := rfl
@[local simp] private theorem sz_peIkPk (e : Expr O Γ e2ePrincipalEntryTy) :
    (peIkPk e).size = e.size + 2 := by simp only [peIkPk, Expr.size]
@[local simp] private theorem sz_peSecSign (e : Expr O Γ e2ePrincipalEntryTy) :
    (peSecSign e).size = e.size + 3 := by simp only [peSecSign, Expr.size]
@[local simp] private theorem sz_peSignPk (e : Expr O Γ e2ePrincipalEntryTy) :
    (peSignPk e).size = e.size + 4 := by simp only [peSignPk, Expr.size]
@[local simp] private theorem sz_peCorr (e : Expr O Γ e2ePrincipalEntryTy) :
    (peCorr e).size = e.size + 4 := by simp only [peCorr, Expr.size]

@[local simp] private theorem sz_beSpkSk (e : Expr O Γ e2eSpkBundleEntryTy) :
    (beSpkSk e).size = e.size + 1 := rfl
@[local simp] private theorem sz_beSpkPk (e : Expr O Γ e2eSpkBundleEntryTy) :
    (beSpkPk e).size = e.size + 2 := by simp only [beSpkPk, Expr.size]
@[local simp] private theorem sz_beSpkSig (e : Expr O Γ e2eSpkBundleEntryTy) :
    (beSpkSig e).size = e.size + 3 := by simp only [beSpkSig, Expr.size]
@[local simp] private theorem sz_bePqSk (e : Expr O Γ e2eSpkBundleEntryTy) :
    (bePqSk e).size = e.size + 4 := by simp only [bePqSk, Expr.size]
@[local simp] private theorem sz_bePqPk (e : Expr O Γ e2eSpkBundleEntryTy) :
    (bePqPk e).size = e.size + 5 := by simp only [bePqPk, Expr.size]
@[local simp] private theorem sz_bePqSig (e : Expr O Γ e2eSpkBundleEntryTy) :
    (bePqSig e).size = e.size + 6 := by simp only [bePqSig, Expr.size]
@[local simp] private theorem sz_beRev (e : Expr O Γ e2eSpkBundleEntryTy) :
    (beRev e).size = e.size + 6 := by simp only [beRev, Expr.size]

@[local simp] private theorem sz_oeSk (e : Expr O Γ e2eOpkEntryTy) :
    (oeSk e).size = e.size + 1 := rfl
@[local simp] private theorem sz_oePk (e : Expr O Γ e2eOpkEntryTy) :
    (oePk e).size = e.size + 2 := by simp only [oePk, Expr.size]
@[local simp] private theorem sz_oeCons (e : Expr O Γ e2eOpkEntryTy) :
    (oeCons e).size = e.size + 2 := by simp only [oeCons, Expr.size]

@[local simp] private theorem sz_bndIkB (b : Expr O Γ bundleT) :
    (bndIkB b).size = b.size + 1 := rfl
@[local simp] private theorem sz_bndSpkId (b : Expr O Γ bundleT) :
    (bndSpkId b).size = b.size + 2 := by simp only [bndSpkId, Expr.size]
@[local simp] private theorem sz_bndSpkB (b : Expr O Γ bundleT) :
    (bndSpkB b).size = b.size + 3 := by simp only [bndSpkB, Expr.size]
@[local simp] private theorem sz_bndSpkSig (b : Expr O Γ bundleT) :
    (bndSpkSig b).size = b.size + 4 := by simp only [bndSpkSig, Expr.size]
@[local simp] private theorem sz_bndOpkB (b : Expr O Γ bundleT) :
    (bndOpkB b).size = b.size + 5 := by simp only [bndOpkB, Expr.size]
@[local simp] private theorem sz_bndPqId (b : Expr O Γ bundleT) :
    (bndPqId b).size = b.size + 6 := by simp only [bndPqId, Expr.size]
@[local simp] private theorem sz_bndPqB (b : Expr O Γ bundleT) :
    (bndPqB b).size = b.size + 7 := by simp only [bndPqB, Expr.size]
@[local simp] private theorem sz_bndPqSig (b : Expr O Γ bundleT) :
    (bndPqSig b).size = b.size + 7 := by simp only [bndPqSig, Expr.size]

@[local simp] private theorem sz_hdrIkA (h : Expr O Γ hdrT) :
    (hdrIkA h).size = h.size + 1 := rfl
@[local simp] private theorem sz_hdrEkA (h : Expr O Γ hdrT) :
    (hdrEkA h).size = h.size + 2 := by simp only [hdrEkA, Expr.size]
@[local simp] private theorem sz_hdrSpkId (h : Expr O Γ hdrT) :
    (hdrSpkId h).size = h.size + 3 := by simp only [hdrSpkId, Expr.size]
@[local simp] private theorem sz_hdrOpkId (h : Expr O Γ hdrT) :
    (hdrOpkId h).size = h.size + 4 := by simp only [hdrOpkId, Expr.size]
@[local simp] private theorem sz_hdrPqId (h : Expr O Γ hdrT) :
    (hdrPqId h).size = h.size + 5 := by simp only [hdrPqId, Expr.size]
@[local simp] private theorem sz_hdrKemCt (h : Expr O Γ hdrT) :
    (hdrKemCt h).size = h.size + 5 := by simp only [hdrKemCt, Expr.size]

@[local simp] private theorem sz_ieSid (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieSid e).size = e.size + 1 := rfl
@[local simp] private theorem sz_ieHonPeer (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieHonPeer e).size = e.size + 2 := by simp only [ieHonPeer, Expr.size]
@[local simp] private theorem sz_iePeerIk (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (iePeerIk e).size = e.size + 3 := by simp only [iePeerIk, Expr.size]
@[local simp] private theorem sz_iePeerSpk (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (iePeerSpk e).size = e.size + 4 := by simp only [iePeerSpk, Expr.size]
@[local simp] private theorem sz_iePeerOpk (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (iePeerOpk e).size = e.size + 5 := by simp only [iePeerOpk, Expr.size]
@[local simp] private theorem sz_iePeerPq (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (iePeerPq e).size = e.size + 6 := by simp only [iePeerPq, Expr.size]
@[local simp] private theorem sz_ieSpkHon (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieSpkHon e).size = e.size + 7 := by simp only [ieSpkHon, Expr.size]
@[local simp] private theorem sz_ieOpkHon (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieOpkHon e).size = e.size + 8 := by simp only [ieOpkHon, Expr.size]
@[local simp] private theorem sz_iePqHon (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (iePqHon e).size = e.size + 9 := by simp only [iePqHon, Expr.size]
@[local simp] private theorem sz_ieEkSk (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieEkSk e).size = e.size + 10 := by simp only [ieEkSk, Expr.size]
@[local simp] private theorem sz_ieFresh (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieFresh e).size = e.size + 11 := by simp only [ieFresh, Expr.size]
@[local simp] private theorem sz_ieReal (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieReal e).size = e.size + 12 := by simp only [ieReal, Expr.size]
@[local simp] private theorem sz_ieRand (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieRand e).size = e.size + 13 := by simp only [ieRand, Expr.size]
@[local simp] private theorem sz_ieHdr (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieHdr e).size = e.size + 14 := by simp only [ieHdr, Expr.size]
@[local simp] private theorem sz_ieTested (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieTested e).size = e.size + 15 := by simp only [ieTested, Expr.size]
@[local simp] private theorem sz_ieRev (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieRev e).size = e.size + 15 := by simp only [ieRev, Expr.size]

@[local simp] private theorem sz_reSid (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reSid e).size = e.size + 1 := rfl
@[local simp] private theorem sz_reIk (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reIk e).size = e.size + 2 := by simp only [reIk, Expr.size]
@[local simp] private theorem sz_reSpk (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reSpk e).size = e.size + 3 := by simp only [reSpk, Expr.size]
@[local simp] private theorem sz_reOpk (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reOpk e).size = e.size + 4 := by simp only [reOpk, Expr.size]
@[local simp] private theorem sz_rePq (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (rePq e).size = e.size + 5 := by simp only [rePq, Expr.size]
@[local simp] private theorem sz_reHdr (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reHdr e).size = e.size + 6 := by simp only [reHdr, Expr.size]
@[local simp] private theorem sz_reSendHon (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reSendHon e).size = e.size + 7 := by simp only [reSendHon, Expr.size]
@[local simp] private theorem sz_reReal (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reReal e).size = e.size + 8 := by simp only [reReal, Expr.size]
@[local simp] private theorem sz_reRand (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reRand e).size = e.size + 9 := by simp only [reRand, Expr.size]
@[local simp] private theorem sz_reTested (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reTested e).size = e.size + 10 := by simp only [reTested, Expr.size]
@[local simp] private theorem sz_reRev (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reRev e).size = e.size + 10 := by simp only [reRev, Expr.size]

@[local simp] private theorem sz_stSecb (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (stSecb st).size = st.size + 1 := rfl
@[local simp] private theorem sz_stPrin (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (stPrin st).size = st.size + 2 := by simp only [stPrin, Expr.size]
@[local simp] private theorem sz_stSpk (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (stSpk st).size = st.size + 3 := by simp only [stSpk, Expr.size]
@[local simp] private theorem sz_stOpk (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (stOpk st).size = st.size + 4 := by simp only [stOpk, Expr.size]
@[local simp] private theorem sz_stSess (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (stSess st).size = st.size + 5 := by simp only [stSess, Expr.size]
@[local simp] private theorem sz_stResp (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (stResp st).size = st.size + 6 := by simp only [stResp, Expr.size]
@[local simp] private theorem sz_stUsedOpk (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (stUsedOpk st).size = st.size + 7 := by simp only [stUsedOpk, Expr.size]
@[local simp] private theorem sz_stUsedNoOpk (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (stUsedNoOpk st).size = st.size + 8 := by simp only [stUsedNoOpk, Expr.size]
@[local simp] private theorem sz_stSeen (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (stSeen st).size = st.size + 9 := by simp only [stSeen, Expr.size]
@[local simp] private theorem sz_stRo (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (stRo st).size = st.size + 10 := by simp only [stRo, Expr.size]
@[local simp] private theorem sz_stAdv (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (stAdv st).size = st.size + 10 := by simp only [stAdv, Expr.size]

@[local simp] private theorem sz_accIkSk (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    (accIkSk e).size = e.size + 1 := rfl
@[local simp] private theorem sz_accSpkSk (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    (accSpkSk e).size = e.size + 2 := by simp only [accSpkSk, Expr.size]
@[local simp] private theorem sz_accOpkSk (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    (accOpkSk e).size = e.size + 3 := by simp only [accOpkSk, Expr.size]
@[local simp] private theorem sz_accPqSk (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    (accPqSk e).size = e.size + 4 := by simp only [accPqSk, Expr.size]
@[local simp] private theorem sz_accTp (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    (accTp e).size = e.size + 5 := by simp only [accTp, Expr.size]
@[local simp] private theorem sz_accRp (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    (accRp e).size = e.size + 6 := by simp only [accRp, Expr.size]
@[local simp] private theorem sz_accHdr (e : Expr O Γ (PqxdhSimTypes.accInpTy ℓ)) :
    (accHdr e).size = e.size + 6 := by simp only [accHdr, Expr.size]

@[local simp] private theorem sz_rNoneE : (rNoneE (O := O) (Γ := Γ)).size = 2 := rfl
@[local simp] private theorem sz_rInitPrinE (ik s : Expr O Γ (PB 32)) :
    (rInitPrinE ik s).size = ik.size + s.size + 3 := by simp only [rInitPrinE, Expr.size]
@[local simp] private theorem sz_rPkE (pk : Expr O Γ (PB 32)) :
    (rPkE pk).size = pk.size + 3 := by simp only [rPkE, Expr.size]
@[local simp] private theorem sz_rCorrE (ik s : Expr O Γ (PB 32)) :
    (rCorrE ik s).size = ik.size + s.size + 5 := by simp only [rCorrE, Expr.size]
@[local simp] private theorem sz_rBundleE (b : Expr O Γ bundleT) :
    (rBundleE b).size = b.size + 5 := by simp only [rBundleE, Expr.size]
@[local simp] private theorem sz_rHdrE (h : Expr O Γ hdrT) :
    (rHdrE h).size = h.size + 6 := by simp only [rHdrE, Expr.size]
@[local simp] private theorem sz_rInitUnfreshE (dk : Expr O Γ drKeyT) (h : Expr O Γ hdrT) :
    (rInitUnfreshE dk h).size = dk.size + h.size + 8 := by
  simp only [rInitUnfreshE, Expr.size]
@[local simp] private theorem sz_rAcceptFreshE : (rAcceptFreshE (O := O) (Γ := Γ)).size = 9 := rfl
@[local simp] private theorem sz_rDrKeyE (dk : Expr O Γ drKeyT) :
    (rDrKeyE dk).size = dk.size + 9 := by simp only [rDrKeyE, Expr.size]
@[local simp] private theorem sz_rSpkSkE (sk : Expr O Γ (PB 32)) :
    (rSpkSkE sk).size = sk.size + 10 := by simp only [rSpkSkE, Expr.size]
@[local simp] private theorem sz_rsE (r : Expr O Γ keyIndRT) (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (rsE r st).size = r.size + st.size + 1 := rfl

@[local simp] private theorem size_orE (a b : Expr O Γ .bool) :
    (orE a b).size = a.size + b.size + 4 := by
  simp only [orE, Expr.size]; omega

@[local simp] private theorem size_isSomeE {τ : Ty (e2eSig ℓ)} (e : Expr O Γ (.opt τ)) :
    (isSomeE e).size = e.size + 3 := by simp only [isSomeE, Expr.size]

@[local simp] private theorem size_isNoneE {τ : Ty (e2eSig ℓ)} (e : Expr O Γ (.opt τ)) :
    (isNoneE e).size = e.size + 3 := by simp only [isNoneE, Expr.size]

@[local simp] private theorem size_optMapE {τ υ : Ty (e2eSig ℓ)} (e : Expr O Γ (.opt τ))
    (f : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    (optMapE e f).size = e.size + (f .zero).size + 3 := by
  simp only [optMapE, size_eCaseOpt, Expr.size]; omega

@[local simp] private theorem size_natEqE (a b : Expr O Γ .nat) :
    (natEqE a b).size = a.size + b.size + 1 := rfl

@[local simp] private theorem size_nat2EqE (a b : Expr O Γ (.prod .nat .nat)) :
    (nat2EqE a b).size = 2 * a.size + 2 * b.size + 7 := by
  simp only [nat2EqE, Expr.size]; omega

@[local simp] private theorem size_nat3EqE
    (a b : Expr O Γ (.prod .nat (.prod .nat .nat))) :
    (nat3EqE a b).size = 3 * a.size + 3 * b.size + 15 := by
  simp only [nat3EqE, size_nat2EqE, Expr.size]; omega

@[local simp] private theorem size_nat4EqE
    (a b : Expr O Γ (.prod .nat (.prod .nat (.prod .nat .nat)))) :
    (nat4EqE a b).size = 4 * a.size + 4 * b.size + 25 := by
  simp only [nat4EqE, size_nat3EqE, Expr.size]; omega

@[local simp] private theorem size_peSetCorrE (e : Expr O Γ e2ePrincipalEntryTy) :
    (peSetCorrE e).size = e.size + 20 := by
  simp only [peSetCorrE, size_eLet, sz_peSec0, sz_peIkPk, sz_peSecSign, sz_peSignPk,
    size_v, Expr.size]

@[local simp] private theorem size_beSetRevE (e : Expr O Γ e2eSpkBundleEntryTy) :
    (beSetRevE e).size = e.size + 35 := by
  simp only [beSetRevE, size_eLet, sz_beSpkSk, sz_beSpkPk, sz_beSpkSig, sz_bePqSk, sz_bePqPk,
    sz_bePqSig, size_v, Expr.size]

@[local simp] private theorem size_oeSetConsE (e : Expr O Γ e2eOpkEntryTy) :
    (oeSetConsE e).size = e.size + 9 := by
  simp only [oeSetConsE, size_eLet, sz_oeSk, sz_oePk, size_v, Expr.size]

@[local simp] private theorem size_ieSetTestedE (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieSetTestedE e).size = e.size + 152 := by
  simp only [ieSetTestedE, size_eLet, sz_ieSid, sz_ieHonPeer, sz_iePeerIk, sz_iePeerSpk,
    sz_iePeerOpk, sz_iePeerPq, sz_ieSpkHon, sz_ieOpkHon, sz_iePqHon, sz_ieEkSk, sz_ieFresh,
    sz_ieReal, sz_ieRand, sz_ieHdr, sz_ieRev, size_v, Expr.size]

@[local simp] private theorem size_ieSetRevE (e : Expr O Γ (e2eInitiatorEntryTy ℓ S)) :
    (ieSetRevE e).size = e.size + 152 := by
  simp only [ieSetRevE, size_eLet, sz_ieSid, sz_ieHonPeer, sz_iePeerIk, sz_iePeerSpk,
    sz_iePeerOpk, sz_iePeerPq, sz_ieSpkHon, sz_ieOpkHon, sz_iePqHon, sz_ieEkSk, sz_ieFresh,
    sz_ieReal, sz_ieRand, sz_ieHdr, sz_ieTested, size_v, Expr.size]

@[local simp] private theorem size_ieSetRandE (e : Expr O Γ (e2eInitiatorEntryTy ℓ S))
    (rk : Expr O Γ drKeyT) :
    (ieSetRandE e rk).size = e.size + rk.size + 171 := by
  simp only [ieSetRandE, size_eLet, sz_ieSid, sz_ieHonPeer, sz_iePeerIk, sz_iePeerSpk,
    sz_iePeerOpk, sz_iePeerPq, sz_ieSpkHon, sz_ieOpkHon, sz_iePqHon, sz_ieEkSk, sz_ieFresh,
    sz_ieReal, sz_ieHdr, sz_ieTested, sz_ieRev, size_v, Expr.size]

@[local simp] private theorem size_reSetTestedE (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reSetTestedE e).size = e.size + 77 := by
  simp only [reSetTestedE, size_eLet, sz_reSid, sz_reIk, sz_reSpk, sz_reOpk, sz_rePq, sz_reHdr,
    sz_reSendHon, sz_reReal, sz_reRand, sz_reRev, size_v, Expr.size]

@[local simp] private theorem size_reSetRevE (e : Expr O Γ (e2eRespEntryTy ℓ S)) :
    (reSetRevE e).size = e.size + 77 := by
  simp only [reSetRevE, size_eLet, sz_reSid, sz_reIk, sz_reSpk, sz_reOpk, sz_rePq, sz_reHdr,
    sz_reSendHon, sz_reReal, sz_reRand, sz_reTested, size_v, Expr.size]

@[local simp] private theorem size_reSetRandE (e : Expr O Γ (e2eRespEntryTy ℓ S))
    (rk : Expr O Γ drKeyT) :
    (reSetRandE e rk).size = e.size + rk.size + 90 := by
  simp only [reSetRandE, size_eLet, sz_reSid, sz_reIk, sz_reSpk, sz_reOpk, sz_rePq, sz_reHdr,
    sz_reSendHon, sz_reReal, sz_reTested, sz_reRev, size_v, Expr.size]

@[local simp] private theorem size_setPrinE (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (ps : Expr O Γ (.list (.prod .nat e2ePrincipalEntryTy))) :
    (setPrinE st ps).size = st.size + ps.size + 13 := by
  simp only [setPrinE, size_eLet, sz_stSecb, size_v, Expr.size]

@[local simp] private theorem size_setSpkE (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (bs : Expr O Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy))) :
    (setSpkE st bs).size = st.size + bs.size + 19 := by
  simp only [setSpkE, size_eLet, sz_stSecb, sz_stPrin, size_v, Expr.size]

@[local simp] private theorem size_setOpkE (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (os : Expr O Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy))) :
    (setOpkE st os).size = st.size + os.size + 26 := by
  simp only [setOpkE, size_eLet, sz_stSecb, sz_stPrin, sz_stSpk, size_v, Expr.size]

@[local simp] private theorem size_setSessE (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (ss : Expr O Γ (.list (e2eInitiatorEntryTy ℓ S))) :
    (setSessE st ss).size = st.size + ss.size + 34 := by
  simp only [setSessE, size_eLet, sz_stSecb, sz_stPrin, sz_stSpk, sz_stOpk, size_v,
    Expr.size]

@[local simp] private theorem size_setRespE (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (rs : Expr O Γ (.list (e2eRespEntryTy ℓ S))) :
    (setRespE st rs).size = st.size + rs.size + 43 := by
  simp only [setRespE, size_eLet, sz_stSecb, sz_stPrin, sz_stSpk, sz_stOpk, sz_stSess, size_v,
    Expr.size]

@[local simp] private theorem size_setAdvE (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (ak : Expr O Γ (.list (.prod (PB 32) (PB 32)))) :
    (setAdvE st ak).size = st.size + ak.size + 89 := by
  simp only [setAdvE, size_eLet, sz_stSecb, sz_stPrin, sz_stSpk, sz_stOpk, sz_stSess, sz_stResp,
    sz_stUsedOpk, sz_stUsedNoOpk, sz_stSeen, sz_stRo, size_v, Expr.size]

@[local simp] private theorem size_setAcceptOpkE (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (os : Expr O Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (used : Expr O Γ (.list (.prod .nat (.prod .nat .nat))))
    (seen : Expr O Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32)))))) :
    (setAcceptOpkE st os used seen).size =
      st.size + os.size + used.size + seen.size + 86 := by
  simp only [setAcceptOpkE, size_eLet, sz_stSecb, sz_stPrin, sz_stSpk, sz_stSess, sz_stResp,
    sz_stUsedNoOpk, sz_stRo, sz_stAdv, size_v, Expr.size]; omega

@[local simp] private theorem size_setAcceptNoOpkE (st : Expr O Γ (e2eKeyIndStateTy ℓ S))
    (used : Expr O Γ (.list (.prod .nat (.prod .nat .nat))))
    (seen : Expr O Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32)))))) :
    (setAcceptNoOpkE st used seen).size =
      st.size + used.size + seen.size + 85 := by
  simp only [setAcceptNoOpkE, size_eLet, sz_stSecb, sz_stPrin, sz_stSpk, sz_stOpk, sz_stSess,
    sz_stResp, sz_stUsedOpk, sz_stRo, sz_stAdv, size_v, Expr.size]; omega

/-! ## Hook-Parameterized Expression and Monadic Helper `.size` Identities -/

@[local simp] private theorem size_finValE {n : ℕ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (FinT n)) :
    (finValE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) e).size =
      e.size + 1 := rfl

@[local simp] private theorem size_sidKeyE
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (sidKeyE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) s).size =
      s.size + 59 := by
  simp only [sidKeyE, size_eCaseSum, size_finValE, size_v, Expr.size,
    show bits 0 = 1 from rfl, show bits 1 = 1 from rfl,
    show bits 2 = 2 from rfl, show bits 3 = 2 from rfl]

@[local simp] private theorem size_sidEqE
    (a b : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (sidEqE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) a b).size =
      4 * a.size + 4 * b.size + 497 := by
  simp only [sidEqE, size_nat4EqE, size_sidKeyE]; omega

@[local simp] private theorem size_optPu32EqE
    (a b : Expr (e2eOps ℓ P C K decT encT) Γ (.opt PU32)) :
    (optPu32EqE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) a b).size =
      a.size + b.size + 18 := by
  simp only [optPu32EqE, optEqByE, eCaseOpt, size_pureOp_loc,
    E2EPureOp.opSize, size_eLet, size_isNoneE, size_v, Expr.size]

@[local simp] private theorem size_optPb32EqE
    (a b : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32))) :
    (optPb32EqE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) a b).size =
      a.size + b.size + 18 := by
  simp only [optPb32EqE, optEqByE, eCaseOpt, size_pureOp_loc,
    E2EPureOp.opSize, size_eLet, size_isNoneE, size_v, Expr.size]

@[local simp] private theorem size_encECWideE
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (encECWideE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) pk).size =
      pk.size + 3 := rfl

@[local simp] private theorem size_encKEME
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 1568)) :
    (encKEME (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) pk).size =
      pk.size + 2 := rfl

@[local simp] private theorem size_dhNonZeroE
    (dh : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (dhNonZeroE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) dh).size =
      dh.size + 37 := by
  unfold dhNonZeroE zero32E
  simp only [size_pureOp_loc, E2EPureOp.opSize, List.length_replicate, Expr.size]

@[local simp] private theorem size_dhOptNonZeroE
    (dh4? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32))) :
    (dhOptNonZeroE (I := stepAIface ℓ I₀) (mkStepAPqxdhHooks ℓ P C K decT encT I₀) dh4?).size =
      dh4?.size + 40 := by
  unfold dhOptNonZeroE
  simp only [size_eCaseOpt, size_dhNonZeroE, size_v, Expr.size]

@[local simp] private theorem size_buildSecretsE
    (dh1 dh2 dh3 : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32))
    (dh4? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32)))
    (ss : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (buildSecretsE (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) dh1 dh2 dh3 dh4? ss).size =
      dh1.size + dh2.size + dh3.size + dh4?.size + ss.size + 65 := by
  have hF : SignalPqxdh.F_X25519.length = 32 := by simp [SignalPqxdh.F_X25519]
  have hop : ∀ o, (e2eOps ℓ P C K decT encT).opSize (Sum.inl o) = o.opSize := fun _ => rfl
  unfold buildSecretsE
  simp only [eCaseOpt, e2ePureOp, hop, E2EPureOp.opSize, hF,
    size_eLet, size_v, Expr.size]; omega

@[local simp] private theorem size_checkSeenE
    (used : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32))))))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (pqspkId spkId : Expr (e2eOps ℓ P C K decT encT) Γ PU32)
    (ekAPk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (checkSeenE (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) used k pqspkId spkId ekAPk).size =
      used.size + k.size + pqspkId.size + spkId.size + ekAPk.size +
        bits S.N_recv_tot + 60 := by
  unfold checkSeenE
  simp only [size_pureOp_loc, E2EPureOp.opSize,
    size_eLet, size_eAny, size_v, Expr.size]; omega

@[local simp] private theorem size_isTestableE
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (isTestableE (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sid).size =
      st.size + sid.size + bits S.N_send_tot + bits S.N_recv_tot + 1130 := by
  unfold isTestableE
  simp only [size_eLet, size_eCaseOpt, size_eFind, size_sidEqE, sz_stSess, sz_stResp,
    sz_ieSid, sz_reSid, sz_reSendHon, sz_reTested, sz_reRev, sz_ieFresh, sz_ieTested, sz_ieRev,
    size_v, Expr.size]; omega

@[local simp] private theorem size_sBytes32C :
    (sBytes32C (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) (Γ := Γ)).size = 6 := rfl

@[local simp] private theorem size_sRandom64C :
    (sRandom64C (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) (Γ := Γ)).size = 19 := by
  unfold sRandom64C
  simp only [e2ePureOp, size_bindV, size_sBytes32C, size_v, Comp.size, Expr.size]
  rfl

@[local simp] private theorem size_sDrKey96C :
    (sDrKey96C (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) (Γ := Γ)).size = 27 := by
  unfold sDrKey96C
  simp only [size_bindV, size_sBytes32C, size_v, Comp.size, Expr.size]

@[local simp] private theorem size_sKemKeyGenC :
    (sKemKeyGenC (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) (Γ := Γ)).size = 23 := by
  unfold sKemKeyGenC
  simp only [mkStepAPqxdhHooks, size_bindV, size_sRandom64C, size_cryptoOp_loc, size_v, Comp.size]

@[local simp] private theorem size_findHonestC
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (findHonestC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) ps ik).size =
      ps.size + ik.size + bits S.N_id + 23 := by
  unfold findHonestC
  simp only [size_letV, size_bindV, size_findMV, size_cryptoOp_loc,
    size_pureOp_loc, E2EPureOp.opSize, sz_peIkPk, size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_isAdvRegC (nAdv : ℕ)
    (ak : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (PB 32) (PB 32))))
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (isAdvRegC (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv ak pk).size =
      ak.size + pk.size + bits nAdv + 21 := by
  unfold isAdvRegC
  simp only [size_letV, size_bindV, size_anyMV, size_cryptoOp_loc,
    size_pureOp_loc, E2EPureOp.opSize, size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_isGameSpkC
    (bs : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (isGameSpkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) bs pk).size =
      bs.size + pk.size + bits S.N_spk_tot + 23 := by
  unfold isGameSpkC
  simp only [size_letV, size_bindV, size_anyMV, size_cryptoOp_loc,
    size_pureOp_loc, E2EPureOp.opSize, sz_beSpkPk, size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_isGameOpkC
    (os : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (isGameOpkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) os pk).size =
      os.size + pk.size + bits S.N_opk_tot + 23 := by
  unfold isGameOpkC
  simp only [size_letV, size_bindV, size_anyMV, size_cryptoOp_loc,
    size_pureOp_loc, E2EPureOp.opSize, sz_oePk, size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_koskBundleOkC (nAdv : ℕ)
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) :
    (koskBundleOkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st bundle).size =
      st.size + bundle.size +
        bits S.N_id + bits S.N_spk_tot + bits S.N_opk_tot + 3 * bits nAdv + 249 := by
  unfold koskBundleOkC
  simp only [size_letV, size_bindV, size_caseOptV, size_findHonestC, size_isAdvRegC,
    size_isGameSpkC, size_isGameOpkC, sz_stPrin, sz_stAdv, sz_stSpk, sz_stOpk,
    sz_bndIkB, sz_bndSpkB, sz_bndOpkB, size_orE, size_isSomeE, size_v, Comp.size, Expr.size]
  omega

@[local simp] private theorem size_koskSenderOkC (nAdv : ℕ)
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (koskSenderOkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st ik).size =
      st.size + ik.size + bits S.N_id + bits nAdv + 79 := by
  unfold koskSenderOkC
  simp only [size_letV, size_bindV, size_findHonestC, size_isAdvRegC, sz_stPrin, sz_stAdv,
    size_orE, size_isSomeE, size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_resolveSigPkC
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (resolveSigPkC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) ps ik).size =
      ps.size + ik.size + bits S.N_id + 42 := by
  unfold resolveSigPkC
  simp only [size_letV, size_bindV, size_findHonestC, size_eCaseOpt, sz_peSignPk,
    size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_honestPeerC
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (honestPeerC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) ps ik).size =
      ps.size + ik.size + bits S.N_id + 40 := by
  unfold honestPeerC
  simp only [size_bindV, size_findHonestC, size_eCaseOpt, sz_peCorr, size_v, Comp.size,
    Expr.size]

@[local simp] private theorem size_checkProvC
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) :
    (checkProvC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st bundle).size =
      st.size + bundle.size +
        bits S.N_id + 2 * bits S.N_spk_tot + bits S.N_opk_tot + 157 := by
  unfold checkProvC
  simp only [mkStepAPqxdhHooks, size_letV, size_bindV, size_caseOptV,
    size_anyMV, size_eAny, size_findHonestC, size_cryptoOp_loc, size_pureOp_loc, E2EPureOp.opSize,
    sz_stPrin, sz_stSpk, sz_stOpk,
    sz_bndIkB, sz_bndSpkB, sz_bndPqB, sz_bndOpkB, sz_beSpkPk, sz_bePqPk, sz_oePk,
    size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_optPow8C
    (pk? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32))) :
    (optPow8C (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) pk?).size = pk?.size + 10 := by
  unfold optPow8C
  simp only [size_caseOptV, size_bindV, size_cryptoOp_loc, size_v, Comp.size,
    Expr.size]

@[local simp] private theorem size_partnerC
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInitiatorEntryTy ℓ S))
    (r : Expr (e2eOps ℓ P C K decT encT) Γ (e2eRespEntryTy ℓ S)) :
    (partnerC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) s r).size =
      s.size + r.size + 224 := by
  unfold partnerC
  simp only [mkStepAPqxdhHooks, size_letV, size_bindV, size_optPow8C,
    size_optPb32EqE, size_cryptoOp_loc, size_pureOp_loc, E2EPureOp.opSize,
    sz_hdrIkA, sz_hdrEkA, sz_hdrKemCt,
    sz_ieHdr, sz_reHdr, sz_iePeerIk, sz_reIk, sz_iePeerSpk, sz_reSpk, sz_iePeerOpk, sz_reOpk,
    sz_iePeerPq, sz_rePq, size_v, Comp.size, Expr.size]

@[local simp] private theorem size_partnerRandKeyC
    (rs : Expr (e2eOps ℓ P C K decT encT) Γ (.list (e2eRespEntryTy ℓ S)))
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInitiatorEntryTy ℓ S)) :
    (partnerRandKeyC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) rs s).size =
      rs.size + s.size + bits S.N_recv_tot + 249 := by
  unfold partnerRandKeyC
  simp only [size_letV, size_bindV, size_findMV, size_partnerC, size_optMapE, sz_reRand,
    size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_recordRespC
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (r : Expr (e2eOps ℓ P C K decT encT) Γ (e2eRespEntryTy ℓ S)) :
    (recordRespC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st r).size =
      st.size + r.size + bits S.N_send_tot + 432 := by
  unfold recordRespC
  simp only [size_letV, size_bindV, size_findMV, size_caseOptV, size_partnerC, size_sDrKey96C,
    size_setRespE, size_reSetRandE, sz_stSess, sz_stResp, sz_ieRand, size_v, Comp.size,
    Expr.size]; omega

@[local simp] private theorem size_acceptKeysC
    (ikBSk spkBSk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32))
    (opkBSk? : Expr (e2eOps ℓ P C K decT encT) Γ (.opt (PB 32)))
    (pqspkBSk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 3168))
    (tp rp : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (hdr : Expr (e2eOps ℓ P C K decT encT) Γ hdrT) :
    (acceptKeysC (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) ikBSk spkBSk opkBSk? pqspkBSk tp rp hdr).size =
      ikBSk.size + spkBSk.size + opkBSk?.size + pqspkBSk.size + tp.size + rp.size + hdr.size +
        477 := by
  unfold acceptKeysC
  simp only [mkStepAPqxdhHooks, size_letV, size_bindV, size_caseOptV,
    size_cryptoOp_loc, size_pureOp_loc, E2EPureOp.opSize,
    size_dhNonZeroE, size_dhOptNonZeroE, size_buildSecretsE,
    sz_accTp, sz_accRp, sz_accHdr, sz_accSpkSk, sz_accIkSk, sz_accOpkSk, sz_accPqSk,
    sz_hdrIkA, sz_hdrEkA, sz_hdrOpkId, sz_hdrKemCt, size_v, Comp.size, Expr.size,
    show bits 32 = 6 from rfl, show bits 1568 = 11 from rfl]; omega

/-! ## Per-Branch `.size` Upper Bounds -/

private abbrev armSizeBudget (S : Setup) (nAdv : ℕ) : ℕ :=
  5 * bits S.N_id + 3 * bits S.N_spk_tot + 3 * bits S.N_opk_tot +
    2 * bits S.N_send_tot + 2 * bits S.N_recv_tot + 3 * bits nAdv + 1600

private theorem size_initPrin1KeyB
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (hu : u.size ≤ 4) :
    (initPrin1KeyB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st u).size ≤ 200 + bits S.N_id := by
  unfold initPrin1KeyB
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_bindV, size_finValE, size_natEqE,
    size_sBytes32C, size_cryptoOp_loc, size_setPrinE, sz_stPrin, sz_rsE, sz_rNoneE, sz_rInitPrinE,
    size_v, Comp.size, Expr.size]; omega

private theorem size_corruptB
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (hu : u.size ≤ 4) :
    (corruptB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st u).size ≤ 200 + 2 * bits S.N_id := by
  unfold corruptB
  simp only [size_letV, size_caseOptV, size_eFind, size_eMap, size_finValE, size_natEqE,
    size_peSetCorrE, size_setPrinE, sz_stPrin, sz_peSec0, sz_peSecSign, sz_rsE, sz_rNoneE,
    sz_rCorrE, size_v, Comp.size, Expr.size]; omega

private theorem size_genSpkB
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (hu : u.size ≤ 4) (hj : j.size ≤ 4) :
    (genSpkB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st u j).size ≤
      310 + bits S.N_id + bits S.N_spk_tot := by
  unfold genSpkB
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_caseOptV, size_eFind, size_bindV,
    size_finValE, size_nat2EqE, size_natEqE, size_sBytes32C, size_sRandom64C, size_sKemKeyGenC,
    size_cryptoOp_loc, size_pureOp_loc, E2EPureOp.opSize, size_encECWideE, size_encKEME, size_setSpkE,
    sz_stSpk, sz_stPrin, sz_peSecSign, sz_peIkPk, sz_rsE, sz_rNoneE, sz_rBundleE,
    size_v, Comp.size, Expr.size]; omega

private theorem size_genOpkB
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (o : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk))
    (hu : u.size ≤ 4) (hj : j.size ≤ 4) (ho : o.size ≤ 4) :
    (genOpkB (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st u j o).size ≤
      200 + bits S.N_opk_tot := by
  unfold genOpkB
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_bindV, size_finValE, size_nat3EqE,
    size_sBytes32C, size_cryptoOp_loc, size_setOpkE, sz_stOpk, sz_rsE, sz_rNoneE, sz_rPkE,
    size_v, Comp.size, Expr.size]; omega

private theorem size_initiateC (nAdv : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hsid : sid.size ≤ 12) (hu : u.size ≤ 4) (hbnd : bundle.size ≤ 4) :
    (initiateC (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st sid u bundle).size ≤
      6 * bits S.N_id + 3 * bits S.N_spk_tot + 2 * bits S.N_opk_tot +
        bits S.N_send_tot + bits S.N_recv_tot + 3 * bits nAdv + 2600 := by
  unfold initiateC
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_caseOptV, size_eFind,
    size_bindV, size_eCaseOpt, size_cryptoOp_loc,
    size_finValE, size_sidEqE, size_natEqE,
    size_koskBundleOkC, size_sBytes32C, size_resolveSigPkC, size_encECWideE, size_encKEME,
    size_buildSecretsE, size_honestPeerC, size_checkProvC, size_optMapE, size_isSomeE,
    size_partnerRandKeyC, size_sDrKey96C, size_findHonestC, size_setSessE, size_ieSetRandE,
    sz_stSess, sz_stPrin, sz_stResp, sz_ieSid, sz_peSec0, sz_peIkPk,
    sz_bndIkB, sz_bndSpkB, sz_bndSpkSig, sz_bndPqB, sz_bndPqSig, sz_bndOpkB, sz_bndSpkId,
    sz_bndPqId, sz_rsE, sz_rNoneE, sz_rInitUnfreshE, sz_rHdrE,
    size_v, Comp.size, Expr.size]; omega

private theorem size_initiateOpkB (nAdv : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (i : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_opk))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hu : u.size ≤ 4) (hi : i.size ≤ 4) (hbnd : bundle.size ≤ 4) :
    (initiateOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st u i bundle).size ≤
      6 * bits S.N_id + 3 * bits S.N_spk_tot + 2 * bits S.N_opk_tot +
        bits S.N_send_tot + bits S.N_recv_tot + 3 * bits nAdv + 2650 := by
  unfold initiateOpkB
  have hinit := size_initiateC (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nAdv st (.inl (.pair u i)) u bundle
    (by simp only [Expr.size]; omega) hu hbnd
  simp only [size_isNoneE, sz_bndOpkB, sz_rsE, sz_rNoneE, size_v, Comp.size]
  omega

private theorem size_initiateNoOpkB (nAdv : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (i : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_no_opk))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hu : u.size ≤ 4) (hi : i.size ≤ 4) (hbnd : bundle.size ≤ 4) :
    (initiateNoOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st u i bundle).size ≤
      6 * bits S.N_id + 3 * bits S.N_spk_tot + 2 * bits S.N_opk_tot +
        bits S.N_send_tot + bits S.N_recv_tot + 3 * bits nAdv + 2650 := by
  unfold initiateNoOpkB
  have hinit := size_initiateC (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nAdv st (.inr (.inl (.pair u i))) u bundle
    (by simp only [Expr.size]; omega) hu hbnd
  simp only [size_isSomeE, sz_bndOpkB, sz_rsE, sz_rNoneE, size_v, Comp.size]
  omega

private theorem size_acceptOpkB (nAdv : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (o : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk))
    (hdr : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (hk : k.size ≤ 4) (hj : j.size ≤ 4) (ho : o.size ≤ 4) (hhdr : hdr.size ≤ 5) :
    (acceptOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st k j o hdr).size ≤
      3 * bits S.N_id + bits S.N_spk_tot + 3 * bits S.N_opk_tot +
        bits S.N_send_tot + bits S.N_recv_tot + bits nAdv + 2400 := by
  unfold acceptOpkB
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_bindV, size_caseOptV, size_eFind,
    size_eMap, size_eCaseOpt, size_pureOp_loc, E2EPureOp.opSize,
    size_finValE, size_optPu32EqE, size_natEqE,
    size_nat3EqE, size_nat2EqE, size_koskSenderOkC, size_checkSeenE, size_acceptKeysC,
    size_findHonestC, size_recordRespC, size_setAcceptOpkE, size_oeSetConsE, size_isSomeE,
    sz_hdrSpkId, sz_hdrPqId, sz_hdrOpkId, sz_hdrIkA, sz_hdrEkA,
    sz_stUsedOpk, sz_stPrin, sz_stSpk, sz_stOpk, sz_stSeen,
    sz_oeCons, sz_peSec0, sz_beSpkSk, sz_oeSk, sz_bePqSk, sz_peIkPk, sz_beSpkPk, sz_oePk,
    sz_bePqPk, sz_rsE, sz_rNoneE, sz_rDrKeyE, sz_rAcceptFreshE,
    size_v, Comp.size, Expr.size, show bits 32 = 6 from rfl]; omega

private theorem size_acceptNoOpkB (nAdv : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (l : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_no_opk))
    (hdr : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (hk : k.size ≤ 4) (hj : j.size ≤ 4) (hl : l.size ≤ 4) (hhdr : hdr.size ≤ 5) :
    (acceptNoOpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv st k j l hdr).size ≤
      3 * bits S.N_id + bits S.N_spk_tot +
        bits S.N_send_tot + 2 * bits S.N_recv_tot + bits nAdv + 2300 := by
  have hno : bits S.N_no_opk_tot ≤ bits S.N_recv_tot :=
    ReductionDsl.bits_mono (by unfold Setup.N_recv_tot; omega)
  unfold acceptNoOpkB
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_bindV, size_caseOptV, size_eFind,
    size_eCaseOpt, size_pureOp_loc, E2EPureOp.opSize,
    size_finValE, size_isNoneE, size_natEqE, size_nat3EqE,
    size_nat2EqE, size_koskSenderOkC, size_checkSeenE, size_acceptKeysC, size_findHonestC,
    size_recordRespC, size_setAcceptNoOpkE, size_isSomeE,
    sz_hdrSpkId, sz_hdrPqId, sz_hdrOpkId, sz_hdrIkA, sz_hdrEkA,
    sz_stUsedNoOpk, sz_stPrin, sz_stSpk, sz_stSeen,
    sz_peSec0, sz_beSpkSk, sz_bePqSk, sz_peIkPk, sz_beSpkPk, sz_bePqPk,
    sz_rsE, sz_rNoneE, sz_rDrKeyE, sz_rAcceptFreshE,
    size_v, Comp.size, Expr.size, show bits 32 = 6 from rfl]; omega

private theorem size_testB
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (hsid : sid.size ≤ 4) :
    (testB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sid).size ≤
      3 * bits S.N_send_tot + 3 * bits S.N_recv_tot + 3800 := by
  unfold testB
  simp only [size_letV, size_isTestableE, size_caseOptV, size_eFind, size_eMap, size_sidEqE,
    size_reSetTestedE, size_ieSetTestedE, size_setRespE, size_setSessE,
    sz_stSess, sz_stResp, sz_stSecb, sz_ieSid, sz_reSid, sz_reReal, sz_reRand, sz_ieReal,
    sz_ieRand, sz_rsE, sz_rNoneE, sz_rDrKeyE, size_v, Comp.size, Expr.size]; omega

private theorem size_ro1KeyRealB
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sec : Expr (e2eOps ℓ P C K decT encT) Γ (PB 192)) (hsec : sec.size ≤ 4) :
    (ro1KeyRealB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sec).size ≤ 30 := by
  unfold ro1KeyRealB
  simp only [size_bindV, size_cryptoOp_loc, sz_rsE, sz_rDrKeyE, size_v, Comp.size]; omega

private theorem size_revealDh1KeyRealB
    (st : Var Γ (e2eKeyIndStateTy ℓ S)) :
    (revealDh1KeyRealB (S := S) (O := e2eOps ℓ P C K decT encT)
      (I := stepAIface ℓ I₀) st).size ≤ 10 := by
  unfold revealDh1KeyRealB
  simp only [sz_rsE, sz_rNoneE, size_v, Comp.size]; omega

private theorem size_revealB
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (hsid : sid.size ≤ 4) :
    (revealB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sid).size ≤
      2 * bits S.N_send_tot + 2 * bits S.N_recv_tot + 2600 := by
  unfold revealB
  simp only [size_letV, size_caseOptV, size_eFind, size_eMap, size_sidEqE,
    size_reSetRevE, size_ieSetRevE, size_setRespE, size_setSessE,
    sz_stSess, sz_stResp, sz_ieSid, sz_reSid, sz_reTested, sz_reReal, sz_ieTested, sz_ieReal,
    sz_rsE, sz_rNoneE, sz_rDrKeyE, size_v, Comp.size, Expr.size]; omega

private theorem size_registerB
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) (hsk : sk.size ≤ 4) :
    (registerB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st sk).size ≤ 140 := by
  unfold registerB
  simp only [size_letV, size_bindV, size_natEqE, size_pureOp_loc,
    E2EPureOp.opSize, size_cryptoOp_loc, size_setAdvE, sz_stAdv, sz_rsE, sz_rNoneE, sz_rPkE, size_v,
    Comp.size, Expr.size, show bits 32 = 6 from rfl]; omega

private theorem size_revealSpkB
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (hu : u.size ≤ 4) (hj : j.size ≤ 4) :
    (revealSpkB (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) st u j).size ≤
      200 + 2 * bits S.N_spk_tot := by
  unfold revealSpkB
  simp only [size_letV, size_caseOptV, size_eFind, size_eMap, size_finValE, size_nat2EqE,
    size_beSetRevE, size_setSpkE, sz_stSpk, sz_beSpkSk, sz_rsE, sz_rNoneE, sz_rSpkSkE,
    size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_checkSeenEFuel (nFuel : ℕ)
    (used : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat (.prod PU32 (.prod PU32 (PB 32))))))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (pqspkId spkId : Expr (e2eOps ℓ P C K decT encT) Γ PU32)
    (ekAPk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (checkSeenEFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel used k pqspkId spkId ekAPk).size =
      used.size + k.size + pqspkId.size + spkId.size + ekAPk.size +
        bits (min nFuel S.N_recv_tot) + 60 := by
  unfold checkSeenEFuel
  simp only [size_pureOp_loc, E2EPureOp.opSize,
    size_eLet, size_eAny, size_v, Expr.size]; omega

@[local simp] private theorem size_isTestableEFuel (nFuel : ℕ)
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (isTestableEFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st sid).size =
      st.size + sid.size + bits (min nFuel S.N_send_tot) + bits (min nFuel S.N_recv_tot) + 1130 := by
  unfold isTestableEFuel
  simp only [size_eLet, size_eCaseOpt, size_eFind, size_sidEqE, sz_stSess, sz_stResp,
    sz_ieSid, sz_reSid, sz_reSendHon, sz_reTested, sz_reRev, sz_ieFresh, sz_ieTested, sz_ieRev,
    size_v, Expr.size]; omega

@[local simp] private theorem size_findHonestCFuel (nFuel : ℕ)
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (findHonestCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel ps ik).size =
      ps.size + ik.size + bits (min nFuel S.N_id) + 23 := by
  unfold findHonestCFuel
  simp only [size_letV, size_bindV, size_findMV, size_cryptoOp_loc,
    size_pureOp_loc, E2EPureOp.opSize, sz_peIkPk, size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_isGameSpkCFuel (nFuel : ℕ)
    (bs : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat .nat) e2eSpkBundleEntryTy)))
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (isGameSpkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel bs pk).size =
      bs.size + pk.size + bits (min nFuel S.N_spk_tot) + 23 := by
  unfold isGameSpkCFuel
  simp only [size_letV, size_bindV, size_anyMV, size_cryptoOp_loc,
    size_pureOp_loc, E2EPureOp.opSize, sz_beSpkPk, size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_isGameOpkCFuel (nFuel : ℕ)
    (os : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (.prod .nat (.prod .nat .nat)) e2eOpkEntryTy)))
    (pk : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (isGameOpkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel os pk).size =
      os.size + pk.size + bits (min nFuel S.N_opk_tot) + 23 := by
  unfold isGameOpkCFuel
  simp only [size_letV, size_bindV, size_anyMV, size_cryptoOp_loc,
    size_pureOp_loc, E2EPureOp.opSize, sz_oePk, size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_koskBundleOkCFuel (nFuel : ℕ)
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) :
    (koskBundleOkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st bundle).size =
      st.size + bundle.size +
        bits (min nFuel S.N_id) + bits (min nFuel S.N_spk_tot) +
        bits (min nFuel S.N_opk_tot) + 3 * bits nFuel + 249 := by
  unfold koskBundleOkCFuel
  simp only [size_letV, size_bindV, size_caseOptV, size_findHonestCFuel, size_isAdvRegC,
    size_isGameSpkCFuel, size_isGameOpkCFuel, sz_stPrin, sz_stAdv, sz_stSpk, sz_stOpk,
    sz_bndIkB, sz_bndSpkB, sz_bndOpkB, size_orE, size_isSomeE, size_v, Comp.size, Expr.size]
  omega

@[local simp] private theorem size_koskSenderOkCFuel (nFuel : ℕ)
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (koskSenderOkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st ik).size =
      st.size + ik.size + bits (min nFuel S.N_id) + bits nFuel + 79 := by
  unfold koskSenderOkCFuel
  simp only [size_letV, size_bindV, size_findHonestCFuel, size_isAdvRegC, sz_stPrin, sz_stAdv,
    size_orE, size_isSomeE, size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_resolveSigPkCFuel (nFuel : ℕ)
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (resolveSigPkCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel ps ik).size =
      ps.size + ik.size + bits (min nFuel S.N_id) + 42 := by
  unfold resolveSigPkCFuel
  simp only [size_letV, size_bindV, size_findHonestCFuel, size_eCaseOpt, sz_peSignPk,
    size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_honestPeerCFuel (nFuel : ℕ)
    (ps : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod .nat e2ePrincipalEntryTy)))
    (ik : Expr (e2eOps ℓ P C K decT encT) Γ (PB 32)) :
    (honestPeerCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel ps ik).size =
      ps.size + ik.size + bits (min nFuel S.N_id) + 40 := by
  unfold honestPeerCFuel
  simp only [size_bindV, size_findHonestCFuel, size_eCaseOpt, sz_peCorr, size_v, Comp.size,
    Expr.size]

@[local simp] private theorem size_checkProvCFuel (nFuel : ℕ)
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT) :
    (checkProvCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st bundle).size =
      st.size + bundle.size +
        bits (min nFuel S.N_id) + 2 * bits (min nFuel S.N_spk_tot) +
        bits (min nFuel S.N_opk_tot) + 157 := by
  unfold checkProvCFuel
  simp only [mkStepAPqxdhHooks, size_letV, size_bindV, size_caseOptV,
    size_anyMV, size_eAny, size_findHonestCFuel, size_cryptoOp_loc, size_pureOp_loc, E2EPureOp.opSize,
    sz_stPrin, sz_stSpk, sz_stOpk,
    sz_bndIkB, sz_bndSpkB, sz_bndPqB, sz_bndOpkB, sz_beSpkPk, sz_bePqPk, sz_oePk,
    size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_partnerRandKeyCFuel (nFuel : ℕ)
    (rs : Expr (e2eOps ℓ P C K decT encT) Γ (.list (e2eRespEntryTy ℓ S)))
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInitiatorEntryTy ℓ S)) :
    (partnerRandKeyCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel rs s).size =
      rs.size + s.size + bits (min nFuel S.N_recv_tot) + 249 := by
  unfold partnerRandKeyCFuel
  simp only [size_letV, size_bindV, size_findMV, size_partnerC, size_optMapE, sz_reRand,
    size_v, Comp.size, Expr.size]; omega

@[local simp] private theorem size_recordRespCFuel (nFuel : ℕ)
    (st : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (r : Expr (e2eOps ℓ P C K decT encT) Γ (e2eRespEntryTy ℓ S)) :
    (recordRespCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st r).size =
      st.size + r.size + bits (min nFuel S.N_send_tot) + 432 := by
  unfold recordRespCFuel
  simp only [size_letV, size_bindV, size_findMV, size_caseOptV, size_partnerC, size_sDrKey96C,
    size_setRespE, size_reSetRandE, sz_stSess, sz_stResp, sz_ieRand, size_v, Comp.size,
    Expr.size]; omega

private theorem size_initPrin1KeyBFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (hu : u.size ≤ 4) :
    (initPrin1KeyBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st u).size ≤
      200 + bits (min nFuel S.N_id) := by
  unfold initPrin1KeyBFuel
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_bindV, size_finValE, size_natEqE,
    size_sBytes32C, size_cryptoOp_loc, size_setPrinE, sz_stPrin, sz_rsE, sz_rNoneE, sz_rInitPrinE,
    size_v, Comp.size, Expr.size]; omega

private theorem size_corruptBFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id)) (hu : u.size ≤ 4) :
    (corruptBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st u).size ≤
      200 + 2 * bits (min nFuel S.N_id) := by
  unfold corruptBFuel
  simp only [size_letV, size_caseOptV, size_eFind, size_eMap, size_finValE, size_natEqE,
    size_peSetCorrE, size_setPrinE, sz_stPrin, sz_peSec0, sz_peSecSign, sz_rsE, sz_rNoneE,
    sz_rCorrE, size_v, Comp.size, Expr.size]; omega

private theorem size_genSpkBFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (hu : u.size ≤ 4) (hj : j.size ≤ 4) :
    (genSpkBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st u j).size ≤
      310 + bits (min nFuel S.N_id) + bits (min nFuel S.N_spk_tot) := by
  unfold genSpkBFuel
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_caseOptV, size_eFind, size_bindV,
    size_finValE, size_nat2EqE, size_natEqE, size_sBytes32C, size_sRandom64C, size_sKemKeyGenC,
    size_cryptoOp_loc, size_pureOp_loc, E2EPureOp.opSize, size_encECWideE, size_encKEME, size_setSpkE,
    sz_stSpk, sz_stPrin, sz_peSecSign, sz_peIkPk, sz_rsE, sz_rNoneE, sz_rBundleE,
    size_v, Comp.size, Expr.size]; omega

private theorem size_genOpkBFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (o : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk))
    (hu : u.size ≤ 4) (hj : j.size ≤ 4) (ho : o.size ≤ 4) :
    (genOpkBFuel (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st u j o).size ≤
      200 + bits (min nFuel S.N_opk_tot) := by
  unfold genOpkBFuel
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_bindV, size_finValE, size_nat3EqE,
    size_sBytes32C, size_cryptoOp_loc, size_setOpkE, sz_stOpk, sz_rsE, sz_rNoneE, sz_rPkE,
    size_v, Comp.size, Expr.size]; omega

private theorem size_initiateCFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hsid : sid.size ≤ 12) (hu : u.size ≤ 4) (hbnd : bundle.size ≤ 4) :
    (initiateCFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st sid u bundle).size ≤
      6 * bits (min nFuel S.N_id) + 3 * bits (min nFuel S.N_spk_tot) +
        2 * bits (min nFuel S.N_opk_tot) + bits (min nFuel S.N_send_tot) +
        bits (min nFuel S.N_recv_tot) + 3 * bits nFuel + 2600 := by
  unfold initiateCFuel
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_caseOptV, size_eFind,
    size_bindV, size_eCaseOpt, size_cryptoOp_loc,
    size_finValE, size_sidEqE, size_natEqE,
    size_koskBundleOkCFuel, size_sBytes32C, size_resolveSigPkCFuel, size_encECWideE, size_encKEME,
    size_buildSecretsE, size_honestPeerCFuel, size_checkProvCFuel, size_optMapE, size_isSomeE,
    size_partnerRandKeyCFuel, size_sDrKey96C, size_findHonestCFuel, size_setSessE, size_ieSetRandE,
    sz_stSess, sz_stPrin, sz_stResp, sz_ieSid, sz_peSec0, sz_peIkPk,
    sz_bndIkB, sz_bndSpkB, sz_bndSpkSig, sz_bndPqB, sz_bndPqSig, sz_bndOpkB, sz_bndSpkId,
    sz_bndPqId, sz_rsE, sz_rNoneE, sz_rInitUnfreshE, sz_rHdrE,
    size_v, Comp.size, Expr.size]; omega

private theorem size_initiateOpkBFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (i : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_opk))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hu : u.size ≤ 4) (hi : i.size ≤ 4) (hbnd : bundle.size ≤ 4) :
    (initiateOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st u i bundle).size ≤
      6 * bits (min nFuel S.N_id) + 3 * bits (min nFuel S.N_spk_tot) +
        2 * bits (min nFuel S.N_opk_tot) + bits (min nFuel S.N_send_tot) +
        bits (min nFuel S.N_recv_tot) + 3 * bits nFuel + 2650 := by
  unfold initiateOpkBFuel
  have hinit := size_initiateCFuel (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nFuel st (.inl (.pair u i)) u bundle
    (by simp only [Expr.size]; omega) hu hbnd
  simp only [size_isNoneE, sz_bndOpkB, sz_rsE, sz_rNoneE, size_v, Comp.size]
  omega

private theorem size_initiateNoOpkBFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (i : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_send_no_opk))
    (bundle : Expr (e2eOps ℓ P C K decT encT) Γ bundleT)
    (hu : u.size ≤ 4) (hi : i.size ≤ 4) (hbnd : bundle.size ≤ 4) :
    (initiateNoOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st u i bundle).size ≤
      6 * bits (min nFuel S.N_id) + 3 * bits (min nFuel S.N_spk_tot) +
        2 * bits (min nFuel S.N_opk_tot) + bits (min nFuel S.N_send_tot) +
        bits (min nFuel S.N_recv_tot) + 3 * bits nFuel + 2650 := by
  unfold initiateNoOpkBFuel
  have hinit := size_initiateCFuel (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nFuel st (.inr (.inl (.pair u i))) u bundle
    (by simp only [Expr.size]; omega) hu hbnd
  simp only [size_isSomeE, sz_bndOpkB, sz_rsE, sz_rNoneE, size_v, Comp.size]
  omega

private theorem size_acceptOpkBFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (o : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_opk))
    (hdr : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (hk : k.size ≤ 4) (hj : j.size ≤ 4) (ho : o.size ≤ 4) (hhdr : hdr.size ≤ 5) :
    (acceptOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st k j o hdr).size ≤
      3 * bits (min nFuel S.N_id) + bits (min nFuel S.N_spk_tot) +
        3 * bits (min nFuel S.N_opk_tot) + bits (min nFuel S.N_send_tot) +
        bits (min nFuel S.N_recv_tot) + bits nFuel + 2400 := by
  unfold acceptOpkBFuel
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_bindV, size_caseOptV, size_eFind,
    size_eMap, size_eCaseOpt, size_pureOp_loc, E2EPureOp.opSize,
    size_finValE, size_optPu32EqE, size_natEqE,
    size_nat3EqE, size_nat2EqE, size_koskSenderOkCFuel, size_checkSeenEFuel, size_acceptKeysC,
    size_findHonestCFuel, size_recordRespCFuel, size_setAcceptOpkE, size_oeSetConsE, size_isSomeE,
    sz_hdrSpkId, sz_hdrPqId, sz_hdrOpkId, sz_hdrIkA, sz_hdrEkA,
    sz_stUsedOpk, sz_stPrin, sz_stSpk, sz_stOpk, sz_stSeen,
    sz_oeCons, sz_peSec0, sz_beSpkSk, sz_oeSk, sz_bePqSk, sz_peIkPk, sz_beSpkPk, sz_oePk,
    sz_bePqPk, sz_rsE, sz_rNoneE, sz_rDrKeyE, sz_rAcceptFreshE,
    size_v, Comp.size, Expr.size, show bits 32 = 6 from rfl]; omega

private theorem size_acceptNoOpkBFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (k : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (l : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_no_opk))
    (hdr : Expr (e2eOps ℓ P C K decT encT) Γ hdrT)
    (hk : k.size ≤ 4) (hj : j.size ≤ 4) (hl : l.size ≤ 4) (hhdr : hdr.size ≤ 5) :
    (acceptNoOpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st k j l hdr).size ≤
      3 * bits (min nFuel S.N_id) + bits (min nFuel S.N_spk_tot) +
        bits (min nFuel S.N_send_tot) + 2 * bits (min nFuel S.N_recv_tot) +
        bits nFuel + 2300 := by
  have hno : bits (min nFuel S.N_no_opk_tot) ≤ bits (min nFuel S.N_recv_tot) :=
    _root_.ReductionDsl.bits_mono (by unfold Setup.N_recv_tot; omega)
  unfold acceptNoOpkBFuel
  simp only [mkStepAPqxdhHooks, size_letV, size_eAny, size_bindV, size_caseOptV, size_eFind,
    size_eCaseOpt, size_pureOp_loc, E2EPureOp.opSize,
    size_finValE, size_isNoneE, size_natEqE, size_nat3EqE,
    size_nat2EqE, size_koskSenderOkCFuel, size_checkSeenEFuel, size_acceptKeysC, size_findHonestCFuel,
    size_recordRespCFuel, size_setAcceptNoOpkE, size_isSomeE,
    sz_hdrSpkId, sz_hdrPqId, sz_hdrOpkId, sz_hdrIkA, sz_hdrEkA,
    sz_stUsedNoOpk, sz_stPrin, sz_stSpk, sz_stSeen,
    sz_peSec0, sz_beSpkSk, sz_bePqSk, sz_peIkPk, sz_beSpkPk, sz_bePqPk,
    sz_rsE, sz_rNoneE, sz_rDrKeyE, sz_rAcceptFreshE,
    size_v, Comp.size, Expr.size, show bits 32 = 6 from rfl]; omega

private theorem size_testBFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (hsid : sid.size ≤ 4) :
    (testBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st sid).size ≤
      3 * bits (min nFuel S.N_send_tot) + 3 * bits (min nFuel S.N_recv_tot) + 3800 := by
  unfold testBFuel
  simp only [size_letV, size_isTestableEFuel, size_caseOptV, size_eFind, size_eMap, size_sidEqE,
    size_reSetTestedE, size_ieSetTestedE, size_setRespE, size_setSessE,
    sz_stSess, sz_stResp, sz_stSecb, sz_ieSid, sz_reSid, sz_reReal, sz_reRand, sz_ieReal,
    sz_ieRand, sz_rsE, sz_rNoneE, sz_rDrKeyE, size_v, Comp.size, Expr.size]; omega

private theorem size_revealBFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (sid : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) (hsid : sid.size ≤ 4) :
    (revealBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st sid).size ≤
      2 * bits (min nFuel S.N_send_tot) + 2 * bits (min nFuel S.N_recv_tot) + 2600 := by
  unfold revealBFuel
  simp only [size_letV, size_caseOptV, size_eFind, size_eMap, size_sidEqE,
    size_reSetRevE, size_ieSetRevE, size_setRespE, size_setSessE,
    sz_stSess, sz_stResp, sz_ieSid, sz_reSid, sz_reTested, sz_reReal, sz_ieTested, sz_ieReal,
    sz_rsE, sz_rNoneE, sz_rDrKeyE, size_v, Comp.size, Expr.size]; omega

private theorem size_revealSpkBFuel (nFuel : ℕ)
    (st : Var Γ (e2eKeyIndStateTy ℓ S))
    (u : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (j : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv))
    (hu : u.size ≤ 4) (hj : j.size ≤ 4) :
    (revealSpkBFuel (S := S) (I := stepAIface ℓ I₀)
      (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nFuel st u j).size ≤
      200 + 2 * bits (min nFuel S.N_spk_tot) := by
  unfold revealSpkBFuel
  simp only [size_letV, size_caseOptV, size_eFind, size_eMap, size_finValE, size_nat2EqE,
    size_beSetRevE, size_setSpkE, sz_stSpk, sz_beSpkSk, sz_rsE, sz_rNoneE, sz_rSpkSkE,
    size_v, Comp.size, Expr.size]; omega

end SizeLemmas

private theorem size_caseSum_ub {Sig : _root_.ReductionDsl.Sig} {O : Ops Sig}
    {ι : Type} {T : OracleSpec ι} {I : Iface Sig T}
    {Γ : List (Ty Sig)} {α β υ : Ty Sig}
    (e : Expr O Γ (.sum α β)) (l : Comp O I (α :: Γ) υ) (r : Comp O I (β :: Γ) υ)
    (B1 B2 : ℕ) {B : ℕ} (hl : l.size ≤ B1) (hr : r.size ≤ B2) (hB : e.size + B1 + B2 + 1 ≤ B) :
    (Comp.caseSum e l r).size ≤ B := by
  simp only [Comp.size]; omega

private theorem size_caseSum_var_le {Sig : _root_.ReductionDsl.Sig} {O : Ops Sig}
    {ι : Type} {T : OracleSpec ι} {I : Iface Sig T}
    {Γ : List (Ty Sig)} {α β υ : Ty Sig}
    (v0 : Var Γ (.sum α β)) (l : Comp O I (α :: Γ) υ) (r : Comp O I (β :: Γ) υ)
    (B1 B2 : ℕ) (hl : l.size ≤ B1) (hr : r.size ≤ B2) :
    (Comp.caseSum (.var v0) l r).size ≤ B1 + B2 + 2 := by
  simp only [Comp.size, Expr.size]; omega

/-- Compositional `Comp.size` bound for `pqxdh1KeyRealStepC`. -/
theorem size_pqxdh1KeyRealStepC (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)) :
    (pqxdh1KeyRealStepC ℓ S P C K decT encT I₀ nAdv stE qE).size ≤
      stE.size + qE.size + pqxdh1KeyRealStepSize S nAdv := by
  unfold pqxdh1KeyRealStepC pqxdh1KeyRealStepG
  have hbody :
      (pqxdh1KeyRealBodyG (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv
        (Γ := e2eKeyIndStateTy ℓ S :: .prod (e2eKeyIndStateTy ℓ S) (keyIndQT S) :: Γ)
        .zero (.snd (.var (.succ .zero)))).size ≤
        pqxdh1KeyRealStepSize S nAdv - 20 := by
    unfold pqxdh1KeyRealBodyG
    refine size_caseSum_ub _ _ _ _ _
      (size_initPrin1KeyB _ _ (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_corruptB _ _ (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_genSpkB _ _ _ (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_genOpkB _ _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_initiateOpkB _ _ _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_initiateNoOpkB _ _ _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_acceptOpkB _ _ _ _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_acceptNoOpkB _ _ _ _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_testB _ _ (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_ro1KeyRealB _ _ (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_revealDh1KeyRealB _)
      (size_caseSum_var_le _ _ _ _ _
        (size_revealB _ _ (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_registerB _ _ (by simp only [Expr.size]; omega))
        (size_revealSpkB _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)))))))))))))) ?_
    simp only [Expr.size, pqxdh1KeyRealStepSize]
    omega
  simp only [Comp.size, Expr.size, pqxdh1KeyRealStepSize] at hbody ⊢
  omega

theorem pqxdh1KeyRealStepClampedSize_le_bits (S : Setup) {nAdv B : ℕ} (hle : nAdv ≤ B) :
    pqxdh1KeyRealStepClampedSize S nAdv ≤ 76 * bits B + 20000 := by
  have hid : bits (min nAdv S.N_id) ≤ bits B :=
    _root_.ReductionDsl.bits_mono ((Nat.min_le_left _ _).trans hle)
  have hspk : bits (min nAdv S.N_spk_tot) ≤ bits B :=
    _root_.ReductionDsl.bits_mono ((Nat.min_le_left _ _).trans hle)
  have hopk : bits (min nAdv S.N_opk_tot) ≤ bits B :=
    _root_.ReductionDsl.bits_mono ((Nat.min_le_left _ _).trans hle)
  have hsend : bits (min nAdv S.N_send_tot) ≤ bits B :=
    _root_.ReductionDsl.bits_mono ((Nat.min_le_left _ _).trans hle)
  have hrecv : bits (min nAdv S.N_recv_tot) ≤ bits B :=
    _root_.ReductionDsl.bits_mono ((Nat.min_le_left _ _).trans hle)
  have hadv : bits nAdv ≤ bits B := _root_.ReductionDsl.bits_mono hle
  unfold pqxdh1KeyRealStepClampedSize
  omega

theorem pqxdhTestStepSize_le_bits (S : Setup) {nFuel B : ℕ} (hle : nFuel ≤ B) :
    pqxdhTestStepSize S nFuel ≤ 6 * bits B + 3850 := by
  have hsend : bits (min nFuel S.N_send_tot) ≤ bits B :=
    _root_.ReductionDsl.bits_mono ((Nat.min_le_left _ _).trans hle)
  have hrecv : bits (min nFuel S.N_recv_tot) ≤ bits B :=
    _root_.ReductionDsl.bits_mono ((Nat.min_le_left _ _).trans hle)
  unfold pqxdhTestStepSize
  omega

theorem pqxdhRevealSpkStepSize_le_bits (S : Setup) {nFuel B : ℕ} (hle : nFuel ≤ B) :
    pqxdhRevealSpkStepSize S nFuel ≤ 2 * bits B + 250 := by
  have hspk : bits (min nFuel S.N_spk_tot) ≤ bits B :=
    _root_.ReductionDsl.bits_mono ((Nat.min_le_left _ _).trans hle)
  unfold pqxdhRevealSpkStepSize
  omega

theorem size_pqxdh1KeyRealStepClampedC (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)) :
    (pqxdh1KeyRealStepClampedC ℓ S P C K decT encT I₀ nAdv stE qE).size ≤
      stE.size + qE.size + pqxdh1KeyRealStepClampedSize S nAdv := by
  unfold pqxdh1KeyRealStepClampedC pqxdh1KeyRealStepClampedG
  have hbody :
      (pqxdh1KeyRealBodyClampedG (mkStepAPqxdhHooks ℓ P C K decT encT I₀) nAdv
        (Γ := e2eKeyIndStateTy ℓ S :: .prod (e2eKeyIndStateTy ℓ S) (keyIndQT S) :: Γ)
        .zero (.snd (.var (.succ .zero)))).size ≤
        pqxdh1KeyRealStepClampedSize S nAdv - 20 := by
    unfold pqxdh1KeyRealBodyClampedG
    refine size_caseSum_ub _ _ _ _ _
      (size_initPrin1KeyBFuel nAdv _ _ (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_corruptBFuel nAdv _ _ (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_genSpkBFuel nAdv _ _ _ (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_genOpkBFuel nAdv _ _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_initiateOpkBFuel nAdv _ _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_initiateNoOpkBFuel nAdv _ _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_acceptOpkBFuel nAdv _ _ _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_acceptNoOpkBFuel nAdv _ _ _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_testBFuel nAdv _ _ (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_ro1KeyRealB _ _ (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_revealDh1KeyRealB _)
      (size_caseSum_var_le _ _ _ _ _
        (size_revealBFuel nAdv _ _ (by simp only [Expr.size]; omega))
      (size_caseSum_var_le _ _ _ _ _
        (size_registerB _ _ (by simp only [Expr.size]; omega))
        (size_revealSpkBFuel nAdv _ _ _
          (by simp only [Expr.size]; omega)
          (by simp only [Expr.size]; omega)))))))))))))) ?_
    simp only [Expr.size, pqxdh1KeyRealStepClampedSize]
    omega
  simp only [Comp.size, Expr.size, pqxdh1KeyRealStepClampedSize] at hbody ⊢
  omega

theorem size_pqxdhTestStepC (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)) :
    (pqxdhTestStepC ℓ S P C K decT encT I₀ nFuel stE sidE).size ≤
      stE.size + sidE.size + pqxdhTestStepSize S nFuel := by
  unfold pqxdhTestStepC pqxdhTestStepG
  have hbody := size_testBFuel (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nFuel
    (Γ := e2eKeyIndStateTy ℓ S :: .prod (e2eKeyIndStateTy ℓ S) (sidT S) :: Γ)
    .zero (.snd (.var (.succ .zero))) (by simp only [Expr.size]; omega)
  simp only [Comp.size, Expr.size, pqxdhTestStepSize] at hbody ⊢
  omega

theorem size_pqxdhRevealSpkStepC (ℓ : ℕ) (S : Setup) {Pt : Type}
    (P : Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nFuel : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (uE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_id))
    (jE : Expr (e2eOps ℓ P C K decT encT) Γ (FinT S.N_recv)) :
    (pqxdhRevealSpkStepC ℓ S P C K decT encT I₀ nFuel stE uE jE).size ≤
      stE.size + uE.size + jE.size + pqxdhRevealSpkStepSize S nFuel := by
  unfold pqxdhRevealSpkStepC pqxdhRevealSpkStepG
  have hbody := size_revealSpkBFuel (S := S) (I₀ := I₀) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nFuel
    (Γ := e2eKeyIndStateTy ℓ S ::
      .prod (e2eKeyIndStateTy ℓ S) (.prod (FinT S.N_id) (FinT S.N_recv)) :: Γ)
    .zero (.fst (.snd (.var (.succ .zero)))) (.snd (.snd (.var (.succ .zero))))
    (by simp only [Expr.size]; omega) (by simp only [Expr.size]; omega)
  simp only [Comp.size, Expr.size, pqxdhRevealSpkStepSize] at hbody ⊢
  omega

end Computational.Proofs.E2E.Dsl.M3PqxdhSize

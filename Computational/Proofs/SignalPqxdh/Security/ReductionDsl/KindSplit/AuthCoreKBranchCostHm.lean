/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacProofs

/-!
# Two-Fuel `AuthPrfHmac` Branch Bounds

Step-cost, `.random64`-coin, primitive-query, AST-size, and byte-literal-size bounds over
`pqxdhOps` for the two-fuel `(K_on, K_ro)` `AuthPrfHmac` arms `intSendPrepKC`, `hmSendKC`,
`hmSchedPrepKC`, `hmSchedKC`, `hmRecvTailKC`, and `hmRecvKC`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCostHm

open _root_.ReductionDsl (Ty Var Expr Comp bits)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (sampR64W compLitSize)
open _root_.SignalPqxdh (Setup)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps B primIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (shcrStTy pauseTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (authHybridStateFixedTy prfMkCoreTy prfMkStepPreTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead (cpaSlotSendResTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
  (muStTy intPrepTy schedPrepArgsTy schedPrepTy schedArgsTy schedResTy hmRecvDataTy hmResTy hmPreTy)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (sendKC recvKB shcrFinishSendKC shcrSendKC shcrAcceptKB shcrResumeKC
   authCkSendKB authCkRecvKB authMkSendPreKB authMkRecvPreKB cpaSendSlotKB cpaRecvKC
   intSendPrepKC hmSendKC hmSchedPrepKC hmSchedKC hmRecvTailKC hmRecvKC)

section HmBranchBounds

open _root_.ReductionDsl (bits_mul)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (exprLitSize pqOpLitSize r64W castLegacySamp)
open _root_.SignalPqxdh (F_X25519 firstMsgHdrLen)
open _root_.SignalPqxdh.LegacyCosted (PSamp pqPrimIface pqBytesOps pqU32Ops)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf (
  PT RSF RSH Ext sendQTy recvQTy sessionIdTy authMkSaltCacheTy idealAuthSessionTy
  handshakeHdrTy preKeyBundleTy principalEntryTy opkEntryTy authHybridStateTy preKeyMsgTy
  v letV bindV caseOptV caseSumV findMV anyMV
  eLet eLet2 eCaseOpt eCaseSum eFind eAny eMap
  natEq natLt nat2Eq nat3Eq optU32Eq sidEq sameSaltKeyE saltBytesE kyberEq kyberCheckE
  bytesLen bytesBeq bytes2Eq bytesVarint litB catB bytesCons widenB takeKB
  u32OfNat u32Beq boolOr boolBeq isSomeE optFst optSnd
  samplePrim queryPrim encEC encKEM buildSecretsE firstMsgADE sendGuardE
  aNone aSendFresh aSendUnfresh aRecvHonest aRecvUnfresh
  ahsfHybrid ahsfRecvCount ahsfMkSaltCache ahsfSlots ahsfMk ahsfMkSlots ahsfUpd
  emptyAuthSlotStE assMk
  ahsBase ahsInitKemRecs ahsRecvKemRecs ahsIdealSessions ahsMk ahsUpd
  asSecb asHasWonAuth asPrincipals asSpkBundles asOpkEntries asSessions
  asUsedSendSessions asUsedRecvOPK asUsedRecvNoOPK asUsedKyberTriples
  asSentOPKEvents asSentNoOPKEvents asRecvdOPKEvents asRecvdNoOPKEvents
  asRoCache asRootRoCache asAdvKeys stMk stUpd
  peCorrupted peIkAPk peSecIKA0 peSecIKAsign peIkSignPk
  pkbIkB pkbSpkId pkbSpkB pkbSpkSig pkbPqspkId pkbPqspkB pkbPqspkSig pkbOpkB?
  sbSpkPk sbSpkSk sbPqspkPk sbPqspkSk oeOpkSk oeOpkPk oeConsumed oeMk oeUpd
  hdMk pmMk seMk ikrMk rkrMk iasMk
  hdrIkAPk hdrEkAPk hdrSpkId hdrOpkId? hdrPqspkId hdrKemCt
  pkmHdr pkmEphAPk pkmPqRatchetMsg pkmAeadCt
  iasSid iasIkAPk iasPeerIkPk iasPeerSpkPk iasPeerOpkPk? iasEkAPk iasPeerPqspkPk iasKemCt
  iasSpqrSalt? iasDrKey iasRk1 iasMkSeed iasCk1_1 iasEphAPk
  findHonestC isAdvRegC isGameSpkC isGameOpkC koskBundleOkC koskSenderOkC
  resolveSigPkC checkBundleProvenanceExactC hkdfRoC rootRoC matchIdealAuthHandshakeC
  koskBundleOkC_cost koskSenderOkC_cost checkBundleProvenanceExactC_cost
  matchIdealAuthHandshakeC_cost
  hkdfRoC_cost rootRoC_cost firstMsgADE_cost buildSecretsE_cost sidEq_cost
  optU32Eq_cost sameSaltKeyE_cost kyberCheckE_cost
  koskBundleOkC_queries koskSenderOkC_queries checkBundleProvenanceExactC_queries
  matchIdealAuthHandshakeC_queries
  cost_encEC cost_encKEM cost_letC cost_samplePrim cost_queryPrim
  cost_bytesLen cost_bytesBeq cost_boolOr cost_litB cost_catB cost_takeKB
  cost_u32OfNat cost_u32Beq
  letV_cost_le bindV_cost_le caseOptV_cost_le caseSumV_cost_le
  queries_letC primW primWS bits_0 bits_1 bits_32
)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead (
  getDBytes defaultMsgKeysE
  defaultMsgKeys_cipherKey_length defaultMsgKeys_macKey_length defaultMsgKeys_iv_length
  iasAdE iasAeadCtE iasMsgPlainE iasCk1_0E
  spkHonIdealFromPeerC spkHonIdealFromPeerC_cost spkHonIdealFromPeerC_queries
)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac (
  muKeyIdTy encContTy intFinArgsTy schedOutTy schedFinArgsTy
  bytesTake bytesDrop natLe muKeys muChal muPend muBad muMk
  etmBodyE etmBody24E etmTagE macInputE muKeyIdEq initKeyIdE pendFilterE pendHitE
  ipUEntry ipPeer ipFim ipFresh ipIdeal ipMsgPlain ipT3 ipKeys6 ipDrKey ipRks4
  ipSalt ipPqMsg ipAd ipProv ipRoC ipRootC
  hmKeyIdC encPostC hmEncPreIdC hmForgeIdC finishIntC
  sendSidE hmSendTailC hmRecvPrepC forgeRetIdC hmSchedFinC finErasedE
  cost_bytesTake cost_bytesDrop cost_widenB_32 cost_natLe
  etmBodyE_cost etmBodyE_widenB_cost etmBody24E_cost etmTagE_cost macInputE_cost
  pendFilterE_cost pendHitE_cost encPostC_cost finishIntC_cost
  bits_8 bits_24 bits_firstMsgHdrLen
)

private abbrev hm_zP : pqPrimIface.Tag → ℕ := fun _ => 0
private abbrev hm_r64S : pqPrimIface.smp.Samp → ℕ := sampR64W (I := pqPrimIface) rfl

@[local simp] private theorem hm_r64S_bool : hm_r64S .bool = 0 := rfl
@[local simp] private theorem hm_r64S_bytes32 : hm_r64S .bytes32 = 0 := rfl
@[local simp] private theorem hm_r64S_drKey96 : hm_r64S .drKey96 = 0 := rfl
@[local simp] private theorem hm_r64S_msgKeys80 : hm_r64S .msgKeys80 = 0 := rfl
@[local simp] private theorem hm_r64S_index (_n : ℕ) : hm_r64S (.index _n) = 0 := rfl

@[local simp] private theorem hm_queries_authPrf_letC {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqSig T} {Γ : List PT} {a b : PT}
    (e : Expr pqxdhOps Γ a) (k : Comp pqxdhOps I (a :: Γ) b)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC e k).queries w ws =
      k.queries w ws := by
  simp [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, Comp.queries]

@[local simp] private theorem hm_findHonestC_r64 (S : Setup) (K : ℕ) {Γ Δ : List PT}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).queries hm_zP hm_r64S = 0 := by
  simp [findHonestC, letV, findMV, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_isAdvRegC_r64 (K : ℕ) {Γ Δ : List PT}
    (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvRegC K st pk).queries hm_zP hm_r64S = 0 := by
  simp [isAdvRegC, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_isGameSpkC_r64 (S : Setup) (K : ℕ) {Γ Δ : List PT}
    (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).queries hm_zP hm_r64S = 0 := by
  simp [isGameSpkC, letV, anyMV, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_isGameOpkC_r64 (S : Setup) (K : ℕ) {Γ Δ : List PT}
    (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).queries hm_zP hm_r64S = 0 := by
  simp [isGameOpkC, letV, anyMV, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_koskBundleOkC_r64 (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.preKeyBundleTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC S K st bu : Comp pqxdhOps pqPrimIface Δ .bool).queries hm_zP hm_r64S = 0 := by
  simp [koskBundleOkC, bindV, caseOptV, Comp.queries]

@[local simp] private theorem hm_hkdfRoC_r64 (K : ℕ) {Γ Δ : List PT}
    (st : Var Γ authStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfRoC K st sec).queries hm_zP hm_r64S = 0 := by
  simp [hkdfRoC, letV, caseOptV, bindV, samplePrim, Comp.queries]

@[local simp] private theorem hm_rootRoC_r64 (K : ℕ) {Γ Δ : List PT}
    (st : Var Γ authStateTy) [Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32)) :
    (rootRoC K st rk dh).queries hm_zP hm_r64S = 0 := by
  simp [rootRoC, letV, caseOptV, bindV, samplePrim, Comp.queries]

@[local simp] private theorem hm_checkBundleProvenanceExactC_r64 (S : Setup) (K : ℕ)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ authStateTy)
    (bu : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.preKeyBundleTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkBundleProvenanceExactC S K st bu : Comp pqxdhOps pqPrimIface Δ _).queries hm_zP hm_r64S = 0 := by
  simp [checkBundleProvenanceExactC, bindV, caseOptV, letV, anyMV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_spkHonIdealFromPeerC_r64 (S : Setup) (K : ℕ)
    {Γ₁ Γ₂ Γ₃ Δ : List PT} (st : Var Γ₁ authStateTy)
    (pp : Var Γ₂ (.opt (.prod .nat _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.principalEntryTy)))
    (bu : Var Γ₃ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.preKeyBundleTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (spkHonIdealFromPeerC S K st pp bu : Comp pqxdhOps pqPrimIface Δ .bool).queries hm_zP hm_r64S = 0 := by
  simp [spkHonIdealFromPeerC, caseOptV, letV, anyMV, bindV, queryPrim, hm_zP, Comp.queries]

private theorem hm_bits_mono {m n : ℕ} (h : m ≤ n) : bits m ≤ bits n := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem hm_F_X25519_length : F_X25519.length = 32 := by
  simp [F_X25519]

@[local simp] private theorem hm_intSendPrepKC_r64 (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (AuthCoreKArmsBase.intSendPrepKC S K_on K_ro opk (Δ := Δ) fhst x).queries hm_zP hm_r64S = 0 := by
  simp [AuthCoreKArmsBase.intSendPrepKC, letV, bindV, caseOptV, samplePrim, queryPrim,
    hm_zP, Comp.queries]

theorem intSendPrepKC_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (intSendPrepKC S K_on K_ro opk (Δ := Δ) fhst x).cost ≤
      10500 + 3569 * K_on + 1540 * min K_on S.N_dh + 531 * K_ro := by
  cases opk <;>
  · simp only [intSendPrepKC, AuthCoreKArmsBase.intSendPrepKC,
      koskBundleOkC_cost, spkHonIdealFromPeerC_cost, checkBundleProvenanceExactC_cost,
      hkdfRoC_cost, rootRoC_cost, firstMsgADE_cost, buildSecretsE_cost, sidEq_cost,
      findHonestC, getDBytes, optSnd,
      bindV, letV, caseOptV, findMV, eFind, eAny, eCaseOpt,
      natEq, isSomeE,
      ahsfHybrid, ahsBase, asSecb, asPrincipals, asUsedSendSessions, asRoCache, asRootRoCache,
      peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig,
      cost_encEC, cost_encKEM, cost_letC, cost_samplePrim, cost_queryPrim,
      cost_bytesLen, cost_bytesBeq, cost_boolOr, cost_litB,
      PSamp.cost, PSamp.ty, _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

theorem intSendPrepKC_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (intSendPrepKC S K_on K_ro opk (Δ := Δ) fhst x).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  change (AuthCoreKArmsBase.intSendPrepKC S K_on K_ro opk (Δ := Δ) fhst x).queries
    hm_zP hm_r64S ≤ 2
  rw [hm_intSendPrepKC_r64]; decide

theorem intSendPrepKC_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (intSendPrepKC S K_on K_ro opk (Δ := Δ) fhst x).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 25 + 20 * min K_on S.N_dh := by
  change (intSendPrepKC S K_on K_ro opk (Δ := Δ) fhst x).queries primW primWS ≤ _
  cases opk <;>
  · simp only [intSendPrepKC, AuthCoreKArmsBase.intSendPrepKC,
      koskBundleOkC_queries, spkHonIdealFromPeerC_queries, checkBundleProvenanceExactC_queries,
      hkdfRoC, rootRoC, findHonestC,
      bindV, letV, caseOptV, findMV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem intSendPrepKC_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (intSendPrepKC S K_on K_ro opk (Δ := Δ) fhst x).size ≤
      12000 + 30 * bits K_on + 10 * bits K_ro := by
  cases opk <;>
  · simp only [intSendPrepKC, AuthCoreKArmsBase.intSendPrepKC,
      spkHonIdealFromPeerC, findHonestC, isAdvRegC, isGameSpkC, isGameOpkC,
      koskBundleOkC, resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC,
      getDBytes, buildSecretsE, firstMsgADE, sidEq, natEq, nat2Eq, nat3Eq, optU32Eq,
      isSomeE, optFst, optSnd, boolOr, eLet2,
      ahsfHybrid, ahsBase, asSecb, asPrincipals, asSpkBundles, asOpkEntries,
      asUsedSendSessions, asRoCache, asRootRoCache, asAdvKeys,
      peCorrupted, peIkAPk, peSecIKA0, peIkSignPk,
      pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbPqspkId, pkbPqspkB, pkbPqspkSig, pkbOpkB?,
      sbSpkPk, sbSpkSk, sbPqspkPk, oeOpkSk, oeOpkPk,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM,
      v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
      _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV, findMV, anyMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny,
      litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytes2Eq, bytesVarint,
      u32OfNat, u32Beq,
      samplePrim, queryPrim, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, id_eq]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      pqBytesOps, pqU32Ops, Sum.elim]
    have hmdh : bits (min K_on S.N_dh) ≤ bits K_on := hm_bits_mono (Nat.min_le_left _ _)
    have hb4dh : bits (4 * min K_on S.N_dh) ≤ bits K_on + 3 := by
      have h := bits_mul 4 (min K_on S.N_dh)
      have : bits 4 = 3 := by decide
      omega
    have hbHdr : bits firstMsgHdrLen = 7 := by decide
    have hb0 : bits 0 = 1 := by decide
    have hb1 : bits 1 = 1 := by decide
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem intSendPrepKC_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (intSendPrepKC S K_on K_ro opk (Δ := Δ) fhst x) ≤ 4000 := by
  cases opk <;>
  · simp only [intSendPrepKC, AuthCoreKArmsBase.intSendPrepKC,
      spkHonIdealFromPeerC, findHonestC, isAdvRegC, isGameSpkC, isGameOpkC,
      koskBundleOkC, resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC,
      getDBytes, buildSecretsE, firstMsgADE, sidEq, natEq, nat2Eq, nat3Eq, optU32Eq,
      isSomeE, optFst, optSnd, boolOr, eLet2,
      ahsfHybrid, ahsBase, asSecb, asPrincipals, asSpkBundles, asOpkEntries,
      asUsedSendSessions, asRoCache, asRootRoCache, asAdvKeys,
      peCorrupted, peIkAPk, peSecIKA0, peIkSignPk,
      pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbPqspkId, pkbPqspkB, pkbPqspkSig, pkbOpkB?,
      sbSpkPk, sbSpkSk, sbPqspkPk, oeOpkSk, oeOpkPk,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM,
      v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
      _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV, findMV, anyMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny,
      litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytes2Eq, bytesVarint,
      u32OfNat, u32Beq,
      samplePrim, queryPrim, encEC, encKEM,
      compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_cons, List.length_replicate, hm_F_X25519_length,
      Nat.add_zero, Nat.zero_add,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, id_eq]
    omega

@[local simp] private theorem hm_muKeyIdEq_cost {Γ : List PT} (a b : Expr pqxdhOps Γ muKeyIdTy) :
    (muKeyIdEq a b).cost = a.cost + b.cost + 55 := by
  simp only [muKeyIdEq, eLet2, eLet, eCaseSum, sidEq_cost, natEq, v, Expr.cost]
  omega

@[local simp] private theorem hm_initKeyIdE_cost (S : Setup) {Γ : List PT}
    (sid : Expr pqxdhOps Γ sessionIdTy) :
    (initKeyIdE S sid).cost = sid.cost + 7 := by
  simp only [initKeyIdE, eCaseSum, v, Expr.cost, bits_0]
  omega

@[local simp] private theorem hm_hmKeyIdC_cost (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy)) :
    (hmKeyIdC K a).cost = a.cost + 127 + K * 59 := by
  simp only [hmKeyIdC, letV, caseOptV, bindV, eFind, hm_muKeyIdEq_cost,
    muKeys, muChal, muPend, muBad, muMk, cost_letC, cost_samplePrim,
    PSamp.cost, PSamp.ty, _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.cost, Expr.cost,
    PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

@[local simp] private theorem hm_hmEncPreIdC_cost (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmEncPreIdC K a).cost = a.cost + 1968 + K * 1700 := by
  simp only [hmEncPreIdC, letV, caseOptV, bindV, eFind, hm_muKeyIdEq_cost, natEq, natLt,
    hm_hmKeyIdC_cost, encPostC_cost, muKeys, muChal, muPend, muBad, muMk,
    cost_letC, cost_samplePrim, cost_queryPrim, cost_widenB_32,
    PSamp.cost, PSamp.ty, _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.cost, Expr.cost,
    PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  omega

@[local simp] private theorem hm_hmForgeIdC_cost (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmForgeIdC K a).cost = a.cost + 3855 + K * 177 := by
  simp only [hmForgeIdC, letV, bindV, eCaseOpt, eFind, hm_muKeyIdEq_cost, cost_natLe, isSomeE,
    hm_hmKeyIdC_cost, macInputE_cost, etmBodyE_cost, etmTagE_cost,
    muKeys, muChal, muPend, muBad, muMk,
    cost_letC, cost_queryPrim, cost_bytesBeq, cost_bytesLen, cost_boolOr,
    _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat,
    bits_24, bits_32]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  omega

@[local simp] private theorem hm_defaultMsgKeysE_litSize {Γ : List PT} :
    exprLitSize (defaultMsgKeysE (Γ := Γ)) = 0 := by
  simp [defaultMsgKeysE, litB, exprLitSize, pqOpLitSize]
  exact ⟨rfl, rfl, rfl⟩

@[local simp] private theorem hm_hmKeyIdC_r64 (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy)) :
    (hmKeyIdC K a).queries hm_zP hm_r64S = 0 := by
  simp [hmKeyIdC, letV, caseOptV, bindV, samplePrim, Comp.queries]

@[local simp] private theorem hm_encPostC_r64 (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod encContTy (B 32))) :
    (encPostC K a).queries hm_zP hm_r64S = 0 := by
  simp [encPostC, letV, Comp.queries]

@[local simp] private theorem hm_hmEncPreIdC_r64 (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmEncPreIdC K a).queries hm_zP hm_r64S = 0 := by
  simp [hmEncPreIdC, letV, caseOptV, bindV, samplePrim, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_finishIntC_r64 {Δ : List PT}
    (a : Expr pqxdhOps Δ intFinArgsTy) :
    (finishIntC a).queries hm_zP hm_r64S = 0 := by
  simp [finishIntC, letV, Comp.queries]

@[local simp] private theorem hm_hmSendTailC_r64 (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy) (p : Var Γ₅ intPrepTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmSendTailC S K opk jt fhst mst x p : Comp pqxdhOps pqPrimIface Δ hmPreTy).queries
      hm_zP hm_r64S = 0 := by
  simp [hmSendTailC, letV, bindV, caseSumV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_hmSendKC_r64 (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmSendKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).queries hm_zP hm_r64S = 0 := by
  simp [hmSendKC, AuthCoreKArmsBase.hmSendKC, bindV, caseOptV, Comp.queries]

private theorem hm_hmSendTailC_cost_le (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ sendQTy) (p : Var Γ₅ intPrepTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmSendTailC S K opk jt fhst mst x p : Comp pqxdhOps pqPrimIface Δ hmPreTy).cost ≤
      3500 + K * 1750 := by
  cases opk <;>
  · simp only [hmSendTailC, sendSidE,
      hm_hmEncPreIdC_cost, finishIntC_cost, hm_initKeyIdE_cost,
      getDBytes, defaultMsgKeysE,
      defaultMsgKeys_cipherKey_length, defaultMsgKeys_macKey_length, defaultMsgKeys_iv_length,
      ipAd, ipMsgPlain, ipIdeal, ipRks4, ipSalt, ipT3, ipFim,
      bindV, letV, caseSumV, eCaseOpt,
      cost_letC, cost_queryPrim, cost_litB,
      _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem hm_hmSendTailC_queries_le (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ sendQTy) (p : Var Γ₅ intPrepTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmSendTailC S K opk jt fhst mst x p : Comp pqxdhOps pqPrimIface Δ hmPreTy).queries
      primW primWS ≤ 2 := by
  cases opk <;>
  · simp only [hmSendTailC, hmEncPreIdC, hmKeyIdC, encPostC, finishIntC,
      bindV, letV, caseOptV, caseSumV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries]
    omega

theorem hmSendKC_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmSendKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).cost ≤
      14100 + 5319 * K_on + 1540 * min K_on S.N_dh + 531 * K_ro := by
  unfold hmSendKC AuthCoreKArmsBase.hmSendKC
  have hPrep := intSendPrepKC_cost_le S K_on K_ro opk (Δ := Δ) fhst x
  unfold intSendPrepKC at hPrep
  have hTail := hm_hmSendTailC_cost_le S K_on opk (Δ := intPrepTy :: .opt intPrepTy :: Δ)
    jt fhst mst x (.zero : Var (intPrepTy :: .opt intPrepTy :: Δ) intPrepTy)
  cases opk <;>
  · simp only [sendGuardE, isSomeE, pkbOpkB?, aNone, bindV, caseOptV,
      v, Comp.cost, Expr.cost, ite_true, ite_false, Bool.false_eq_true]
    omega

theorem hmSendKC_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmSendKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  change (hmSendKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).queries hm_zP hm_r64S ≤ 2
  rw [hm_hmSendKC_r64]
  decide

theorem hmSendKC_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmSendKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 30 + 20 * min K_on S.N_dh := by
  change (hmSendKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).queries primW primWS ≤ _
  unfold hmSendKC AuthCoreKArmsBase.hmSendKC
  have hPrep : (intSendPrepKC S K_on K_ro opk (Δ := Δ) fhst x).queries primW primWS ≤
      25 + 20 * min K_on S.N_dh := intSendPrepKC_queries_prim_le S K_on K_ro opk (Δ := Δ) fhst x
  unfold intSendPrepKC at hPrep
  have hTail := hm_hmSendTailC_queries_le S K_on opk (Δ := intPrepTy :: .opt intPrepTy :: Δ)
    jt fhst mst x (.zero : Var (intPrepTy :: .opt intPrepTy :: Δ) intPrepTy)
  simp only [bindV, caseOptV, Comp.queries]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
private theorem hm_hmSendTailC_size_le (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ sendQTy) (p : Var Γ₅ intPrepTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmSendTailC S K opk jt fhst mst x p : Comp pqxdhOps pqPrimIface Δ hmPreTy).size ≤
      2900 + 10 * bits K := by
  cases opk <;>
  · simp only [hmSendTailC, sendSidE, hmEncPreIdC, hmKeyIdC, encPostC, finishIntC,
      initKeyIdE, muKeyIdEq, pendFilterE, pendHitE, macInputE, etmBodyE, etmBody24E,
      bytesTake, bytesDrop, defaultMsgKeysE, getDBytes,
      muKeys, muChal, muPend, muBad, muMk,
      ipUEntry, ipPeer, ipFim, ipFresh, ipIdeal, ipMsgPlain, ipT3, ipKeys6, ipDrKey,
      ipRks4, ipSalt, ipPqMsg, ipAd, ipProv, ipRoC, ipRootC,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots, ahsfUpd,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, stMk, stUpd,
      hdMk, pmMk, seMk, ikrMk, iasMk, aSendFresh, aSendUnfresh,
      peIkAPk, pkbIkB, pkbSpkId, pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB,
      sidEq, natEq, natLt, nat2Eq, nat3Eq, boolOr, isSomeE, optFst, optSnd, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC,
      v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
      _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny,
      litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytesVarint,
      samplePrim, queryPrim,
      Comp.size, Expr.size, bits_0, bits_8, bits_24, bits_32, bits_firstMsgHdrLen,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, id_eq]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      pqBytesOps, pqU32Ops, Sum.elim]
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
private theorem hm_hmSendTailC_litSize_le (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ sendQTy) (p : Var Γ₅ intPrepTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    compLitSize (hmSendTailC S K opk jt fhst mst x p : Comp pqxdhOps pqPrimIface Δ hmPreTy) ≤
      500 := by
  cases opk <;>
  · simp only [hmSendTailC, sendSidE, hmEncPreIdC, hmKeyIdC, encPostC, finishIntC,
      initKeyIdE, muKeyIdEq, pendFilterE, pendHitE, macInputE, etmBodyE, etmBody24E,
      bytesTake, bytesDrop, hm_defaultMsgKeysE_litSize, getDBytes,
      muKeys, muChal, muPend, muBad, muMk,
      ipUEntry, ipPeer, ipFim, ipFresh, ipIdeal, ipMsgPlain, ipT3, ipKeys6, ipDrKey,
      ipRks4, ipSalt, ipPqMsg, ipAd, ipProv, ipRoC, ipRootC,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots, ahsfUpd,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, stMk, stUpd,
      hdMk, pmMk, seMk, ikrMk, iasMk, aSendFresh, aSendUnfresh,
      peIkAPk, pkbIkB, pkbSpkId, pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB,
      sidEq, natEq, natLt, nat2Eq, nat3Eq, boolOr, isSomeE, optFst, optSnd, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC,
      v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
      _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny,
      litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytesVarint,
      samplePrim, queryPrim,
      compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_cons, List.length_replicate,
      Nat.add_zero, Nat.zero_add,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, id_eq]
    omega

theorem hmSendKC_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmSendKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).size ≤
      15000 + 40 * bits K_on + 10 * bits K_ro := by
  unfold hmSendKC AuthCoreKArmsBase.hmSendKC
  have hPrep := intSendPrepKC_size_le S K_on K_ro opk (Δ := Δ) fhst x
  unfold intSendPrepKC at hPrep
  have hTail := hm_hmSendTailC_size_le S K_on opk (Δ := intPrepTy :: .opt intPrepTy :: Δ)
    jt fhst mst x (.zero : Var (intPrepTy :: .opt intPrepTy :: Δ) intPrepTy)
  cases opk <;>
  · simp only [sendGuardE, isSomeE, pkbOpkB?, aNone, bindV, caseOptV,
      v, Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true]
    omega

theorem hmSendKC_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    compLitSize (hmSendKC S K_on K_ro opk (Δ := Δ) jt fhst mst x) ≤ 5000 := by
  unfold hmSendKC AuthCoreKArmsBase.hmSendKC
  have hPrep := intSendPrepKC_litSize_le S K_on K_ro opk (Δ := Δ) fhst x
  unfold intSendPrepKC at hPrep
  have hTail := hm_hmSendTailC_litSize_le S K_on opk (Δ := intPrepTy :: .opt intPrepTy :: Δ)
    jt fhst mst x (.zero : Var (intPrepTy :: .opt intPrepTy :: Δ) intPrepTy)
  cases opk <;>
  · simp only [sendGuardE, isSomeE, pkbOpkB?, aNone, bindV, caseOptV,
      v, compLitSize, exprLitSize, ↓reduceIte, Bool.false_eq_true]
    omega

@[local simp] private theorem hm_matchIdealAuthHandshakeC_r64
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (ikB : Var Γ₁ (B 32)) (spkB : Var Γ₂ (B 32)) (opkB? : Var Γ₃ (.opt (B 32)))
    (pqspkB : Var Γ₄ (B 1568)) (hdr : Var Γ₅ handshakeHdrTy) (s : Var Γ₆ idealAuthSessionTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (matchIdealAuthHandshakeC ikB spkB opkB? pqspkB hdr s :
      Comp pqxdhOps pqPrimIface Δ .bool).queries hm_zP hm_r64S = 0 := by
  simp [matchIdealAuthHandshakeC, bindV, caseOptV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_hmSchedPrepKC_r64 (S : Setup) (K_on K_ro : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    (AuthCoreKArmsBase.hmSchedPrepKC S K_on K_ro a).queries hm_zP hm_r64S = 0 := by
  simp only [AuthCoreKArmsBase.hmSchedPrepKC, letV, bindV, caseOptV, findMV, samplePrim, queryPrim,
    hm_findHonestC_r64, hm_matchIdealAuthHandshakeC_r64, hm_hkdfRoC_r64, hm_rootRoC_r64,
    hm_queries_authPrf_letC, hm_zP, hm_r64S_bytes32, hm_r64S_drKey96, Comp.queries]
  omega

private theorem hm_hmSchedPrepKC_queries_tight (S : Setup) (K_on K_ro : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    (AuthCoreKArmsBase.hmSchedPrepKC S K_on K_ro a).queries primW primWS ≤
      6 + 2 * min K_on S.N_dh + 10 * min K_on S.N_sess_tot := by
  simp only [AuthCoreKArmsBase.hmSchedPrepKC,
    matchIdealAuthHandshakeC_queries, hkdfRoC, rootRoC, findHonestC,
    bindV, letV, caseOptV, findMV,
    queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
private theorem hm_hmSchedPrepKC_size_tight (S : Setup) (K_on K_ro : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    (AuthCoreKArmsBase.hmSchedPrepKC S K_on K_ro a).size ≤
      a.size + 2500 + 3 * bits K_on + 3 * bits K_ro := by
  simp only [AuthCoreKArmsBase.hmSchedPrepKC,
    findHonestC, matchIdealAuthHandshakeC, hkdfRoC, rootRoC, iasCk1_0E,
    natEq, bytes2Eq, isSomeE, boolOr, eLet2,
    ahsBase, ahsIdealSessions, asPrincipals, asRoCache, asRootRoCache,
    peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkPk,
    hdrIkAPk, hdrEkAPk, hdrKemCt, pkmHdr, pkmEphAPk, pkmPqRatchetMsg,
    iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt,
    iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasEphAPk,
    Expr.litBool, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Expr.boolOr,
    Expr.listCons, Expr.findBounded,
    Comp.iteC, Comp.caseOptC, Comp.findBoundedM,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV,
    eLet, eCaseOpt, eFind, bytesBeq, samplePrim, queryPrim,
    Comp.size, Expr.size]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    pqBytesOps, pqU32Ops, Sum.elim]
  have hmdh : bits (min K_on S.N_dh) ≤ bits K_on := hm_bits_mono (Nat.min_le_left _ _)
  have hmsess : bits (min K_on S.N_sess_tot) ≤ bits K_on := hm_bits_mono (Nat.min_le_left _ _)
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
private theorem hm_hmSchedPrepKC_litSize_tight (S : Setup) (K_on K_ro : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    compLitSize (AuthCoreKArmsBase.hmSchedPrepKC S K_on K_ro a) ≤ exprLitSize a + 500 := by
  simp only [AuthCoreKArmsBase.hmSchedPrepKC,
    findHonestC, matchIdealAuthHandshakeC, hkdfRoC, rootRoC, iasCk1_0E,
    natEq, bytes2Eq, isSomeE, boolOr, eLet2,
    ahsBase, ahsIdealSessions, asPrincipals, asRoCache, asRootRoCache,
    peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkPk,
    hdrIkAPk, hdrEkAPk, hdrKemCt, pkmHdr, pkmEphAPk, pkmPqRatchetMsg,
    iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt,
    iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasEphAPk,
    Expr.litBool, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Expr.boolOr,
    Expr.listCons, Expr.findBounded,
    Comp.iteC, Comp.caseOptC, Comp.findBoundedM,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV,
    eLet, eCaseOpt, eFind, bytesBeq, samplePrim, queryPrim,
    compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
  omega

theorem hmSchedPrepKC_cost_le (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    (hmSchedPrepKC S K_on K_ro a).cost ≤
      a.cost + 1500 + 69 * K_on + 210 * min K_on S.N_dh + 7350 * min K_on S.N_sess_tot +
        531 * K_ro := by
  simp only [hmSchedPrepKC, AuthCoreKArmsBase.hmSchedPrepKC,
    matchIdealAuthHandshakeC_cost, hkdfRoC_cost, rootRoC_cost, findHonestC, iasCk1_0E,
    bindV, letV, caseOptV, findMV, eCaseOpt, isSomeE,
    ahsBase, ahsIdealSessions, asPrincipals, asRoCache, asRootRoCache,
    peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkPk,
    hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg,
    iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasEphAPk,
    cost_letC, cost_samplePrim, cost_queryPrim, cost_bytesBeq, cost_boolOr,
    PSamp.cost, PSamp.ty, _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.cost, Expr.cost,
    PNat.val_ofNat]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

theorem hmSchedPrepKC_r64_le (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    (hmSchedPrepKC S K_on K_ro a).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  change (AuthCoreKArmsBase.hmSchedPrepKC S K_on K_ro a).queries hm_zP hm_r64S ≤ 2
  rw [hm_hmSchedPrepKC_r64]
  decide

theorem hmSchedPrepKC_queries_prim_le (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    (hmSchedPrepKC S K_on K_ro a).queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤
      15 + 4 * min K_on S.N_dh + 10 * min K_on S.N_sess_tot := by
  have h := hm_hmSchedPrepKC_queries_tight S K_on K_ro a
  change (AuthCoreKArmsBase.hmSchedPrepKC S K_on K_ro a).queries primW primWS ≤ _
  omega

theorem hmSchedPrepKC_size_le (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    (hmSchedPrepKC S K_on K_ro a).size ≤
      a.size + 6000 + 20 * bits K_on + 10 * bits K_ro := by
  have h := hm_hmSchedPrepKC_size_tight S K_on K_ro a
  unfold hmSchedPrepKC
  omega

theorem hmSchedPrepKC_litSize_le (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    compLitSize (hmSchedPrepKC S K_on K_ro a) ≤ exprLitSize a + 3000 := by
  have h := hm_hmSchedPrepKC_litSize_tight S K_on K_ro a
  unfold hmSchedPrepKC
  omega

@[local simp] private theorem hm_hmForgeIdC_r64 (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmForgeIdC K a).queries hm_zP hm_r64S = 0 := by
  simp [hmForgeIdC, letV, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_forgeRetIdC_r64 (K : ℕ) {Γ₁ Δ : List PT}
    (fc : Var Γ₁ (.prod .nat (.prod (B 158) (.prod (B 32) muStTy)))) [Ext Γ₁ Δ]
    (idx : Expr pqxdhOps Δ muKeyIdTy) (cache' : Expr pqxdhOps Δ authMkSaltCacheTy) :
    (forgeRetIdC K fc idx cache').queries hm_zP hm_r64S = 0 := by
  simp [forgeRetIdC, letV, bindV, Comp.queries]

@[local simp] private theorem hm_hmSchedFinC_r64 (S : Setup) (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedFinArgsTy) : (hmSchedFinC S K a).queries hm_zP hm_r64S = 0 := by
  simp [hmSchedFinC, letV, bindV, caseOptV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_hmSchedKC_r64 (S : Setup) (K_on K_ro : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    (AuthCoreKArmsBase.hmSchedKC S K_on K_ro a).queries hm_zP hm_r64S = 0 := by
  simp [AuthCoreKArmsBase.hmSchedKC, letV, bindV, caseOptV, Comp.queries]

private theorem hm_hmSchedFinC_cost_le (S : Setup) (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedFinArgsTy) : (hmSchedFinC S K a).cost ≤ a.cost + 6500 + K * 900 := by
  simp only [hmSchedFinC, forgeRetIdC, hm_hmForgeIdC_cost, hm_initKeyIdE_cost, firstMsgADE_cost,
    sidEq_cost, sameSaltKeyE_cost, iasAdE, iasAeadCtE, iasMsgPlainE, defaultMsgKeysE,
    defaultMsgKeys_cipherKey_length, defaultMsgKeys_macKey_length, defaultMsgKeys_iv_length,
    bindV, letV, caseOptV, eFind, eCaseOpt, peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg,
    pkmAeadCt, iasSid, iasSpqrSalt?, cost_letC, cost_queryPrim, cost_bytesBeq, cost_litB,
    _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

private theorem hm_hmSchedFinC_queries_le (S : Setup) (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedFinArgsTy) : (hmSchedFinC S K a).queries primW primWS ≤ 2 := by
  simp only [hmSchedFinC, forgeRetIdC, hmForgeIdC, hmKeyIdC,
    bindV, letV, caseOptV, queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries]
  omega

private theorem hm_letV_queries_le {Γ : List PT} {τ₁ τ₂ : PT} (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ₂) {M : ℕ}
    (hk : (k .zero).queries primW primWS ≤ M) : (letV e k).queries primW primWS ≤ M := by
  simpa only [letV, queries_letC] using hk

private theorem hm_bindV_queries_le {Γ : List PT} {τ₁ τ₂ : PT}
    (m : Comp pqxdhOps pqPrimIface Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ₂) {M₁ M₂ : ℕ}
    (hm : m.queries primW primWS ≤ M₁) (hk : (k .zero).queries primW primWS ≤ M₂) :
    (bindV m k).queries primW primWS ≤ M₁ + M₂ := by
  simp only [bindV, Comp.queries]; omega

private theorem hm_caseOptV_queries_le {Γ : List PT} {τ₁ τ₂ : PT}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps pqPrimIface Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ₂) {M₁ M₂ : ℕ}
    (hn : kn.queries primW primWS ≤ M₁) (hs : (ks .zero).queries primW primWS ≤ M₂) :
    (caseOptV o kn ks).queries primW primWS ≤ max M₁ M₂ := by
  simp only [caseOptV, Comp.queries]; omega

private theorem hm_hmSchedKC_queries_tight (S : Setup) (K_on K_ro : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    (AuthCoreKArmsBase.hmSchedKC S K_on K_ro a).queries primW primWS ≤
      8 + 2 * min K_on S.N_dh + 10 * min K_on S.N_sess_tot := by
  unfold AuthCoreKArmsBase.hmSchedKC
  refine le_trans
    (hm_letV_queries_le _ _ <| hm_letV_queries_le _ _ <| hm_letV_queries_le _ _ <|
     hm_letV_queries_le _ _ <| hm_letV_queries_le _ _ <| hm_letV_queries_le _ _ <|
     hm_bindV_queries_le _ _ (hm_hmSchedPrepKC_queries_tight S K_on K_ro _) <|
     hm_caseOptV_queries_le _ _ _ (by simp only [Comp.queries]; exact le_rfl)
       (hm_hmSchedFinC_queries_le S K_on _))
    (by omega)

theorem hmSchedKC_cost_le (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    (hmSchedKC S K_on K_ro a).cost ≤
      a.cost + 8100 + 969 * K_on + 210 * min K_on S.N_dh + 7350 * min K_on S.N_sess_tot +
        531 * K_ro := by
  unfold hmSchedKC AuthCoreKArmsBase.hmSchedKC
  have hPrep : ∀ {Δ' : List (Ty pqSig)} (p : Expr pqxdhOps Δ' schedPrepArgsTy),
      (AuthCoreKArmsBase.hmSchedPrepKC S K_on K_ro p).cost ≤
        p.cost + 1500 + 69 * K_on + 210 * min K_on S.N_dh + 7350 * min K_on S.N_sess_tot +
          531 * K_ro := hmSchedPrepKC_cost_le S K_on K_ro
  refine le_trans
    (letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     bindV_cost_le _ _ (hPrep _) <|
     caseOptV_cost_le _ _ _
       (by simp only [v, Comp.cost, Expr.cost]; exact le_rfl)
       (hm_hmSchedFinC_cost_le S K_on _))
    ?_
  simp only [v, Expr.cost]; omega

theorem hmSchedKC_r64_le (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    (hmSchedKC S K_on K_ro a).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  change (AuthCoreKArmsBase.hmSchedKC S K_on K_ro a).queries hm_zP hm_r64S ≤ 2
  rw [hm_hmSchedKC_r64]; decide

theorem hmSchedKC_queries_prim_le (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    (hmSchedKC S K_on K_ro a).queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤
      20 + 4 * min K_on S.N_dh + 10 * min K_on S.N_sess_tot := by
  have h := hm_hmSchedKC_queries_tight S K_on K_ro a
  change (AuthCoreKArmsBase.hmSchedKC S K_on K_ro a).queries primW primWS ≤ _
  omega

private theorem hm_letV_size_le {Γ : List PT} {τ₁ τ₂ : PT} (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ₂) {M : ℕ}
    (hk : (k .zero).size ≤ M) : (letV e k).size ≤ e.size + M + 2 := by
  simp only [letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, Comp.size]; omega

private theorem hm_bindV_size_le {Γ : List PT} {τ₁ τ₂ : PT}
    (m : Comp pqxdhOps pqPrimIface Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ₂) {M₁ M₂ : ℕ}
    (hm : m.size ≤ M₁) (hk : (k .zero).size ≤ M₂) : (bindV m k).size ≤ M₁ + M₂ + 1 := by
  simp only [bindV, Comp.size]; omega

private theorem hm_caseOptV_size_le {Γ : List PT} {τ₁ τ₂ : PT}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps pqPrimIface Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ₂) {M₁ M₂ : ℕ}
    (hn : kn.size ≤ M₁) (hs : (ks .zero).size ≤ M₂) :
    (caseOptV o kn ks).size ≤ o.size + M₁ + M₂ + 1 := by
  simp only [caseOptV, Comp.size]; omega

private theorem hm_letV_litSize_le {Γ : List PT} {τ₁ τ₂ : PT} (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ₂) {M : ℕ}
    (hk : compLitSize (k .zero) ≤ M) : compLitSize (letV e k) ≤ exprLitSize e + M := by
  simp only [letV, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, compLitSize]; omega

private theorem hm_bindV_litSize_le {Γ : List PT} {τ₁ τ₂ : PT}
    (m : Comp pqxdhOps pqPrimIface Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ₂) {M₁ M₂ : ℕ}
    (hm : compLitSize m ≤ M₁) (hk : compLitSize (k .zero) ≤ M₂) :
    compLitSize (bindV m k) ≤ M₁ + M₂ := by
  simp only [bindV, compLitSize]; omega

private theorem hm_caseOptV_litSize_le {Γ : List PT} {τ₁ τ₂ : PT}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps pqPrimIface Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ₂) {M₁ M₂ : ℕ}
    (hn : compLitSize kn ≤ M₁) (hs : compLitSize (ks .zero) ≤ M₂) :
    compLitSize (caseOptV o kn ks) ≤ exprLitSize o + M₁ + M₂ := by
  simp only [caseOptV, compLitSize]; omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
private theorem hm_hmSchedFinC_size_le (S : Setup) (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedFinArgsTy) :
    (hmSchedFinC S K a).size ≤ a.size + 4500 + 17 * bits K := by
  simp only [hmSchedFinC, forgeRetIdC, hmForgeIdC, hmKeyIdC, initKeyIdE, muKeyIdEq,
    macInputE, etmBodyE, etmTagE, bytesTake, bytesDrop, natLe, firstMsgADE, encEC,
    sidEq, sameSaltKeyE, saltBytesE, natEq, nat2Eq, nat3Eq, bytes2Eq, defaultMsgKeysE,
    iasAdE, iasAeadCtE, iasMsgPlainE, iasSid, iasSpqrSalt?,
    peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    muKeys, muChal, muPend, muBad, muMk, isSomeE, boolOr, eLet2,
    Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Expr.boolOr,
    Expr.listCons, Expr.findBounded, Comp.iteC, Comp.caseOptC,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, eLet, eCaseOpt, eCaseSum, eFind,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytesVarint, samplePrim, queryPrim,
    Comp.size, Expr.size, bits_0, bits_1, bits_8, bits_24, bits_32, bits_firstMsgHdrLen]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    pqBytesOps, pqU32Ops, Sum.elim]
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
private theorem hm_hmSchedFinC_litSize_le (S : Setup) (K : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedFinArgsTy) :
    compLitSize (hmSchedFinC S K a) ≤ exprLitSize a + 500 := by
  simp only [hmSchedFinC, forgeRetIdC, hmForgeIdC, hmKeyIdC, initKeyIdE, muKeyIdEq,
    macInputE, etmBodyE, etmTagE, bytesTake, bytesDrop, natLe, firstMsgADE, encEC,
    sidEq, sameSaltKeyE, saltBytesE, natEq, nat2Eq, nat3Eq, bytes2Eq, hm_defaultMsgKeysE_litSize,
    iasAdE, iasAeadCtE, iasMsgPlainE, iasSid, iasSpqrSalt?,
    peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    muKeys, muChal, muPend, muBad, muMk, isSomeE, boolOr, eLet2,
    Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Expr.boolOr,
    Expr.listCons, Expr.findBounded, Comp.iteC, Comp.caseOptC,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, eLet, eCaseOpt, eCaseSum, eFind,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytesVarint, samplePrim, queryPrim,
    compLitSize, exprLitSize, pqOpLitSize, List.length_nil, List.length_cons, List.length_replicate,
    hm_F_X25519_length, Nat.add_zero, Nat.zero_add]
  omega

private theorem hm_hmSchedKC_size_tight (S : Setup) (K_on K_ro : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    (AuthCoreKArmsBase.hmSchedKC S K_on K_ro a).size ≤
      a.size + 7200 + 20 * bits K_on + 3 * bits K_ro := by
  unfold AuthCoreKArmsBase.hmSchedKC
  refine le_trans
    (hm_letV_size_le _ _ <| hm_letV_size_le _ _ <| hm_letV_size_le _ _ <|
     hm_letV_size_le _ _ <| hm_letV_size_le _ _ <| hm_letV_size_le _ _ <|
     hm_bindV_size_le _ _ (hm_hmSchedPrepKC_size_tight S K_on K_ro _) <|
     hm_caseOptV_size_le _ _ _
       (by simp only [v, Comp.size, Expr.size]; exact le_rfl)
       (hm_hmSchedFinC_size_le S K_on _))
    (by simp only [v, Expr.size]; omega)

private theorem hm_hmSchedKC_litSize_tight (S : Setup) (K_on K_ro : ℕ) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    compLitSize (AuthCoreKArmsBase.hmSchedKC S K_on K_ro a) ≤ exprLitSize a + 1100 := by
  unfold AuthCoreKArmsBase.hmSchedKC
  refine le_trans
    (hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <|
     hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <|
     hm_bindV_litSize_le _ _ (hm_hmSchedPrepKC_litSize_tight S K_on K_ro _) <|
     hm_caseOptV_litSize_le _ _ _
       (by simp only [v, compLitSize, exprLitSize]; exact le_rfl)
       (hm_hmSchedFinC_litSize_le S K_on _))
    (by simp only [v, exprLitSize]; omega)

theorem hmSchedKC_size_le (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    (hmSchedKC S K_on K_ro a).size ≤
      a.size + 10000 + 30 * bits K_on + 10 * bits K_ro := by
  have h := hm_hmSchedKC_size_tight S K_on K_ro a
  unfold hmSchedKC; omega

theorem hmSchedKC_litSize_le (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    compLitSize (hmSchedKC S K_on K_ro a) ≤ exprLitSize a + 4000 := by
  have h := hm_hmSchedKC_litSize_tight S K_on K_ro a
  unfold hmSchedKC; omega

@[local simp] private theorem hm_hmRecvTailKC_r64 (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (AuthCoreKArmsBase.hmRecvTailKC S K_on K_ro opk (Δ := Δ) jt fhst mst x d).queries
      hm_zP hm_r64S = 0 := by
  simp [AuthCoreKArmsBase.hmRecvTailKC, letV, bindV, Comp.queries]

private theorem hm_hmRecvTailKC_queries_tight (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (AuthCoreKArmsBase.hmRecvTailKC S K_on K_ro opk (Δ := Δ) jt fhst mst x d).queries
      primW primWS ≤ 8 + 2 * min K_on S.N_dh + 10 * min K_on S.N_sess_tot := by
  unfold AuthCoreKArmsBase.hmRecvTailKC
  refine le_trans
    (hm_letV_queries_le _ _ <| hm_letV_queries_le _ _ <| hm_letV_queries_le _ _ <|
     hm_letV_queries_le _ _ <| hm_letV_queries_le _ _ <| hm_letV_queries_le _ _ <|
     hm_letV_queries_le _ _ <| hm_letV_queries_le _ _ <| hm_letV_queries_le _ _ <|
     hm_bindV_queries_le _ _ (hm_hmSchedKC_queries_tight S K_on K_ro _)
       (by simp only [letV, queries_letC, Comp.queries]; exact le_rfl))
    (by omega)

set_option linter.unusedSimpArgs false in
private theorem hm_finErasedE_size_le (K : ℕ) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ : List PT}
    (kjo : Var Γ₁ (.prod .nat (.prod .nat .nat)))
    (usedT' : Var Γ₂ (.list (.prod .nat (.prod _root_.SignalPqxdh.LegacyCosted.U32
      (.prod _root_.SignalPqxdh.LegacyCosted.U32 (B 32))))))
    (sndHon : Var Γ₃ .bool) (hstDec : Var Γ₄ authHybridStateTy) (res? : Var Γ₅ schedOutTy)
    [Ext Γ₁ Γ] [Ext Γ₂ Γ] [Ext Γ₃ Γ] [Ext Γ₄ Γ] [Ext Γ₅ Γ] :
    (finErasedE K opk (Γ := Γ) kjo usedT' sndHon hstDec res?).size ≤ 400 + 2 * bits K := by
  cases opk <;>
  · simp only [finErasedE, eMap, eCaseOpt, natEq, nat2Eq, nat3Eq,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, stMk, stUpd, oeOpkSk, oeOpkPk, oeMk, oeUpd,
      aNone, aRecvHonest, aRecvUnfresh,
      Expr.litBool, Expr.noneE, Expr.someE, Expr.boolAnd, Expr.listCons, Expr.mapBounded,
      v, eLet, Expr.size, ↓reduceIte, Bool.false_eq_true]
    omega

set_option linter.unusedSimpArgs false in
private theorem hm_finErasedE_litSize_eq (K : ℕ) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ : List PT}
    (kjo : Var Γ₁ (.prod .nat (.prod .nat .nat)))
    (usedT' : Var Γ₂ (.list (.prod .nat (.prod _root_.SignalPqxdh.LegacyCosted.U32
      (.prod _root_.SignalPqxdh.LegacyCosted.U32 (B 32))))))
    (sndHon : Var Γ₃ .bool) (hstDec : Var Γ₄ authHybridStateTy) (res? : Var Γ₅ schedOutTy)
    [Ext Γ₁ Γ] [Ext Γ₂ Γ] [Ext Γ₃ Γ] [Ext Γ₄ Γ] [Ext Γ₅ Γ] :
    exprLitSize (finErasedE K opk (Γ := Γ) kjo usedT' sndHon hstDec res?) = 0 := by
  cases opk <;>
    simp [finErasedE, eMap, eCaseOpt, natEq, nat2Eq, nat3Eq,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, stMk, stUpd, oeOpkSk, oeOpkPk, oeMk, oeUpd,
      aNone, aRecvHonest, aRecvUnfresh, v, eLet, exprLitSize]

private theorem hm_letV_finErasedE_size_le (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (kjo : Var Γ₁ (.prod .nat (.prod .nat .nat)))
    (usedT' : Var Γ₂ (.list (.prod .nat (.prod _root_.SignalPqxdh.LegacyCosted.U32
      (.prod _root_.SignalPqxdh.LegacyCosted.U32 (B 32))))))
    (sndHon : Var Γ₃ .bool) (hstDec : Var Γ₄ authHybridStateTy) (res? : Var Γ₅ schedOutTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    {τ : PT} (k : Var (RSH :: Δ) RSH → Comp pqxdhOps pqPrimIface (RSH :: Δ) τ)
    {M : ℕ} (hk : (k .zero).size ≤ M) :
    (letV (finErasedE K opk (Γ := Δ) kjo usedT' sndHon hstDec res?) k).size ≤
      402 + 2 * bits K + M := by
  have h1 := hm_letV_size_le (finErasedE K opk (Γ := Δ) kjo usedT' sndHon hstDec res?) k hk
  have h2 := hm_finErasedE_size_le K opk (Γ := Δ) kjo usedT' sndHon hstDec res?
  omega

set_option linter.unusedSimpArgs false in
private theorem hm_hmRecvTailKC_size_tight (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (AuthCoreKArmsBase.hmRecvTailKC S K_on K_ro opk (Δ := Δ) jt fhst mst x d).size ≤
      8000 + 22 * bits K_on + 3 * bits K_ro := by
  unfold AuthCoreKArmsBase.hmRecvTailKC
  refine le_trans
    (hm_letV_size_le _ _ <| hm_letV_size_le _ _ <| hm_letV_size_le _ _ <|
     hm_letV_size_le _ _ <| hm_letV_size_le _ _ <| hm_letV_size_le _ _ <|
     hm_letV_size_le _ _ <| hm_letV_size_le _ _ <| hm_letV_size_le _ _ <|
     hm_bindV_size_le _ _ (hm_hmSchedKC_size_tight S K_on K_ro _) <|
     hm_letV_size_le _ _ <| hm_letV_size_le _ _ <| hm_letV_size_le _ _ <|
     hm_letV_finErasedE_size_le K_on opk _ _ _ _ _ _
       (by simp only [ahsfRecvCount, emptyAuthSlotStE, assMk, Expr.litBool, Expr.litNat,
             Expr.listNil, v, Comp.size, Expr.size, bits_0, bits_1]; exact le_rfl))
    (by simp only [ahsfRecvCount, ahsfMkSaltCache, v, Expr.size]; omega)

private theorem hm_hmRecvTailKC_litSize_tight (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    compLitSize (AuthCoreKArmsBase.hmRecvTailKC S K_on K_ro opk (Δ := Δ) jt fhst mst x d) ≤
      1100 := by
  unfold AuthCoreKArmsBase.hmRecvTailKC
  refine le_trans
    (hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <|
     hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <|
     hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <|
     hm_bindV_litSize_le _ _ (hm_hmSchedKC_litSize_tight S K_on K_ro _) <|
     hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <| hm_letV_litSize_le _ _ <|
     hm_letV_litSize_le _ _
       (by simp only [ahsfRecvCount, v, compLitSize, exprLitSize]; exact le_rfl))
    (by simp only [hm_finErasedE_litSize_eq, ahsfRecvCount, ahsfMkSaltCache, v, exprLitSize]; omega)

theorem hmRecvTailKC_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmRecvTailKC S K_on K_ro opk (Δ := Δ) jt fhst mst x d).cost ≤
      9000 + 1119 * K_on + 210 * min K_on S.N_dh + 7350 * min K_on S.N_sess_tot + 531 * K_ro := by
  unfold hmRecvTailKC AuthCoreKArmsBase.hmRecvTailKC
  have hSched : ∀ {Δ' : List (Ty pqSig)} (p : Expr pqxdhOps Δ' schedArgsTy),
      (AuthCoreKArmsBase.hmSchedKC S K_on K_ro p).cost ≤
        p.cost + 8100 + 969 * K_on + 210 * min K_on S.N_dh + 7350 * min K_on S.N_sess_tot +
          531 * K_ro := hmSchedKC_cost_le S K_on K_ro
  refine le_trans
    (letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     bindV_cost_le (N := 500 + K_on * 40) _ _ (hSched _) ?_)
    (by simp only [ahsfRecvCount, ahsfMkSaltCache, v, Expr.cost]; omega)
  cases opk <;>
  · simp only [finErasedE, letV, eMap, eCaseOpt, natEq, nat2Eq, nat3Eq,
      ahsfRecvCount, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asAdvKeys, stMk, stUpd, oeOpkSk, oeOpkPk, oeMk, oeUpd,
      aNone, aRecvHonest, aRecvUnfresh, cost_letC, v, Comp.cost, Expr.cost,
      bits_0, bits_1, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

theorem hmRecvTailKC_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmRecvTailKC S K_on K_ro opk (Δ := Δ) jt fhst mst x d).queries
        (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  change (AuthCoreKArmsBase.hmRecvTailKC S K_on K_ro opk (Δ := Δ) jt fhst mst x d).queries
    hm_zP hm_r64S ≤ 2
  rw [hm_hmRecvTailKC_r64]; decide

theorem hmRecvTailKC_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmRecvTailKC S K_on K_ro opk (Δ := Δ) jt fhst mst x d).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤
      25 + 4 * min K_on S.N_dh + 10 * min K_on S.N_sess_tot := by
  have h := hm_hmRecvTailKC_queries_tight S K_on K_ro opk (Δ := Δ) jt fhst mst x d
  change (AuthCoreKArmsBase.hmRecvTailKC S K_on K_ro opk (Δ := Δ) jt fhst mst x d).queries
    primW primWS ≤ _
  omega

theorem hmRecvTailKC_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmRecvTailKC S K_on K_ro opk (Δ := Δ) jt fhst mst x d).size ≤
      12000 + 30 * bits K_on + 10 * bits K_ro := by
  have h := hm_hmRecvTailKC_size_tight S K_on K_ro opk (Δ := Δ) jt fhst mst x d
  unfold hmRecvTailKC; omega

theorem hmRecvTailKC_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    compLitSize (hmRecvTailKC S K_on K_ro opk (Δ := Δ) jt fhst mst x d) ≤ 4000 := by
  have h := hm_hmRecvTailKC_litSize_tight S K_on K_ro opk (Δ := Δ) jt fhst mst x d
  unfold hmRecvTailKC; omega

@[local simp] private theorem hm_koskSenderOkC_r64 (S : Setup) (K : ℕ) {Γ Δ : List PT}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).queries hm_zP hm_r64S = 0 := by
  simp [koskSenderOkC, letV, bindV, Comp.queries]

@[local simp] private theorem hm_hmRecvPrepC_r64 (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (hmRecvPrepC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ (.opt hmRecvDataTy)).queries
      hm_zP hm_r64S = 0 := by
  cases opk <;>
    simp [hmRecvPrepC, letV, bindV, caseOptV, caseSumV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_hmRecvKC_r64 (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (AuthCoreKArmsBase.hmRecvKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).queries hm_zP hm_r64S = 0 := by
  simp [AuthCoreKArmsBase.hmRecvKC, bindV, caseOptV, Comp.queries]

set_option linter.unusedSimpArgs false in
private theorem hm_hmRecvPrepC_cost_le (S : Setup) (K : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (hmRecvPrepC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ (.opt hmRecvDataTy)).cost ≤
      7000 + K * 300 + min K S.N_dh * 420 := by
  cases opk <;>
  · simp only [hmRecvPrepC, koskSenderOkC_cost, optU32Eq_cost, kyberCheckE_cost, buildSecretsE_cost,
      findHonestC, bindV, letV, caseOptV, caseSumV, findMV, eFind, eAny, eCaseOpt,
      natEq, nat2Eq, nat3Eq, isSomeE, ahsfHybrid, ahsBase, ahsRecvKemRecs, ahsMk, ahsUpd,
      ahsInitKemRecs, ahsIdealSessions, asPrincipals, asSpkBundles, asOpkEntries, asUsedRecvOPK,
      asUsedRecvNoOPK, asUsedKyberTriples, peSecIKA0, peIkAPk, sbSpkSk, sbPqspkSk, sbPqspkPk,
      oeOpkSk, oeOpkPk, oeConsumed, rkrMk, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId,
      hdrKemCt, pkmHdr, pkmEphAPk, cost_u32OfNat, cost_u32Beq, cost_letC, cost_queryPrim,
      cost_bytesLen, cost_bytesBeq, cost_boolOr, _root_.SignalPqxdh.LegacyCosted.Ty.wd, v,
      Comp.cost, Expr.cost, PNat.val_ofNat, bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
private theorem hm_hmRecvPrepC_queries_le (S : Setup) (K : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (hmRecvPrepC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ (.opt hmRecvDataTy)).queries
      primW primWS ≤ 8 + 4 * min K S.N_dh := by
  cases opk <;>
  · simp only [hmRecvPrepC, koskSenderOkC_queries, findHonestC, bindV, letV, caseOptV, caseSumV,
      findMV, Comp.iteC, queries_letC, queryPrim, primW, primWS, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
private theorem hm_hmRecvPrepC_size_le (S : Setup) (K : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (hmRecvPrepC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ (.opt hmRecvDataTy)).size ≤
      4500 + 12 * bits K := by
  cases opk <;>
  · simp only [hmRecvPrepC, koskSenderOkC, findHonestC, isAdvRegC, optU32Eq, kyberCheckE, kyberEq,
      buildSecretsE, natEq, nat2Eq, nat3Eq, boolOr, isSomeE, eLet2, rkrMk,
      ahsfHybrid, ahsBase, ahsRecvKemRecs, ahsInitKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
      asPrincipals, asSpkBundles, asOpkEntries, asUsedRecvOPK, asUsedRecvNoOPK,
      asUsedKyberTriples, asAdvKeys, peCorrupted, peIkAPk, peSecIKA0, sbSpkSk, sbPqspkPk,
      sbPqspkSk, oeOpkSk, oeOpkPk, oeConsumed, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?,
      hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listCons, Expr.findBounded, Expr.anyBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM,
      v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
      _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV, findMV, anyMV,
      eLet, eCaseOpt, eFind, eAny, litB, catB, widenB, bytesLen, bytesBeq, u32OfNat, u32Beq,
      queryPrim, Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, id_eq]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      pqBytesOps, pqU32Ops, Sum.elim]
    have hmdh : bits (min K S.N_dh) ≤ bits K := hm_bits_mono (Nat.min_le_left _ _)
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
private theorem hm_hmRecvPrepC_litSize_le (S : Setup) (K : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (hmRecvPrepC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ (.opt hmRecvDataTy)) ≤
      500 := by
  cases opk <;>
  · simp only [hmRecvPrepC, koskSenderOkC, findHonestC, isAdvRegC, optU32Eq, kyberCheckE, kyberEq,
      buildSecretsE, natEq, nat2Eq, nat3Eq, boolOr, isSomeE, eLet2, rkrMk,
      ahsfHybrid, ahsBase, ahsRecvKemRecs, ahsInitKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
      asPrincipals, asSpkBundles, asOpkEntries, asUsedRecvOPK, asUsedRecvNoOPK,
      asUsedKyberTriples, asAdvKeys, peCorrupted, peIkAPk, peSecIKA0, sbSpkSk, sbPqspkPk,
      sbPqspkSk, oeOpkSk, oeOpkPk, oeConsumed, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?,
      hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listCons, Expr.findBounded, Expr.anyBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM,
      v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
      _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV, findMV, anyMV,
      eLet, eCaseOpt, eFind, eAny, litB, catB, widenB, bytesLen, bytesBeq, u32OfNat, u32Beq,
      queryPrim, compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_cons, List.length_replicate, hm_F_X25519_length,
      Nat.add_zero, Nat.zero_add, ↓reduceIte, Bool.false_eq_true, id_eq]
    omega

theorem hmRecvKC_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmRecvKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).cost ≤
      16200 + 1469 * K_on + 630 * min K_on S.N_dh + 7350 * min K_on S.N_sess_tot + 531 * K_ro := by
  unfold hmRecvKC AuthCoreKArmsBase.hmRecvKC
  have hTail : ∀ {Δ' : List (Ty pqSig)} [Ext Γ₁ Δ'] [Ext Γ₂ Δ'] [Ext Γ₃ Δ'] [Ext Γ₄ Δ']
      (d : Var Δ' hmRecvDataTy),
      (AuthCoreKArmsBase.hmRecvTailKC S K_on K_ro opk (Δ := Δ') jt fhst mst x d).cost ≤
        9000 + 1119 * K_on + 210 * min K_on S.N_dh + 7350 * min K_on S.N_sess_tot + 531 * K_ro :=
    fun d => hmRecvTailKC_cost_le S K_on K_ro opk jt fhst mst x d
  refine le_trans
    (bindV_cost_le _ _ (hm_hmRecvPrepC_cost_le S K_on opk fhst x) <|
     caseOptV_cost_le _ _ _
       (by simp only [aNone, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, v, Comp.cost, Expr.cost,
             bits_1]; exact le_rfl)
       (bindV_cost_le _ _ (hTail .zero) (by simp only [v, Comp.cost, Expr.cost]; exact le_rfl)))
    (by simp only [v, Expr.cost]; omega)

theorem hmRecvKC_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmRecvKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  change (AuthCoreKArmsBase.hmRecvKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).queries
    hm_zP hm_r64S ≤ 2
  rw [hm_hmRecvKC_r64]; decide

theorem hmRecvKC_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmRecvKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤
      30 + 10 * min K_on S.N_dh + 10 * min K_on S.N_sess_tot := by
  unfold hmRecvKC AuthCoreKArmsBase.hmRecvKC
  change (bindV _ _).queries primW primWS ≤ _
  refine le_trans
    (hm_bindV_queries_le _ _ (hm_hmRecvPrepC_queries_le S K_on opk fhst x) <|
     hm_caseOptV_queries_le _ _ _
       (by simp only [Comp.queries]; exact le_rfl)
       (hm_bindV_queries_le _ _ (hm_hmRecvTailKC_queries_tight S K_on K_ro opk jt fhst mst x .zero)
         (by simp only [Comp.queries]; exact le_rfl)))
    (by omega)

theorem hmRecvKC_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmRecvKC S K_on K_ro opk (Δ := Δ) jt fhst mst x).size ≤
      16000 + 40 * bits K_on + 10 * bits K_ro := by
  unfold hmRecvKC AuthCoreKArmsBase.hmRecvKC
  refine le_trans
    (hm_bindV_size_le _ _ (hm_hmRecvPrepC_size_le S K_on opk fhst x) <|
     hm_caseOptV_size_le _ _ _
       (by simp only [aNone, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, v, Comp.size, Expr.size,
             bits_1]; exact le_rfl)
       (hm_bindV_size_le _ _ (hm_hmRecvTailKC_size_tight S K_on K_ro opk jt fhst mst x .zero)
         (by simp only [v, Comp.size, Expr.size]; exact le_rfl)))
    (by simp only [v, Expr.size]; omega)

theorem hmRecvKC_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    compLitSize (hmRecvKC S K_on K_ro opk (Δ := Δ) jt fhst mst x) ≤ 5000 := by
  unfold hmRecvKC AuthCoreKArmsBase.hmRecvKC
  refine le_trans
    (hm_bindV_litSize_le _ _ (hm_hmRecvPrepC_litSize_le S K_on opk fhst x) <|
     hm_caseOptV_litSize_le _ _ _
       (by simp only [aNone, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, v, compLitSize,
             exprLitSize]; exact le_rfl)
       (hm_bindV_litSize_le _ _ (hm_hmRecvTailKC_litSize_tight S K_on K_ro opk jt fhst mst x .zero)
         (by simp only [v, compLitSize, exprLitSize]; exact le_rfl)))
    (by simp only [v, exprLitSize]; omega)

end HmBranchBounds

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCostHm

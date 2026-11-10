/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Auth.Game
public import Computational.Specifications.Assumptions.KemCorrect

/-!
# The one-key first-message `Auth` statement (Lemma 1, second conjunct)

**Trusted: the statement.** Every definition in this file is part of
`SignalPqxdh.Security.PqxdhAuth1KeySecureδ`, the second conjunct of `PqxdhSecureδ` in Lemma 1
(`SignalPqxdh.Security.PqxdhCorrectAndSecureδ`, `Security/HeadlineDelta.lean`). Read it alongside
the game in `Security/Auth/Game.lean`, the shared `ReductionDsl` tables and budgets in
`Security/Headline.lean` and `CostedBudgets.lean`, and `KemCorrect.lean`. See
`Computational/docs/TRUSTED_BASE.md`.

This file extends the 11-tag handshake primitive interface with the 8 first-message ratcheting and
AEAD operations (`AuthPTag`), defines the `ReductionDsl` challenger interfaces and `authSpec S`
game codec over `pqAtomicSig`, and states that a costed seven-reduction family (`sig`, `shcr`,
`gdh`, `ck`, `mk`, `cpa`, `int`) bounds `Auth1KeyAdvantage` by `pqxdhAuthAdvantageBoundδ` under
both the uniform (`stepCostBudget`) and online/random-oracle split (`stepCostBudgetSplit`)
step-cost budgets.
-/

@[expose] public section

set_option autoImplicit false

/-! ## Challenger interfaces and game codec -/

namespace SignalPqxdh.Costed

open _root_.ReductionDsl (
  Ty Iface GameCodec
  bundleT bundleV bundleOfV
  hdrT hdrV hdrOfV
  drKeyT drKeyV drKeyOfV
  dhSecretsT
)
open OracleSpec OracleComp

local notation "PT" => Ty pqAtomicSig

/-- Representation of 80-byte `MessageKeys` `(cipherKey, macKey, iv)` in `pqAtomicSig`. -/
@[reducible] def msgKeysT : PT := .prod (PB 32) (.prod (PB 32) (PB 16))

def msgKeysV (k : MessageKeys) : msgKeysT.denote := (k.cipherKey, k.macKey, k.iv)
def msgKeysOfV (v : msgKeysT.denote) : MessageKeys := ⟨v.1, v.2.1, v.2.2⟩

/-- Tags for the 8 first-message primitive queries in `SignalPqxdh.PrimQuery` beyond the 11
    handshake tags of `PTag`. -/
inductive FirstMsgPTag where
  | rootCreateChain
  | chainKdfSeed
  | chainKdfNext
  | spqrInitSend (p c : ℕ+)
  | spqrInitRecv (p c : ℕ+)
  | deriveMsgKeys (s : ℕ+)
  | aeadEnc (a m c : ℕ+)
  | aeadDec (a c m : ℕ+)
  deriving DecidableEq

@[reducible] def FirstMsgPTag.dom : FirstMsgPTag → PT
  | .rootCreateChain => .prod (PB 32) (PB 32)
  | .chainKdfSeed | .chainKdfNext => PB 32
  | .spqrInitSend _ _ => .prod (PB 32) (PB 32)
  | .spqrInitRecv _ c => .prod (PB 32) (PB c)
  | .deriveMsgKeys s => .prod (PB 32) (.opt (PB s))
  | .aeadEnc a m _ => .prod msgKeysT (.prod (PB a) (PB m))
  | .aeadDec a c _ => .prod msgKeysT (.prod (PB a) (PB c))

@[reducible] def FirstMsgPTag.cod : FirstMsgPTag → PT
  | .rootCreateChain => .prod (PB 32) (PB 32)
  | .chainKdfSeed | .chainKdfNext => PB 32
  | .spqrInitSend p c => .opt (.prod (PB p) (.prod (.opt (PB 32)) (PB c)))
  | .spqrInitRecv p _ => .opt (.prod (PB p) (.opt (PB 32)))
  | .deriveMsgKeys _ => msgKeysT
  | .aeadEnc _ _ c => PB c
  | .aeadDec _ _ m => .opt (PB m)

def FirstMsgPTag.enc : (t : FirstMsgPTag) → t.dom.denote → PrimQuery
  | .rootCreateChain, (rk, dh) => .rootCreateChain rk dh
  | .chainKdfSeed, ck => .chainKdfSeed ck
  | .chainKdfNext, ck => .chainKdfNext ck
  | .spqrInitSend _ _, (p, r) => .spqrInitSend p r
  | .spqrInitRecv _ _, (p, m) => .spqrInitRecv p m
  | .deriveMsgKeys _, (k, s) => .deriveMsgKeys k s
  | .aeadEnc _ _ _, (k, ad, pt) => .aeadEnc (msgKeysOfV k) ad pt
  | .aeadDec _ _ _, (k, ad, ct) => .aeadDec (msgKeysOfV k) ad ct

def FirstMsgPTag.dec : (t : FirstMsgPTag) → (x : t.dom.denote) → primSpec (t.enc x) → t.cod.denote
  | .rootCreateChain, _, r | .chainKdfSeed, _, r | .chainKdfNext, _, r
  | .spqrInitSend _ _, _, r | .spqrInitRecv _ _, _, r
  | .aeadEnc _ _ _, _, r | .aeadDec _ _ _, _, r => r
  | .deriveMsgKeys _, _, r => msgKeysV r

/-- Nominal byte-width query cost `1 + wd(dom) + wd(cod)` of each first-message primitive tag. -/
def FirstMsgPTag.qCost : FirstMsgPTag → ℕ
  | .rootCreateChain => 129
  | .chainKdfSeed | .chainKdfNext => 65
  | .spqrInitSend p c => 97 + p.val + c.val
  | .spqrInitRecv p c => 65 + p.val + c.val
  | .deriveMsgKeys s => 113 + s.val
  | .aeadEnc a m c => 81 + a.val + m.val + c.val
  | .aeadDec a c m => 81 + a.val + c.val + m.val

/-- Combined 19-tag primitive vocabulary (`PTag ⊕ FirstMsgPTag`) for `Auth` reductions. -/
abbrev AuthPTag : Type := PTag ⊕ FirstMsgPTag

@[reducible] def AuthPTag.dom : AuthPTag → PT
  | .inl t => t.dom (ℓ := 0) (Pt := Empty)
  | .inr t => t.dom

@[reducible] def AuthPTag.cod : AuthPTag → PT
  | .inl t => t.cod (ℓ := 0) (Pt := Empty)
  | .inr t => t.cod

def AuthPTag.enc : (t : AuthPTag) → t.dom.denote → PrimQuery
  | .inl t, x => t.enc (ℓ := 0) (Pt := Empty) x
  | .inr t, x => t.enc x

def AuthPTag.dec : (t : AuthPTag) → (x : t.dom.denote) → primSpec (t.enc x) → t.cod.denote
  | .inl t, x, r => t.dec (ℓ := 0) (Pt := Empty) x r
  | .inr t, x, r => t.dec x r

def AuthPTag.qCost : AuthPTag → ℕ
  | .inl t => t.qCost
  | .inr t => t.qCost

/-- Primitive target interface on `PrimBaseSpec` for the `shcr`, `ck`, and `cpa` reductions. -/
@[reducible] def pqAuthPrimIface : Iface pqAtomicSig PrimBaseSpec where
  fwdU n := query (spec := PrimBaseSpec) (.inl n)
  uCost := 1
  Tag := AuthPTag
  dom := AuthPTag.dom
  cod := AuthPTag.cod
  enc t x := .inr (t.enc x)
  dec t x r := t.dec x r
  qCost := AuthPTag.qCost
  smp := pqAtomicSamplers

/-- Challenger oracle specification over `pqAtomicSig` with nominal per-tag query costs. -/
structure ChallengerOracle where
  ι : Type
  spec : OracleSpec.{0, 0} ι
  Tag : Type
  dom : Tag → PT
  cod : Tag → PT
  enc : (t : Tag) → (dom t).denote → ι
  dec : (t : Tag) → (x : (dom t).denote) → spec (enc t x) → (cod t).denote
  qCost : Tag → ℕ

/-- Target interface on `PrimBaseSpec + C.spec` over `AuthPTag ⊕ C.Tag` and `pqAtomicSamplers`. -/
@[reducible] def pqAuthChalIface (C : ChallengerOracle) : Iface pqAtomicSig (PrimBaseSpec + C.spec) where
  fwdU n := query (spec := PrimBaseSpec + C.spec) (.inl (.inl n))
  uCost := 1
  Tag := AuthPTag ⊕ C.Tag
  dom | .inl t => t.dom | .inr t => C.dom t
  cod | .inl t => t.cod | .inr t => C.cod t
  enc | .inl t, x => .inl (.inr (t.enc x)) | .inr t, x => .inr (C.enc t x)
  dec | .inl t, x, r => t.dec x r | .inr t, x, r => C.dec t x r
  qCost | .inl t => t.qCost | .inr t => C.qCost t
  smp := pqAtomicSamplers

/-- Joint signing-and-DDH challenger oracle (`sigAndDdhSpec`): `.inl m` signs an `m`-byte message
    (`qCost = 65 + m`) and `.inr ()` tests DDH on three 32-byte keys (`qCost = 97`). -/
def sigAndDdhOracle : ChallengerOracle where
  ι := SigQuery ⊕ DdhQuery
  spec := sigAndDdhSpec
  Tag := ℕ+ ⊕ Unit
  dom | .inl m => PB m | .inr () => .prod (PB 32) (.prod (PB 32) (PB 32))
  cod | .inl _ => PB 64 | .inr () => .bool
  enc | .inl _, msg => .inl (.sign msg) | .inr (), x => .inr x
  dec | .inl _, _, r => r | .inr (), _, r => r
  qCost | .inl m => 65 + m.val | .inr () => 97

/-- Maps an optional raw SPQR salt to the 32-byte `PrfMsgKeys` salt key via
    `effectiveHkdfSaltBytes` (DEV-LS25). -/
def saltKeyEnc (salt? : Option Bytes) : PrfMsgKeysQuery := .derive (effectiveHkdfSaltBytes salt?)

/-- Nominal 32-byte output cost of `saltKeyEnc`. -/
def saltKeyEncCost : ℕ := 32

/-- Message-key PRF challenger oracle (`prfMsgKeysSpec`): encodes an optional `s`-byte salt via
    `saltKeyEnc` and returns 80-byte `MessageKeys` (`qCost = 113 + s`). -/
def msgKeyPrfOracle : ChallengerOracle where
  ι := PrfMsgKeysQuery
  spec := prfMsgKeysSpec
  Tag := ℕ+
  dom := fun s => .opt (PB s)
  cod := fun _ => msgKeysT
  enc := fun _ salt? => saltKeyEnc salt?
  dec := fun _ _ r => msgKeysV r
  qCost := fun s => 113 + s.val

/-- HMAC PRF challenger oracle (`prfHmacSpec`): evaluates on an `m`-byte MAC input and returns a
    32-byte tag (`qCost = 33 + m`). -/
def hmacPrfOracle : ChallengerOracle where
  ι := PrfHmacQuery
  spec := prfHmacSpec
  Tag := ℕ+
  dom := fun m => PB m
  cod := fun _ => PB 32
  enc := fun _ msg => .eval msg
  dec := fun _ _ r => r
  qCost := fun m => 33 + m.val

abbrev pqAuthSigAndDdhIface := pqAuthChalIface sigAndDdhOracle
abbrev pqPrfMkIface := pqAuthChalIface msgKeyPrfOracle
abbrev pqPrfHmacIface := pqAuthChalIface hmacPrfOracle

/-- Representation of `PreKeyMsg` `(hdr, ephAPk, pqRatchetMsg, aeadCt)` in `pqAtomicSig`. -/
@[reducible] def preKeyMsgT : PT :=
  .prod (hdrT (ℓ := 0) (Pt := Empty)) (.prod (PB 32) (.prod (PB 32) (PB 32)))

def preKeyMsgV (m : PreKeyMsg) : preKeyMsgT.denote :=
  (hdrV (ℓ := 0) (Pt := Empty) m.hdr, (m.ephAPk, (m.pqRatchetMsg, m.aeadCt)))
def preKeyMsgOfV (v : preKeyMsgT.denote) : PreKeyMsg :=
  ⟨hdrOfV (ℓ := 0) (Pt := Empty) v.1, v.2.1, v.2.2.1, v.2.2.2⟩

/-- Sum-of-products representation of `AuthQuery S` (12 constructors) in `pqAtomicSig`. -/
@[reducible] def authQT : PT :=
  .sum .nat (.sum .nat (.sum (.prod .nat .nat) (.sum (.prod .nat (.prod .nat .nat))
  (.sum (.prod .nat (.prod .nat (.prod (bundleT (ℓ := 0) (Pt := Empty)) (.prod (PB 32) (PB 32)))))
  (.sum (.prod .nat (.prod .nat (.prod (bundleT (ℓ := 0) (Pt := Empty)) (.prod (PB 32) (PB 32)))))
  (.sum (.prod .nat (.prod .nat (.prod .nat preKeyMsgT)))
  (.sum (.prod .nat (.prod .nat (.prod .nat preKeyMsgT)))
  (.sum (PB 192) (.sum (.prod (PB 32) (PB 32)) (.sum .unit (PB 32)))))))))))

def authQenc {S : Setup} : AuthQuery S → authQT.denote
  | .initPrin u => .inl u.val
  | .corruptIK u => .inr (.inl u.val)
  | .genSPK u j => .inr (.inr (.inl (u.val, j.val)))
  | .genOPK u j o => .inr (.inr (.inr (.inl (u.val, (j.val, o.val)))))
  | .sendOPK u i b m0 m1 =>
    .inr (.inr (.inr (.inr (.inl (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) b, (m0, m1))))))))
  | .sendNoOPK u i b m0 m1 =>
    .inr (.inr (.inr (.inr (.inr (.inl (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) b, (m0, m1)))))))))
  | .recvOPK k j o msg =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inl (k.val, (j.val, (o.val, preKeyMsgV msg)))))))))
  | .recvNoOPK k j l msg =>
    .inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inl (k.val, (j.val, (l.val, preKeyMsgV msg))))))))))
  | .roQuery sec =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sec))))))))
  | .roRootQuery rk dh =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (rk, dh))))))))))
  | .revealDhSecrets =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))))
  | .registerKey sk =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr sk))))))))))

/-- Sum-of-products representation of `AuthResponse` (12 constructors) in `pqAtomicSig`. -/
@[reducible] def authRT : PT :=
  .sum .unit (.sum (.prod (PB 32) (PB 32)) (.sum (PB 32) (.sum (.prod (PB 32) (PB 32))
  (.sum (bundleT (ℓ := 0) (Pt := Empty)) (.sum preKeyMsgT
  (.sum (.prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod (PB 32) (.prod (PB 32) preKeyMsgT)))
  (.sum .unit (.sum (.prod (drKeyT (ℓ := 0) (Pt := Empty)) (.prod (PB 32) (.prod (PB 32) (PB 32))))
  (.sum (drKeyT (ℓ := 0) (Pt := Empty))
    (.sum (.prod (PB 32) (PB 32)) (dhSecretsT (ℓ := 0) (Pt := Empty))))))))))))

def authRdec : authRT.denote → AuthResponse
  | .inl () => .noneResp
  | .inr (.inl (ik, s)) => .initPrinResp ik s
  | .inr (.inr (.inl pk)) => .pkResp pk
  | .inr (.inr (.inr (.inl (ik, s)))) => .corrResp ik s
  | .inr (.inr (.inr (.inr (.inl b)))) => .bundleResp (bundleOfV (ℓ := 0) (Pt := Empty) b)
  | .inr (.inr (.inr (.inr (.inr (.inl m))))) => .sendFreshResp (preKeyMsgOfV m)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (dk, (rk, (ck, m))))))))) =>
    .sendUnfreshResp (drKeyOfV (ℓ := 0) (Pt := Empty) dk) rk ck (preKeyMsgOfV m)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))) => .recvHonestResp
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (dk, (rk, (ck, pt))))))))))) =>
    .recvUnfreshResp (drKeyOfV (ℓ := 0) (Pt := Empty) dk) rk ck pt
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl dk))))))))) =>
    .drKeyResp (drKeyOfV (ℓ := 0) (Pt := Empty) dk)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (rk, ck))))))))))) =>
    .rootKdfResp rk ck
  | .inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inr (.inr (.inr (.inr (l1, (l2, (l3, l4))))))))))))) =>
    .dhSecretsResp l1 l2 l3 l4

/-- Game codec for `authSpec S` over `pqAtomicSig`; `codecCost = 32` bounds the constructor
    nesting depth and node count (`≤ 21`) of `authQenc` and `authRdec`. -/
def authCodec (S : Setup) : GameCodec pqAtomicSig (authSpec S) where
  Q := authQT
  R := authRT
  qenc := authQenc
  rdec := fun _ r => authRdec r
  codecCost := 32

end SignalPqxdh.Costed

namespace SignalPqxdh.Security

open scoped ENNReal
open SignalPqxdh
open _root_.ReductionDsl (Ty CostedReduction TwoStageCostedReduction Mid)
open SignalPqxdh.Costed

/-! ## Advantage bound under δ-correct KEM -/

/-- Advantage bound for `Auth` under a δ-correct KEM: `pqxdhAuthBound` plus a single
    `kemDecapsFailureTerm S δ` across all KEM decapsulations in the game. -/
noncomputable def pqxdhAuthAdvantageBoundδ (S : Setup) (q_roRoot : ℕ) (δ : ℝ≥0∞)
    (epsSig epsKemShCr epsGapDh epsPrfCk epsPrfMsgKeys epsAeadCpa epsPrfHmac : ℝ≥0∞) : ℝ≥0∞ :=
  pqxdhAuthBound S q_roRoot epsSig epsKemShCr epsGapDh epsPrfCk epsPrfMsgKeys epsAeadCpa
      epsPrfHmac +
    kemDecapsFailureTerm S δ

/-! ## Query weights and reduction families -/

/-- Unit primitive-query weight on `AuthPTag`. -/
def authPrimIfacePrimQueryWeight : AuthPTag → ℕ := fun _ => 1

/-- Primitive-query weight on `AuthPTag ⊕ ChalTag` (1 on `AuthPTag`, 0 on `ChalTag`). -/
def authChalIfacePrimQueryWeight {ChalTag : Type} : AuthPTag ⊕ ChalTag → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Signing-query weight on `pqAuthSigAndDdhIface` (1 on `.inr (.inl _)`, 0 otherwise). -/
def authChalIfaceSigQueryWeight : AuthPTag ⊕ (ℕ+ ⊕ Unit) → ℕ
  | .inr (.inl _) => 1
  | _ => 0

/-- DDH-query weight on `pqAuthSigAndDdhIface` (1 on `.inr (.inr ())`, 0 otherwise). -/
def authChalIfaceDdhQueryWeight : AuthPTag ⊕ (ℕ+ ⊕ Unit) → ℕ
  | .inr (.inr ()) => 1
  | _ => 0

/-- Semantic DDH-query budget for the `sig` and `gdh` reductions in `Auth`: bilinear
    random-oracle-by-session consistency checks (`(4 · M_ro + M_root) · M_sess`) plus distinct
    session-pair checks (`3 · M_sess · (M_sess - 1)`), capped at `5 · q_total²`, together with
    `q_total + N_dh + N_sess_tot` final-extraction queries. Because only online queries create
    sessions, `M_sess` is clamped at `min (min b.q_on b.q_total) S.N_sess_tot`. -/
def authGdhQueryBudget (S : Setup) (b : QueryBudget) : Nat :=
  let M_ro := min b.q_ro b.q_total
  let M_root := min b.q_roRoot b.q_total
  let M_sess := min (min b.q_on b.q_total) S.N_sess_tot
  min (5 * b.q_total ^ 2)
      ((4 * M_ro + M_root) * M_sess + 3 * M_sess * (M_sess - 1)) +
    b.q_total + S.N_dh + S.N_sess_tot

/-- Semantic reduction family for one-key first-message authentication and privacy: maps each
    `b`-bounded `AuthAdversary S` to adversaries against `GapSigEufCma`, `KemShCr`,
    `GapDhWithSign`, `PrfChainKey`, `PrfMsgKeys`, `AeadIndCpa`, and `PrfHmac`. -/
structure Auth1KeyReductionFamily (S : Setup) where
  mk' ::
  sig  : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → GapSigEufCmaAdv
  shcr : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → KemShCrAdv
  gdh  : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → GapDhWithSignAdv
  ck   : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → PrfCkAdv
  mk   : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → PrfMsgKeysAdv
  cpa  : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → AeadIndCpaAdv
  int  : (b : QueryBudget) → BoundedAdv (AuthAdversary S) b → PrfHmacAdv

/-- Syntactic `ReductionDsl` counterparts of `Auth1KeyReductionFamily S` over `pqAtomicOps` and
    `authCodec S`: `sig` and `gdh` target `pqAuthSigAndDdhIface`, `mk` and `int` target
    `pqPrfMkIface` and `pqPrfHmacIface`, and `shcr`, `ck`, and `cpa` target `pqAuthPrimIface`. -/
structure Auth1KeyCostedReductionFamily (S : Setup) where
  mk' ::
  sig  : QueryBudget → CostedReduction pqAtomicOps pqAuthSigAndDdhIface (authSpec S) (authCodec S)
           (PB 32) .unit .bool (.prod (PB 1569) (PB 64))
  shcr : QueryBudget → TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
           (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
           (.prod (PB 32) (PB 1568)) (PB 1568)
  gdh  : QueryBudget → CostedReduction pqAtomicOps pqAuthSigAndDdhIface (authSpec S) (authCodec S)
           (.prod (PB 32) (PB 32)) .unit .bool (PB 32)
  ck   : QueryBudget → CostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
           (.prod (PB 32) (PB 32)) .unit .bool .bool
  mk   : QueryBudget → CostedReduction pqAtomicOps pqPrfMkIface (authSpec S) (authCodec S)
           .unit .unit .bool .bool
  cpa  : QueryBudget → TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
           .unit .unit .bool (.prod (PB 158) (.prod (PB 32) (PB 32)))
           (.opt (PB 32)) .bool
  int  : QueryBudget → CostedReduction pqAtomicOps pqPrfHmacIface (authSpec S) (authCodec S)
           .unit .unit .bool .bool

/-- Evaluates an `Auth1KeyCostedReductionFamily S` into a semantic `Auth1KeyReductionFamily S`
    with fuel `b.q_total`, default output `false`, signing budget `2 * min S.N_spk_tot S.N_recv`,
    DDH budget `authGdhQueryBudget S b`, and PRF budgets `1` (`ck`) and `S.N_recv_tot + 1`
    (`mk`, `int`). -/
def Auth1KeyCostedReductionFamily.eval {S : Setup} (R : Auth1KeyCostedReductionFamily S) :
    Auth1KeyReductionFamily S where
  sig b A :=
    { run := fun pk => (R.sig b).eval (fun _ => A.1.run) pk
      q_sig := 2 * min S.N_spk_tot S.N_recv
      q_ddh := authGdhQueryBudget S b
      q_prim := gdhPrimQueryBudget S b }
  shcr b A :=
    { State := Mid (authSpec S) Bool (R.shcr b).π.denote (R.shcr b).σ.denote (PB 1568).denote
      choosePk := fun pk sk =>
        (R.shcr b).eval1 (fun _ => A.1.run) (pk, sk) b.q_total false
      findCollision := fun st ss ct =>
        (R.shcr b).eval2 st (ss, ct) b.q_total false
      q_prim := primQueryBudget S b }
  gdh b A :=
    { run := fun U V => (R.gdh b).eval (fun _ => A.1.run) (U, V)
      q_ddh := authGdhQueryBudget S b
      q_sig := 2 * min S.N_spk_tot S.N_recv
      q_prim := gdhPrimQueryBudget S b }
  ck b A :=
    { dist := fun mkSeedChal ck1_1Chal =>
        (R.ck b).eval (fun _ => A.1.run) (mkSeedChal, ck1_1Chal)
      q_prf := 1
      q_prim := primQueryBudget S b }
  mk b A :=
    { run := (R.mk b).eval (fun _ => A.1.run) ()
      q_prf := S.N_recv_tot + 1
      q_prim := primQueryBudget S b }
  cpa b A :=
    { State := Mid (authSpec S) Bool (R.cpa b).π.denote (R.cpa b).σ.denote
        (Ty.prod (PB 158) (Ty.prod (PB 32) (PB 32))).denote
      choose := do
        let r ← (R.cpa b).eval1 (fun _ => A.1.run) () b.q_total false
        pure (r.1.1, r.1.2.1, r.1.2.2, r.2)
      dist := fun st c? =>
        (R.cpa b).eval2 st c? b.q_total false
      q_prim := primQueryBudget S b }
  int b A :=
    { run := (R.int b).eval (fun _ => A.1.run) ()
      q_prf := S.N_recv_tot + 1
      q_prim := primQueryBudget S b }

/-- Classifies `AuthQuery` into online queries (`0`, matching `isAuthOnlineQuery`) and offline
    random-oracle queries `.roQuery` and `.roRootQuery` (`1`) for per-kind step-cost accounting. -/
def authQueryKind {S : Setup} : AuthQuery S → Fin 2
  | .roQuery _       => 1
  | .roRootQuery _ _ => 1
  | _                => 0

/-- Per-kind query caps for a `b`-bounded `AuthAdversary`: `min b.q_on b.q_total` online queries
    (`0`) and `min (b.q_ro + b.q_roRoot) b.q_total` random-oracle queries (`1`). -/
def authKindCounts (b : QueryBudget) : Fin 2 → ℕ
  | 0 => min b.q_on b.q_total
  | 1 => min (b.q_ro + b.q_roRoot) b.q_total

/-- Syntactic resource bounds for an `Auth1KeyCostedReductionFamily S`: operator and sampler
    size-honesty, uniform (`stepCostBudget`) and online/random-oracle split (`stepCostBudgetSplit`)
    step-cost bounds, worst-case query bounds over `b.q_total` handled queries, and run-local
    output block-size bounds via `GRedBlockBounded` / `GRed2BlockBounded`. -/
structure Auth1KeyCostedReductionBounds (S : Setup) (R : Auth1KeyCostedReductionFamily S) :
    Prop where
  ops_sizeHonest  : PqOpsSizeHonest pqAtomicOps
  samp_sizeHonest : PqSampSizeHonest pqAtomicSamplers
  sig_cost        : ∀ (b : QueryBudget), (R.sig b).totalCost b.q_total ≤ stepCostBudget S b
  shcr_cost       : ∀ (b : QueryBudget), (R.shcr b).totalCost b.q_total ≤ stepCostBudget S b
  gdh_cost        : ∀ (b : QueryBudget), (R.gdh b).totalCost b.q_total ≤ stepCostBudget S b
  ck_cost         : ∀ (b : QueryBudget), (R.ck b).totalCost b.q_total ≤ stepCostBudget S b
  mk_cost         : ∀ (b : QueryBudget), (R.mk b).totalCost b.q_total ≤ stepCostBudget S b
  cpa_cost        : ∀ (b : QueryBudget), (R.cpa b).totalCost b.q_total ≤ stepCostBudget S b
  int_cost        : ∀ (b : QueryBudget), (R.int b).totalCost b.q_total ≤ stepCostBudget S b
  sig_q_sig       : ∀ (b : QueryBudget),
    (R.sig b).totalQueries authChalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤
      2 * b.q_total
  sig_q_ddh       : ∀ (b : QueryBudget),
    (R.sig b).totalQueries authChalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  sig_q_prim      : ∀ (b : QueryBudget),
    (R.sig b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b
  shcr_q_prim     : ∀ (b : QueryBudget),
    (R.shcr b).totalQueries authPrimIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b
  gdh_q_sig       : ∀ (b : QueryBudget),
    (R.gdh b).totalQueries authChalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤
      2 * b.q_total
  gdh_q_ddh       : ∀ (b : QueryBudget),
    (R.gdh b).totalQueries authChalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  gdh_q_prim      : ∀ (b : QueryBudget),
    (R.gdh b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b
  ck_q_prim       : ∀ (b : QueryBudget),
    (R.ck b).totalQueries authPrimIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b
  mk_q_prim       : ∀ (b : QueryBudget),
    (R.mk b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b
  cpa_q_prim      : ∀ (b : QueryBudget),
    (R.cpa b).totalQueries authPrimIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b
  int_q_prim      : ∀ (b : QueryBudget),
    (R.int b).totalQueries authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤
      primQueryBudget S b
  sig_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.sig b)
  shcr_blocks     : ∀ (b : QueryBudget) (ℓ : Nat), GRed2BlockBounded S b ℓ (R.shcr b)
  gdh_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.gdh b)
  ck_blocks       : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.ck b)
  mk_blocks       : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.mk b)
  cpa_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRed2BlockBounded S b ℓ (R.cpa b)
  int_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.int b)
  sig_costByKind  : ∀ (b : QueryBudget),
    (R.sig b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot))
  shcr_costByKind : ∀ (b : QueryBudget),
    (R.shcr b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot))
  gdh_costByKind  : ∀ (b : QueryBudget),
    (R.gdh b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot))
  ck_costByKind   : ∀ (b : QueryBudget),
    (R.ck b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot))
  mk_costByKind   : ∀ (b : QueryBudget),
    (R.mk b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot))
  cpa_costByKind  : ∀ (b : QueryBudget),
    (R.cpa b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot))
  int_costByKind  : ∀ (b : QueryBudget),
    (R.int b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot))

/-- Semantic query-budget compliance for an `Auth1KeyReductionFamily S`: every component
    reduction adversary satisfies its `.Bounded` predicate for all `b` and `A`. -/
structure Auth1KeyReductionQueryBounds (S : Setup) (R : Auth1KeyReductionFamily S) : Prop where
  sig_bounded  : ∀ b A, (R.sig b A).Bounded
  shcr_bounded : ∀ b A, (R.shcr b A).Bounded
  gdh_bounded  : ∀ b A, (R.gdh b A).Bounded
  ck_bounded   : ∀ b A, (R.ck b A).Bounded
  mk_bounded   : ∀ b A, (R.mk b A).Bounded
  cpa_bounded  : ∀ b A, (R.cpa b A).Bounded
  int_bounded  : ∀ b A, (R.int b A).Bounded

/-! ## One-key `Auth` security statement -/

/-- Advantage-reduction bound for `R : Auth1KeyReductionFamily S`: for every δ-correct
    well-formed primitive suite `P` and `b`-bounded adversary `A`, `Auth1KeyAdvantage S P A.1`
    is bounded by `pqxdhAuthAdvantageBoundδ` evaluated at the seven component advantages of `R`. -/
def PqxdhAuth1KeyReductionBoundδ (S : Setup) (R : Auth1KeyReductionFamily S) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (δ : ℝ≥0∞), KemDeltaCorrect P δ →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      Auth1KeyAdvantage S P A.1 ≤
        pqxdhAuthAdvantageBoundδ S b.q_roRoot δ
          (GapSigEufCma P P.isValidDhTriple (R.sig b A))
          (KemShCr P (R.shcr b A))
          (GapDhWithSign P P.isValidDhTriple P.pow8 (R.gdh b A))
          (PrfChainKey P (R.ck b A))
          (PrfMsgKeys P (R.mk b A))
          (AeadIndCpa P (R.cpa b A))
          (PrfHmac P (R.int b A))

/-- One-key first-message authentication and privacy at setup `S` under a δ-correct KEM: there
    exists a costed reduction family `R : Auth1KeyCostedReductionFamily S` that satisfies syntactic
    resource bounds, semantic query bounds, and `PqxdhAuth1KeyReductionBoundδ S R.eval`. -/
def PqxdhAuth1KeySecureδ (S : Setup) : Prop :=
  ∃ R : Auth1KeyCostedReductionFamily S,
    Auth1KeyCostedReductionBounds S R ∧
    Auth1KeyReductionQueryBounds S R.eval ∧
    PqxdhAuth1KeyReductionBoundδ S R.eval

end SignalPqxdh.Security

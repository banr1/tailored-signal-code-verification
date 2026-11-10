/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.CostedTables -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.MacroLift -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SizeBudgetBridge -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.ClampsLossless -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.M3Interfaces -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.E2EStateRepr -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.FreshnessSim -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.StartAndExtSmAux -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.StartAndExtSm -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.M3Subprograms -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync


/-!
# Auxiliary Lifters and Encodings for `HaltedPrefixSubprogs`

Defines per-session `KemFailSessionTrack` DSL encodings and exact `e2eOps → atomicE2EOps` and
`e2eSessionTargetIface` expression and computation lifters for `HaltedPrefixSubprogs`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.HaltedPrefixSubprogsAux

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp UniformSamplerTag bits iterM
  findML anyML mapML consumeFirstML foldML
  partyToBool bytesToWordLE spqrMsgPayloadSuffix atomicSig atomicE2EOps atomicBaseSamplers
  e2eSessionTargetIface AtomicPureOp AtomicCurveCheckOp AtomicSpqrKemOp
  B BV256 BV512 U32 U64 recvResultEnc)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState ShaCompress)
open CryptoGames.Ratchet.LibsignalSim (simInitKemFailTrack)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State)
open CryptoVerification.E2E (Bytes BHE2EDrvState SampledSessionKey bhE2EGuard bhE2EFinishStartSpk
  bhKeySOf bhBytesWord)
open CryptoVerification.E2E.Costed (E2EPureOp E2ECurveCheckOp E2ECryptoOp E2EUnifBase E2ESessionTag
  e2eSig e2eOps e2eSamplers)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (liftSort liftTy liftCtx liftVal liftVal_heq liftVar liftEnv liftEnv_get
   renExpr renComp wk1Ren wk1Expr wk1Expr_cost wk1Expr_eval
   wk1Comp wk1Comp_queries wk1Comp_cost wk1Comp_eval
   readProstVarint_eq splitSpqrPrev_eq)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_succ_le)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (KemFailTrackState KemFailSessionTrack initKemFailTrack initKemFailSessionTrack)

/-! ## `KemFailSessionTrack` types and encodings -/

@[expose, reducible] def kemCoinsT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .sum .unit (.sum (BV512 (ℓ := ℓ) (Pt := Pt)) (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))

@[expose, reducible] def kemSentEntryT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.prod (U64 (ℓ := ℓ) (Pt := Pt)) (B (ℓ := ℓ) (Pt := Pt) 64)) (U32 (ℓ := ℓ) (Pt := Pt))

@[expose, reducible] def kemTrackT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (U64 (ℓ := ℓ) (Pt := Pt))
    (.prod (kemCoinsT ℓ Pt)
      (.prod (.prod (B (ℓ := ℓ) (Pt := Pt) 32) (B (ℓ := ℓ) (Pt := Pt) 32))
        (.prod (.list (kemSentEntryT ℓ Pt))
          (.prod (.prod (.tbl .nat) (.tbl .nat))
            (.opt (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))))))

@[expose, reducible] def honestWireEntryT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (B (ℓ := ℓ) (Pt := Pt) 32) .bool

@[expose, reducible] def sessHTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (kemTrackT ℓ Pt) (.list (honestWireEntryT ℓ Pt))

@[expose, reducible] def kemCoinsBridgeAtomicEnc {ℓ : ℕ} {Pt : Type} :
    CryptoVerification.SpqrV1Sync.Braid.Coins → (kemCoinsT ℓ Pt).denote
  | .init => .inl ()
  | .seed s => .inr (.inl (bytesToWordLE 512 s.toList))
  | .both s r => .inr (.inr (bytesToWordLE 512 s.toList, bytesToWordLE 256 r.toList))

@[expose, reducible] def kemTrackBridgeAtomicEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (tr : KemFailTrackState F) : (kemTrackT ℓ Pt).denote :=
  (tr.e,
   (kemCoinsBridgeAtomicEnc tr.c,
    ((V1State.encodeRaw (tr.st .A).into_pb, V1State.encodeRaw (tr.st .B).into_pb),
     (tr.sentB.map (fun (m, ctr) => ((m.epoch, spqrMsgPayloadSuffix m), ctr)),
      ((tr.sendCtr .A, tr.sendCtr .B),
       tr.cand.map fun p => (bytesToWordLE 512 p.1.toList, bytesToWordLE 256 p.2.toList))))))

@[expose, reducible] def sessHEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (st : KemFailSessionTrack F Bytes) : (sessHTy ℓ Pt).denote :=
  (kemTrackBridgeAtomicEnc st.1, st.2.map fun (w, P) => (w, partyToBool P))

/-! ## Expression and computation lifters -/

private theorem renExpr_size {S₀ : Sig} {O₀ : Ops S₀} {Γ₁ Γ₂ : List (Ty S₀)} {t : Ty S₀}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (e : Expr O₀ Γ₁ t) : (renExpr f e).size = e.size := by
  induction e generalizing Γ₂ <;> simp [renExpr, Expr.size, *]

@[simp] theorem wk1Expr_size {S₀ : Sig} {O₀ : Ops S₀} {a b : Ty S₀} {Γ : List (Ty S₀)}
    (e : Expr O₀ [a] b) : (wk1Expr (Γ := Γ) e).size = e.size := renExpr_size wk1Ren e

private theorem renComp_size {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ₁ Γ₂ : List (Ty S₀)} {t : Ty S₀}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O₀ I₀ Γ₁ t) : (renComp f c).size = c.size := by
  induction c generalizing Γ₂ <;> simp [renComp, Comp.size, renExpr_size, *]

@[simp] theorem wk1Comp_size {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {a b : Ty S₀} {Γ : List (Ty S₀)}
    (c : Comp O₀ I₀ [a] b) : (wk1Comp (Γ := Γ) c).size = c.size := renComp_size wk1Ren c

private theorem renComp_queries_any {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ₁ Γ₂ : List (Ty S₀)} {t : Ty S₀}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O₀ I₀ Γ₁ t)
    (w : I₀.Tag → ℕ) (ws : I₀.smp.Samp → ℕ) :
    (renComp f c).queries w ws = c.queries w ws := by
  induction c generalizing Γ₂ <;> simp [renComp, Comp.queries, *]

@[simp] theorem wk1Comp_queries_any {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {a b : Ty S₀} {Γ : List (Ty S₀)}
    (c : Comp O₀ I₀ [a] b) (w : I₀.Tag → ℕ) (ws : I₀.smp.Samp → ℕ) :
    (wk1Comp (Γ := Γ) c).queries w ws = c.queries w ws := renComp_queries_any wk1Ren c w ws

@[expose] def castDen {S₀ : Sig} {t₁ t₂ : Ty S₀} (h : t₁ = t₂) (x : t₁.denote) : t₂.denote := h ▸ x

@[simp] private theorem castDen_symm_castDen {S₀ : Sig} {t₁ t₂ : Ty S₀}
    (h : t₁ = t₂) (x : t₁.denote) : castDen h.symm (castDen h x) = x := by cases h; rfl

private theorem castDen_liftVal_eq {ℓ : ℕ} {Pt : Type} {t : Ty (e2eSig ℓ)}
    {t' : Ty (atomicSig ℓ Pt)} (h : liftTy (Pt := Pt) t = t')
    (hD : t'.denote = t.denote) (x : t.denote) :
    castDen h (liftVal (Pt := Pt) x) = cast hD.symm x := by
  have h1 : HEq (castDen h (liftVal (Pt := Pt) x)) (liftVal (Pt := Pt) x) := by cases h; rfl
  exact eq_of_heq ((h1.trans (liftVal_heq (Pt := Pt) x)).trans (cast_heq hD.symm x).symm)

theorem liftVal_eq_id {ℓ : ℕ} {Pt : Type} {t : Ty (e2eSig ℓ)}
    (hD : (liftTy (Pt := Pt) t).denote = t.denote := by rfl) (x : t.denote) :
    liftVal (Pt := Pt) x = cast hD.symm x :=
  eq_of_heq ((liftVal_heq (Pt := Pt) x).trans (cast_heq hD.symm x).symm)

@[expose] def castExpr {S₀ : Sig} {O₀ : Ops S₀} {Γ : List (Ty S₀)} {t₁ t₂ : Ty S₀}
    (h : t₁ = t₂) (e : Expr O₀ Γ t₁) : Expr O₀ Γ t₂ := h ▸ e

@[simp] theorem castExpr_cost {S₀ : Sig} {O₀ : Ops S₀} {Γ : List (Ty S₀)} {t₁ t₂ : Ty S₀}
    (h : t₁ = t₂) (e : Expr O₀ Γ t₁) : (castExpr h e).cost = e.cost := by cases h; rfl

@[simp] theorem castExpr_size {S₀ : Sig} {O₀ : Ops S₀} {Γ : List (Ty S₀)} {t₁ t₂ : Ty S₀}
    (h : t₁ = t₂) (e : Expr O₀ Γ t₁) : (castExpr h e).size = e.size := by cases h; rfl

private theorem castExpr_eval {S₀ : Sig} {O₀ : Ops S₀} {Γ : List (Ty S₀)} {t₁ t₂ : Ty S₀}
    (h : t₁ = t₂) (e : Expr O₀ Γ t₁) (ρ : Env Γ) :
    (castExpr h e).eval ρ = castDen h (e.eval ρ) := by cases h; rfl

@[expose] def castComp {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι} {I₀ : Iface S₀ T}
    {Γ : List (Ty S₀)} {t₁ t₂ : Ty S₀} (h : t₁ = t₂) (c : Comp O₀ I₀ Γ t₁) : Comp O₀ I₀ Γ t₂ := h ▸ c

@[simp] theorem castComp_cost {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {t₁ t₂ : Ty S₀} (h : t₁ = t₂) (c : Comp O₀ I₀ Γ t₁) :
    (castComp h c).cost = c.cost := by cases h; rfl

@[simp] theorem castComp_size {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {t₁ t₂ : Ty S₀} (h : t₁ = t₂) (c : Comp O₀ I₀ Γ t₁) :
    (castComp h c).size = c.size := by cases h; rfl

@[simp] theorem castComp_queries {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {t₁ t₂ : Ty S₀} (h : t₁ = t₂) (c : Comp O₀ I₀ Γ t₁)
    (w : I₀.Tag → ℕ) (ws : I₀.smp.Samp → ℕ) :
    (castComp h c).queries w ws = c.queries w ws := by cases h; rfl

private theorem castComp_eval {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {t₁ t₂ : Ty S₀}
    (h : t₁ = t₂) (c : Comp O₀ I₀ Γ t₁) (ρ : Env Γ) :
    (castComp h c).eval ρ = castDen h <$> c.eval ρ := by cases h; exact (id_map (c.eval ρ)).symm

private theorem partyToBool_eq (p : Party) :
    partyToBool p = CryptoVerification.E2E.Costed.partyToBool p := by cases p <;> rfl

private theorem boolToParty_eq (b : Bool) :
    _root_.ReductionDsl.boolToParty b = CryptoVerification.E2E.Costed.boolToParty b := by cases b <;> rfl

@[expose] def liftPureOp : E2EPureOp → AtomicPureOp
  | .pbytesLit w v => .pbytesLit w v | .pbytesCat m n => .pbytesCat m n
  | .pbytesCons b w => .pbytesCons b w | .pbytesWiden w d => .pbytesWiden w d
  | .pbytesTakeK w k => .pbytesTakeK w k | .pbytesTake w => .pbytesTake w
  | .pbytesDrop w => .pbytesDrop w | .pbytesLen w => .pbytesLen w | .pbytesEq m n => .pbytesEq m n
  | .bytesLit w v => .bytesLit w v | .bytesCat m n => .bytesCat m n
  | .bytesCons b w => .bytesCons b w | .bytesWiden w d => .bytesWiden w d
  | .bytesTakeK w k => .bytesTakeK w k | .bytesTake w => .bytesTake w
  | .bytesDrop w => .bytesDrop w | .bytesLen w => .bytesLen w | .bytesEq m n => .bytesEq m n
  | .bytesLtOp m n => .bytesLtOp m n | .pbytesToBytes w => .pbytesToBytes w
  | .bytesToPbytes w => .bytesToPbytes w | .pu32Lit k => .pu32Lit k | .pu32OfNat => .pu32OfNat
  | .pu32ToNat => .pu32ToNat | .pu32Eq => .pu32Eq | .pu32ToU32 => .pu32ToU32
  | .u32ToPu32 => .u32ToPu32 | .u8Lit v => .u8Lit v | .u8OfNat => .u8OfNat | .u8ToNat => .u8ToNat
  | .u8Eq => .u8Eq | .u8Lt => .u8Lt | .u32Lit v => .u32Lit v | .u32OfNat => .u32OfNat
  | .u32ToNat => .u32ToNat | .u32Eq => .u32Eq | .u32Lt => .u32Lt | .u32Add => .u32Add
  | .u32Sub => .u32Sub | .u32BeBytes => .u32BeBytes | .u64Lit v => .u64Lit v
  | .u64OfNat => .u64OfNat | .u64ToNat => .u64ToNat | .u64Eq => .u64Eq | .u64Lt => .u64Lt
  | .u64Add => .u64Add | .u64Sub => .u64Sub | .u64Trunc8 => .u64Trunc8 | .finVal n => .finVal n
  | .finEq n => .finEq n | .bv128Eq => .bv128Eq | .bv256Lit v => .bv256Lit v
  | .bv256Eq => .bv256Eq | .bv256ToPbytes32 => .bv256ToPbytes32
  | .pbytesToBv256 => .pbytesToBv256 | .bv256ToBytes32 => .bv256ToBytes32
  | .bytesToBv256 => .bytesToBv256 | .bv512Lit v => .bv512Lit v
  | .bv512ToBytes64 => .bv512ToBytes64 | .idKeyOfPbytes => .idKeyOfPbytes
  | .idKeySerialize => .idKeySerialize | .idKeyEq => .idKeyEq | .pkOfPbytes => .pkOfPbytes
  | .pkDeserialize => .pkDeserialize | .pkSerialize => .pkSerialize | .pkEq => .pkEq
  | .plainDefault => .plainDefault | .plainToBytes => .plainToBytes
  | .bytesToPlain => .bytesToPlain | .plainEq => .plainEq
  | .checkShortCiphertext => .checkShortCiphertext | .parsePreKeyWire => .parsePreKeyWire
  | .partneredInnerBytes => .partneredInnerBytes | .wireInnerBytes => .wireInnerBytes
  | .splitWhisperWire => .splitWhisperWire | .isValidSignalWire => .isValidSignalWire
  | .signalMsgParse => .signalMsgParse | .wrapWhisperWire => .wrapWhisperWire
  | .wrapPreKeyWire => .wrapPreKeyWire | .spqrParsePreamble => .spqrParsePreamble
  | .spqrAssembleMsg => .spqrAssembleMsg | .spqrStateSplit => .spqrStateSplit
  | .spqrStateJoin => .spqrStateJoin | .ghostStateSplit => .ghostStateSplit
  | .ghostStateJoin => .ghostStateJoin | .encodeSessionRecord => .encodeSessionRecord

@[expose] def liftCurveCheckOp : E2ECurveCheckOp → AtomicCurveCheckOp
  | .decEncCheck => .decEncCheck | .checkRatchetKeyOnCurve => .checkRatchetKeyOnCurve

@[expose] def liftE2EOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    (e2eOps ℓ P C K decT encT).Op → (atomicE2EOps ℓ P C K decT encT).Op
  | .inl o => .inl (.inl (liftPureOp o))
  | .inr (.inl cc) => .inl (.inr (liftCurveCheckOp cc))
  | .inr (.inr c) => match c with
    | .x25519 => .inr (.inr (.inr (.inr .x25519))) | .x25519Base => .inr (.inr (.inr (.inr .x25519Base)))
    | .pow8 => .inr (.inr (.inr (.inr .pow8))) | .isCanonical => .inr (.inr (.inr (.inr .isCanonical)))
    | .sigSign => .inr (.inr (.inr (.inr .sigSign))) | .sigVerify => .inr (.inr (.inr (.inr .sigVerify)))
    | .kemKeyGen => .inr (.inr (.inr (.inr .kemKeyGen))) | .kemEncaps => .inr (.inr (.inr (.inr .kemEncaps)))
    | .kemDecaps => .inr (.inr (.inr (.inr .kemDecaps))) | .hkdfDerive96 => .inr (.inr (.inr (.inr .hkdfDerive96)))
    | .sessionKeyPairGen => .inr (.inr (.inl .sessionKeyPairGen))
    | .sessionRootCreateChain => .inr (.inr (.inl .sessionRootCreateChain))
    | .chainStep => .inr (.inr (.inl .chainStep)) | .deriveMsgKeys => .inr (.inr (.inl .deriveMsgKeys))
    | .aes256CbcEnc => .inr (.inr (.inl .aes256CbcEnc)) | .aes256CbcDec => .inr (.inr (.inl .aes256CbcDec))
    | .signalMsgEncode => .inr (.inr (.inl .signalMsgEncode))
    | .signalMsgVerifyMac => .inr (.inr (.inl .signalMsgVerifyMac))
    | .spqrV1InitOp => .inr (.inr (.inr (.inl .spqrV1InitOp)))
    | .spqrNegotiateInit => .inr (.inr (.inr (.inl .spqrNegotiateInit)))
    | .spqrBraidSend => .inr (.inr (.inr (.inl .spqrBraidSend)))
    | .spqrBraidRecv => .inr (.inr (.inr (.inl .spqrBraidRecv)))
    | .spqrChainFromVn => .inr (.inr (.inr (.inl .spqrChainFromVn)))
    | .spqrChainAddEpoch => .inr (.inr (.inr (.inl .spqrChainAddEpoch)))
    | .spqrChainNextKey => .inr (.inr (.inr (.inl .spqrChainNextKey)))

theorem liftE2EOp_dom {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op) :
    liftTy (Pt := Pt) ((e2eOps ℓ P C K decT encT).dom o) =
      (atomicE2EOps ℓ P C K decT encT).dom (liftE2EOp (Pt := Pt) o) := by
  rcases o with o | cc | c <;> [cases o <;> rfl; cases cc <;> rfl; cases c <;> rfl]

theorem liftE2EOp_cod {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op) :
    liftTy (Pt := Pt) ((e2eOps ℓ P C K decT encT).cod o) =
      (atomicE2EOps ℓ P C K decT encT).cod (liftE2EOp (Pt := Pt) o) := by
  rcases o with o | cc | c <;> [cases o <;> rfl; cases cc <;> rfl; cases c <;> rfl]

theorem liftE2EOp_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).cost (liftE2EOp (Pt := Pt) o) =
      (e2eOps ℓ P C K decT encT).cost o := by
  rcases o with o | cc | c <;> [cases o <;> rfl; cases cc <;> rfl; cases c <;> rfl]

private theorem liftE2EOp_opSize {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).opSize (liftE2EOp (Pt := Pt) o) =
      (e2eOps ℓ P C K decT encT).opSize o := by
  rcases o with o | cc | c <;> [cases o <;> rfl; cases cc <;> rfl; cases c <;> rfl]

private theorem list_find_map {α β : Type} (g : α → β) (q : β → Bool) (p : α → Bool)
    (hpq : ∀ x, q (g x) = p x) :
    ∀ xs : List α, (xs.map g).find? q = (xs.find? p).map g
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.find?_cons, hpq x]
    cases p x
    · exact list_find_map g q p hpq xs
    · rfl

private theorem list_any_map_eq {α β : Type} (g : α → β) (q : β → Bool) (p : α → Bool)
    (hpq : ∀ x, q (g x) = p x) :
    ∀ xs : List α, (xs.map g).any q = xs.any p
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.any_cons, hpq x, list_any_map_eq g q p hpq xs]

private theorem list_map_map_eq {α β γ δ : Type} (g : α → β) (h : γ → δ)
    (f' : β → δ) (f : α → γ) (hfg : ∀ x, f' (g x) = h (f x)) :
    ∀ xs : List α, (xs.map g).map f' = (xs.map f).map h
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, hfg x, list_map_map_eq g h f' f hfg xs]

private theorem list_foldr_map_eq {α β γ δ : Type} (g : α → β) (h : γ → δ)
    (f' : β → δ → δ) (f : α → γ → γ) (hf : ∀ x acc, f' (g x) (h acc) = h (f x acc)) (z : γ) :
    ∀ xs : List α, (xs.map g).foldr f' (h z) = h (xs.foldr f z)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.foldr_cons, list_foldr_map_eq g h f' f hf z xs, hf x]

private theorem atomic_e2eDecodePreKeyMsg_eq (c : Bytes) :
    _root_.ReductionDsl.e2eDecodePreKeyMsg c =
      CryptoVerification.E2E.Costed.e2eDecodePreKeyMsg c := by
  have hraw : _root_.ReductionDsl.e2eDecodePreKeyRaw c =
      CryptoVerification.E2E.Costed.e2eDecodePreKeyRaw c := by
    unfold _root_.ReductionDsl.e2eDecodePreKeyRaw CryptoVerification.E2E.Costed.e2eDecodePreKeyRaw
      _root_.ReductionDsl.e2eParseOptPreKeyId CryptoVerification.E2E.Costed.e2eParseOptPreKeyId
      _root_.ReductionDsl.e2eParseDjbKeyField CryptoVerification.E2E.Costed.e2eParseDjbKeyField
      _root_.ReductionDsl.e2eParseInnerMsgField CryptoVerification.E2E.Costed.e2eParseInnerMsgField
      _root_.ReductionDsl.e2eParseUint32Field CryptoVerification.E2E.Costed.e2eParseUint32Field
      _root_.ReductionDsl.e2eParseKyberCtField CryptoVerification.E2E.Costed.e2eParseKyberCtField
    rw [readProstVarint_eq]
    rfl
  unfold _root_.ReductionDsl.e2eDecodePreKeyMsg CryptoVerification.E2E.Costed.e2eDecodePreKeyMsg
  rw [hraw]
  rfl

private theorem atomic_spqrChainToV_eq (ℓ : ℕ) (Pt : Type)
    (c : CryptoVerification.LibsignalSpqrV1.ChainPB) :
    _root_.ReductionDsl.spqrChainToV (ℓ := ℓ) (Pt := Pt) c =
      CryptoVerification.E2E.Costed.spqrChainToV (ℓ := ℓ) c := by
  have hdir : _root_.ReductionDsl.spqrDirToV (ℓ := ℓ) (Pt := Pt) =
      CryptoVerification.E2E.Costed.spqrDirToV (ℓ := ℓ) := by
    funext d
    dsimp only [_root_.ReductionDsl.spqrDirToV, CryptoVerification.E2E.Costed.spqrDirToV]
    rw [splitSpqrPrev_eq]
  dsimp only [_root_.ReductionDsl.spqrChainToV, CryptoVerification.E2E.Costed.spqrChainToV]
  rw [hdir]
  rfl

private theorem atomic_spqrSplitEval_eq (ℓ : ℕ) (Pt : Type) (x : Bytes) :
    _root_.ReductionDsl.spqrSplitEval (ℓ := ℓ) (Pt := Pt) x =
      CryptoVerification.E2E.Costed.spqrSplitEval (ℓ := ℓ) x := by
  unfold _root_.ReductionDsl.spqrSplitEval CryptoVerification.E2E.Costed.spqrSplitEval
  have hvn : _root_.ReductionDsl.spqrVnToV (ℓ := ℓ) (Pt := Pt) =
      CryptoVerification.E2E.Costed.spqrVnToV (ℓ := ℓ) := by
    funext vn; cases vn.chainParams <;> rfl
  have hch : _root_.ReductionDsl.spqrChainToV (ℓ := ℓ) (Pt := Pt) =
      CryptoVerification.E2E.Costed.spqrChainToV (ℓ := ℓ) :=
    funext (atomic_spqrChainToV_eq ℓ Pt)
  rw [hvn, hch]
  cases CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState x with
  | error _ => rfl
  | ok st =>
    cases st.inner with
    | none => rfl
    | some i => cases i; rfl

private theorem atomic_spqrJoinEval_eq (ℓ : ℕ) (Pt : Type)
    (x : (CryptoVerification.E2E.Costed.spqrStatePartsT (ℓ := ℓ)).denote) :
    _root_.ReductionDsl.spqrJoinEval (ℓ := ℓ) (Pt := Pt) x =
      CryptoVerification.E2E.Costed.spqrJoinEval (ℓ := ℓ) x := by
  rcases x with ⟨v1?, vn?, ch?⟩
  unfold _root_.ReductionDsl.spqrJoinEval CryptoVerification.E2E.Costed.spqrJoinEval
  dsimp only
  apply congrArg (List.take (32 * 11000))
  rcases v1? with _ | _ <;> rcases vn? with _ | _ <;> rcases ch? with _ | _ <;> rfl

private theorem atomic_e2eEncodeSessionRecord_eq (ℓ : ℕ) (Pt : Type)
    (x : ((CryptoVerification.E2E.Costed.e2ePureOps ℓ).dom .encodeSessionRecord).denote) :
    _root_.ReductionDsl.e2eEncodeSessionRecord (ℓ := ℓ) (Pt := Pt) x =
      CryptoVerification.E2E.Costed.e2eEncodeSessionRecord (ℓ := ℓ) x := by
  rcases x with ⟨⟨regIdA, regIdB, bobReg, hdr⟩, g⟩
  have hex : _root_.ReductionDsl.e2eRecordExtras = CryptoVerification.E2E.Costed.e2eRecordExtras := by
    funext rA rB bR h p; cases p <;> rfl
  have hbs :
      CryptoVerification.E2E.binStateOfUnderExtras
        (_root_.ReductionDsl.e2eRecordExtras regIdA regIdB bobReg
          (_root_.ReductionDsl.hdrOfV (ℓ := ℓ) (Pt := Pt) hdr)) g =
      CryptoVerification.E2E.binStateOfUnderExtras
        (CryptoVerification.E2E.Costed.e2eRecordExtras regIdA regIdB bobReg
          (CryptoVerification.E2E.Costed.hdrOfV (ℓ := ℓ) hdr)) g := by
    rw [hex]; rfl
  exact congrArg (fun bs : CryptoVerification.E2E.BinState =>
    { bs with bytes := bs.bytes.take (32 * 24000) }) hbs

private theorem liftPureOp_domD (ℓ : ℕ) (Pt : Type) (o : E2EPureOp) :
    ((_root_.ReductionDsl.atomicPureOps ℓ Pt).dom (liftPureOp o)).denote =
      ((CryptoVerification.E2E.Costed.e2ePureOps ℓ).dom o).denote := by
  cases o <;> rfl

private theorem liftPureOp_codD (ℓ : ℕ) (Pt : Type) (o : E2EPureOp) :
    ((_root_.ReductionDsl.atomicPureOps ℓ Pt).cod (liftPureOp o)).denote =
      ((CryptoVerification.E2E.Costed.e2ePureOps ℓ).cod o).denote := by
  cases o <;> rfl

set_option maxHeartbeats 400000 in
private theorem liftPureOp_val_eq (ℓ : ℕ) (Pt : Type) (o : E2EPureOp)
    (x : ((CryptoVerification.E2E.Costed.e2ePureOps ℓ).dom o).denote) :
    (_root_.ReductionDsl.atomicPureOps ℓ Pt).eval (liftPureOp o)
      (cast (liftPureOp_domD ℓ Pt o).symm x) =
      cast (liftPureOp_codD ℓ Pt o).symm ((CryptoVerification.E2E.Costed.e2ePureOps ℓ).eval o x) := by
  cases o
  case checkShortCiphertext => rcases x with ⟨c0, _ | i⟩ <;> rfl
  case splitWhisperWire => rcases x with _ | ⟨t, body⟩ <;> rfl
  case parsePreKeyWire =>
    exact congrArg
      (Option.map fun m =>
        (m.regId, (_root_.ReductionDsl.hdrV (_root_.ReductionDsl.e2eHdrOfPreKeyMsg m),
          m.inner.take x.length)))
      (atomic_e2eDecodePreKeyMsg_eq x)
  case partneredInnerBytes =>
    rcases x with ⟨bobAcc, regIdA, hdr, c0⟩
    change _root_.ReductionDsl.e2ePartneredInnerBytes bobAcc regIdA
        (_root_.ReductionDsl.hdrOfV hdr) c0 =
      CryptoVerification.E2E.Costed.e2ePartneredInnerBytes bobAcc regIdA
        (CryptoVerification.E2E.Costed.hdrOfV hdr) c0
    simp only [_root_.ReductionDsl.e2ePartneredInnerBytes,
      CryptoVerification.E2E.Costed.e2ePartneredInnerBytes,
      atomic_e2eDecodePreKeyMsg_eq]
    rfl
  case wireInnerBytes =>
    change _root_.ReductionDsl.e2eWireInnerBytes x =
      CryptoVerification.E2E.Costed.e2eWireInnerBytes x
    simp only [_root_.ReductionDsl.e2eWireInnerBytes,
      CryptoVerification.E2E.Costed.e2eWireInnerBytes,
      atomic_e2eDecodePreKeyMsg_eq]
    rfl
  case wrapPreKeyWire =>
    rcases x with ⟨regIdA, hdr, inner⟩
    change (if inner.isEmpty then []
        else (CryptoVerification.E2E.wirePrekey ::
          (_root_.ReductionDsl.e2eExpectedPreKeyMsg regIdA
            (_root_.ReductionDsl.hdrOfV hdr) inner).bytes).take
          (32 * (2 * (ℓ / 32) + 84))) =
      (if inner.isEmpty then []
        else (CryptoVerification.E2E.wirePrekey ::
          (CryptoVerification.E2E.Costed.e2eExpectedPreKeyMsg regIdA
            (CryptoVerification.E2E.Costed.hdrOfV hdr) inner).bytes).take
          (32 * (2 * (ℓ / 32) + 84)))
    have hexp :
        _root_.ReductionDsl.e2eExpectedPreKeyMsg regIdA
          (_root_.ReductionDsl.hdrOfV (ℓ := ℓ) (Pt := Pt) hdr) inner =
        CryptoVerification.E2E.Costed.e2eExpectedPreKeyMsg regIdA
          (CryptoVerification.E2E.Costed.hdrOfV (ℓ := ℓ) hdr) inner := rfl
    rw [hexp]
  case spqrStateSplit => exact atomic_spqrSplitEval_eq ℓ Pt x
  case spqrStateJoin => exact atomic_spqrJoinEval_eq ℓ Pt x
  case ghostStateSplit => cases x.party <;> rfl
  case ghostStateJoin => cases x.1 <;> rfl
  case encodeSessionRecord => exact atomic_e2eEncodeSessionRecord_eq ℓ Pt x
  all_goals rfl

private theorem liftE2EOp_domD {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op) :
    ((atomicE2EOps ℓ P C K decT encT).dom (liftE2EOp (Pt := Pt) o)).denote =
      ((e2eOps ℓ P C K decT encT).dom o).denote := by
  rcases o with o | cc | c
  · exact liftPureOp_domD ℓ Pt o
  · cases cc <;> rfl
  · cases c <;> rfl

private theorem liftE2EOp_codD {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op) :
    ((atomicE2EOps ℓ P C K decT encT).cod (liftE2EOp (Pt := Pt) o)).denote =
      ((e2eOps ℓ P C K decT encT).cod o).denote := by
  rcases o with o | cc | c
  · exact liftPureOp_codD ℓ Pt o
  · cases cc <;> rfl
  · cases c <;> rfl

private theorem liftE2EOp_val_eq {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op)
    (x : ((e2eOps ℓ P C K decT encT).dom o).denote) :
    (atomicE2EOps ℓ P C K decT encT).eval (liftE2EOp (Pt := Pt) o)
      (cast (liftE2EOp_domD (Pt := Pt) o).symm x) =
      cast (liftE2EOp_codD (Pt := Pt) o).symm ((e2eOps ℓ P C K decT encT).eval o x) := by
  rcases o with o | cc | c
  · exact liftPureOp_val_eq ℓ Pt o x
  · cases cc <;> rfl
  · cases c
    case spqrChainFromVn =>
      change _root_.ReductionDsl.spqrChainFromVnEval (ℓ := ℓ) (Pt := Pt) C.F x =
        CryptoVerification.E2E.Costed.spqrChainFromVnEval (ℓ := ℓ) C.F x
      unfold _root_.ReductionDsl.spqrChainFromVnEval CryptoVerification.E2E.Costed.spqrChainFromVnEval
      have hvn : _root_.ReductionDsl.spqrVnOfV (ℓ := ℓ) (Pt := Pt) x =
          CryptoVerification.E2E.Costed.spqrVnOfV (ℓ := ℓ) x := rfl
      rw [hvn]
      cases CryptoVerification.LibsignalSpqrV1.chainFromVersionNegotiation
          (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith C.F)
          (CryptoVerification.E2E.Costed.spqrVnOfV (ℓ := ℓ) x) with
      | error _ => rfl
      | ok c0 => exact congrArg some (atomic_spqrChainToV_eq ℓ Pt c0.intoPb)
    case spqrChainAddEpoch =>
      rcases x with ⟨ch, ep, sec⟩
      change _root_.ReductionDsl.spqrChainAddEpochEval (ℓ := ℓ) (Pt := Pt) C.F ch ep sec =
        CryptoVerification.E2E.Costed.spqrChainAddEpochEval (ℓ := ℓ) C.F ch ep sec
      unfold _root_.ReductionDsl.spqrChainAddEpochEval CryptoVerification.E2E.Costed.spqrChainAddEpochEval
      have hch : _root_.ReductionDsl.spqrChainOfV (ℓ := ℓ) (Pt := Pt) ch =
          CryptoVerification.E2E.Costed.spqrChainOfV (ℓ := ℓ) ch := rfl
      rw [hch]
      cases CryptoVerification.LibsignalSpqrV1.Chain.fromPb
          (CryptoVerification.E2E.Costed.spqrChainOfV (ℓ := ℓ) ch) with
      | error _ => rfl
      | ok c0 =>
        dsimp only
        cases c0.addEpoch (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith C.F)
            ⟨ep, keyToBytes32 sec⟩ with
        | error _ => rfl
        | ok c1 => exact congrArg (fun v => (false, some v)) (atomic_spqrChainToV_eq ℓ Pt c1.intoPb)
    all_goals rfl

private theorem liftE2EOp_eval_eq {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (o : (e2eOps ℓ P C K decT encT).Op)
    {Γ₂ : List (Ty (atomicSig ℓ Pt))}
    (a₂ : Expr (atomicE2EOps ℓ P C K decT encT) Γ₂ (liftTy (Pt := Pt) ((e2eOps ℓ P C K decT encT).dom o)))
    (ρ₂ : Env Γ₂) (x : ((e2eOps ℓ P C K decT encT).dom o).denote)
    (ha : a₂.eval ρ₂ = liftVal (Pt := Pt) x) :
    (castExpr (liftE2EOp_cod (Pt := Pt) o).symm
      (Expr.op (O := atomicE2EOps ℓ P C K decT encT) (liftE2EOp (Pt := Pt) o)
        (castExpr (liftE2EOp_dom (Pt := Pt) o) a₂))).eval ρ₂ =
      liftVal (Pt := Pt) ((e2eOps ℓ P C K decT encT).eval o x) := by
  rw [castExpr_eval]
  dsimp only [Expr.eval]
  rw [castExpr_eval, ha,
    castDen_liftVal_eq (liftE2EOp_dom (Pt := Pt) o) (liftE2EOp_domD (Pt := Pt) o) x,
    liftE2EOp_val_eq (Pt := Pt) o x,
    ← castDen_liftVal_eq (liftE2EOp_cod (Pt := Pt) o) (liftE2EOp_codD (Pt := Pt) o) _,
    castDen_symm_castDen]

@[expose] def liftE2EExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
      Expr (e2eOps ℓ P C K decT encT) Γ t →
      Expr (atomicE2EOps ℓ P C K decT encT) (liftCtx (Pt := Pt) Γ) (liftTy (Pt := Pt) t)
  | _, _, .var v => .var (liftVar v) | _, _, .unit => .unit
  | _, _, .bool b => .bool b | _, _, .nat n => .nat n
  | _, _, .add a b => .add (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .sub a b => .sub (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .mulK k a => .mulK k (liftE2EExpr a) | _, _, .divK k a => .divK k (liftE2EExpr a)
  | _, _, .modK k a => .modK k (liftE2EExpr a) | _, _, .not a => .not (liftE2EExpr a)
  | _, _, .lt a b => .lt (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .eqN a b => .eqN (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .and a b => .and (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .ite c a b => .ite (liftE2EExpr c) (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .pair a b => .pair (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .fst a => .fst (liftE2EExpr a) | _, _, .snd a => .snd (liftE2EExpr a)
  | _, _, .inl a => .inl (liftE2EExpr a) | _, _, .inr a => .inr (liftE2EExpr a)
  | _, _, .none => .none | _, _, .some a => .some (liftE2EExpr a)
  | _, _, .caseOpt e n s => .caseOpt (liftE2EExpr e) (liftE2EExpr n) (liftE2EExpr s)
  | _, _, .caseSum e l r => .caseSum (liftE2EExpr e) (liftE2EExpr l) (liftE2EExpr r)
  | _, _, .letE e b => .letE (liftE2EExpr e) (liftE2EExpr b)
  | _, _, .op o a =>
    castExpr (liftE2EOp_cod (Pt := Pt) o).symm
      (.op (liftE2EOp (Pt := Pt) o) (castExpr (liftE2EOp_dom (Pt := Pt) o) (liftE2EExpr a)))
  | _, _, .nil => .nil | _, _, .cons x l => .cons (liftE2EExpr x) (liftE2EExpr l)
  | _, _, .len l => .len (liftE2EExpr l) | _, _, .take n l => .take (liftE2EExpr n) (liftE2EExpr l)
  | _, _, .appendL Kb a b => .appendL Kb (liftE2EExpr a) (liftE2EExpr b)
  | _, _, .findB Kb l p => .findB Kb (liftE2EExpr l) (liftE2EExpr p)
  | _, _, .anyB Kb l p => .anyB Kb (liftE2EExpr l) (liftE2EExpr p)
  | _, _, .mapB Kb l f => .mapB Kb (liftE2EExpr l) (liftE2EExpr f)
  | _, _, .foldrB Kb l z f => .foldrB Kb (liftE2EExpr l) (liftE2EExpr z) (liftE2EExpr f)
  | _, _, .tconst a => .tconst (liftE2EExpr a)
  | _, _, .tget m i => .tget (liftE2EExpr m) (liftE2EExpr i)
  | _, _, .tset m i a => .tset (liftE2EExpr m) (liftE2EExpr i) (liftE2EExpr a)

@[simp] theorem liftE2EExpr_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ t) :
    (liftE2EExpr (Pt := Pt) e).cost = e.cost := by
  induction e <;> simp [liftE2EExpr, Expr.cost, liftE2EOp_cost, *]

@[simp] theorem liftE2EExpr_size {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ t) :
    (liftE2EExpr (Pt := Pt) e).size = e.size := by
  induction e <;> simp [liftE2EExpr, Expr.size, liftE2EOp_opSize, *]

theorem liftE2EExpr_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ t) (ρ : Env Γ) :
    (liftE2EExpr (Pt := Pt) e).eval (liftEnv (Pt := Pt) ρ) = liftVal (Pt := Pt) (e.eval ρ) := by
  induction e with
  | var v => exact liftEnv_get ρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add a b iha ihb | sub a b iha ihb | lt a b iha ihb | eqN a b iha ihb | and a b iha ihb
  | pair a b iha ihb | cons a b iha ihb | tget a b iha ihb =>
    simp only [liftE2EExpr, Expr.eval, iha ρ, ihb ρ]; rfl
  | mulK _ a iha | divK _ a iha | modK _ a iha | not a iha
  | inl a iha | inr a iha | some a iha | tconst a iha =>
    simp only [liftE2EExpr, Expr.eval, iha ρ]; rfl
  | ite c a b ihc iha ihb =>
    simp only [liftE2EExpr, Expr.eval, ihc ρ]; cases c.eval ρ <;> [exact ihb ρ; exact iha ρ]
  | fst a iha | snd a iha =>
    simp only [liftE2EExpr, Expr.eval, iha ρ]; rcases a.eval ρ with ⟨_, _⟩; rfl
  | caseOpt e n s ihe ihn ihs =>
    simp only [liftE2EExpr, Expr.eval, ihe ρ]; rcases e.eval ρ with _ | x <;> [exact ihn ρ; exact ihs (.cons x ρ)]
  | caseSum e l r ihe ihl ihr =>
    simp only [liftE2EExpr, Expr.eval, ihe ρ]; rcases e.eval ρ with x | y <;> [exact ihl (.cons x ρ); exact ihr (.cons y ρ)]
  | letE e b ihe ihb => simp only [liftE2EExpr, Expr.eval, ihe ρ]; exact ihb (.cons (e.eval ρ) ρ)
  | op o a iha => exact liftE2EOp_eval_eq o (liftE2EExpr a) (liftEnv ρ) (a.eval ρ) (iha ρ)
  | len l ihl => simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, List.length_map]
  | take n l ihn ihl => simp only [liftE2EExpr, Expr.eval, ihn ρ, ihl ρ, liftVal, List.map_take]
  | appendL Kb a b iha ihb =>
    simp only [liftE2EExpr, Expr.eval, iha ρ, ihb ρ, liftVal, ← List.map_append, List.map_take]
  | findB Kb l p ihl ihp =>
    simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_find_map liftVal _ _ (fun x => ihp (.cons x ρ)) ((l.eval ρ).take Kb)
  | anyB Kb l p ihl ihp =>
    simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_any_map_eq liftVal _ _ (fun x => ihp (.cons x ρ)) ((l.eval ρ).take Kb)
  | mapB Kb l f ihl ihf =>
    simp only [liftE2EExpr, Expr.eval, ihl ρ, liftVal, ← List.map_take]
    exact list_map_map_eq liftVal liftVal _ _ (fun x => ihf (.cons x ρ)) ((l.eval ρ).take Kb)
  | foldrB Kb l z f ihl ihz ihf =>
    simp only [liftE2EExpr, Expr.eval, ihl ρ, ihz ρ]
    change (((l.eval ρ).map liftVal).take Kb).foldr _ (liftVal (z.eval ρ)) = _
    rw [← List.map_take]
    exact list_foldr_map_eq liftVal liftVal _ _
      (fun x acc => ihf (.cons x (.cons acc ρ))) (z.eval ρ) ((l.eval ρ).take Kb)
  | tset m i a ihm ihi iha =>
    simp only [liftE2EExpr, Expr.eval, ihm ρ, ihi ρ, iha ρ]
    funext j; by_cases hj : j = i.eval ρ <;> simp [hj, liftVal]

@[expose] def liftSamp : UniformSamplerTag E2EUnifBase →
    UniformSamplerTag _root_.ReductionDsl.AtomicBaseUnif
  | .bool => .bool | .index n => .index n
  | .base .bv256 => .base .bv256 | .base .bv512 => .base .bv512

@[expose] def liftSessionTag : E2ESessionTag → _root_.ReductionDsl.E2ESessionTag
  | .tr => .tr | .ch => .ch | .dl => .dl | .ij => .ij | .cr => .cr

theorem liftSamp_sDom {ℓ : ℕ} {Pt : Type} (s : UniformSamplerTag E2EUnifBase) :
    liftTy (Pt := Pt) ((e2eSamplers ℓ).sDom s) =
      (e2eSessionTargetIface ℓ Pt).smp.sDom (liftSamp s) := by
  cases s <;> rfl

theorem liftSamp_sTy {ℓ : ℕ} {Pt : Type} (s : UniformSamplerTag E2EUnifBase) :
    liftTy (Pt := Pt) ((e2eSamplers ℓ).sTy s) =
      (e2eSessionTargetIface ℓ Pt).smp.sTy (liftSamp s) := by
  cases s with | bool | index _ => rfl | base b => cases b <;> rfl

theorem liftSessionTag_dom {ℓ : ℕ} {Pt : Type} (g : E2ESessionTag) :
    liftTy (Pt := Pt) ((CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ).dom g) =
      (e2eSessionTargetIface ℓ Pt).dom (liftSessionTag g) := by
  cases g <;> rfl

theorem liftSessionTag_cod {ℓ : ℕ} {Pt : Type} (g : E2ESessionTag) :
    liftTy (Pt := Pt) ((CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ).cod g) =
      (e2eSessionTargetIface ℓ Pt).cod (liftSessionTag g) := by
  cases g <;> rfl

/-- Lifts a `Comp` from `Costed.e2eSessionTargetIface ℓ` into `e2eSessionTargetIface ℓ Pt`. -/
@[expose] def liftSessionComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
      Comp (e2eOps ℓ P C K decT encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) Γ t →
      Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt)
        (liftCtx (Pt := Pt) Γ) (liftTy (Pt := Pt) t)
  | _, _, .ret e => .ret (liftE2EExpr e)
  | _, _, .bind c k => .bind (liftSessionComp c) (liftSessionComp k)
  | _, _, .ite b c d => .ite (liftE2EExpr b) (liftSessionComp c) (liftSessionComp d)
  | _, _, .caseOpt e n s => .caseOpt (liftE2EExpr e) (liftSessionComp n) (liftSessionComp s)
  | _, _, .caseSum e l r => .caseSum (liftE2EExpr e) (liftSessionComp l) (liftSessionComp r)
  | _, _, .sample s e =>
    castComp (I₀ := e2eSessionTargetIface ℓ Pt) (liftSamp_sTy (Pt := Pt) s).symm
      (.sample (I := e2eSessionTargetIface ℓ Pt) (liftSamp s)
        (castExpr (liftSamp_sDom (Pt := Pt) s) (liftE2EExpr e)))
  | _, _, .query g e =>
    castComp (I₀ := e2eSessionTargetIface ℓ Pt) (liftSessionTag_cod (Pt := Pt) g).symm
      (.query (I := e2eSessionTargetIface ℓ Pt) (liftSessionTag g)
        (castExpr (liftSessionTag_dom (Pt := Pt) g) (liftE2EExpr e)))
  | _, _, .iter n e body => .iter n (liftE2EExpr e) (liftSessionComp body)
  | _, _, .findM Kb l p => .findM Kb (liftE2EExpr l) (liftSessionComp p)
  | _, _, .anyM Kb l p => .anyM Kb (liftE2EExpr l) (liftSessionComp p)
  | _, _, .mapM Kb l f => .mapM Kb (liftE2EExpr l) (liftSessionComp f)
  | _, _, .consumeFirstM Kb l p mk =>
    .consumeFirstM Kb (liftE2EExpr l) (liftSessionComp p) (liftE2EExpr mk)
  | _, _, .foldM Kb l z f => .foldM Kb (liftE2EExpr l) (liftE2EExpr z) (liftSessionComp f)

@[simp] theorem liftSessionComp_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (c : Comp (e2eOps ℓ P C K decT encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) Γ t) :
    (liftSessionComp (Pt := Pt) c).cost = c.cost := by
  induction c <;> simp [liftSessionComp, Comp.cost, *]
  case sample s _ => cases s with | bool | index _ => rfl | base b => cases b <;> rfl
  case query g _ => cases g <;> rfl

@[simp] theorem liftSessionComp_size {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (c : Comp (e2eOps ℓ P C K decT encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) Γ t) :
    (liftSessionComp (Pt := Pt) c).size = c.size := by
  induction c <;> simp [liftSessionComp, Comp.size, *]

theorem liftSessionComp_queries {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (w : _root_.ReductionDsl.E2ESessionTag → ℕ)
    (ws : UniformSamplerTag _root_.ReductionDsl.AtomicBaseUnif → ℕ)
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (c : Comp (e2eOps ℓ P C K decT encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) Γ t) :
    (liftSessionComp (Pt := Pt) c).queries w ws =
      c.queries (fun g => w (liftSessionTag g)) (fun s => ws (liftSamp s)) := by
  induction c <;> simp [liftSessionComp, Comp.queries, *]

private theorem atomic_recvResultEnc_eq (ℓ : ℕ) (Pt : Type) :
    _root_.ReductionDsl.recvResultEnc (ℓ := ℓ) (Pt := Pt) =
      CryptoVerification.E2E.Costed.recvResultEnc (ℓ := ℓ) := by
  funext rr; cases rr <;> rfl

private theorem cast_oracleComp_eq_map {ι : Type} {T : OracleSpec ι} {α β : Type}
    (h : α = β) (m : OracleComp T α) :
    cast (congrArg (OracleComp T) h) m = (cast h) <$> m := by
  subst h; exact (id_map m).symm

private theorem sessionQuery_bridge {ι : Type} {T : OracleSpec ι} {ℓ : ℕ} {Pt : Type}
    {dom₁ cod₁ : Ty (e2eSig ℓ)} {dom₂ cod₂ : Ty (atomicSig ℓ Pt)}
    (hdom : liftTy (Pt := Pt) dom₁ = dom₂) (hcod : liftTy (Pt := Pt) cod₁ = cod₂)
    (hdomD : dom₂.denote = dom₁.denote) (hcodD : cod₂.denote = cod₁.denote)
    (q₁ : dom₁.denote → OracleComp T cod₁.denote)
    (q₂ : dom₂.denote → OracleComp T cod₂.denote) (x : dom₁.denote)
    (hq : q₂ (cast hdomD.symm x) = cast (congrArg (OracleComp T) hcodD.symm) (q₁ x)) :
    q₂ (castDen hdom (liftVal (Pt := Pt) x)) =
      (fun y => castDen hcod (liftVal (Pt := Pt) y)) <$> q₁ x := by
  rw [castDen_liftVal_eq hdom hdomD x, hq]
  have hFun : (fun y => castDen hcod (liftVal (Pt := Pt) y)) = cast hcodD.symm :=
    funext fun y => castDen_liftVal_eq hcod hcodD y
  rw [hFun]; exact cast_oracleComp_eq_map hcodD.symm (q₁ x)

private abbrev SessionTargetSpec (ℓ : ℕ) :=
  unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes

private theorem liftSessionTag_eval (ℓ : ℕ) (Pt : Type) (g : E2ESessionTag)
    (x : ((CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ).dom g).denote) :
    (let I₂ := e2eSessionTargetIface ℓ Pt
     let x' := castDen (liftSessionTag_dom (Pt := Pt) g) (liftVal (Pt := Pt) x)
     I₂.dec (liftSessionTag g) x' <$>
       (liftM ((SessionTargetSpec ℓ).query (I₂.enc (liftSessionTag g) x')) :
         OracleComp (SessionTargetSpec ℓ) _)) =
      (fun y => castDen (liftSessionTag_cod (Pt := Pt) g) (liftVal (Pt := Pt) y)) <$>
        (let I₁ := CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ
         I₁.dec g x <$>
           (liftM ((SessionTargetSpec ℓ).query (I₁.enc g x)) :
             OracleComp (SessionTargetSpec ℓ) _)) := by
  let I₁ := CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ
  let I₂ := e2eSessionTargetIface ℓ Pt
  cases g <;>
    refine sessionQuery_bridge (liftSessionTag_dom _) (liftSessionTag_cod _) rfl rfl
      (fun z => I₁.dec _ z <$>
        (liftM ((SessionTargetSpec ℓ).query (I₁.enc _ z)) : OracleComp (SessionTargetSpec ℓ) _))
      (fun z => I₂.dec (liftSessionTag _) z <$>
        (liftM ((SessionTargetSpec ℓ).query (I₂.enc (liftSessionTag _) z)) :
          OracleComp (SessionTargetSpec ℓ) _)) x ?_
  case tr => rcases x with ⟨p, _, _⟩; cases p <;> rfl
  case ch => rcases x with ⟨p, _, _, _⟩; cases p <;> rfl
  case dl => rcases x with ⟨p, _⟩; cases p <;> exact congrArg (fun f => Option.map f <$> _) (atomic_recvResultEnc_eq ℓ Pt)
  case ij => rcases x with ⟨p, _⟩; cases p <;> exact congrArg (fun f => Option.map f <$> _) (atomic_recvResultEnc_eq ℓ Pt)
  case cr => cases x <;> rfl

@[simp] private theorem map_id_lam {m : Type → Type} [Functor m] [LawfulFunctor m]
    {α : Type} (x : m α) : (fun a => a) <$> x = x := id_map x

private theorem iterM_map_hom {m : Type → Type} [Monad m] [LawfulMonad m] {α₁ α₂ : Type}
    (g : α₁ → α₂) (f₁ : α₁ → m α₁) (f₂ : α₂ → m α₂) (hf : ∀ a, f₂ (g a) = g <$> f₁ a) :
    ∀ (n : ℕ) (a : α₁), iterM f₂ n (g a) = g <$> iterM f₁ n a
  | 0, a => by simp [iterM]
  | n + 1, a => by
    simp only [iterM, hf a, bind_map_left, map_bind]
    exact bind_congr fun a' => iterM_map_hom g f₁ f₂ hf n a'

private theorem findML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m] {α₁ α₂ : Type}
    (g : α₁ → α₂) (p₁ : α₁ → m Bool) (p₂ : α₂ → m Bool) (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α₁, findML p₂ (xs.map g) = Option.map g <$> findML p₁ xs
  | [] => by simp [findML]
  | x :: xs => by
    simp only [List.map_cons, findML, hp x, map_bind]
    exact bind_congr fun b => by cases b; exact findML_map_hom g p₁ p₂ hp xs; simp

private theorem anyML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m] {α₁ α₂ : Type}
    (g : α₁ → α₂) (p₁ : α₁ → m Bool) (p₂ : α₂ → m Bool) (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α₁, anyML p₂ (xs.map g) = anyML p₁ xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, anyML, hp x]
    exact bind_congr fun b => by cases b; exact anyML_map_hom g p₁ p₂ hp xs; rfl

private theorem mapML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → m β₁) (f₂ : α₂ → m β₂) (hf : ∀ x, f₂ (g x) = h <$> f₁ x) :
    ∀ xs : List α₁, mapML f₂ (xs.map g) = List.map h <$> mapML f₁ xs
  | [] => by simp [mapML]
  | x :: xs => by
    simp only [List.map_cons, mapML, hf x, bind_map_left, map_bind]
    exact bind_congr fun y => by rw [mapML_map_hom g h f₁ f₂ hf xs, bind_map_left]; simp

private theorem consumeFirstML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ : Type} (g : α₁ → α₂) (p₁ : α₁ → m Bool) (p₂ : α₂ → m Bool)
    (mk₁ : α₁ → α₁) (mk₂ : α₂ → α₂)
    (hp : ∀ x, p₂ (g x) = p₁ x) (hmk : ∀ x, mk₂ (g x) = g (mk₁ x)) :
    ∀ xs : List α₁, consumeFirstML p₂ mk₂ (xs.map g) =
      (fun r : Bool × List α₁ => (r.1, r.2.map g)) <$> consumeFirstML p₁ mk₁ xs
  | [] => by simp [consumeFirstML]
  | x :: xs => by
    simp only [List.map_cons, consumeFirstML, hp x, map_bind]
    exact bind_congr fun b => by
      cases b
      · rw [consumeFirstML_map_hom g p₁ p₂ mk₁ mk₂ hp hmk xs, bind_map_left]; simp
      · simp [hmk x]

private theorem foldML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁ → m β₁) (f₂ : α₂ → β₂ → m β₂)
    (hf : ∀ x acc, f₂ (g x) (h acc) = h <$> f₁ x acc) :
    ∀ (xs : List α₁) (acc : β₁), foldML f₂ (h acc) (xs.map g) = h <$> foldML f₁ acc xs
  | [], acc => by simp [foldML]
  | x :: xs, acc => by
    simp only [List.map_cons, foldML, hf x acc, bind_map_left, map_bind]
    exact bind_congr fun acc' => foldML_map_hom g h f₁ f₂ hf xs acc'

theorem liftSessionComp_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (c : Comp (e2eOps ℓ P C K decT encT) (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) Γ t)
    (ρ : Env Γ) :
    (liftSessionComp (Pt := Pt) c).eval (liftEnv (Pt := Pt) ρ) =
      liftVal (Pt := Pt) <$> c.eval ρ := by
  have hLift : ∀ {α : Type} (p : ProbComp α),
      (e2eSessionTargetIface ℓ Pt).liftP p =
        (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ).liftP p := fun _ => rfl
  induction c with
  | ret e => simp [liftSessionComp, Comp.eval, liftE2EExpr_eval]
  | bind c k ihc ihk =>
    simp only [liftSessionComp, Comp.eval, ihc ρ, bind_map_left, map_bind]
    exact bind_congr fun x => ihk (.cons x ρ)
  | ite b c d ihc ihd =>
    simp only [liftSessionComp, Comp.eval, liftE2EExpr_eval b ρ]
    change (if b.eval ρ then _ else _) = _
    split_ifs <;> [exact ihc ρ; exact ihd ρ]
  | caseOpt e n s ihn ihs =>
    simp only [liftSessionComp, Comp.eval, liftE2EExpr_eval e ρ]
    cases e.eval ρ with | none => exact ihn ρ | some x => exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    simp only [liftSessionComp, Comp.eval, liftE2EExpr_eval e ρ]
    cases e.eval ρ with | inl x => exact ihl (.cons x ρ) | inr y => exact ihr (.cons y ρ)
  | sample s e =>
    simp only [liftSessionComp, castComp_eval, Comp.eval, hLift]
    rcases s with _ | _ | (_ | _) <;> rfl
  | query g e =>
    dsimp only [liftSessionComp]
    rw [castComp_eval]
    have hx : (castExpr (liftSessionTag_dom (Pt := Pt) g) (liftE2EExpr e)).eval (liftEnv ρ) =
        castDen (liftSessionTag_dom (Pt := Pt) g) (liftVal (Pt := Pt) (e.eval ρ)) := by
      rw [castExpr_eval, liftE2EExpr_eval]
    have hq : (Comp.query (I := e2eSessionTargetIface ℓ Pt) (liftSessionTag g)
          (castExpr (liftSessionTag_dom (Pt := Pt) g) (liftE2EExpr e))).eval (liftEnv ρ) =
        (fun y => castDen (liftSessionTag_cod (Pt := Pt) g) (liftVal (Pt := Pt) y)) <$>
          (Comp.query g e).eval ρ :=
      Eq.trans (congrArg (fun x' => (e2eSessionTargetIface ℓ Pt).dec (liftSessionTag g) x' <$>
        (liftM ((SessionTargetSpec ℓ).query
          ((e2eSessionTargetIface ℓ Pt).enc (liftSessionTag g) x')) :
            OracleComp (SessionTargetSpec ℓ) _)) hx)
        (liftSessionTag_eval ℓ Pt g (e.eval ρ))
    rw [hq, ← comp_map]
    simp only [Function.comp_def, castDen_symm_castDen]
  | iter n e body ih =>
    simp only [liftSessionComp, Comp.eval, liftE2EExpr_eval e ρ]
    exact iterM_map_hom liftVal (fun a => body.eval (.cons a ρ))
      (fun a => (liftSessionComp body).eval (.cons a (liftEnv ρ)))
      (fun a => ih (.cons a ρ)) n (e.eval ρ)
  | findM Kb l p ih =>
    simp only [liftSessionComp, Comp.eval, liftE2EExpr_eval l ρ, liftVal, ← List.map_take]
    exact findML_map_hom liftVal (fun x => p.eval (.cons x ρ))
      (fun x => (liftSessionComp p).eval (.cons x (liftEnv ρ)))
      (fun x => (ih (.cons x ρ)).trans (id_map _)) ((l.eval ρ).take Kb)
  | anyM Kb l p ih =>
    simp only [liftSessionComp, Comp.eval, liftE2EExpr_eval l ρ, liftVal, ← List.map_take, map_id_lam]
    exact anyML_map_hom liftVal (fun x => p.eval (.cons x ρ))
      (fun x => (liftSessionComp p).eval (.cons x (liftEnv ρ)))
      (fun x => (ih (.cons x ρ)).trans (id_map _)) ((l.eval ρ).take Kb)
  | mapM Kb l f ih =>
    simp only [liftSessionComp, Comp.eval, liftE2EExpr_eval l ρ, liftVal, ← List.map_take]
    exact mapML_map_hom liftVal liftVal (fun x => f.eval (.cons x ρ))
      (fun x => (liftSessionComp f).eval (.cons x (liftEnv ρ)))
      (fun x => ih (.cons x ρ)) ((l.eval ρ).take Kb)
  | consumeFirstM Kb l p mk ih =>
    simp only [liftSessionComp, Comp.eval, liftE2EExpr_eval l ρ, liftVal, ← List.map_take]
    exact consumeFirstML_map_hom liftVal (fun x => p.eval (.cons x ρ))
      (fun x => (liftSessionComp p).eval (.cons x (liftEnv ρ)))
      (fun x => mk.eval (.cons x ρ))
      (fun x => (liftE2EExpr mk).eval (.cons x (liftEnv ρ)))
      (fun x => (ih (.cons x ρ)).trans (id_map _))
      (fun x => liftE2EExpr_eval mk (.cons x ρ)) ((l.eval ρ).take Kb)
  | foldM Kb l z f ih =>
    simp only [liftSessionComp, Comp.eval, liftE2EExpr_eval l ρ, liftE2EExpr_eval z ρ,
      liftVal, ← List.map_take]
    exact foldML_map_hom liftVal liftVal (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun x acc => (liftSessionComp f).eval (.cons x (.cons acc (liftEnv ρ))))
      (fun x acc => ih (.cons x (.cons acc ρ))) ((l.eval ρ).take Kb) (z.eval ρ)

@[expose] def snocAtomicE {ℓ : ℕ} {Pt : Type} (qStart : ℕ) {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} {τ : Ty (atomicSig ℓ Pt)}
    (xsE : Expr O Γ (.list τ)) (xE : Expr O Γ τ) : Expr O Γ (.list τ) :=
  .appendL (qStart + 1) xsE (.cons xE .nil)

theorem snocAtomicE_cost {ℓ : ℕ} {Pt : Type} (qStart : ℕ) {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} {τ : Ty (atomicSig ℓ Pt)}
    (xsE : Expr O Γ (.list τ)) (xE : Expr O Γ τ) :
    (snocAtomicE qStart xsE xE).cost ≤ xsE.cost + xE.cost + qStart + 4 := by
  unfold snocAtomicE; simp only [Expr.cost]; omega

theorem snocAtomicE_size {ℓ : ℕ} {Pt : Type} (qStart : ℕ) {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} {τ : Ty (atomicSig ℓ Pt)}
    (xsE : Expr O Γ (.list τ)) (xE : Expr O Γ τ) :
    (snocAtomicE qStart xsE xE).size ≤ xsE.size + xE.size + bits qStart + 6 := by
  have hk := bits_succ_le qStart
  unfold snocAtomicE; simp only [Expr.size]; omega

@[simp] theorem snocAtomicE_eval {ℓ : ℕ} {Pt : Type} (qStart : ℕ) {O : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} {τ : Ty (atomicSig ℓ Pt)}
    (xsE : Expr O Γ (.list τ)) (xE : Expr O Γ τ) (ρ : Env Γ)
    (hlen : (xsE.eval ρ).length ≤ qStart) :
    (snocAtomicE qStart xsE xE).eval ρ = xsE.eval ρ ++ [xE.eval ρ] := by
  have h1 : (xsE.eval ρ ++ [xE.eval ρ]).length ≤ qStart + 1 := by simp; omega
  simp only [snocAtomicE, Expr.eval, List.take_of_length_le h1]

theorem bhE2EFinishStartSpk_some_drKey {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (bMode? : Option Bool) (σ : BHE2EDrvState S ℓ)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse) (ac : BitVec 256)
    {idx : ℕ} {σ' : BHE2EDrvState S ℓ}
    (h : bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac = (some idx, σ')) :
    ∃ dk, kr1 = .drKeyResp dk ∧
      dk.rootKey.length = 32 ∧ dk.chainKey.length = 32 ∧ dk.pqrKey.length = 32 := by
  unfold bhE2EFinishStartSpk at h
  rcases hg : bhE2EGuard σ sid with _ | ⟨hdr, bnd, ⟨u, j⟩⟩
  · simp [hg] at h
  · cases kr1 with
    | drKeyResp dk =>
      cases kr2 with
      | spkSkResp spkSk =>
        simp only [hg] at h
        split_ifs at h with hlen
        · simp only [Bool.and_eq_true, beq_iff_eq] at hlen
          exact ⟨dk, rfl, hlen.1.1.1, hlen.1.1.2, hlen.1.2⟩
        · cases h
      | _ => simp [hg] at h
    | _ => simp [hg] at h


section Lift1Helpers

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
variable {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
variable {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

@[expose] def lift1Expr {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (body : Expr (e2eOps ℓ P C K decT encT) [a] b) :
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) b) :=
  .letE argE (wk1Expr (liftE2EExpr (Pt := Pt) body))

theorem lift1Expr_cost {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (body : Expr (e2eOps ℓ P C K decT encT) [a] b) :
    (lift1Expr argE body).cost = argE.cost + body.cost + 1 := by
  simp only [lift1Expr, Expr.cost, wk1Expr_cost, liftE2EExpr_cost]

theorem lift1Expr_size {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (body : Expr (e2eOps ℓ P C K decT encT) [a] b) :
    (lift1Expr argE body).size = argE.size + body.size + 1 := by
  simp only [lift1Expr, Expr.size, wk1Expr_size, liftE2EExpr_size]

theorem lift1Expr_eval {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (body : Expr (e2eOps ℓ P C K decT encT) [a] b) (ρ : Env Γ) (v : a.denote)
    (harg : argE.eval ρ = liftVal (Pt := Pt) v) :
    (lift1Expr argE body).eval ρ = liftVal (Pt := Pt) (body.eval (.cons v .nil)) := by
  dsimp only [lift1Expr, Expr.eval]; rw [harg, wk1Expr_eval]
  exact liftE2EExpr_eval body (.cons v .nil)

@[expose] def lift1Comp {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (body : Comp (e2eOps ℓ P C K decT encT)
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) [a] b) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ (liftTy (Pt := Pt) b) :=
  .bind (.ret argE) (wk1Comp (liftSessionComp (Pt := Pt) body))

theorem lift1Comp_cost {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (body : Comp (e2eOps ℓ P C K decT encT)
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) [a] b) :
    (lift1Comp argE body).cost = argE.cost + body.cost + 2 := by
  simp only [lift1Comp, Comp.cost, wk1Comp_cost, liftSessionComp_cost]; omega

theorem lift1Comp_size {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (body : Comp (e2eOps ℓ P C K decT encT)
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) [a] b) :
    (lift1Comp argE body).size = argE.size + body.size + 2 := by
  simp only [lift1Comp, Comp.size, wk1Comp_size, liftSessionComp_size]; omega

theorem lift1Comp_queries {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (body : Comp (e2eOps ℓ P C K decT encT)
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) [a] b)
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ)
    (ws : (e2eSessionTargetIface ℓ Pt).smp.Samp → ℕ) :
    (lift1Comp argE body).queries w ws =
      body.queries (fun g => w (liftSessionTag g)) (fun s => ws (liftSamp s)) := by
  simp only [lift1Comp, Comp.queries, wk1Comp_queries_any, liftSessionComp_queries, Nat.zero_add]

theorem lift1Comp_eval {a b : Ty (e2eSig ℓ)} {Γ : List (Ty (atomicSig ℓ Pt))}
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (liftTy (Pt := Pt) a))
    (body : Comp (e2eOps ℓ P C K decT encT)
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) [a] b) (ρ : Env Γ) (v : a.denote)
    (harg : argE.eval ρ = liftVal (Pt := Pt) v) :
    (lift1Comp argE body).eval ρ = liftVal (Pt := Pt) <$> body.eval (.cons v .nil) := by
  dsimp only [lift1Comp, Comp.eval]; rw [pure_bind, harg, wk1Comp_eval]
  exact liftSessionComp_eval body (.cons v .nil)

end Lift1Helpers

end Computational.Proofs.E2E.Dsl.HaltedPrefixSubprogsAux

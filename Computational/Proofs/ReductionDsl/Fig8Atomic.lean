/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatements
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Proofs.ReductionDsl.MacroLift
public import Computational.Proofs.ReductionDsl.AtomicTablesHonest
public import Computational.Proofs.ReductionDsl.SM.DeliverForge

/-!
# Atomic `ReductionDsl` compilation for ACD19 Figure 8 reductions

Compiles the Figure 8 secure-messaging reductions (and `DeliverForge` variants) from `smSig` and
`ckaSig` into `ReductionDsl.atomicFig8Ops` over `atomicSig ℓ Pt` with explicit 32-byte block
measures and atomic primitive step costs, guarded at `ℓ < 10 ^ 6` via `MacroLift.guardRed`.
-/

@[expose] public section

set_option autoImplicit false

open ReductionDsl (Sig Ty Var Env Expr Comp Samplers Ops Iface GameCodec CostedReduction
  OpsSizeHonest SampSizeHonest bits liftRen
  AtomicSort atomicSig AtomicUnifBase atomicSamplers
  AtomicPureOp atomicPureOps AtomicPtEncOp atomicPtEncOps AtomicSymOp atomicSymOps
  AtomicGroupOp atomicGroupOps atomicFsOps atomicFig8Ops
  PB B U8 U32 U64 BV128 BV256 PK IdKey PlainT PtT signalHdrT signalParsedT
  partyToBool boolToParty toLEBytes bytesToWordLE
  salt32V salt32OfV lpubT lpubV lpubOfV wireSaltCtT wireSaltCtV wireSaltCtOfV
  lctT lctV lctOfV fig8HdrT fsSendStT fsSendStV fsSendStOfV fsRecvStT fsRecvStV fsRecvStOfV
  fsRrT fsRrEnc fsRrDec ckaStT ckaStV ckaStOfV fig8CtT fig8CtV fig8CtOfV
  fig8StT fig8StV fig8StOfV smRrT smRrEnc smRrDec
  CKATag PRNGTag FSAEADTag SMTag SMTagDF
  ckaTargetIface prngTargetIface fsaeadHeaderIface fig8SmIface fig8SmIfaceDF
  fig8SmCodec fig8SmCodecDF
  atomicFig8Ops_sizeHonest atomicSamplers_sizeHonest)

namespace Computational.Proofs.ReductionDsl.Fig8Atomic

open OracleSpec OracleComp
open _root_.CryptoGames (Party AEADScheme MACScheme WireAEAD CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.HMAC (keyToBytes32 hmacSha256Trunc8 hmacWith sha256With toBEBytes
  bytesToWord64LE hmacScheme)
open _root_.CryptoGames.HKDF (bytesToKey32 deriveMessageKeys hkdfExtract)
open _root_.CryptoGames.CBC (Plain Block nBlocks blockToBytesLE cbcDecRaw)
open _root_.CryptoGames.LibsignalAead (SerializedIdentityKeys addressCheckPasses libsignalReceiveWire
  libsignalWireAead)
open _root_.CryptoGames.Ratchet (keyToBytesVec32 padOrTruncatePlain chainHmac messageKeySeed chainKeySeed
  hmacPRF rootPRNG extractPRF expandPRG rootKdf rootSalt rootExpand)
open _root_.CryptoGames.Ratchet.LibsignalInst (Salt32 LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  dummyKey lIds lHeader lWire lAeadK lAead lPubOf lChainPRG lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey IdentityKey SignalHeader
  ProtoSignalMessage SignalMessage SignalMessageProtoCodec MessageKeyGenerator currentVersion
  macLength macIds serializeContent computeMac aesCbcEncrypt aesCbcDecrypt signalWireCodec
  maxForwardJumps rustLenBound)
open _root_.CryptoGames.CKA (DHFun dhScheme CKASort ckaSig CKAOp ckaOps ckaSchemeOps
  CKASamp ckaSamplers ckaIface ckaHdrTy ckaHdrCtTy ckaRrTy ckaPsTy ckaPsDec ckaPsEnc
  ckaSMQ ckaSMR ckaSMCodec ckaSMQDF ckaSMRDF ckaSMCodecDF)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps prngSchemeOps prngSamplers prngIface
  prngSMCodec prngSMCodecDF FSHdrTag fsHdrRrTy fsHdrRrEnc fsaeadHeaderAdIface)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState skipKeys fromAEADPRG)
open _root_.CryptoGames.SM (SMSort smSig SMOp smOps SMSamp smSamplers smIface smIfaceDF
  smQ smR smCodec smQDF smRDF smCodecDF partyEnc partyDec RecvResult)
open CryptoVerification.E2E (ofU8 toU8 fitVec u8Vec vecU8)
open CryptoVerification.LibsignalProtoCodec (WireType emptyProtoSignalMessage
  encodeVarintAux encodeVarint encodeKey encodeBytesField encodeUint32Field encode
  decodeVarintAux decodeVarint decodeKey skipBytes skipScalar skipField skipGroup
  mergeBytes mergeUint32 mergeField decodeLoop decode protoSignalCodec)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal mapCtx mapVarAux auxVar mapEnvAux
  get_mapEnvAux get_auxVar callMacroAux callMacroAux_cost callMacroAux_size callMacroAux_queries
  callMacroAux_eval guardRed guardRed_gRedBounded)

/-! ## Key/wire helpers and `TargetCodecs` roundtrips -/

section ValueRoundtrips

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : ℕ)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : ℕ)
    (hj : j < bs.length) (h32 : j < 32) :
    (bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [bytesToKey32] using extractLsb'_zero_bytesToKey32_cons b (bytesToKey32 rest)
    | succ j =>
      have hcons : bytesToKey32 (b :: rest) =
          (bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons b (bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem bytesToKey32_keyToBytes32 (k : BitVec 256) :
    bytesToKey32 (keyToBytes32 k) = k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hj : i / 8 < 32 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToKey32 (keyToBytes32 k) (i / 8) (by simp [keyToBytes32, hj]) hj)
  simp only [keyToBytes32, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr, decide_true,
    Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

theorem keyToBytes32_bytesToKey32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

private theorem flatMap_blockToBytesLE_length :
    ∀ l : List Block, (l.flatMap blockToBytesLE).length = 16 * l.length
  | [] => rfl
  | _ :: bs => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, blockToBytesLE,
      List.length_ofFn, flatMap_blockToBytesLE_length bs]
    omega

theorem aesCbcEncrypt_length_eq {ℓ : ℕ} (E : BitVec 256 → Block → Block)
    (k : BitVec 256) (iv : Block) (pt : Plain ℓ) :
    (aesCbcEncrypt E k iv pt.toList).length = 16 * (ℓ / 16 + 1) := by
  unfold aesCbcEncrypt
  rw [flatMap_blockToBytesLE_length, List.Vector.toList_length, nBlocks, pt.toList_length]

private theorem prostEncodeVarintAux_length_le :
    ∀ (k : ℕ) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => by simp [encodeVarintAux]
  | k + 1, v => by
    simp only [encodeVarintAux]
    split
    · simp
    · simp only [List.length_cons]
      have ih := prostEncodeVarintAux_length_le k (v >>> 7)
      omega

private theorem prostEncodeBytesField_length_le (tag : ℕ) (opt : Option (List (BitVec 8))) (N : ℕ)
    (h : ∀ b ∈ opt, b.length ≤ N) :
    (encodeBytesField tag opt).length ≤ 20 + N := by
  cases opt with
  | none => simp [encodeBytesField]
  | some b =>
    simp only [encodeBytesField, List.length_append]
    have h1 := prostEncodeVarintAux_length_le 10
      (BitVec.ofNat 64 (tag * 8 + WireType.lengthDelimited.toNat))
    have h2 := prostEncodeVarintAux_length_le 10 (BitVec.ofNat 64 b.length)
    have h3 := h b rfl
    unfold encodeKey encodeVarint
    omega

private theorem prostEncodeUint32Field_length_le (tag : ℕ) (opt : Option (BitVec 32)) :
    (encodeUint32Field tag opt).length ≤ 20 := by
  cases opt with
  | none => simp [encodeUint32Field]
  | some v =>
    simp only [encodeUint32Field, List.length_append]
    have h1 := prostEncodeVarintAux_length_le 10
      (BitVec.ofNat 64 (tag * 8 + WireType.varint.toNat))
    have h2 := prostEncodeVarintAux_length_le 10 (v.zeroExtend 64)
    unfold encodeKey encodeVarint
    omega

private theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]

theorem signalMsgNew_serialized_length_le {ℓ : ℕ} (F : ShaCompress)
    (msgVer : BitVec 8) (macKey : BitVec 256) (addr? : Option (List (BitVec 8)))
    (senderRk : PublicKey) (ctr prevCtr : BitVec 32) (ct : List (BitVec 8))
    (idS idR : IdentityKey) (pqMsg : List (BitVec 8))
    (hct : ct.length ≤ 32 * (ℓ / 32 + 2))
    (hpq : pqMsg.length ≤ 96)
    (haddr : ∀ a ∈ addr?, a.length ≤ 128) :
    (SignalMessage.new F protoSignalCodec msgVer macKey addr? senderRk ctr prevCtr ct
      idS idR pqMsg).serialized.length ≤ 32 * (ℓ / 32) + 450 := by
  have hmac : (hmacSha256Trunc8 F (keyToBytes32 macKey)
      ((macIds idS idR).toList ++
        serializeContent protoSignalCodec msgVer senderRk ctr prevCtr ct pqMsg addr?)).length ≤ 8 :=
    List.length_take_le 8 _
  dsimp only [SignalMessage.new, computeMac]
  rw [List.length_append]
  have hser : (serializeContent protoSignalCodec msgVer senderRk ctr prevCtr ct pqMsg addr?).length ≤
      32 * (ℓ / 32) + 442 := by
    dsimp only [serializeContent, protoSignalCodec, encode]
    simp only [List.length_cons, List.length_append]
    have f1 := prostEncodeBytesField_length_le 1 (some senderRk.serialize) 33
      (fun b hb => by simp only [Option.mem_def, Option.some.injEq] at hb; subst hb
                      rw [publicKey_serialize_length])
    have f2 := prostEncodeUint32Field_length_le 2 (some ctr)
    have f3 := prostEncodeUint32Field_length_le 3 (some prevCtr)
    have f4 := prostEncodeBytesField_length_le 4 (some ct) (32 * (ℓ / 32 + 2))
      (fun b hb => by simp only [Option.mem_def, Option.some.injEq] at hb; subst hb; exact hct)
    have f5 := prostEncodeBytesField_length_le 5 (if pqMsg.isEmpty then none else some pqMsg) 96
      (fun b hb => by split at hb; · cases hb
                      · simp only [Option.mem_def, Option.some.injEq] at hb; subst hb; exact hpq)
    have f6 := prostEncodeBytesField_length_le 6 addr? 128 haddr
    omega
  omega

theorem boolToParty_partyToBool (p : Party) : boolToParty (partyToBool p) = p := by
  cases p <;> rfl

theorem partyToBool_boolToParty (b : Bool) : partyToBool (boolToParty b) = b := by
  cases b <;> rfl

theorem partyToBool_eq_partyEnc (p : Party) : partyToBool p = partyEnc p := by
  cases p <;> rfl

theorem boolToParty_eq_partyDec (b : Bool) : boolToParty b = partyDec b := by
  cases b <;> rfl

theorem salt32OfV_salt32V (s : Salt32) : salt32OfV (salt32V s) = s := by
  apply Subtype.ext
  change keyToBytes32 (bytesToKey32 s.toList) = s.toList
  exact keyToBytes32_bytesToKey32 s.toList s.toList_length

theorem salt32V_salt32OfV (x : BitVec 256) : salt32V (salt32OfV x) = x :=
  bytesToKey32_keyToBytes32 x

theorem lpubOfV_lpubV {ℓ : ℕ} {Pt : Type} (p : LibsignalMsgPublicPart) :
    lpubOfV (ℓ := ℓ) (Pt := Pt) (lpubV p) = p := by
  cases p; simp [lpubV, lpubOfV, salt32OfV_salt32V]

theorem wireSaltCtOfV_wireSaltCtV {ℓ : ℕ} {Pt : Type} (c : LibsignalCiphertextWithSalt32) :
    wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) (wireSaltCtV c) = c := by
  rcases c with ⟨w, s⟩; simp [wireSaltCtV, wireSaltCtOfV, salt32OfV_salt32V]

theorem lctOfV_lctV {ℓ : ℕ} {Pt : Type} (c : ℕ × LibsignalCiphertextWithSalt32) :
    lctOfV (ℓ := ℓ) (Pt := Pt) (lctV c) = c := by
  rcases c with ⟨i, w⟩; simp [lctV, lctOfV, wireSaltCtOfV_wireSaltCtV]

theorem fsSendStOfV_fsSendStV {ℓ : ℕ} {Pt : Type} (s : RatchetSenderState (BitVec 256)) :
    fsSendStOfV (ℓ := ℓ) (Pt := Pt) (fsSendStV s) = s := by
  cases s; rfl

theorem fsRecvStOfV_fsRecvStV {ℓ : ℕ} {Pt : Type}
    (r : RatchetReceiverState (BitVec 256) (BitVec 256)) :
    fsRecvStOfV (ℓ := ℓ) (Pt := Pt) (fsRecvStV r) = r := by
  cases r; rfl

theorem ckaStOfV_ckaStV {ℓ : ℕ} {Pt : Type} (s : CryptoGames.CKA.DDH.State (BitVec 256) Pt) :
    ckaStOfV (ℓ := ℓ) (Pt := Pt) (ckaStV s) = s := by
  cases s <;> rfl

theorem fig8CtOfV_fig8CtV {ℓ : ℕ} {Pt : Type} (c : Fig8C Pt) :
    fig8CtOfV (ℓ := ℓ) (Pt := Pt) (fig8CtV c) = c := by
  rcases c with ⟨h, lc⟩; simp [fig8CtV, fig8CtOfV, lctOfV_lctV]

theorem fig8StOfV_fig8StV {ℓ : ℕ} {Pt : Type} (s : Fig8St Pt) :
    fig8StOfV (ℓ := ℓ) (Pt := Pt) (fig8StV s) = s := by
  rcases s with ⟨p, rk, vS, vR, γ, cur, tcur⟩
  simp only [fig8StV, fig8StOfV, boolToParty_partyToBool, Option.map_map, Function.comp_def,
    fsSendStOfV_fsSendStV, fsRecvStOfV_fsRecvStV, ckaStOfV_ckaStV]
  have hvS : Option.map (fun x => x) vS = vS := by cases vS <;> rfl
  have hvR : (fun k => Option.map (fun x => x) (vR k)) = vR := by
    funext k; cases vR k <;> rfl
  rw [hvS, hvR]

end ValueRoundtrips


/-! ## Pure-operator AST compiler -/

section PureCompiler

def callPureMacroAux {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {a b : Ty S₂} (e : Expr O₂ [a, auxT] b) :
    Expr O₂ (a :: mapCtx f auxT Γ) b :=
  Expr.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ (auxVar f auxT Γ))
    e

@[simp] theorem callPureMacroAux_cost {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {a b : Ty S₂} (e : Expr O₂ [a, auxT] b) :
    (callPureMacroAux f auxT Γ e).cost = e.cost :=
  Expr.renameM_cost _ e

@[simp] theorem callPureMacroAux_size {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {a b : Ty S₂} (e : Expr O₂ [a, auxT] b) :
    (callPureMacroAux f auxT Γ e).size = e.size :=
  Expr.renameM_size _ e

theorem callPureMacroAux_eval {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) {auxT : Ty S₂}
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) (aux : auxT.denote)
    {Γ : List (Ty S₁)} (ρ : Env Γ) {O₂ : Ops S₂} {a b : Ty S₂}
    (e : Expr O₂ [a, auxT] b) (x : a.denote) :
    (callPureMacroAux f auxT Γ e).eval (.cons x (mapEnvAux f toDen aux ρ)) =
      e.eval (.cons x (.cons aux .nil)) := by
  refine Expr.renameM_eval e ?_
  intro u v
  cases v with
  | zero => rfl
  | succ v =>
    cases v with
    | zero => exact get_auxVar f toDen aux ρ
    | succ v => nomatch v

/-- Bundle of pure `Expr` operator macros and `Comp` sampler/query macros with access to `(arg, aux)`. -/
structure PureBundle (S₁ S₂ : Sig) (O₁ : Ops S₁) (O₂ : Ops S₂)
    {ι : Type} {T : OracleSpec ι} (I₁ : Iface S₁ T) (I₂ : Iface S₂ T)
    (auxT : Ty S₂) where
  fSort : S₁.Base → Ty S₂
  opMacro : (o : O₁.Op) → Expr O₂ [mapTy fSort (O₁.dom o), auxT] (mapTy fSort (O₁.cod o))
  sampMacro : (s : I₁.smp.Samp) →
    Comp O₂ I₂ [mapTy fSort (I₁.smp.sDom s), auxT] (mapTy fSort (I₁.smp.sTy s))
  queryMacro : (g : I₁.Tag) →
    Comp O₂ I₂ [mapTy fSort (I₁.dom g), auxT] (mapTy fSort (I₁.cod g))

variable {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
  {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}

def compilePureExpr (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Expr O₁ Γ t → Expr O₂ (mapCtx M.fSort auxT Γ) (mapTy M.fSort t)
  | _, _, .var v => .var (mapVarAux M.fSort auxT v)
  | _, _, .unit => .unit
  | _, _, .bool b => .bool b
  | _, _, .nat n => .nat n
  | _, _, .add a b => .add (compilePureExpr M a) (compilePureExpr M b)
  | _, _, .sub a b => .sub (compilePureExpr M a) (compilePureExpr M b)
  | _, _, .mulK k a => .mulK k (compilePureExpr M a)
  | _, _, .divK k a => .divK k (compilePureExpr M a)
  | _, _, .modK k a => .modK k (compilePureExpr M a)
  | _, _, .lt a b => .lt (compilePureExpr M a) (compilePureExpr M b)
  | _, _, .eqN a b => .eqN (compilePureExpr M a) (compilePureExpr M b)
  | _, _, .not a => .not (compilePureExpr M a)
  | _, _, .and a b => .and (compilePureExpr M a) (compilePureExpr M b)
  | _, _, .ite c a b => .ite (compilePureExpr M c) (compilePureExpr M a) (compilePureExpr M b)
  | _, _, .pair a b => .pair (compilePureExpr M a) (compilePureExpr M b)
  | _, _, .fst a => .fst (compilePureExpr M a)
  | _, _, .snd a => .snd (compilePureExpr M a)
  | _, _, .inl a => .inl (compilePureExpr M a)
  | _, _, .inr a => .inr (compilePureExpr M a)
  | _, _, .none => .none
  | _, _, .some a => .some (compilePureExpr M a)
  | _, _, .caseOpt e n s =>
    .caseOpt (compilePureExpr M e) (compilePureExpr M n) (compilePureExpr M s)
  | _, _, .caseSum e l r =>
    .caseSum (compilePureExpr M e) (compilePureExpr M l) (compilePureExpr M r)
  | _, _, .letE e b => .letE (compilePureExpr M e) (compilePureExpr M b)
  | Γ, _, .op o a =>
    .letE (compilePureExpr M a) (callPureMacroAux M.fSort auxT Γ (M.opMacro o))
  | _, _, .nil => .nil
  | _, _, .cons x l => .cons (compilePureExpr M x) (compilePureExpr M l)
  | _, _, .len l => .len (compilePureExpr M l)
  | _, _, .take n l => .take (compilePureExpr M n) (compilePureExpr M l)
  | _, _, .appendL K a b => .appendL K (compilePureExpr M a) (compilePureExpr M b)
  | _, _, .findB K l p => .findB K (compilePureExpr M l) (compilePureExpr M p)
  | _, _, .anyB K l p => .anyB K (compilePureExpr M l) (compilePureExpr M p)
  | _, _, .mapB K l f => .mapB K (compilePureExpr M l) (compilePureExpr M f)
  | _, _, .foldrB K l z f =>
    .foldrB K (compilePureExpr M l) (compilePureExpr M z) (compilePureExpr M f)
  | _, _, .tconst a => .tconst (compilePureExpr M a)
  | _, _, .tget m i => .tget (compilePureExpr M m) (compilePureExpr M i)
  | _, _, .tset m i a =>
    .tset (compilePureExpr M m) (compilePureExpr M i) (compilePureExpr M a)

def compilePureComp (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Comp O₁ I₁ Γ t → Comp O₂ I₂ (mapCtx M.fSort auxT Γ) (mapTy M.fSort t)
  | _, _, .ret e => .ret (compilePureExpr M e)
  | _, _, .bind c k => .bind (compilePureComp M c) (compilePureComp M k)
  | _, _, .ite b c d => .ite (compilePureExpr M b) (compilePureComp M c) (compilePureComp M d)
  | _, _, .caseOpt e n s =>
    .caseOpt (compilePureExpr M e) (compilePureComp M n) (compilePureComp M s)
  | _, _, .caseSum e l r =>
    .caseSum (compilePureExpr M e) (compilePureComp M l) (compilePureComp M r)
  | Γ, _, .sample s e =>
    .bind (.ret (compilePureExpr M e)) (callMacroAux M.fSort auxT Γ (M.sampMacro s))
  | Γ, _, .query g e =>
    .bind (.ret (compilePureExpr M e)) (callMacroAux M.fSort auxT Γ (M.queryMacro g))
  | _, _, .iter n e body => .iter n (compilePureExpr M e) (compilePureComp M body)
  | _, _, .findM K l p => .findM K (compilePureExpr M l) (compilePureComp M p)
  | _, _, .anyM K l p => .anyM K (compilePureExpr M l) (compilePureComp M p)
  | _, _, .mapM K l f => .mapM K (compilePureExpr M l) (compilePureComp M f)
  | _, _, .consumeFirstM K l p mk =>
    .consumeFirstM K (compilePureExpr M l) (compilePureComp M p) (compilePureExpr M mk)
  | _, _, .foldM K l z f =>
    .foldM K (compilePureExpr M l) (compilePureExpr M z) (compilePureComp M f)

def opExcess (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) (o : O₁.Op) : ℕ :=
  ((M.opMacro o).cost + 1) - O₁.cost o

def sampExcess (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) (s : I₁.smp.Samp) : ℕ :=
  ((M.sampMacro s).cost + 2) - I₁.smp.sCost s

def queryExcess (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) (g : I₁.Tag) : ℕ :=
  ((M.queryMacro g).cost + 2) - I₁.qCost g

def exprExcess (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} → Expr O₁ Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .nat _ | _, _, .none | _, _, .nil => 0
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b | _, _, .and a b
  | _, _, .pair a b | _, _, .cons a b | _, _, .take a b | _, _, .appendL _ a b
  | _, _, .tget a b => exprExcess M a + exprExcess M b
  | _, _, .mulK _ a | _, _, .divK _ a | _, _, .modK _ a | _, _, .not a | _, _, .fst a
  | _, _, .snd a | _, _, .inl a | _, _, .inr a | _, _, .some a | _, _, .len a
  | _, _, .tconst a => exprExcess M a
  | _, _, .ite c a b => exprExcess M c + max (exprExcess M a) (exprExcess M b)
  | _, _, .caseOpt e n s => exprExcess M e + max (exprExcess M n) (exprExcess M s)
  | _, _, .caseSum e l r => exprExcess M e + max (exprExcess M l) (exprExcess M r)
  | _, _, .letE e b => exprExcess M e + exprExcess M b
  | _, _, .op o a => exprExcess M a + opExcess M o
  | _, _, .findB K l p | _, _, .anyB K l p | _, _, .mapB K l p =>
    exprExcess M l + K * exprExcess M p
  | _, _, .foldrB K l z f => exprExcess M l + exprExcess M z + K * exprExcess M f
  | _, _, .tset m i a => exprExcess M m + exprExcess M i + exprExcess M a

def compExcess (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} → Comp O₁ I₁ Γ t → ℕ
  | _, _, .ret e => exprExcess M e
  | _, _, .bind c k => compExcess M c + compExcess M k
  | _, _, .ite b c d => exprExcess M b + max (compExcess M c) (compExcess M d)
  | _, _, .caseOpt e n s => exprExcess M e + max (compExcess M n) (compExcess M s)
  | _, _, .caseSum e l r => exprExcess M e + max (compExcess M l) (compExcess M r)
  | _, _, .sample s e => exprExcess M e + sampExcess M s
  | _, _, .query g e => exprExcess M e + queryExcess M g
  | _, _, .iter n e body => exprExcess M e + n * compExcess M body
  | _, _, .findM K l p | _, _, .anyM K l p | _, _, .mapM K l p =>
    exprExcess M l + K * compExcess M p
  | _, _, .consumeFirstM K l p mk =>
    exprExcess M l + K * (compExcess M p + exprExcess M mk)
  | _, _, .foldM K l z f => exprExcess M l + exprExcess M z + K * compExcess M f

theorem compilePureExpr_cost_le (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compilePureExpr M e).cost ≤ e.cost + exprExcess M e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    simp [compilePureExpr, exprExcess, Expr.cost]
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2 | and _ _ ih1 ih2
  | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2 | appendL _ _ _ ih1 ih2
  | tget _ _ ih1 ih2 =>
    simp only [compilePureExpr, exprExcess, Expr.cost]; omega
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    simp only [compilePureExpr, exprExcess, Expr.cost]; omega
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb =>
    simp only [compilePureExpr, exprExcess, Expr.cost]; omega
  | letE _ _ ihe ihb =>
    simp only [compilePureExpr, exprExcess, Expr.cost]; omega
  | op o a iha =>
    simp only [compilePureExpr, exprExcess, opExcess, Expr.cost, callPureMacroAux_cost]; omega
  | findB K _ _ ihl ihp | anyB K _ _ ihl ihp | mapB K _ _ ihl ihp =>
    simp only [compilePureExpr, exprExcess, Expr.cost]
    have hm := Nat.mul_le_mul_left K ihp
    nlinarith
  | foldrB K _ _ _ ihl ihz ihf =>
    simp only [compilePureExpr, exprExcess, Expr.cost]
    have hm := Nat.mul_le_mul_left K ihf
    nlinarith
  | tset _ _ _ ih1 ih2 ih3 =>
    simp only [compilePureExpr, exprExcess, Expr.cost]; omega

theorem compilePureComp_cost_le (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureComp M c).cost ≤ c.cost + compExcess M c := by
  induction c with
  | ret e =>
    have he := compilePureExpr_cost_le M e
    simp only [compilePureComp, compExcess, Comp.cost]; omega
  | bind _ _ ihc ihk =>
    simp only [compilePureComp, compExcess, Comp.cost]; omega
  | ite b _ _ ihc ihd =>
    have hb := compilePureExpr_cost_le M b
    simp only [compilePureComp, compExcess, Comp.cost]; omega
  | caseOpt e _ _ ihn ihs =>
    have he := compilePureExpr_cost_le M e
    simp only [compilePureComp, compExcess, Comp.cost]; omega
  | caseSum e _ _ ihl ihr =>
    have he := compilePureExpr_cost_le M e
    simp only [compilePureComp, compExcess, Comp.cost]; omega
  | sample s e =>
    have he := compilePureExpr_cost_le M e
    simp only [compilePureComp, compExcess, sampExcess, Comp.cost, callMacroAux_cost]; omega
  | query g e =>
    have he := compilePureExpr_cost_le M e
    simp only [compilePureComp, compExcess, queryExcess, Comp.cost, callMacroAux_cost]; omega
  | iter n e _ ihb =>
    have he := compilePureExpr_cost_le M e
    have hm := Nat.mul_le_mul_left n ihb
    simp only [compilePureComp, compExcess, Comp.cost]; nlinarith
  | findM K l _ ihp | anyM K l _ ihp | mapM K l _ ihp =>
    have hl := compilePureExpr_cost_le M l
    have hm := Nat.mul_le_mul_left K ihp
    simp only [compilePureComp, compExcess, Comp.cost]; nlinarith
  | consumeFirstM K l _ mk ihp =>
    have hl := compilePureExpr_cost_le M l
    have hmk := compilePureExpr_cost_le M mk
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add ihp hmk)
    simp only [compilePureComp, compExcess, Comp.cost]; nlinarith
  | foldM K l z _ ihf =>
    have hl := compilePureExpr_cost_le M l
    have hz := compilePureExpr_cost_le M z
    have hm := Nat.mul_le_mul_left K ihf
    simp only [compilePureComp, compExcess, Comp.cost]; nlinarith

theorem compilePureExpr_size_le (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (S_max : ℕ) (hS : 1 ≤ S_max)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ S_max)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compilePureExpr M e).size ≤ S_max * e.size := by
  induction e with
  | var _ | unit | bool _ | none | nil =>
    simp only [compilePureExpr, Expr.size]; omega
  | nat _ =>
    simp only [compilePureExpr, Expr.size]; nlinarith
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2 | and _ _ ih1 ih2
  | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2 | appendL _ _ _ ih1 ih2
  | tget _ _ ih1 ih2 | letE _ _ ih1 ih2 =>
    simp only [compilePureExpr, Expr.size]; nlinarith
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    simp only [compilePureExpr, Expr.size]; nlinarith
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb
  | foldrB _ _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    simp only [compilePureExpr, Expr.size]; nlinarith
  | op o _ iha =>
    have ho := hOp o
    simp only [compilePureExpr, Expr.size, callPureMacroAux_size]; nlinarith
  | findB _ _ _ ihl ihp | anyB _ _ _ ihl ihp | mapB _ _ _ ihl ihp =>
    simp only [compilePureExpr, Expr.size]; nlinarith

theorem compilePureComp_size_le (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (S_max : ℕ) (hS : 1 ≤ S_max)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ S_max)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ S_max)
    (hQuery : ∀ g, (M.queryMacro g).size + 2 ≤ S_max)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureComp M c).size ≤ S_max * c.size := by
  induction c with
  | ret e =>
    have he := compilePureExpr_size_le M S_max hS hOp e
    simp only [compilePureComp, Comp.size]; nlinarith
  | bind _ _ ihc ihk =>
    simp only [compilePureComp, Comp.size]; nlinarith
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := compilePureExpr_size_le M S_max hS hOp b
    simp only [compilePureComp, Comp.size]; nlinarith
  | sample s e =>
    have he := compilePureExpr_size_le M S_max hS hOp e
    have hs := hSamp s
    simp only [compilePureComp, Comp.size, callMacroAux_size]; nlinarith
  | query g e =>
    have he := compilePureExpr_size_le M S_max hS hOp e
    have hq := hQuery g
    simp only [compilePureComp, Comp.size, callMacroAux_size]; nlinarith
  | iter _ e _ ihb =>
    have he := compilePureExpr_size_le M S_max hS hOp e
    simp only [compilePureComp, Comp.size]; nlinarith
  | findM _ l _ ihp | anyM _ l _ ihp | mapM _ l _ ihp =>
    have hl := compilePureExpr_size_le M S_max hS hOp l
    simp only [compilePureComp, Comp.size]; nlinarith
  | consumeFirstM _ l _ mk ihp =>
    have hl := compilePureExpr_size_le M S_max hS hOp l
    have hmk := compilePureExpr_size_le M S_max hS hOp mk
    simp only [compilePureComp, Comp.size]; nlinarith
  | foldM _ l z _ ihf =>
    have hl := compilePureExpr_size_le M S_max hS hOp l
    have hz := compilePureExpr_size_le M S_max hS hOp z
    simp only [compilePureComp, Comp.size]; nlinarith

theorem compilePureComp_queries_le (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hSampQ : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQueryQ : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureComp M c).queries w₂ ws₂ ≤ c.queries w₁ ws₁ := by
  induction c with
  | ret _ => simp [compilePureComp, Comp.queries]
  | bind _ _ ihc ihk => simp only [compilePureComp, Comp.queries]; omega
  | ite _ _ _ ihc ihd | caseOpt _ _ _ ihc ihd | caseSum _ _ _ ihc ihd =>
    simp only [compilePureComp, Comp.queries]; exact max_le_max ihc ihd
  | sample s _ =>
    simp only [compilePureComp, Comp.queries, callMacroAux_queries, zero_add]; exact hSampQ s
  | query g _ =>
    simp only [compilePureComp, Comp.queries, callMacroAux_queries, zero_add]; exact hQueryQ g
  | iter n _ _ ihb =>
    simp only [compilePureComp, Comp.queries]; exact Nat.mul_le_mul_left n ihb
  | findM K _ _ ihp | anyM K _ _ ihp | mapM K _ _ ihp | consumeFirstM K _ _ _ ihp
  | foldM K _ _ _ ihp =>
    simp only [compilePureComp, Comp.queries]; exact Nat.mul_le_mul_left K ihp

theorem compilePureExpr_eval (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote) (aux : auxT.denote)
    (hOpE : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) x) (.cons aux .nil)) =
        toVal M.fSort toDen (O₁.cod o) (O₁.eval o x))
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) (ρ : Env Γ) :
    (compilePureExpr M e).eval (mapEnvAux M.fSort toDen aux ρ) =
      toVal M.fSort toDen t (e.eval ρ) := by
  induction e with
  | var v => exact get_mapEnvAux M.fSort toDen aux ρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 => simp [compilePureExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | sub _ _ ih1 ih2 => simp [compilePureExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | mulK _ _ ih => simp [compilePureExpr, Expr.eval, toVal, ih ρ]
  | divK _ _ ih => simp [compilePureExpr, Expr.eval, toVal, ih ρ]
  | modK _ _ ih => simp [compilePureExpr, Expr.eval, toVal, ih ρ]
  | lt _ _ ih1 ih2 => simp [compilePureExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | eqN _ _ ih1 ih2 => simp [compilePureExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | not _ ih => simp [compilePureExpr, Expr.eval, toVal, ih ρ]
  | and _ _ ih1 ih2 => simp [compilePureExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | ite c _ _ ihc iha ihb =>
    simp only [compilePureExpr, Expr.eval, ihc ρ, toVal]
    cases c.eval ρ <;> [exact ihb ρ; exact iha ρ]
  | pair _ _ ih1 ih2 => simp [compilePureExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | fst _ ih => simp [compilePureExpr, Expr.eval, toVal, ih ρ]
  | snd _ ih => simp [compilePureExpr, Expr.eval, toVal, ih ρ]
  | inl _ ih => simp [compilePureExpr, Expr.eval, toVal, ih ρ]
  | inr _ ih => simp [compilePureExpr, Expr.eval, toVal, ih ρ]
  | some _ ih => simp [compilePureExpr, Expr.eval, toVal, ih ρ]
  | caseOpt e _ _ ihe ihn ihs =>
    simp only [compilePureExpr, Expr.eval, ihe ρ, toVal]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e _ _ ihe ihl ihr =>
    simp only [compilePureExpr, Expr.eval, ihe ρ, toVal]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | letE e _ ihe ihb =>
    simp only [compilePureExpr, Expr.eval, ihe ρ]
    exact ihb (.cons (e.eval ρ) ρ)
  | op o a iha =>
    simp only [compilePureExpr, Expr.eval, iha ρ, callPureMacroAux_eval M.fSort toDen aux ρ]
    exact hOpE o (a.eval ρ)
  | cons _ _ ih1 ih2 => simp [compilePureExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | len _ ih => simp [compilePureExpr, Expr.eval, toVal, ih ρ]
  | take _ _ ih1 ih2 => simp [compilePureExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ, List.map_take]
  | appendL _ _ _ ih1 ih2 =>
    simp [compilePureExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ, List.map_take, List.map_append]
  | findB K l p ihl ihp =>
    simp only [compilePureExpr, Expr.eval, ihl ρ, toVal, ← List.map_take]
    rw [List.find?_map]
    congr 2; funext x; exact ihp (.cons x ρ)
  | anyB K l p ihl ihp =>
    simp only [compilePureExpr, Expr.eval, ihl ρ, toVal, ← List.map_take, List.any_map]
    congr 1; funext x; exact ihp (.cons x ρ)
  | mapB K l f ihl ihf =>
    simp only [compilePureExpr, Expr.eval, ihl ρ, toVal, ← List.map_take, List.map_map]
    congr 1; funext x; exact ihf (.cons x ρ)
  | foldrB K l z f ihl ihz ihf =>
    simp only [compilePureExpr, Expr.eval, ihl ρ, ihz ρ, toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs, z.eval ρ = acc₀
    induction xs with
    | nil => rfl
    | cons x xs ihxs =>
      simp only [List.map_cons, List.foldr_cons, ihxs]
      exact ihf (.cons x (.cons (xs.foldr (fun y b => f.eval (.cons y (.cons b ρ))) acc₀) ρ))
  | tconst _ ih =>
    funext i; exact ih ρ
  | tget m i ihm ihi =>
    have hm := congrFun (ihm ρ) (i.eval ρ)
    simp only [compilePureExpr, Expr.eval, ihi ρ, toVal] at hm ⊢
    exact hm
  | tset m i a ihm ihi iha =>
    funext j
    have hm := congrFun (ihm ρ) j
    simp only [compilePureExpr, Expr.eval, ihi ρ, iha ρ, toVal] at hm ⊢
    split_ifs <;> [rfl; exact hm]

theorem compilePureComp_eval (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote) (aux : auxT.denote)
    (hOpE : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) x) (.cons aux .nil)) =
        toVal M.fSort toDen (O₁.cod o) (O₁.eval o x))
    (hSampE : ∀ s x,
      (M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) x) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s x))
    (hQueryE : ∀ g x,
      (M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) x) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g x <$> (liftM (T.query (I₁.enc g x)) : OracleComp T _)))
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) (ρ : Env Γ) :
    (compilePureComp M c).eval (mapEnvAux M.fSort toDen aux ρ) =
      toVal M.fSort toDen t <$> c.eval ρ := by
  induction c with
  | ret e =>
    simp [compilePureComp, Comp.eval, compilePureExpr_eval M toDen aux hOpE e ρ]
  | bind c k ihc ihk =>
    simp only [compilePureComp, Comp.eval, ihc ρ, bind_map_left, map_bind]
    exact OracleComp.bind_congr' rfl fun x => ihk (.cons x ρ)
  | ite b c d ihc ihd =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M toDen aux hOpE b ρ, toVal]
    cases b.eval ρ <;> [exact ihd ρ; exact ihc ρ]
  | caseOpt e n s ihn ihs =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M toDen aux hOpE e ρ, toVal]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M toDen aux hOpE e ρ, toVal]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | sample s e =>
    simp only [compilePureComp, Comp.eval, pure_bind,
      compilePureExpr_eval M toDen aux hOpE e ρ, callMacroAux_eval M.fSort toDen aux ρ]
    exact hSampE s (e.eval ρ)
  | query g e =>
    simp only [compilePureComp, Comp.eval, pure_bind,
      compilePureExpr_eval M toDen aux hOpE e ρ, callMacroAux_eval M.fSort toDen aux ρ]
    exact hQueryE g (e.eval ρ)
  | iter n e body ihb =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M toDen aux hOpE e ρ]
    generalize e.eval ρ = s₀
    induction n generalizing s₀ with
    | zero => simp [ReductionDsl.iterM]
    | succ n ihn =>
      simp only [ReductionDsl.iterM, map_bind]
      change ((compilePureComp M body).eval (mapEnvAux M.fSort toDen aux (.cons s₀ ρ)) >>= _) = _
      rw [ihb (.cons s₀ ρ), bind_map_left]
      exact OracleComp.bind_congr' rfl fun s₁ => ihn s₁
  | findM K l p ihp =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M toDen aux hOpE l ρ,
      toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs
    induction xs with
    | nil => simp [ReductionDsl.findML]
    | cons x xs ihxs =>
      simp only [List.map_cons, ReductionDsl.findML, map_bind]
      change (do
        let c ← (compilePureComp M p).eval (mapEnvAux M.fSort toDen aux (.cons x ρ))
        if c then pure (Option.some (toVal M.fSort toDen _ x)) else _) = _
      rw [ihp (.cons x ρ), bind_map_left]
      refine OracleComp.bind_congr' rfl fun b => ?_
      cases b <;> [exact ihxs; simp [toVal]]
  | anyM K l p ihp =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M toDen aux hOpE l ρ,
      toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs
    induction xs with
    | nil => simp [ReductionDsl.anyML]
    | cons x xs ihxs =>
      simp only [List.map_cons, ReductionDsl.anyML, map_bind]
      change (do
        let c ← (compilePureComp M p).eval (mapEnvAux M.fSort toDen aux (.cons x ρ))
        if c then pure true else _) = _
      rw [ihp (.cons x ρ), bind_map_left]
      refine OracleComp.bind_congr' rfl fun b => ?_
      cases b <;> [exact ihxs; simp [toVal]]
  | mapM K l f ihf =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M toDen aux hOpE l ρ,
      toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs
    induction xs with
    | nil => simp [ReductionDsl.mapML]
    | cons x xs ihxs =>
      simp only [List.map_cons, ReductionDsl.mapML, ihxs, bind_map_left, map_bind, map_pure]
      change (do
        let y ← (compilePureComp M f).eval (mapEnvAux M.fSort toDen aux (.cons x ρ))
        _) = _
      rw [ihf (.cons x ρ), bind_map_left]
  | consumeFirstM K l p mk ihp =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M toDen aux hOpE l ρ,
      toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs
    induction xs with
    | nil => simp [ReductionDsl.consumeFirstML]
    | cons x xs ihxs =>
      simp only [List.map_cons, ReductionDsl.consumeFirstML, ihxs, bind_map_left, map_bind]
      change (do
        let c ← (compilePureComp M p).eval (mapEnvAux M.fSort toDen aux (.cons x ρ))
        if c then
          pure (true,
            (compilePureExpr M mk).eval (mapEnvAux M.fSort toDen aux (.cons x ρ)) ::
              List.map (toVal M.fSort toDen _) xs)
        else _) = _
      rw [ihp (.cons x ρ), compilePureExpr_eval M toDen aux hOpE mk (.cons x ρ), bind_map_left]
      refine OracleComp.bind_congr' rfl fun b => ?_
      cases b <;> simp [toVal, map_pure]
  | foldM K l z f ihf =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M toDen aux hOpE l ρ,
      compilePureExpr_eval M toDen aux hOpE z ρ, toVal, ← List.map_take]
    generalize (l.eval ρ).take K = xs, z.eval ρ = acc₀
    induction xs generalizing acc₀ with
    | nil => simp [ReductionDsl.foldML]
    | cons x xs ihxs =>
      simp only [List.map_cons, ReductionDsl.foldML, map_bind]
      change (do
        let b' ← (compilePureComp M f).eval
          (mapEnvAux M.fSort toDen aux (.cons x (.cons acc₀ ρ)))
        _) = _
      rw [ihf (.cons x (.cons acc₀ ρ)), bind_map_left]
      exact OracleComp.bind_congr' rfl fun acc₁ => ihxs acc₁

end PureCompiler

section CompilePureRed

variable {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
  {ι κ : Type} {T : OracleSpec ι} {G : OracleSpec κ}
  {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
  {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G} {auxT : Ty S₂}

/-- Boundary and game-codec adapters with query-aware response adaptation. -/
structure PureAdapters (fSort : S₁.Base → Ty S₂) (O₂ : Ops S₂)
    (C₁ : GameCodec S₁ G) (C₂ : GameCodec S₂ G) (auxT : Ty S₂)
    (rIn₁ aIn₁ aOut₁ out₁ : Ty S₁) (rIn₂ aIn₂ aOut₂ out₂ : Ty S₂) where
  splitIn : Expr O₂ [rIn₂] (.prod (mapTy fSort rIn₁) auxT)
  adaptAIn : Expr O₂ [mapTy fSort aIn₁] aIn₂
  adaptQ : Expr O₂ [C₂.Q] (mapTy fSort C₁.Q)
  adaptR : Expr O₂ [mapTy fSort C₁.R, C₂.Q] C₂.R
  adaptAOut : Expr O₂ [aOut₂] (mapTy fSort aOut₁)
  adaptOut : Expr O₂ [mapTy fSort out₁] out₂

def callAdaptR {r₁T q₂T r₂T a b c d e : Ty S₂}
    (adR : Expr O₂ [r₁T, q₂T] r₂T) :
    Expr O₂ (r₁T :: a :: b :: c :: d :: e :: [q₂T]) r₂T :=
  Expr.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ (.succ (.succ (.succ (.succ (.succ .zero)))))
      | .succ (.succ w) => nomatch w)
    adR

@[simp] theorem callAdaptR_cost {r₁T q₂T r₂T a b c d e : Ty S₂}
    (adR : Expr O₂ [r₁T, q₂T] r₂T) :
    (callAdaptR (a := a) (b := b) (c := c) (d := d) (e := e) adR).cost = adR.cost :=
  Expr.renameM_cost _ adR

@[simp] theorem callAdaptR_size {r₁T q₂T r₂T a b c d e : Ty S₂}
    (adR : Expr O₂ [r₁T, q₂T] r₂T) :
    (callAdaptR (a := a) (b := b) (c := c) (d := d) (e := e) adR).size = adR.size :=
  Expr.renameM_size _ adR

theorem callAdaptR_eval {r₁T q₂T r₂T a b c d e : Ty S₂}
    (adR : Expr O₂ [r₁T, q₂T] r₂T)
    (r₁ : r₁T.denote) (x₁ : a.denote) (x₂ : b.denote) (x₃ : c.denote)
    (x₄ : d.denote) (x₅ : e.denote) (q₂ : q₂T.denote) :
    (callAdaptR (a := a) (b := b) (c := c) (d := d) (e := e) adR).eval
        (.cons r₁ (.cons x₁ (.cons x₂ (.cons x₃ (.cons x₄ (.cons x₅ (.cons q₂ .nil))))))) =
      adR.eval (.cons r₁ (.cons q₂ .nil)) := by
  refine Expr.renameM_eval adR ?_
  intro u v
  cases v with
  | zero => rfl
  | succ v =>
    cases v with
    | zero => rfl
    | succ w => nomatch w

def compilePureRed (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : PureAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁) :
    CostedReduction O₂ I₂ G C₂ rIn₂ aIn₂ aOut₂ out₂ where
  σ := .prod (mapTy M.fSort R.σ) auxT
  init :=
    .bind (.ret A.splitIn)
      (.bind (.ret (.snd (.var .zero)))
        (.bind (.ret (.fst (.var (.succ .zero))))
          (.bind
            (Comp.wkTop2 (compilePureComp M R.init))
            (.ret
              (.pair
                (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptAIn))
                (.pair (.snd (.var .zero)) (.var (.succ (.succ .zero)))))))))
  handle :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptQ)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compilePureComp M R.handle))
            (.ret
              (.pair
                (.letE (.fst (.var .zero)) (callAdaptR A.adaptR))
                (.pair (.snd (.var .zero)) (.var (.succ (.succ (.succ .zero))))))))))
  finish :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptAOut)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compilePureComp M R.finish))
            (.ret
              (.letE (.var .zero) (Expr.wkTop1 A.adaptOut))))))

theorem compilePureRed_totalQueries_le (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : PureAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hSampQ : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQueryQ : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g)
    (q : ℕ) :
    (compilePureRed M A R).totalQueries w₂ ws₂ q ≤ R.totalQueries w₁ ws₁ q := by
  have hi := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSampQ hQueryQ R.init
  have hh := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSampQ hQueryQ R.handle
  have hf := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSampQ hQueryQ R.finish
  have hmul := Nat.mul_le_mul_left q hh
  simp only [CostedReduction.totalQueries, compilePureRed, Comp.queries, Comp.renameM_queries,
    zero_add, add_zero]
  omega

theorem compilePureRed_totalCost_le (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : PureAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁) (q : ℕ) :
    (compilePureRed M A R).totalCost q ≤
      (R.init.cost + compExcess M R.init + A.splitIn.cost + A.adaptAIn.cost + 24) +
      q * max I₂.uCost
        (R.handle.cost + compExcess M R.handle + A.adaptQ.cost + A.adaptR.cost +
          C₂.codecCost + 28) +
      (R.finish.cost + compExcess M R.finish + A.adaptAOut.cost + A.adaptOut.cost + 22) := by
  have hi := compilePureComp_cost_le M R.init
  have hh := compilePureComp_cost_le M R.handle
  have hf := compilePureComp_cost_le M R.finish
  have hinit :
      (compilePureRed M A R).init.cost ≤
        R.init.cost + compExcess M R.init + A.splitIn.cost + A.adaptAIn.cost + 24 := by
    simp only [compilePureRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hhandle :
      (compilePureRed M A R).handle.cost ≤
        R.handle.cost + compExcess M R.handle + A.adaptQ.cost + A.adaptR.cost + 28 := by
    simp only [compilePureRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, callAdaptR_cost,
      Expr.cost]
    omega
  have hfinish :
      (compilePureRed M A R).finish.cost ≤
        R.finish.cost + compExcess M R.finish + A.adaptAOut.cost + A.adaptOut.cost + 22 := by
    simp only [compilePureRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hmax :
      max I₂.uCost ((compilePureRed M A R).handle.cost + C₂.codecCost) ≤
      max I₂.uCost (R.handle.cost + compExcess M R.handle + A.adaptQ.cost + A.adaptR.cost +
        C₂.codecCost + 28) :=
    max_le_max le_rfl (by omega)
  have hmul := Nat.mul_le_mul_left q hmax
  dsimp only [CostedReduction.totalCost]
  omega

theorem compilePureRed_size_le (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : PureAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (S_max : ℕ) (hS : 1 ≤ S_max)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ S_max)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ S_max)
    (hQuery : ∀ g, (M.queryMacro g).size + 2 ≤ S_max) :
    (compilePureRed M A R).size ≤
      S_max * R.size + A.splitIn.size + A.adaptAIn.size +
      A.adaptQ.size + A.adaptR.size + A.adaptAOut.size + A.adaptOut.size + 74 := by
  have hi := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.init
  have hh := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.handle
  have hf := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.finish
  have hinit :
      (compilePureRed M A R).init.size ≤
        S_max * R.init.size + A.splitIn.size + A.adaptAIn.size + 24 := by
    simp only [compilePureRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  have hhandle :
      (compilePureRed M A R).handle.size ≤
        S_max * R.handle.size + A.adaptQ.size + A.adaptR.size + 28 := by
    simp only [compilePureRed, Comp.size, Comp.renameM_size, Expr.renameM_size, callAdaptR_size,
      Expr.size]
    omega
  have hfinish :
      (compilePureRed M A R).finish.size ≤
        S_max * R.finish.size + A.adaptAOut.size + A.adaptOut.size + 22 := by
    simp only [compilePureRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  dsimp only [CostedReduction.size]
  nlinarith

private theorem simulateQ_state_hom
    {σ₁ σ₂ : Type} (proj : σ₁ → σ₂)
    {impl₁ : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T))}
    {impl₂ : QueryImpl (unifSpec + G) (StateT σ₂ (OracleComp T))}
    (hStep : ∀ q s₁, (impl₂ q).run (proj s₁) = Prod.map id proj <$> (impl₁ q).run s₁)
    {α : Type} (oa : OracleComp (unifSpec + G) α) :
    ∀ s₁ : σ₁,
      (simulateQ impl₂ oa).run (proj s₁) = Prod.map id proj <$> (simulateQ impl₁ oa).run s₁ := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s₁; simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    intro s₁
    simp only [simulateQ_query_bind, StateT.run_bind]
    change
      (do let p ← (impl₂ q).run (proj s₁); (simulateQ impl₂ (mx p.1)).run p.2) =
        Prod.map id proj <$>
          (do let p ← (impl₁ q).run s₁; (simulateQ impl₁ (mx p.1)).run p.2)
    rw [hStep q s₁, bind_map_left, map_bind]
    exact bind_congr fun p => ih p.1 p.2

theorem compilePureRed_eval (M : PureBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (Ad : PureAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote)
    (x₂ : rIn₂.denote) (x₁ : rIn₁.denote) (aux : auxT.denote)
    (hSplit : Ad.splitIn.eval (.cons x₂ .nil) = (toVal M.fSort toDen rIn₁ x₁, aux))
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hOpE : ∀ o z,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) z) (.cons aux .nil)) =
        toVal M.fSort toDen (O₁.cod o) (O₁.eval o z))
    (hSampE : ∀ s z,
      (M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s z))
    (hQueryE : ∀ g z,
      (M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g z <$> (liftM (T.query (I₁.enc g z)) : OracleComp T _)))
    (hQ : ∀ t : κ,
      Ad.adaptQ.eval (.cons (C₂.qenc t) .nil) = toVal M.fSort toDen C₁.Q (C₁.qenc t))
    (hR : ∀ (t : κ) (r₁ : C₁.R.denote),
      C₂.rdec t (Ad.adaptR.eval (.cons (toVal M.fSort toDen C₁.R r₁) (.cons (C₂.qenc t) .nil))) =
        C₁.rdec t r₁)
    (adv₁ : aIn₁.denote → OracleComp (unifSpec + G) aOut₁.denote)
    (adv₂ : aIn₂.denote → OracleComp (unifSpec + G) aOut₂.denote)
    (toOut : aOut₁.denote → aOut₂.denote)
    (hAdv : ∀ a₁ : aIn₁.denote,
      adv₂ (Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ a₁) .nil)) = toOut <$> adv₁ a₁)
    (hAOut : ∀ b₁ : aOut₁.denote,
      Ad.adaptAOut.eval (.cons (toOut b₁) .nil) = toVal M.fSort toDen aOut₁ b₁)
    {outEq : out₁.denote → out₂.denote}
    (hOut : ∀ y₁ : out₁.denote,
      Ad.adaptOut.eval (.cons (toVal M.fSort toDen out₁ y₁) .nil) = outEq y₁) :
    (compilePureRed M Ad R).eval adv₂ x₂ = outEq <$> R.eval adv₁ x₁ := by
  let mkSt : R.σ.denote → (compilePureRed M Ad R).σ.denote :=
    fun s => (toVal M.fSort toDen R.σ s, aux)
  have hInit :
      (compilePureRed M Ad R).init.eval (.cons x₂ .nil) =
        (fun (p : (aIn₁.prod R.σ).denote) =>
          ((Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ p.1) .nil),
            mkSt p.2) : (aIn₂.prod (compilePureRed M Ad R).σ).denote)) <$>
          R.init.eval (.cons x₁ .nil) := by
    simp only [compilePureRed, Comp.eval, pure_bind, Expr.eval, Env.get, hSplit]
    rw [Comp.wkTop2_eval]
    change (do
      let x ← (compilePureComp M R.init).eval (mapEnvAux M.fSort toDen aux (.cons x₁ .nil))
      _) = _
    rw [compilePureComp_eval M toDen aux hOpE hSampE hQueryE R.init (.cons x₁ .nil),
      bind_map_left]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    refine bind_congr fun p => ?_
    congr 1; congr 1
    dsimp only [toVal]
    exact Expr.wkTop1_eval Ad.adaptAIn _ _
  have hStep :
      ∀ (q : (unifSpec + G).Domain) (s₁ : R.σ.denote),
        ((compilePureRed M Ad R).impl q).run (mkSt s₁) =
          Prod.map id mkSt <$> (R.impl q).run s₁ := by
    intro q s₁
    rcases q with n | t
    · change
        (StateT.lift (I₂.fwdU n)).run (mkSt s₁) =
          Prod.map id mkSt <$> (StateT.lift (I₁.fwdU n)).run s₁
      rw [StateT.run_lift, StateT.run_lift, hFwdU n]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq]
    · simp only [CostedReduction.impl, ReductionDsl.handlerImpl, StateT.run_mk, compilePureRed,
        Comp.eval, pure_bind, Expr.eval, Env.get, mkSt]
      have hq' :
          (Expr.wkTop1 Ad.adaptQ).eval
            (Env.cons (C₂.qenc t)
              (Env.cons aux
                (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
                  (toVal M.fSort toDen R.σ s₁, aux) (Env.cons (C₂.qenc t) Env.nil)))) =
            toVal M.fSort toDen C₁.Q (C₁.qenc t) := by
        rw [Expr.wkTop1_eval]; exact hQ t
      rw [hq', Comp.wkTop3_eval]
      have hm :
          Env.cons (toVal M.fSort toDen R.σ s₁)
            (Env.cons (toVal M.fSort toDen C₁.Q (C₁.qenc t)) (Env.cons aux Env.nil)) =
            mapEnvAux M.fSort toDen aux (.cons s₁ (.cons (C₁.qenc t) .nil)) := rfl
      dsimp only [compilePureRed, Ty.denote]
      rw [hm, compilePureComp_eval M toDen aux hOpE hSampE hQueryE R.handle
        (.cons s₁ (.cons (C₁.qenc t) .nil)), bind_map_left, bind_assoc, map_bind]
      refine OracleComp.bind_congr' rfl fun p => ?_
      simp only [pure_bind, map_pure, Prod.map, id_eq, toVal]
      congr 1; congr 1
      rw [callAdaptR_eval]
      exact hR t p.1
  unfold CostedReduction.eval
  rw [hInit, bind_map_left, map_bind]
  refine OracleComp.bind_congr' rfl fun p => ?_
  rcases p with ⟨a₁, s₁⟩
  dsimp only
  rw [hAdv a₁, simulateQ_map, StateT.run_map,
    simulateQ_state_hom mkSt hStep (adv₁ a₁) s₁]
  simp only [bind_map_left, map_bind, Prod.map, id_eq]
  refine OracleComp.bind_congr' rfl fun p' => ?_
  rcases p' with ⟨b₁, s₁'⟩
  dsimp only
  simp only [compilePureRed, Comp.eval, pure_bind, Expr.eval, Env.get, mkSt]
  have hb' :
      (Expr.wkTop1 Ad.adaptAOut).eval
        (Env.cons (toOut b₁)
          (Env.cons aux
            (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
              (toVal M.fSort toDen R.σ s₁', aux) (Env.cons (toOut b₁) Env.nil)))) =
        toVal M.fSort toDen aOut₁ b₁ := by
    rw [Expr.wkTop1_eval]; exact hAOut b₁
  rw [hb', Comp.wkTop3_eval]
  have hm' :
      Env.cons (toVal M.fSort toDen R.σ s₁')
        (Env.cons (toVal M.fSort toDen aOut₁ b₁) (Env.cons aux Env.nil)) =
        mapEnvAux M.fSort toDen aux (.cons s₁' (.cons b₁ .nil)) := rfl
  rw [hm', compilePureComp_eval M toDen aux hOpE hSampE hQueryE R.finish (.cons s₁' (.cons b₁ .nil)),
    bind_map_left, map_eq_bind_pure_comp, Function.comp_def]
  refine OracleComp.bind_congr' rfl fun y₁ => ?_
  congr 1
  rw [Expr.wkTop1_eval, hOut y₁]

end CompilePureRed

/-! ## Atomic operations and wire/tag helpers -/

section ProstParseLossless

private theorem prostDecodeVarintAux_length_le (i : ℕ) (acc : BitVec 64) (bs : List (BitVec 8))
    {v : BitVec 64} {rest : List (BitVec 8)}
    (h : decodeVarintAux i acc bs = some (v, rest)) :
    rest.length ≤ bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b tail ih =>
    simp only [decodeVarintAux] at h
    split at h
    · split at h
      · cases h
      · injection h with hp; injection hp with _ hr; subst hr; exact Nat.le_succ _
    · split at h
      · cases h
      · exact Nat.le_trans (ih _ _ h) (Nat.le_succ _)

private theorem prostDecodeVarint_length_le (bs : List (BitVec 8))
    {v : BitVec 64} {rest : List (BitVec 8)}
    (h : decodeVarint bs = some (v, rest)) :
    rest.length ≤ bs.length :=
  prostDecodeVarintAux_length_le 0 0 bs h

private theorem prostDecodeKey_length_le (bs : List (BitVec 8))
    {kw : ℕ × WireType} {rest : List (BitVec 8)}
    (h : decodeKey bs = some (kw, rest)) :
    rest.length ≤ bs.length := by
  unfold decodeKey at h
  cases hd : decodeVarint bs with
  | none => rw [hd] at h; cases h
  | some kr =>
    rcases kr with ⟨key, r0⟩
    have hr0 := prostDecodeVarint_length_le bs hd
    rw [hd] at h; dsimp only at h
    split at h
    · cases h
    · cases hw : WireType.ofNat? (key.toNat % 8) with
      | none => rw [hw] at h; cases h
      | some wt =>
        rw [hw] at h; dsimp only at h
        split at h
        · cases h
        · injection h with hp; injection hp with _ hr; subst hr; exact hr0

private theorem prostSkipBytes_length_le (n : ℕ) (bs : List (BitVec 8)) {rest : List (BitVec 8)}
    (h : skipBytes n bs = some rest) :
    rest.length ≤ bs.length := by
  unfold skipBytes at h
  split at h
  · cases h
  · injection h with hr; subst hr; simp

private theorem prostSkipScalar_length_le (wt : WireType) (bs : List (BitVec 8))
    {rest : List (BitVec 8)} (h : skipScalar wt bs = some rest) :
    rest.length ≤ bs.length := by
  unfold skipScalar at h
  cases wt with
  | varint =>
    rcases Option.mem_map.mp h with ⟨⟨_, _⟩, hd, rfl⟩
    exact prostDecodeVarint_length_le bs hd
  | thirtyTwoBit => exact prostSkipBytes_length_le 4 bs h
  | sixtyFourBit => exact prostSkipBytes_length_le 8 bs h
  | lengthDelimited =>
    cases hd : decodeVarint bs with
    | none => rw [hd] at h; cases h
    | some lr =>
      rcases lr with ⟨len, r0⟩
      rw [hd] at h; dsimp only at h
      exact Nat.le_trans (prostSkipBytes_length_le len.toNat r0 h)
        (prostDecodeVarint_length_le bs hd)
  | startGroup => cases h
  | endGroup => cases h

private theorem prostSkipField_group_length_le :
    ∀ fuel : ℕ,
      (∀ depth tag wt bs rest, skipField fuel depth tag wt bs = some rest →
        rest.length ≤ bs.length) ∧
      (∀ depth tag bs rest, skipGroup fuel depth tag bs = some rest →
        rest.length ≤ bs.length)
  | 0 => ⟨(fun _ _ _ _ _ h => by simp [skipField] at h),
          (fun _ _ _ _ h => by simp [skipGroup] at h)⟩
  | fuel + 1 => by
    obtain ⟨ihF, ihG⟩ := prostSkipField_group_length_le fuel
    refine ⟨?_, ?_⟩
    · intro depth tag wt bs rest h
      unfold skipField at h
      split at h
      · cases h
      · cases wt with
        | endGroup => cases h
        | startGroup => exact ihG depth tag bs rest h
        | varint => exact prostSkipScalar_length_le .varint bs h
        | sixtyFourBit => exact prostSkipScalar_length_le .sixtyFourBit bs h
        | lengthDelimited => exact prostSkipScalar_length_le .lengthDelimited bs h
        | thirtyTwoBit => exact prostSkipScalar_length_le .thirtyTwoBit bs h
    · intro depth tag bs rest h
      unfold skipGroup at h
      cases hk : decodeKey bs with
      | none => rw [hk] at h; cases h
      | some kw =>
        rcases kw with ⟨⟨itag, iwt⟩, r0⟩
        have hr0 := prostDecodeKey_length_le bs hk
        rw [hk] at h
        cases iwt with
        | endGroup =>
          dsimp only at h
          split at h
          · injection h with hr; subst hr; exact hr0
          · cases h
        | varint =>
          dsimp only at h
          cases hf : skipField fuel (depth - 1) itag .varint r0 with
          | none => rw [hf] at h; cases h
          | some r1 =>
            rw [hf] at h; dsimp only at h
            exact Nat.le_trans (ihG depth tag r1 rest h) (Nat.le_trans (ihF _ _ _ r0 r1 hf) hr0)
        | sixtyFourBit =>
          dsimp only at h
          cases hf : skipField fuel (depth - 1) itag .sixtyFourBit r0 with
          | none => rw [hf] at h; cases h
          | some r1 =>
            rw [hf] at h; dsimp only at h
            exact Nat.le_trans (ihG depth tag r1 rest h) (Nat.le_trans (ihF _ _ _ r0 r1 hf) hr0)
        | lengthDelimited =>
          dsimp only at h
          cases hf : skipField fuel (depth - 1) itag .lengthDelimited r0 with
          | none => rw [hf] at h; cases h
          | some r1 =>
            rw [hf] at h; dsimp only at h
            exact Nat.le_trans (ihG depth tag r1 rest h) (Nat.le_trans (ihF _ _ _ r0 r1 hf) hr0)
        | startGroup =>
          dsimp only at h
          cases hf : skipField fuel (depth - 1) itag .startGroup r0 with
          | none => rw [hf] at h; cases h
          | some r1 =>
            rw [hf] at h; dsimp only at h
            exact Nat.le_trans (ihG depth tag r1 rest h) (Nat.le_trans (ihF _ _ _ r0 r1 hf) hr0)
        | thirtyTwoBit =>
          dsimp only at h
          cases hf : skipField fuel (depth - 1) itag .thirtyTwoBit r0 with
          | none => rw [hf] at h; cases h
          | some r1 =>
            rw [hf] at h; dsimp only at h
            exact Nat.le_trans (ihG depth tag r1 rest h) (Nat.le_trans (ihF _ _ _ r0 r1 hf) hr0)

private theorem prostMergeBytes_length_le (wt : WireType) (bs : List (BitVec 8))
    {v rest : List (BitVec 8)} (h : mergeBytes wt bs = some (v, rest)) :
    v.length ≤ bs.length ∧ rest.length ≤ bs.length := by
  unfold mergeBytes at h
  split at h
  · cases h
  · cases hd : decodeVarint bs with
    | none => rw [hd] at h; cases h
    | some lr =>
      rcases lr with ⟨len, r0⟩
      have hr0 := prostDecodeVarint_length_le bs hd
      rw [hd] at h; dsimp only at h
      split at h
      · cases h
      · injection h with hp; injection hp with hv hr; subst hv hr
        exact ⟨Nat.le_trans (List.length_take_le' _ _) hr0, by simp; omega⟩

private theorem prostMergeUint32_length_le (wt : WireType) (bs : List (BitVec 8))
    {v : BitVec 32} {rest : List (BitVec 8)}
    (h : mergeUint32 wt bs = some (v, rest)) :
    rest.length ≤ bs.length := by
  unfold mergeUint32 at h
  split at h
  · cases h
  · cases hd : decodeVarint bs with
    | none => rw [hd] at h; cases h
    | some vr =>
      rcases vr with ⟨_, r0⟩
      rw [hd] at h; dsimp only at h
      injection h with hp; injection hp with _ hr; subst hr
      exact prostDecodeVarint_length_le bs hd

private def ProtoSignalFieldsLe (N : ℕ) (p : ProtoSignalMessage) : Prop :=
  (∀ v ∈ p.ciphertext, v.length ≤ N) ∧
  (∀ v ∈ p.pqRatchet, v.length ≤ N) ∧
  (∀ v ∈ p.addresses, v.length ≤ N)

private theorem prostMergeField_preserves {N : ℕ} {p p' : ProtoSignalMessage}
    {tag : ℕ} {wt : WireType} {bs rest : List (BitVec 8)}
    (hp : ProtoSignalFieldsLe N p) (hbs : bs.length ≤ N)
    (h : mergeField p tag wt bs = some (p', rest)) :
    ProtoSignalFieldsLe N p' ∧ rest.length ≤ bs.length := by
  unfold mergeField at h
  match tag with
  | 1 =>
    rcases Option.mem_map.mp h with ⟨⟨_, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq; subst hp_eq hr_eq
    exact ⟨hp, (prostMergeBytes_length_le wt bs hm).2⟩
  | 2 =>
    rcases Option.mem_map.mp h with ⟨⟨_, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq; subst hp_eq hr_eq
    exact ⟨hp, prostMergeUint32_length_le wt bs hm⟩
  | 3 =>
    rcases Option.mem_map.mp h with ⟨⟨_, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq; subst hp_eq hr_eq
    exact ⟨hp, prostMergeUint32_length_le wt bs hm⟩
  | 4 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq; subst hp_eq hr_eq
    obtain ⟨hv, hr⟩ := prostMergeBytes_length_le wt bs hm
    refine ⟨⟨?_, hp.2.1, hp.2.2⟩, hr⟩
    intro w hw; simp only [Option.mem_def, Option.some.injEq] at hw; subst hw
    exact Nat.le_trans hv hbs
  | 5 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq; subst hp_eq hr_eq
    obtain ⟨hv, hr⟩ := prostMergeBytes_length_le wt bs hm
    refine ⟨⟨hp.1, ?_, hp.2.2⟩, hr⟩
    intro w hw; simp only [Option.mem_def, Option.some.injEq] at hw; subst hw
    exact Nat.le_trans hv hbs
  | 6 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq; subst hp_eq hr_eq
    obtain ⟨hv, hr⟩ := prostMergeBytes_length_le wt bs hm
    refine ⟨⟨hp.1, hp.2.1, ?_⟩, hr⟩
    intro w hw; simp only [Option.mem_def, Option.some.injEq] at hw; subst hw
    exact Nat.le_trans hv hbs
  | 0 | _ + 7 =>
    rcases Option.mem_map.mp h with ⟨r, hs, hp'⟩
    injection hp' with hp_eq hr_eq; subst hp_eq hr_eq
    exact ⟨hp, (prostSkipField_group_length_le (2 * bs.length + 2)).1 _ _ _ bs r hs⟩

private theorem prostDecodeLoop_preserves (fuel N : ℕ) (p : ProtoSignalMessage)
    (bs : List (BitVec 8)) {p' : ProtoSignalMessage}
    (hp : ProtoSignalFieldsLe N p) (hbs : bs.length ≤ N)
    (h : decodeLoop fuel p bs = some p') :
    ProtoSignalFieldsLe N p' := by
  induction fuel generalizing p bs with
  | zero =>
    cases bs with
    | nil => simp only [decodeLoop, Option.some.injEq] at h; subst h; exact hp
    | cons _ _ => simp [decodeLoop] at h
  | succ fuel ih =>
    cases bs with
    | nil => simp only [decodeLoop, Option.some.injEq] at h; subst h; exact hp
    | cons b tail =>
      simp only [decodeLoop] at h
      cases hk : decodeKey (b :: tail) with
      | none => rw [hk] at h; cases h
      | some kw =>
        rcases kw with ⟨⟨tag, wt⟩, rest⟩
        have hrest := Nat.le_trans (prostDecodeKey_length_le (b :: tail) hk) hbs
        rw [hk] at h; dsimp only at h
        cases hm : mergeField p tag wt rest with
        | none => rw [hm] at h; cases h
        | some pr =>
          rcases pr with ⟨p1, rest'⟩
          obtain ⟨hp1, hrest'⟩ := prostMergeField_preserves hp hrest hm
          rw [hm] at h; dsimp only at h
          exact ih p1 rest' hp1 (Nat.le_trans hrest' hrest) h

theorem atomicPureOps_eval_signalMsgParse_lossless (ℓ : ℕ) (Pt : Type) (body : List (BitVec 8)) :
    (atomicPureOps ℓ Pt).eval .signalMsgParse body =
      match SignalMessage.tryFrom protoSignalCodec body with
      | .ok m =>
        some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
              (m.ciphertext, (m.pqRatchet, m.addresses)))
      | .error _ => none := by
  dsimp only [atomicPureOps, AtomicPureOp.eval]
  rcases hm : SignalMessage.tryFrom protoSignalCodec body with _ | m
  · rfl
  · dsimp only
    have hfields :
        m.ciphertext.length ≤ body.length ∧
        m.pqRatchet.length ≤ body.length ∧
        (∀ a ∈ m.addresses, a.length ≤ body.length) := by
      unfold SignalMessage.tryFrom at hm
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hm
      split at hm
      · cases hm
      · split at hm
        · cases hm
        · split at hm
          · cases hm
          · cases hdec : protoSignalCodec.decode ((body.take (body.length - macLength)).drop 1) with
            | none => rw [hdec] at hm; cases hm
            | some p =>
              rw [hdec] at hm; dsimp only at hm
              cases hrk : p.ratchetKey with
              | none => rw [hrk] at hm; cases hm
              | some rk =>
                rw [hrk] at hm; dsimp only at hm
                cases hdes : PublicKey.deserialize rk with
                | error _ => rw [hdes] at hm; cases hm
                | ok srk =>
                  rw [hdes] at hm; dsimp only at hm
                  cases hctr : p.counter with
                  | none => rw [hctr] at hm; cases hm
                  | some ctr =>
                    rw [hctr] at hm; dsimp only at hm
                    cases hct : p.ciphertext with
                    | none => rw [hct] at hm; cases hm
                    | some ct =>
                      rw [hct] at hm; dsimp only at hm
                      injection hm with hm'; subst hm'
                      have hbuf : ((body.take (body.length - macLength)).drop 1).length ≤
                          body.length := by
                        have := List.length_take_le (body.length - macLength) body
                        simp only [List.length_drop]; omega
                      have hemp : ProtoSignalFieldsLe body.length emptyProtoSignalMessage :=
                        ⟨by simp [emptyProtoSignalMessage],
                         by simp [emptyProtoSignalMessage],
                         by simp [emptyProtoSignalMessage]⟩
                      have hp := prostDecodeLoop_preserves _ body.length emptyProtoSignalMessage _
                        hemp hbuf hdec
                      refine ⟨hp.1 ct hct, ?_, hp.2.2⟩
                      cases hpq : p.pqRatchet with
                      | none => simp
                      | some pq => exact hp.2.1 pq hpq
    obtain ⟨hct, hpq, haddr⟩ := hfields
    have hmap : m.addresses.map (·.take body.length) = m.addresses := by
      cases ha : m.addresses with
      | none => rfl
      | some a => dsimp only [Option.map]; rw [List.take_of_length_le (haddr a ha)]
    rw [List.take_of_length_le hct, List.take_of_length_le hpq, hmap]

end ProstParseLossless

section TagAndKeyHelpers

private theorem extractLsb'_zero_bytesToWordLE64_cons (b : BitVec 8) (acc : BitVec 64) :
    ((acc <<< 8) ||| b.zeroExtend 64).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h64 : i < 64 := by omega
  simp [hi, h64]

private theorem extractLsb'_succ_bytesToWordLE64_cons (b : BitVec 8) (acc : BitVec 64) (j : ℕ)
    (hj : j + 1 < 8) :
    ((acc <<< 8) ||| b.zeroExtend 64).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 64 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToWordLE64 (bs : List (BitVec 8)) (j : ℕ)
    (hj : j < bs.length) (h8 : j < 8) :
    (bytesToWordLE 64 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [bytesToWordLE] using extractLsb'_zero_bytesToWordLE64_cons b (bytesToWordLE 64 rest)
    | succ j =>
      have hcons : bytesToWordLE 64 (b :: rest) =
          (bytesToWordLE 64 rest <<< 8) ||| b.zeroExtend 64 := rfl
      rw [hcons, extractLsb'_succ_bytesToWordLE64_cons b (bytesToWordLE 64 rest) j h8,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

@[simp] theorem toLEBytes8_length (v : BitVec 64) : (toLEBytes 8 v).length = 8 := by
  simp [toLEBytes]

theorem toLEBytes8_zero : toLEBytes 8 (0#64) = List.replicate 8 0#8 := by
  refine List.ext_getElem (by simp [toLEBytes]) fun j h1 h2 => ?_
  simp [toLEBytes]

theorem bytesToWordLE64_eq_bytesToWord64LE (bs : List (BitVec 8)) :
    bytesToWordLE 64 bs = bytesToWord64LE bs := rfl

theorem bytesToWordLE64_toLEBytes8 (v : BitVec 64) :
    bytesToWordLE 64 (toLEBytes 8 v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hj : i / 8 < 8 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToWordLE64 (toLEBytes 8 v) (i / 8) (by simp [toLEBytes, hj]) hj)
  simp only [toLEBytes, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr, decide_true,
    Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

theorem toLEBytes8_bytesToWordLE64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    toLEBytes 8 (bytesToWordLE 64 bs) = bs := by
  refine List.ext_getElem (by simp [toLEBytes, h]) fun j h1 h2 => ?_
  simp only [toLEBytes, List.getElem_ofFn]
  exact extractLsb'_bytesToWordLE64 bs j h2 (by omega)

private theorem flatMap_toBEBytes4_length :
    ∀ l : List (BitVec 32), (l.flatMap (toBEBytes 4)).length = 4 * l.length
  | [] => rfl
  | _ :: bs => by
    simp only [List.flatMap_cons, List.length_append, toBEBytes, List.length_ofFn,
      List.length_cons, flatMap_toBEBytes4_length bs]
    omega

theorem sha256With_length (F : ShaCompress) (m : List (BitVec 8)) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  rw [flatMap_toBEBytes4_length, List.Vector.toList_length]

theorem hmacWith_length (F : ShaCompress) (k m : List (BitVec 8)) :
    (hmacWith F k m).length = 32 := by
  unfold hmacWith
  exact sha256With_length F _

theorem computeMac_length (F : ShaCompress) (idS idR : IdentityKey) (macKey : BitVec 256)
    (msg : List (BitVec 8)) :
    (computeMac F idS idR macKey msg).length = 8 := by
  unfold computeMac hmacSha256Trunc8
  rw [List.length_take, hmacWith_length]
  decide

@[simp] theorem ofU8_toU8 (bs : List (BitVec 8)) : ofU8 (toU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b tail ih => simp [ofU8, toU8] at ih ⊢; exact ih

@[simp] theorem u8Vec32_vecU8 (v : List.Vector (BitVec 8) 32) :
    u8Vec 32 (vecU8 v) = v := by
  apply Subtype.ext
  simp [u8Vec, vecU8, fitVec, v.toList_length]

/-- Predicate ensuring `AtomicSymOp.signalMsgEncode` runs without output clamping. -/
@[reducible] def atomicShortPubB (p : LibsignalMsgPublicPart) : Bool :=
  decide (p.pqmsg.length ≤ 96) && p.addrs.all fun a => decide (a.length ≤ 128)

theorem atomicShortPubB_imp_shortB {p : LibsignalMsgPublicPart}
    (h : atomicShortPubB p = true) : p.shortB = true := by
  simp only [atomicShortPubB, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [LibsignalMsgPublicPart.shortB, Bool.and_eq_true]
  refine ⟨decide_eq_true (Nat.lt_of_le_of_lt h.1 (show 96 < 2 ^ 29 by decide)), ?_⟩
  cases ha : p.addrs with
  | none => rfl
  | some a =>
    simp only [ha, Option.all_some, decide_eq_true_eq] at h ⊢
    exact Nat.lt_of_le_of_lt h.2 (show 128 < 2 ^ 29 by decide)

end TagAndKeyHelpers


/-! ## Atomic AEAD, symmetric ratchet, and fallback CKA -/

section ShallowSchemes

theorem tryFrom_append_sfx8 (codec : SignalMessageProtoCodec)
    (ser mac₁ mac₂ : List (BitVec 8))
    (hm₁ : mac₁.length = macLength) (hm₂ : mac₂.length = macLength) :
    SignalMessage.tryFrom codec (ser ++ mac₁) =
      (SignalMessage.tryFrom codec (ser ++ mac₂)).map
        (fun m => { m with serialized := ser ++ mac₁ }) := by
  cases ser with
  | nil =>
    unfold SignalMessage.tryFrom
    simp only [List.nil_append, hm₁, hm₂, macLength, show (8 : ℕ) < 8 + 1 by decide, ↓reduceIte]
    rfl
  | cons hd tl =>
    have hlen : (hd :: tl ++ mac₁).length = (hd :: tl ++ mac₂).length := by
      simp [hm₁, hm₂]
    have hhead : (hd :: tl ++ mac₁).headD 0 = (hd :: tl ++ mac₂).headD 0 := rfl
    have htake₁ :
        (hd :: tl ++ mac₁).take ((hd :: tl ++ mac₁).length - macLength) = hd :: tl := by
      rw [List.length_append, hm₁, Nat.add_sub_cancel,
        List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    have htake₂ :
        (hd :: tl ++ mac₂).take ((hd :: tl ++ mac₂).length - macLength) = hd :: tl := by
      rw [List.length_append, hm₂, Nat.add_sub_cancel,
        List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    unfold SignalMessage.tryFrom
    rw [htake₁, htake₂, hlen, hhead]
    dsimp only [Bind.bind, Except.bind]
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> rfl

theorem macIds_ite_mod2 (idOf : Party → IdentityKey) (t : ℕ) :
    (let p := if t % 2 = 1 then (idOf .A, idOf .B) else (idOf .B, idOf .A)
     macIds p.1 p.2) = lIds idOf t := by
  unfold lIds Party.senderOf Party.other
  by_cases h : t % 2 = 1 <;> simp [h]

theorem addressCheckPasses_self (x : Option (List (BitVec 8))) :
    addressCheckPasses x x = true := by
  cases x with
  | none => rfl
  | some a => simp [addressCheckPasses]

def aeadAtomicEnc {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (seed : BitVec 256)
    (a : (ℕ × CryptoGames.SM.Construction.Header Pt) × LibsignalMsgPublicPart) (m : Plain ℓ) :
    LibsignalCiphertextWithSalt32 :=
  let ids := if a.1.2.1 % 2 = 1 then (idOf .A, idOf .B) else (idOf .B, idOf .A)
  let mks := MessageKeyGenerator.generateKeys C.F ⟨keyToBytes32 seed, 0#32⟩ (some a.2.salt)
  let ct := (aesCbcEncrypt C.E mks.cipherKey mks.iv m.toList).take (32 * (ℓ / 32 + 2))
  let srk := match a.1.2.2 with | none => dummyKey | some T => encT T
  let raw := (SignalMessage.new C.F protoSignalCodec currentVersion mks.macKey a.2.addrs srk
    (BitVec.ofNat 32 (a.1.1 - 1)) a.2.pn ct ids.1 ids.2 a.2.pqmsg).serialized.take
      (32 * (2 * (ℓ / 32) + 24))
  ((raw.take (raw.length - 8), bytesToWordLE 64 ((raw.drop (raw.length - 8)).take 8)), a.2.salt)

def aeadAtomic {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    AEADScheme (BitVec 256) ((ℕ × CryptoGames.SM.Construction.Header Pt) × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32 where
  enc := aeadAtomicEnc C ℓ encT idOf
  dec := (lAead C protoSignalCodec ℓ encT idOf).dec

@[simp] theorem aeadAtomic_dec_eq {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    (aeadAtomic C ℓ encT idOf).dec = (lAead C protoSignalCodec ℓ encT idOf).dec := rfl

private theorem aesCbcEncrypt_eq_cbcPkcs7 {ℓ : ℕ} (E : BitVec 256 → Block → Block)
    (k : BitVec 256) (iv : Block) (m : Plain ℓ) :
    aesCbcEncrypt E k iv m.toList =
      ((CryptoGames.CBC.cbcPkcs7EncryptOnly E ℓ).enc (k, iv) m).toList.flatMap blockToBytesLE := by
  rcases m with ⟨mList, rfl⟩
  rfl

theorem aeadAtomic_enc_eq {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (seed : BitVec 256)
    (a : (ℕ × CryptoGames.SM.Construction.Header Pt) × LibsignalMsgPublicPart) (m : Plain ℓ)
    (hshort : atomicShortPubB a.2 = true) :
    (aeadAtomic C ℓ encT idOf).enc seed a m =
      (lAead C protoSignalCodec ℓ encT idOf).enc seed a m := by
  rcases a with ⟨⟨i, ⟨t, T?⟩⟩, ⟨pn, pqmsg, salt, addrs⟩⟩
  simp only [atomicShortPubB, Bool.and_eq_true, decide_eq_true_eq] at hshort
  have haddr : ∀ x ∈ addrs, x.length ≤ 128 := by
    intro x hx; cases addrs with
    | none => cases hx
    | some y =>
      simp only [Option.mem_def, Option.some.injEq] at hx; subst hx
      simpa using hshort.2
  dsimp only [aeadAtomic, aeadAtomicEnc, lAead, lAeadK, lWire, libsignalWireAead,
    CryptoGames.LibsignalAead.wireEncode,
    signalWireCodec, lHeader, MessageKeyGenerator.generateKeys]
  set dk := deriveMessageKeys C.F (some salt) (keyToBytes32 seed)
  set ct0 := aesCbcEncrypt C.E dk.1.1 dk.1.2 m.toList
  have hct0 : ct0.length ≤ 32 * (ℓ / 32 + 2) := by
    have heq : ct0.length = 16 * (ℓ / 16 + 1) := aesCbcEncrypt_length_eq C.E dk.1.1 dk.1.2 m
    omega
  have htake_ct : ct0.take (32 * (ℓ / 32 + 2)) = ct0 := List.take_of_length_le hct0
  rw [htake_ct]
  set ids := if t % 2 = 1 then (idOf .A, idOf .B) else (idOf .B, idOf .A)
  set srk := match T? with | none => dummyKey | some T => encT T
  have hsrk : (T?.map encT).getD dummyKey = srk := by cases T? <;> rfl
  have hraw_le :
      (SignalMessage.new C.F protoSignalCodec currentVersion dk.2 addrs srk
        (BitVec.ofNat 32 (i - 1)) pn ct0 ids.1 ids.2 pqmsg).serialized.length ≤
        32 * (2 * (ℓ / 32) + 24) := by
    have h450 := signalMsgNew_serialized_length_le (ℓ := ℓ) C.F currentVersion dk.2
      addrs srk (BitVec.ofNat 32 (i - 1)) pn ct0 ids.1 ids.2 pqmsg hct0 hshort.1 haddr
    omega
  rw [List.take_of_length_le hraw_le]
  dsimp only [SignalMessage.new]
  set ser := serializeContent protoSignalCodec currentVersion srk
    (BitVec.ofNat 32 (i - 1)) pn ct0 pqmsg addrs
  set mac := computeMac C.F ids.1 ids.2 dk.2 ser
  have hmac_len : mac.length = 8 := computeMac_length C.F ids.1 ids.2 dk.2 ser
  have htake_ser : (ser ++ mac).take ((ser ++ mac).length - 8) = ser := by
    rw [List.length_append, hmac_len, Nat.add_sub_cancel,
      List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hdrop_mac : ((ser ++ mac).drop ((ser ++ mac).length - 8)).take 8 = mac := by
    rw [List.length_append, hmac_len, Nat.add_sub_cancel,
      List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append,
      List.take_of_length_le (Nat.le_of_eq hmac_len)]
  rw [htake_ser, hdrop_mac, hsrk]
  have hids : macIds ids.1 ids.2 = lIds idOf t := macIds_ite_mod2 idOf t
  dsimp only [mac, computeMac, hmacScheme, ser, ct0]
  rw [aesCbcEncrypt_eq_cbcPkcs7, bytesToWordLE64_eq_bytesToWord64LE, hids]

def fsAtomic {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) :=
  fromAEADPRG ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
    (lChainPRG C.F) maxForwardJumps

def fsAtomicB {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (B : ℕ) :
    FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) :=
  let fs0 := fsAtomic C ℓ encT idOf
  { fs0 with
    receive := fun v a c =>
      fs0.receive { v with skippedKeys := v.skippedKeys.take B } a c }

@[simp] theorem fsAtomic_receive_eq {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) :
    (fsAtomic C ℓ encT idOf).receive =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive := by
  funext v a c
  dsimp only [fsAtomic, lFS, fromAEADPRG, AEADScheme.movePubPartToAD, aeadAtomic]

theorem fsAtomicB_send_eq {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (B : ℕ)
    (v : RatchetSenderState (BitVec 256)) (a : CryptoGames.SM.Construction.Header Pt)
    (m : LibsignalMsgPublicPart × Plain ℓ) (hshort : atomicShortPubB m.1 = true) :
    (fsAtomicB C ℓ encT idOf B).send v a m =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).send v a m := by
  dsimp only [fsAtomicB, fsAtomic, lFS, fromAEADPRG, AEADScheme.movePubPartToAD]
  rw [aeadAtomic_enc_eq C ℓ encT idOf _ ((v.lastIndex + 1, a), m.1) m.2 hshort]

theorem fsAtomicB_receive_eq_fsAtomic {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (B : ℕ)
    (v : RatchetReceiverState (BitVec 256) (BitVec 256)) (a : CryptoGames.SM.Construction.Header Pt)
    (c : ℕ × LibsignalCiphertextWithSalt32) (hlen : v.skippedKeys.length ≤ B) :
    (fsAtomicB C ℓ encT idOf B).receive v a c = (fsAtomic C ℓ encT idOf).receive v a c := by
  dsimp only [fsAtomicB]
  rw [List.take_of_length_le hlen]

theorem fsAtomicB_receive_eq {Pt : Type} (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (B : ℕ)
    (v : RatchetReceiverState (BitVec 256) (BitVec 256)) (a : CryptoGames.SM.Construction.Header Pt)
    (c : ℕ × LibsignalCiphertextWithSalt32) (hlen : v.skippedKeys.length ≤ B) :
    (fsAtomicB C ℓ encT idOf B).receive v a c =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive v a c :=
  fsAtomicB_receive_eq_fsAtomic C ℓ encT idOf B v a c hlen

theorem skipKeys_length {CK MK : Type} (G : ℕ → PRGScheme CK (CK × MK)) :
    ∀ (n : ℕ) (w : CK) (p : ℕ) (acc : List (ℕ × MK)),
      (skipKeys G n w p acc).2.length = acc.length + n
  | 0, _, _, acc => by simp [skipKeys]
  | n + 1, w, p, acc => by
    simp only [skipKeys, skipKeys_length G n, List.length_cons]
    omega

def RSReachB {CK MK : Type} (maxSkip k : ℕ) (v : RatchetReceiverState CK MK) : Prop :=
  CryptoGames.SM.Engine.RSReach maxSkip k v ∧ v.skippedKeys.length ≤ v.lastIndex

theorem RSReachB.init {CK MK AD M C : Type}
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (k : CK) :
    RSReachB maxSkip 0 ((fromAEADPRG ae G maxSkip).initReceiver k) :=
  ⟨CryptoGames.SM.Engine.RSReach.init ae G maxSkip k, by simp [fromAEADPRG]⟩

theorem RSReachB.mono {CK MK : Type} {maxSkip k k' : ℕ}
    {v : RatchetReceiverState CK MK}
    (hk : k ≤ k') (h : RSReachB maxSkip k v) : RSReachB maxSkip k' v :=
  ⟨h.1.mono hk, h.2⟩

theorem RSReachB.receive_fromAEADPRG {CK MK AD M C : Type}
    (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip k : ℕ)
    {v v' : RatchetReceiverState CK MK} {a : AD} {c : ℕ × C} {i : ℕ} {m : M}
    (hv : RSReachB maxSkip k v)
    (hrec : (fromAEADPRG ae G maxSkip).receive v a c = some (v', i, m)) :
    i ≤ (k + 1) * (maxSkip + 1) ∧ RSReachB maxSkip (k + 1) v' := by
  have ⟨hi, hrs⟩ := CryptoGames.SM.Engine.RSReach.receive ae G maxSkip k hv.1 hrec
  refine ⟨hi, hrs, ?_⟩
  rcases c with ⟨idx, e⟩
  dsimp only [fromAEADPRG] at hrec
  rcases hlk : v.skippedKeys.lookup idx with _ | key
  · rw [hlk] at hrec
    split_ifs at hrec with hbad
    have hnot : ¬ idx ≤ v.lastIndex ∧ ¬ maxSkip < idx - v.lastIndex - 1 := not_or.mp hbad
    rcases hdec : ae.dec ((G (idx - 1)).gen
        (skipKeys G (idx - v.lastIndex - 1) v.chainKey v.lastIndex v.skippedKeys).1).2
        (idx, a) e with _ | m'
    · rw [hdec] at hrec; cases hrec
    · rw [hdec] at hrec
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl, rfl⟩
      dsimp only
      rw [skipKeys_length]
      have := hv.2
      omega
  · rw [hlk] at hrec
    dsimp only at hrec
    rcases hdec : ae.dec key (idx, a) e with _ | m'
    · rw [hdec] at hrec; cases hrec
    · rw [hdec] at hrec
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl, rfl⟩
      exact Nat.le_trans (List.length_filter_le _ _) hv.2

/-- `Dh.base`-fallback variant of `CKA.dhScheme` agreeing on ping-pong reachable states without `0 : Pt`. -/
def dhSchemeFb {Sc Pt : Type} (D : DHFun Sc Pt) :
    CKAScheme Sc (CryptoGames.CKA.DDH.State Sc Pt) Sc Pt Pt where
  initA x₀ := .pub (D.dh x₀ D.base)
  initB x₀ := .exp x₀
  send γ x := match γ with
    | .pub h => (.exp x, D.dh x D.base, D.dh x h)
    | .exp _ => (.exp x, D.dh x D.base, D.base)
  receive γ T := match γ with
    | .exp x => (.pub T, D.dh x T)
    | .pub _ => (.pub T, D.base)

@[simp] theorem dhSchemeFb_initA_eq {Sc Pt : Type} [Zero Pt] (D : DHFun Sc Pt) :
    (dhSchemeFb D).initA = (dhScheme D).initA := rfl

@[simp] theorem dhSchemeFb_initB_eq {Sc Pt : Type} [Zero Pt] (D : DHFun Sc Pt) :
    (dhSchemeFb D).initB = (dhScheme D).initB := rfl

@[simp] theorem dhSchemeFb_send_pub {Sc Pt : Type} [Zero Pt] (D : DHFun Sc Pt) (h : Pt) (x : Sc) :
    (dhSchemeFb D).send (.pub h) x = (dhScheme D).send (.pub h) x := rfl

@[simp] theorem dhSchemeFb_receive_exp {Sc Pt : Type} [Zero Pt] (D : DHFun Sc Pt) (x : Sc)
    (T : Pt) :
    (dhSchemeFb D).receive (.exp x) T = (dhScheme D).receive (.exp x) T := rfl

end ShallowSchemes


/-! ## Atomic `Expr` operator macros -/

section AtomicOpMacros

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (lam : Pt)

local notation "O" => atomicFig8Ops ℓ Pt C Dh encPt encT lam
local notation "S" => atomicSig ℓ Pt

def opPure {Γ : List (Ty S)} (o : AtomicPureOp) (a : Expr O Γ (o.dom ℓ Pt)) :
    Expr O Γ (o.cod ℓ Pt) :=
  @Expr.op S O Γ (Sum.inl (Sum.inl o)) a

def opPtEncPk {Γ : List (Ty S)} (a : Expr O Γ PtT) : Expr O Γ PK :=
  @Expr.op S O Γ (Sum.inl (Sum.inr (Sum.inl AtomicPtEncOp.ptEncPk))) a

def opSym {Γ : List (Ty S)} (o : AtomicSymOp) (a : Expr O Γ (o.dom ℓ Pt)) :
    Expr O Γ (o.cod ℓ Pt) :=
  @Expr.op S O Γ (Sum.inl (Sum.inr (Sum.inr o))) a

def opGrp {Γ : List (Ty S)} (o : AtomicGroupOp) (a : Expr O Γ (o.dom ℓ Pt)) :
    Expr O Γ (o.cod ℓ Pt) :=
  @Expr.op S O Γ (Sum.inr o) a

@[simp] private theorem env_get_zero {S' : Sig} {Γ : List (Ty S')} {t : Ty S'}
    (x : t.denote) (ρ : Env Γ) : (Env.cons x ρ).get .zero = x := rfl

@[simp] private theorem env_get_succ {S' : Sig} {Γ : List (Ty S')} {t u : Ty S'}
    (x : u.denote) (ρ : Env Γ) (v : Var Γ t) : (Env.cons x ρ).get (.succ v) = ρ.get v := rfl

@[simp] theorem opPure_eval {Γ : List (Ty S)} (o : AtomicPureOp) (a : Expr O Γ (o.dom ℓ Pt))
    (ρ : Env Γ) :
    (opPure ℓ Pt C Dh encPt encT lam o a).eval ρ = o.eval ℓ Pt (a.eval ρ) := rfl

@[simp] theorem opPure_cost {Γ : List (Ty S)} (o : AtomicPureOp) (a : Expr O Γ (o.dom ℓ Pt)) :
    (opPure ℓ Pt C Dh encPt encT lam o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem opPtEncPk_eval {Γ : List (Ty S)} (a : Expr O Γ PtT) (ρ : Env Γ) :
    (opPtEncPk ℓ Pt C Dh encPt encT lam a).eval ρ = encT (a.eval ρ) := rfl

@[simp] theorem opPtEncPk_cost {Γ : List (Ty S)} (a : Expr O Γ PtT) :
    (opPtEncPk ℓ Pt C Dh encPt encT lam a).cost = a.cost + 4 := rfl

@[simp] theorem opSym_eval {Γ : List (Ty S)} (o : AtomicSymOp) (a : Expr O Γ (o.dom ℓ Pt))
    (ρ : Env Γ) :
    (opSym ℓ Pt C Dh encPt encT lam o a).eval ρ = o.eval ℓ Pt C (a.eval ρ) := rfl

@[simp] theorem opSym_cost {Γ : List (Ty S)} (o : AtomicSymOp) (a : Expr O Γ (o.dom ℓ Pt)) :
    (opSym ℓ Pt C Dh encPt encT lam o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem opGrp_eval {Γ : List (Ty S)} (o : AtomicGroupOp) (a : Expr O Γ (o.dom ℓ Pt))
    (ρ : Env Γ) :
    (opGrp ℓ Pt C Dh encPt encT lam o a).eval ρ = o.eval ℓ Pt C Dh encPt lam (a.eval ρ) := rfl

@[simp] theorem opGrp_cost {Γ : List (Ty S)} (o : AtomicGroupOp) (a : Expr O Γ (o.dom ℓ Pt)) :
    (opGrp ℓ Pt C Dh encPt encT lam o a).cost = a.cost + o.cost := rfl

@[simp] theorem opPure_size {Γ : List (Ty S)} (o : AtomicPureOp) (a : Expr O Γ (o.dom ℓ Pt)) :
    (opPure ℓ Pt C Dh encPt encT lam o a).size = a.size + o.opSize + 1 := rfl

@[simp] theorem opPtEncPk_size {Γ : List (Ty S)} (a : Expr O Γ PtT) :
    (opPtEncPk ℓ Pt C Dh encPt encT lam a).size = a.size + 1 := rfl

@[simp] theorem opSym_size {Γ : List (Ty S)} (o : AtomicSymOp) (a : Expr O Γ (o.dom ℓ Pt)) :
    (opSym ℓ Pt C Dh encPt encT lam o a).size = a.size + 1 := rfl

@[simp] theorem opGrp_size {Γ : List (Ty S)} (o : AtomicGroupOp) (a : Expr O Γ (o.dom ℓ Pt)) :
    (opGrp ℓ Pt C Dh encPt encT lam o a).size = a.size + 1 := rfl

private theorem toU8_length (bs : List (BitVec 8)) : (toU8 bs).length = bs.length := by
  simp [toU8]

private theorem vecU8_length32 (v : List.Vector (BitVec 8) 32) : (vecU8 v).length = 32 := by
  simp [vecU8, toU8_length, v.toList_length]

def pkLitExpr {Γ : List (Ty S)} (pk : PublicKey) : Expr O Γ PK :=
  opPure ℓ Pt C Dh encPt encT lam .pkOfPbytes
    (opPure ℓ Pt C Dh encPt encT lam (.pbytesLit 32 (vecU8 pk.bytes)) .unit)

@[simp] theorem pkLitExpr_eval {Γ : List (Ty S)} (pk : PublicKey) (ρ : Env Γ) :
    (pkLitExpr ℓ Pt C Dh encPt encT lam pk).eval ρ = pk := by
  rcases pk with ⟨bytes⟩
  simp [pkLitExpr, AtomicPureOp.eval, u8Vec32_vecU8]

theorem pkLitExpr_cost {Γ : List (Ty S)} (pk : PublicKey) :
    (pkLitExpr ℓ Pt C Dh encPt encT lam (Γ := Γ) pk).cost = 98 := by
  simp [pkLitExpr, AtomicPureOp.cost, Expr.cost, vecU8_length32]

@[simp] theorem pkLitExpr_size {Γ : List (Ty S)} (pk : PublicKey) :
    (pkLitExpr ℓ Pt C Dh encPt encT lam (Γ := Γ) pk).size = 35 := by
  simp [pkLitExpr, AtomicPureOp.opSize, Expr.size, vecU8_length32]

def idKeyLitExpr {Γ : List (Ty S)} (ik : IdentityKey) : Expr O Γ IdKey :=
  opPure ℓ Pt C Dh encPt encT lam .idKeyOfPbytes
    (opPure ℓ Pt C Dh encPt encT lam (.pbytesLit 32 (vecU8 ik.publicKey.bytes)) .unit)

@[simp] theorem idKeyLitExpr_eval {Γ : List (Ty S)} (ik : IdentityKey) (ρ : Env Γ) :
    (idKeyLitExpr ℓ Pt C Dh encPt encT lam ik).eval ρ = ik := by
  rcases ik with ⟨⟨bytes⟩⟩
  simp [idKeyLitExpr, AtomicPureOp.eval, u8Vec32_vecU8]

theorem idKeyLitExpr_cost {Γ : List (Ty S)} (ik : IdentityKey) :
    (idKeyLitExpr ℓ Pt C Dh encPt encT lam (Γ := Γ) ik).cost = 98 := by
  simp [idKeyLitExpr, AtomicPureOp.cost, Expr.cost, vecU8_length32]

@[simp] theorem idKeyLitExpr_size {Γ : List (Ty S)} (ik : IdentityKey) :
    (idKeyLitExpr ℓ Pt C Dh encPt encT lam (Γ := Γ) ik).size = 35 := by
  simp [idKeyLitExpr, AtomicPureOp.opSize, Expr.size, vecU8_length32]

def optBytesEqExpr {Γ : List (Ty S)} (x y : Expr O Γ (.opt (B 32))) : Expr O Γ .bool :=
  .caseOpt x
    (.caseOpt y (.bool true) (.bool false))
    (.caseOpt (Expr.renameM (Δ := B 32 :: Γ) (fun ⦃_⦄ v => Var.succ v) y) (.bool false)
      (opPure ℓ Pt C Dh encPt encT lam (.bytesEq 32 32) (.pair (.var (.succ .zero)) (.var .zero))))

theorem optBytesEqExpr_eval {Γ : List (Ty S)} (x y : Expr O Γ (.opt (B 32))) (ρ : Env Γ) :
    (optBytesEqExpr ℓ Pt C Dh encPt encT lam x y).eval ρ = (x.eval ρ == y.eval ρ) := by
  have hr : ∀ (z : (B (ℓ := ℓ) (Pt := Pt) 32).denote),
      (Expr.renameM (Δ := B 32 :: Γ) (fun ⦃_⦄ v => Var.succ v) y).eval (.cons z ρ) = y.eval ρ :=
    fun z => Expr.renameM_eval (Δ := B 32 :: Γ) y (ρ₁ := ρ) (ρ₂ := .cons z ρ) (fun _ _ => rfl)
  dsimp only [optBytesEqExpr, Expr.eval]
  cases hx : x.eval ρ with
  | none => cases hy : y.eval ρ <;> simp
  | some a =>
    cases hy : y.eval ρ with
    | none => simp [hr, hy]
    | some b =>
      simp only [hr, hy, opPure_eval, AtomicPureOp.eval, Expr.eval, env_get_zero, env_get_succ]
      rfl

theorem optBytesEqExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ (.opt (B 32))) :
    (optBytesEqExpr ℓ Pt C Dh encPt encT lam x y).cost ≤ x.cost + y.cost + 70 := by
  simp only [optBytesEqExpr, opPure_cost, AtomicPureOp.cost, Expr.cost, Expr.renameM_cost,
    PNat.val_ofNat]
  omega

theorem optBytesEqExpr_size {Γ : List (Ty S)} (x y : Expr O Γ (.opt (B 32))) :
    (optBytesEqExpr ℓ Pt C Dh encPt encT lam x y).size ≤ x.size + 2 * y.size + 12 := by
  simp only [optBytesEqExpr, opPure_size, AtomicPureOp.opSize, Expr.size, Expr.renameM_size]
  omega

def optPtEqExpr {Γ : List (Ty S)} (x y : Expr O Γ (.opt PtT)) : Expr O Γ .bool :=
  .caseOpt x
    (.caseOpt y (.bool true) (.bool false))
    (.caseOpt (Expr.renameM (Δ := PtT :: Γ) (fun ⦃_⦄ v => Var.succ v) y) (.bool false)
      (opGrp ℓ Pt C Dh encPt encT lam .ptEq (.pair (.var (.succ .zero)) (.var .zero))))

theorem optPtEqExpr_eval {Γ : List (Ty S)} (x y : Expr O Γ (.opt PtT)) (ρ : Env Γ) :
    (optPtEqExpr ℓ Pt C Dh encPt encT lam x y).eval ρ = (x.eval ρ == y.eval ρ) := by
  have hr : ∀ (z : (PtT (ℓ := ℓ) (Pt := Pt)).denote),
      (Expr.renameM (Δ := PtT :: Γ) (fun ⦃_⦄ v => Var.succ v) y).eval (.cons z ρ) = y.eval ρ :=
    fun z => Expr.renameM_eval (Δ := PtT :: Γ) y (ρ₁ := ρ) (ρ₂ := .cons z ρ) (fun _ _ => rfl)
  dsimp only [optPtEqExpr, Expr.eval]
  cases hx : x.eval ρ with
  | none => cases hy : y.eval ρ <;> simp
  | some a =>
    cases hy : y.eval ρ with
    | none => simp [hr, hy]
    | some b =>
      simp only [hr, hy, opGrp_eval, AtomicGroupOp.eval, Expr.eval, env_get_zero, env_get_succ]
      exact Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans beq_iff_eq.symm)

theorem optPtEqExpr_cost {Γ : List (Ty S)} (x y : Expr O Γ (.opt PtT)) :
    (optPtEqExpr ℓ Pt C Dh encPt encT lam x y).cost ≤ x.cost + y.cost + 8 := by
  simp only [optPtEqExpr, opGrp_cost, AtomicGroupOp.cost, Expr.cost, Expr.renameM_cost]
  omega

theorem optPtEqExpr_size {Γ : List (Ty S)} (x y : Expr O Γ (.opt PtT)) :
    (optPtEqExpr ℓ Pt C Dh encPt encT lam x y).size ≤ x.size + 2 * y.size + 12 := by
  simp only [optPtEqExpr, opGrp_size, Expr.size, Expr.renameM_size]
  omega

def lPubOfExpr {Γ : List (Ty S)} (cV : Expr O Γ wireSaltCtT) : Expr O Γ (.opt lpubT) :=
  .letE cV
    (.caseOpt
      (opPure ℓ Pt C Dh encPt encT lam .signalMsgParse
        (opPure ℓ Pt C Dh encPt encT lam .bytesAppend8
          (.pair (.fst (.fst (.var .zero)))
            (opPure ℓ Pt C Dh encPt encT lam (.bytesLit 8 (List.replicate 8 0#8)) .unit))))
      .none
      (.some
        (.pair (.snd (.snd (.snd (.fst (.var .zero)))))
          (.pair (.fst (.snd (.snd (.var .zero))))
            (.pair (.snd (.var (.succ .zero)))
              (.snd (.snd (.snd (.var .zero)))))))))

theorem lPubOfExpr_eval {Γ : List (Ty S)} (cV : Expr O Γ wireSaltCtT) (ρ : Env Γ) :
    (lPubOfExpr ℓ Pt C Dh encPt encT lam cV).eval ρ =
      (lPubOf protoSignalCodec (wireSaltCtOfV (cV.eval ρ))).map lpubV := by
  rcases hcv : cV.eval ρ with ⟨⟨ser, tag⟩, saltBv⟩
  have hparse := atomicPureOps_eval_signalMsgParse_lossless ℓ Pt (ser ++ List.replicate 8 0#8)
  dsimp only [atomicPureOps] at hparse
  have happ : (opPure ℓ Pt C Dh encPt encT lam .bytesAppend8
      (.pair (.fst (.fst (.var .zero)))
        (opPure ℓ Pt C Dh encPt encT lam (.bytesLit 8 (List.replicate 8 0#8)) .unit))).eval
      (.cons ((ser, tag), saltBv) ρ) = ser ++ List.replicate 8 0#8 := by
    simp [opPure_eval, AtomicPureOp.eval, Expr.eval]
  dsimp only [lPubOfExpr, Expr.eval]
  rw [hcv, opPure_eval, happ, hparse]
  dsimp only [wireSaltCtOfV, lPubOf, signalWireCodec, macLength]
  rcases htf : SignalMessage.tryFrom protoSignalCodec (ser ++ List.replicate 8 0#8) with _ | m
  · rfl
  · simp [SignalMessage.header, lpubV, salt32V_salt32OfV]

theorem lPubOfExpr_cost {Γ : List (Ty S)} (cV : Expr O Γ wireSaltCtT) :
    (lPubOfExpr ℓ Pt C Dh encPt encT lam cV).cost ≤ cV.cost + (ℓ / 32 + 65) := by
  simp only [lPubOfExpr, opPure_cost, AtomicPureOp.cost, Expr.cost, List.length_replicate,
    PNat.val_ofNat]
  omega

theorem lPubOfExpr_size {Γ : List (Ty S)} (cV : Expr O Γ wireSaltCtT) :
    (lPubOfExpr ℓ Pt C Dh encPt encT lam cV).size ≤ cV.size + 40 := by
  simp only [lPubOfExpr, opPure_size, AtomicPureOp.opSize, List.length_replicate, Expr.size]
  omega

def chainGenExpr {Γ : List (Ty S)} (ck : Expr O Γ BV256) : Expr O Γ (.prod BV256 BV256) :=
  .letE ck
    (.pair
      (opSym ℓ Pt C Dh encPt encT lam (.hmacSha256Op 1)
        (.pair (.var .zero)
          (opPure ℓ Pt C Dh encPt encT lam (.bytesLit 1 [chainKeySeed]) .unit)))
      (opSym ℓ Pt C Dh encPt encT lam (.hmacSha256Op 1)
        (.pair (.var .zero)
          (opPure ℓ Pt C Dh encPt encT lam (.bytesLit 1 [messageKeySeed]) .unit))))

@[simp] theorem chainGenExpr_eval {Γ : List (Ty S)} (ck : Expr O Γ BV256) (ρ : Env Γ) (p : ℕ) :
    (chainGenExpr ℓ Pt C Dh encPt encT lam ck).eval ρ =
      (lChainPRG C.F p).gen (ck.eval ρ) := by
  dsimp only [chainGenExpr, lChainPRG, hmacPRF, MACScheme.tag, chainHmac,
    Expr.eval, env_get_zero, opSym_eval, opPure_eval, AtomicSymOp.eval, AtomicPureOp.eval]

theorem chainGenExpr_cost {Γ : List (Ty S)} (ck : Expr O Γ BV256) :
    (chainGenExpr ℓ Pt C Dh encPt encT lam ck).cost ≤ ck.cost + 40 := by
  simp only [chainGenExpr, opSym_cost, opPure_cost, AtomicSymOp.cost, AtomicPureOp.cost, Expr.cost,
    List.length_singleton, PNat.val_ofNat]
  omega

theorem chainGenExpr_size {Γ : List (Ty S)} (ck : Expr O Γ BV256) :
    (chainGenExpr ℓ Pt C Dh encPt encT lam ck).size ≤ ck.size + 20 := by
  simp only [chainGenExpr, opSym_size, opPure_size, AtomicPureOp.opSize, List.length_singleton,
    Expr.size]
  omega

def aeadEncExpr :
    Expr O [.prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) PlainT), .prod IdKey IdKey]
      wireSaltCtT :=
  let argT : Ty S := .prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) PlainT)
  let mksT : Ty S := .prod BV256 (.prod BV256 (.prod BV128 U32))
  let Γ₀ : List (Ty S) := [argT, .prod IdKey IdKey]
  let Γ₁ : List (Ty S) := mksT :: Γ₀
  let Γ₂ : List (Ty S) := B 32 :: Γ₁
  let vArg : Expr O Γ₀ argT := .var .zero
  let seed := Expr.fst vArg
  let ad := Expr.fst (Expr.snd vArg)
  let saltBv := Expr.fst (Expr.snd (Expr.snd (Expr.snd ad)))
  let mks := opSym ℓ Pt C Dh encPt encT lam .deriveMsgKeys
    (.pair seed (.pair (opPure ℓ Pt C Dh encPt encT lam (.u32Lit 0#32) .unit) (.some saltBv)))
  .letE mks
    (let vMks : Expr O Γ₁ mksT := .var .zero
     let vArg1 : Expr O Γ₁ argT := .var (.succ .zero)
     let vAux1 : Expr O Γ₁ (.prod IdKey IdKey) := .var (.succ (.succ .zero))
     let ad1 := Expr.fst (Expr.snd vArg1)
     let i1 := Expr.fst (Expr.fst ad1)
     let hdr1 := Expr.snd (Expr.fst ad1)
     let pub1 := Expr.snd ad1
     let ct := opSym ℓ Pt C Dh encPt encT lam .aes256CbcEnc
       (.pair (Expr.fst vMks) (.pair (Expr.fst (Expr.snd (Expr.snd vMks))) (Expr.snd (Expr.snd vArg1))))
     let srk := .caseOpt (Expr.snd hdr1) (pkLitExpr ℓ Pt C Dh encPt encT lam dummyKey)
       (opPtEncPk ℓ Pt C Dh encPt encT lam (.var .zero))
     let ids := .ite (.eqN (.modK 2 (Expr.fst hdr1)) (.nat 1))
       vAux1 (.pair (Expr.snd vAux1) (Expr.fst vAux1))
     let sHdr := .pair (opPure ℓ Pt C Dh encPt encT lam (.u8Lit currentVersion) .unit)
       (.pair srk
         (.pair (opPure ℓ Pt C Dh encPt encT lam .u32OfNat (.sub i1 (.nat 1))) (Expr.fst pub1)))
     let raw := opSym ℓ Pt C Dh encPt encT lam .signalMsgEncode
       (.pair sHdr
         (.pair ct
           (.pair (Expr.fst (Expr.snd pub1))
             (.pair (Expr.snd (Expr.snd (Expr.snd pub1)))
               (.pair (Expr.fst ids) (.pair (Expr.snd ids) (Expr.fst (Expr.snd vMks))))))))
     .letE raw
       (let vRaw : Expr O Γ₂ (B 32) := .var .zero
        let vArg2 : Expr O Γ₂ argT := .var (.succ (.succ .zero))
        let n := .sub (opPure ℓ Pt C Dh encPt encT lam (.bytesLen 32) vRaw) (.nat 8)
        let ser := opPure ℓ Pt C Dh encPt encT lam (.bytesTake 32) (.pair n vRaw)
        let tag := opPure ℓ Pt C Dh encPt encT lam .bytesToU64Le
          (opPure ℓ Pt C Dh encPt encT lam (.bytesTakeK 32 8)
            (opPure ℓ Pt C Dh encPt encT lam (.bytesDrop 32) (.pair n vRaw)))
        .pair (.pair ser tag) (Expr.fst (Expr.snd (Expr.snd (Expr.snd (Expr.fst (Expr.snd vArg2))))))))

theorem aeadEncExpr_eval (idOf : Party → IdentityKey) (seed : BitVec 256)
    (i : ℕ) (h : CryptoGames.SM.Construction.Header Pt)
    (pubV : (lpubT (ℓ := ℓ) (Pt := Pt)).denote)
    (m : Plain ℓ) :
    (aeadEncExpr ℓ Pt C Dh encPt encT lam).eval
      (.cons (seed, (((i, h), pubV), m)) (.cons (idOf .A, idOf .B) .nil)) =
    wireSaltCtV ((aeadAtomic C ℓ encT idOf).enc seed ((i, h), lpubOfV pubV) m) := by
  rcases h with ⟨t, T?⟩
  rcases pubV with ⟨pn, pq, saltBv, addrs⟩
  have hsalt_rt : salt32V (salt32OfV saltBv) = saltBv := salt32V_salt32OfV saltBv
  dsimp only [salt32OfV] at hsalt_rt
  dsimp only [aeadEncExpr, aeadAtomic, aeadAtomicEnc, lpubOfV, wireSaltCtV, salt32OfV,
    Expr.eval, env_get_zero, env_get_succ, opSym_eval, opPure_eval, opPtEncPk_eval,
    AtomicSymOp.eval, AtomicPureOp.eval, Option.map]
  cases T? <;> by_cases ht : t % 2 = 1 <;>
    simp [ht, hsalt_rt]

theorem aeadEncExpr_cost :
    (aeadEncExpr ℓ Pt C Dh encPt encT lam).cost ≤ 12 * (ℓ / 32) + 800 := by
  have hpk := pkLitExpr_cost ℓ Pt C Dh encPt encT lam
    (Γ := [.prod BV256 (.prod BV256 (.prod BV128 U32)),
           .prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) PlainT),
           .prod IdKey IdKey]) dummyKey
  simp only [aeadEncExpr, opSym_cost, opPure_cost, opPtEncPk_cost,
    AtomicSymOp.cost, AtomicPureOp.cost, Expr.cost, PNat.val_ofNat, hpk]
  have hdiv16 : ℓ / 16 ≤ 2 * (ℓ / 32) + 1 := by omega
  have hb1 : bits 1 ≤ 2 := by decide
  have hb2 : bits 2 ≤ 2 := by decide
  have hb8 : bits 8 ≤ 4 := by decide
  have hb32 : bits 32 ≤ 6 := by decide
  omega

theorem aeadEncExpr_size :
    (aeadEncExpr ℓ Pt C Dh encPt encT lam).size ≤ 200 := by
  simp only [aeadEncExpr, opSym_size, opPure_size, AtomicPureOp.opSize, opPtEncPk_size,
    pkLitExpr_size, Expr.size]
  have hb1 : bits 1 ≤ 2 := by decide
  have hb2 : bits 2 ≤ 2 := by decide
  have hb8 : bits 8 ≤ 4 := by decide
  omega

private theorem verifyMacWithAddresses_append_tag (F : ShaCompress)
    (m : SignalMessage) (ser : List (BitVec 8)) (tag : BitVec 64)
    (idOf : Party → IdentityKey) (t : ℕ) (macKey : BitVec 256) :
    let ids := if t % 2 = 1 then (idOf .A, idOf .B) else (idOf .B, idOf .A)
    ({ m with serialized := ser ++ toLEBytes 8 tag }).verifyMacWithAddresses
      F m.addresses ids.1 ids.2 macKey =
    ((hmacScheme F).tag macKey ((lIds idOf t).toList ++ ser) == tag) := by
  intro ids
  dsimp only [SignalMessage.verifyMacWithAddresses, SignalMessage.verifyMac]
  have hlen : (toLEBytes 8 tag).length = macLength := toLEBytes8_length tag
  have htake : (ser ++ toLEBytes 8 tag).take ((ser ++ toLEBytes 8 tag).length - macLength) = ser := by
    rw [List.length_append, hlen, Nat.add_sub_cancel,
      List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hdrop : (ser ++ toLEBytes 8 tag).drop ((ser ++ toLEBytes 8 tag).length - macLength) =
      toLEBytes 8 tag := by
    rw [List.length_append, hlen, Nat.add_sub_cancel,
      List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]
  rw [htake, hdrop, addressCheckPasses_self, Bool.and_true]
  have hids : macIds ids.1 ids.2 = lIds idOf t := macIds_ite_mod2 idOf t
  have hcmlen : (computeMac F ids.1 ids.2 macKey ser).length = 8 :=
    computeMac_length F ids.1 ids.2 macKey ser
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have hw := congrArg (bytesToWordLE 64) h
    rw [bytesToWordLE64_toLEBytes8] at hw
    dsimp only [computeMac, hmacScheme] at hw ⊢
    rw [← bytesToWordLE64_eq_bytesToWord64LE, ← hids]
    exact hw
  · intro h
    dsimp only [hmacScheme] at h
    rw [← bytesToWordLE64_eq_bytesToWord64LE, ← hids] at h
    have hw := congrArg (toLEBytes 8) h
    change toLEBytes 8 (bytesToWordLE 64 (computeMac F ids.1 ids.2 macKey ser)) =
      toLEBytes 8 tag at hw
    rwa [toLEBytes8_bytesToWordLE64 _ hcmlen] at hw

def aeadDecExpr :
    Expr O [.prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) wireSaltCtT), .prod IdKey IdKey]
      (.opt PlainT) :=
  let argT : Ty S := .prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) wireSaltCtT)
  let parsedT : Ty S := signalParsedT
  let mksT : Ty S := .prod BV256 (.prod BV256 (.prod BV128 U32))
  let Γ₀ : List (Ty S) := [argT, .prod IdKey IdKey]
  let Γ₁ : List (Ty S) := parsedT :: Γ₀
  let Γ₂ : List (Ty S) := mksT :: Γ₁
  let vArg : Expr O Γ₀ argT := .var .zero
  let aSalt := Expr.fst (Expr.snd (Expr.snd (Expr.snd (Expr.fst (Expr.snd vArg)))))
  let cSalt := Expr.snd (Expr.snd (Expr.snd vArg))
  .ite (opPure ℓ Pt C Dh encPt encT lam .bv256Eq (.pair cSalt aSalt))
    (.caseOpt
      (opPure ℓ Pt C Dh encPt encT lam .signalMsgParse
        (opPure ℓ Pt C Dh encPt encT lam .bytesAppend8
          (.pair (Expr.fst (Expr.fst (Expr.snd (Expr.snd vArg))))
            (opPure ℓ Pt C Dh encPt encT lam (.bytesLit 8 (List.replicate 8 0#8)) .unit))))
      .none
      (let vArg1 : Expr O Γ₁ argT := .var (.succ .zero)
       let seed1 := Expr.fst vArg1
       let aSalt1 := Expr.fst (Expr.snd (Expr.snd (Expr.snd (Expr.fst (Expr.snd vArg1)))))
       let mks : Expr O Γ₁ mksT := opSym ℓ Pt C Dh encPt encT lam .deriveMsgKeys
         (.pair seed1 (.pair (opPure ℓ Pt C Dh encPt encT lam (.u32Lit 0#32) .unit) (.some aSalt1)))
       .letE mks
         (let vMks : Expr O Γ₂ mksT := .var .zero
          let vP : Expr O Γ₂ parsedT := .var (.succ .zero)
          let vArg2 : Expr O Γ₂ argT := .var (.succ (.succ .zero))
          let vAux2 : Expr O Γ₂ (.prod IdKey IdKey) := .var (.succ (.succ (.succ .zero)))
          let ad2 := Expr.fst (Expr.snd vArg2)
          let i2 := Expr.fst (Expr.fst ad2)
          let hdr2 := Expr.snd (Expr.fst ad2)
          let pub2 := Expr.snd ad2
          let w2 := Expr.fst (Expr.snd (Expr.snd vArg2))
          let ids := .ite (.eqN (.modK 2 (Expr.fst hdr2)) (.nat 1))
            vAux2 (.pair (Expr.snd vAux2) (Expr.fst vAux2))
          let fullWire := opPure ℓ Pt C Dh encPt encT lam .bytesAppend8
            (.pair (Expr.fst w2) (opPure ℓ Pt C Dh encPt encT lam .u64LeBytes (Expr.snd w2)))
          let macOk := opSym ℓ Pt C Dh encPt encT lam .signalMsgVerifyMac
            (.pair fullWire
              (.pair (Expr.snd (Expr.snd (Expr.snd vP)))
                (.pair (Expr.fst ids) (.pair (Expr.snd ids) (Expr.fst (Expr.snd vMks))))))
          let srk : Expr O Γ₂ PK := Expr.caseOpt (Expr.snd hdr2)
            (pkLitExpr ℓ Pt C Dh encPt encT lam dummyKey)
            (opPtEncPk ℓ Pt C Dh encPt encT lam (.var .zero))
          let hdrOk :=
            .and (opPure ℓ Pt C Dh encPt encT lam .u8Eq
                (.pair (Expr.fst (Expr.fst vP))
                  (opPure ℓ Pt C Dh encPt encT lam (.u8Lit currentVersion) .unit)))
              (.and (opPure ℓ Pt C Dh encPt encT lam .pkEq (.pair (Expr.fst (Expr.snd (Expr.fst vP))) srk))
                (.and (opPure ℓ Pt C Dh encPt encT lam .u32Eq
                    (.pair (Expr.fst (Expr.snd (Expr.snd (Expr.fst vP))))
                      (opPure ℓ Pt C Dh encPt encT lam .u32OfNat (.sub i2 (.nat 1)))))
                  (.and (opPure ℓ Pt C Dh encPt encT lam .u32Eq
                      (.pair (Expr.snd (Expr.snd (Expr.snd (Expr.fst vP)))) (Expr.fst pub2)))
                    (.and (opPure ℓ Pt C Dh encPt encT lam (.bytesEq 32 32)
                        (.pair (Expr.fst (Expr.snd (Expr.snd vP))) (Expr.fst (Expr.snd pub2))))
                      (optBytesEqExpr ℓ Pt C Dh encPt encT lam
                        (Expr.snd (Expr.snd (Expr.snd vP))) (Expr.snd (Expr.snd (Expr.snd pub2))))))))
          .ite (.and macOk hdrOk)
            (opSym ℓ Pt C Dh encPt encT lam .aes256CbcDec
              (.pair (Expr.fst vMks) (.pair (Expr.fst (Expr.snd (Expr.snd vMks))) (Expr.fst (Expr.snd vP)))))
            .none)))
    .none

private theorem eval_caseOpt {Γ : List (Ty S)} {a b : Ty S}
    (e : Expr O Γ (.opt a)) (n : Expr O Γ b) (s : Expr O (a :: Γ) b) (ρ : Env Γ) :
    (Expr.caseOpt e n s).eval ρ =
      match e.eval ρ with
      | none => n.eval ρ
      | some x => s.eval (.cons x ρ) := by
  simp only [Expr.eval]
  cases e.eval ρ <;> rfl

private theorem eval_ite {Γ : List (Ty S)} {a : Ty S}
    (c : Expr O Γ .bool) (t e : Expr O Γ a) (ρ : Env Γ) :
    (Expr.ite c t e).eval ρ = if c.eval ρ then t.eval ρ else e.eval ρ := rfl

private theorem eval_letE {Γ : List (Ty S)} {a b : Ty S}
    (e : Expr O Γ a) (body : Expr O (a :: Γ) b) (ρ : Env Γ) :
    (Expr.letE e body).eval ρ = body.eval (.cons (e.eval ρ) ρ) := rfl

private theorem eval_pair {Γ : List (Ty S)} {a b : Ty S}
    (x : Expr O Γ a) (y : Expr O Γ b) (ρ : Env Γ) :
    (Expr.pair x y).eval ρ = (x.eval ρ, y.eval ρ) := rfl

private theorem eval_fst {Γ : List (Ty S)} {a b : Ty S}
    (x : Expr O Γ (.prod a b)) (ρ : Env Γ) :
    (Expr.fst x).eval ρ = (x.eval ρ).1 := rfl

private theorem eval_snd {Γ : List (Ty S)} {a b : Ty S}
    (x : Expr O Γ (.prod a b)) (ρ : Env Γ) :
    (Expr.snd x).eval ρ = (x.eval ρ).2 := rfl

theorem aeadDecExpr_eval (idOf : Party → IdentityKey) (seed : BitVec 256)
    (i : ℕ) (h : CryptoGames.SM.Construction.Header Pt)
    (pubV : (lpubT (ℓ := ℓ) (Pt := Pt)).denote)
    (cV : (wireSaltCtT (ℓ := ℓ) (Pt := Pt)).denote) :
    (aeadDecExpr ℓ Pt C Dh encPt encT lam).eval
      (.cons (seed, (((i, h), pubV), cV)) (.cons (idOf .A, idOf .B) .nil)) =
    (lAead C protoSignalCodec ℓ encT idOf).dec seed ((i, h), lpubOfV pubV) (wireSaltCtOfV cV) := by
  rcases h with ⟨t, T?⟩
  rcases pubV with ⟨pn, pq, aSaltBv, addrs⟩
  rcases cV with ⟨⟨ser, tag⟩, cSaltBv⟩
  by_cases hsalt : cSaltBv = aSaltBv
  · subst hsalt
    let argT : Ty S := .prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) wireSaltCtT)
    let ρ₀ : Env [argT, .prod IdKey IdKey] :=
      .cons (seed, (((i, (t, T?)), (pn, (pq, (cSaltBv, addrs)))), ((ser, tag), cSaltBv)))
        (.cons (idOf .A, idOf .B) .nil)
    have hsalt_eq : ¬ (salt32OfV cSaltBv ≠ salt32OfV cSaltBv) := not_not.mpr rfl
    have hbv_eq : (opPure ℓ Pt C Dh encPt encT lam .bv256Eq
        (.pair (.snd (.snd (.snd (.var .zero))))
          (.fst (.snd (.snd (.snd (.fst (.snd (.var .zero))))))))).eval ρ₀ = true := by
      dsimp only [ρ₀, Expr.eval, env_get_zero, opPure_eval, AtomicPureOp.eval]
      exact beq_self_eq_true cSaltBv
    have happ_lit : (opPure ℓ Pt C Dh encPt encT lam .bytesAppend8
        (.pair (.fst (.fst (.snd (.snd (.var .zero)))))
          (opPure ℓ Pt C Dh encPt encT lam (.bytesLit 8 (List.replicate 8 0#8)) .unit))).eval ρ₀ =
        ser ++ List.replicate 8 0#8 := rfl
    have hparse := atomicPureOps_eval_signalMsgParse_lossless ℓ Pt (ser ++ List.replicate 8 0#8)
    dsimp only [atomicPureOps] at hparse
    change (aeadDecExpr ℓ Pt C Dh encPt encT lam).eval ρ₀ = _
    dsimp only [aeadDecExpr]
    rw [eval_ite, hbv_eq]
    simp only [↓reduceIte]
    rw [eval_caseOpt, opPure_eval, happ_lit, hparse]
    rcases htf : SignalMessage.tryFrom protoSignalCodec (ser ++ List.replicate 8 0#8) with err | m
    · have htf0 : SignalMessage.tryFrom protoSignalCodec (ser ++ List.replicate 8 0) =
          .error err := htf
      dsimp only [lAead, lAeadK, lWire, libsignalWireAead, libsignalReceiveWire,
        signalWireCodec, lpubOfV, wireSaltCtOfV, macLength, Expr.eval]
      simp only [hsalt_eq, ↓reduceIte, htf0, ite_self]
    · have htf0 : SignalMessage.tryFrom protoSignalCodec (ser ++ List.replicate 8 0) =
          .ok m := htf
      let parsedT : Ty S := signalParsedT
      let mksT : Ty S := .prod BV256 (.prod BV256 (.prod BV128 U32))
      let pVal : parsedT.denote :=
        ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
          (m.ciphertext, (m.pqRatchet, m.addresses)))
      let mks0 :=
        MessageKeyGenerator.generateKeys C.F ⟨keyToBytes32 seed, 0#32⟩ (some (salt32OfV cSaltBv))
      let mksVal : mksT.denote :=
        (mks0.cipherKey, (mks0.macKey, (mks0.iv, mks0.counter)))
      let ρ₂ : Env [mksT, parsedT, argT, .prod IdKey IdKey] := .cons mksVal (.cons pVal ρ₀)
      change (Expr.letE _ _).eval (.cons pVal ρ₀) = _
      have hmks_eval : (opSym ℓ Pt C Dh encPt encT lam .deriveMsgKeys
          (.pair (.fst (.var (.succ .zero)))
            (.pair (opPure ℓ Pt C Dh encPt encT lam (.u32Lit 0#32) .unit)
              (.some (.fst (.snd (.snd (.snd (.fst (.snd (.var (.succ .zero)))))))))))).eval
          (.cons pVal ρ₀) = mksVal := rfl
      rw [eval_letE, hmks_eval]
      change (Expr.ite _ _ _).eval ρ₂ = _
      have hids_eval :
          ((Expr.ite (.eqN (.modK 2 (.fst (.snd (.fst (.fst (.snd (.var (.succ (.succ .zero)))))))))
              (.nat 1))
            (.var (.succ (.succ (.succ .zero))))
            (.pair (.snd (.var (.succ (.succ (.succ .zero)))))
              (.fst (.var (.succ (.succ (.succ .zero))))))) : Expr O _ _).eval ρ₂ =
          (if t % 2 = 1 then (idOf .A, idOf .B) else (idOf .B, idOf .A)) := by
        by_cases ht : t % 2 = 1 <;> simp [ρ₂, ρ₀, Expr.eval, ht]
      have happTag : AtomicPureOp.bytesAppend8.eval ℓ Pt
          (ser, AtomicPureOp.u64LeBytes.eval ℓ Pt tag) = ser ++ toLEBytes 8 tag := by
        simp [AtomicPureOp.eval, List.take_of_length_le (Nat.le_of_eq (toLEBytes8_length tag))]
      have htfTag := tryFrom_append_sfx8 protoSignalCodec ser (toLEBytes 8 tag)
        (List.replicate 8 0#8) (toLEBytes8_length tag) (by simp [macLength])
      rw [htf] at htfTag; dsimp only [Except.map] at htfTag
      have hmacEq := verifyMacWithAddresses_append_tag C.F m ser tag idOf t
        (deriveMessageKeys C.F (some (salt32OfV cSaltBv)) (keyToBytes32 seed)).2
      have hoptB :
          (optBytesEqExpr ℓ Pt C Dh encPt encT lam
            (.snd (.snd (.snd (.var (.succ .zero)))))
            (.snd (.snd (.snd (.snd (.fst (.snd (.var (.succ (.succ .zero)))))))))).eval ρ₂ =
          (m.addresses == addrs) := by
        rw [optBytesEqExpr_eval]
        rfl
      have hsrk :
          (Expr.caseOpt (.snd (.snd (.fst (.fst (.snd (.var (.succ (.succ .zero))))))))
            (pkLitExpr ℓ Pt C Dh encPt encT lam dummyKey)
            (opPtEncPk ℓ Pt C Dh encPt encT lam (.var .zero))).eval ρ₂ =
          (T?.map encT).getD dummyKey := by
        cases T? <;> simp [ρ₂, ρ₀, Expr.eval]
      rw [eval_ite]
      have hand_eval : ∀ (a b : Expr O [mksT, parsedT, argT, .prod IdKey IdKey] .bool),
          (Expr.and a b).eval ρ₂ = (a.eval ρ₂ && b.eval ρ₂) := fun _ _ => rfl
      rw [hand_eval]
      have hmacOk_eval :
          (opSym ℓ Pt C Dh encPt encT lam .signalMsgVerifyMac
            (.pair (opPure ℓ Pt C Dh encPt encT lam .bytesAppend8
                (.pair (.fst (.fst (.snd (.snd (.var (.succ (.succ .zero)))))))
                  (opPure ℓ Pt C Dh encPt encT lam .u64LeBytes
                    (.snd (.fst (.snd (.snd (.var (.succ (.succ .zero))))))))))
              (.pair (.snd (.snd (.snd (.var (.succ .zero)))))
                (.pair (.fst (Expr.ite (.eqN (.modK 2 (.fst (.snd (.fst (.fst (.snd (.var (.succ (.succ .zero))))))))) (.nat 1))
                    (.var (.succ (.succ (.succ .zero))))
                    (.pair (.snd (.var (.succ (.succ (.succ .zero))))) (.fst (.var (.succ (.succ (.succ .zero))))))))
                  (.pair (.snd (Expr.ite (.eqN (.modK 2 (.fst (.snd (.fst (.fst (.snd (.var (.succ (.succ .zero))))))))) (.nat 1))
                      (.var (.succ (.succ (.succ .zero))))
                      (.pair (.snd (.var (.succ (.succ (.succ .zero))))) (.fst (.var (.succ (.succ (.succ .zero))))))))
                    (.fst (.snd (.var .zero)))))))).eval ρ₂ =
          ((hmacScheme C.F).tag
            (deriveMessageKeys C.F (some (salt32OfV cSaltBv)) (keyToBytes32 seed)).2
            ((lIds idOf t).toList ++ ser) == tag) := by
        rw [opSym_eval]
        simp only [eval_pair, eval_fst, eval_snd, hids_eval, opPure_eval]
        dsimp only [ρ₂, mksVal, mks0, pVal, ρ₀, Expr.eval, env_get_zero, env_get_succ,
          MessageKeyGenerator.generateKeys]
        rw [happTag]; dsimp only [AtomicSymOp.eval]; rw [htfTag]; exact hmacEq
      rw [hmacOk_eval]
      have hhdrOk_eval :
          (Expr.and (opPure ℓ Pt C Dh encPt encT lam .u8Eq
              (.pair (.fst (.fst (.var (.succ .zero))))
                (opPure ℓ Pt C Dh encPt encT lam (.u8Lit currentVersion) .unit)))
            (.and (opPure ℓ Pt C Dh encPt encT lam .pkEq
                (.pair (.fst (.snd (.fst (.var (.succ .zero)))))
                  (Expr.caseOpt (.snd (.snd (.fst (.fst (.snd (.var (.succ (.succ .zero))))))))
                    (pkLitExpr ℓ Pt C Dh encPt encT lam dummyKey)
                    (opPtEncPk ℓ Pt C Dh encPt encT lam (.var .zero)))))
              (.and (opPure ℓ Pt C Dh encPt encT lam .u32Eq
                  (.pair (.fst (.snd (.snd (.fst (.var (.succ .zero))))))
                    (opPure ℓ Pt C Dh encPt encT lam .u32OfNat
                      (.sub (.fst (.fst (.fst (.snd (.var (.succ (.succ .zero))))))) (.nat 1)))))
                (.and (opPure ℓ Pt C Dh encPt encT lam .u32Eq
                    (.pair (.snd (.snd (.snd (.fst (.var (.succ .zero))))))
                      (.fst (.snd (.fst (.snd (.var (.succ (.succ .zero)))))))))
                  (.and (opPure ℓ Pt C Dh encPt encT lam (.bytesEq 32 32)
                      (.pair (.fst (.snd (.snd (.var (.succ .zero)))))
                        (.fst (.snd (.snd (.fst (.snd (.var (.succ (.succ .zero))))))))))
                    (optBytesEqExpr ℓ Pt C Dh encPt encT lam
                      (.snd (.snd (.snd (.var (.succ .zero)))))
                      (.snd (.snd (.snd (.snd (.fst (.snd (.var (.succ (.succ .zero))))))))))))))).eval ρ₂ =
          decide (m.header = lHeader encT i (t, T?) ⟨pn, pq, salt32OfV cSaltBv, addrs⟩) := by
        simp only [hand_eval, opPure_eval, eval_pair, eval_fst, eval_snd, hsrk, hoptB]
        dsimp only [ρ₂, pVal, ρ₀, Expr.eval, env_get_zero, env_get_succ, AtomicPureOp.eval]
        rcases m with ⟨mv, mrk, mcnt, mprev, mct, mpq, maddrs, mser⟩
        dsimp only [SignalMessage.header, lHeader]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, SignalHeader.mk.injEq]
      rw [hhdrOk_eval]
      dsimp only [lAead, lAeadK, lWire, libsignalWireAead, libsignalReceiveWire,
        signalWireCodec, lpubOfV, wireSaltCtOfV, macLength]
      simp only [hsalt_eq, ↓reduceIte, htf0]
      cases hmacB : ((hmacScheme C.F).tag
          (deriveMessageKeys C.F (some (salt32OfV cSaltBv)) (keyToBytes32 seed)).2
          ((lIds idOf t).toList ++ ser) == tag)
      · simp [Expr.eval]
      · dsimp only [Bool.true_and, ↓reduceIte, addressCheckPasses,
          ρ₂, mksVal, mks0, pVal, ρ₀, Expr.eval, env_get_zero, env_get_succ,
          opSym_eval, AtomicSymOp.eval, MessageKeyGenerator.generateKeys, aesCbcDecrypt]
        cases hdec : cbcDecRaw C.D
            (deriveMessageKeys C.F (some (salt32OfV cSaltBv)) (keyToBytes32 seed)).1.1
            (deriveMessageKeys C.F (some (salt32OfV cSaltBv)) (keyToBytes32 seed)).1.2
            m.ciphertext <;>
          by_cases hh : m.header = lHeader encT i (t, T?) ⟨pn, pq, salt32OfV cSaltBv, addrs⟩ <;>
          simp [hh]
  · have hsalt_ne : salt32OfV cSaltBv ≠ salt32OfV aSaltBv := by
      intro heq; apply hsalt; have := congrArg salt32V heq; simpa [salt32V_salt32OfV] using this
    let ρ₀ : Env [.prod BV256 (.prod (.prod (.prod .nat (fig8HdrT (ℓ := ℓ) (Pt := Pt))) lpubT)
        wireSaltCtT), .prod IdKey IdKey] :=
      .cons (seed, (((i, (t, T?)), (pn, (pq, (aSaltBv, addrs)))), ((ser, tag), cSaltBv)))
        (.cons (idOf .A, idOf .B) .nil)
    change (aeadDecExpr ℓ Pt C Dh encPt encT lam).eval ρ₀ = _
    dsimp only [aeadDecExpr]
    rw [eval_ite]
    have hbv_cond :
        (opPure ℓ Pt C Dh encPt encT lam .bv256Eq
          (.pair (.snd (.snd (.snd (.var .zero))))
            (.fst (.snd (.snd (.snd (.fst (.snd (.var .zero))))))))).eval ρ₀ = false := by
      simp [Expr.eval, AtomicPureOp.eval, ρ₀, hsalt]
    rw [hbv_cond]
    simp [Expr.eval, lAead, lAeadK, wireSaltCtOfV, lpubOfV, hsalt_ne]

theorem aeadDecExpr_cost :
    (aeadDecExpr ℓ Pt C Dh encPt encT lam).cost ≤ 14 * (ℓ / 32) + 850 := by
  let parsedT : Ty S := signalParsedT
  have hpk := pkLitExpr_cost ℓ Pt C Dh encPt encT lam
    (Γ := [.prod BV256 (.prod BV256 (.prod BV128 U32)),
           parsedT,
           .prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) wireSaltCtT),
           .prod IdKey IdKey]) dummyKey
  have hopt := optBytesEqExpr_cost ℓ Pt C Dh encPt encT lam
    (Γ := [.prod BV256 (.prod BV256 (.prod BV128 U32)),
           parsedT,
           .prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) wireSaltCtT),
           .prod IdKey IdKey])
    (.snd (.snd (.snd (.var (.succ .zero)))))
    (.snd (.snd (.snd (.snd (.fst (.snd (.var (.succ (.succ .zero)))))))))
  simp only [Expr.cost] at hopt
  simp only [aeadDecExpr, opSym_cost, opPure_cost, opPtEncPk_cost,
    AtomicSymOp.cost, AtomicPureOp.cost, Expr.cost, List.length_replicate,
    PNat.val_ofNat, hpk]
  have hdiv16 : ℓ / 16 ≤ 2 * (ℓ / 32) + 1 := by omega
  have hb1 : bits 1 ≤ 2 := by decide
  have hb2 : bits 2 ≤ 2 := by decide
  omega

theorem aeadDecExpr_size :
    (aeadDecExpr ℓ Pt C Dh encPt encT lam).size ≤ 350 := by
  let parsedT : Ty S := signalParsedT
  have hopt := optBytesEqExpr_size ℓ Pt C Dh encPt encT lam
    (Γ := [.prod BV256 (.prod BV256 (.prod BV128 U32)),
           parsedT,
           .prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) wireSaltCtT),
           .prod IdKey IdKey])
    (.snd (.snd (.snd (.var (.succ .zero)))))
    (.snd (.snd (.snd (.snd (.fst (.snd (.var (.succ (.succ .zero)))))))))
  simp only [Expr.size] at hopt
  simp only [aeadDecExpr, opSym_size, opPure_size, AtomicPureOp.opSize, List.length_replicate,
    opPtEncPk_size, pkLitExpr_size, Expr.size]
  have hb1 : bits 1 ≤ 2 := by decide
  have hb2 : bits 2 ≤ 2 := by decide
  omega

def appAux {Γ : List (Ty S)} {a b : Ty S} (f : Expr O [a, .prod IdKey IdKey] b)
    (arg : Expr O Γ a) (vAux : Var Γ (.prod IdKey IdKey)) : Expr O Γ b :=
  .letE arg
    (Expr.renameM
      (fun ⦃_⦄ v => match v with
        | .zero => .zero
        | .succ .zero => .succ vAux)
      f)

theorem appAux_eval {Γ : List (Ty S)} {a b : Ty S} (f : Expr O [a, .prod IdKey IdKey] b)
    (arg : Expr O Γ a) (vAux : Var Γ (.prod IdKey IdKey)) (ρ : Env Γ) :
    (appAux ℓ Pt C Dh encPt encT lam f arg vAux).eval ρ =
      f.eval (.cons (arg.eval ρ) (.cons (ρ.get vAux) .nil)) := by
  dsimp only [appAux, Expr.eval]
  refine Expr.renameM_eval f ?_
  intro u v
  cases v with
  | zero => rfl
  | succ v =>
    cases v with
    | zero => rfl
    | succ v => nomatch v

@[simp] theorem appAux_cost {Γ : List (Ty S)} {a b : Ty S} (f : Expr O [a, .prod IdKey IdKey] b)
    (arg : Expr O Γ a) (vAux : Var Γ (.prod IdKey IdKey)) :
    (appAux ℓ Pt C Dh encPt encT lam f arg vAux).cost = arg.cost + f.cost + 1 := by
  simp [appAux, Expr.cost]

@[simp] theorem appAux_size {Γ : List (Ty S)} {a b : Ty S} (f : Expr O [a, .prod IdKey IdKey] b)
    (arg : Expr O Γ a) (vAux : Var Γ (.prod IdKey IdKey)) :
    (appAux ℓ Pt C Dh encPt encT lam f arg vAux).size = arg.size + f.size + 1 := by
  simp [appAux, Expr.size]

def unitsPowExpr : ℕ → {Γ : List (Ty S)} → Expr O Γ (.list .unit)
  | 0, _ => .cons .unit .nil
  | k + 1, _ => .letE (unitsPowExpr k) (.appendL (2 ^ (k + 1)) (.var .zero) (.var .zero))

theorem unitsPowExpr_eval : ∀ (k : ℕ) {Γ : List (Ty S)} (ρ : Env Γ),
    (unitsPowExpr ℓ Pt C Dh encPt encT lam (Γ := Γ) k).eval ρ = List.replicate (2 ^ k) ()
  | 0, _, _ => rfl
  | k + 1, _, ρ => by
    dsimp only [unitsPowExpr, Expr.eval]
    rw [unitsPowExpr_eval k ρ, env_get_zero]
    have hrep : List.replicate (2 ^ k) () ++ List.replicate (2 ^ k) () =
        List.replicate (2 ^ (k + 1)) () := by
      rw [← List.replicate_add, Nat.pow_succ, Nat.mul_two]
    rw [hrep, List.take_of_length_le (by simp)]

theorem unitsPowExpr_cost : ∀ (k : ℕ) {Γ : List (Ty S)},
    (unitsPowExpr ℓ Pt C Dh encPt encT lam (Γ := Γ) k).cost ≤ 6 * 2 ^ k
  | 0, _ => by simp [unitsPowExpr, Expr.cost]
  | k + 1, Γ => by
    have ih := unitsPowExpr_cost k (Γ := Γ)
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    simp only [unitsPowExpr, Expr.cost, Nat.pow_succ]
    omega

theorem unitsPowExpr_size : ∀ (k : ℕ) {Γ : List (Ty S)},
    (unitsPowExpr ℓ Pt C Dh encPt encT lam (Γ := Γ) k).size ≤ k * k + 6 * k + 3
  | 0, _ => by simp [unitsPowExpr, Expr.size]
  | k + 1, Γ => by
    have ih := unitsPowExpr_size k (Γ := Γ)
    have hlt : 2 ^ (k + 1) < 2 ^ (k + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
    have hb : bits (2 ^ (k + 1)) ≤ k + 2 := ReductionDsl.bits_le_of_lt hlt (by omega)
    simp only [unitsPowExpr, Expr.size]
    nlinarith

private theorem foldr_replicate_skipKeys {CK MK : Type} (G : ℕ → PRGScheme CK (CK × MK)) :
    ∀ (n : ℕ) (w : CK) (p : ℕ) (acc : List (ℕ × MK)),
      (List.replicate n ()).foldr
        (fun _ (st : CK × (ℕ × List (ℕ × MK))) =>
          let g := (G st.2.1).gen st.1
          (g.1, (st.2.1 + 1, (st.2.1 + 1, g.2) :: st.2.2)))
        (w, (p, acc)) =
      ((skipKeys G n w p acc).1, (p + n, (skipKeys G n w p acc).2))
  | 0, w, p, acc => by simp [skipKeys]
  | n + 1, w, p, acc => by
    rw [List.replicate_add n 1 (), List.foldr_append]
    dsimp only [List.replicate, List.foldr, skipKeys]
    rw [foldr_replicate_skipKeys G n]
    simp [Nat.add_assoc, Nat.add_comm 1 n]

private theorem find_map_snd_eq_lookup (i : ℕ) :
    ∀ (l : List (ℕ × BitVec 256)),
      (l.find? (fun x => decide (x.1 = i))).map Prod.snd = l.lookup i
  | [] => rfl
  | (k, v) :: tl => by
    by_cases h : k = i
    · subst k; simp [List.find?, List.lookup]
    · have hne : (i == k) = false := beq_false_of_ne (Ne.symm h)
      simp only [List.find?, List.lookup, h, decide_false, hne]
      exact find_map_snd_eq_lookup i tl

private theorem foldr_filter_neq (i : ℕ) :
    ∀ (l : List (ℕ × BitVec 256)),
      l.foldr (fun x acc => if decide (x.1 = i) then acc else x :: acc) [] =
        l.filter (·.1 != i)
  | [] => rfl
  | (k, v) :: tl => by
    by_cases h : k = i
    · subst k; simp only [List.foldr, List.filter, decide_true, ↓reduceIte, bne_self_eq_false]
      exact foldr_filter_neq i tl
    · have hne : (k != i) = true := bne_iff_ne.mpr h
      simp only [List.foldr, List.filter, h, decide_false, hne, Bool.false_eq_true, ↓reduceIte]
      exact congrArg ((k, v) :: ·) (foldr_filter_neq i tl)

private theorem two_mul_succ_le_two_pow : ∀ k : ℕ, 3 ≤ k → 2 * (k + 1) ≤ 2 ^ k
  | 0, h | 1, h | 2, h => by omega
  | 3, _ => by decide
  | k + 4, _ => by
    have ih := two_mul_succ_le_two_pow (k + 3) (by omega)
    have h1 : 2 ≤ 2 ^ (k + 3) := by
      have : 2 ^ 3 ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [Nat.pow_succ 2 (k + 3)]
    omega

private theorem two_mul_bits_le_add_two (n : ℕ) : 2 * bits n ≤ n + 2 := by
  by_cases hn8 : n < 8
  · interval_cases n <;> decide
  · unfold bits
    have hn0 : n ≠ 0 := by omega
    have hk3 : 3 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) hn0).mpr (by omega)
    have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
    have hmul := two_mul_succ_le_two_pow (Nat.log 2 n) hk3
    omega

private theorem bits_le_succ (n : ℕ) : bits n ≤ n + 1 := by
  have := two_mul_bits_le_add_two n
  omega

def fsInitSendExpr : Expr O [BV256, .prod IdKey IdKey] fsSendStT :=
  .pair (.var .zero) (.nat 0)

@[simp] theorem fsInitSendExpr_eval (idOf : Party → IdentityKey) (B : ℕ) (k : BitVec 256) :
    (fsInitSendExpr ℓ Pt C Dh encPt encT lam).eval (.cons k (.cons (idOf .A, idOf .B) .nil)) =
      fsSendStV ((fsAtomicB (Pt := Pt) C ℓ encT idOf B).initSender k) := rfl

theorem fsInitSendExpr_cost : (fsInitSendExpr ℓ Pt C Dh encPt encT lam).cost = 3 := rfl

theorem fsInitSendExpr_size : (fsInitSendExpr ℓ Pt C Dh encPt encT lam).size = 3 := rfl

def fsInitRecvExpr : Expr O [BV256, .prod IdKey IdKey] fsRecvStT :=
  .pair (.var .zero) (.pair (.nat 0) .nil)

@[simp] theorem fsInitRecvExpr_eval (idOf : Party → IdentityKey) (B : ℕ) (k : BitVec 256) :
    (fsInitRecvExpr ℓ Pt C Dh encPt encT lam).eval (.cons k (.cons (idOf .A, idOf .B) .nil)) =
      fsRecvStV ((fsAtomicB (Pt := Pt) C ℓ encT idOf B).initReceiver k) := rfl

theorem fsInitRecvExpr_cost : (fsInitRecvExpr ℓ Pt C Dh encPt encT lam).cost = 5 := rfl

theorem fsInitRecvExpr_size : (fsInitRecvExpr ℓ Pt C Dh encPt encT lam).size = 5 := rfl

def fsSendExpr :
    Expr O [.prod fsSendStT (.prod fig8HdrT (.prod lpubT PlainT)), .prod IdKey IdKey]
      (.prod fsSendStT lctT) :=
  .letE (chainGenExpr ℓ Pt C Dh encPt encT lam (.fst (.fst (.var .zero))))
    (let vArg1 := Expr.var (.succ .zero)
     let i1 := Expr.add (.snd (.fst vArg1)) (.nat 1)
     let encArg := Expr.pair (.snd (.var .zero))
       (.pair (.pair (.pair i1 (.fst (.snd vArg1))) (.fst (.snd (.snd vArg1))))
         (.snd (.snd (.snd vArg1))))
     let ct := appAux ℓ Pt C Dh encPt encT lam
       (aeadEncExpr ℓ Pt C Dh encPt encT lam) encArg (.succ (.succ .zero))
     .pair (.pair (.fst (.var .zero)) i1) (.pair i1 ct))

theorem fsSendExpr_eval (idOf : Party → IdentityKey) (B : ℕ)
    (ss : RatchetSenderState (BitVec 256)) (h : CryptoGames.SM.Construction.Header Pt)
    (p : LibsignalMsgPublicPart) (m : Plain ℓ) :
    (fsSendExpr ℓ Pt C Dh encPt encT lam).eval
      (.cons (fsSendStV ss, (h, (lpubV p, m))) (.cons (idOf .A, idOf .B) .nil)) =
    let res := (fsAtomicB C ℓ encT idOf B).send ss h (p, m)
    (fsSendStV res.1, lctV res.2) := by
  rcases ss with ⟨ck, lastIdx⟩
  dsimp only [fsSendExpr, fsAtomicB, fsAtomic, fromAEADPRG, AEADScheme.movePubPartToAD,
    fsSendStV, lctV, Expr.eval]
  rw [chainGenExpr_eval ℓ Pt C Dh encPt encT lam _ _ lastIdx]
  simp only [Expr.eval, env_get_zero, env_get_succ, appAux_eval]
  rw [aeadEncExpr_eval, lpubOfV_lpubV]

theorem fsSendExpr_cost :
    (fsSendExpr ℓ Pt C Dh encPt encT lam).cost ≤ 12 * (ℓ / 32) + 900 := by
  have hcg := chainGenExpr_cost ℓ Pt C Dh encPt encT lam
    (Γ := [.prod fsSendStT (.prod fig8HdrT (.prod lpubT PlainT)), .prod IdKey IdKey])
    (.fst (.fst (.var .zero)))
  have hae := aeadEncExpr_cost ℓ Pt C Dh encPt encT lam
  simp only [fsSendExpr, appAux_cost, Expr.cost] at hcg ⊢
  have hb1 : bits 1 ≤ 2 := by decide
  omega

theorem fsSendExpr_size :
    (fsSendExpr ℓ Pt C Dh encPt encT lam).size ≤ 300 := by
  have hcg := chainGenExpr_size ℓ Pt C Dh encPt encT lam
    (Γ := [.prod fsSendStT (.prod fig8HdrT (.prod lpubT PlainT)), .prod IdKey IdKey])
    (.fst (.fst (.var .zero)))
  have hae := aeadEncExpr_size ℓ Pt C Dh encPt encT lam
  simp only [fsSendExpr, appAux_size, Expr.size] at hcg ⊢
  have hb1 : bits 1 ≤ 2 := by decide
  omega

private theorem fromAEADPRG_movePubPartToAD_receive_none {CK MK AD Pub M C : Type}
    (ae : AEADScheme MK ((ℕ × AD) × Pub) M C) (pubOf : C → Option Pub)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
    (v : RatchetReceiverState CK MK) (a : AD) (idx : ℕ) (wsc : C)
    (hnone : pubOf wsc = none) :
    (fromAEADPRG (ae.movePubPartToAD pubOf) G maxSkip).receive v a (idx, wsc) = none := by
  dsimp only [fromAEADPRG, AEADScheme.movePubPartToAD]
  rcases v.skippedKeys.lookup idx with _ | key
  · split_ifs
    · rfl
    · simp [hnone]
  · simp [hnone]

def fsRecvExpr (B0 B : ℕ) :
    Expr O [.prod fsRecvStT (.prod fig8HdrT lctT), .prod IdKey IdKey]
      (.opt (.prod fsRecvStT (.prod .nat (.prod lpubT PlainT)))) :=
  let inT : Ty S := .prod fsRecvStT (.prod fig8HdrT lctT)
  let Γ₁ : List (Ty S) := [lpubT, inT, .prod IdKey IdKey]
  let vIn1 : Expr O Γ₁ inT := .var (.succ .zero)
  let rs1 := Expr.fst vIn1
  let ck1 := Expr.fst rs1
  let last1 := Expr.fst (Expr.snd rs1)
  let sk1 := Expr.snd (Expr.snd rs1)
  let idx1 := Expr.fst (Expr.snd (Expr.snd vIn1))
  let found : Expr O Γ₁ (.opt (.prod .nat BV256)) :=
    .findB B0 sk1 (.eqN (.fst (.var .zero)) (.fst (.snd (.snd (.var (.succ (.succ .zero)))))))
  let filtSk : Expr O (.prod .nat BV256 :: Γ₁) (.list (.prod .nat BV256)) :=
    .foldrB B0 (.snd (.snd (.fst (.var (.succ (.succ .zero)))))) .nil
      (.ite (.eqN (.fst (.var .zero))
          (.fst (.snd (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))))
        (.var (.succ .zero))
        (.cons (.var .zero) (.var (.succ .zero))))
  let someFound : Expr O (.prod .nat BV256 :: Γ₁) (.opt (.prod BV256 fsRecvStT)) :=
    .some (.pair (.snd (.var .zero))
      (.pair (.fst (.fst (.var (.succ (.succ .zero)))))
        (.pair (.fst (.snd (.fst (.var (.succ (.succ .zero)))))) filtSk)))
  let nSkip1 := Expr.sub (Expr.sub idx1 last1) (.nat 1)
  let cond1 := Expr.and (.lt last1 idx1) (.not (.lt (.nat maxForwardJumps) nSkip1))
  let skipStep : Expr O (.unit :: fsRecvStT :: Γ₁) fsRecvStT :=
    .letE (chainGenExpr ℓ Pt C Dh encPt encT lam (.fst (.var (.succ .zero))))
      (let st' := Expr.var (.succ (.succ .zero))
       let pNext := Expr.add (.fst (.snd st')) (.nat 1)
       .pair (.fst (.var .zero))
         (.pair pNext (.cons (.pair pNext (.snd (.var .zero))) (.snd (.snd st')))))
  let skipFold1 : Expr O Γ₁ fsRecvStT :=
    .foldrB maxForwardJumps
      (.take nSkip1 (unitsPowExpr ℓ Pt C Dh encPt encT lam 15))
      (.pair ck1 (.pair last1 (.take (.nat B0) sk1)))
      skipStep
  let noneFound : Expr O Γ₁ (.opt (.prod BV256 fsRecvStT)) :=
    .ite cond1
      (.letE skipFold1
        (.letE (chainGenExpr ℓ Pt C Dh encPt encT lam (.fst (.var .zero)))
          (.some (.pair (.snd (.var .zero))
            (.pair (.fst (.var .zero))
              (.pair (.fst (.snd (.snd (.var (.succ (.succ (.succ .zero)))))))
                (.snd (.snd (.var (.succ .zero))))))))))
      .none
  .caseOpt (lPubOfExpr ℓ Pt C Dh encPt encT lam (.snd (.snd (.snd (.var .zero)))))
    .none
    (.caseOpt (.caseOpt found noneFound someFound)
      .none
      (let vIn2 := Expr.var (.succ (.succ .zero))
       let decArg := Expr.pair (.fst (.var .zero))
         (.pair (.pair (.pair (.fst (.snd (.snd vIn2))) (.fst (.snd vIn2))) (.var (.succ .zero)))
           (.snd (.snd (.snd vIn2))))
       .caseOpt
         (appAux ℓ Pt C Dh encPt encT lam
           (aeadDecExpr ℓ Pt C Dh encPt encT lam) decArg (.succ (.succ (.succ .zero))))
         .none
         (let idx3 := Expr.fst (.snd (.snd (.var (.succ (.succ (.succ .zero))))))
          .some (.pair (.snd (.var (.succ .zero)))
            (.pair (.ite (.lt idx3 (.nat B)) idx3 (.nat B))
              (.pair (.var (.succ (.succ .zero))) (.var .zero)))))))

theorem fsRecvExpr_eval (idOf : Party → IdentityKey) (B0 B : ℕ)
    (rs : RatchetReceiverState (BitVec 256) (BitVec 256))
    (h : CryptoGames.SM.Construction.Header Pt)
    (c : ℕ × LibsignalCiphertextWithSalt32) :
    (fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B).eval
      (.cons (fsRecvStV rs, (h, lctV c)) (.cons (idOf .A, idOf .B) .nil)) =
    ((fsAtomicB C ℓ encT idOf B0).receive rs h c).map
      (fun (rs', idx, p, m) => (fsRecvStV rs', (min idx B, (lpubV p, m)))) := by
  rcases rs with ⟨ck, lastIdx, sk⟩
  rcases c with ⟨idx, wsc⟩
  let inT : Ty S := .prod fsRecvStT (.prod fig8HdrT lctT)
  let Γ₀ : List (Ty S) := [inT, .prod IdKey IdKey]
  let ρ₀ : Env Γ₀ := .cons ((ck, (lastIdx, sk)), (h, (idx, wireSaltCtV wsc)))
    (.cons (idOf .A, idOf .B) .nil)
  change (fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B).eval ρ₀ = _
  unfold fsRecvExpr
  rw [eval_caseOpt]
  rcases hpub : lPubOf protoSignalCodec wsc with _ | pub
  · have hlpub0 :
        (lPubOfExpr ℓ Pt C Dh encPt encT lam (.snd (.snd (.snd (.var .zero)))) :
          Expr O Γ₀ (.opt lpubT)).eval ρ₀ =
        (none : (@Ty.opt S lpubT).denote) := by
      rw [lPubOfExpr_eval]
      change Option.map lpubV (lPubOf protoSignalCodec (wireSaltCtOfV (wireSaltCtV wsc))) = none
      rw [wireSaltCtOfV_wireSaltCtV, hpub]
      rfl
    rw [hlpub0]
    simp only [fsAtomicB, fsAtomic]
    rw [fromAEADPRG_movePubPartToAD_receive_none _ _ _ _ _ _ _ _ hpub]
    rfl
  · have hlpub1 :
        (lPubOfExpr ℓ Pt C Dh encPt encT lam (.snd (.snd (.snd (.var .zero)))) :
          Expr O Γ₀ (.opt lpubT)).eval ρ₀ =
        (some (lpubV pub) : (@Ty.opt S lpubT).denote) := by
      rw [lPubOfExpr_eval]
      change Option.map lpubV (lPubOf protoSignalCodec (wireSaltCtOfV (wireSaltCtV wsc))) =
        some (lpubV pub)
      rw [wireSaltCtOfV_wireSaltCtV, hpub]
      rfl
    rw [hlpub1]
    let Γ₁ : List (Ty S) := [lpubT, inT, .prod IdKey IdKey]
    let ρ₁ : Env Γ₁ := .cons (lpubV pub) ρ₀
    have hdec : ∀ (mk : (BV256 (ℓ := ℓ) (Pt := Pt)).denote)
        (rs' : RatchetReceiverState (BitVec 256) (BitVec 256)),
        (let vIn2 : Expr O (.prod BV256 fsRecvStT :: Γ₁) inT := Expr.var (.succ (.succ .zero))
         let decArg := Expr.pair (.fst (.var .zero))
           (.pair (.pair (.pair (.fst (.snd (.snd vIn2))) (.fst (.snd vIn2))) (.var (.succ .zero)))
             (.snd (.snd (.snd vIn2))))
         Expr.caseOpt
           (appAux ℓ Pt C Dh encPt encT lam
             (aeadDecExpr ℓ Pt C Dh encPt encT lam) decArg (.succ (.succ (.succ .zero))))
           .none
           (let idx3 := Expr.fst (.snd (.snd (.var (.succ (.succ (.succ .zero))))))
            .some (.pair (.snd (.var (.succ .zero)))
              (.pair (.ite (.lt idx3 (.nat B)) idx3 (.nat B))
                (.pair (.var (.succ (.succ .zero))) (.var .zero)))))).eval
          (.cons (mk, fsRecvStV (ℓ := ℓ) (Pt := Pt) rs') ρ₁) =
        (match (lAead C protoSignalCodec ℓ encT idOf).dec mk ((idx, h), pub) wsc with
         | none => none
         | some m => some (fsRecvStV rs', (min idx B, (lpubV pub, m)))) := by
      intro mk rs'
      let ρ_dec : Env (.prod BV256 fsRecvStT :: Γ₁) :=
        .cons (mk, fsRecvStV (ℓ := ℓ) (Pt := Pt) rs') ρ₁
      change (Expr.caseOpt _ _ _).eval ρ_dec = _
      rw [eval_caseOpt, appAux_eval]
      have haead :
          (aeadDecExpr ℓ Pt C Dh encPt encT lam).eval
            (.cons ((let vIn2 : Expr O (.prod BV256 fsRecvStT :: Γ₁) inT :=
                  Expr.var (.succ (.succ .zero))
                Expr.pair (.fst (.var .zero))
                  (.pair (.pair (.pair (.fst (.snd (.snd vIn2))) (.fst (.snd vIn2)))
                      (.var (.succ .zero)))
                    (.snd (.snd (.snd vIn2))))).eval ρ_dec)
              (.cons (ρ_dec.get (.succ (.succ (.succ .zero)))) .nil)) =
          (lAead C protoSignalCodec ℓ encT idOf).dec mk ((idx, h), pub) wsc := by
        change (aeadDecExpr ℓ Pt C Dh encPt encT lam).eval
          (.cons (mk, (((idx, h), lpubV pub), wireSaltCtV wsc))
            (.cons (idOf .A, idOf .B) .nil)) = _
        rw [aeadDecExpr_eval, lpubOfV_lpubV, wireSaltCtOfV_wireSaltCtV]
      rcases hdec_res : (lAead C protoSignalCodec ℓ encT idOf).dec mk ((idx, h), pub) wsc with _ | m
      · have haead0 :
            (aeadDecExpr ℓ Pt C Dh encPt encT lam).eval
              (.cons ((let vIn2 : Expr O (.prod BV256 fsRecvStT :: Γ₁) inT :=
                    Expr.var (.succ (.succ .zero))
                  Expr.pair (.fst (.var .zero))
                    (.pair (.pair (.pair (.fst (.snd (.snd vIn2))) (.fst (.snd vIn2)))
                        (.var (.succ .zero)))
                      (.snd (.snd (.snd vIn2))))).eval ρ_dec)
                (.cons (ρ_dec.get (.succ (.succ (.succ .zero)))) .nil)) =
            (none : (@Ty.opt S PlainT).denote) := haead.trans hdec_res
        rw [haead0]
        rfl
      · have haead1 :
            (aeadDecExpr ℓ Pt C Dh encPt encT lam).eval
              (.cons ((let vIn2 : Expr O (.prod BV256 fsRecvStT :: Γ₁) inT :=
                    Expr.var (.succ (.succ .zero))
                  Expr.pair (.fst (.var .zero))
                    (.pair (.pair (.pair (.fst (.snd (.snd vIn2))) (.fst (.snd vIn2)))
                        (.var (.succ .zero)))
                      (.snd (.snd (.snd vIn2))))).eval ρ_dec)
                (.cons (ρ_dec.get (.succ (.succ (.succ .zero)))) .nil)) =
            (some m : (@Ty.opt S PlainT).denote) := haead.trans hdec_res
        rw [haead1]
        dsimp only
        have hleaf : (let idx3 : Expr O (PlainT :: .prod BV256 fsRecvStT :: Γ₁) .nat :=
              Expr.fst (.snd (.snd (.var (.succ (.succ (.succ .zero))))))
            Expr.some (.pair (.snd (.var (.succ .zero)))
              (.pair (.ite (.lt idx3 (.nat B)) idx3 (.nat B))
                (.pair (.var (.succ (.succ .zero))) (.var .zero)))) :
            Expr O (PlainT :: .prod BV256 fsRecvStT :: Γ₁)
              (.opt (.prod fsRecvStT (.prod .nat (.prod lpubT PlainT))))).eval
            (.cons m ρ_dec) =
          (some (fsRecvStV (ℓ := ℓ) (Pt := Pt) rs',
            (if decide (idx < B) = true then idx else B, (lpubV pub, m))) :
            (@Ty.opt S (.prod fsRecvStT (.prod .nat (.prod lpubT PlainT)))).denote) := rfl
        rw [hleaf]
        have hmin : (if idx < B then idx else B) = min idx B := by
          by_cases hlt : idx < B <;> simp [hlt, Nat.min_def] <;> omega
        simp only [decide_eq_true_eq, hmin]
    change (Expr.caseOpt _ _ _).eval ρ₁ = _
    rw [eval_caseOpt, eval_caseOpt]
    have hlk := find_map_snd_eq_lookup idx (sk.take B0)
    rcases hfind : (sk.take B0).find? (fun x => decide (x.1 = idx)) with _ | ⟨kFound, keyFound⟩
    · have hfind0 :
          (Expr.findB B0 (.snd (.snd (.fst (.var (.succ .zero)))))
            (.eqN (.fst (.var .zero)) (.fst (.snd (.snd (.var (.succ (.succ .zero))))))) :
            Expr O Γ₁ (.opt (.prod .nat BV256))).eval ρ₁ =
          (none : (@Ty.opt S (.prod .nat BV256)).denote) := hfind
      rw [hfind0]
      rw [hfind] at hlk
      dsimp only [Option.map] at hlk
      dsimp only [fsAtomicB, fsAtomic, fromAEADPRG, AEADScheme.movePubPartToAD]
      rw [← hlk, hpub]
      rw [eval_ite]
      by_cases hbad : idx ≤ lastIdx ∨ maxForwardJumps < idx - lastIdx - 1
      · have hcond0 :
            (Expr.and
              (.lt (.fst (.snd (.fst (.var (.succ .zero)))))
                   (.fst (.snd (.snd (.var (.succ .zero))))))
              (.not (.lt (.nat maxForwardJumps)
                (.sub (.sub (.fst (.snd (.snd (.var (.succ .zero)))))
                            (.fst (.snd (.fst (.var (.succ .zero)))))) (.nat 1)))) :
              Expr O Γ₁ .bool).eval ρ₁ =
            (false : (@Ty.bool S).denote) := by
          change (decide (lastIdx < idx) && !decide (maxForwardJumps < idx - lastIdx - 1)) = false
          rcases hbad with h1 | h2
          · have : ¬ lastIdx < idx := by omega
            simp [this]
          · simp [h2]
        rw [hcond0]
        simp only [Bool.false_eq_true, ↓reduceIte, hbad, Option.map_none]
        rfl
      · have hnot := not_or.mp hbad
        have hlt1 : lastIdx < idx := by omega
        have hle2 : idx - lastIdx - 1 ≤ maxForwardJumps := by omega
        have hcond1 :
            (Expr.and
              (.lt (.fst (.snd (.fst (.var (.succ .zero)))))
                   (.fst (.snd (.snd (.var (.succ .zero))))))
              (.not (.lt (.nat maxForwardJumps)
                (.sub (.sub (.fst (.snd (.snd (.var (.succ .zero)))))
                            (.fst (.snd (.fst (.var (.succ .zero)))))) (.nat 1)))) :
              Expr O Γ₁ .bool).eval ρ₁ =
            (true : (@Ty.bool S).denote) := by
          change (decide (lastIdx < idx) && !decide (maxForwardJumps < idx - lastIdx - 1)) = true
          simp [hlt1, hle2]
        rw [hcond1]
        simp only [↓reduceIte, hbad]
        let skipRes := skipKeys (lChainPRG C.F) (idx - lastIdx - 1) ck lastIdx (sk.take B0)
        have hskip :
            (Expr.foldrB maxForwardJumps
              (.take (.sub (.sub (.fst (.snd (.snd (.var (.succ .zero)))))
                                 (.fst (.snd (.fst (.var (.succ .zero)))))) (.nat 1))
                     (unitsPowExpr ℓ Pt C Dh encPt encT lam 15))
              (.pair (.fst (.fst (.var (.succ .zero))))
                (.pair (.fst (.snd (.fst (.var (.succ .zero)))))
                  (.take (.nat B0) (.snd (.snd (.fst (.var (.succ .zero))))))))
              (.letE (chainGenExpr ℓ Pt C Dh encPt encT lam (.fst (.var (.succ .zero))))
                (let st' := Expr.var (.succ (.succ .zero))
                 let pNext := Expr.add (.fst (.snd st')) (.nat 1)
                 .pair (.fst (.var .zero))
                   (.pair pNext (.cons (.pair pNext (.snd (.var .zero))) (.snd (.snd st')))))) :
              Expr O Γ₁ fsRecvStT).eval ρ₁ =
            (fsRecvStV (ℓ := ℓ) (Pt := Pt)
              ⟨skipRes.1, lastIdx + (idx - lastIdx - 1), skipRes.2⟩ :
              (fsRecvStT (ℓ := ℓ) (Pt := Pt)).denote) := by
          change (((unitsPowExpr ℓ Pt C Dh encPt encT lam (Γ := Γ₁) 15).eval ρ₁).take
              (idx - lastIdx - 1) |>.take maxForwardJumps).foldr
            (fun (x : Unit) (acc : BitVec 256 × (ℕ × List (ℕ × BitVec 256))) =>
              let g := (chainGenExpr ℓ Pt C Dh encPt encT lam
                (Γ := .unit :: fsRecvStT :: Γ₁) (.fst (.var (.succ .zero)))).eval
                (.cons x (.cons acc ρ₁))
              (g.1, (acc.2.1 + 1, (acc.2.1 + 1, g.2) :: acc.2.2)))
            (ck, (lastIdx, sk.take B0)) = _
          rw [unitsPowExpr_eval]
          have hm25k : maxForwardJumps ≤ 2 ^ 15 := by norm_num [maxForwardJumps]
          have htake1 : (List.replicate (2 ^ 15) ()).take (idx - lastIdx - 1) =
              List.replicate (idx - lastIdx - 1) () := by
            rw [List.take_replicate, Nat.min_eq_left (by omega)]
          have htake2 : (List.replicate (idx - lastIdx - 1) ()).take maxForwardJumps =
              List.replicate (idx - lastIdx - 1) () := by
            rw [List.take_replicate, Nat.min_eq_right hle2]
          have hstep_eq :
              (fun (x : Unit) (acc : BitVec 256 × (ℕ × List (ℕ × BitVec 256))) =>
                let g := (chainGenExpr ℓ Pt C Dh encPt encT lam
                  (Γ := .unit :: fsRecvStT :: Γ₁) (.fst (.var (.succ .zero)))).eval
                  (.cons x (.cons acc ρ₁))
                (g.1, (acc.2.1 + 1, (acc.2.1 + 1, g.2) :: acc.2.2))) =
              (fun (_ : Unit) (st : BitVec 256 × (ℕ × List (ℕ × BitVec 256))) =>
                let g := (lChainPRG C.F st.2.1).gen st.1
                (g.1, (st.2.1 + 1, (st.2.1 + 1, g.2) :: st.2.2))) := by
            funext x st
            rw [chainGenExpr_eval ℓ Pt C Dh encPt encT lam _ _ st.2.1]
            rfl
          rw [htake1, htake2, hstep_eq, foldr_replicate_skipKeys]
          rfl
        rw [eval_letE, hskip]
        let genRes := (lChainPRG C.F (idx - 1)).gen skipRes.1
        have hsome1 :
            (Expr.letE (chainGenExpr ℓ Pt C Dh encPt encT lam (.fst (.var .zero)))
              (.some (.pair (.snd (.var .zero))
                (.pair (.fst (.var .zero))
                  (.pair (.fst (.snd (.snd (.var (.succ (.succ (.succ .zero)))))))
                    (.snd (.snd (.var (.succ .zero)))))))) :
              Expr O (fsRecvStT :: Γ₁) (.opt (.prod BV256 fsRecvStT))).eval
            (.cons (fsRecvStV (ℓ := ℓ) (Pt := Pt)
              ⟨skipRes.1, lastIdx + (idx - lastIdx - 1), skipRes.2⟩) ρ₁) =
            (some ((genRes.2 : (BV256 (ℓ := ℓ) (Pt := Pt)).denote),
              fsRecvStV (ℓ := ℓ) (Pt := Pt) ⟨genRes.1, idx, skipRes.2⟩) :
              (@Ty.opt S (.prod BV256 fsRecvStT)).denote) := by
          rw [eval_letE, chainGenExpr_eval ℓ Pt C Dh encPt encT lam _ _ (idx - 1)]
          rfl
        rw [hsome1]
        dsimp only [aeadAtomic]
        rw [hdec genRes.2 ⟨genRes.1, idx, skipRes.2⟩]
        rcases (lAead C protoSignalCodec ℓ encT idOf).dec genRes.2 ((idx, h), pub) wsc with _ | m <;>
          rfl
    · have hfind1 :
          (Expr.findB B0 (.snd (.snd (.fst (.var (.succ .zero)))))
            (.eqN (.fst (.var .zero)) (.fst (.snd (.snd (.var (.succ (.succ .zero))))))) :
            Expr O Γ₁ (.opt (.prod .nat BV256))).eval ρ₁ =
          (some (kFound, (keyFound : (BV256 (ℓ := ℓ) (Pt := Pt)).denote)) :
            (@Ty.opt S (.prod .nat BV256)).denote) := hfind
      rw [hfind1]
      rw [hfind] at hlk
      dsimp only [Option.map] at hlk
      dsimp only [fsAtomicB, fsAtomic, fromAEADPRG, AEADScheme.movePubPartToAD]
      rw [← hlk, hpub]
      have hsome2 :
          (let filtSk : Expr O (.prod .nat BV256 :: Γ₁) (.list (.prod .nat BV256)) :=
             .foldrB B0 (.snd (.snd (.fst (.var (.succ (.succ .zero)))))) .nil
               (.ite (.eqN (.fst (.var .zero))
                   (.fst (.snd (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))))
                 (.var (.succ .zero))
                 (.cons (.var .zero) (.var (.succ .zero))))
           Expr.some (.pair (.snd (.var .zero))
             (.pair (.fst (.fst (.var (.succ (.succ .zero)))))
               (.pair (.fst (.snd (.fst (.var (.succ (.succ .zero)))))) filtSk)))).eval
          (.cons (kFound, (keyFound : (BV256 (ℓ := ℓ) (Pt := Pt)).denote)) ρ₁) =
          (some ((keyFound : (BV256 (ℓ := ℓ) (Pt := Pt)).denote),
            fsRecvStV (ℓ := ℓ) (Pt := Pt) ⟨ck, lastIdx, (sk.take B0).filter (·.1 != idx)⟩) :
            (@Ty.opt S (.prod BV256 fsRecvStT)).denote) := by
        change some (keyFound, (ck, (lastIdx,
          (sk.take B0).foldr (fun x acc => if decide (x.1 = idx) then acc else x :: acc) []))) = _
        rw [foldr_filter_neq idx (sk.take B0)]
        rfl
      rw [hsome2]
      dsimp only [aeadAtomic]
      rw [hdec keyFound ⟨ck, lastIdx, (sk.take B0).filter (·.1 != idx)⟩]
      rcases (lAead C protoSignalCodec ℓ encT idOf).dec keyFound ((idx, h), pub) wsc with _ | m <;>
        rfl


theorem fsRecvExpr_cost (B0 B : ℕ) :
    (fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B).cost ≤
      20 * B0 + 3 * bits B + 16 * (ℓ / 32) + 2200000 := by
  let inT : Ty S := .prod fsRecvStT (.prod fig8HdrT lctT)
  let Γ₀ : List (Ty S) := [inT, .prod IdKey IdKey]
  let Γ₁ : List (Ty S) := [lpubT, inT, .prod IdKey IdKey]
  have hlpub := lPubOfExpr_cost ℓ Pt C Dh encPt encT lam (Γ := Γ₀) (.snd (.snd (.snd (.var .zero))))
  have hpow := unitsPowExpr_cost ℓ Pt C Dh encPt encT lam (Γ := Γ₁) 15
  have hcg1 := chainGenExpr_cost ℓ Pt C Dh encPt encT lam
    (Γ := .unit :: fsRecvStT :: Γ₁) (.fst (.var (.succ .zero)))
  have hcg2 := chainGenExpr_cost ℓ Pt C Dh encPt encT lam
    (Γ := fsRecvStT :: Γ₁) (.fst (.var .zero))
  have hadec := aeadDecExpr_cost ℓ Pt C Dh encPt encT lam
  have hbB0 := bits_le_succ B0
  have hb25k : bits 25000 = 15 := by
    unfold bits
    have hlo : 14 ≤ Nat.log 2 25000 :=
      (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by norm_num)
    have hhi : Nat.log 2 25000 < 15 :=
      Nat.log_lt_of_lt_pow (by omega) (by norm_num)
    omega
  have hmfj : maxForwardJumps = 25000 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hmax13 : max 1 3 = 3 := rfl
  have h2p15 : (2 : ℕ) ^ 15 = 32768 := by norm_num
  rw [h2p15] at hpow
  simp only [fsRecvExpr, appAux_cost, Expr.cost, hmfj, hb1, hb25k,
    Nat.reduceAdd, hmax13] at hlpub hcg1 hcg2 ⊢
  generalize (lPubOfExpr ℓ Pt C Dh encPt encT lam (Γ := Γ₀)
    (.snd (.snd (.snd (.var .zero))))).cost = c_lpub at hlpub ⊢
  generalize (unitsPowExpr ℓ Pt C Dh encPt encT lam (Γ := Γ₁) 15).cost = c_pow at hpow ⊢
  generalize (chainGenExpr ℓ Pt C Dh encPt encT lam
    (Γ := .unit :: fsRecvStT :: Γ₁) (.fst (.var (.succ .zero)))).cost = c_cg1 at hcg1 ⊢
  generalize (chainGenExpr ℓ Pt C Dh encPt encT lam
    (Γ := fsRecvStT :: Γ₁) (.fst (.var .zero))).cost = c_cg2 at hcg2 ⊢
  generalize (aeadDecExpr ℓ Pt C Dh encPt encT lam).cost = c_adec at hadec ⊢
  generalize bits B0 = bB0 at hbB0 ⊢
  generalize bits B = bB
  generalize ℓ / 32 = q32 at hlpub hadec ⊢
  omega

theorem fsRecvExpr_size (B0 B : ℕ) :
    (fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B).size ≤
      3 * bits B0 + 2 * bits B + 1200 := by
  let inT : Ty S := .prod fsRecvStT (.prod fig8HdrT lctT)
  let Γ₀ : List (Ty S) := [inT, .prod IdKey IdKey]
  let Γ₁ : List (Ty S) := [lpubT, inT, .prod IdKey IdKey]
  have hlpub := lPubOfExpr_size ℓ Pt C Dh encPt encT lam (Γ := Γ₀) (.snd (.snd (.snd (.var .zero))))
  have hpow := unitsPowExpr_size ℓ Pt C Dh encPt encT lam (Γ := Γ₁) 15
  have hcg1 := chainGenExpr_size ℓ Pt C Dh encPt encT lam
    (Γ := .unit :: fsRecvStT :: Γ₁) (.fst (.var (.succ .zero)))
  have hcg2 := chainGenExpr_size ℓ Pt C Dh encPt encT lam
    (Γ := fsRecvStT :: Γ₁) (.fst (.var .zero))
  have hadec := aeadDecExpr_size ℓ Pt C Dh encPt encT lam
  have hb25k : bits 25000 = 15 := by
    unfold bits
    have hlo : 14 ≤ Nat.log 2 25000 :=
      (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by norm_num)
    have hhi : Nat.log 2 25000 < 15 :=
      Nat.log_lt_of_lt_pow (by omega) (by norm_num)
    omega
  have hmfj : maxForwardJumps = 25000 := rfl
  have hb1 : bits 1 = 1 := rfl
  simp only [fsRecvExpr, appAux_size, Expr.size, hmfj, hb1, hb25k,
    Nat.reduceAdd] at hlpub hpow hcg1 hcg2 ⊢
  generalize (lPubOfExpr ℓ Pt C Dh encPt encT lam (Γ := Γ₀)
    (.snd (.snd (.snd (.var .zero))))).size = s_lpub at hlpub ⊢
  generalize (unitsPowExpr ℓ Pt C Dh encPt encT lam (Γ := Γ₁) 15).size = s_pow at hpow ⊢
  generalize (chainGenExpr ℓ Pt C Dh encPt encT lam
    (Γ := .unit :: fsRecvStT :: Γ₁) (.fst (.var (.succ .zero)))).size = s_cg1 at hcg1 ⊢
  generalize (chainGenExpr ℓ Pt C Dh encPt encT lam
    (Γ := fsRecvStT :: Γ₁) (.fst (.var .zero))).size = s_cg2 at hcg2 ⊢
  generalize (aeadDecExpr ℓ Pt C Dh encPt encT lam).size = s_adec at hadec ⊢
  generalize bits B0 = bB0
  generalize bits B = bB
  omega

def ckaInitAExpr : Expr O [BV256, .prod IdKey IdKey] ckaStT :=
  .inl (opGrp ℓ Pt C Dh encPt encT lam .ptDh
    (.pair (.var .zero) (opGrp ℓ Pt C Dh encPt encT lam .ptBase .unit)))

@[simp] theorem ckaInitAExpr_eval (idOf : Party → IdentityKey) (kc : BitVec 256) :
    (ckaInitAExpr ℓ Pt C Dh encPt encT lam).eval (.cons kc (.cons (idOf .A, idOf .B) .nil)) =
      ckaStV ((dhSchemeFb Dh).initA kc) := rfl

theorem ckaInitAExpr_cost : (ckaInitAExpr ℓ Pt C Dh encPt encT lam).cost ≤ 15 := by
  simp only [ckaInitAExpr, opGrp_cost, AtomicGroupOp.cost, Expr.cost]; omega

theorem ckaInitAExpr_size : (ckaInitAExpr ℓ Pt C Dh encPt encT lam).size ≤ 10 := by
  simp only [ckaInitAExpr, opGrp_size, Expr.size]; omega

def ckaInitBExpr : Expr O [BV256, .prod IdKey IdKey] ckaStT :=
  .inr (.var .zero)

@[simp] theorem ckaInitBExpr_eval (idOf : Party → IdentityKey) (kc : BitVec 256) :
    (ckaInitBExpr ℓ Pt C Dh encPt encT lam).eval (.cons kc (.cons (idOf .A, idOf .B) .nil)) =
      ckaStV ((dhSchemeFb Dh).initB kc) := rfl

theorem ckaInitBExpr_cost : (ckaInitBExpr ℓ Pt C Dh encPt encT lam).cost = 2 := rfl

theorem ckaInitBExpr_size : (ckaInitBExpr ℓ Pt C Dh encPt encT lam).size = 2 := rfl

def ckaSendExpr :
    Expr O [.prod ckaStT BV256, .prod IdKey IdKey] (.prod ckaStT (.prod PtT PtT)) :=
  .caseSum (.fst (.var .zero))
    (let x1 : Expr O [PtT, .prod ckaStT BV256, .prod IdKey IdKey] BV256 := .snd (.var (.succ .zero))
     let pubX := opGrp ℓ Pt C Dh encPt encT lam .ptDh
       (.pair x1 (opGrp ℓ Pt C Dh encPt encT lam .ptBase .unit))
     .pair (.inr x1) (.pair pubX (opGrp ℓ Pt C Dh encPt encT lam .ptDh (.pair x1 (.var .zero)))))
    (let x1 : Expr O [BV256, .prod ckaStT BV256, .prod IdKey IdKey] BV256 := .snd (.var (.succ .zero))
     let pubX := opGrp ℓ Pt C Dh encPt encT lam .ptDh
       (.pair x1 (opGrp ℓ Pt C Dh encPt encT lam .ptBase .unit))
     .pair (.inr x1) (.pair pubX (opGrp ℓ Pt C Dh encPt encT lam .ptBase .unit)))

@[simp] theorem ckaSendExpr_eval (idOf : Party → IdentityKey)
    (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (x : BitVec 256) :
    (ckaSendExpr ℓ Pt C Dh encPt encT lam).eval
      (.cons (ckaStV γ, x) (.cons (idOf .A, idOf .B) .nil)) =
    let res := (dhSchemeFb Dh).send γ x
    (ckaStV res.1, (res.2.1, res.2.2)) := by
  cases γ <;>
    simp [ckaSendExpr, dhSchemeFb, ckaStV, opGrp_eval, AtomicGroupOp.eval, Expr.eval]

theorem ckaSendExpr_cost : (ckaSendExpr ℓ Pt C Dh encPt encT lam).cost ≤ 55 := by
  simp only [ckaSendExpr, opGrp_cost, AtomicGroupOp.cost, Expr.cost]; omega

theorem ckaSendExpr_size : (ckaSendExpr ℓ Pt C Dh encPt encT lam).size ≤ 40 := by
  simp only [ckaSendExpr, opGrp_size, Expr.size]; omega

def ckaRecvExpr :
    Expr O [.prod ckaStT PtT, .prod IdKey IdKey] (.prod ckaStT PtT) :=
  .caseSum (.fst (.var .zero))
    (let t1 : Expr O [PtT, .prod ckaStT PtT, .prod IdKey IdKey] PtT := .snd (.var (.succ .zero))
     .pair (.inl t1) (opGrp ℓ Pt C Dh encPt encT lam .ptBase .unit))
    (let t1 : Expr O [BV256, .prod ckaStT PtT, .prod IdKey IdKey] PtT := .snd (.var (.succ .zero))
     .pair (.inl t1) (opGrp ℓ Pt C Dh encPt encT lam .ptDh (.pair (.var .zero) t1)))

@[simp] theorem ckaRecvExpr_eval (idOf : Party → IdentityKey)
    (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (t : Pt) :
    (ckaRecvExpr ℓ Pt C Dh encPt encT lam).eval
      (.cons (ckaStV γ, t) (.cons (idOf .A, idOf .B) .nil)) =
    let res := (dhSchemeFb Dh).receive γ t
    (ckaStV res.1, res.2) := by
  cases γ <;>
    simp [ckaRecvExpr, dhSchemeFb, ckaStV, opGrp_eval, AtomicGroupOp.eval, Expr.eval]

theorem ckaRecvExpr_cost : (ckaRecvExpr ℓ Pt C Dh encPt encT lam).cost ≤ 30 := by
  simp only [ckaRecvExpr, opGrp_cost, AtomicGroupOp.cost, Expr.cost]; omega

theorem ckaRecvExpr_size : (ckaRecvExpr ℓ Pt C Dh encPt encT lam).size ≤ 25 := by
  simp only [ckaRecvExpr, opGrp_size, Expr.size]; omega

private theorem hkdfExtract_length (F : ShaCompress) (salt : CryptoGames.HKDF.Salt)
    (ikm : List (BitVec 8)) :
    (hkdfExtract F salt ikm).length = 32 := by
  unfold hkdfExtract hmacWith
  cases salt <;> exact sha256With_length F _

def prngInitExpr : Expr O [BV256, .prod IdKey IdKey] BV256 := .var .zero

@[simp] theorem prngInitExpr_eval (idOf : Party → IdentityKey) (kr : BitVec 256) :
    (prngInitExpr ℓ Pt C Dh encPt encT lam).eval (.cons kr (.cons (idOf .A, idOf .B) .nil)) =
      (rootPRNG C.F encPt).init kr := rfl

theorem prngInitExpr_cost : (prngInitExpr ℓ Pt C Dh encPt encT lam).cost = 1 := rfl

theorem prngInitExpr_size : (prngInitExpr ℓ Pt C Dh encPt encT lam).size = 1 := rfl

def prngUpExpr : Expr O [.prod BV256 PtT, .prod IdKey IdKey] (.prod BV256 BV256) :=
  opGrp ℓ Pt C Dh encPt encT lam .rootExpandPrg
    (opGrp ℓ Pt C Dh encPt encT lam .extractPrfTag (.var .zero))

@[simp] theorem prngUpExpr_eval (idOf : Party → IdentityKey) (σ : BitVec 256) (I : Pt) :
    (prngUpExpr ℓ Pt C Dh encPt encT lam).eval (.cons (σ, I) (.cons (idOf .A, idOf .B) .nil)) =
      (rootPRNG C.F encPt).up σ I := by
  dsimp only [prngUpExpr, Expr.eval, env_get_zero, opGrp_eval, AtomicGroupOp.eval,
    expandPRG, rootExpand, extractPRF, rootPRNG, rootKdf, CryptoGames.HKDF.hkdf]
  rw [keyToBytes32_bytesToKey32 _ (hkdfExtract_length C.F _ _)]

theorem prngUpExpr_cost : (prngUpExpr ℓ Pt C Dh encPt encT lam).cost ≤ 25 := by
  simp only [prngUpExpr, opGrp_cost, AtomicGroupOp.cost, Expr.cost]; omega

theorem prngUpExpr_size : (prngUpExpr ℓ Pt C Dh encPt encT lam).size ≤ 10 := by
  simp only [prngUpExpr, opGrp_size, Expr.size]; omega

def lamIExpr : Expr O [.unit, .prod IdKey IdKey] PtT :=
  opGrp ℓ Pt C Dh encPt encT lam .ptLam .unit

@[simp] theorem lamIExpr_eval (idOf : Party → IdentityKey) :
    (lamIExpr ℓ Pt C Dh encPt encT lam).eval (.cons () (.cons (idOf .A, idOf .B) .nil)) = lam := rfl

theorem lamIExpr_cost : (lamIExpr ℓ Pt C Dh encPt encT lam).cost = 2 := rfl

theorem lamIExpr_size : (lamIExpr ℓ Pt C Dh encPt encT lam).size = 2 := rfl

def defaultEExpr : Expr O [.unit, .prod IdKey IdKey] lctT :=
  .pair (.nat 0)
    (.pair
      (.pair (opPure ℓ Pt C Dh encPt encT lam (.bytesLit 32 []) .unit)
        (opPure ℓ Pt C Dh encPt encT lam (.u64Lit 0#64) .unit))
      (opPure ℓ Pt C Dh encPt encT lam (.bv256Lit 0#256) .unit))

@[simp] theorem defaultEExpr_eval (idOf : Party → IdentityKey) :
    (defaultEExpr ℓ Pt C Dh encPt encT lam).eval (.cons () (.cons (idOf .A, idOf .B) .nil)) =
      lctV (ℓ := ℓ) (Pt := Pt) default := by
  have hz : bytesToKey32 (List.replicate 32 0#8) = 0#256 := by decide
  dsimp only [defaultEExpr, Expr.eval, opPure_eval, AtomicPureOp.eval, lctV, wireSaltCtV, salt32V]
  exact congrArg (fun s => (0, (([], 0#64), s))) hz.symm

theorem defaultEExpr_cost : (defaultEExpr ℓ Pt C Dh encPt encT lam).cost ≤ 50 := by
  have hb0 : bits 0 = 1 := rfl
  simp only [defaultEExpr, opPure_cost, AtomicPureOp.cost, Expr.cost, List.length_nil,
    PNat.val_ofNat, hb0]
  omega

theorem defaultEExpr_size : (defaultEExpr ℓ Pt C Dh encPt encT lam).size ≤ 50 := by
  have hb0 : bits 0 = 1 := rfl
  simp only [defaultEExpr, opPure_size, AtomicPureOp.opSize, List.length_nil, Expr.size, hb0]
  omega

def eqPtExpr : Expr O [.prod PtT PtT, .prod IdKey IdKey] .bool :=
  opGrp ℓ Pt C Dh encPt encT lam .ptEq (.var .zero)

@[simp] theorem eqPtExpr_eval (idOf : Party → IdentityKey) (a b : Pt) :
    (eqPtExpr ℓ Pt C Dh encPt encT lam).eval (.cons (a, b) (.cons (idOf .A, idOf .B) .nil)) =
      @BEq.beq Pt instBEqOfDecidableEq a b := rfl

theorem eqPtExpr_cost : (eqPtExpr ℓ Pt C Dh encPt encT lam).cost = 3 := rfl

theorem eqPtExpr_size : (eqPtExpr ℓ Pt C Dh encPt encT lam).size = 2 := rfl

private theorem salt32V_inj {s1 s2 : List.Vector (BitVec 8) 32} (h : salt32V s1 = salt32V s2) :
    s1 = s2 := by
  have := congrArg salt32OfV h
  rwa [salt32OfV_salt32V, salt32OfV_salt32V] at this

def eqMExpr :
    Expr O [.prod (.prod lpubT PlainT) (.prod lpubT PlainT), .prod IdKey IdKey] .bool :=
  let m1 := Expr.fst (.var .zero)
  let m2 := Expr.snd (.var .zero)
  let p1 := Expr.fst m1
  let p2 := Expr.fst m2
  .and (opPure ℓ Pt C Dh encPt encT lam .u32Eq (.pair (.fst p1) (.fst p2)))
    (.and (opPure ℓ Pt C Dh encPt encT lam (.bytesEq 32 32)
        (.pair (.fst (.snd p1)) (.fst (.snd p2))))
      (.and (opPure ℓ Pt C Dh encPt encT lam .bv256Eq
          (.pair (.fst (.snd (.snd p1))) (.fst (.snd (.snd p2)))))
        (.and (optBytesEqExpr ℓ Pt C Dh encPt encT lam
            (.snd (.snd (.snd p1))) (.snd (.snd (.snd p2))))
          (opPure ℓ Pt C Dh encPt encT lam .plainEq (.pair (.snd m1) (.snd m2))))))

theorem eqMExpr_eval (idOf : Party → IdentityKey)
    (m1 m2 : LibsignalMsgPublicPart × Plain ℓ) :
    (eqMExpr ℓ Pt C Dh encPt encT lam).eval
      (.cons ((lpubV m1.1, m1.2), (lpubV m2.1, m2.2)) (.cons (idOf .A, idOf .B) .nil)) =
    @BEq.beq (LibsignalMsgPublicPart × Plain ℓ) instBEqOfDecidableEq m1 m2 := by
  rcases m1 with ⟨⟨pn1, pq1, s1, ad1⟩, pl1⟩
  rcases m2 with ⟨⟨pn2, pq2, s2, ad2⟩, pl2⟩
  have hs_iff : salt32V s1 = salt32V s2 ↔ s1 = s2 := ⟨salt32V_inj, fun h => h ▸ rfl⟩
  dsimp only [eqMExpr, Expr.eval, env_get_zero, opPure_eval, AtomicPureOp.eval]
  rw [optBytesEqExpr_eval]
  dsimp only [Expr.eval, env_get_zero, lpubV]
  apply Bool.eq_iff_iff.mpr
  rw [@beq_iff_eq (LibsignalMsgPublicPart × Plain ℓ) instBEqOfDecidableEq _]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Prod.mk.injEq,
    LibsignalMsgPublicPart.mk.injEq, hs_iff]
  tauto

theorem eqMExpr_cost :
    (eqMExpr ℓ Pt C Dh encPt encT lam).cost ≤ ℓ / 32 + 230 := by
  have hopt := optBytesEqExpr_cost ℓ Pt C Dh encPt encT lam
    (Γ := [.prod (.prod lpubT PlainT) (.prod lpubT PlainT), .prod IdKey IdKey])
    (.snd (.snd (.snd (.fst (.fst (.var .zero))))))
    (.snd (.snd (.snd (.fst (.snd (.var .zero))))))
  simp only [eqMExpr, opPure_cost, AtomicPureOp.cost, Expr.cost, PNat.val_ofNat] at hopt ⊢
  omega

theorem eqMExpr_size :
    (eqMExpr ℓ Pt C Dh encPt encT lam).size ≤ 120 := by
  have hopt := optBytesEqExpr_size ℓ Pt C Dh encPt encT lam
    (Γ := [.prod (.prod lpubT PlainT) (.prod lpubT PlainT), .prod IdKey IdKey])
    (.snd (.snd (.snd (.fst (.fst (.var .zero))))))
    (.snd (.snd (.snd (.fst (.snd (.var .zero))))))
  simp only [eqMExpr, opPure_size, AtomicPureOp.opSize, Expr.size] at hopt ⊢
  omega

def lctEqBody {Γ : List (Ty S)} (c1 c2 : Expr O Γ lctT) : Expr O Γ .bool :=
  .and (.eqN (.fst c1) (.fst c2))
    (.and (opPure ℓ Pt C Dh encPt encT lam (.bytesEq 32 32)
        (.pair (.fst (.fst (.snd c1))) (.fst (.fst (.snd c2)))))
      (.and (opPure ℓ Pt C Dh encPt encT lam .u64Eq
          (.pair (.snd (.fst (.snd c1))) (.snd (.fst (.snd c2)))))
        (opPure ℓ Pt C Dh encPt encT lam .bv256Eq
          (.pair (.snd (.snd c1)) (.snd (.snd c2))))))

theorem lctEqBody_eval {Γ : List (Ty S)} (c1 c2 : Expr O Γ lctT) (ρ : Env Γ)
    (e1 e2 : ℕ × LibsignalCiphertextWithSalt32)
    (h1 : c1.eval ρ = lctV e1) (h2 : c2.eval ρ = lctV e2) :
    (lctEqBody ℓ Pt C Dh encPt encT lam c1 c2).eval ρ = decide (e1 = e2) := by
  rcases e1 with ⟨i1, ⟨s1, t1⟩, b1⟩
  rcases e2 with ⟨i2, ⟨s2, t2⟩, b2⟩
  have hb_iff : salt32V b1 = salt32V b2 ↔ b1 = b2 := ⟨salt32V_inj, fun h => h ▸ rfl⟩
  simp only [lctEqBody, Expr.eval, opPure_eval, AtomicPureOp.eval, h1, h2, lctV, wireSaltCtV]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Prod.mk.injEq, hb_iff]
  tauto

theorem lctEqBody_cost {Γ : List (Ty S)} (c1 c2 : Expr O Γ lctT) :
    (lctEqBody ℓ Pt C Dh encPt encT lam c1 c2).cost ≤ 4 * c1.cost + 4 * c2.cost + 110 := by
  simp only [lctEqBody, opPure_cost, AtomicPureOp.cost, Expr.cost, PNat.val_ofNat]
  omega

theorem lctEqBody_size {Γ : List (Ty S)} (c1 c2 : Expr O Γ lctT) :
    (lctEqBody ℓ Pt C Dh encPt encT lam c1 c2).size ≤ 4 * c1.size + 4 * c2.size + 40 := by
  simp only [lctEqBody, opPure_size, AtomicPureOp.opSize, Expr.size]
  omega

def eqEExpr : Expr O [.prod lctT lctT, .prod IdKey IdKey] .bool :=
  lctEqBody ℓ Pt C Dh encPt encT lam (.fst (.var .zero)) (.snd (.var .zero))

@[simp] theorem eqEExpr_eval (idOf : Party → IdentityKey)
    (e1 e2 : ℕ × LibsignalCiphertextWithSalt32) :
    (eqEExpr ℓ Pt C Dh encPt encT lam).eval
      (.cons (lctV e1, lctV e2) (.cons (idOf .A, idOf .B) .nil)) =
    @BEq.beq (ℕ × LibsignalCiphertextWithSalt32) instBEqOfDecidableEq e1 e2 := by
  exact lctEqBody_eval ℓ Pt C Dh encPt encT lam _ _ _ e1 e2 rfl rfl

theorem eqEExpr_cost : (eqEExpr ℓ Pt C Dh encPt encT lam).cost ≤ 130 := by
  have h := lctEqBody_cost ℓ Pt C Dh encPt encT lam
    (Γ := [.prod lctT lctT, .prod IdKey IdKey]) (.fst (.var .zero)) (.snd (.var .zero))
  simp only [eqEExpr, Expr.cost] at h ⊢
  omega

theorem eqEExpr_size : (eqEExpr ℓ Pt C Dh encPt encT lam).size ≤ 60 := by
  have h := lctEqBody_size ℓ Pt C Dh encPt encT lam
    (Γ := [.prod lctT lctT, .prod IdKey IdKey]) (.fst (.var .zero)) (.snd (.var .zero))
  simp only [eqEExpr, Expr.size] at h ⊢
  omega

def smEqCtExpr : Expr O [.prod fig8CtT fig8CtT, .prod IdKey IdKey] .bool :=
  let c1 := Expr.fst (.var .zero)
  let c2 := Expr.snd (.var .zero)
  .and (.eqN (.fst (.fst c1)) (.fst (.fst c2)))
    (.and (optPtEqExpr ℓ Pt C Dh encPt encT lam (.snd (.fst c1)) (.snd (.fst c2)))
      (lctEqBody ℓ Pt C Dh encPt encT lam (.snd c1) (.snd c2)))

theorem smEqCtExpr_eval (idOf : Party → IdentityKey) (c1 c2 : Fig8C Pt) :
    (smEqCtExpr ℓ Pt C Dh encPt encT lam).eval
      (.cons (fig8CtV c1, fig8CtV c2) (.cons (idOf .A, idOf .B) .nil)) = (c1 == c2) := by
  rcases c1 with ⟨⟨t1, T1⟩, e1⟩
  rcases c2 with ⟨⟨t2, T2⟩, e2⟩
  let Γ₀ : List (Ty S) := [.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)),
    .prod IdKey IdKey]
  let ρ0 : Env Γ₀ :=
    .cons (fig8CtV ((t1, T1), e1), fig8CtV ((t2, T2), e2)) (.cons (idOf .A, idOf .B) .nil)
  have h1 : (Expr.eqN (.fst (.fst (.fst (.var .zero))))
      (.fst (.fst (.snd (.var .zero)))) : Expr O Γ₀ .bool).eval ρ0 = decide (t1 = t2) := rfl
  have h2 : (optPtEqExpr ℓ Pt C Dh encPt encT lam
      (.snd (.fst (.fst (.var .zero)))) (.snd (.fst (.snd (.var .zero))))).eval ρ0 =
      (T1 == T2) := optPtEqExpr_eval ℓ Pt C Dh encPt encT lam _ _ ρ0
  have h3 : (lctEqBody ℓ Pt C Dh encPt encT lam
      (.snd (.fst (.var .zero))) (.snd (.snd (.var .zero)))).eval ρ0 =
      decide (e1 = e2) :=
    lctEqBody_eval ℓ Pt C Dh encPt encT lam _ _ ρ0 e1 e2 rfl rfl
  change ((Expr.eqN (.fst (.fst (.fst (.var .zero))))
        (.fst (.fst (.snd (.var .zero)))) : Expr O Γ₀ .bool).eval ρ0 &&
      ((optPtEqExpr ℓ Pt C Dh encPt encT lam
        (.snd (.fst (.fst (.var .zero)))) (.snd (.fst (.snd (.var .zero))))).eval ρ0 &&
      (lctEqBody ℓ Pt C Dh encPt encT lam
        (.snd (.fst (.var .zero))) (.snd (.snd (.var .zero)))).eval ρ0)) =
    (((t1, T1), e1) == ((t2, T2), e2))
  rw [h1, h2, h3]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Prod.mk.injEq]
  tauto

theorem smEqCtExpr_cost : (smEqCtExpr ℓ Pt C Dh encPt encT lam).cost ≤ 170 := by
  have h1 := optPtEqExpr_cost ℓ Pt C Dh encPt encT lam
    (Γ := [.prod fig8CtT fig8CtT, .prod IdKey IdKey])
    (.snd (.fst (.fst (.var .zero)))) (.snd (.fst (.snd (.var .zero))))
  have h2 := lctEqBody_cost ℓ Pt C Dh encPt encT lam
    (Γ := [.prod fig8CtT fig8CtT, .prod IdKey IdKey])
    (.snd (.fst (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [smEqCtExpr, Expr.cost] at h1 h2 ⊢
  omega

theorem smEqCtExpr_size : (smEqCtExpr ℓ Pt C Dh encPt encT lam).size ≤ 120 := by
  have h1 := optPtEqExpr_size ℓ Pt C Dh encPt encT lam
    (Γ := [.prod fig8CtT fig8CtT, .prod IdKey IdKey])
    (.snd (.fst (.fst (.var .zero)))) (.snd (.fst (.snd (.var .zero))))
  have h2 := lctEqBody_size ℓ Pt C Dh encPt encT lam
    (Γ := [.prod fig8CtT fig8CtT, .prod IdKey IdKey])
    (.snd (.fst (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [smEqCtExpr, Expr.size] at h1 h2 ⊢
  omega

def smBlankExpr : Expr O [.prod lpubT PlainT, .prod IdKey IdKey] (.prod lpubT PlainT) :=
  .pair (.fst (.var .zero)) (opPure ℓ Pt C Dh encPt encT lam .plainDefault .unit)

@[simp] theorem smBlankExpr_eval (idOf : Party → IdentityKey)
    (m : LibsignalMsgPublicPart × Plain ℓ) :
    (smBlankExpr ℓ Pt C Dh encPt encT lam).eval
      (.cons (lpubV m.1, m.2) (.cons (idOf .A, idOf .B) .nil)) =
    (lpubV (CryptoGames.LibsignalSM.lBlank ℓ m).1, (CryptoGames.LibsignalSM.lBlank ℓ m).2) := by
  dsimp only [smBlankExpr, Expr.eval, env_get_zero, opPure_eval, AtomicPureOp.eval,
    CryptoGames.LibsignalSM.lBlank]
  refine Prod.ext rfl (List.Vector.ext fun i => ?_)
  change (List.Vector.replicate ℓ 0#8).get i = (List.Vector.ofFn default).get i
  rw [List.Vector.get_replicate, List.Vector.get_ofFn]
  rfl

theorem smBlankExpr_cost :
    (smBlankExpr ℓ Pt C Dh encPt encT lam).cost ≤ ℓ / 32 + 10 := by
  simp only [smBlankExpr, opPure_cost, AtomicPureOp.cost, Expr.cost]
  omega

theorem smBlankExpr_size :
    (smBlankExpr ℓ Pt C Dh encPt encT lam).size ≤ 10 := by
  simp only [smBlankExpr, opPure_size, AtomicPureOp.opSize, Expr.size]
  omega

end AtomicOpMacros

end Computational.Proofs.ReductionDsl.Fig8Atomic

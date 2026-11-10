/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
public import Computational.Proofs.ReductionDsl.AtomicTablesHonest -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.MacroLift -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.FSAEAD.PubCosted -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.FSAEAD.HybridCosted -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.FSAEAD.SaltWireCosted -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.PubRed
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.GameHop.StateSim


/-! # Base codecs, `CoinSimEquiv`, and `PureMacroBundle` definitions -/

public section

set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp GameCodec CostedReduction
  handlerImpl bits iterM findML anyML mapML consumeFirstML foldML atomicSig AtomicPureOp
  AtomicSymOp atomicFsOps atomicBaseSamplers bytesToWordLE fitBytesN toLEBytes fig8PubAdOfV
  fig8PubAdT fig8PubAdV fsRecvStOfV fsRecvStT fsRecvStV fsRrDec fsRrEnc fsSendStOfV fsSendStT
  fsSendStV lctOfV lctT lctV lpubOfV lpubT lpubV salt32OfV salt32V slotAdOfV slotAdT slotAdV
  wireSaltCtOfV wireSaltCtT wireSaltCtV wireSignalHdrOfV wireSignalHdrT wireSignalHdrV)

namespace Computational.Proofs.ReductionDsl.FsAtomicMacros
open CryptoGames (Party WireAEAD MACScheme AEADScheme CipherScheme)
open CryptoGames.HMAC (toBEBytes keyToBytes32 hmacWith hmacSha256Trunc8 bytesToWord64LE hmacScheme)
open CryptoGames.HKDF (bytesToKey32 deriveMessageKeys DerivedMessageKeys)
open CryptoGames.CBC (Plain Block nBlocks cbcPkcs7EncryptOnly blockToBytesLE cbcDecRaw)
open CryptoGames.Ratchet (keyToBytesVec32 padOrTruncatePlain)
open CryptoGames.Ratchet.LibsignalInst (Salt32 LibsignalCiphertextWithSalt32
  LibsignalMsgPublicPart dummyKey lIds lHeader lWire lAeadK lAead lAeadR lPubOf lChainPRG lIdeal
  lSaltPRF32 lSaltRed lWireRed slotSaltRed slotWireRed LibsignalWireOracleSpec)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey IdentityKey MessageKeyGenerator
  ProtoSignalMessage SignalMessage SignalHeader SignalMessageProtoCodec serializeContent computeMac
  macLength aesCbcEncrypt aesCbcDecrypt currentVersion signalWireCodec maxForwardJumps)
open CryptoGames.LibsignalAead (SerializedIdentityKeys wireEncode libsignalReceiveWire
  libsignalWireAead)
open CryptoGames.SM.Construction (Header)
open CryptoGames.FSAEAD (ReceiveResult RatchetSenderState RatchetReceiverState)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarintAux decodeVarint decodeKey
  skipBytes skipScalar skipField skipGroup mergeBytes mergeUint32 mergeField decodeLoop
  emptyProtoSignalMessage decode encodeVarintAux encodeVarint encodeKey encodeBytesField
  encodeUint32Field encode protoSignalCodec)
open CryptoVerification.E2E (Bytes u8Vec toU8 ofU8 vecU8 fitVec)

/-- Predicate ensuring `AtomicSymOp.signalMsgEncode` evaluates without output clamping. -/
@[expose, reducible] def atomicShortB (p : LibsignalMsgPublicPart) : Bool :=
  decide (p.pqmsg.length ≤ 96) && p.addrs.all fun a => decide (a.length ≤ 128)

/-! ## `TargetCodecs` roundtrips and `atomicShortB` -/

private theorem ofU8_toU8 (bs : List (BitVec 8)) : ofU8 (toU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons _ _ ih => simp only [toU8, ofU8, List.map_cons] at *; rw [ih]

theorem u8Vec_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) : u8Vec n (vecU8 v) = v := by
  apply List.Vector.eq; rcases v with ⟨l, hl⟩
  simp [u8Vec, vecU8, ofU8_toU8, fitVec, List.Vector.toList, hl]

private theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]

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

@[simp] theorem bytesToKey32_keyToBytes32 (k : BitVec 256) :
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

theorem atomicShortB_iff (p : LibsignalMsgPublicPart) :
    atomicShortB p = true ↔ p.pqmsg.length ≤ 96 ∧ ∀ a ∈ p.addrs, a.length ≤ 128 := by
  unfold atomicShortB
  cases ha : p.addrs with
  | none => simp
  | some a => simp

@[simp] theorem keyToBytesVec32_toList (x : BitVec 256) :
    (keyToBytesVec32 x).toList = keyToBytes32 x := rfl

@[simp] theorem salt32OfV_salt32V (s : Salt32) : salt32OfV (salt32V s) = s := by
  apply List.Vector.eq
  simpa [salt32OfV, salt32V] using keyToBytes32_bytesToKey32 s.toList s.toList_length

@[simp] theorem salt32V_salt32OfV (x : BitVec 256) : salt32V (salt32OfV x) = x := by
  simp [salt32V, salt32OfV]

@[simp] theorem fitBytesN_toList {n : ℕ} (v : List.Vector (BitVec 8) n) :
    fitBytesN n v.toList = v := by
  apply List.Vector.eq
  simp [fitBytesN, List.take_append_of_le_length (le_of_eq v.toList_length.symm)]

@[simp] theorem wireSignalHdrOfV_wireSignalHdrV {ℓ : ℕ} {Pt : Type} (h : SignalHeader) :
    wireSignalHdrOfV (ℓ := ℓ) (Pt := Pt) (wireSignalHdrV h) = h := by
  cases h; rfl

@[simp] theorem wireSignalHdrV_wireSignalHdrOfV {ℓ : ℕ} {Pt : Type}
    (v : (wireSignalHdrT (ℓ := ℓ) (Pt := Pt)).denote) :
    wireSignalHdrV (ℓ := ℓ) (Pt := Pt) (wireSignalHdrOfV v) = v := by
  rcases v with ⟨⟨ver, ⟨rk, ⟨ctr, pctr⟩⟩⟩, ⟨pq, addrs⟩⟩; rfl

@[simp] theorem lpubOfV_lpubV {ℓ : ℕ} {Pt : Type} (p : LibsignalMsgPublicPart) :
    lpubOfV (ℓ := ℓ) (Pt := Pt) (lpubV p) = p := by
  cases p; simp [lpubV, lpubOfV]

@[simp] theorem lpubV_lpubOfV {ℓ : ℕ} {Pt : Type} (v : (lpubT (ℓ := ℓ) (Pt := Pt)).denote) :
    lpubV (ℓ := ℓ) (Pt := Pt) (lpubOfV v) = v := by
  rcases v with ⟨pn, ⟨pq, ⟨sv, addrs⟩⟩⟩; simp [lpubV, lpubOfV]

@[simp] theorem wireSaltCtOfV_wireSaltCtV {ℓ : ℕ} {Pt : Type}
    (c : LibsignalCiphertextWithSalt32) :
    wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) (wireSaltCtV c) = c := by
  rcases c with ⟨w, s⟩; simp [wireSaltCtV, wireSaltCtOfV]

@[simp] theorem wireSaltCtV_wireSaltCtOfV {ℓ : ℕ} {Pt : Type}
    (v : (wireSaltCtT (ℓ := ℓ) (Pt := Pt)).denote) :
    wireSaltCtV (ℓ := ℓ) (Pt := Pt) (wireSaltCtOfV v) = v := by
  rcases v with ⟨w, sv⟩; simp [wireSaltCtV, wireSaltCtOfV]

@[simp] theorem lctOfV_lctV {ℓ : ℕ} {Pt : Type} (c : ℕ × LibsignalCiphertextWithSalt32) :
    lctOfV (ℓ := ℓ) (Pt := Pt) (lctV c) = c := by
  rcases c with ⟨i, w⟩; simp [lctV, lctOfV]

@[simp] theorem lctV_lctOfV {ℓ : ℕ} {Pt : Type} (v : (lctT (ℓ := ℓ) (Pt := Pt)).denote) :
    lctV (ℓ := ℓ) (Pt := Pt) (lctOfV v) = v := by
  rcases v with ⟨i, w⟩; simp [lctV, lctOfV]

@[simp] theorem fig8PubAdOfV_fig8PubAdV {ℓ : ℕ} {Pt : Type}
    (a : Header Pt × LibsignalMsgPublicPart) :
    fig8PubAdOfV (ℓ := ℓ) (Pt := Pt) (fig8PubAdV a) = a := by
  rcases a with ⟨h, p⟩; simp [fig8PubAdV, fig8PubAdOfV]

@[simp] theorem fig8PubAdV_fig8PubAdOfV {ℓ : ℕ} {Pt : Type}
    (v : (fig8PubAdT (ℓ := ℓ) (Pt := Pt)).denote) :
    fig8PubAdV (ℓ := ℓ) (Pt := Pt) (fig8PubAdOfV v) = v := by
  rcases v with ⟨h, p⟩; simp [fig8PubAdV, fig8PubAdOfV]

@[simp] theorem slotAdOfV_slotAdV {ℓ : ℕ} {Pt : Type}
    (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) :
    slotAdOfV (ℓ := ℓ) (Pt := Pt) (slotAdV a) = a := by
  rcases a with ⟨i, b⟩; simp [slotAdV, slotAdOfV]

@[simp] theorem slotAdV_slotAdOfV {ℓ : ℕ} {Pt : Type}
    (v : (slotAdT (ℓ := ℓ) (Pt := Pt)).denote) :
    slotAdV (ℓ := ℓ) (Pt := Pt) (slotAdOfV v) = v := by
  rcases v with ⟨i, b⟩; simp [slotAdV, slotAdOfV]

@[simp] theorem fsSendStOfV_fsSendStV {ℓ : ℕ} {Pt : Type}
    (s : RatchetSenderState (BitVec 256)) :
    fsSendStOfV (ℓ := ℓ) (Pt := Pt) (fsSendStV s) = s := by
  cases s; rfl

@[simp] theorem fsSendStV_fsSendStOfV {ℓ : ℕ} {Pt : Type}
    (v : (fsSendStT (ℓ := ℓ) (Pt := Pt)).denote) :
    fsSendStV (ℓ := ℓ) (Pt := Pt) (fsSendStOfV v) = v := by
  cases v; rfl

@[simp] theorem fsRecvStOfV_fsRecvStV {ℓ : ℕ} {Pt : Type}
    (r : RatchetReceiverState (BitVec 256) (BitVec 256)) :
    fsRecvStOfV (ℓ := ℓ) (Pt := Pt) (fsRecvStV r) = r := by
  cases r; rfl

@[simp] theorem fsRecvStV_fsRecvStOfV {ℓ : ℕ} {Pt : Type}
    (v : (fsRecvStT (ℓ := ℓ) (Pt := Pt)).denote) :
    fsRecvStV (ℓ := ℓ) (Pt := Pt) (fsRecvStOfV v) = v := by
  rcases v with ⟨ck, ⟨idx, sk⟩⟩; rfl

@[simp] theorem fsRrDec_fsRrEnc {ℓ : ℕ} {Pt M : Type} {msgT : Ty (atomicSig ℓ Pt)}
    (encM : M → msgT.denote) (decM : msgT.denote → M) (h : ∀ x, decM (encM x) = x)
    (r : ReceiveResult M) :
    fsRrDec (ℓ := ℓ) (Pt := Pt) decM (fsRrEnc (ℓ := ℓ) (Pt := Pt) encM r) = r := by
  cases r with
  | rejected => rfl
  | accepted i m =>
    cases m with
    | none => rfl
    | some x => simp [fsRrEnc, fsRrDec, h x]

/-! ## Clamp-losslessness of atomic wire and cipher ops -/

private theorem prostDecodeVarintAux_length_le (i : ℕ) (acc : BitVec 64) (bs : Bytes)
    {v : BitVec 64} {rest : Bytes}
    (h : decodeVarintAux i acc bs = some (v, rest)) :
    rest.length ≤ bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b tail ih =>
    simp only [decodeVarintAux] at h
    split at h
    · split at h
      · cases h
      · injection h with hp
        injection hp with _ hr
        subst hr
        exact Nat.le_succ _
    · split at h
      · cases h
      · exact Nat.le_trans (ih _ _ h) (Nat.le_succ _)

private theorem prostDecodeVarint_length_le (bs : Bytes) {v : BitVec 64} {rest : Bytes}
    (h : decodeVarint bs = some (v, rest)) :
    rest.length ≤ bs.length :=
  prostDecodeVarintAux_length_le 0 0 bs h

private theorem prostDecodeKey_length_le (bs : Bytes) {kw : ℕ × WireType} {rest : Bytes}
    (h : decodeKey bs = some (kw, rest)) :
    rest.length ≤ bs.length := by
  unfold decodeKey at h
  cases hd : decodeVarint bs with
  | none => rw [hd] at h; cases h
  | some kr =>
    rcases kr with ⟨key, r0⟩
    have hr0 := prostDecodeVarint_length_le bs hd
    rw [hd] at h
    dsimp only at h
    split at h
    · cases h
    · cases hw : WireType.ofNat? (key.toNat % 8) with
      | none => rw [hw] at h; cases h
      | some wt =>
        rw [hw] at h
        dsimp only at h
        split at h
        · cases h
        · injection h with hp
          injection hp with _ hr
          subst hr
          exact hr0

private theorem prostSkipBytes_length_le (n : ℕ) (bs : Bytes) {rest : Bytes}
    (h : skipBytes n bs = some rest) :
    rest.length ≤ bs.length := by
  unfold skipBytes at h
  split at h
  · cases h
  · injection h with hr
    subst hr
    simp

private theorem prostSkipScalar_length_le (wt : WireType) (bs : Bytes) {rest : Bytes}
    (h : skipScalar wt bs = some rest) :
    rest.length ≤ bs.length := by
  unfold skipScalar at h
  cases wt with
  | varint =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hd, rfl⟩
    exact prostDecodeVarint_length_le bs hd
  | thirtyTwoBit => exact prostSkipBytes_length_le 4 bs h
  | sixtyFourBit => exact prostSkipBytes_length_le 8 bs h
  | lengthDelimited =>
    cases hd : decodeVarint bs with
    | none => rw [hd] at h; cases h
    | some lr =>
      rcases lr with ⟨len, r0⟩
      rw [hd] at h
      dsimp only at h
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

private theorem prostMergeBytes_length_le (wt : WireType) (bs : Bytes) {v rest : Bytes}
    (h : mergeBytes wt bs = some (v, rest)) :
    v.length ≤ bs.length ∧ rest.length ≤ bs.length := by
  unfold mergeBytes at h
  split at h
  · cases h
  · cases hd : decodeVarint bs with
    | none => rw [hd] at h; cases h
    | some lr =>
      rcases lr with ⟨len, r0⟩
      have hr0 := prostDecodeVarint_length_le bs hd
      rw [hd] at h
      dsimp only at h
      split at h
      · cases h
      · injection h with hp
        injection hp with hv hr
        subst hv hr
        exact ⟨Nat.le_trans (List.length_take_le' _ _) hr0, by simp; omega⟩

private theorem prostMergeUint32_length_le (wt : WireType) (bs : Bytes)
    {v : BitVec 32} {rest : Bytes}
    (h : mergeUint32 wt bs = some (v, rest)) :
    rest.length ≤ bs.length := by
  unfold mergeUint32 at h
  split at h
  · cases h
  · cases hd : decodeVarint bs with
    | none => rw [hd] at h; cases h
    | some vr =>
      rcases vr with ⟨v0, r0⟩
      rw [hd] at h
      dsimp only at h
      injection h with hp
      injection hp with _ hr
      subst hr
      exact prostDecodeVarint_length_le bs hd

private def ProtoSignalFieldsLe (N : ℕ) (p : ProtoSignalMessage) : Prop :=
  (∀ v ∈ p.ciphertext, v.length ≤ N) ∧
  (∀ v ∈ p.pqRatchet, v.length ≤ N) ∧
  (∀ v ∈ p.addresses, v.length ≤ N)

private theorem prostMergeField_preserves {N : ℕ} {p p' : ProtoSignalMessage}
    {tag : ℕ} {wt : WireType} {bs rest : Bytes}
    (hp : ProtoSignalFieldsLe N p) (hbs : bs.length ≤ N)
    (h : mergeField p tag wt bs = some (p', rest)) :
    ProtoSignalFieldsLe N p' ∧ rest.length ≤ bs.length := by
  unfold mergeField at h
  match tag with
  | 1 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq; subst hp_eq hr_eq
    exact ⟨hp, (prostMergeBytes_length_le wt bs hm).2⟩
  | 2 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
    injection hp' with hp_eq hr_eq; subst hp_eq hr_eq
    exact ⟨hp, prostMergeUint32_length_le wt bs hm⟩
  | 3 =>
    rcases Option.mem_map.mp h with ⟨⟨v, r⟩, hm, hp'⟩
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

private theorem prostDecodeLoop_preserves (fuel N : ℕ) (p : ProtoSignalMessage) (bs : Bytes)
    {p' : ProtoSignalMessage}
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

theorem atomicPureOps_signalMsgParse_lossless (ℓ : ℕ) (Pt : Type) (body : Bytes) :
    AtomicPureOp.eval ℓ Pt .signalMsgParse body =
      match SignalMessage.tryFrom protoSignalCodec body with
      | .ok m =>
        some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
              (m.ciphertext, (m.pqRatchet, m.addresses)))
      | .error _ => none := by
  dsimp only [AtomicPureOp.eval]
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
                      have hbuf : ((body.take (body.length - macLength)).drop 1).length ≤ body.length := by
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

theorem atomicSymOps_aes256CbcEnc_lossless (ℓ : ℕ) (Pt : Type) (C : Crypto)
    (k : BitVec 256) (iv : Block) (pt : Plain ℓ) :
    AtomicSymOp.eval ℓ Pt C .aes256CbcEnc (k, (iv, pt)) =
      aesCbcEncrypt C.E k iv pt.toList := by
  dsimp only [AtomicSymOp.eval]
  have hlen := aesCbcEncrypt_length_eq C.E k iv pt
  exact List.take_of_length_le (by omega)

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

private theorem prostEncodeBytesField_length_le (tag : ℕ) (opt : Option Bytes) (N : ℕ)
    (h : ∀ b ∈ opt, b.length ≤ N) :
    (encodeBytesField tag opt).length ≤ 20 + N := by
  cases opt with
  | none => simp [encodeBytesField]
  | some b =>
    simp only [encodeBytesField, List.length_append]
    have h1 := prostEncodeVarintAux_length_le 10 (BitVec.ofNat 64 (tag * 8 + WireType.lengthDelimited.toNat))
    have h2 := prostEncodeVarintAux_length_le 10 (BitVec.ofNat 64 b.length)
    have h3 := h b rfl
    unfold encodeKey encodeVarint; omega

private theorem prostEncodeUint32Field_length_le (tag : ℕ) (opt : Option (BitVec 32)) :
    (encodeUint32Field tag opt).length ≤ 20 := by
  cases opt with
  | none => simp [encodeUint32Field]
  | some v =>
    simp only [encodeUint32Field, List.length_append]
    have h1 := prostEncodeVarintAux_length_le 10 (BitVec.ofNat 64 (tag * 8 + WireType.varint.toNat))
    have h2 := prostEncodeVarintAux_length_le 10 (v.zeroExtend 64)
    unfold encodeKey encodeVarint; omega

theorem signalMsgNew_serialized_length_le {ℓ : ℕ} (F : ShaCompress)
    (msgVer : BitVec 8) (macKey : BitVec 256) (addr? : Option Bytes) (senderRk : PublicKey)
    (ctr prevCtr : BitVec 32) (ct : Bytes) (idS idR : IdentityKey) (pqMsg : Bytes)
    (hct : ct.length ≤ 32 * (ℓ / 32 + 2))
    (hpq : pqMsg.length ≤ 96)
    (haddr : ∀ a ∈ addr?, a.length ≤ 128) :
    (SignalMessage.new F protoSignalCodec msgVer macKey addr? senderRk ctr prevCtr ct
      idS idR pqMsg).serialized.length ≤ 32 * (ℓ / 32) + 450 := by
  have hmac : (hmacSha256Trunc8 F (keyToBytes32 macKey)
      ((CryptoGames.LibsignalSession.macIds idS idR).toList ++
        serializeContent protoSignalCodec msgVer senderRk ctr prevCtr ct pqMsg addr?)).length ≤ 8 :=
    List.length_take_le 8 _
  dsimp only [SignalMessage.new, computeMac]
  rw [List.length_append]
  have hser : (serializeContent protoSignalCodec msgVer senderRk ctr prevCtr ct pqMsg addr?).length ≤
      32 * (ℓ / 32) + 442 := by
    dsimp only [serializeContent, protoSignalCodec, encode]
    simp only [List.length_cons, List.length_append]
    have f1 := prostEncodeBytesField_length_le 1 (some senderRk.serialize) 33
      (fun b hb => by simp only [Option.mem_def, Option.some.injEq] at hb; subst hb; rw [publicKey_serialize_length])
    have f2 := prostEncodeUint32Field_length_le 2 (some ctr)
    have f3 := prostEncodeUint32Field_length_le 3 (some prevCtr)
    have f4 := prostEncodeBytesField_length_le 4 (some ct) (32 * (ℓ / 32 + 2))
      (fun b hb => by simp only [Option.mem_def, Option.some.injEq] at hb; subst hb; exact hct)
    have f5 := prostEncodeBytesField_length_le 5 (if pqMsg.isEmpty then none else some pqMsg) 96
      (fun b hb => by
        split at hb
        · cases hb
        · simp only [Option.mem_def, Option.some.injEq] at hb; subst hb; exact hpq)
    have f6 := prostEncodeBytesField_length_le 6 addr? 128 haddr
    omega
  omega

theorem atomicSymOps_signalMsgEncode_lossless (ℓ : ℕ) (Pt : Type) (C : Crypto)
    (msgVer : BitVec 8) (senderRk : PublicKey) (ctr prevCtr : BitVec 32)
    (ct pqMsg : Bytes) (addr? : Option Bytes) (idS idR : IdentityKey) (macKey : BitVec 256)
    (hct : ct.length ≤ 32 * (ℓ / 32 + 2))
    (hpq : pqMsg.length ≤ 96)
    (haddr : ∀ a ∈ addr?, a.length ≤ 128) :
    AtomicSymOp.eval ℓ Pt C .signalMsgEncode
      ((msgVer, (senderRk, (ctr, prevCtr))), (ct, (pqMsg, (addr?, (idS, (idR, macKey)))))) =
      (SignalMessage.new C.F protoSignalCodec msgVer macKey addr? senderRk ctr prevCtr ct
        idS idR pqMsg).serialized := by
  dsimp only [AtomicSymOp.eval]
  have hlen := signalMsgNew_serialized_length_le C.F msgVer macKey addr? senderRk ctr prevCtr
    ct idS idR pqMsg hct hpq haddr
  exact List.take_of_length_le (by omega)

private theorem flatMap_toBEBytes4_length :
    ∀ l : List (BitVec 32), (l.flatMap (toBEBytes 4)).length = 4 * l.length
  | [] => rfl
  | _ :: ws => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, toBEBytes, List.length_ofFn,
      flatMap_toBEBytes4_length ws]
    omega

@[simp] theorem hmacWith_length (F : ShaCompress) (k m : Bytes) :
    (hmacWith F k m).length = 32 := by
  unfold hmacWith CryptoGames.HMAC.sha256With
  rw [flatMap_toBEBytes4_length, List.Vector.toList_length]

theorem computeMac_length (F : ShaCompress) (idS idR : IdentityKey) (macKey : BitVec 256)
    (msg : Bytes) :
    (computeMac F idS idR macKey msg).length = 8 := by
  simp [computeMac, hmacSha256Trunc8]

/-! ## `CoinSimEquiv` and atomic uniform samplers -/

section CoinSim

open scoped ENNReal
open Computational.Proofs.GameHop.Rnd (equivBitVecSplit evalDistEq_uniformSample_equiv
  evalDistEq_uniformSample_pair_of_bijective evalDistEq_uniformSample_prod
  evalDistEq_marginal_fst_of_bijective evalDistEq_marginal_snd_of_bijective)

/-- Stateful simulator `impl` interpreting `fwdU` as fresh uniform coins in `ProbComp`. -/
structure ValidCoinSim {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {σ : Type} (impl : QueryImpl T (StateT σ ProbComp)) : Prop where
  coin_eq : ∀ (n : ℕ) (s : σ),
    (simulateQ impl (fwdU n)).run s =ᵈ
      ((query (m := ProbComp) (spec := unifSpec) n) >>= fun u => pure (u, s))

/-- Distributional equivalence under every `ValidCoinSim fwdU` simulator. -/
structure CoinSimEquiv {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α : Type} (oa₁ oa₂ : OracleComp T α) : Prop where
  run_eq : ∀ {σ : Type} (impl : QueryImpl T (StateT σ ProbComp)),
    ValidCoinSim fwdU impl →
    ∀ (s : σ), (simulateQ impl oa₁).run s =ᵈ (simulateQ impl oa₂).run s

namespace CoinSimEquiv

variable {ι : Type} {T : OracleSpec.{0, 0} ι} {fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))}

theorem refl {α : Type} (oa : OracleComp T α) : CoinSimEquiv fwdU oa oa :=
  ⟨fun _ _ _ => EvalDistEq.rfl⟩

theorem of_eq {α : Type} {oa₁ oa₂ : OracleComp T α} (h : oa₁ = oa₂) :
    CoinSimEquiv fwdU oa₁ oa₂ :=
  h ▸ refl oa₁

theorem symm {α : Type} {oa₁ oa₂ : OracleComp T α} (h : CoinSimEquiv fwdU oa₁ oa₂) :
    CoinSimEquiv fwdU oa₂ oa₁ :=
  ⟨fun impl himpl s => (h.run_eq impl himpl s).symm⟩

theorem trans {α : Type} {oa₁ oa₂ oa₃ : OracleComp T α}
    (h₁ : CoinSimEquiv fwdU oa₁ oa₂) (h₂ : CoinSimEquiv fwdU oa₂ oa₃) :
    CoinSimEquiv fwdU oa₁ oa₃ :=
  ⟨fun impl himpl s => (h₁.run_eq impl himpl s).trans (h₂.run_eq impl himpl s)⟩

theorem bind {α β : Type} {oa₁ oa₂ : OracleComp T α} {k₁ k₂ : α → OracleComp T β}
    (hoa : CoinSimEquiv fwdU oa₁ oa₂)
    (hk : ∀ a, CoinSimEquiv fwdU (k₁ a) (k₂ a)) :
    CoinSimEquiv fwdU (oa₁ >>= k₁) (oa₂ >>= k₂) := ⟨by
  intro σ impl himpl s
  simp only [simulateQ_bind, StateT.run_bind]
  exact (hoa.run_eq impl himpl s).bind fun p => (hk p.1).run_eq impl himpl p.2⟩

theorem map {α β : Type} (f : α → β) {oa₁ oa₂ : OracleComp T α}
    (h : CoinSimEquiv fwdU oa₁ oa₂) :
    CoinSimEquiv fwdU (f <$> oa₁) (f <$> oa₂) := by
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  exact h.bind fun a => refl (pure (f a))

theorem iterM_congr {α : Type} {f₁ f₂ : α → OracleComp T α}
    (hf : ∀ a, CoinSimEquiv fwdU (f₁ a) (f₂ a)) :
    ∀ (n : ℕ) (a : α), CoinSimEquiv fwdU (iterM f₁ n a) (iterM f₂ n a)
  | 0, a => refl (pure a)
  | n + 1, a => (hf a).bind (iterM_congr hf n)

theorem findML_congr {α : Type} {p₁ p₂ : α → OracleComp T Bool}
    (hp : ∀ a, CoinSimEquiv fwdU (p₁ a) (p₂ a)) :
    ∀ (xs : List α), CoinSimEquiv fwdU (findML p₁ xs) (findML p₂ xs)
  | [] => refl (pure none)
  | x :: xs =>
    (hp x).bind fun b => by
      cases b
      · exact findML_congr hp xs
      · exact refl (pure (some x))

theorem anyML_congr {α : Type} {p₁ p₂ : α → OracleComp T Bool}
    (hp : ∀ a, CoinSimEquiv fwdU (p₁ a) (p₂ a)) :
    ∀ (xs : List α), CoinSimEquiv fwdU (anyML p₁ xs) (anyML p₂ xs)
  | [] => refl (pure false)
  | x :: xs =>
    (hp x).bind fun b => by
      cases b
      · exact anyML_congr hp xs
      · exact refl (pure true)

theorem mapML_congr {α β : Type} {f₁ f₂ : α → OracleComp T β}
    (hf : ∀ a, CoinSimEquiv fwdU (f₁ a) (f₂ a)) :
    ∀ (xs : List α), CoinSimEquiv fwdU (mapML f₁ xs) (mapML f₂ xs)
  | [] => refl (pure [])
  | x :: xs => (hf x).bind fun y => (mapML_congr hf xs).bind fun ys => refl (pure (y :: ys))

theorem consumeFirstML_congr {α : Type} {p₁ p₂ : α → OracleComp T Bool} (mk : α → α)
    (hp : ∀ a, CoinSimEquiv fwdU (p₁ a) (p₂ a)) :
    ∀ (xs : List α),
      CoinSimEquiv fwdU (consumeFirstML p₁ mk xs)
        (consumeFirstML p₂ mk xs)
  | [] => refl (pure (false, []))
  | x :: xs =>
    (hp x).bind fun b => by
      cases b
      · exact (consumeFirstML_congr mk hp xs).bind fun r => refl (pure (r.1, x :: r.2))
      · exact refl (pure (true, mk x :: xs))

theorem foldML_congr {α β : Type} {f₁ f₂ : α → β → OracleComp T β}
    (hf : ∀ a b, CoinSimEquiv fwdU (f₁ a b) (f₂ a b)) :
    ∀ (xs : List α) (b : β),
      CoinSimEquiv fwdU (foldML f₁ b xs) (foldML f₂ b xs)
  | [], b => refl (pure b)
  | x :: xs, b => (hf x b).bind (foldML_congr hf xs)

end CoinSimEquiv

theorem evalDistEq_simulateQ_liftP {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {σ : Type} (impl : QueryImpl T (StateT σ ProbComp))
    (himpl : ValidCoinSim I.fwdU impl) {α : Type} (p : ProbComp α) :
    ∀ (s : σ), (simulateQ impl (I.liftP p)).run s =ᵈ (p >>= fun a => pure (a, s)) := by
  induction p using OracleComp.inductionOn with
  | pure a => intro s; simp [Iface.liftP]
  | query_bind n k ih =>
    intro s
    unfold Iface.liftP
    rw [simulateQ_query_bind, simulateQ_bind, StateT.run_bind]
    change (simulateQ impl (I.fwdU n)).run s >>=
        (fun z => (simulateQ impl (I.liftP (k z.1))).run z.2) =ᵈ _
    refine ((himpl.coin_eq n s).bind fun z => ih z.1 z.2).trans ?_
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.rfl

theorem coinSimEquiv_liftP {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι}
    (I : Iface S T) {α : Type} {p₁ p₂ : ProbComp α} (h : p₁ =ᵈ p₂) :
    CoinSimEquiv I.fwdU (I.liftP p₁) (I.liftP p₂) := ⟨by
  intro σ impl himpl s
  exact (evalDistEq_simulateQ_liftP I impl himpl p₁ s).trans
    ((h.bind fun _ => EvalDistEq.rfl).trans
      (evalDistEq_simulateQ_liftP I impl himpl p₂ s).symm)⟩

@[expose] def compCoinImpl {κ ι : Type} {G : OracleSpec.{0, 0} κ} {T : OracleSpec.{0, 0} ι}
    {σ₁ σ₂ : Type}
    (h : QueryImpl G (StateT σ₁ (OracleComp T)))
    (impl : QueryImpl T (StateT σ₂ ProbComp)) :
    QueryImpl G (StateT (σ₁ × σ₂) ProbComp) := fun q =>
  StateT.mk fun s => do
    let z ← (simulateQ impl ((h q).run s.1)).run s.2
    pure (z.1.1, (z.1.2, z.2))

theorem simulateQ_compCoinImpl_run {κ ι : Type} {G : OracleSpec.{0, 0} κ}
    {T : OracleSpec.{0, 0} ι} {σ₁ σ₂ α : Type}
    (h : QueryImpl G (StateT σ₁ (OracleComp T)))
    (impl : QueryImpl T (StateT σ₂ ProbComp))
    (oa : OracleComp G α) :
    ∀ (s₁ : σ₁) (s₂ : σ₂),
      (simulateQ impl ((simulateQ h oa).run s₁)).run s₂ =
        (fun p : α × (σ₁ × σ₂) => ((p.1, p.2.1), p.2.2)) <$>
          (simulateQ (compCoinImpl h impl) oa).run (s₁, s₂) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s₁ s₂; simp
  | query_bind q k ih =>
    intro s₁ s₂
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_query_bind, StateT.run_bind, map_bind]
    change (do
      let z ← (simulateQ impl ((h q).run s₁)).run s₂
      (simulateQ impl ((simulateQ h (k z.1.1)).run z.1.2)).run z.2) =
      (do
        let w ← (do
          let z ← (simulateQ impl ((h q).run s₁)).run s₂
          pure (z.1.1, (z.1.2, z.2)))
        (fun p : α × (σ₁ × σ₂) => ((p.1, p.2.1), p.2.2)) <$>
          (simulateQ (compCoinImpl h impl) (k w.1)).run w.2)
    rw [bind_assoc]
    refine bind_congr fun z => ?_
    rw [pure_bind]
    exact ih z.1.1 z.1.2 z.2

theorem validCoinSim_compCoinImpl {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec.{0, 0} ι} {I : Iface S T} {G : OracleSpec.{0, 0} κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out)
    {σ₂ : Type} {impl : QueryImpl T (StateT σ₂ ProbComp)}
    (himpl : ValidCoinSim I.fwdU impl) :
    ValidCoinSim (fun n => query (spec := unifSpec + G) (.inl n)) (compCoinImpl R.impl impl) := ⟨by
  intro n ⟨s₁, s₂⟩
  rw [simulateQ_HasQuery_query]
  change (do
    let z ← (simulateQ impl (I.fwdU n >>= fun x => pure (x, s₁))).run s₂
    pure (z.1.1, (z.1.2, z.2))) =ᵈ
    ((query (m := ProbComp) (spec := unifSpec) n) >>= fun u => pure (u, (s₁, s₂)))
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    bind_assoc, pure_bind]
  have hb := (himpl.coin_eq n s₂).bind
    (f := fun z : Fin (n + 1) × σ₂ => (pure (z.1, (s₁, z.2)) : ProbComp _))
    (g := fun z : Fin (n + 1) × σ₂ => (pure (z.1, (s₁, z.2)) : ProbComp _))
    (fun _ => EvalDistEq.rfl)
  simpa only [bind_assoc, pure_bind] using hb⟩

theorem CostedReduction.eval_coinSimEquiv_congr {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec.{0, 0} ι} {I : Iface S T} {G : OracleSpec.{0, 0} κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out)
    {adv₁ adv₂ : aIn.denote → OracleComp (unifSpec + G) aOut.denote}
    (hA : ∀ a, CoinSimEquiv (fun n => query (spec := unifSpec + G) (.inl n)) (adv₁ a) (adv₂ a))
    (x : rIn.denote) :
    CoinSimEquiv I.fwdU (R.eval adv₁ x) (R.eval adv₂ x) := ⟨by
  intro σ₂ impl himpl s₂
  unfold CostedReduction.eval
  simp only [simulateQ_bind, StateT.run_bind]
  refine EvalDistEq.rfl.bind fun p0 => ?_
  rcases p0 with ⟨⟨a, s₁⟩, s₂'⟩
  rw [simulateQ_compCoinImpl_run, simulateQ_compCoinImpl_run]
  simp only [bind_map_left]
  exact ((hA a).run_eq (compCoinImpl R.impl impl)
    (validCoinSim_compCoinImpl R himpl) (s₁, s₂')).bind fun _ => EvalDistEq.rfl⟩

private def idCoinImpl : QueryImpl unifSpec (StateT Unit ProbComp) :=
  fun n => StateT.lift (query (m := ProbComp) (spec := unifSpec) n)

private theorem simulateQ_idCoinImpl_run {α : Type} (oa : ProbComp α) :
    (simulateQ idCoinImpl oa).run () = (·, ()) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [simulateQ_query_bind, StateT.run_bind, map_bind]
    change (do
      let p ← (do let u ← query (m := ProbComp) (spec := unifSpec) n; pure (u, ()))
      (simulateQ idCoinImpl (k p.1)).run p.2) =
      (do
        let u ← query (m := ProbComp) (spec := unifSpec) n
        (·, ()) <$> k u)
    rw [bind_assoc]
    refine bind_congr fun u => ?_
    rw [pure_bind]
    exact ih u

theorem CoinSimEquiv.evalDistEq_unifSpec {α : Type} {oa₁ oa₂ : ProbComp α}
    (h : CoinSimEquiv (fun n => query (spec := unifSpec) n) oa₁ oa₂) :
    oa₁ =ᵈ oa₂ := by
  have hv : ValidCoinSim (fun n => query (spec := unifSpec) n) idCoinImpl := ⟨fun n s => by
    cases s
    rw [simulateQ_HasQuery_query]
    dsimp only [idCoinImpl, StateT.lift, StateT.run]
    exact EvalDistEq.rfl⟩
  have hrun := (h.run_eq idCoinImpl hv ()).map Prod.fst
  rw [simulateQ_idCoinImpl_run, simulateQ_idCoinImpl_run, Functor.map_map, Functor.map_map] at hrun
  change id <$> oa₁ =ᵈ id <$> oa₂ at hrun
  simpa only [id_map] using hrun

theorem validCoinSim_challengerImpl {κ σ : Type} {H : OracleSpec.{0, 0} κ}
    (hOracle : QueryImpl H (StateT σ ProbComp)) :
    ValidCoinSim (fun n => query (spec := unifSpec + H) (.inl n))
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hOracle) := ⟨by
  intro n s
  rw [simulateQ_HasQuery_query, QueryImpl.add_apply_inl]
  dsimp only [QueryImpl.liftTarget, QueryImpl.ofLift, StateT.lift, StateT.run]
  exact EvalDistEq.rfl⟩

theorem prgAdvantage_congr {Seed R : Type} [SampleableType Seed] [SampleableType R]
    (prg : PRGScheme Seed R) {adv₁ adv₂ : PRGScheme.PRGAdversary R}
    (h : ∀ r, adv₁ r =ᵈ adv₂ r) :
    prg.prgAdvantage adv₁ = prg.prgAdvantage adv₂ := by
  unfold PRGScheme.prgAdvantage PRGScheme.prgRealExperiment PRGScheme.prgIdealExperiment
  rw [(EvalDistEq.rfl.bind fun s => h (prg.gen s)).evalDist_eq,
    (EvalDistEq.rfl.bind h).evalDist_eq]

theorem prfAdvantage_congr {Key Input Tag : Type} [DecidableEq Input]
    [SampleableType Key] [SampleableType Tag]
    (mac : MACScheme Key Input Tag) {adv₁ adv₂ : MACScheme.PRFAdversary Input Tag}
    (h : CoinSimEquiv (fun n => query (spec := unifSpec + MACScheme.prfSpec Input Tag) (.inl n))
      adv₁ adv₂) :
    mac.prfAdvantage adv₁ = mac.prfAdvantage adv₂ := by
  unfold MACScheme.prfAdvantage
  have hg : mac.prfGame adv₁ =ᵈ mac.prfGame adv₂ := by
    unfold MACScheme.prfGame
    refine EvalDistEq.rfl.bind fun b => EvalDistEq.rfl.bind fun key => ?_
    simp only [StateT.run']
    exact ((h.run_eq _ (validCoinSim_challengerImpl _)
      ({ key := key, b := b } : MACScheme.PRFState Key Input Tag)).map Prod.fst).bind
      fun _ => EvalDistEq.rfl
  rw [hg.evalDist_eq]

theorem wireOtccaAdvantage_congr {K AD H M M' C T : Type}
    [SampleableType K] [SampleableType C] [SampleableType T] [DecidableEq AD] [DecidableEq T]
    (ae : WireAEAD K AD H M M' C T) {adv₁ adv₂ : WireAEAD.WireAdversary AD H M M' T}
    (h : CoinSimEquiv (fun n => query (spec := unifSpec + WireAEAD.wireSpec AD H M M' T) (.inl n))
      adv₁ adv₂) :
    ae.wireOtccaAdvantage adv₁ = ae.wireOtccaAdvantage adv₂ := by
  unfold WireAEAD.wireOtccaAdvantage
  have hg : ae.wireOtccaGame adv₁ =ᵈ ae.wireOtccaGame adv₂ := by
    unfold WireAEAD.wireOtccaGame
    refine EvalDistEq.rfl.bind fun b => EvalDistEq.rfl.bind fun key => ?_
    simp only [StateT.run']
    exact ((h.run_eq _ (validCoinSim_challengerImpl _)
      ({ key := key, b := b } : WireAEAD.WireState K AD T)).map Prod.fst).bind
      fun _ => EvalDistEq.rfl
  rw [hg.evalDist_eq]

theorem otccaAdvantage_congr {Key AD M C : Type}
    [DecidableEq AD] [DecidableEq C] [SampleableType Key] [SampleableType C]
    (ae : AEADScheme Key AD M C) {adv₁ adv₂ : AEADScheme.OTCCAAdversary AD M C}
    (h : CoinSimEquiv (fun n => query (spec := unifSpec + AEADScheme.otccaSpec AD M C) (.inl n))
      adv₁ adv₂) :
    ae.otccaAdvantage adv₁ = ae.otccaAdvantage adv₂ := by
  unfold AEADScheme.otccaAdvantage
  have hg : ae.otccaGame adv₁ =ᵈ ae.otccaGame adv₂ := by
    unfold AEADScheme.otccaGame
    refine EvalDistEq.rfl.bind fun b => EvalDistEq.rfl.bind fun key => ?_
    simp only [StateT.run']
    exact ((h.run_eq _ (validCoinSim_challengerImpl _)
      ({ key := key, b := b } : AEADScheme.OTCCAState Key AD C)).map Prod.fst).bind
      fun _ => EvalDistEq.rfl
  rw [hg.evalDist_eq]

theorem sample_derivedMsgKeys_evalDistEq :
    (do
      let ck ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      let iv ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
      let mk ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
      pure ((ck, iv), mk)) =ᵈ ($ᵗ DerivedMessageKeys : ProbComp DerivedMessageKeys) := by
  refine EvalDistEq.symm ?_
  refine (evalDistEq_uniformSample_prod (α := BitVec 256 × BitVec 128) (β := BitVec 256)).trans ?_
  refine ((evalDistEq_uniformSample_prod (α := BitVec 256) (β := BitVec 128)).bind
    fun _ => EvalDistEq.rfl).trans ?_
  simp only [bind_assoc, pure_bind]
  rfl

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
      simpa [bytesToWordLE] using
        extractLsb'_zero_bytesToWordLE64_cons b (bytesToWordLE 64 rest)
    | succ j =>
      have hcons : bytesToWordLE 64 (b :: rest) =
          (bytesToWordLE 64 rest <<< 8) ||| b.zeroExtend 64 := rfl
      rw [hcons, extractLsb'_succ_bytesToWordLE64_cons b (bytesToWordLE 64 rest) j h8,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem bytesToWordLE_64_toLEBytes_16_take_8 (x : BitVec 128) :
    bytesToWordLE 64 ((toLEBytes 16 x).take 8) = x.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hj : i / 8 < 8 := by omega
  have hr : i % 8 < 8 := by omega
  have hlen : i / 8 < ((toLEBytes 16 x).take 8).length := by simp [toLEBytes, hj]
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToWordLE64 ((toLEBytes 16 x).take 8) (i / 8) hlen hj)
  simp only [toLEBytes, List.getElem_take, List.getElem_ofFn, BitVec.getLsbD_extractLsb',
    hr, hi, Nat.zero_add, decide_true, Bool.true_and, Nat.div_add_mod] at hbyte ⊢
  exact hbyte

theorem sample_u64_of_bv128_evalDistEq :
    (do
      let x ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
      pure (bytesToWordLE 64 ((toLEBytes 16 x).take 8))) =ᵈ
      ($ᵗ (BitVec 64) : ProbComp (BitVec 64)) := by
  simp only [bytesToWordLE_64_toLEBytes_16_take_8]
  have hm := evalDistEq_marginal_snd_of_bijective (equivBitVecSplit 64 64).bijective
  rw [map_eq_bind_pure_comp] at hm
  exact hm

private def equivBitVec1Bool : BitVec 1 ≃ Bool where
  toFun v := v == 1#1
  invFun b := if b then 1#1 else 0#1
  left_inv v := by
    rcases v with ⟨⟨_ | ⟨_ | _⟩, hv⟩⟩
    · rfl
    · rfl
    · omega
  right_inv b := by cases b <;> rfl

theorem sample_bool_of_bv128_evalDistEq :
    (do
      let x ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
      pure (decide ((bytesToWordLE 64 ((toLEBytes 16 x).take 8)).toNat % 2 = 1))) =ᵈ
      ($ᵗ Bool : ProbComp Bool) := by
  let fBool : BitVec 64 → ProbComp Bool := fun u => pure (decide (u.toNat % 2 = 1))
  have hstep :
      (do
        let x ← ($ᵗ (BitVec 128) : ProbComp (BitVec 128))
        pure (decide ((bytesToWordLE 64 ((toLEBytes 16 x).take 8)).toNat % 2 = 1))) =ᵈ
      (($ᵗ (BitVec 64) : ProbComp (BitVec 64)) >>= fBool) := by
    have hb := sample_u64_of_bv128_evalDistEq.bind (f := fBool) (g := fBool)
      fun _ => EvalDistEq.rfl
    simpa only [fBool, bind_assoc, pure_bind] using hb
  refine hstep.trans ?_
  have hbit : ∀ u : BitVec 64,
      decide (u.toNat % 2 = 1) = equivBitVec1Bool (u.extractLsb' 0 1) := by
    intro u
    change decide (u.toNat % 2 = 1) = (u.extractLsb' 0 1 == 1#1)
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff, beq_iff_eq, ← BitVec.toNat_inj]
    dsimp only [BitVec.extractLsb']
    simp [BitVec.toNat_ofNat]
  dsimp only [fBool]
  simp only [hbit]
  have hm := (evalDistEq_marginal_snd_of_bijective (equivBitVecSplit 63 1).bijective).map
    equivBitVec1Bool
  rw [Functor.map_map, map_eq_bind_pure_comp] at hm
  exact hm.trans (evalDistEq_uniformSample_equiv equivBitVec1Bool)

private def equivVectorCons (α : Type) (n : ℕ) :
    α × List.Vector α n ≃ List.Vector α (n + 1) where
  toFun p := p.1 ::ᵥ p.2
  invFun v := (v.head, v.tail)
  left_inv := fun ⟨_, _⟩ => by simp
  right_inv v := v.cons_head_tail

theorem sample_blocks_iter_evalDistEq (n : ℕ) :
    ∀ (init : Bytes),
      iterM
        (fun acc : Bytes => do
          let b ← ($ᵗ Block : ProbComp Block)
          pure (acc ++ (toLEBytes 16 b).take 16))
        n init =ᵈ
      ((fun v : List.Vector Block n => init ++ v.toList.flatMap blockToBytesLE) <$>
        ($ᵗ (List.Vector Block n) : ProbComp (List.Vector Block n))) := by
  induction n with
  | zero =>
    intro init
    have hconst : (fun v : List.Vector Block 0 => init ++ v.toList.flatMap blockToBytesLE) =
        fun _ => init := by
      funext v; rw [List.Vector.eq_nil v]; simp
    rw [hconst]
    refine EvalDistEq.of_forall_prEvent_eq fun p => ?_
    by_cases hp : p init <;> simp [iterM, hp]
  | succ n ih =>
    intro init
    have htake : ∀ b : Block, (toLEBytes 16 b).take 16 = blockToBytesLE b := fun b => by
      rw [List.take_of_length_le (by simp [toLEBytes])]; rfl
    dsimp only [iterM]
    simp only [bind_assoc, pure_bind, htake]
    refine (EvalDistEq.rfl.bind fun b => ih (init ++ blockToBytesLE b)).trans ?_
    simp only [map_eq_bind_pure_comp, Function.comp_def, List.append_assoc]
    have hcons :
        (do
          let b ← ($ᵗ Block : ProbComp Block)
          let v ← ($ᵗ (List.Vector Block n) : ProbComp (List.Vector Block n))
          pure (equivVectorCons Block n (b, v))) =ᵈ
        ($ᵗ (List.Vector Block (n + 1)) : ProbComp (List.Vector Block (n + 1))) :=
      evalDistEq_uniformSample_pair_of_bijective
        (g := fun b v => equivVectorCons Block n (b, v))
        (equivVectorCons Block n).bijective
    have hm := hcons.bind fun w =>
      (EvalDistEq.rfl : (pure (init ++ w.toList.flatMap blockToBytesLE) : ProbComp _) =ᵈ _)
    simp only [bind_assoc, pure_bind] at hm
    exact hm

end CoinSim

/-! ## `PureMacroBundle` compiler -/


section PureMacro

open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal)

@[expose, reducible] def compWkTop1 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a t : Ty S} (c : Comp O I [a] t) : Comp O I (a :: Γ) t :=
  Comp.renameM (fun ⦃_⦄ v => match v with | .zero => .zero | .succ w => nomatch w) c

theorem compWkTop1_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a t : Ty S} (c : Comp O I [a] t) (x : a.denote) (ρ : Env Γ) :
    (compWkTop1 c).eval (.cons x ρ) = c.eval (.cons x .nil) :=
  Comp.renameM_eval c fun ⦃_⦄ v => by cases v with | zero => rfl | succ w => nomatch w

@[expose, reducible] def mapPureCtx {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) : List (Ty S₁) → List (Ty S₂)
  | [] => []
  | t :: Γ => mapTy f t :: mapPureCtx f Γ

@[expose] def mapPureVar {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} → Var Γ t → Var (mapPureCtx f Γ) (mapTy f t)
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (mapPureVar f v)

@[expose] def mapPureEnv {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂)
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) :
    {Γ : List (Ty S₁)} → Env Γ → Env (mapPureCtx f Γ)
  | _, .nil => .nil
  | _, .cons x ρ => .cons (toVal f toDen _ x) (mapPureEnv f toDen ρ)

theorem get_mapPureEnv {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂)
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote)
    {Γ : List (Ty S₁)} {t : Ty S₁} (ρ : Env Γ) (v : Var Γ t) :
    (mapPureEnv f toDen ρ).get (mapPureVar f v) = toVal f toDen t (ρ.get v) := by
  induction v with
  | zero => cases ρ; rfl
  | succ v ih => cases ρ with | cons _ ρ => exact ih ρ

/-- Macro bundle translating pure `O₁` operators and `I₁` samples/queries into `O₂` and `I₂`. -/
structure PureMacroBundle {S₁ S₂ : Sig} (O₁ : Ops S₁) (O₂ : Ops S₂)
    {ι : Type} {T : OracleSpec.{0, 0} ι} (I₁ : Iface S₁ T) (I₂ : Iface S₂ T) where
  baseTy : S₁.Base → Ty S₂
  toDen : (b : S₁.Base) → S₁.den b → (baseTy b).denote
  opMacro : (o : O₁.Op) → Expr O₂ [mapTy baseTy (O₁.dom o)] (mapTy baseTy (O₁.cod o))
  sampMacro : (s : I₁.smp.Samp) →
    Comp O₂ I₂ [mapTy baseTy (I₁.smp.sDom s)] (mapTy baseTy (I₁.smp.sTy s))
  queryMacro : (g : I₁.Tag) →
    Comp O₂ I₂ [mapTy baseTy (I₁.dom g)] (mapTy baseTy (I₁.cod g))

@[expose] def compilePureExpr {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Expr O₁ Γ t → Expr O₂ (mapPureCtx M.baseTy Γ) (mapTy M.baseTy t)
  | _, _, .var v => .var (mapPureVar M.baseTy v)
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
  | _, _, .op o a => .letE (compilePureExpr M a) (Expr.wkTop1 (M.opMacro o))
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
  | _, _, .tset m i a => .tset (compilePureExpr M m) (compilePureExpr M i) (compilePureExpr M a)

@[expose] def compilePureComp {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Comp O₁ I₁ Γ t → Comp O₂ I₂ (mapPureCtx M.baseTy Γ) (mapTy M.baseTy t)
  | _, _, .ret e => .ret (compilePureExpr M e)
  | _, _, .bind c k => .bind (compilePureComp M c) (compilePureComp M k)
  | _, _, .ite b c d => .ite (compilePureExpr M b) (compilePureComp M c) (compilePureComp M d)
  | _, _, .caseOpt e n s =>
    .caseOpt (compilePureExpr M e) (compilePureComp M n) (compilePureComp M s)
  | _, _, .caseSum e l r =>
    .caseSum (compilePureExpr M e) (compilePureComp M l) (compilePureComp M r)
  | _, _, .sample s e => .bind (.ret (compilePureExpr M e)) (compWkTop1 (M.sampMacro s))
  | _, _, .query g e => .bind (.ret (compilePureExpr M e)) (compWkTop1 (M.queryMacro g))
  | _, _, .iter n e body => .iter n (compilePureExpr M e) (compilePureComp M body)
  | _, _, .findM K l p => .findM K (compilePureExpr M l) (compilePureComp M p)
  | _, _, .anyM K l p => .anyM K (compilePureExpr M l) (compilePureComp M p)
  | _, _, .mapM K l f => .mapM K (compilePureExpr M l) (compilePureComp M f)
  | _, _, .consumeFirstM K l p mk =>
    .consumeFirstM K (compilePureExpr M l) (compilePureComp M p) (compilePureExpr M mk)
  | _, _, .foldM K l z f =>
    .foldM K (compilePureExpr M l) (compilePureExpr M z) (compilePureComp M f)

@[expose] def exprCostBound {S : Sig} {O : Ops S} (opC : O.Op → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .none | _, _, .nil => 1
  | _, _, .nat n => bits n
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b
  | _, _, .and a b | _, _, .pair a b | _, _, .cons a b | _, _, .take a b
  | _, _, .letE a b => exprCostBound opC a + exprCostBound opC b + 1
  | _, _, .mulK k a | _, _, .divK k a | _, _, .modK k a => exprCostBound opC a + bits k
  | _, _, .not a | _, _, .fst a | _, _, .snd a | _, _, .inl a | _, _, .inr a
  | _, _, .some a | _, _, .len a | _, _, .tconst a => exprCostBound opC a + 1
  | _, _, .ite c a b | _, _, .caseOpt c a b | _, _, .caseSum c a b =>
    exprCostBound opC c + max (exprCostBound opC a) (exprCostBound opC b) + 1
  | _, _, .op o a => exprCostBound opC a + opC o
  | _, _, .appendL K a b => exprCostBound opC a + exprCostBound opC b + K + 1
  | _, _, .findB K l p | _, _, .anyB K l p | _, _, .mapB K l p =>
    exprCostBound opC l + K * (exprCostBound opC p + 1) + 1
  | _, _, .foldrB K l z f =>
    exprCostBound opC l + exprCostBound opC z + K * (exprCostBound opC f + 1) + 1
  | _, _, .tget m i => exprCostBound opC m + exprCostBound opC i + 64
  | _, _, .tset m i a => exprCostBound opC m + exprCostBound opC i + exprCostBound opC a + 128

@[expose] def compCostBound {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => exprCostBound opC e + 1
  | _, _, .bind c k => compCostBound opC sC qC c + compCostBound opC sC qC k + 1
  | _, _, .ite b c d | _, _, .caseOpt b c d | _, _, .caseSum b c d =>
    exprCostBound opC b + max (compCostBound opC sC qC c) (compCostBound opC sC qC d) + 1
  | _, _, .sample s e => exprCostBound opC e + sC s
  | _, _, .query g e => exprCostBound opC e + qC g
  | _, _, .iter n e body => exprCostBound opC e + n * (compCostBound opC sC qC body + 1) + 1
  | _, _, .findM K l p | _, _, .anyM K l p | _, _, .mapM K l p =>
    exprCostBound opC l + K * (compCostBound opC sC qC p + 1) + 1
  | _, _, .consumeFirstM K l p mk =>
    exprCostBound opC l + K * (compCostBound opC sC qC p + exprCostBound opC mk + 1) + 1
  | _, _, .foldM K l z f =>
    exprCostBound opC l + exprCostBound opC z + K * (compCostBound opC sC qC f + 1) + 1

theorem compilePureExpr_cost_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂) (opC : O₁.Op → ℕ)
    (hOp : ∀ o, (M.opMacro o).cost + 1 ≤ opC o)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compilePureExpr M e).cost ≤ exprCostBound opC e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ iha ihb | sub _ _ iha ihb | lt _ _ iha ihb | eqN _ _ iha ihb
  | and _ _ iha ihb | pair _ _ iha ihb | cons _ _ iha ihb | take _ _ iha ihb
  | letE _ _ iha ihb | appendL _ _ _ iha ihb | tget _ _ iha ihb =>
    simp only [compilePureExpr, Expr.cost, exprCostBound]; omega
  | mulK _ _ iha | divK _ _ iha | modK _ _ iha | not _ iha | fst _ iha | snd _ iha
  | inl _ iha | inr _ iha | some _ iha | len _ iha | tconst _ iha =>
    simp only [compilePureExpr, Expr.cost, exprCostBound]; omega
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb =>
    have hm := max_le_max iha ihb
    simp only [compilePureExpr, Expr.cost, exprCostBound]; omega
  | op o _ iha =>
    have ho := hOp o
    simp only [compilePureExpr, Expr.cost, Expr.wkTop1, Expr.renameM_cost, exprCostBound]; omega
  | findB K _ _ ihl ihp | anyB K _ _ ihl ihp | mapB K _ _ ihl ihp =>
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihp 1)
    simp only [compilePureExpr, Expr.cost, exprCostBound]; omega
  | foldrB K _ _ _ ihl ihz ihf =>
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihf 1)
    simp only [compilePureExpr, Expr.cost, exprCostBound]; omega
  | tset _ _ _ ihm ihi iha =>
    simp only [compilePureExpr, Expr.cost, exprCostBound]; omega

theorem compilePureComp_cost_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂)
    (opC : O₁.Op → ℕ) (sC : I₁.smp.Samp → ℕ) (qC : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).cost + 1 ≤ opC o)
    (hSamp : ∀ s, (M.sampMacro s).cost + 2 ≤ sC s)
    (hQuery : ∀ g, (M.queryMacro g).cost + 2 ≤ qC g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureComp M c).cost ≤ compCostBound opC sC qC c := by
  induction c with
  | ret e =>
    have he := compilePureExpr_cost_le M opC hOp e
    simp only [compilePureComp, Comp.cost, compCostBound]; omega
  | bind _ _ ihc ihk =>
    simp only [compilePureComp, Comp.cost, compCostBound]; omega
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := compilePureExpr_cost_le M opC hOp b
    have hm := max_le_max ihc ihd
    simp only [compilePureComp, Comp.cost, compCostBound]; omega
  | sample s e =>
    have he := compilePureExpr_cost_le M opC hOp e
    have hs := hSamp s
    simp only [compilePureComp, Comp.cost, compWkTop1, Comp.renameM_cost, compCostBound]; omega
  | query g e =>
    have he := compilePureExpr_cost_le M opC hOp e
    have hq := hQuery g
    simp only [compilePureComp, Comp.cost, compWkTop1, Comp.renameM_cost, compCostBound]; omega
  | iter n e _ ihb =>
    have he := compilePureExpr_cost_le M opC hOp e
    have hm := Nat.mul_le_mul_left n (Nat.add_le_add_right ihb 1)
    simp only [compilePureComp, Comp.cost, compCostBound]; omega
  | findM K l _ ihp | anyM K l _ ihp | mapM K l _ ihp =>
    have hl := compilePureExpr_cost_le M opC hOp l
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihp 1)
    simp only [compilePureComp, Comp.cost, compCostBound]; omega
  | consumeFirstM K l _ mk ihp =>
    have hl := compilePureExpr_cost_le M opC hOp l
    have hmk := compilePureExpr_cost_le M opC hOp mk
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right (Nat.add_le_add ihp hmk) 1)
    simp only [compilePureComp, Comp.cost, compCostBound]; omega
  | foldM K l z _ ihf =>
    have hl := compilePureExpr_cost_le M opC hOp l
    have hz := compilePureExpr_cost_le M opC hOp z
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihf 1)
    simp only [compilePureComp, Comp.cost, compCostBound]; omega

theorem compilePureExpr_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂) (S_max : ℕ) (hS : 1 ≤ S_max)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ S_max)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compilePureExpr M e).size ≤ S_max * e.size := by
  induction e with
  | var _ | unit | bool _ | none | nil =>
    simp only [compilePureExpr, Expr.size]; omega
  | nat n =>
    simp only [compilePureExpr, Expr.size]; nlinarith
  | add _ _ iha ihb | sub _ _ iha ihb | lt _ _ iha ihb | eqN _ _ iha ihb
  | and _ _ iha ihb | pair _ _ iha ihb | cons _ _ iha ihb | take _ _ iha ihb
  | letE _ _ iha ihb | appendL _ _ _ iha ihb | tget _ _ iha ihb =>
    simp only [compilePureExpr, Expr.size]; nlinarith
  | mulK _ _ iha | divK _ _ iha | modK _ _ iha | not _ iha | fst _ iha | snd _ iha
  | inl _ iha | inr _ iha | some _ iha | len _ iha | tconst _ iha =>
    simp only [compilePureExpr, Expr.size]; nlinarith
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb =>
    simp only [compilePureExpr, Expr.size]; nlinarith
  | op o _ iha =>
    have ho := hOp o
    simp only [compilePureExpr, Expr.size, Expr.wkTop1, Expr.renameM_size]; nlinarith
  | findB _ _ _ ihl ihp | anyB _ _ _ ihl ihp | mapB _ _ _ ihl ihp =>
    simp only [compilePureExpr, Expr.size]; nlinarith
  | foldrB _ _ _ _ ihl ihz ihf =>
    simp only [compilePureExpr, Expr.size]; nlinarith
  | tset _ _ _ ihm ihi iha =>
    simp only [compilePureExpr, Expr.size]; nlinarith

theorem compilePureComp_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂) (S_max : ℕ) (hS : 1 ≤ S_max)
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
    simp only [compilePureComp, Comp.size, compWkTop1, Comp.renameM_size]; nlinarith
  | query g e =>
    have he := compilePureExpr_size_le M S_max hS hOp e
    have hq := hQuery g
    simp only [compilePureComp, Comp.size, compWkTop1, Comp.renameM_size]; nlinarith
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

theorem compilePureExpr_size_le_nodes {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂) (S_max : ℕ)
    (hOp : ∀ o, (M.opMacro o).size ≤ S_max)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compilePureExpr M e).size ≤ e.size + S_max * e.nodes := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    simp only [compilePureExpr, Expr.size, Expr.nodes]; omega
  | add _ _ iha ihb | sub _ _ iha ihb | lt _ _ iha ihb | eqN _ _ iha ihb
  | and _ _ iha ihb | pair _ _ iha ihb | cons _ _ iha ihb | take _ _ iha ihb
  | letE _ _ iha ihb | appendL _ _ _ iha ihb | tget _ _ iha ihb
  | findB _ _ _ iha ihb | anyB _ _ _ iha ihb | mapB _ _ _ iha ihb =>
    simp only [compilePureExpr, Expr.size, Expr.nodes]; nlinarith
  | mulK _ _ iha | divK _ _ iha | modK _ _ iha | not _ iha | fst _ iha | snd _ iha
  | inl _ iha | inr _ iha | some _ iha | len _ iha | tconst _ iha =>
    simp only [compilePureExpr, Expr.size, Expr.nodes]; nlinarith
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb
  | foldrB _ _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    simp only [compilePureExpr, Expr.size, Expr.nodes]; nlinarith
  | op o _ iha =>
    have ho := hOp o
    simp only [compilePureExpr, Expr.size, Expr.nodes, Expr.wkTop1, Expr.renameM_size]; nlinarith

theorem compilePureComp_size_le_nodes {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂) (S_max : ℕ)
    (hOp : ∀ o, (M.opMacro o).size ≤ S_max)
    (hSamp : ∀ s, (M.sampMacro s).size + 1 ≤ S_max)
    (hQuery : ∀ g, (M.queryMacro g).size + 1 ≤ S_max)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureComp M c).size ≤ c.size + S_max * c.nodes := by
  induction c with
  | ret e =>
    have he := compilePureExpr_size_le_nodes M S_max hOp e
    simp only [compilePureComp, Comp.size, Comp.nodes]; nlinarith
  | bind _ _ ihc ihk =>
    simp only [compilePureComp, Comp.size, Comp.nodes]; nlinarith
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := compilePureExpr_size_le_nodes M S_max hOp b
    simp only [compilePureComp, Comp.size, Comp.nodes]; nlinarith
  | sample s e =>
    have he := compilePureExpr_size_le_nodes M S_max hOp e
    have hs := hSamp s
    simp only [compilePureComp, Comp.size, Comp.nodes, compWkTop1, Comp.renameM_size]; nlinarith
  | query g e =>
    have he := compilePureExpr_size_le_nodes M S_max hOp e
    have hq := hQuery g
    simp only [compilePureComp, Comp.size, Comp.nodes, compWkTop1, Comp.renameM_size]; nlinarith
  | iter _ e _ ihb | findM _ e _ ihb | anyM _ e _ ihb | mapM _ e _ ihb =>
    have he := compilePureExpr_size_le_nodes M S_max hOp e
    simp only [compilePureComp, Comp.size, Comp.nodes]; nlinarith
  | consumeFirstM _ l _ mk ihp =>
    have hl := compilePureExpr_size_le_nodes M S_max hOp l
    have hmk := compilePureExpr_size_le_nodes M S_max hOp mk
    simp only [compilePureComp, Comp.size, Comp.nodes]; nlinarith
  | foldM _ l z _ ihf =>
    have hl := compilePureExpr_size_le_nodes M S_max hOp l
    have hz := compilePureExpr_size_le_nodes M S_max hOp z
    simp only [compilePureComp, Comp.size, Comp.nodes]; nlinarith

theorem compilePureComp_queries_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hSamp : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQuery : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureComp M c).queries w₂ ws₂ ≤ c.queries w₁ ws₁ := by
  induction c with
  | ret _ => rfl
  | bind _ _ ihc ihk => simp only [compilePureComp, Comp.queries]; omega
  | ite _ _ _ ihc ihd | caseOpt _ _ _ ihc ihd | caseSum _ _ _ ihc ihd =>
    simp only [compilePureComp, Comp.queries]; exact max_le_max ihc ihd
  | sample s _ =>
    simp only [compilePureComp, Comp.queries, compWkTop1, Comp.renameM_queries, zero_add]
    exact hSamp s
  | query g _ =>
    simp only [compilePureComp, Comp.queries, compWkTop1, Comp.renameM_queries, zero_add]
    exact hQuery g
  | iter n _ _ ih => simp only [compilePureComp, Comp.queries]; exact Nat.mul_le_mul_left n ih
  | findM K _ _ ih | anyM K _ _ ih | mapM K _ _ ih | consumeFirstM K _ _ _ ih
  | foldM K _ _ _ ih => simp only [compilePureComp, Comp.queries]; exact Nat.mul_le_mul_left K ih

private theorem list_find_hom {α β : Type} (g : α → β) (p₁ : α → Bool) (p₂ : β → Bool)
    (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α, (xs.map g).find? p₂ = (xs.find? p₁).map g
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.find?_cons, hp x]
    cases p₁ x <;> [exact list_find_hom g p₁ p₂ hp xs; rfl]

private theorem list_any_hom {α β : Type} (g : α → β) (p₁ : α → Bool) (p₂ : β → Bool)
    (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α, (xs.map g).any p₂ = xs.any p₁
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.any_cons, hp x]
    cases p₁ x <;> [exact list_any_hom g p₁ p₂ hp xs; rfl]

private theorem list_foldr_hom {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁ → β₁) (f₂ : α₂ → β₂ → β₂)
    (hf : ∀ x acc, f₂ (g x) (h acc) = h (f₁ x acc)) (z : β₁) :
    ∀ xs : List α₁, (xs.map g).foldr f₂ (h z) = h (xs.foldr f₁ z)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.foldr_cons, list_foldr_hom g h f₁ f₂ hf z xs, hf]

theorem compilePureExpr_eval {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂)
    (hOp : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.baseTy M.toDen (O₁.dom o) x) .nil) =
        toVal M.baseTy M.toDen (O₁.cod o) (O₁.eval o x))
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) (ρ : Env Γ) :
    (compilePureExpr M e).eval (mapPureEnv M.baseTy M.toDen ρ) =
      toVal M.baseTy M.toDen t (e.eval ρ) := by
  induction e with
  | var v => exact get_mapPureEnv M.baseTy M.toDen ρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add a b iha ihb | sub a b iha ihb | lt a b iha ihb | eqN a b iha ihb
  | and a b iha ihb | pair a b iha ihb | cons a b iha ihb | tget a b iha ihb =>
    simp [compilePureExpr, Expr.eval, iha ρ, ihb ρ, toVal]
  | take n l ihn ihl =>
    simp [compilePureExpr, Expr.eval, ihn ρ, ihl ρ, toVal, List.map_take]
  | appendL K a b iha ihb =>
    simp [compilePureExpr, Expr.eval, iha ρ, ihb ρ, toVal, ← List.map_append, List.map_take]
  | mulK k a iha | divK k a iha | modK k a iha | not a iha | fst a iha | snd a iha
  | inl a iha | inr a iha | some a iha | len a iha | tconst a iha =>
    simp [compilePureExpr, Expr.eval, iha ρ, toVal]
  | ite c a b ihc iha ihb =>
    simp only [compilePureExpr, Expr.eval, ihc ρ, toVal]
    split_ifs <;> [exact iha ρ; exact ihb ρ]
  | caseOpt e n s ihe ihn ihs =>
    simp only [compilePureExpr, Expr.eval, ihe ρ, toVal]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e l r ihe ihl ihr =>
    simp only [compilePureExpr, Expr.eval, ihe ρ, toVal]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | letE e b ihe ihb =>
    simp only [compilePureExpr, Expr.eval, ihe ρ]
    exact ihb (.cons (e.eval ρ) ρ)
  | op o a iha =>
    simp only [compilePureExpr, Expr.eval, iha ρ, Expr.wkTop1_eval]
    exact hOp o (a.eval ρ)
  | findB K l p ihl ihp =>
    simp only [compilePureExpr, Expr.eval, ihl ρ, toVal, ← List.map_take]
    exact list_find_hom (toVal M.baseTy M.toDen _) (fun x => p.eval (.cons x ρ))
      (fun y => (compilePureExpr M p).eval (.cons y (mapPureEnv M.baseTy M.toDen ρ)))
      (fun x => ihp (.cons x ρ)) ((l.eval ρ).take K)
  | anyB K l p ihl ihp =>
    simp only [compilePureExpr, Expr.eval, ihl ρ, toVal, ← List.map_take]
    exact list_any_hom (toVal M.baseTy M.toDen _) (fun x => p.eval (.cons x ρ))
      (fun y => (compilePureExpr M p).eval (.cons y (mapPureEnv M.baseTy M.toDen ρ)))
      (fun x => ihp (.cons x ρ)) ((l.eval ρ).take K)
  | mapB K l f ihl ihf =>
    simp only [compilePureExpr, Expr.eval, ihl ρ, toVal, ← List.map_take, List.map_map]
    congr 1; funext x; exact ihf (.cons x ρ)
  | foldrB K l z f ihl ihz ihf =>
    simp only [compilePureExpr, Expr.eval, ihl ρ, ihz ρ, toVal, ← List.map_take]
    exact list_foldr_hom _ _ _ _ (fun x acc => ihf (.cons x (.cons acc ρ))) (z.eval ρ)
      ((l.eval ρ).take K)
  | tset m i a ihm ihi iha =>
    simp only [compilePureExpr, Expr.eval, ihm ρ, ihi ρ, iha ρ, toVal]
    funext j; split_ifs <;> rfl

private theorem iterM_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α β : Type} (g : α → β) (f₁ : α → OracleComp T α) (f₂ : β → OracleComp T β)
    (hf : ∀ a, CoinSimEquiv fwdU (f₂ (g a)) (g <$> f₁ a)) :
    ∀ (n : ℕ) (a : α), CoinSimEquiv fwdU (iterM f₂ n (g a)) (g <$> iterM f₁ n a)
  | 0, _ => CoinSimEquiv.of_eq (by simp [iterM])
  | n + 1, a => by
    dsimp only [iterM]
    refine ((hf a).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left, map_bind]
    exact (CoinSimEquiv.refl (f₁ a)).bind fun a' => iterM_coinSimEquiv_hom fwdU g f₁ f₂ hf n a'

private theorem findML_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α β : Type} (g : α → β) (p₁ : α → OracleComp T Bool) (p₂ : β → OracleComp T Bool)
    (hp : ∀ x, CoinSimEquiv fwdU (p₂ (g x)) (p₁ x)) :
    ∀ xs : List α, CoinSimEquiv fwdU (findML p₂ (xs.map g)) (Option.map g <$> findML p₁ xs)
  | [] => CoinSimEquiv.of_eq (by simp [findML])
  | x :: xs => by
    dsimp only [List.map_cons, findML]; rw [map_bind]
    exact (hp x).bind fun b => match b with
      | true => CoinSimEquiv.of_eq (by simp)
      | false => findML_coinSimEquiv_hom fwdU g p₁ p₂ hp xs

private theorem anyML_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α β : Type} (g : α → β) (p₁ : α → OracleComp T Bool) (p₂ : β → OracleComp T Bool)
    (hp : ∀ x, CoinSimEquiv fwdU (p₂ (g x)) (p₁ x)) :
    ∀ xs : List α, CoinSimEquiv fwdU (anyML p₂ (xs.map g)) (anyML p₁ xs)
  | [] => CoinSimEquiv.refl _
  | x :: xs => by
    dsimp only [List.map_cons, anyML]
    exact (hp x).bind fun b => match b with
      | true => CoinSimEquiv.refl _
      | false => anyML_coinSimEquiv_hom fwdU g p₁ p₂ hp xs

private theorem mapML_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → OracleComp T β₁) (f₂ : α₂ → OracleComp T β₂)
    (hf : ∀ x, CoinSimEquiv fwdU (f₂ (g x)) (h <$> f₁ x)) :
    ∀ xs : List α₁, CoinSimEquiv fwdU (mapML f₂ (xs.map g)) (List.map h <$> mapML f₁ xs)
  | [] => CoinSimEquiv.of_eq (by simp [mapML])
  | x :: xs => by
    dsimp only [List.map_cons, mapML]
    refine ((hf x).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left, map_bind]
    refine (CoinSimEquiv.refl (f₁ x)).bind fun y => ?_
    rw [map_bind]
    refine ((mapML_coinSimEquiv_hom fwdU g h f₁ f₂ hf xs).bind fun _ =>
      CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left]; exact CoinSimEquiv.of_eq (by simp)

private theorem consumeFirstML_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α β : Type} (g : α → β)
    (p₁ : α → OracleComp T Bool) (p₂ : β → OracleComp T Bool)
    (mk₁ : α → α) (mk₂ : β → β)
    (hp : ∀ x, CoinSimEquiv fwdU (p₂ (g x)) (p₁ x))
    (hmk : ∀ x, mk₂ (g x) = g (mk₁ x)) :
    ∀ xs : List α,
      CoinSimEquiv fwdU (consumeFirstML p₂ mk₂ (xs.map g))
        (Prod.map id (List.map g) <$> consumeFirstML p₁ mk₁ xs)
  | [] => CoinSimEquiv.of_eq (by simp [consumeFirstML])
  | x :: xs => by
    dsimp only [List.map_cons, consumeFirstML]; rw [map_bind]
    refine (hp x).bind fun b => ?_
    cases b with
    | true => exact CoinSimEquiv.of_eq (by simp [hmk x])
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [map_bind]
      refine ((consumeFirstML_coinSimEquiv_hom fwdU g p₁ p₂ mk₁ mk₂ hp hmk xs).bind fun _ =>
        CoinSimEquiv.refl _).trans ?_
      rw [bind_map_left]; exact CoinSimEquiv.of_eq (by simp)

private theorem foldML_coinSimEquiv_hom {ι : Type} {T : OracleSpec.{0, 0} ι}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁ → OracleComp T β₁) (f₂ : α₂ → β₂ → OracleComp T β₂)
    (hf : ∀ x b, CoinSimEquiv fwdU (f₂ (g x) (h b)) (h <$> f₁ x b)) :
    ∀ (b : β₁) (xs : List α₁),
      CoinSimEquiv fwdU (foldML f₂ (h b) (xs.map g)) (h <$> foldML f₁ b xs)
  | _, [] => CoinSimEquiv.of_eq (by simp [foldML])
  | b, x :: xs => by
    dsimp only [List.map_cons, foldML]
    refine ((hf x b).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left, map_bind]
    exact (CoinSimEquiv.refl (f₁ x b)).bind fun b' =>
      foldML_coinSimEquiv_hom fwdU g h f₁ f₂ hf b' xs

theorem compilePureComp_coinSimEquiv {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂)
    (hOp : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.baseTy M.toDen (O₁.dom o) x) .nil) =
        toVal M.baseTy M.toDen (O₁.cod o) (O₁.eval o x))
    (hSamp : ∀ s x,
      CoinSimEquiv I₂.fwdU
        ((M.sampMacro s).eval (.cons (toVal M.baseTy M.toDen (I₁.smp.sDom s) x) .nil))
        (toVal M.baseTy M.toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s x)))
    (hQuery : ∀ g x,
      CoinSimEquiv I₂.fwdU
        ((M.queryMacro g).eval (.cons (toVal M.baseTy M.toDen (I₁.dom g) x) .nil))
        (toVal M.baseTy M.toDen (I₁.cod g) <$>
          (I₁.dec g x <$> (liftM (T.query (I₁.enc g x)) : OracleComp T _))))
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) (ρ : Env Γ) :
    CoinSimEquiv I₂.fwdU
      ((compilePureComp M c).eval (mapPureEnv M.baseTy M.toDen ρ))
      (toVal M.baseTy M.toDen t <$> c.eval ρ) := by
  induction c with
  | ret e =>
    exact CoinSimEquiv.of_eq (by simp [compilePureComp, Comp.eval, compilePureExpr_eval M hOp e ρ])
  | bind c k ihc ihk =>
    dsimp only [compilePureComp, Comp.eval]
    refine ((ihc ρ).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left, map_bind]
    exact (CoinSimEquiv.refl (c.eval ρ)).bind fun x => ihk (.cons x ρ)
  | ite b c d ihc ihd =>
    dsimp only [compilePureComp, Comp.eval]
    rw [compilePureExpr_eval M hOp b ρ]; dsimp only [toVal]
    cases b.eval ρ with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ihd ρ
    | true => simp only [↓reduceIte]; exact ihc ρ
  | caseOpt e n s ihn ihs =>
    dsimp only [compilePureComp, Comp.eval]
    rw [compilePureExpr_eval M hOp e ρ]; dsimp only [toVal]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    dsimp only [compilePureComp, Comp.eval]
    rw [compilePureExpr_eval M hOp e ρ]; dsimp only [toVal]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | sample s e =>
    dsimp only [compilePureComp, Comp.eval]
    rw [pure_bind, compWkTop1_eval, compilePureExpr_eval M hOp e ρ]
    exact hSamp s (e.eval ρ)
  | query g e =>
    dsimp only [compilePureComp, Comp.eval]
    rw [pure_bind, compWkTop1_eval, compilePureExpr_eval M hOp e ρ]
    exact hQuery g (e.eval ρ)
  | iter n e body ihb =>
    dsimp only [compilePureComp, Comp.eval]
    rw [compilePureExpr_eval M hOp e ρ]
    exact iterM_coinSimEquiv_hom I₂.fwdU (toVal M.baseTy M.toDen _)
      (fun a => body.eval (.cons a ρ)) _ (fun a => ihb (.cons a ρ)) n (e.eval ρ)
  | findM K l p ihp =>
    dsimp only [compilePureComp, Comp.eval]
    rw [compilePureExpr_eval M hOp l ρ]; dsimp only [toVal]; rw [← List.map_take]
    exact findML_coinSimEquiv_hom I₂.fwdU (toVal M.baseTy M.toDen _)
      (fun x => p.eval (.cons x ρ)) _ (fun x => (ihp (.cons x ρ)).trans
        (CoinSimEquiv.of_eq (show id <$> p.eval (.cons x ρ) = _ from id_map _))) ((l.eval ρ).take K)
  | anyM K l p ihp =>
    dsimp only [compilePureComp, Comp.eval]
    rw [compilePureExpr_eval M hOp l ρ]; dsimp only [toVal]; rw [← List.map_take]
    refine (anyML_coinSimEquiv_hom I₂.fwdU (toVal M.baseTy M.toDen _)
      (fun x => p.eval (.cons x ρ)) _ (fun x => (ihp (.cons x ρ)).trans
        (CoinSimEquiv.of_eq (show id <$> p.eval (.cons x ρ) = _ from id_map _)))
      ((l.eval ρ).take K)).trans ?_
    exact CoinSimEquiv.of_eq (show _ = id <$> _ from (id_map _).symm)
  | mapM K l f ihf =>
    dsimp only [compilePureComp, Comp.eval]
    rw [compilePureExpr_eval M hOp l ρ]; dsimp only [toVal]; rw [← List.map_take]
    exact mapML_coinSimEquiv_hom I₂.fwdU (toVal M.baseTy M.toDen _) (toVal M.baseTy M.toDen _)
      (fun x => f.eval (.cons x ρ)) _ (fun x => ihf (.cons x ρ)) ((l.eval ρ).take K)
  | consumeFirstM K l p mk ihp =>
    dsimp only [compilePureComp, Comp.eval]
    rw [compilePureExpr_eval M hOp l ρ]; dsimp only [toVal]; rw [← List.map_take]
    exact consumeFirstML_coinSimEquiv_hom I₂.fwdU (toVal M.baseTy M.toDen _)
      (fun x => p.eval (.cons x ρ)) _ (fun x => mk.eval (.cons x ρ)) _
      (fun x => (ihp (.cons x ρ)).trans
        (CoinSimEquiv.of_eq (show id <$> p.eval (.cons x ρ) = _ from id_map _)))
      (fun x => compilePureExpr_eval M hOp mk (.cons x ρ)) ((l.eval ρ).take K)
  | foldM K l z f ihf =>
    dsimp only [compilePureComp, Comp.eval]
    rw [compilePureExpr_eval M hOp l ρ, compilePureExpr_eval M hOp z ρ]
    dsimp only [toVal]; rw [← List.map_take]
    exact foldML_coinSimEquiv_hom I₂.fwdU (toVal M.baseTy M.toDen _) (toVal M.baseTy M.toDen _)
      (fun x acc => f.eval (.cons x (.cons acc ρ))) _
      (fun x acc => ihf (.cons x (.cons acc ρ))) (z.eval ρ) ((l.eval ρ).take K)

private theorem iterM_map_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (f₁ : α → m α) (f₂ : β → m β)
    (hf : ∀ a, f₂ (g a) = g <$> f₁ a) :
    ∀ (n : ℕ) (a : α), iterM f₂ n (g a) = g <$> iterM f₁ n a
  | 0, _ => by simp [iterM]
  | n + 1, a => by
    simp only [iterM, hf a, bind_map_left, map_bind]
    exact bind_congr fun a' => iterM_map_eq g f₁ f₂ hf n a'

private theorem findML_map_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (p₁ : α → m Bool) (p₂ : β → m Bool)
    (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α, findML p₂ (xs.map g) = Option.map g <$> findML p₁ xs
  | [] => by simp [findML]
  | x :: xs => by
    simp only [List.map_cons, findML, hp x, map_bind]
    exact bind_congr fun b => match b with
      | true => by simp
      | false => findML_map_eq g p₁ p₂ hp xs

private theorem anyML_map_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (p₁ : α → m Bool) (p₂ : β → m Bool)
    (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α, anyML p₂ (xs.map g) = anyML p₁ xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, anyML, hp x]
    exact bind_congr fun b => match b with
      | true => rfl
      | false => anyML_map_eq g p₁ p₂ hp xs

private theorem mapML_map_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → m β₁) (f₂ : α₂ → m β₂)
    (hf : ∀ x, f₂ (g x) = h <$> f₁ x) :
    ∀ xs : List α₁, mapML f₂ (xs.map g) = List.map h <$> mapML f₁ xs
  | [] => by simp [mapML]
  | x :: xs => by
    simp only [List.map_cons, mapML, hf x, bind_map_left, map_bind]
    refine bind_congr fun _ => ?_
    rw [mapML_map_eq g h f₁ f₂ hf xs, bind_map_left]; simp

private theorem foldML_map_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁ → m β₁) (f₂ : α₂ → β₂ → m β₂)
    (hf : ∀ x b, f₂ (g x) (h b) = h <$> f₁ x b) :
    ∀ (b : β₁) (xs : List α₁), foldML f₂ (h b) (xs.map g) = h <$> foldML f₁ b xs
  | _, [] => by simp [foldML]
  | b, x :: xs => by
    simp only [List.map_cons, foldML, hf x b, bind_map_left, map_bind]
    exact bind_congr fun b' => foldML_map_eq g h f₁ f₂ hf b' xs

private theorem consumeFirstML_map_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (p₁ : α → m Bool) (p₂ : β → m Bool)
    (mk₁ : α → α) (mk₂ : β → β)
    (hp : ∀ x, p₂ (g x) = p₁ x) (hmk : ∀ x, mk₂ (g x) = g (mk₁ x)) :
    ∀ xs : List α,
      consumeFirstML p₂ mk₂ (xs.map g) = Prod.map id (List.map g) <$> consumeFirstML p₁ mk₁ xs
  | [] => by simp [consumeFirstML]
  | x :: xs => by
    simp only [List.map_cons, consumeFirstML, hp x, map_bind]
    refine bind_congr fun b => ?_
    cases b with
    | true => simp [hmk x]
    | false => rw [consumeFirstML_map_eq g p₁ p₂ mk₁ mk₂ hp hmk xs, bind_map_left]; simp

theorem compilePureComp_eval_eq {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec.{0, 0} ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (M : PureMacroBundle O₁ O₂ I₁ I₂)
    (hOp : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.baseTy M.toDen (O₁.dom o) x) .nil) =
        toVal M.baseTy M.toDen (O₁.cod o) (O₁.eval o x))
    (hSamp : ∀ s x,
      (M.sampMacro s).eval (.cons (toVal M.baseTy M.toDen (I₁.smp.sDom s) x) .nil) =
        toVal M.baseTy M.toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s x))
    (hQuery : ∀ g x,
      (M.queryMacro g).eval (.cons (toVal M.baseTy M.toDen (I₁.dom g) x) .nil) =
        toVal M.baseTy M.toDen (I₁.cod g) <$>
          (I₁.dec g x <$> (liftM (T.query (I₁.enc g x)) : OracleComp T _)))
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) (ρ : Env Γ) :
    (compilePureComp M c).eval (mapPureEnv M.baseTy M.toDen ρ) =
      toVal M.baseTy M.toDen t <$> c.eval ρ := by
  induction c with
  | ret e => simp [compilePureComp, Comp.eval, compilePureExpr_eval M hOp e ρ]
  | bind c k ihc ihk =>
    simp only [compilePureComp, Comp.eval, ihc ρ, bind_map_left, map_bind]
    exact bind_congr fun x => ihk (.cons x ρ)
  | ite b _ _ ihc ihd =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M hOp b ρ, toVal]
    split_ifs <;> [exact ihc ρ; exact ihd ρ]
  | caseOpt e _ _ ihn ihs =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M hOp e ρ, toVal]
    cases e.eval ρ with | none => exact ihn ρ | some x => exact ihs (.cons x ρ)
  | caseSum e _ _ ihl ihr =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M hOp e ρ, toVal]
    cases e.eval ρ with | inl x => exact ihl (.cons x ρ) | inr y => exact ihr (.cons y ρ)
  | sample s e =>
    simp only [compilePureComp, Comp.eval, pure_bind, compWkTop1_eval,
      compilePureExpr_eval M hOp e ρ]
    exact hSamp s (e.eval ρ)
  | query g e =>
    simp only [compilePureComp, Comp.eval, pure_bind, compWkTop1_eval,
      compilePureExpr_eval M hOp e ρ]
    exact hQuery g (e.eval ρ)
  | iter n e body ihb =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M hOp e ρ]
    exact iterM_map_eq (toVal M.baseTy M.toDen _) (fun a => body.eval (.cons a ρ)) _
      (fun a => ihb (.cons a ρ)) n (e.eval ρ)
  | findM K l p ihp =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M hOp l ρ, toVal, ← List.map_take]
    exact findML_map_eq (toVal M.baseTy M.toDen _) (fun x => p.eval (.cons x ρ)) _
      (fun x => (ihp (.cons x ρ)).trans (show id <$> p.eval (.cons x ρ) = _ from id_map _))
      ((l.eval ρ).take K)
  | anyM K l p ihp =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M hOp l ρ, toVal, ← List.map_take]
    refine (anyML_map_eq (toVal M.baseTy M.toDen _) (fun x => p.eval (.cons x ρ)) _
      (fun x => (ihp (.cons x ρ)).trans (show id <$> p.eval (.cons x ρ) = _ from id_map _))
      ((l.eval ρ).take K)).trans ?_
    exact (show id <$> _ = _ from id_map _).symm
  | mapM K l f ihf =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M hOp l ρ, toVal, ← List.map_take]
    exact mapML_map_eq (toVal M.baseTy M.toDen _) (toVal M.baseTy M.toDen _)
      (fun x => f.eval (.cons x ρ)) _ (fun x => ihf (.cons x ρ)) ((l.eval ρ).take K)
  | consumeFirstM K l p mk ihp =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M hOp l ρ, toVal, ← List.map_take]
    exact consumeFirstML_map_eq (toVal M.baseTy M.toDen _) _ _ _ _
      (fun x => (ihp (.cons x ρ)).trans (show id <$> p.eval (.cons x ρ) = _ from id_map _))
      (fun x => compilePureExpr_eval M hOp mk (.cons x ρ)) ((l.eval ρ).take K)
  | foldM K l z f ihf =>
    simp only [compilePureComp, Comp.eval, compilePureExpr_eval M hOp l ρ,
      compilePureExpr_eval M hOp z ρ, toVal, ← List.map_take]
    exact foldML_map_eq (toVal M.baseTy M.toDen _) (toVal M.baseTy M.toDen _)
      (fun x acc => f.eval (.cons x (.cons acc ρ))) _
      (fun x acc => ihf (.cons x (.cons acc ρ))) (z.eval ρ) ((l.eval ρ).take K)

@[expose, reducible] def castHandle {S₂ : Sig} {O₂ : Ops S₂} {ι : Type} {T : OracleSpec.{0, 0} ι}
    {I₂ : Iface S₂ T} {σ Q₁ R₁ Q₂ R₂ : Ty S₂}
    (hQ : Q₁ = Q₂) (hR : R₁ = R₂)
    (c : Comp O₂ I₂ [σ, Q₁] (.prod R₁ σ)) : Comp O₂ I₂ [σ, Q₂] (.prod R₂ σ) :=
  hQ ▸ hR ▸ c

@[expose] def compilePureRed {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q := by rfl)
    (hR : mapTy M.baseTy C₁.R = C₂.R := by rfl) :
    CostedReduction O₂ I₂ G C₂ (mapTy M.baseTy rIn₁) .unit .bool .bool where
  σ := mapTy M.baseTy R.σ
  init := compilePureComp M R.init
  handle := castHandle hQ hR (compilePureComp M R.handle)
  finish := compilePureComp M R.finish

theorem compilePureRed_totalCost_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (opC : O₁.Op → ℕ) (sC : I₁.smp.Samp → ℕ) (qC : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).cost + 1 ≤ opC o)
    (hSamp : ∀ s, (M.sampMacro s).cost + 2 ≤ sC s)
    (hQuery : ∀ g, (M.queryMacro g).cost + 2 ≤ qC g) (q : ℕ) :
    (compilePureRed C₂ M R hQ hR).totalCost q ≤
      compCostBound opC sC qC R.init +
      q * max I₂.uCost (compCostBound opC sC qC R.handle + C₂.codecCost) +
      compCostBound opC sC qC R.finish := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, cc₂⟩
  dsimp only at hQ hR; subst hQ; subst hR
  have hi := compilePureComp_cost_le M opC sC qC hOp hSamp hQuery R.init
  have hh := compilePureComp_cost_le M opC sC qC hOp hSamp hQuery R.handle
  have hf := compilePureComp_cost_le M opC sC qC hOp hSamp hQuery R.finish
  have hmax : max I₂.uCost ((compilePureComp M R.handle).cost + cc₂) ≤
      max I₂.uCost (compCostBound opC sC qC R.handle + cc₂) :=
    max_le_max le_rfl (Nat.add_le_add_right hh cc₂)
  have hmul := Nat.mul_le_mul_left q hmax
  dsimp only [CostedReduction.totalCost, compilePureRed, castHandle]
  omega

theorem compilePureRed_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (S_max : ℕ) (hS : 1 ≤ S_max)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ S_max)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ S_max)
    (hQuery : ∀ g, (M.queryMacro g).size + 2 ≤ S_max) :
    (compilePureRed C₂ M R hQ hR).size ≤ S_max * R.size := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, cc₂⟩
  dsimp only at hQ hR; subst hQ; subst hR
  have hi := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.init
  have hh := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.handle
  have hf := compilePureComp_size_le M S_max hS hOp hSamp hQuery R.finish
  dsimp only [CostedReduction.size, compilePureRed, castHandle]
  nlinarith

theorem compilePureRed_size_le_nodes {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (S_max : ℕ)
    (hOp : ∀ o, (M.opMacro o).size ≤ S_max)
    (hSamp : ∀ s, (M.sampMacro s).size + 1 ≤ S_max)
    (hQuery : ∀ g, (M.queryMacro g).size + 1 ≤ S_max) :
    (compilePureRed C₂ M R hQ hR).size ≤ R.size + S_max * R.nodes := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, cc₂⟩
  dsimp only at hQ hR; subst hQ; subst hR
  have hi := compilePureComp_size_le_nodes M S_max hOp hSamp hQuery R.init
  have hh := compilePureComp_size_le_nodes M S_max hOp hSamp hQuery R.handle
  have hf := compilePureComp_size_le_nodes M S_max hOp hSamp hQuery R.finish
  dsimp only [CostedReduction.size, CostedReduction.nodes, compilePureRed, castHandle]
  nlinarith

theorem compilePureRed_totalQueries_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hSamp : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQuery : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g) (q : ℕ) :
    (compilePureRed C₂ M R hQ hR).totalQueries w₂ ws₂ q ≤ R.totalQueries w₁ ws₁ q := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, cc₂⟩
  dsimp only at hQ hR; subst hQ; subst hR
  have hi := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSamp hQuery R.init
  have hh := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSamp hQuery R.handle
  have hf := compilePureComp_queries_le M w₁ ws₁ w₂ ws₂ hSamp hQuery R.finish
  have hmul := Nat.mul_le_mul_left q hh
  dsimp only [CostedReduction.totalQueries, compilePureRed, castHandle]
  omega

private theorem simulateQ_state_coinSimEquiv {ι κ : Type}
    {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    {σ₁ σ₂ : Type} (proj : σ₁ → σ₂)
    {impl₁ : QueryImpl G (StateT σ₁ (OracleComp T))}
    {impl₂ : QueryImpl G (StateT σ₂ (OracleComp T))}
    (hStep : ∀ q s₁,
      CoinSimEquiv fwdU ((impl₂ q).run (proj s₁)) (Prod.map id proj <$> (impl₁ q).run s₁))
    {α : Type} (oa : OracleComp G α) :
    ∀ s₁ : σ₁,
      CoinSimEquiv fwdU ((simulateQ impl₂ oa).run (proj s₁))
        (Prod.map id proj <$> (simulateQ impl₁ oa).run s₁) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s₁; exact CoinSimEquiv.of_eq (by simp)
  | query_bind q mx ih =>
    intro s₁
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    change CoinSimEquiv fwdU
      ((impl₂ q).run (proj s₁) >>= fun p => (simulateQ impl₂ (mx p.1)).run p.2)
      (Prod.map id proj <$> ((impl₁ q).run s₁ >>= fun p => (simulateQ impl₁ (mx p.1)).run p.2))
    rw [map_bind]
    refine ((hStep q s₁).bind fun _ => CoinSimEquiv.refl _).trans ?_
    rw [bind_map_left]
    exact (CoinSimEquiv.refl ((impl₁ q).run s₁)).bind fun p => ih p.1 p.2

private theorem simulateQ_state_eq {ι κ : Type}
    {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {σ₁ σ₂ : Type} (proj : σ₁ → σ₂)
    {impl₁ : QueryImpl G (StateT σ₁ (OracleComp T))}
    {impl₂ : QueryImpl G (StateT σ₂ (OracleComp T))}
    (hStep : ∀ q s₁, (impl₂ q).run (proj s₁) = Prod.map id proj <$> (impl₁ q).run s₁)
    {α : Type} (oa : OracleComp G α) :
    ∀ s₁ : σ₁,
      (simulateQ impl₂ oa).run (proj s₁) = Prod.map id proj <$> (simulateQ impl₁ oa).run s₁ := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s₁; simp
  | query_bind q mx ih =>
    intro s₁
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    change ((impl₂ q).run (proj s₁) >>= fun p => (simulateQ impl₂ (mx p.1)).run p.2) =
      Prod.map id proj <$> ((impl₁ q).run s₁ >>= fun p => (simulateQ impl₁ (mx p.1)).run p.2)
    rw [hStep q s₁, bind_map_left, map_bind]
    exact bind_congr fun p => ih p.1 p.2

theorem compilePureRed_eval_eq {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hOp : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.baseTy M.toDen (O₁.dom o) x) .nil) =
        toVal M.baseTy M.toDen (O₁.cod o) (O₁.eval o x))
    (hSamp : ∀ s x,
      (M.sampMacro s).eval (.cons (toVal M.baseTy M.toDen (I₁.smp.sDom s) x) .nil) =
        toVal M.baseTy M.toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s x))
    (hQuery : ∀ g x,
      (M.queryMacro g).eval (.cons (toVal M.baseTy M.toDen (I₁.dom g) x) .nil) =
        toVal M.baseTy M.toDen (I₁.cod g) <$>
          (I₁.dec g x <$> (liftM (T.query (I₁.enc g x)) : OracleComp T _)))
    (hQenc : ∀ t : κ, C₂.qenc t = hQ ▸ toVal M.baseTy M.toDen C₁.Q (C₁.qenc t))
    (hRdec : ∀ (t : κ) (r₁ : C₁.R.denote),
      C₂.rdec t (hR ▸ toVal M.baseTy M.toDen C₁.R r₁) = C₁.rdec t r₁)
    (A : Unit → OracleComp (unifSpec + G) Bool) (x : rIn₁.denote) :
    (compilePureRed C₂ M R hQ hR).eval A (toVal M.baseTy M.toDen rIn₁ x) = R.eval A x := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, cc₂⟩
  dsimp only at hQ hR; subst hQ; subst hR
  let C₂' : GameCodec S₂ G := ⟨mapTy M.baseTy C₁.Q, mapTy M.baseTy C₁.R, qenc₂, rdec₂, cc₂⟩
  dsimp only [CostedReduction.eval, compilePureRed, castHandle]
  change (do
    let p ← (compilePureComp M R.init).eval (mapPureEnv M.baseTy M.toDen (.cons x .nil))
    let q ← (simulateQ (handlerImpl (C := C₂') (compilePureComp M R.handle)) (A p.1)).run p.2
    (compilePureComp M R.finish).eval (.cons q.2 (.cons q.1 .nil))) = _
  rw [compilePureComp_eval_eq M hOp hSamp hQuery R.init (.cons x .nil), bind_map_left]
  refine bind_congr fun ⟨a, s⟩ => ?_
  have hStep : ∀ q s₁,
      (handlerImpl (C := C₂') (compilePureComp M R.handle) q).run
        (toVal M.baseTy M.toDen R.σ s₁) =
        Prod.map id (toVal M.baseTy M.toDen R.σ) <$> (R.impl q).run s₁ := by
    intro q s₁
    cases q with
    | inl n => simp [CostedReduction.impl, handlerImpl, StateT.lift, StateT.run, hFwdU n]
    | inr t =>
      dsimp only [CostedReduction.impl, handlerImpl, StateT.run, StateT.mk, C₂'] at hQenc hRdec ⊢
      rw [hQenc t]
      change (do
        let p ← (compilePureComp M R.handle).eval
          (mapPureEnv M.baseTy M.toDen (.cons s₁ (.cons (C₁.qenc t) .nil)))
        pure (rdec₂ t p.1, p.2)) = _
      rw [compilePureComp_eval_eq M hOp hSamp hQuery R.handle (.cons s₁ (.cons (C₁.qenc t) .nil)),
        bind_map_left, map_bind]
      exact bind_congr fun ⟨r₁, s₁'⟩ => by dsimp [toVal]; rw [hRdec t r₁]; rfl
  rw [show (toVal M.baseTy M.toDen (.prod .unit R.σ) (a, s)).1 = a from rfl,
    show (toVal M.baseTy M.toDen (.prod .unit R.σ) (a, s)).2 = toVal M.baseTy M.toDen R.σ s from rfl,
    simulateQ_state_eq (toVal M.baseTy M.toDen R.σ) hStep (A a) s, bind_map_left]
  refine bind_congr fun ⟨b, s'⟩ => ?_
  dsimp only [Prod.map, id]
  change (compilePureComp M R.finish).eval (mapPureEnv M.baseTy M.toDen (.cons s' (.cons b .nil))) = _
  exact (compilePureComp_eval_eq M hOp hSamp hQuery R.finish (.cons s' (.cons b .nil))).trans
    (show id <$> _ = _ from id_map _)

theorem compilePureRed_coinSimEquiv {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hOp : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.baseTy M.toDen (O₁.dom o) x) .nil) =
        toVal M.baseTy M.toDen (O₁.cod o) (O₁.eval o x))
    (hSamp : ∀ s x,
      CoinSimEquiv I₂.fwdU
        ((M.sampMacro s).eval (.cons (toVal M.baseTy M.toDen (I₁.smp.sDom s) x) .nil))
        (toVal M.baseTy M.toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s x)))
    (hQuery : ∀ g x,
      CoinSimEquiv I₂.fwdU
        ((M.queryMacro g).eval (.cons (toVal M.baseTy M.toDen (I₁.dom g) x) .nil))
        (toVal M.baseTy M.toDen (I₁.cod g) <$>
          (I₁.dec g x <$> (liftM (T.query (I₁.enc g x)) : OracleComp T _))))
    (hQenc : ∀ t : κ, C₂.qenc t = hQ ▸ toVal M.baseTy M.toDen C₁.Q (C₁.qenc t))
    (hRdec : ∀ (t : κ) (r₁ : C₁.R.denote),
      C₂.rdec t (hR ▸ toVal M.baseTy M.toDen C₁.R r₁) = C₁.rdec t r₁)
    (A : Unit → OracleComp (unifSpec + G) Bool) (x : rIn₁.denote) :
    CoinSimEquiv I₂.fwdU
      ((compilePureRed C₂ M R hQ hR).eval A (toVal M.baseTy M.toDen rIn₁ x))
      (R.eval A x) := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, cc₂⟩
  dsimp only at hQ hR; subst hQ; subst hR
  let C₂' : GameCodec S₂ G := ⟨mapTy M.baseTy C₁.Q, mapTy M.baseTy C₁.R, qenc₂, rdec₂, cc₂⟩
  dsimp only [CostedReduction.eval, compilePureRed, castHandle]
  change CoinSimEquiv I₂.fwdU
    (do
      let p ← (compilePureComp M R.init).eval (mapPureEnv M.baseTy M.toDen (.cons x .nil))
      let q ← (simulateQ (handlerImpl (C := C₂') (compilePureComp M R.handle)) (A p.1)).run p.2
      (compilePureComp M R.finish).eval (.cons q.2 (.cons q.1 .nil)))
    _
  refine ((compilePureComp_coinSimEquiv M hOp hSamp hQuery R.init (.cons x .nil)).bind
    fun _ => CoinSimEquiv.refl _).trans ?_
  rw [bind_map_left]
  refine (CoinSimEquiv.refl (R.init.eval (.cons x .nil))).bind fun ⟨a, s⟩ => ?_
  have hStep : ∀ q s₁,
      CoinSimEquiv I₂.fwdU
        ((handlerImpl (C := C₂') (compilePureComp M R.handle) q).run
          (toVal M.baseTy M.toDen R.σ s₁))
        (Prod.map id (toVal M.baseTy M.toDen R.σ) <$> (R.impl q).run s₁) := by
    intro q s₁
    cases q with
    | inl n =>
      exact CoinSimEquiv.of_eq (by simp [CostedReduction.impl, handlerImpl, StateT.lift,
        StateT.run, hFwdU n])
    | inr t =>
      dsimp only [CostedReduction.impl, handlerImpl, StateT.run, StateT.mk, C₂'] at hQenc hRdec ⊢
      rw [hQenc t]
      change CoinSimEquiv I₂.fwdU
        (do
          let p ← (compilePureComp M R.handle).eval
            (mapPureEnv M.baseTy M.toDen (.cons s₁ (.cons (C₁.qenc t) .nil)))
          pure (rdec₂ t p.1, p.2)) _
      refine ((compilePureComp_coinSimEquiv M hOp hSamp hQuery R.handle
        (.cons s₁ (.cons (C₁.qenc t) .nil))).bind fun _ => CoinSimEquiv.refl _).trans ?_
      rw [bind_map_left, map_bind]
      exact (CoinSimEquiv.refl _).bind fun ⟨r₁, s₁'⟩ =>
        CoinSimEquiv.of_eq (by dsimp [toVal]; rw [hRdec t r₁]; rfl)
  dsimp only [toVal]
  refine ((simulateQ_state_coinSimEquiv I₂.fwdU (toVal M.baseTy M.toDen R.σ) hStep (A a) s).bind
    fun _ => CoinSimEquiv.refl _).trans ?_
  rw [bind_map_left]
  refine (CoinSimEquiv.refl _).bind fun ⟨b, s'⟩ => ?_
  dsimp only [Prod.map, id]
  change CoinSimEquiv I₂.fwdU
    ((compilePureComp M R.finish).eval (mapPureEnv M.baseTy M.toDen (.cons s' (.cons b .nil)))) _
  exact (compilePureComp_coinSimEquiv M hOp hSamp hQuery R.finish
    (.cons s' (.cons b .nil))).trans (CoinSimEquiv.of_eq (show id <$> _ = _ from id_map _))

open _root_.ReductionDsl (TwoStageCostedReduction Mid runFuel)
open CryptoVerification.LibsignalSession (evalTwoStage1)

@[expose, reducible] def castHandlePre {S₂ : Sig} {O₂ : Ops S₂} {ι : Type} {T : OracleSpec.{0, 0} ι}
    {I₂ : Iface S₂ T} {σ π ch Q₁ R₁ Q₂ R₂ : Ty S₂}
    (hQ : Q₁ = Q₂) (hR : R₁ = R₂)
    (c : Comp O₂ I₂ [σ, Q₁] (.sum (.prod R₁ σ) (.prod ch (.prod π σ)))) :
    Comp O₂ I₂ [σ, Q₂] (.sum (.prod R₂ σ) (.prod ch (.prod π σ))) :=
  hQ ▸ hR ▸ c

@[expose, reducible] def castResume {S₂ : Sig} {O₂ : Ops S₂} {ι : Type} {T : OracleSpec.{0, 0} ι}
    {I₂ : Iface S₂ T} {σ π rIn2 R₁ R₂ : Ty S₂}
    (hR : R₁ = R₂)
    (c : Comp O₂ I₂ [σ, π, rIn2] (.prod R₁ σ)) : Comp O₂ I₂ [σ, π, rIn2] (.prod R₂ σ) :=
  hR ▸ c

@[expose] def compilePureTwoStageRed {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .unit .unit .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q := by rfl)
    (hR : mapTy M.baseTy C₁.R = C₂.R := by rfl) :
    TwoStageCostedReduction O₂ I₂ G C₂ (mapTy M.baseTy rIn₁) .unit .bool .unit .unit .bool where
  σ := mapTy M.baseTy R.σ
  π := mapTy M.baseTy R.π
  init := compilePureComp M R.init
  handlePre := castHandlePre hQ hR (compilePureComp M R.handlePre)
  chDone := compilePureComp M R.chDone
  resume := castResume hR (compilePureComp M R.resume)
  handlePost := castHandle hQ hR (compilePureComp M R.handlePost)
  finish := compilePureComp M R.finish


@[simp, expose] def _root_.ReductionDsl.TwoStageCostedReduction.nodes {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out) : ℕ :=
  R.init.nodes + R.handlePre.nodes + R.chDone.nodes + R.resume.nodes + R.handlePost.nodes +
    R.finish.nodes


@[expose] def compilePureTwoStageMid {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .unit .unit .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R) {α : Type} :
    Mid G α R.π.denote R.σ.denote Unit →
      Mid G α (compilePureTwoStageRed C₂ M R hQ hR).π.denote
        (compilePureTwoStageRed C₂ M R hQ hR).σ.denote Unit
  | .done a s =>
    .done a (toVal M.baseTy M.toDen R.σ s : (compilePureTwoStageRed C₂ M R hQ hR).σ.denote)
  | .paused t c p s k =>
    .paused t c
      (toVal M.baseTy M.toDen R.π p : (compilePureTwoStageRed C₂ M R hQ hR).π.denote)
      (toVal M.baseTy M.toDen R.σ s : (compilePureTwoStageRed C₂ M R hQ hR).σ.denote) k


end PureMacro

end Computational.Proofs.ReductionDsl.FsAtomicMacros

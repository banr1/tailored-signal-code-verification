/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliPqAdapterRemoteIdInv
import all Init.Data.String.Defs
import all Init.Data.Repr
public import Computational.Proofs.LibsignalCli.CliPqBadKemBound
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Simulation
import Computational.Proofs.E2E.BhAdapterIjHelpersV1Core
import Computational.Proofs.E2E.ComposedBinaryLinkV1
import Computational.Proofs.LibsignalCli.Entry.CliPqEntryBridges
import Computational.Proofs.LibsignalCli.Entry.CliPqReachSize
import Computational.Proofs.LibsignalCli.Entry.CliPqSessionCap
import Computational.Proofs.ReductionDsl.SM.GameCosted
import LibsignalBinary.Proofs.SignalSession.Closure.Version
import ProofLib.SepLogic.WP.StepsCore
import VCVio.EvalDist.Monad.Basic

/-!
# Bob SM step coupling

**Checked by Lean.** Proves Bob's SM deliver and inject step couplings (`cliDrvSM_bob_dl_coupled`,
`cliDrvSM_bob_ij_coupled`) outside `cliClause2BadKemBool`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession
  CryptoVerification.LibsignalCli.Entry

/-! ## Canonical tag-3 wire helpers and Bob `cliPqReceive` specs -/

private theorem params_receive_remoteIdentity {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (g g' : GhostState PQ) (c : Bytes) (rc : BitVec 256)
    {t i : ℕ} {pt : Bytes}
    (h : P.receive g c rc = some (g', t, i, pt)) :
    g'.session.remoteIdentity = g.session.remoteIdentity := by
  unfold Params.receive at h
  rcases htf : SignalMessage.tryFrom P.codec c with _ | msg
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    rcases hd : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
        msg .whisper rc g.session with ⟨_ | pt', s'⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      have hrem := (Closure.Version.tryDecryptFromRecord_sessionVersion_remoteIdentity
        P.C P.spqr (P.expectedAddrs g.party) msg .whisper rc g.session).2
      rw [hd] at hrem
      have hg' : g'.session.remoteIdentity = s'.remoteIdentity := by rw [← h.1]
      exact hg'.trans hrem

private theorem bhReadProstVarint_prostVarint (n : ℕ) (rest : List (BitVec 8)) :
    bhReadProstVarint (Prost.varint n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn generalizing rest with
  | ind n ih =>
    rw [Prost.varint.eq_1]
    split_ifs with hlt
    · have h8 : (BitVec.ofNat 8 n).toNat = n := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp [bhReadProstVarint, h8, hlt]
    · have h8 : (BitVec.ofNat 8 (n % 128 + 128)).toNat = n % 128 + 128 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hdiv : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
      simp only [List.cons_append, bhReadProstVarint, h8,
        show ¬ (n % 128 + 128 < 128) by omega, ↓reduceIte,
        ih (n / 128) hdiv rest, Option.map_some]
      congr 1; congr 1; omega

private theorem take_drop_append {α : Type} (l rest : List α) :
    l.length ≤ (l ++ rest).length ∧ (l ++ rest).take l.length = l ∧
      (l ++ rest).drop l.length = rest := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨by simp, ?_, ?_⟩
    · simp [h2]
    · simp [h3]

private theorem prost_varint_step (n : ℕ) :
    Prost.varint n =
      if n < 128 then [BitVec.ofNat 8 n]
      else BitVec.ofNat 8 (n % 128 + 128) :: Prost.varint (n / 128) :=
  Prost.varint.eq_1 n

private theorem prost_key_lt128 (tag wt : ℕ) (h : 8 * tag + wt < 128) :
    Prost.key tag wt = [BitVec.ofNat 8 (8 * tag + wt)] := by
  unfold Prost.key
  rw [prost_varint_step]
  simp [h]

private theorem bhDecodePreKeyMsgE_wirePrekey (m : PreKeyMessageFields) :
    bhDecodePreKeyMsgE (wirePrekey :: m.bytes) = some m := by
  have hraw : bhDecodePreKeyMsgERaw (wirePrekey :: m.bytes) = some m := by
    rcases m with ⟨regId, opkId, spkId, kpkId, ⟨kyberCtL, hct⟩, ⟨baseKeyL, hbk⟩, ⟨idPubL, hid⟩, inner⟩
    have hf2 : Prost.bytesField 2 (some (djbKey ⟨baseKeyL, hbk⟩)) = [0x12#8, 0x21#8, 0x05#8] ++ baseKeyL := by
      unfold Prost.bytesField djbKey
      simp only [List.Vector.toList_mk, List.length_cons, hbk,
        show 32 + 1 = 33 from rfl,
        show Prost.key 2 2 = [0x12#8] by rw [prost_key_lt128 2 2 (by omega)],
        show Prost.varint 33 = [0x21#8] by rw [prost_varint_step]; simp,
        List.cons_append, List.nil_append]
    have hf3 : Prost.bytesField 3 (some (djbKey ⟨idPubL, hid⟩)) = [0x1a#8, 0x21#8, 0x05#8] ++ idPubL := by
      unfold Prost.bytesField djbKey
      simp only [List.Vector.toList_mk, List.length_cons, hid,
        show 32 + 1 = 33 from rfl,
        show Prost.key 3 2 = [0x1a#8] by rw [prost_key_lt128 3 2 (by omega)],
        show Prost.varint 33 = [0x21#8] by rw [prost_varint_step]; simp,
        List.cons_append, List.nil_append]
    have hf4 : Prost.bytesField 4 (some inner) = [0x22#8] ++ Prost.varint inner.length ++ inner := by
      unfold Prost.bytesField
      rw [show Prost.key 4 2 = [0x22#8] by rw [prost_key_lt128 4 2 (by omega)]]
    have hf5 : Prost.uint32Field 5 (some regId) = [0x28#8] ++ Prost.varint regId.toNat := by
      unfold Prost.uint32Field
      rw [show Prost.key 5 0 = [0x28#8] by rw [prost_key_lt128 5 0 (by omega)]]
    have hf6 : Prost.uint32Field 6 (some spkId) = [0x30#8] ++ Prost.varint spkId.toNat := by
      unfold Prost.uint32Field
      rw [show Prost.key 6 0 = [0x30#8] by rw [prost_key_lt128 6 0 (by omega)]]
    have hf7 : Prost.uint32Field 7 (some kpkId) = [0x38#8] ++ Prost.varint kpkId.toNat := by
      unfold Prost.uint32Field
      rw [show Prost.key 7 0 = [0x38#8] by rw [prost_key_lt128 7 0 (by omega)]]
    have hf8 : Prost.bytesField 8 (some (kyberKey ⟨kyberCtL, hct⟩)) =
        [0x42#8, 0xa1#8, 0x0c#8, 0x08#8] ++ kyberCtL := by
      unfold Prost.bytesField kyberKey
      simp only [List.Vector.toList_mk, List.length_cons, hct,
        show 1568 + 1 = 1569 from rfl,
        show Prost.key 8 2 = [0x42#8] by rw [prost_key_lt128 8 2 (by omega)],
        show Prost.varint 1569 = [0xa1#8, 0x0c#8] by
          rw [prost_varint_step]
          simp only [show ¬(1569 < 128) by omega, ↓reduceIte]
          rw [prost_varint_step]
          simp only [show 1569 / 128 < 128 by omega, ↓reduceIte],
        List.cons_append, List.nil_append]
    let tail8 : List (BitVec 8) := 0x42#8 :: 0xa1#8 :: 0x0c#8 :: 0x08#8 :: kyberCtL
    let tail7 : List (BitVec 8) := 0x38#8 :: (Prost.varint kpkId.toNat ++ tail8)
    let tail6 : List (BitVec 8) := 0x30#8 :: (Prost.varint spkId.toNat ++ tail7)
    let tail5 : List (BitVec 8) := 0x28#8 :: (Prost.varint regId.toNat ++ tail6)
    let tail4 : List (BitVec 8) := 0x22#8 :: (Prost.varint inner.length ++ (inner ++ tail5))
    let tail3 : List (BitVec 8) := 0x1a#8 :: 0x21#8 :: 0x05#8 :: (idPubL ++ tail4)
    let tail2 : List (BitVec 8) := 0x12#8 :: 0x21#8 :: 0x05#8 :: (baseKeyL ++ tail3)
    have hbytes : (PreKeyMessageFields.mk regId opkId spkId kpkId ⟨kyberCtL, hct⟩ ⟨baseKeyL, hbk⟩ ⟨idPubL, hid⟩ inner).bytes =
        versionByte currentVersion :: (Prost.uint32Field 1 opkId ++ tail2) := by
      unfold PreKeyMessageFields.bytes ProtoPreKeySignalMessage.encode
      rw [hf2, hf3, hf4, hf5, hf6, hf7, hf8]
      simp [tail2, tail3, tail4, tail5, tail6, tail7, tail8, List.append_assoc]
    have hopk_parse : bhParseOptPreKeyId (Prost.uint32Field 1 opkId ++ tail2) =
        some (opkId.map (fun v => UInt32.ofNat v.toNat), tail2) := by
      cases opkId with
      | none =>
        simp [Prost.uint32Field, tail2, bhParseOptPreKeyId, show (0x12#8 == 0x08#8) = false by decide]
      | some v =>
        have hf1 : Prost.uint32Field 1 (some v) = 0x08#8 :: Prost.varint v.toNat := by
          unfold Prost.uint32Field
          rw [show Prost.key 1 0 = [0x08#8] by rw [prost_key_lt128 1 0 (by omega)]]
          rfl
        rw [hf1, List.cons_append]
        simp [bhParseOptPreKeyId, bhReadProstVarint_prostVarint]
    rw [hbytes]
    unfold bhDecodePreKeyMsgERaw
    simp only [beq_self_eq_true, Bool.and_self,
      ↓reduceIte, hopk_parse, Option.bind]
    obtain ⟨_, ht1, hd1⟩ := take_drop_append baseKeyL tail3
    rw [hbk] at ht1 hd1
    obtain ⟨_, ht2, hd2⟩ := take_drop_append idPubL tail4
    rw [hid] at ht2 hd2
    obtain ⟨_, ht3, hd3⟩ := take_drop_append inner tail5
    have ht4 : kyberCtL.take 1568 = kyberCtL := by simp [hct]
    cases opkId <;>
      simp [tail2, tail3, tail4, tail5, tail6, tail7, tail8,
        bhParseDjbKeyField, bhParseInnerMsgFieldWithRest, bhReadProstVarint_prostVarint,
        bhParseUint32Field, bhParseKyberCtField, Option.bind,
        ht1, hd1, ht2, hd2, ht3, hd3, ht4, hbk, hid, hct]
  unfold bhDecodePreKeyMsgE
  rw [hraw]
  simp

private theorem bhDecodePreKeyMsgE_eq_some_imp {c : Bytes} {m : PreKeyMessageFields}
    (h : bhDecodePreKeyMsgE c = some m) :
    c = wirePrekey :: m.bytes ∧ c.head? = some wirePrekey := by
  unfold bhDecodePreKeyMsgE at h
  rcases hraw : bhDecodePreKeyMsgERaw c with _ | m' <;> rw [hraw] at h
  · cases h
  · dsimp only at h
    by_cases heq : (c == wirePrekey :: m'.bytes) = true
    · simp only [heq, ↓reduceIte, Option.some.injEq] at h; subst h
      have hc : c = wirePrekey :: m'.bytes := beq_iff_eq.mp heq
      exact ⟨hc, by rw [hc]; rfl⟩
    · simp [heq] at h

@[local simp]
private theorem bhDecodePreKeyMsgE_wireWhisper_cons (body : Bytes) :
    bhDecodePreKeyMsgE (wireWhisper :: body) = none := by
  unfold bhDecodePreKeyMsgE bhDecodePreKeyMsgERaw
  cases body with
  | nil => rfl
  | cons b rest =>
    have hne : (wireWhisper == wirePrekey) = false := by decide
    simp [hne]

private theorem bhWireInnerBytes_of_decode_some {c : Bytes} {m : PreKeyMessageFields}
    (h : bhDecodePreKeyMsgE c = some m) :
    bhWireInnerBytes c = some m.inner := by
  simp [bhWireInnerBytes, h]

@[local simp]
private theorem bhWireInnerBytes_wireWhisper_cons (body : Bytes) :
    bhWireInnerBytes (wireWhisper :: body) = some body := by
  simp [bhWireInnerBytes]

private theorem prost_varint_len_le (k : ℕ) :
    ∀ n : ℕ, n < 128 ^ (k + 1) → (Prost.varint n).length ≤ k + 1 := by
  induction k with
  | zero =>
    intro n hn
    rw [Prost.varint.eq_1]
    simp [show n < 128 by omega]
  | succ k ih =>
    intro n hn
    rw [Prost.varint.eq_1]
    split_ifs with hlt
    · simp
    · simp only [List.length_cons]
      have hpow : 128 ^ (k + 1 + 1) = 128 * 128 ^ (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hdiv : n / 128 < 128 ^ (k + 1) := by omega
      have := ih (n / 128) hdiv
      omega

private theorem prost_uint32Field_len_le {tag : ℕ} (ht : tag ≤ 8) (v? : Option (BitVec 32)) :
    (Prost.uint32Field tag v?).length ≤ 10 := by
  cases v? with
  | none => simp [Prost.uint32Field]
  | some v =>
    simp only [Prost.uint32Field, Prost.key, List.length_append]
    have h1 := prost_varint_len_le 0 (8 * tag + 0) (by omega)
    have h2 := prost_varint_len_le 4 v.toNat (by have := v.isLt; omega)
    omega

private theorem prost_bytesField_len_le {tag : ℕ} (ht : tag ≤ 8) (bs : List (BitVec 8))
    (hbs : bs.length < 2 ^ 32) :
    (Prost.bytesField tag (some bs)).length ≤ 10 + bs.length := by
  simp only [Prost.bytesField, Prost.key, List.length_append]
  have h1 := prost_varint_len_le 0 (8 * tag + 2) (by omega)
  have h2 := prost_varint_len_le 4 bs.length (by omega)
  omega

private theorem encodeVarintAux_len_le (k : ℕ) :
    ∀ w : BitVec 64, (LibsignalProtoCodec.encodeVarintAux k w).length ≤ k := by
  induction k with
  | zero => intro _; simp [LibsignalProtoCodec.encodeVarintAux]
  | succ k ih =>
    intro w
    simp only [LibsignalProtoCodec.encodeVarintAux]
    split_ifs
    · simp
    · simp only [List.length_cons]
      have := ih (w >>> 7)
      omega

private theorem encodeVarint_len_le (w : BitVec 64) :
    (LibsignalProtoCodec.encodeVarint w).length ≤ 10 :=
  encodeVarintAux_len_le 10 w

private theorem encodeKey_len_le (tag : ℕ) (wt : LibsignalProtoCodec.WireType) :
    (LibsignalProtoCodec.encodeKey tag wt).length ≤ 10 :=
  encodeVarint_len_le _

private theorem encodeBytes3_len_le (tag : ℕ) (bs : List (BitVec 8)) :
    (RecordCodecs.encodeProto3BytesField tag bs).length ≤ 20 + bs.length := by
  unfold RecordCodecs.encodeProto3BytesField
  split_ifs with h
  · simp
  · simp only [LibsignalProtoCodec.encodeBytesField, List.length_append]
    have h1 := encodeKey_len_le tag .lengthDelimited
    have h2 := encodeVarint_len_le (BitVec.ofNat 64 bs.length)
    omega

private theorem encodeUint32_3_len_le (tag : ℕ) (v : BitVec 32) :
    (RecordCodecs.encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold RecordCodecs.encodeProto3Uint32Field
  split_ifs with h
  · simp
  · simp only [LibsignalProtoCodec.encodeUint32Field, List.length_append]
    have h1 := encodeKey_len_le tag .varint
    have h2 := encodeVarint_len_le (v.zeroExtend 64)
    omega

private theorem shortCiphertext_wirePrekey_of_inner_lt {m : PreKeyMessageFields}
    (hlen : m.inner.length + 2048 < 2 ^ 32) :
    shortCiphertext (wirePrekey :: m.bytes) = true := by
  unfold shortCiphertext PreKeyMessageFields.bytes ProtoPreKeySignalMessage.encode
  have hopk := prost_uint32Field_len_le (tag := 1) (by omega) m.opkId
  have hdl_bk : (djbKey m.baseKey).length = 33 := by simp [djbKey]
  have hbk : (Prost.bytesField 2 (some (djbKey m.baseKey))).length ≤ 43 := by
    have := prost_bytesField_len_le (tag := 2) (by omega) (djbKey m.baseKey) (by omega)
    omega
  have hdl_id : (djbKey m.idPub).length = 33 := by simp [djbKey]
  have hid : (Prost.bytesField 3 (some (djbKey m.idPub))).length ≤ 43 := by
    have := prost_bytesField_len_le (tag := 3) (by omega) (djbKey m.idPub) (by omega)
    omega
  have hin := prost_bytesField_len_le (tag := 4) (by omega) m.inner (by omega)
  have hreg := prost_uint32Field_len_le (tag := 5) (by omega) (some m.regId)
  have hspk := prost_uint32Field_len_le (tag := 6) (by omega) (some m.spkId)
  have hkpk := prost_uint32Field_len_le (tag := 7) (by omega) (some m.kpkId)
  have hkl_ct : (kyberKey m.kyberCt).length = 1569 := by simp [kyberKey]
  have hct : (Prost.bytesField 8 (some (kyberKey m.kyberCt))).length ≤ 1579 := by
    have := prost_bytesField_len_le (tag := 8) (by omega) (kyberKey m.kyberCt) (by omega)
    omega
  simp only [List.length_cons, List.length_append, decide_eq_true_eq]
  omega

private theorem wirePrekey_len_le_stdinCap_of_inner_le {m : PreKeyMessageFields}
    (hle : m.inner.length ≤ 1_000_300) :
    (wirePrekey :: m.bytes).length ≤ stdinCapBytes := by
  unfold stdinCapBytes PreKeyMessageFields.bytes ProtoPreKeySignalMessage.encode
  have hopk := prost_uint32Field_len_le (tag := 1) (by omega) m.opkId
  have hdl_bk : (djbKey m.baseKey).length = 33 := by simp [djbKey]
  have hbk : (Prost.bytesField 2 (some (djbKey m.baseKey))).length ≤ 43 := by
    have := prost_bytesField_len_le (tag := 2) (by omega) (djbKey m.baseKey) (by omega)
    omega
  have hdl_id : (djbKey m.idPub).length = 33 := by simp [djbKey]
  have hid : (Prost.bytesField 3 (some (djbKey m.idPub))).length ≤ 43 := by
    have := prost_bytesField_len_le (tag := 3) (by omega) (djbKey m.idPub) (by omega)
    omega
  have hin := prost_bytesField_len_le (tag := 4) (by omega) m.inner (by omega)
  have hreg := prost_uint32Field_len_le (tag := 5) (by omega) (some m.regId)
  have hspk := prost_uint32Field_len_le (tag := 6) (by omega) (some m.spkId)
  have hkpk := prost_uint32Field_len_le (tag := 7) (by omega) (some m.kpkId)
  have hkl_ct : (kyberKey m.kyberCt).length = 1569 := by simp [kyberKey]
  have hct : (Prost.bytesField 8 (some (kyberKey m.kyberCt))).length ≤ 1579 := by
    have := prost_bytesField_len_le (tag := 8) (by omega) (kyberKey m.kyberCt) (by omega)
    omega
  simp only [List.length_cons, List.length_append]
  omega

private theorem cliPqLenOk_of_decode_some {c : Bytes} {m : PreKeyMessageFields}
    (hdec : bhDecodePreKeyMsgE c = some m) (hlen : m.inner.length + 2048 < 2 ^ 32) :
    cliPqLenOk c = true := by
  obtain ⟨hc, _⟩ := bhDecodePreKeyMsgE_eq_some_imp hdec
  unfold cliPqLenOk
  rw [hdec]
  have hsc : shortCiphertext c = true := by rw [hc]; exact shortCiphertext_wirePrekey_of_inner_lt hlen
  simp [hsc]
  omega

private theorem cliPqLenOk_wireWhisper {body : Bytes}
    (hlen : (wireWhisper :: body).length < 2 ^ 32) :
    cliPqLenOk (wireWhisper :: body) = true := by
  unfold cliPqLenOk shortCiphertext
  simp
  omega

private theorem wfPq_cliPqDirB0 {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (W : PEParams) (bi : ModelDriverInstance S ℓ)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) :
    PqxdhPartyInSpecDomain W (cliPqxdhDirBobBeforeAccept bi sigs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ h; simp [cliPqxdhDirBobBeforeAccept] at h
  · intro f hf
    suffices h : f.2.length ≤ fileCapBytes by
      exact ⟨by unfold fileCapBytes at h; omega, fun _ => h⟩
    unfold cliPqxdhDirBobBeforeAccept encodeDir at hf
    simp only [List.map_nil, List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map] at hf
    rcases hf with ((((h1 | h2 | h3) | h4) | ⟨⟨i, k⟩, hm, rfl⟩) | ⟨⟨i, ok⟩, hm, rfl⟩) | hf_lr
    · subst h1; decide +kernel
    · subst h2
      dsimp [RecordCodecs.IdentityKeyPairStructure.encode]
      simp only [List.length_append]
      have h_pk := encodeBytes3_len_le 1 (djbKey (keyPairOf W.C bi.meB.idPriv).publicKey.bytes)
      have h_sk := encodeBytes3_len_le 2 bi.meB.idPriv.toList
      have hdjb : (djbKey (keyPairOf W.C bi.meB.idPriv).publicKey.bytes).length = 33 := by simp [djbKey]
      have hpriv : bi.meB.idPriv.toList.length = 32 := bi.meB.idPriv.2
      unfold fileCapBytes; omega
    · subst h3; simp [le32, fileCapBytes]
    · subst h4; simp [IdentityKey.serialize, PublicKey.serialize, fileCapBytes]
    · simp only [Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      dsimp [signedRecordBytes, RecordCodecs.SignedPreKeyRecordStructure.encode]
      simp only [List.length_append]
      have a1 := encodeUint32_3_len_le 1 bi.keysB.spkId
      have a2 := encodeBytes3_len_le 2 (djbKey (keyPairOf W.C bi.keysB.spkPriv).publicKey.bytes)
      have a3 := encodeBytes3_len_le 3 bi.keysB.spkPriv.toList
      have a4 := encodeBytes3_len_le 4 sigs.1.toList
      have a5 : (RecordCodecs.encodeProto3Fixed64Field 5 0#64).length = 0 := rfl
      have l2 : (djbKey (keyPairOf W.C bi.keysB.spkPriv).publicKey.bytes).length = 33 := by simp [djbKey]
      have l3 : bi.keysB.spkPriv.toList.length = 32 := bi.keysB.spkPriv.2
      have l4 : sigs.1.toList.length = 64 := sigs.1.2
      unfold fileCapBytes; omega
    · rcases h_opk : bi.keysB.opk with _ | ⟨oid, osk⟩ <;> rw [h_opk] at hm
      · simp at hm
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        dsimp [oneTimeRecordBytes, RecordCodecs.PreKeyRecordStructure.encode]
        simp only [List.length_append]
        have a1 := encodeUint32_3_len_le 1 i
        have a2 := encodeBytes3_len_le 2 (djbKey (keyPairOf W.C osk).publicKey.bytes)
        have a3 := encodeBytes3_len_le 3 osk.toList
        have l2 : (djbKey (keyPairOf W.C osk).publicKey.bytes).length = 33 := by simp [djbKey]
        have l3 : osk.toList.length = 32 := osk.2
        unfold fileCapBytes; omega
    · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hf_lr
      rcases hf_lr with rfl | rfl
      · dsimp [kyberRecordBytes, RecordCodecs.SignedPreKeyRecordStructure.encode]
        simp only [List.length_append]
        have a1 := encodeUint32_3_len_le 1 bi.keysB.kpkId
        have a2 := encodeBytes3_len_le 2 (kyberKey bi.keysB.kpkPub)
        have a3 := encodeBytes3_len_le 3 (0x08#8 :: bi.keysB.kpkSec.toList)
        have a4 := encodeBytes3_len_le 4 sigs.2.toList
        have a5 : (RecordCodecs.encodeProto3Fixed64Field 5 0#64).length = 0 := rfl
        have l2 : (kyberKey bi.keysB.kpkPub).length = 1569 := by simp [kyberKey]
        have l3 : (0x08#8 :: bi.keysB.kpkSec.toList).length = 3169 := by simp
        have l4 : sigs.2.toList.length = 64 := sigs.2.2
        unfold fileCapBytes; omega
      · simp [baseKeysBytes, fileCapBytes]
  · simp [cliPqxdhDirBobBeforeAccept]
  · unfold cliPqxdhDirBobBeforeAccept; dsimp only
    cases bi.keysB.opk <;> simp
  · simp [cliPqxdhDirBobBeforeAccept]
  · simp [cliPqxdhDirBobBeforeAccept]

private theorem cliPqDirB1_props {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (bi : ModelDriverInstance S ℓ) (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) :
    (cliPqxdhDirBobAfterAccept bi sigs).party = .B ∧
    (cliPqxdhDirBobAfterAccept bi sigs).me = bi.meB ∧
    (cliPqxdhDirBobAfterAccept bi sigs).peerId = some (bhIdKeyOf bi.hdr.ikAPk) ∧
    (cliPqxdhDirBobAfterAccept bi sigs).session = none ∧
    (cliPqxdhDirBobAfterAccept bi sigs).trusts (bhIdKeyOf bi.hdr.ikAPk) = true ∧
    lastResortUses (cliPqxdhDirBobAfterAccept bi sigs) ≤ 1 := by
  have hrm : ∀ (st : PqParty) (m : PreKeyMessageFields),
      (removeOpk st m).party = st.party ∧
      (removeOpk st m).me = st.me ∧
      (removeOpk st m).peerId = st.peerId ∧
      (removeOpk st m).session = st.session ∧
      lastResortUses (removeOpk st m) = lastResortUses st := by
    intro st m; unfold removeOpk; cases m.opkId <;> simp [lastResortUses]
  unfold cliPqxdhDirBobAfterAccept
  set m0 := bhExpectedPreKeyMsg bi.meA.regId bi.hdr []
  set d0 := cliPqxdhDirBobBeforeAccept bi sigs
  obtain ⟨hp, hme, hpeer, hsess, hlr⟩ := hrm ((markKyberUsed d0 m0).getD d0) m0
  have hd0_props :
      ((markKyberUsed d0 m0).getD d0).party = .B ∧
      ((markKyberUsed d0 m0).getD d0).me = bi.meB ∧
      ((markKyberUsed d0 m0).getD d0).peerId = some (bhIdKeyOf bi.hdr.ikAPk) ∧
      ((markKyberUsed d0 m0).getD d0).session = none ∧
      lastResortUses ((markKyberUsed d0 m0).getD d0) ≤ 1 := by
    unfold markKyberUsed
    have hkot : List.lookup m0.kpkId d0.kyberOneTime = none := by simp [d0, cliPqxdhDirBobBeforeAccept]
    rw [hkot]
    by_cases hk : (m0.kpkId == bi.keysB.kpkId) = true
    · have hk_eq : m0.kpkId = bi.keysB.kpkId := beq_iff_eq.mp hk
      have hklr : List.lookup m0.kpkId d0.kyberLastResort =
          some ({ pub := bi.keysB.kpkPub, sec := bi.keysB.kpkSec, sig := sigs.2, timestamp := 0#64 }, []) := by
        simp [d0, cliPqxdhDirBobBeforeAccept, List.lookup, hk]
      rw [hklr]
      simp [d0, cliPqxdhDirBobBeforeAccept, hk_eq, lastResortUses, fileCapBytes]
    · have hk_false : (m0.kpkId == bi.keysB.kpkId) = false := Bool.eq_false_iff.mpr hk
      have hklr : List.lookup m0.kpkId d0.kyberLastResort = none := by
        simp [d0, cliPqxdhDirBobBeforeAccept, List.lookup, hk_false]
      rw [hklr]
      simp [d0, cliPqxdhDirBobBeforeAccept, lastResortUses]
  refine ⟨hp.trans hd0_props.1, hme.trans hd0_props.2.1, hpeer.trans hd0_props.2.2.1,
    hsess.trans hd0_props.2.2.2.1, ?_, hlr ▸ hd0_props.2.2.2.2⟩
  unfold PqParty.trusts
  rw [hpeer.trans hd0_props.2.2.1]
  simp

private theorem markKyberUsed_cliPqDirB0_expected {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (bi : ModelDriverInstance S ℓ) (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (inner : Bytes)
    (hkpk : (bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner).kpkId = bi.keysB.kpkId) :
    ∃ st1,
      markKyberUsed (cliPqxdhDirBobBeforeAccept bi sigs)
        (bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner) = some st1 ∧
      ∀ x g,
        { removeOpk st1 (bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner) with
            peerId := some ⟨⟨(bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner).idPub⟩⟩,
            session := some (x, g) } =
          { cliPqxdhDirBobAfterAccept bi sigs with session := some (x, g) } := by
  set m := bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner
  set m0 := bhExpectedPreKeyMsg bi.meA.regId bi.hdr []
  set d0 := cliPqxdhDirBobBeforeAccept bi sigs
  have hm_kpk : m0.kpkId = bi.keysB.kpkId := hkpk
  have hmk_eq : markKyberUsed d0 m = markKyberUsed d0 m0 := rfl
  have hmk0 : ∃ st1, markKyberUsed d0 m0 = some st1 := by
    unfold markKyberUsed
    have hkot : List.lookup m0.kpkId d0.kyberOneTime = none := by simp [d0, cliPqxdhDirBobBeforeAccept]
    have hklr : List.lookup m0.kpkId d0.kyberLastResort =
        some ({ pub := bi.keysB.kpkPub, sec := bi.keysB.kpkSec, sig := sigs.2, timestamp := 0#64 }, []) := by
      simp [d0, cliPqxdhDirBobBeforeAccept, hm_kpk]
    rw [hkot, hklr]
    simp only [List.length_nil, Nat.mul_zero, fileCapBytes, Nat.not_lt_zero, List.not_mem_nil,
      or_self, ↓reduceIte]
    exact ⟨_, rfl⟩
  obtain ⟨st1, hst1⟩ := hmk0
  refine ⟨st1, hmk_eq.trans hst1, fun x g => ?_⟩
  have hb1 : cliPqxdhDirBobAfterAccept bi sigs = removeOpk st1 m0 := by
    unfold cliPqxdhDirBobAfterAccept
    change removeOpk ((markKyberUsed d0 m0).getD d0) m0 = removeOpk st1 m0
    rw [hst1]; rfl
  have hrm_eq : removeOpk st1 m = removeOpk st1 m0 := rfl
  have hid_eq : (⟨⟨m.idPub⟩⟩ : IdentityKey) = bhIdKeyOf bi.hdr.ikAPk := rfl
  have hpeer : (cliPqxdhDirBobAfterAccept bi sigs).peerId = some (bhIdKeyOf bi.hdr.ikAPk) :=
    (cliPqDirB1_props bi sigs).2.2.1
  rw [hrm_eq, ← hb1, hid_eq, ← hpeer]

private theorem keysFor_cliPqDirB0_of_acceptKeys {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (W : PEParams) (bi : ModelDriverInstance S ℓ)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (m : PreKeyMessageFields) (dk : SignalPqxdh.DRKey)
    (hids : m.spkId = bi.keysB.spkId ∧ m.kpkId = bi.keysB.kpkId)
    (hacc : SignalPqxdh.Model.acceptKeys P (acceptInput W bi.meB bi.keysB m) = some dk) :
    ∃ k,
      preKeysNamedBy (cliPqxdhDirBobBeforeAccept bi sigs) m = some k ∧
      k.spkId = bi.keysB.spkId ∧
      k.spkPriv = bi.keysB.spkPriv ∧
      k.kpkId = bi.keysB.kpkId ∧
      acceptInput W bi.meB k m = acceptInput W bi.meB bi.keysB m := by
  unfold preKeysNamedBy
  set d0 := cliPqxdhDirBobBeforeAccept bi sigs
  have hspk : List.lookup m.spkId d0.signed =
      some { priv := bi.keysB.spkPriv, sig := sigs.1, timestamp := 0#64 } := by
    simp [d0, cliPqxdhDirBobBeforeAccept, hids.1]
  have hkot : List.lookup m.kpkId d0.kyberOneTime = none := by simp [d0, cliPqxdhDirBobBeforeAccept]
  have hklr : List.lookup m.kpkId d0.kyberLastResort =
      some ({ pub := bi.keysB.kpkPub, sec := bi.keysB.kpkSec, sig := sigs.2, timestamp := 0#64 }, []) := by
    simp [d0, cliPqxdhDirBobBeforeAccept, hids.2]
  rw [hspk, hkot, hklr]
  dsimp only [Option.map]
  rcases hopk : m.opkId with _ | j
  · refine ⟨{ spkId := m.spkId, spkPriv := bi.keysB.spkPriv, kpkId := m.kpkId,
              kpkPub := bi.keysB.kpkPub, kpkSec := bi.keysB.kpkSec, opk := none },
            rfl, hids.1, rfl, hids.2, ?_⟩
    simp [acceptInput, hopk]
  · unfold SignalPqxdh.Model.acceptKeys at hacc
    have hinp_hdr : (acceptInput W bi.meB bi.keysB m).hdr.opkId? = some (u32 j) := by
      simp [acceptInput, hopk]
    rcases hkb : bi.keysB.opk with _ | ⟨j', sk⟩
    · have hinp_opk : (acceptInput W bi.meB bi.keysB m).opkBSk? = none := by
        simp [acceptInput, hopk, hkb]
      rw [hinp_hdr, hinp_opk] at hacc
      simp at hacc
    · by_cases hj : j = j'
      · subst hj
        have hot : List.lookup j d0.oneTime = some (some sk) := by
          simp [d0, cliPqxdhDirBobBeforeAccept, hkb]
        dsimp only
        rw [hot]
        refine ⟨bi.keysB, ?_, rfl, rfl, rfl, rfl⟩
        cases hkeys : bi.keysB
        rw [hkeys] at hkb hids
        dsimp only at hkb hids ⊢
        rw [hids.1, hids.2, hkb]
      · have hinp_opk : (acceptInput W bi.meB bi.keysB m).opkBSk? = none := by
          simp [acceptInput, hopk, hkb, Ne.symm hj]
        rw [hinp_hdr, hinp_opk] at hacc
        simp at hacc

private theorem lookup_readBackDir_some {paths : List String}
    {fs : String → Option Bytes} {p : String} {v : Bytes}
    (h : List.lookup p (readBackDir paths fs) = some v) :
    fs p = some v := by
  unfold readBackDir at h
  induction paths with
  | nil => simp at h
  | cons q qs ih =>
    rcases hfq : fs q with _ | bs
    · simp [hfq] at h
      exact ih h
    · simp only [List.filterMap_cons, hfq, Option.map_some, List.lookup] at h
      by_cases hpq : (p == q) = true
      · simp only [hpq, Option.some.injEq] at h
        have heq : p = q := beq_iff_eq.mp hpq
        subst heq; subst h; exact hfq
      · have hpq_f : (p == q) = false := Bool.eq_false_iff.mpr hpq
        rw [hpq_f] at h
        exact ih h

private theorem lookup_sessionFile_encodeDir_B (W : PEParams) (st : PqParty)
    (k : IdentityKey) (x : RecordExtras) (g : GhostState Bytes)
    (hp : st.party = .B) (hpeer : st.peerId = some k)
    (hsess : st.session = some (x, g)) :
    List.lookup (sessionFile (partyAddress .A)) (encodeDir W st) =
      some (encodeRecordUnderExtras (fun _ => x) g) := by
  unfold encodeDir
  have hot : Party.B.other = .A := rfl
  rw [hp, hot, hpeer, hsess]
  have hne1 : (sessionFile (partyAddress .A) == addressFile) = false := by decide
  have hne2 : (sessionFile (partyAddress .A) == identityKeyPairFile) = false := by decide
  have hne3 : (sessionFile (partyAddress .A) == registrationIdFile) = false := by decide
  have hne4 : (sessionFile (partyAddress .A) == identityFile (partyAddressName .A)) = false := by decide
  simp [List.lookup, hne1, hne2, hne3, hne4]

private theorem cliPqInputs_recv_eq_cliPqRecvInputsFromFiles (W : PEParams)
    (d st : PqParty) (rec c : Bytes) (rc : BitVec 256)
    (hp : d.party = st.party)
    (hraw : cliPqDirRaw W d rec = encodeDir W st) :
    cliPqInputs W d rec (.recv (partyAddress d.party.other)) [] (HMAC.keyToBytes32 rc) c =
      cliPqRecvInputsFromFiles st.party (encodeDir W st) c rc := by
  unfold cliPqInputs cliPqRecvInputsFromFiles cliPqRawInputs
  rw [hp, hraw]

private theorem paramsIdsWithSpqr_eq_paramsPqBIds (W : PEParams) (idA idB : IdentityKey) :
    paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) idA idB = paramsPqBIds W idA idB :=
  rfl

private theorem params_receive_party {PQ PQC : Type} [Inhabited PQ]
    (P : Params PQ PQC) (g g' : GhostState PQ) (c : Bytes) (rc : BitVec 256)
    {t i : ℕ} {pt : Bytes}
    (h : P.receive g c rc = some (g', t, i, pt)) :
    g'.party = g.party := by
  unfold Params.receive at h
  rcases htf : SignalMessage.tryFrom P.codec c with _ | msg
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    rcases hd : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
        msg .whisper rc g.session with ⟨_ | pt', s'⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]

private theorem cliPqRecv_prekey_first_spec {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hspec : CliSpecPqxdh run X W)
    (bi : ModelDriverInstance S ℓ) (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (idA idB : IdentityKey) (spkCoins aliceCoins : BitVec 256)
    (dk : SignalPqxdh.DRKey) (q_rem : ℕ)
    (inner : Bytes) (rc : BitVec 256)
    (hidA : idA = bhIdKeyOf bi.hdr.ikAPk)
    (hidB : idB = ⟨(keyPairOf W.C bi.meB.idPriv).publicKey⟩)
    (hspk : keyPairOf W.C bi.keysB.spkPriv = KeyPair.generate W.C spkCoins)
    (hlen : inner.length + 2048 < 2 ^ 32)
    (hcap : (wirePrekey :: (bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner).bytes).length ≤ stdinCapBytes)
    (hids : (bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner).spkId = bi.keysB.spkId ∧
            (bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner).kpkId = bi.keysB.kpkId)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W bi.meB bi.keysB (bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner)) = some dk) :
    let m := bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner
    let c := wirePrekey :: m.bytes
    let sB0 : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
    let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) idA idB
    let gB0 := (sessionSchemeFixedSpk P_v1 ℓ spkCoins).initB (bhKeySOf dk aliceCoins)
    let xB := bhRecvExtrasOfHdr bi.meA bi.meB bi.hdr
    (cliPqScheme run W ℓ bi sigs bi.stA0 sB0).receive sB0 c rc =
      ((sessionSchemeFixedSpk P_v1 ℓ spkCoins).receive gB0 inner rc).map
        (fun (gB', t, idx, pt) => (binStateOfUnderExtras (fun _ => xB) gB', t, idx, pt)) ∧
    (∀ gB' t idx pt,
      (sessionSchemeFixedSpk P_v1 ℓ spkCoins).receive gB0 inner rc = some (gB', t, idx, pt) →
      0 < q_rem →
      gB'.party = .B ∧
      gB'.epoch = 1 ∧
      gB'.session.pendingPreKey = false ∧
      gB'.session.remoteIdentity = some idA ∧
      CliPartyActiveInv W (cliPqxdhDirBobAfterAccept bi sigs) xB gB' (q_rem - 1)) := by
  intro m c sB0 P_v1 gB0 xB
  set d0 := cliPqxdhDirBobBeforeAccept bi sigs
  have hwf0 : PqxdhPartyInSpecDomain W d0 := wfPq_cliPqDirB0 W bi sigs
  have hdec_c : bhDecodePreKeyMsgE c = some m := bhDecodePreKeyMsgE_wirePrekey m
  have hlen_ok : cliPqLenOk c = true := cliPqLenOk_of_decode_some hdec_c hlen
  have hwire_in : bhWireInnerBytes c = some inner := bhWireInnerBytes_of_decode_some hdec_c
  obtain ⟨k, hk_for, hk_spkId, hk_spkPriv, hk_kpkId, hk_inp⟩ :=
    keysFor_cliPqDirB0_of_acceptKeys (modelPrims X W) W bi sigs m dk hids hacc
  obtain ⟨st1, hmk_st1, hst1_b1⟩ := markKyberUsed_cliPqDirB0_expected bi sigs inner hids.2
  have hacc_k : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W bi.meB k m) = some dk := by
    rw [hk_inp]; exact hacc
  have hids_k : m.spkId = k.spkId ∧ m.kpkId = k.kpkId := ⟨hids.1.trans hk_spkId.symm, hids.2.trans hk_kpkId.symm⟩
  have hjoin := recvPrekeyState_join_eq_initB_receive X W bi.meB k m rc aliceCoins dk hids_k hacc_k
  have hidA_m : (⟨⟨m.idPub⟩⟩ : IdentityKey) = idA := hidA.symm
  have hP_eq : paramsPqBIds W ⟨⟨m.idPub⟩⟩ ⟨(keyPairOf W.C bi.meB.idPriv).publicKey⟩ = P_v1 := by
    dsimp only [P_v1]
    rw [hidA_m, ← hidB, paramsIdsWithSpqr_eq_paramsPqBIds]
  set kInit := initKeysOfSampled (HKDF.bytesToKey32 k.spkPriv.toList)
    ((HKDF.bytesToKey32 (ofU8 dk.rootKey), HKDF.bytesToKey32 (ofU8 dk.chainKey)),
     aliceCoins, HKDF.bytesToKey32 (ofU8 dk.pqrKey))
  have hgB0_eq : P_v1.initB kInit = gB0 := by
    dsimp only [gB0, sessionSchemeFixedSpk, Params.initB, initKeysOfSampled, bhKeySOf, bhBytesWord, kInit,
      P_v1, paramsIdsWithSpqr]
    rw [← keyPairOf_eq_keyPair_generate W.C k.spkPriv, hk_spkPriv, hspk]
  have hm_in : m.inner = inner := rfl
  dsimp only at hjoin
  rw [hP_eq, hgB0_eq, hm_in] at hjoin
  have hxB_eq : responderRecordExtras bi.meB m = xB := rfl
  have htrust0 : (!d0.trusts ⟨⟨m.idPub⟩⟩) = false := by
    simp [d0, cliPqxdhDirBobBeforeAccept, PqParty.trusts, m, bhExpectedPreKeyMsg, bhIdKeyOf]
  have hmod_join : (pqRecvPrekeyModel X W d0 m rc).join =
      (P_v1.receive gB0 inner rc).map (fun (gB', _, _, pt) =>
        ({ cliPqxdhDirBobAfterAccept bi sigs with session := some (xB, gB') }, pt)) := by
    unfold pqRecvPrekeyModel
    rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with err | msg
    · have hrec_none : P_v1.receive gB0 inner rc = none := by
        have htf' : SignalMessage.tryFrom P_v1.codec inner = .error err := htf
        unfold Params.receive
        rw [htf']
      rw [hrec_none]; rfl
    · dsimp only
      have hd0_sess : d0.session = none := rfl
      have hd0_party : d0.party = .B := rfl
      have hd0_me : d0.me = bi.meB := rfl
      change preKeysNamedBy d0 m = some k at hk_for
      change markKyberUsed d0 m = some st1 at hmk_st1
      simp only [htrust0, Bool.false_eq_true, ↓reduceIte, hd0_sess, hk_for, hd0_party, hd0_me]
      rcases hrps : recvPrekeyState X W .B bi.meB k m rc with _ | (_ | ⟨x', g', pt'⟩)
      · rw [hrps] at hjoin
        simp only [Option.join_none] at hjoin ⊢
        rcases hrec : P_v1.receive gB0 inner rc with _ | _
        · rfl
        · rw [hrec] at hjoin; simp at hjoin
      · rw [hrps] at hjoin
        simp only [Option.join_some] at hjoin ⊢
        rcases hrec : P_v1.receive gB0 inner rc with _ | _
        · rfl
        · rw [hrec] at hjoin; simp at hjoin
      · rw [hrps] at hjoin
        simp only [Option.join_some] at hjoin ⊢
        rw [hmk_st1]
        rcases hrec : P_v1.receive gB0 inner rc with _ | ⟨gB', t', idx', pt''⟩
        · rw [hrec] at hjoin; simp at hjoin
        · rw [hrec] at hjoin
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hjoin
          rcases hjoin with ⟨hx', rfl, rfl⟩
          have hx_xB : x' = xB := hx'.trans hxB_eq
          subst hx_xB
          simp only [Option.map_some, Option.join_some]
          rw [hst1_b1 xB g']
  have hcomm := cliPqRecvPrekeyInitDir_eq_pqRecvPrekeyModel hspec d0 hwf0 rfl m rc hlen hcap
  rw [hmod_join] at hcomm
  have hinp_eq : cliPqInputs W (cliPqDirOf bi sigs sB0) sB0.bytes
      (.recv (partyAddress Party.B.other)) [] (HMAC.keyToBytes32 rc) c =
      cliPqRecvInputsFromFiles d0.party (encodeDir W d0) c rc := by
    have hd_of : cliPqDirOf bi sigs sB0 = d0 := rfl
    rw [hd_of]
    exact cliPqInputs_recv_eq_cliPqRecvInputsFromFiles W d0 d0 [] c rc rfl
      (cliPqDirRawSpec_nil_eq_encodeDir W d0)
  have hpart1 : (cliPqScheme run W ℓ bi sigs bi.stA0 sB0).receive sB0 c rc =
      ((sessionSchemeFixedSpk P_v1 ℓ spkCoins).receive gB0 inner rc).map
        (fun (gB', t, idx, pt) => (binStateOfUnderExtras (fun _ => xB) gB', t, idx, pt)) := by
    change cliPqReceive run W ℓ bi sigs sB0 c rc = _
    unfold cliPqReceive
    dsimp only
    have hs_party : sB0.party = .B := rfl
    have hs_empty : (sB0.bytes.isEmpty || sB0.epochs.epoch == 0) = true := rfl
    have hc_eq : (c == wirePrekey :: (bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner).bytes) = true :=
      beq_self_eq_true c
    simp only [hlen_ok, hs_party, hdec_c, hs_empty, hc_eq, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, cliPqRecv, hwire_in]
    rw [hinp_eq]
    dsimp only [sessionSchemeFixedSpk]
    rcases hrec : P_v1.receive gB0 inner rc with _ | ⟨gB', t, idx, pt⟩
    · rw [hrec] at hcomm
      simp only [Option.map_none] at hcomm ⊢
      unfold cliPqRecvPrekeyInitDir cliDirStateOf at hcomm
      rcases hrun : run (cliPqRecvInputsFromFiles d0.party (encodeDir W d0) c rc) with _ | out
      · rfl
      · cases out with
        | aborted => rfl
        | exited code stdout fs =>
          cases code with
          | zero =>
            rw [hrun] at hcomm
            rcases htf0 : SignalMessage.tryFrom protoSignalCodec m.inner with _ | _ <;>
              simp [htf0] at hcomm
          | succ n => rfl
    · rw [hrec] at hcomm
      simp only [Option.map_some] at hcomm ⊢
      have hrec' := hrec
      unfold Params.receive at hrec'
      rcases htf : SignalMessage.tryFrom P_v1.codec inner with _ | msg
      · rw [htf] at hrec'; simp at hrec'
      · rw [htf] at hrec'
        dsimp only at hrec'
        have hparty0 : gB0.party = .B := rfl
        have hrc0 : gB0.session.receiverChains = [] := rfl
        have hep0 : gB0.epoch = 0 := rfl
        have hce0 : gB0.chainEpochs = [] := rfl
        rw [hparty0] at hrec'
        rcases hdec : SessionState.tryDecryptFromRecord P_v1.C P_v1.spqr
            (P_v1.expectedAddrs .B) msg .whisper rc gB0.session with ⟨err | pt0, st_dec⟩
        · rw [hdec] at hrec'; simp at hrec'
        · rw [hdec] at hrec'
          have hidx0 : gB0.session.receiverChains.findIdx?
              (fun rc_1 => rc_1.senderRatchetKey == msg.senderRatchetKey) = none := by
            simp [hrc0]
          rw [hidx0, hep0, hce0] at hrec'
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
          rcases hrec' with ⟨hgB'_def, rfl, rfl, rfl⟩
          unfold cliPqRecvPrekeyInitDir cliDirStateOf at hcomm
          have htf_m : SignalMessage.tryFrom protoSignalCodec m.inner = .ok msg := htf
          have htf_in : SignalMessage.tryFrom protoSignalCodec inner = .ok msg := htf
          rcases hrun : run (cliPqRecvInputsFromFiles d0.party (encodeDir W d0) c rc) with _ | out
          · rw [hrun] at hcomm; simp at hcomm
          · cases out with
            | aborted => rw [hrun] at hcomm; simp at hcomm
            | exited code stdout fs =>
              cases code with
              | succ n => rw [hrun] at hcomm; simp at hcomm
              | zero =>
                rw [hrun, htf_m] at hcomm
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcomm
                rcases hcomm with ⟨hds_eq, rfl⟩
                have hrb : readBackDir (pqPartyCandidatePathsOf d0) fs =
                    encodeDir W { cliPqxdhDirBobAfterAccept bi sigs with session := some (xB, gB') } :=
                  congrArg CliDirState.dirFiles hds_eq
                have hep_eq : (⟨1, [(msg.senderRatchetKey, 1)]⟩ : EpochGhost) = EpochGhost.ofGhost gB' :=
                  congrArg CliDirState.epochs hds_eq
                have hb1_p := cliPqDirB1_props bi sigs
                have hlkp := lookup_sessionFile_encodeDir_B W
                  { cliPqxdhDirBobAfterAccept bi sigs with session := some (xB, gB') }
                  (bhIdKeyOf bi.hdr.ikAPk) xB gB' hb1_p.1 hb1_p.2.2.1 rfl
                rw [← hrb] at hlkp
                have hfs := lookup_readBackDir_some hlkp
                have hep_recv : sB0.epochs.recv msg.senderRatchetKey = (1, ⟨1, [(msg.senderRatchetKey, 1)]⟩) := by
                  simp [sB0, EpochGhost.recv, maxReceiverChains]
                have hgB'_party : gB'.party = .B := (params_receive_party P_v1 gB0 gB' inner rc hrec).trans hparty0
                have hbin_eq : BinState.mk .B (encodeRecordUnderExtras (fun _ => xB) gB') (EpochGhost.ofGhost gB') =
                    binStateOfUnderExtras (fun _ => xB) gB' := by
                  unfold binStateOfUnderExtras; rw [hgB'_party]
                simp only [cliPqAfter, Party.other, hfs, Option.getD_some, Option.map_some,
                  htf_in, hep_recv, hep_eq, hbin_eq]
  refine ⟨hpart1, fun gB' t idx pt hrec_s _hq => ?_⟩
  dsimp only [sessionSchemeFixedSpk] at hrec_s
  rcases hpm_ex : P_v1.receive gB0 inner rc with _ | ⟨g1, t1, idx1, pt1⟩
  · rw [hpm_ex] at hrec_s; simp at hrec_s
  · rw [hpm_ex] at hrec_s
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec_s
    rcases hrec_s with ⟨rfl, rfl, rfl, rfl⟩
    have hmod_some : pqRecvPrekeyModel X W d0 m rc =
        some (some ({ cliPqxdhDirBobAfterAccept bi sigs with session := some (xB, g1) }, pt1)) := by
      rw [hpm_ex] at hmod_join
      simp only [Option.map_some] at hmod_join
      rcases hpm : pqRecvPrekeyModel X W d0 m rc with _ | (_ | v)
      · rw [hpm] at hmod_join; simp at hmod_join
      · rw [hpm] at hmod_join; simp at hmod_join
      · rw [hpm] at hmod_join
        simp only [Option.join_some, Option.some.injEq] at hmod_join
        rw [hmod_join]
    have hvac : ∀ x g, d0.session = some (x, g) → PqSessionMatches x g m := by
      intro _ _ hs; cases hs
    have hstep : PqStep X W d0 { cliPqxdhDirBobAfterAccept bi sigs with session := some (xB, g1) } :=
      PqStep.recvPrekey m rc _ pt1 hlen hvac hmod_some
    have hb1_lr : lastResortUses { cliPqxdhDirBobAfterAccept bi sigs with session := some (xB, g1) } ≤ 1 :=
      (cliPqDirB1_props bi sigs).2.2.2.2.2
    have hwf_b1 : PqxdhPartyInSpecDomain W { cliPqxdhDirBobAfterAccept bi sigs with session := some (xB, g1) } :=
      (wfPq_step_r3 hwf0 hstep (Nat.lt_of_le_of_lt hb1_lr (by decide))).1
    have hg0_party : gB0.party = .B := rfl
    have hg0_rc_nil : gB0.session.receiverChains = [] := rfl
    have hg0_ep : gB0.epoch = 0 := rfl
    have hg0_al : gB0.Aligned := rfl
    have hg0_rem : gB0.session.remoteIdentity = some idA := rfl
    have hp_props := BhAdapterIjHelpersV1.paramsV1_receive_whisper_props W W.Q.K idA idB gB0 inner rc
      hpm_ex (fun _ h => nomatch h) (Nat.zero_le _) hg0_al
      (CryptoVerification.SpqrV1.Top.StateSize.validState_spqrV1Init W.C.F W.Q.K .b2a _)
      (by have : gB0.session.pqRatchetState.length ≤ 640 :=
            spqrV1Init_length_le W.C.F W.Q.K .b2a _; omega)
    have hrem1 : g1.session.remoteIdentity = some idA :=
      (params_receive_remoteIdentity P_v1 gB0 g1 inner rc hpm_ex).trans hg0_rem
    refine ⟨hp_props.1.trans hg0_party, ?_, hp_props.2.1, hrem1, hwf_b1, ?_, hp_props.2.2.2.2.2.1, ?_⟩
    · have hep1 := hp_props.2.2.2.2.1 hg0_rc_nil
      rw [hg0_ep] at hep1; exact hep1
    · exact Nat.lt_of_le_of_lt hb1_lr (by decide)
    · exact pqLength_le_286196_of_wfPq hwf_b1

private theorem cliPqRecv_whisper_spec {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hspec : CliSpecPqxdh run X W)
    (bi : ModelDriverInstance S ℓ) (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (x : RecordExtras) (g : GhostState Bytes) (q_rem : ℕ)
    (body : Bytes) (rc : BitVec 256)
    (hact : CliPartyActiveInv W (cliPqxdhDirBobAfterAccept bi sigs) x g q_rem)
    (_hq : 0 < q_rem)
    (hp : g.party = .B)
    (hep : 0 < g.epoch)
    (hidA : idA = bhIdKeyOf bi.hdr.ikAPk)
    (hrem : g.session.remoteIdentity = some idA)
    (hlen : (wireWhisper :: body).length < 2 ^ 32)
    (hcap : (wireWhisper :: body).length ≤ stdinCapBytes) :
    let c := wireWhisper :: body
    let sB := binStateOfUnderExtras (fun _ => x) g
    let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) idA idB
    (cliPqScheme run W ℓ bi sigs bi.stA0 bi.stB0).receive sB c rc =
      ((sessionSchemeFixedSpk P_v1 ℓ spkCoins).receive g body rc).map
        (fun (g', t, idx, pt) => (binStateOfUnderExtras (fun _ => x) g', t, idx, pt)) ∧
    (∀ g' t idx pt,
      (sessionSchemeFixedSpk P_v1 ℓ spkCoins).receive g body rc = some (g', t, idx, pt) →
      g'.party = .B ∧
      0 < g'.epoch ∧
      g'.session.pendingPreKey = false ∧
      g'.session.remoteIdentity = some idA ∧
      CliPartyActiveInv W (cliPqxdhDirBobAfterAccept bi sigs) x g' (q_rem - 1)) := by
  intro c sB P_v1
  set d1 := cliPqxdhDirBobAfterAccept bi sigs
  set st := { d1 with session := some (x, g) }
  have hb1_p := cliPqDirB1_props bi sigs
  have hst_party : st.party = .B := hb1_p.1
  have hst_peer : st.peerId = some idA := by
    change d1.peerId = some idA
    rw [hidA]; exact hb1_p.2.2.1
  have hst_trust : st.trusts idA = true := by
    unfold PqParty.trusts
    rw [hst_peer]; simp
  obtain ⟨⟨g₀, hR₀, _, hsess₀⟩, _, _⟩ := hact.1.1 x g rfl
  have hrc_len : g.session.receiverChains.length ≤ maxReceiverChains := by
    rw [← hsess₀]; exact (reachPq_invCli hR₀).receiverChains_len
  have hcomm := cliPqRecvWhisperDir_eq_paramsPqBIds_receive (X := X) hspec st hact.1
    idA idB x g idA rfl hact.2.2.1 hrc_len (hp.trans hst_party.symm) hrem hst_trust body rc hlen hcap
  rw [← paramsIdsWithSpqr_eq_paramsPqBIds W idA idB] at hcomm
  have hsB_empty : sB.bytes.isEmpty = false := encodeRecordX_isEmpty_eq_false (fun _ => x) g
  have hsB_party : sB.party = .B := hp
  have hinp_eq : cliPqInputs W (cliPqDirOf bi sigs sB) sB.bytes
      (.recv (partyAddress Party.B.other)) [] (HMAC.keyToBytes32 rc) c =
      cliPqRecvInputsFromFiles st.party (encodeDir W st) (wireWhisper :: body) rc := by
    have hd_of : cliPqDirOf bi sigs sB = d1 := by
      simp [cliPqDirOf, hsB_party, hsB_empty, d1]
    rw [hd_of, ← hb1_p.1]
    exact cliPqInputs_recv_eq_cliPqRecvInputsFromFiles W d1 st sB.bytes c rc rfl
      (cliPqDirRawSpec_encodeRecordX_eq_encodeDir W d1 x g)
  have hpart1 : (cliPqScheme run W ℓ bi sigs bi.stA0 bi.stB0).receive sB c rc =
      ((sessionSchemeFixedSpk P_v1 ℓ spkCoins).receive g body rc).map
        (fun (g', t, idx, pt) => (binStateOfUnderExtras (fun _ => x) g', t, idx, pt)) := by
    change cliPqReceive run W ℓ bi sigs sB c rc = _
    unfold cliPqReceive
    dsimp only
    have hlen_ok : cliPqLenOk c = true := cliPqLenOk_wireWhisper hlen
    have hsB_ep : (sB.bytes.isEmpty || sB.epochs.epoch == 0) = false := by
      have hsB_ep_val : sB.epochs.epoch = g.epoch := rfl
      simp [hsB_empty, hsB_ep_val, Nat.ne_of_gt hep]
    have hdec_none : bhDecodePreKeyMsgE c = none := bhDecodePreKeyMsgE_wireWhisper_cons body
    have hhead : (c.head? == some wireWhisper) = true := rfl
    have hwire_in : bhWireInnerBytes c = some body := bhWireInnerBytes_wireWhisper_cons body
    simp only [hlen_ok, hsB_party, hdec_none, hsB_ep, hhead, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, cliPqRecv, hwire_in]
    rw [hinp_eq]
    dsimp only [sessionSchemeFixedSpk]
    rcases hrec : P_v1.receive g body rc with _ | ⟨g', t, idx, pt⟩
    · rw [hrec] at hcomm
      simp only [Option.map_none] at hcomm ⊢
      unfold cliPqRecvWhisperDir cliDirStateOf at hcomm
      rcases hrun : run (cliPqRecvInputsFromFiles st.party (encodeDir W st) (wireWhisper :: body) rc) with
        _ | out
      · rfl
      · cases out with
        | aborted => rfl
        | exited code stdout fs =>
          cases code with
          | zero =>
            rw [hrun] at hcomm
            rcases htf0 : SignalMessage.tryFrom protoSignalCodec body with _ | _ <;>
              simp [htf0] at hcomm
          | succ n => rfl
    · rw [hrec] at hcomm
      simp only [Option.map_some] at hcomm ⊢
      have hrec' := hrec
      unfold Params.receive at hrec'
      rcases htf : SignalMessage.tryFrom P_v1.codec body with _ | msg
      · rw [htf] at hrec'; simp at hrec'
      · have htf_p : SignalMessage.tryFrom protoSignalCodec body = .ok msg := htf
        unfold cliPqRecvWhisperDir cliDirStateOf at hcomm
        rcases hrun : run (cliPqRecvInputsFromFiles st.party (encodeDir W st) (wireWhisper :: body) rc) with
          _ | out
        · rw [hrun] at hcomm; simp at hcomm
        · cases out with
          | aborted => rw [hrun] at hcomm; simp at hcomm
          | exited code stdout fs =>
            cases code with
            | succ n => rw [hrun] at hcomm; simp at hcomm
            | zero =>
              rw [hrun, htf_p] at hcomm
              simp only [Option.some.injEq, Prod.mk.injEq] at hcomm
              rcases hcomm with ⟨hds_eq, ht_eq, hidx_eq, rfl⟩
              have hrb : readBackDir (pqPartyCandidatePathsOf st) fs =
                  encodeDir W { st with peerId := some idA, session := some (x, g') } :=
                congrArg CliDirState.dirFiles hds_eq
              have hep_eq : (EpochGhost.ofGhost g).recv msg.senderRatchetKey =
                  (t, EpochGhost.ofGhost g') := by
                have he1 : ((EpochGhost.ofGhost g).recv msg.senderRatchetKey).2 = EpochGhost.ofGhost g' := by
                  simpa using congrArg CliDirState.epochs hds_eq
                exact Prod.ext ht_eq he1
              have hlkp := lookup_sessionFile_encodeDir_B W
                { st with peerId := some idA, session := some (x, g') }
                idA x g' hst_party rfl rfl
              rw [← hrb] at hlkp
              have hfs := lookup_readBackDir_some hlkp
              have hsB_ep_eq : sB.epochs = EpochGhost.ofGhost g := rfl
              have hg'_party : g'.party = .B := (params_receive_party P_v1 g g' body rc hrec).trans hp
              have hbin_eq : BinState.mk .B (encodeRecordUnderExtras (fun _ => x) g') (EpochGhost.ofGhost g') =
                  binStateOfUnderExtras (fun _ => x) g' := by
                unfold binStateOfUnderExtras; rw [hg'_party]
              simp only [cliPqAfter, Party.other, hfs, Option.getD_some, Option.map_some,
                htf_p, hsB_ep_eq, hep_eq, hidx_eq, hbin_eq]
  refine ⟨hpart1, fun g' t idx pt hrec_s => ?_⟩
  dsimp only [sessionSchemeFixedSpk] at hrec_s
  rcases hrec : P_v1.receive g body rc with _ | ⟨g1, t1, idx1, pt1⟩
  · rw [hrec] at hrec_s; simp at hrec_s
  · rw [hrec] at hrec_s
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec_s
    rcases hrec_s with ⟨rfl, rfl, rfl, rfl⟩
    have hp_props := BhAdapterIjHelpersV1.paramsV1_receive_whisper_props W W.Q.K idA idB g body rc
      hrec
      (by rw [← hsess₀]; intro rc_c hrc_c mk hmk
          exact ((reachPq_invCli hR₀).receiverChains_inv rc_c hrc_c).2.2.2 mk hmk)
      hrc_len hact.2.2.1
      (by rw [← hsess₀]; exact reachPq_validState_cli hR₀)
      (by have := hact.2.2.2; omega)
    have hrec_raw := hrec
    unfold Params.receive at hrec_raw
    rcases htf : SignalMessage.tryFrom P_v1.codec body with _ | msg
    · rw [htf] at hrec_raw; simp at hrec_raw
    · rw [htf, hp] at hrec_raw; dsimp only at hrec_raw
      rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).expectedAddrs .B) msg .whisper rc g.session with ⟨err | pt_d, s_dec⟩
      · have hdec' : SessionState.tryDecryptFromRecord P_v1.C P_v1.spqr
            (P_v1.expectedAddrs .B) msg .whisper rc g.session = (.error err, s_dec) := by
          have hd : TripleRatchet.decrypt P_v1.C P_v1.spqr (P_v1.expectedAddrs .B) msg .whisper rc =
              TripleRatchet.decrypt W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs .B) msg .whisper rc := rfl
          unfold SessionState.tryDecryptFromRecord SessionState.tryDecryptWithState at hdec ⊢
          rw [hd]; exact hdec
        rw [hdec'] at hrec_raw; simp at hrec_raw
      · have hdec' : SessionState.tryDecryptFromRecord P_v1.C P_v1.spqr
            (P_v1.expectedAddrs .B) msg .whisper rc g.session = (.ok pt_d, s_dec) := by
          have hd : TripleRatchet.decrypt P_v1.C P_v1.spqr (P_v1.expectedAddrs .B) msg .whisper rc =
              TripleRatchet.decrypt W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs .B) msg .whisper rc := rfl
          unfold SessionState.tryDecryptFromRecord SessionState.tryDecryptWithState at hdec ⊢
          rw [hd]; exact hdec
        rw [hdec'] at hrec_raw
        simp only [Option.some.injEq, Prod.mk.injEq] at hrec_raw
        have hg1_sess : g1.session = s_dec := by rw [← hrec_raw.1]
        have hs_rem : s_dec.remoteIdentity = some idA := by
          have hvr := (Closure.Version.tryDecryptFromRecord_sessionVersion_remoteIdentity
            W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs .B) msg .whisper rc g.session).2
          rw [hdec, hrem] at hvr; exact hvr
        have hrem1 : g1.session.remoteIdentity = some idA := hg1_sess ▸ hs_rem
        let st_raw : PqParty := { st with peerId := some idA, session := some (x, { g with session := s_dec }) }
        have hmod : pqRecvWhisperModel W st body rc = some (some (st_raw, pt_d)) := by
          have htf_p : SignalMessage.tryFrom protoSignalCodec body = .ok msg := htf
          have hnt : (!st.trusts idA) = false := by simp [hst_trust]
          simp [pqRecvWhisperModel, pqxdhSessionDecryptModel, st, htf_p, hp, hdec, hs_rem, hnt, st_raw]
        have hstep : PqStep X W st st_raw :=
          PqStep.recvWhisper body rc st_raw pt_d (by simp at hlen; omega) hmod
        have hlr_le : lastResortUses st_raw < 2 ^ 25 := by
          simpa [st_raw, st, lastResortUses] using hact.2.1
        have hwf_raw : PqxdhPartyInSpecDomain W st_raw := (wfPq_step_r3 hact.1 hstep hlr_le).1
        have hwf_g1 : PqxdhPartyInSpecDomain W { d1 with session := some (x, g1) } := by
          have hd1_peer : d1.peerId = some idA := hst_peer
          have hst_eq : st_raw = { d1 with session := some (x, { g with session := s_dec }) } := by
            dsimp only [st_raw, st]; rw [hd1_peer]
          rw [hst_eq] at hwf_raw
          refine ⟨?_, ?_, hwf_raw.2.2.1, hwf_raw.2.2.2.1, hwf_raw.2.2.2.2.1, hwf_raw.2.2.2.2.2⟩
          · intro x' g' hs'
            simp only [Option.some.injEq, Prod.mk.injEq] at hs'
            rcases hs' with ⟨rfl, rfl⟩
            obtain ⟨⟨g₀', hR₀', hp₀', hs₀'⟩, _, hrec_len⟩ :=
              hwf_raw.1 x { g with session := s_dec } rfl
            refine ⟨⟨g₀', hR₀', hp₀'.trans hp_props.1.symm, hs₀'.trans hg1_sess.symm⟩,
              (hp_props.1.trans hp).trans hb1_p.1.symm, ?_⟩
            simpa [encodeRecordUnderExtras, hg1_sess] using hrec_len
          · intro f hf
            have henc : encodeDir W { d1 with session := some (x, g1) } =
                encodeDir W { d1 with session := some (x, { g with session := s_dec }) } := by
              unfold encodeDir encodeRecordUnderExtras; simp [hg1_sess]
            rw [henc] at hf
            exact hwf_raw.2.1 f hf
        refine ⟨hp_props.1.trans hp, ?_, hp_props.2.1, hrem1, hwf_g1, ?_,
          hp_props.2.2.2.2.2.1, ?_⟩
        · rcases hp_props.2.2.2.1 with hep_eq | hep_eq <;> omega
        · simpa [lastResortUses] using hact.2.1
        · exact pqLength_le_286196_of_wfPq hwf_g1

private theorem cliPqRecv_prekey_matched_spec {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hspec : CliSpecPqxdh run X W)
    (bi : ModelDriverInstance S ℓ) (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (x : RecordExtras) (g : GhostState Bytes) (q_rem : ℕ)
    (c : Bytes) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hact : CliPartyActiveInv W (cliPqxdhDirBobAfterAccept bi sigs) x g q_rem)
    (_hq : 0 < q_rem)
    (hp : g.party = .B)
    (hep : 0 < g.epoch)
    (hx : x.aliceBaseKey = djbKey (u8Vec 32 bi.hdr.ekAPk))
    (hidA : idA = bhIdKeyOf bi.hdr.ikAPk)
    (hrem : g.session.remoteIdentity = some idA)
    (hdec_c : bhDecodePreKeyMsgE c = some m)
    (hhdr : (bhHdrOfPreKeyMsg m == bi.hdr) = true)
    (hlen : m.inner.length + 2048 < 2 ^ 32)
    (hcap : c.length ≤ stdinCapBytes) :
    let sB := binStateOfUnderExtras (fun _ => x) g
    let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) idA idB
    (cliPqScheme run W ℓ bi sigs bi.stA0 bi.stB0).receive sB c rc =
      ((sessionSchemeFixedSpk P_v1 ℓ spkCoins).receive g m.inner rc).map
        (fun (g', t, idx, pt) => (binStateOfUnderExtras (fun _ => x) g', t, idx, pt)) ∧
    (∀ g' t idx pt,
      (sessionSchemeFixedSpk P_v1 ℓ spkCoins).receive g m.inner rc = some (g', t, idx, pt) →
      g'.party = .B ∧
      0 < g'.epoch ∧
      g'.session.pendingPreKey = false ∧
      g'.session.remoteIdentity = some idA ∧
      CliPartyActiveInv W (cliPqxdhDirBobAfterAccept bi sigs) x g' (q_rem - 1)) := by
  intro sB P_v1
  set d1 := cliPqxdhDirBobAfterAccept bi sigs
  set st := { d1 with session := some (x, g) }
  have hb1_p := cliPqDirB1_props bi sigs
  have hst_party : st.party = .B := hb1_p.1
  have hhdr_eq : bhHdrOfPreKeyMsg m = bi.hdr := beq_iff_eq.mp hhdr
  have hm_bk : m.baseKey = u8Vec 32 bi.hdr.ekAPk := by
    rw [← hhdr_eq]; exact (u8Vec_vecU8 m.baseKey).symm
  have hm_idA : (⟨⟨m.idPub⟩⟩ : IdentityKey) = idA := by
    rw [hidA, ← hhdr_eq]; simp [bhHdrOfPreKeyMsg, bhIdKeyOf, u8Vec_vecU8]
  have hst_peer : st.peerId = some ⟨⟨m.idPub⟩⟩ := by
    change d1.peerId = some ⟨⟨m.idPub⟩⟩
    rw [hm_idA, hidA]; exact hb1_p.2.2.1
  have hst_trust : st.trusts ⟨⟨m.idPub⟩⟩ = true := by
    unfold PqParty.trusts
    rw [hst_peer]; simp
  obtain ⟨⟨g₀, hR₀, _, hsess₀⟩, _, _⟩ := hact.1.1 x g rfl
  have hrc_len : g.session.receiverChains.length ≤ maxReceiverChains := by
    rw [← hsess₀]; exact (reachPq_invCli hR₀).receiverChains_len
  have hver4 : g.session.sessionVersion = 4 := by
    rw [← hsess₀]; exact (reachPq_invCli hR₀).sessionVersion_eq
  have hmatch : PqSessionMatches x g m := ⟨hx.trans (congrArg djbKey hm_bk.symm), hver4⟩
  have hrem_m : g.session.remoteIdentity = some ⟨⟨m.idPub⟩⟩ := by rw [hm_idA]; exact hrem
  obtain ⟨hc_wire, _⟩ := bhDecodePreKeyMsgE_eq_some_imp hdec_c
  have hcomm := cliPqRecvPrekeyMatchingDir_eq_paramsPqBIds_receive (X := X) hspec st hact.1
    idA idB x g m rfl hact.2.2.1 hrc_len (hp.trans hst_party.symm) hmatch hrem_m hst_trust rc hlen (hc_wire ▸ hcap)
  rw [← paramsIdsWithSpqr_eq_paramsPqBIds W idA idB] at hcomm
  have hsB_empty : sB.bytes.isEmpty = false := encodeRecordX_isEmpty_eq_false (fun _ => x) g
  have hsB_party : sB.party = .B := hp
  have hinp_eq : cliPqInputs W (cliPqDirOf bi sigs sB) sB.bytes
      (.recv (partyAddress Party.B.other)) [] (HMAC.keyToBytes32 rc) c =
      cliPqRecvInputsFromFiles st.party (encodeDir W st) (wirePrekey :: m.bytes) rc := by
    have hd_of : cliPqDirOf bi sigs sB = d1 := by
      simp [cliPqDirOf, hsB_party, hsB_empty, d1]
    rw [hd_of, ← hb1_p.1]
    have h1 := cliPqInputs_recv_eq_cliPqRecvInputsFromFiles W d1 st sB.bytes c rc rfl
      (cliPqDirRawSpec_encodeRecordX_eq_encodeDir W d1 x g)
    rw [h1, hc_wire]
  have hpart1 : (cliPqScheme run W ℓ bi sigs bi.stA0 bi.stB0).receive sB c rc =
      ((sessionSchemeFixedSpk P_v1 ℓ spkCoins).receive g m.inner rc).map
        (fun (g', t, idx, pt) => (binStateOfUnderExtras (fun _ => x) g', t, idx, pt)) := by
    change cliPqReceive run W ℓ bi sigs sB c rc = _
    unfold cliPqReceive
    dsimp only
    have hlen_ok : cliPqLenOk c = true := cliPqLenOk_of_decode_some hdec_c hlen
    have hsB_ep : (sB.bytes.isEmpty || sB.epochs.epoch == 0) = false := by
      have hsB_ep_val : sB.epochs.epoch = g.epoch := rfl
      simp [hsB_empty, hsB_ep_val, Nat.ne_of_gt hep]
    have hwire_in : bhWireInnerBytes c = some m.inner := bhWireInnerBytes_of_decode_some hdec_c
    simp only [hlen_ok, hsB_party, hdec_c, hsB_ep, hhdr, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, cliPqRecv, hwire_in]
    rw [hinp_eq]
    dsimp only [sessionSchemeFixedSpk]
    rcases hrec : P_v1.receive g m.inner rc with _ | ⟨g', t, idx, pt⟩
    · rw [hrec] at hcomm
      simp only [Option.map_none] at hcomm ⊢
      unfold cliPqRecvPrekeyMatchingDir cliDirStateOf at hcomm
      rcases hrun : run (cliPqRecvInputsFromFiles st.party (encodeDir W st) (wirePrekey :: m.bytes) rc) with
        _ | out
      · rfl
      · cases out with
        | aborted => rfl
        | exited code stdout fs =>
          cases code with
          | zero =>
            rw [hrun] at hcomm
            rcases htf0 : SignalMessage.tryFrom protoSignalCodec m.inner with _ | _ <;>
              simp [htf0] at hcomm
          | succ n => rfl
    · rw [hrec] at hcomm
      simp only [Option.map_some] at hcomm ⊢
      have hrec' := hrec
      unfold Params.receive at hrec'
      rcases htf : SignalMessage.tryFrom P_v1.codec m.inner with _ | msg
      · rw [htf] at hrec'; simp at hrec'
      · have htf_p : SignalMessage.tryFrom protoSignalCodec m.inner = .ok msg := htf
        unfold cliPqRecvPrekeyMatchingDir cliDirStateOf at hcomm
        rcases hrun : run (cliPqRecvInputsFromFiles st.party (encodeDir W st) (wirePrekey :: m.bytes) rc) with
          _ | out
        · rw [hrun] at hcomm; simp at hcomm
        · cases out with
          | aborted => rw [hrun] at hcomm; simp at hcomm
          | exited code stdout fs =>
            cases code with
            | succ n => rw [hrun] at hcomm; simp at hcomm
            | zero =>
              rw [hrun, htf_p] at hcomm
              simp only [Option.some.injEq, Prod.mk.injEq] at hcomm
              rcases hcomm with ⟨hds_eq, ht_eq, hidx_eq, rfl⟩
              have hrb : readBackDir (pqPartyCandidatePathsOf st) fs =
                  encodeDir W { st with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, g') } :=
                congrArg CliDirState.dirFiles hds_eq
              have hep_eq : (EpochGhost.ofGhost g).recv msg.senderRatchetKey =
                  (t, EpochGhost.ofGhost g') := by
                have he1 : ((EpochGhost.ofGhost g).recv msg.senderRatchetKey).2 = EpochGhost.ofGhost g' := by
                  simpa using congrArg CliDirState.epochs hds_eq
                exact Prod.ext ht_eq he1
              have hlkp := lookup_sessionFile_encodeDir_B W
                { st with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, g') }
                ⟨⟨m.idPub⟩⟩ x g' hst_party rfl rfl
              rw [← hrb] at hlkp
              have hfs := lookup_readBackDir_some hlkp
              have hsB_ep_eq : sB.epochs = EpochGhost.ofGhost g := rfl
              have hg'_party : g'.party = .B := (params_receive_party P_v1 g g' m.inner rc hrec).trans hp
              have hbin_eq : BinState.mk .B (encodeRecordUnderExtras (fun _ => x) g') (EpochGhost.ofGhost g') =
                  binStateOfUnderExtras (fun _ => x) g' := by
                unfold binStateOfUnderExtras; rw [hg'_party]
              simp only [cliPqAfter, Party.other, hfs, Option.getD_some, Option.map_some,
                htf_p, hsB_ep_eq, hep_eq, hidx_eq, hbin_eq]
  refine ⟨hpart1, fun g' t idx pt hrec_s => ?_⟩
  dsimp only [sessionSchemeFixedSpk] at hrec_s
  rcases hrec : P_v1.receive g m.inner rc with _ | ⟨g1, t1, idx1, pt1⟩
  · rw [hrec] at hrec_s; simp at hrec_s
  · rw [hrec] at hrec_s
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec_s
    rcases hrec_s with ⟨rfl, rfl, rfl, rfl⟩
    have hp_props := BhAdapterIjHelpersV1.paramsV1_receive_whisper_props W W.Q.K idA idB g m.inner rc
      hrec
      (by rw [← hsess₀]; intro rc_c hrc_c mk hmk
          exact ((reachPq_invCli hR₀).receiverChains_inv rc_c hrc_c).2.2.2 mk hmk)
      hrc_len hact.2.2.1
      (by rw [← hsess₀]; exact reachPq_validState_cli hR₀)
      (by have := hact.2.2.2; omega)
    have hrec_raw := hrec
    unfold Params.receive at hrec_raw
    rcases htf : SignalMessage.tryFrom P_v1.codec m.inner with _ | msg
    · rw [htf] at hrec_raw; simp at hrec_raw
    · rw [htf, hp] at hrec_raw; dsimp only at hrec_raw
      rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).expectedAddrs .B) msg .whisper rc g.session with ⟨err | pt_d, s_dec⟩
      · have hdec' : SessionState.tryDecryptFromRecord P_v1.C P_v1.spqr
            (P_v1.expectedAddrs .B) msg .whisper rc g.session = (.error err, s_dec) := by
          have hd : TripleRatchet.decrypt P_v1.C P_v1.spqr (P_v1.expectedAddrs .B) msg .whisper rc =
              TripleRatchet.decrypt W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs .B) msg .whisper rc := rfl
          unfold SessionState.tryDecryptFromRecord SessionState.tryDecryptWithState at hdec ⊢
          rw [hd]; exact hdec
        rw [hdec'] at hrec_raw; simp at hrec_raw
      · have hdec' : SessionState.tryDecryptFromRecord P_v1.C P_v1.spqr
            (P_v1.expectedAddrs .B) msg .whisper rc g.session = (.ok pt_d, s_dec) := by
          have hd : TripleRatchet.decrypt P_v1.C P_v1.spqr (P_v1.expectedAddrs .B) msg .whisper rc =
              TripleRatchet.decrypt W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs .B) msg .whisper rc := rfl
          unfold SessionState.tryDecryptFromRecord SessionState.tryDecryptWithState at hdec ⊢
          rw [hd]; exact hdec
        rw [hdec'] at hrec_raw
        simp only [Option.some.injEq, Prod.mk.injEq] at hrec_raw
        have hg1_sess : g1.session = s_dec := by rw [← hrec_raw.1]
        have hs_rem : s_dec.remoteIdentity = some idA := by
          have hvr := (Closure.Version.tryDecryptFromRecord_sessionVersion_remoteIdentity
            W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs .B) msg .whisper rc g.session).2
          rw [hdec, hrem] at hvr; exact hvr
        have hrem1 : g1.session.remoteIdentity = some idA := hg1_sess ▸ hs_rem
        let st_raw : PqParty := { st with peerId := some idA, session := some (x, { g with session := s_dec }) }
        have hmod : pqRecvWhisperModel W st m.inner rc = some (some (st_raw, pt_d)) := by
          have htf_p : SignalMessage.tryFrom protoSignalCodec m.inner = .ok msg := htf
          have hst_trust_idA : (!st.trusts idA) = false := by rw [← hm_idA]; simp [hst_trust]
          simp [pqRecvWhisperModel, pqxdhSessionDecryptModel, st, htf_p, hp, hdec, hs_rem, hst_trust_idA, st_raw]
        have hstep : PqStep X W st st_raw :=
          PqStep.recvWhisper m.inner rc st_raw pt_d (by omega) hmod
        have hlr_le : lastResortUses st_raw < 2 ^ 25 := by
          simpa [st_raw, st, lastResortUses] using hact.2.1
        have hwf_raw : PqxdhPartyInSpecDomain W st_raw := (wfPq_step_r3 hact.1 hstep hlr_le).1
        have hwf_g1 : PqxdhPartyInSpecDomain W { d1 with session := some (x, g1) } := by
          have hd1_peer : d1.peerId = some idA := by rw [← hm_idA]; exact hst_peer
          have hst_eq : st_raw = { d1 with session := some (x, { g with session := s_dec }) } := by
            dsimp only [st_raw, st]; rw [hd1_peer]
          rw [hst_eq] at hwf_raw
          refine ⟨?_, ?_, hwf_raw.2.2.1, hwf_raw.2.2.2.1, hwf_raw.2.2.2.2.1, hwf_raw.2.2.2.2.2⟩
          · intro x' g' hs'
            simp only [Option.some.injEq, Prod.mk.injEq] at hs'
            rcases hs' with ⟨rfl, rfl⟩
            obtain ⟨⟨g₀', hR₀', hp₀', hs₀'⟩, _, hrec_len⟩ :=
              hwf_raw.1 x { g with session := s_dec } rfl
            refine ⟨⟨g₀', hR₀', hp₀'.trans hp_props.1.symm, hs₀'.trans hg1_sess.symm⟩,
              (hp_props.1.trans hp).trans hb1_p.1.symm, ?_⟩
            simpa [encodeRecordUnderExtras, hg1_sess] using hrec_len
          · intro f hf
            have henc : encodeDir W { d1 with session := some (x, g1) } =
                encodeDir W { d1 with session := some (x, { g with session := s_dec }) } := by
              unfold encodeDir encodeRecordUnderExtras; simp [hg1_sess]
            rw [henc] at hf
            exact hwf_raw.2.1 f hf
        refine ⟨hp_props.1.trans hp, ?_, hp_props.2.1, hrem1, hwf_g1, ?_,
          hp_props.2.2.2.2.2.1, ?_⟩
        · rcases hp_props.2.2.2.1 with hep_eq | hep_eq <;> omega
        · simpa [lastResortUses] using hact.2.1
        · exact pqLength_le_286196_of_wfPq hwf_g1

/-! ## `L_bh` SM query unfolding -/

private theorem cliE2EDrvImplWith_run_sm {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σ_e2e : BHE2EDrvState S ℓ) :
    (cliE2EDrvImplWith P ki C K qep decT encT (.inr (.inr ⟨i, sq⟩))).run σ_e2e =
      (do
        let (sr, σ_e2e') ← bhE2EStepLocalSm C K qep decT encT σ_e2e i sq
        return (bhUnpackSmResp sq sr, σ_e2e')) := by
  unfold cliE2EDrvImplWith
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set,
    StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]

private theorem simulateQ_cliE2EDrvImplWith_sm_bind {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (k : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ_e2e : BHE2EDrvState S ℓ) :
    (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
      ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query (.inr (.inr ⟨i, sq⟩))) :
        OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _) >>= k)).run σ_e2e =
    (bhE2EStepLocalSm C K qep decT encT σ_e2e i sq >>= fun (sr, σ_e2e') =>
      (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT) (k (bhUnpackSmResp sq sr))).run σ_e2e') := by
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_query, OracleSpec.query_def]
  dsimp [OracleQuery.cont, OracleQuery.input]
  rw [id_map, cliE2EDrvImplWith_run_sm]
  simp only [bind_assoc, pure_bind]

private def cliBobAdapterUpdate {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (_decT : PublicKey → Option Pt) (_encT : Pt → PublicKey)
    (inst : BHAdapterInstMeta S) (c : Bytes)
    (σ_ad : CliAdapterState S) (i : ℕ) (optRr : Option (SM.RecvResult (Plain ℓ))) :
    CliAdapterState S :=
  match optRr with
  | some (.accepted _ _ _) =>
    let inst' := (bhShallowUpdateInstMeta inst false true c).2
    ((fun j => if j = i then some inst' else σ_ad.1 j), σ_ad.2)
  | _ => σ_ad

private def cliAliceAdapterUpdatePriv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ_ad : CliAdapterState S) (i : ℕ) (optRr : Option (SM.RecvResult (Plain ℓ))) :
    CliAdapterState S :=
  match optRr with
  | some (.accepted _ _ _) => (σ_ad.1, (fun j => if j = i then true else σ_ad.2.1 j), σ_ad.2.2)
  | _ => σ_ad

private theorem cliComposedAdapterImplWith_cr_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (p : Party) (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT (.inr ⟨i, .inr p⟩)).run σ_ad).run σ_e2e) =
      match σ_ad.1 i with
      | none => pure ((none, σ_ad), σ_e2e)
      | some inst =>
        do
          let (sr, σ_e2e') ← bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inr p)
          match sr.2.2 with
          | none => return ((none, σ_ad), σ_e2e')
          | some g => return ((some (bhBinStateOfParty inst g), σ_ad), σ_e2e') := by
  have hHandle :
      ((bhShallowAdapterImpl S ℓ (BitVec 512) (.inr (.inr ⟨i, .inr p⟩))).run σ_ad) =
      match σ_ad.1 i with
      | none => pure (none, σ_ad)
      | some inst =>
        ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
            (.inr (.inr ⟨i, .inr p⟩))) :
            OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (Option (GhostState Bytes))) >>=
          fun optG =>
            match optG with
            | none => pure (none, σ_ad)
            | some g => pure (some (bhBinStateOfParty inst g), σ_ad)) := by
    dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget]
    rcases σ_ad.1 i with _ | inst
    · rfl
    · dsimp only; congr 1; funext x; cases x <;> rfl
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inr p⟩))).run σ_ad)).run σ_e2e = _
  rw [hHandle]
  rcases σ_ad.1 i with _ | inst
  · simp only [simulateQ_pure, StateT.run_pure]
  · dsimp only
    rw [simulateQ_cliE2EDrvImplWith_sm_bind]
    congr 1; funext ⟨sr, σ_e2e'⟩
    rcases sr with ⟨_, _, _ | g⟩ <;> simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]

private theorem cliComposedAdapterImplWith_tr_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (p : Party) (m : Plain ℓ) (r : Option (BitVec 512))
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩)).run σ_ad).run σ_e2e) =
      match σ_ad.1 i with
      | none => pure ((none, σ_ad), σ_e2e)
      | some inst =>
        do
          let (sr, σ_e2e') ←
            bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inl (.inl (p, m, r)))))
          match sr.1 with
          | none => return ((none, σ_ad), σ_e2e')
          | some ct =>
            let wire :=
              if SM.partyEnc p then
                if ct.isEmpty then [] else wireWhisper :: ct
              else if σ_ad.2.1 i then
                if ct.isEmpty then [] else wireWhisper :: ct
              else bhWrapSendOut inst .A ct
            return ((some wire, σ_ad), σ_e2e') := by
  have hHandle :
      ((bhShallowAdapterImpl S ℓ (BitVec 512)
        (.inr (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩))).run σ_ad) =
      match σ_ad.1 i with
      | none => pure (none, σ_ad)
      | some inst =>
        ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
            (.inr (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩))) :
            OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (Option Bytes)) >>=
          fun optCt =>
            match optCt with
            | none => pure (none, σ_ad)
            | some ct =>
              let wire :=
                if SM.partyEnc p then
                  if ct.isEmpty then [] else wireWhisper :: ct
                else if σ_ad.2.1 i then
                  if ct.isEmpty then [] else wireWhisper :: ct
                else bhWrapSendOut inst .A ct
              pure (some wire, σ_ad)) := by
    dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget, bhShallowWrapWhisper]
    rcases σ_ad.1 i with _ | inst
    · rfl
    · dsimp only; congr 1; funext x; cases x <;> rfl
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩))).run σ_ad)).run σ_e2e = _
  rw [hHandle]
  rcases σ_ad.1 i with _ | inst
  · simp only [simulateQ_pure, StateT.run_pure]
  · dsimp only
    rw [simulateQ_cliE2EDrvImplWith_sm_bind]
    congr 1; funext ⟨sr, σ_e2e'⟩
    rcases sr with ⟨_ | ct, _, _⟩ <;> simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]

private theorem cliComposedAdapterImplWith_ch_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (p : Party) (m0 m1 : Plain ℓ) (r : Option (BitVec 512))
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩)).run σ_ad).run σ_e2e) =
      match σ_ad.1 i with
      | none => pure ((none, σ_ad), σ_e2e)
      | some inst =>
        do
          let (sr, σ_e2e') ←
            bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inl (.inr (p, m0, m1, r)))))
          match sr.1 with
          | none => return ((none, σ_ad), σ_e2e')
          | some ct =>
            let wire :=
              if SM.partyEnc p then
                if ct.isEmpty then [] else wireWhisper :: ct
              else if σ_ad.2.1 i then
                if ct.isEmpty then [] else wireWhisper :: ct
              else bhWrapSendOut inst .A ct
            return ((some wire, σ_ad), σ_e2e') := by
  have hHandle :
      ((bhShallowAdapterImpl S ℓ (BitVec 512)
        (.inr (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩))).run σ_ad) =
      match σ_ad.1 i with
      | none => pure (none, σ_ad)
      | some inst =>
        ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
            (.inr (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩))) :
            OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (Option Bytes)) >>=
          fun optCt =>
            match optCt with
            | none => pure (none, σ_ad)
            | some ct =>
              let wire :=
                if SM.partyEnc p then
                  if ct.isEmpty then [] else wireWhisper :: ct
                else if σ_ad.2.1 i then
                  if ct.isEmpty then [] else wireWhisper :: ct
                else bhWrapSendOut inst .A ct
              pure (some wire, σ_ad)) := by
    dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget, bhShallowWrapWhisper]
    rcases σ_ad.1 i with _ | inst
    · rfl
    · dsimp only; congr 1; funext x; cases x <;> rfl
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩))).run σ_ad)).run σ_e2e = _
  rw [hHandle]
  rcases σ_ad.1 i with _ | inst
  · simp only [simulateQ_pure, StateT.run_pure]
  · dsimp only
    rw [simulateQ_cliE2EDrvImplWith_sm_bind]
    congr 1; funext ⟨sr, σ_e2e'⟩
    rcases sr with ⟨_ | ct, _, _⟩ <;> simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]

private theorem cliComposedAdapterImplWith_dl_A_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (c : Bytes) (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inr (.A, c)))⟩)).run σ_ad).run σ_e2e) =
      match c with
      | [] =>
        do
          let (sr, σ_e2e') ←
            bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inr (.A, []))))
          return ((sr.2.1, σ_ad), σ_e2e')
      | t :: body =>
        if t == wireWhisper then
          match body with
          | [] => pure ((none, σ_ad), σ_e2e)
          | b :: bs =>
            do
              let (sr, σ_e2e') ←
                bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inr (.A, b :: bs))))
              return ((sr.2.1, cliAliceAdapterUpdatePriv σ_ad i sr.2.1), σ_e2e')
        else pure ((none, σ_ad), σ_e2e) := by
  have hHandle :
      ((bhShallowAdapterImpl S ℓ (BitVec 512)
        (.inr (.inr ⟨i, .inl (.inl (.inr (.A, c)))⟩))).run σ_ad) =
      match c with
      | [] =>
        ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
            (.inr (.inr ⟨i, .inl (.inl (.inr (.A, [])))⟩))) :
            OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
              (Option (SM.RecvResult (Plain ℓ)))) >>=
          fun optRr => pure (optRr, σ_ad))
      | t :: body =>
        if t == wireWhisper then
          match body with
          | [] => pure (none, σ_ad)
          | b :: bs =>
            ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
                (.inr (.inr ⟨i, .inl (.inl (.inr (.A, b :: bs)))⟩))) :
                OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                  (Option (SM.RecvResult (Plain ℓ)))) >>=
              fun optRr => pure (optRr, cliAliceAdapterUpdatePriv σ_ad i optRr))
        else pure (none, σ_ad) := by
    dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
      bhShallowWrapWhisper, bhShallowSplitWhisper, bhShallowAliceUpdate, cliAliceAdapterUpdatePriv]
    rcases c with _ | ⟨t, body⟩
    · rfl
    · dsimp only
      cases t == wireWhisper
      · simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons, BEq.rfl]
      · rcases body with _ | ⟨b, bs⟩
        · simp only [↓reduceIte, List.isEmpty_nil]
        · simp only [↓reduceIte, List.isEmpty_cons, Bool.false_eq_true, BEq.rfl]; rfl
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inl (.inr (.A, c)))⟩))).run σ_ad)).run σ_e2e = _
  rw [hHandle]
  rcases c with _ | ⟨t, body⟩
  · dsimp only
    rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
  · dsimp only
    cases t == wireWhisper
    · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_pure, StateT.run_pure]
    · rcases body with _ | ⟨b, bs⟩
      · simp only [↓reduceIte, simulateQ_pure, StateT.run_pure]
      · simp only [↓reduceIte]
        rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1

set_option linter.unusedSimpArgs false in
private theorem cliComposedAdapterImplWith_ij_A_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (c : Bytes) (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inr (.A, c))⟩)).run σ_ad).run σ_e2e) =
      match (match c with | t :: body => if t == wireWhisper then some body else none | [] => none) with
      | none => pure ((none, σ_ad), σ_e2e)
      | some body =>
        if decide (c.length ≤ stdinCapBytes) && shortCiphertext c then
          match bhDecodePreKeyMsgE body with
          | some _ =>
            do
              let (sr, σ_e2e') ←
                bhE2EStepLocalSm C K qep decT encT σ_e2e i
                  (.inl (.inr (.A, if body.isEmpty then [] else wireWhisper :: body)))
              return ((sr.2.1, cliAliceAdapterUpdatePriv σ_ad i sr.2.1), σ_e2e')
          | none =>
            if body.isEmpty then
              do
                let (sr, σ_e2e') ←
                  bhE2EStepLocalSm C K qep decT encT σ_e2e i
                    (.inl (.inr (.A, if c.isEmpty then [] else wireWhisper :: c)))
                return ((sr.2.1, σ_ad), σ_e2e')
            else
              do
                let (sr, σ_e2e') ←
                  bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.A, body)))
                return ((sr.2.1, cliAliceAdapterUpdatePriv σ_ad i sr.2.1), σ_e2e')
        else pure ((none, σ_ad), σ_e2e) := by
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inr (.A, c))⟩))).run σ_ad)).run σ_e2e = _
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
    bhShallowWrapWhisper, bhShallowSplitWhisper, bhShallowParsePreKey,
    bhShallowAliceUpdate, cliAliceAdapterUpdatePriv]
  rcases c with _ | ⟨t, body⟩
  · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte, Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
  · dsimp only
    cases t == wireWhisper
    · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte, Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
    · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte, Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      cases (decide ((t :: body).length ≤ stdinCapBytes) && shortCiphertext (t :: body))
      · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte, Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte, Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
        rcases bhDecodePreKeyMsgE body with _ | m
        · rcases body with _ | ⟨b0, bs⟩
          · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte, Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
            rw [simulateQ_cliE2EDrvImplWith_sm_bind]
            congr 1
          · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte, Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
            rw [simulateQ_cliE2EDrvImplWith_sm_bind]
            congr 1
        · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte, Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
          rw [simulateQ_cliE2EDrvImplWith_sm_bind]
          congr 1

private theorem cliComposedAdapterImplWith_dl_B_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (c : Bytes) (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inr (.B, c)))⟩)).run σ_ad).run σ_e2e) =
      match σ_ad.1 i with
      | none => pure ((none, σ_ad), σ_e2e)
      | some inst =>
        match bhDecodePreKeyMsgE c with
        | some m =>
          match m.inner with
          | [] =>
            do
              let (_, σ_e2e') ←
                bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, [])))
              return ((none, σ_ad), σ_e2e')
          | _ :: _ =>
            do
              let (sr, σ_e2e') ←
                bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inr (.B, c))))
              return ((sr.2.1, cliBobAdapterUpdate decT encT inst c σ_ad i sr.2.1), σ_e2e')
        | none =>
          match c with
          | [] =>
            do
              let (_, σ_e2e') ←
                bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, [])))
              return ((none, σ_ad), σ_e2e')
          | t :: body =>
            if t == wireWhisper then
              match bhDecodePreKeyMsgE body with
              | some _ =>
                do
                  let (_, σ_e2e') ←
                    bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, t :: body)))
                  return ((none, σ_ad), σ_e2e')
              | none =>
                match body with
                | [] =>
                  do
                    let (_, σ_e2e') ←
                      bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, [])))
                    return ((none, σ_ad), σ_e2e')
                | b :: bs =>
                  do
                    let (sr, σ_e2e') ←
                      bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inr (.B, b :: bs))))
                    return ((sr.2.1, σ_ad), σ_e2e')
            else
              do
                let (_, σ_e2e') ←
                  bhE2EStepLocalSm C K qep decT encT σ_e2e i
                    (.inl (.inr (.B, wireWhisper :: t :: body)))
                return ((none, σ_ad), σ_e2e') := by
  have hHandle :
      ((bhShallowAdapterImpl S ℓ (BitVec 512)
        (.inr (.inr ⟨i, .inl (.inl (.inr (.B, c)))⟩))).run σ_ad) =
      match σ_ad.1 i with
      | none => pure (none, σ_ad)
      | some inst =>
        match bhDecodePreKeyMsgE c with
        | some m =>
          match m.inner with
          | [] =>
            ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
                (.inr (.inr ⟨i, .inl (.inr (.B, []))⟩))) :
                OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                  (Option (SM.RecvResult (Plain ℓ)))) >>=
              fun _ => pure (none, σ_ad))
          | _ :: _ =>
            ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
                (.inr (.inr ⟨i, .inl (.inl (.inr (.B, c)))⟩))) :
                OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                  (Option (SM.RecvResult (Plain ℓ)))) >>=
              fun optRr => pure (optRr, cliBobAdapterUpdate decT encT inst c σ_ad i optRr))
        | none =>
          match c with
          | [] =>
            ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
                (.inr (.inr ⟨i, .inl (.inr (.B, []))⟩))) :
                OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                  (Option (SM.RecvResult (Plain ℓ)))) >>=
              fun _ => pure (none, σ_ad))
          | t :: body =>
            if t == wireWhisper then
              match bhDecodePreKeyMsgE body with
              | some _ =>
                ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
                    (.inr (.inr ⟨i, .inl (.inr (.B, t :: body))⟩))) :
                    OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                      (Option (SM.RecvResult (Plain ℓ)))) >>=
                  fun _ => pure (none, σ_ad))
              | none =>
                match body with
                | [] =>
                  ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
                      (.inr (.inr ⟨i, .inl (.inr (.B, []))⟩))) :
                      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                        (Option (SM.RecvResult (Plain ℓ)))) >>=
                    fun _ => pure (none, σ_ad))
                | b :: bs =>
                  ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
                      (.inr (.inr ⟨i, .inl (.inl (.inr (.B, b :: bs)))⟩))) :
                      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                        (Option (SM.RecvResult (Plain ℓ)))) >>=
                    fun optRr => pure (optRr, σ_ad))
            else
              ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
                  (.inr (.inr ⟨i, .inl (.inr (.B, wireWhisper :: t :: body))⟩))) :
                  OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
                    (Option (SM.RecvResult (Plain ℓ)))) >>=
                fun _ => pure (none, σ_ad)) := by
    dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
      bhShallowWrapWhisper, bhShallowSplitWhisper, bhShallowParsePreKey,
      bhShallowBobUpdate, cliBobAdapterUpdate]
    rcases σ_ad.1 i with _ | inst
    · rfl
    · rcases bhDecodePreKeyMsgE c with _ | m
      · rcases c with _ | ⟨t, body⟩
        · rfl
        · dsimp only
          cases t == wireWhisper
          · simp only [Option.map_none, Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons]; rfl
          · simp only [Option.map_none, ↓reduceIte]
            rcases bhDecodePreKeyMsgE body with _ | m2
            · rcases body with _ | ⟨b, bs⟩
              · rfl
              · rfl
            · rfl
      · simp only [Option.map_some]
        rcases m.inner with _ | ⟨x, xs⟩
        · rfl
        · rfl
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inl (.inr (.B, c)))⟩))).run σ_ad)).run σ_e2e = _
  rw [hHandle]
  rcases σ_ad.1 i with _ | inst
  · simp only [simulateQ_pure, StateT.run_pure]
  · dsimp only
    rcases bhDecodePreKeyMsgE c with _ | m
    · rcases c with _ | ⟨t, body⟩
      · dsimp only
        rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
      · dsimp only
        cases t == wireWhisper
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
        · simp only [↓reduceIte]
          rcases bhDecodePreKeyMsgE body with _ | m2
          · rcases body with _ | ⟨b, bs⟩
            · dsimp only
              rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
            · dsimp only
              rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
          · dsimp only
            rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
    · dsimp only
      rcases m.inner with _ | ⟨x, xs⟩
      · dsimp only
        rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
      · dsimp only
        rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1

set_option linter.unusedSimpArgs false in
private theorem cliComposedAdapterImplWith_ij_B_nil {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inr (.B, []))⟩)).run σ_ad).run σ_e2e) =
      match bhDecodePreKeyMsgE [] with
      | none =>
        do
          let (_, σ_e2e') ←
            bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, [])))
          return ((none, σ_ad), σ_e2e')
      | some m =>
        if decide (([] : Bytes).length ≤ stdinCapBytes) && shortCiphertext [] &&
            decide (m.inner.length + 2048 < 2 ^ 32) then
          let cq : Bytes :=
            match σ_ad.1 i with
            | none => []
            | some inst =>
              if m.inner.isEmpty &&
                  (bhShallowUpdateInstMeta inst false false []).1 then []
              else []
          do
            let (sr, σ_e2e') ←
              bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, cq)))
            return ((sr.2.1, σ_ad), σ_e2e')
        else
          do
            let (_, σ_e2e') ←
              bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, [])))
            return ((none, σ_ad), σ_e2e') := by
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inr (.B, []))⟩))).run σ_ad)).run σ_e2e = _
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
    bhShallowWrapWhisper, bhShallowSplitWhisper, bhShallowParsePreKey]
  have hdec : bhDecodePreKeyMsgE ([] : Bytes) = none := by unfold bhDecodePreKeyMsgE; rfl
  simp only [hdec]
  simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte,
    Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
    Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
  rw [simulateQ_cliE2EDrvImplWith_sm_bind]
  congr 1

set_option linter.unusedSimpArgs false in
private theorem cliComposedAdapterImplWith_ij_B_nonwhisper {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (t : BitVec 8) (body : Bytes) (ht : (t == wireWhisper) = false)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inr (.B, t :: body))⟩)).run σ_ad).run σ_e2e) =
      match bhDecodePreKeyMsgE (t :: body) with
      | none =>
        do
          let (_, σ_e2e') ←
            bhE2EStepLocalSm C K qep decT encT σ_e2e i
              (.inl (.inr (.B, wireWhisper :: t :: body)))
          return ((none, σ_ad), σ_e2e')
      | some m =>
        if decide ((t :: body).length ≤ stdinCapBytes) && shortCiphertext (t :: body) &&
            decide (m.inner.length + 2048 < 2 ^ 32) then
          let cq : Bytes :=
            match σ_ad.1 i with
            | none => t :: body
            | some inst =>
              if m.inner.isEmpty &&
                  (bhShallowUpdateInstMeta inst false false (t :: body)).1 then
                wireWhisper :: t :: body
              else t :: body
          do
            let (sr, σ_e2e') ←
              bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, cq)))
            return ((sr.2.1, σ_ad), σ_e2e')
        else
          do
            let (_, σ_e2e') ←
              bhE2EStepLocalSm C K qep decT encT σ_e2e i
                (.inl (.inr (.B, wireWhisper :: t :: body)))
            return ((none, σ_ad), σ_e2e') := by
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inr (.B, t :: body))⟩))).run σ_ad)).run σ_e2e = _
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
    bhShallowWrapWhisper, bhShallowSplitWhisper, bhShallowParsePreKey, bhShallowUpdateInstMeta]
  simp (config := {failIfUnchanged := false}) only [ht, Bool.false_eq_true, ↓reduceIte,
    Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
    Bool.and_true, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
    simulateQ_pure, StateT.run_pure, map_pure]
  rcases Option.eq_none_or_eq_some (bhDecodePreKeyMsgE (t :: body)) with hdec | ⟨m, hdec⟩
  · simp only [hdec]
    simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte,
      Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
      Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
    rw [simulateQ_cliE2EDrvImplWith_sm_bind]
    congr 1
  · simp only [hdec, Option.map_some]
    cases (decide ((t :: body).length ≤ stdinCapBytes) && shortCiphertext (t :: body) &&
        decide (m.inner.length + 2048 < 2 ^ 32))
    · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte,
        Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
        Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      rw [simulateQ_cliE2EDrvImplWith_sm_bind]
      congr 1
    · simp only [↓reduceIte]
      rcases hσ : σ_ad.1 i with _ | inst
      · simp only [hσ]
        simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte,
          Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
          Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def,
          bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
        rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
      · simp only [hσ]
        rcases hin : m.inner with _ | ⟨x0, xs⟩
        all_goals rcases Bool.eq_false_or_eq_true inst.bobAccepted with hb | hb
        all_goals (simp (config := {failIfUnchanged := false}) only [hin, hb, Bool.not_false,
          Bool.not_true, Bool.true_and, Bool.and_eq_true, ite_and, List.isEmpty_nil,
          List.isEmpty_cons, Bool.false_and, beq_self_eq_true, ↓reduceIte, Option.map_some,
          Option.map_none, Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp,
          Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure])
        all_goals ((try split_ifs) <;>
          (simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte,
            Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
            Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def,
            bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure];
           rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1))

set_option linter.unusedSimpArgs false in
private theorem cliComposedAdapterImplWith_ij_B_whisper {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (t : BitVec 8) (body : Bytes) (ht : (t == wireWhisper) = true)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inr (.B, t :: body))⟩)).run σ_ad).run σ_e2e) =
      if decide ((t :: body).length ≤ stdinCapBytes) && shortCiphertext (t :: body) then
        match bhDecodePreKeyMsgE body with
        | some _ =>
          do
            let (sr, σ_e2e') ←
              bhE2EStepLocalSm C K qep decT encT σ_e2e i
                (.inl (.inr (.B, if body.isEmpty then [] else wireWhisper :: body)))
            return ((sr.2.1, σ_ad), σ_e2e')
        | none =>
          if body.isEmpty then
            do
              let (sr, σ_e2e') ←
                bhE2EStepLocalSm C K qep decT encT σ_e2e i
                  (.inl (.inr (.B, wireWhisper :: t :: body)))
              return ((sr.2.1, σ_ad), σ_e2e')
          else
            do
              let (sr, σ_e2e') ←
                bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, body)))
              return ((sr.2.1, σ_ad), σ_e2e')
      else
        do
          let (_, σ_e2e') ←
            bhE2EStepLocalSm C K qep decT encT σ_e2e i
              (.inl (.inr (.B, wireWhisper :: t :: body)))
          return ((none, σ_ad), σ_e2e') := by
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inr (.B, t :: body))⟩))).run σ_ad)).run σ_e2e = _
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
    bhShallowWrapWhisper, bhShallowSplitWhisper, bhShallowParsePreKey]
  simp (config := {failIfUnchanged := false}) only [ht, beq_self_eq_true, ↓reduceIte,
    Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
    Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
  cases (decide ((t :: body).length ≤ stdinCapBytes) && shortCiphertext (t :: body))
  · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte,
      Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
      Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
    rw [simulateQ_cliE2EDrvImplWith_sm_bind]
    congr 1
  · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte,
      Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
      Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
    rcases bhDecodePreKeyMsgE body with _ | m
    · rcases body with _ | ⟨b0, bs⟩
      · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte,
          Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
          Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def,
          bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
        rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
      · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte,
          Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
          Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def,
          bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
        rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
    · simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte,
        Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil,
        Bool.false_eq_true, Bool.and_true, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1

private theorem cliComposedAdapterImplWith_ij_B_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (c : Bytes) (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inr (.B, c))⟩)).run σ_ad).run σ_e2e) =
      match (match c with | t :: body => if t == wireWhisper then some body else none | [] => none) with
      | none =>
        match bhDecodePreKeyMsgE c with
        | none =>
          do
            let (_, σ_e2e') ←
              bhE2EStepLocalSm C K qep decT encT σ_e2e i
                (.inl (.inr (.B, if c.isEmpty then [] else wireWhisper :: c)))
            return ((none, σ_ad), σ_e2e')
        | some m =>
          if decide (c.length ≤ stdinCapBytes) && shortCiphertext c &&
              decide (m.inner.length + 2048 < 2 ^ 32) then
            let cq : Bytes :=
              match σ_ad.1 i with
              | none => c
              | some inst =>
                if m.inner.isEmpty &&
                    (bhShallowUpdateInstMeta inst false false c).1 then
                  if c.isEmpty then [] else wireWhisper :: c
                else c
            do
              let (sr, σ_e2e') ←
                bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, cq)))
              return ((sr.2.1, σ_ad), σ_e2e')
          else
            do
              let (_, σ_e2e') ←
                bhE2EStepLocalSm C K qep decT encT σ_e2e i
                  (.inl (.inr (.B, if c.isEmpty then [] else wireWhisper :: c)))
              return ((none, σ_ad), σ_e2e')
      | some body =>
        if decide (c.length ≤ stdinCapBytes) && shortCiphertext c then
          match bhDecodePreKeyMsgE body with
          | some _ =>
            do
              let (sr, σ_e2e') ←
                bhE2EStepLocalSm C K qep decT encT σ_e2e i
                  (.inl (.inr (.B, if body.isEmpty then [] else wireWhisper :: body)))
              return ((sr.2.1, σ_ad), σ_e2e')
          | none =>
            if body.isEmpty then
              do
                let (sr, σ_e2e') ←
                  bhE2EStepLocalSm C K qep decT encT σ_e2e i
                    (.inl (.inr (.B, if c.isEmpty then [] else wireWhisper :: c)))
                return ((sr.2.1, σ_ad), σ_e2e')
            else
              do
                let (sr, σ_e2e') ←
                  bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, body)))
                return ((sr.2.1, σ_ad), σ_e2e')
        else
          do
            let (_, σ_e2e') ←
              bhE2EStepLocalSm C K qep decT encT σ_e2e i
                (.inl (.inr (.B, if c.isEmpty then [] else wireWhisper :: c)))
            return ((none, σ_ad), σ_e2e') := by
  rcases c with _ | ⟨t, body⟩
  · simpa [List.isEmpty_nil] using
      cliComposedAdapterImplWith_ij_B_nil P ki C K qep decT encT i σ_ad σ_e2e
  · cases ht : (t == wireWhisper)
    · simpa [ht, List.isEmpty_cons] using
        cliComposedAdapterImplWith_ij_B_nonwhisper P ki C K qep decT encT i t body ht σ_ad σ_e2e
    · simpa [ht, List.isEmpty_cons] using
        cliComposedAdapterImplWith_ij_B_whisper P ki C K qep decT encT i t body ht σ_ad σ_e2e

private theorem cliComposedAdapterImplWith_sm_of_stepLocalSm_none {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (q : (cliGameSmSpec ℓ (BitVec 512)).Domain)
    (σ_ad : CliAdapterState S) (σ_e2e σ_e2e' : BHE2EDrvState S ℓ)
    (hStep : ∀ sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain,
      bhIsBobRecvSMQuery sq = bhIsBobRecvSMQuery q →
      bhE2EStepLocalSm C K qep decT encT σ_e2e i sq = pure ((none, none, none), σ_e2e'))
    (hCond : σ_e2e = σ_e2e' ∨ (bhIsBobRecvSMQuery q = true ∧ (σ_ad.1 i).isSome = true)) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e) =
      pure ((bhSmDefaultWithSpqr q, σ_ad), σ_e2e') := by
  rcases q with (((⟨p, m, r⟩ | ⟨p, m0, m1, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
  · rw [cliComposedAdapterImplWith_tr_run]
    rcases hCond with rfl | ⟨hbob, _⟩
    · rcases σ_ad.1 i with _ | inst
      · rfl
      · dsimp only
        rw [hStep (.inl (.inl (.inl (.inl (p, m, r))))) rfl, pure_bind]
        rfl
    · cases hbob
  · rw [cliComposedAdapterImplWith_ch_run]
    rcases hCond with rfl | ⟨hbob, _⟩
    · rcases σ_ad.1 i with _ | inst
      · rfl
      · dsimp only
        rw [hStep (.inl (.inl (.inl (.inr (p, m0, m1, r))))) rfl, pure_bind]
        rfl
    · cases hbob
  · cases p
    · rw [cliComposedAdapterImplWith_dl_A_run]
      rcases hCond with rfl | ⟨hbob, _⟩
      · rcases c with _ | ⟨t, body⟩
        · rw [hStep (.inl (.inl (.inr (.A, [])))) rfl, pure_bind]; rfl
        · dsimp only
          split
          · rcases body with _ | ⟨b, bs⟩
            · rfl
            · dsimp only
              rw [hStep (.inl (.inl (.inr (.A, b :: bs)))) rfl, pure_bind]; rfl
          · rfl
      · cases hbob
    · rw [cliComposedAdapterImplWith_dl_B_run]
      rcases hinst : σ_ad.1 i with _ | inst
      · rcases hCond with rfl | ⟨_, hisSome⟩
        · rfl
        · rw [hinst] at hisSome; cases hisSome
      · have hSdl : ∀ c' : Bytes,
            bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inr (.B, c')))) =
              pure ((none, none, none), σ_e2e') := fun c' => hStep _ rfl
        have hSij : ∀ c' : Bytes,
            bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, c'))) =
              pure ((none, none, none), σ_e2e') := fun c' => hStep _ rfl
        dsimp only
        rcases bhDecodePreKeyMsgE c with _ | m
        · rcases c with _ | ⟨t, body⟩
          · dsimp only; rw [hSij, pure_bind]; rfl
          · dsimp only
            split
            · rcases bhDecodePreKeyMsgE body with _ | _
              · rcases body with _ | ⟨b, bs⟩
                · dsimp only; rw [hSij, pure_bind]; rfl
                · dsimp only; rw [hSdl, pure_bind]; rfl
              · dsimp only; rw [hSij, pure_bind]; rfl
            · rw [hSij, pure_bind]; rfl
        · dsimp only
          rcases m.inner with _ | ⟨x, xs⟩
          · dsimp only; rw [hSij, pure_bind]; rfl
          · dsimp only; rw [hSdl, pure_bind]; rfl
  · cases p
    · rw [cliComposedAdapterImplWith_ij_A_run]
      rcases hCond with rfl | ⟨hbob, _⟩
      · have hSijA : ∀ c' : Bytes,
            bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.A, c'))) =
              pure ((none, none, none), σ_e2e) := fun c' => hStep _ rfl
        rcases c with _ | ⟨t, body⟩
        · rfl
        · cases ht : (t == wireWhisper)
          · simp only [ht]; rfl
          · simp only [ht, ↓reduceIte]
            by_cases hcap : (t :: body).length ≤ stdinCapBytes
            swap
            · simp only [decide_eq_false hcap, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
            · simp only [decide_eq_true hcap, Bool.true_and]
              cases shortCiphertext (t :: body)
              · simp only [Bool.false_eq_true, ↓reduceIte]; rfl
              · simp only [↓reduceIte]
                rcases Option.eq_none_or_eq_some (bhDecodePreKeyMsgE body) with hdec | ⟨m, hdec⟩
                · simp only [hdec]
                  cases body.isEmpty
                  · simp only [Bool.false_eq_true, ↓reduceIte]
                    rw [hSijA, pure_bind]; rfl
                  · simp only [↓reduceIte]
                    rw [hSijA, pure_bind]; rfl
                · simp only [hdec]
                  rw [hSijA, pure_bind]; rfl
      · cases hbob
    · rw [cliComposedAdapterImplWith_ij_B_run]
      have hSij : ∀ c' : Bytes,
          bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, c'))) =
            pure ((none, none, none), σ_e2e') := fun c' => hStep _ rfl
      rcases c with _ | ⟨t, body⟩
      · dsimp only
        rcases Option.eq_none_or_eq_some (bhDecodePreKeyMsgE []) with hdec | ⟨m, hdec⟩
        · simp only [hdec, List.isEmpty_nil, ↓reduceIte]; rw [hSij, pure_bind]; rfl
        · simp only [hdec, List.isEmpty_nil, ↓reduceIte]; split_ifs <;> (rw [hSij, pure_bind]; rfl)
      · dsimp only
        cases ht : (t == wireWhisper)
        · simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons]
          rcases Option.eq_none_or_eq_some (bhDecodePreKeyMsgE (t :: body)) with hdec | ⟨m, hdec⟩
          · simp only [hdec]; rw [hSij, pure_bind]; rfl
          · simp only [hdec]; split_ifs <;> (rw [hSij, pure_bind]; rfl)
        · simp only [↓reduceIte, List.isEmpty_cons, Bool.false_eq_true]
          by_cases hcap : (t :: body).length ≤ stdinCapBytes
          swap
          · simp only [decide_eq_false hcap, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            rw [hSij, pure_bind]; rfl
          · simp only [decide_eq_true hcap, Bool.true_and]
            cases shortCiphertext (t :: body)
            · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hSij, pure_bind]; rfl
            · simp only [↓reduceIte]
              rcases Option.eq_none_or_eq_some (bhDecodePreKeyMsgE body) with hdec | ⟨m, hdec⟩
              · simp only [hdec]
                cases body.isEmpty
                · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hSij, pure_bind]; rfl
                · simp only [↓reduceIte]; rw [hSij, pure_bind]; rfl
              · simp only [hdec]; rw [hSij, pure_bind]; rfl
  · rw [cliComposedAdapterImplWith_cr_run]
    rcases hCond with rfl | ⟨hbob, _⟩
    · rcases σ_ad.1 i with _ | inst
      · rfl
      · dsimp only
        rw [hStep (.inr p) rfl, pure_bind]
        rfl
    · cases hbob

/-! ## Early-exit coupling -/

open CryptoGames.LibsignalSM.Proofs.Refinement

@[simp]
private theorem stateT_lift_run_cli {m : Type → Type} [Monad m] {σ α : Type}
    (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

private theorem cliPartyActiveInv_mono_q_rem {W : PEParams} {d0 : PqParty} {x : RecordExtras}
    {g : GhostState Bytes} {q₁ q₂ : ℕ} (_hq : q₁ ≤ q₂)
    (h : CliPartyActiveInv W d0 x g q₂) :
    CliPartyActiveInv W d0 x g q₁ := h

private theorem cliAdapterInstRel_mono_q_rem {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂)
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (h : CliAdapterInstRel X W q₂ st_cli ds_cli bi d im im_e2e inst ack) :
    CliAdapterInstRel X W q₁ st_cli ds_cli bi d im im_e2e inst ack where
  im_eq := h.im_eq
  sid_eq := h.sid_eq
  hdr_eq := h.hdr_eq
  idB_eq := h.idB_eq
  respSlot_eq := h.respSlot_eq
  respMeta_eq := h.respMeta_eq
  regIdA_eq := h.regIdA_eq
  regIdB_eq := h.regIdB_eq
  aliceAcked_false := h.aliceAcked_false
  idA_pub_eq := h.idA_pub_eq
  idB_pub_eq := h.idB_pub_eq
  extrasB_eq := h.extrasB_eq
  stB0_empty := h.stB0_empty
  resp_bundle_rel := h.resp_bundle_rel
  handshake_rel := h.handshake_rel
  gs_rel := by
    have hgs := h.gs_rel
    cases h1 : bi.gs with
    | none => rw [h1] at hgs; exact hgs
    | some gs_cli =>
      cases h2 : d.gs with
      | none => rw [h1, h2] at hgs; exact hgs
      | some gs_m =>
        rw [h1, h2] at hgs
        dsimp only
        rcases hgs with ⟨hb, hrest⟩
        refine ⟨hb, ?_⟩
        split_ifs at hrest ⊢
        · exact hrest
        · rcases hrest with
            ⟨h01, h02, h03, h04, h05, h06, h07, h08, h09, h10,
             h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
             h21, h22, h23, h24, h25, h26, hactA, hactB⟩
          exact ⟨h01, h02, h03, h04, h05, h06, h07, h08, h09, h10,
            h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
            h21, h22, h23, h24, h25, h26,
            cliPartyActiveInv_mono_q_rem hq hactA,
            fun hacc => cliPartyActiveInv_mono_q_rem hq (hactB hacc)⟩

private theorem cliAdapterInstRel_with_insts {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem : ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (h : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (bhInsts' : List (ModelDriverInstance S ℓ)) (instMeta' : List (ModelDriverInstanceMeta S)) :
    CliAdapterInstRel X W q_rem st_cli
      { ds_cli with bhInsts := bhInsts', instMeta := instMeta' }
      bi d im im_e2e inst ack where
  im_eq := h.im_eq
  sid_eq := h.sid_eq
  hdr_eq := h.hdr_eq
  idB_eq := h.idB_eq
  respSlot_eq := h.respSlot_eq
  respMeta_eq := h.respMeta_eq
  regIdA_eq := h.regIdA_eq
  regIdB_eq := h.regIdB_eq
  aliceAcked_false := h.aliceAcked_false
  idA_pub_eq := h.idA_pub_eq
  idB_pub_eq := h.idB_pub_eq
  extrasB_eq := h.extrasB_eq
  stB0_empty := h.stB0_empty
  resp_bundle_rel := h.resp_bundle_rel
  handshake_rel := h.handshake_rel
  gs_rel := h.gs_rel

private theorem cliAdapterKeyIndInv_with_insts {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (bhInsts' : List (ModelDriverInstance S ℓ)) (instMeta' : List (ModelDriverInstanceMeta S)) :
    CliAdapterKeyIndInv S P W st { ds with bhInsts := bhInsts', instMeta := instMeta' } where
  prins_wf := hInv.prins_wf
  prins_uniq := hInv.prins_uniq
  spk_wf := hInv.spk_wf
  spk_uniq := hInv.spk_uniq
  opk_wf := hInv.opk_wf
  opk_uniq := hInv.opk_uniq
  ds_prins := hInv.ds_prins
  prins_ds := hInv.prins_ds
  ds_bundles := hInv.ds_bundles
  ds_opks := hInv.ds_opks
  sessions_wf := hInv.sessions_wf
  sessions_uniq := hInv.sessions_uniq
  roCache_nil := hInv.roCache_nil
  respSessions_wf := hInv.respSessions_wf
  initTapes_wf := hInv.initTapes_wf
  initTapes_uniq := hInv.initTapes_uniq
  sends_wf := hInv.sends_wf

private theorem cliAdapterDrvRel_mono_qs_rem {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart : ℕ} {qs₁ qs₂ : ℕ → ℕ}
    (hqs : ∀ k, qs₁ k ≤ qs₂ k)
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs₂ st_cli ds_cli σ_ad σ_e2e) :
    CliAdapterDrvRel S ℓ X W b qStart qs₁ st_cli ds_cli σ_ad σ_e2e where
  b_eq := hRel.b_eq
  st_rel := hRel.st_rel
  ki_inv := hRel.ki_inv
  base_e2e_eq := hRel.base_e2e_eq
  base_ad_eq := hRel.base_ad_eq
  corrPrins_eq := hRel.corrPrins_eq
  revealedSpks_eq := hRel.revealedSpks_eq
  insts_len_le := hRel.insts_len_le
  insts_len_eq := hRel.insts_len_eq
  meta_cli_len_eq := hRel.meta_cli_len_eq
  meta_e2e_len_eq := hRel.meta_e2e_len_eq
  ad_none_of_ge := hRel.ad_none_of_ge
  insts_rel := fun k h_cli h_e2e h_mb h_me => by
    obtain ⟨inst, hinst, hInstRel⟩ := hRel.insts_rel k h_cli h_e2e h_mb h_me
    exact ⟨inst, hinst, cliAdapterInstRel_mono_q_rem (hqs k) hInstRel⟩

private theorem cliAdapterDrvRel_decrement_i {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    (i : ℕ)
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e) :
    CliAdapterDrvRel S ℓ X W b qStart (fun k => if k = i then qs_rem k - 1 else qs_rem k)
      st_cli ds_cli σ_ad σ_e2e :=
  cliAdapterDrvRel_mono_qs_rem (fun k => by split_ifs <;> omega) hRel

private theorem instMeta_eq_of_cliRel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e) :
    ds_cli.instMeta = σ_e2e.instMeta := by
  apply List.ext_getElem
  · rw [hRel.meta_cli_len_eq, hRel.insts_len_eq, hRel.meta_e2e_len_eq]
  · intro i hi_mb hi_me
    have hi_cli : i < ds_cli.bhInsts.length := hRel.meta_cli_len_eq ▸ hi_mb
    have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
    obtain ⟨_, _, hInstRel⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
    exact hInstRel.im_eq

private theorem bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e) (i : ℕ) :
    bhDrvInstClean ds_cli i = bhE2EDrvInstClean σ_e2e i := by
  unfold bhDrvInstClean bhE2EDrvInstClean
  by_cases hi_cli : i < ds_cli.bhInsts.length
  · have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
    have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
    have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
    obtain ⟨_, _, hI⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
    rw [List.getElem?_eq_getElem hi_cli, List.getElem?_eq_getElem hi_e2e,
      List.getElem?_eq_getElem hi_mb, List.getElem?_eq_getElem hi_me]
    dsimp only
    rw [← hI.im_eq, hI.respMeta_eq.1, hI.respMeta_eq.2, hI.sid_eq.1, hRel.revealedSpks_eq]
  · have hi_e2e : ¬ i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hi_cli),
      List.getElem?_eq_none (Nat.le_of_not_lt hi_e2e)]

private theorem bhDrvInstClean_imp_ikACorrAtAccept_false {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {ds_cli : ModelDriverState S ℓ} {i : ℕ} (hclean : bhDrvInstClean ds_cli i = true)
    (hi_cli : i < ds_cli.bhInsts.length) (hi : i < ds_cli.instMeta.length) :
    ds_cli.instMeta[i].ikACorrAtAccept = false := by
  unfold bhDrvInstClean at hclean
  rw [List.getElem?_eq_getElem hi_cli, List.getElem?_eq_getElem hi] at hclean
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hclean
  exact hclean.1.2

private theorem bhInstIkACorrupted_eq_bhE2EInstIkACorr_of_cliRel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem : ℕ}
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hInstRel : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack) :
    bhInstIkACorrupted ds_cli bi = bhE2EInstIkACorr σ_e2e d := by
  unfold bhInstIkACorrupted bhE2EInstIkACorr
  rw [hInstRel.sid_eq.1, hInstRel.hdr_eq.1, hRel.base_e2e_eq, hRel.corrPrins_eq]

private theorem cliAdapterDrvRel_update_inst {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    {i : ℕ} (hi_cli : i < ds_cli.bhInsts.length)
    (bi' : ModelDriverInstance S ℓ) (d' : BHModelInst S ℓ) (im' im_e2e' : ModelDriverInstanceMeta S)
    {σ_ad' : CliAdapterState S}
    (inst' : BHAdapterInstMeta S) (ack' : Bool)
    (had_base : σ_ad'.2.2 = σ_ad.2.2)
    (had1_eq : σ_ad'.1 i = some inst')
    (had2_eq : σ_ad'.2.1 i = ack')
    (had1_ne : ∀ k, k ≠ i → σ_ad'.1 k = σ_ad.1 k)
    (had2_ne : ∀ k, k ≠ i → σ_ad'.2.1 k = σ_ad.2.1 k)
    (hInstRel' : CliAdapterInstRel X W (qs_rem i - 1) st_cli
      { ds_cli with bhInsts := ds_cli.bhInsts.set i bi', instMeta := ds_cli.instMeta.set i im' }
      bi' d' im' im_e2e' inst' ack') :
    CliAdapterDrvRel S ℓ X W b qStart (fun k => if k = i then qs_rem k - 1 else qs_rem k)
      st_cli
      { ds_cli with bhInsts := ds_cli.bhInsts.set i bi', instMeta := ds_cli.instMeta.set i im' }
      σ_ad'
      { σ_e2e with insts := σ_e2e.insts.set i d', instMeta := σ_e2e.instMeta.set i im_e2e' } where
  b_eq := hRel.b_eq
  st_rel := hRel.st_rel
  ki_inv := cliAdapterKeyIndInv_with_insts hRel.ki_inv _ _
  base_e2e_eq := hRel.base_e2e_eq
  base_ad_eq := had_base.trans hRel.base_ad_eq
  corrPrins_eq := hRel.corrPrins_eq
  revealedSpks_eq := hRel.revealedSpks_eq
  insts_len_le := by simp [hRel.insts_len_le]
  insts_len_eq := by simp [hRel.insts_len_eq]
  meta_cli_len_eq := by simp [hRel.meta_cli_len_eq]
  meta_e2e_len_eq := by simp [hRel.meta_e2e_len_eq]
  ad_none_of_ge := fun k hk => by
    simp only [List.length_set] at hk
    have hne : k ≠ i := by
      have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
      omega
    rw [had1_ne k hne, had2_ne k hne]
    exact hRel.ad_none_of_ge k hk
  insts_rel := fun k h_cli h_e2e h_mb h_me => by
    simp only [List.length_set] at h_cli h_e2e h_mb h_me
    by_cases hk : k = i
    · subst hk
      refine ⟨inst', had1_eq, ?_⟩
      simp only [↓reduceIte, had2_eq, List.getElem_set_self]
      exact hInstRel'
    · obtain ⟨inst_k, hinst_k, hRel_k⟩ := hRel.insts_rel k h_cli h_e2e h_mb h_me
      refine ⟨inst_k, (had1_ne k hk).trans hinst_k, ?_⟩
      simp only [hk, ↓reduceIte, had2_ne k hk, List.getElem_set_ne (Ne.symm hk)]
      exact cliAdapterInstRel_with_insts hRel_k _ _

private theorem list_set_getElem_self_cli {α : Type*} (l : List α) (i : ℕ) (hi : i < l.length) :
    l.set i l[i] = l := by
  apply List.ext_getElem (by simp)
  intro k hk1 hk2
  rw [List.getElem_set]
  split_ifs with hik
  · subst hik; rfl
  · rfl

private theorem bhDrvState_set_same_gs_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ds_cli : ModelDriverState S ℓ) (i : ℕ)
    (hi_cli : i < ds_cli.bhInsts.length) (hi_mb : i < ds_cli.instMeta.length)
    (gs_cli : SM.GameState BinState (Plain ℓ) Bytes)
    (hgs_cli : ds_cli.bhInsts[i].gs = some gs_cli) :
    { ds_cli with
      bhInsts := ds_cli.bhInsts.set i { ds_cli.bhInsts[i] with gs := some gs_cli }
      instMeta := ds_cli.instMeta.set i ds_cli.instMeta[i] } = ds_cli := by
  have hbi : { ds_cli.bhInsts[i] with gs := some gs_cli } = ds_cli.bhInsts[i] := by
    generalize ds_cli.bhInsts[i] = bi at hgs_cli ⊢
    cases bi; dsimp only at hgs_cli; subst hgs_cli; rfl
  rw [hbi, list_set_getElem_self_cli ds_cli.bhInsts i hi_cli,
    list_set_getElem_self_cli ds_cli.instMeta i hi_mb]

private theorem bhE2EDrvState_set_same_gs_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ_e2e : BHE2EDrvState S ℓ) (i : ℕ)
    (hi_e2e : i < σ_e2e.insts.length) (hi_me : i < σ_e2e.instMeta.length)
    (gs_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hgs_m : σ_e2e.insts[i].gs = some gs_m) :
    { σ_e2e with
      insts := σ_e2e.insts.set i { σ_e2e.insts[i] with gs := some gs_m }
      instMeta := σ_e2e.instMeta.set i σ_e2e.instMeta[i] } = σ_e2e := by
  have hd : { σ_e2e.insts[i] with gs := some gs_m } = σ_e2e.insts[i] := by
    generalize σ_e2e.insts[i] = d at hgs_m ⊢
    cases d; dsimp only at hgs_m; subst hgs_m; rfl
  rw [hd, list_set_getElem_self_cli σ_e2e.insts i hi_e2e,
    list_set_getElem_self_cli σ_e2e.instMeta i hi_me]

private theorem cliAdapterInstRel_set_win {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem : ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInstRel : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    {gs_cli : SM.GameState BinState (Plain ℓ) Bytes}
    {gs_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hgs_cli : bi.gs = some gs_cli) (hgs_m : d.gs = some gs_m) :
    CliAdapterInstRel X W q_rem st_cli ds_cli
      { bi with gs := some { gs_cli with win := true } }
      { d with gs := some { gs_m with win := true } } im im_e2e inst ack where
  im_eq := hInstRel.im_eq
  sid_eq := hInstRel.sid_eq
  hdr_eq := hInstRel.hdr_eq
  idB_eq := hInstRel.idB_eq
  respSlot_eq := hInstRel.respSlot_eq
  respMeta_eq := hInstRel.respMeta_eq
  regIdA_eq := hInstRel.regIdA_eq
  regIdB_eq := hInstRel.regIdB_eq
  aliceAcked_false := hInstRel.aliceAcked_false
  idA_pub_eq := hInstRel.idA_pub_eq
  idB_pub_eq := hInstRel.idB_pub_eq
  extrasB_eq := hInstRel.extrasB_eq
  stB0_empty := hInstRel.stB0_empty
  resp_bundle_rel := hInstRel.resp_bundle_rel
  handshake_rel := by
    obtain ⟨bundleE, dk, aliceCoins, u_init, bnd, t_init, ss, h1, h2, h3, h4⟩ :=
      hInstRel.handshake_rel
    exact ⟨bundleE, dk, aliceCoins, u_init, bnd, t_init, ss, h1, h2, h3,
      fun _ _ h5 h6 h7 h8 => by
        cases h5; cases h6; exact h4 gs_cli gs_m hgs_cli hgs_m h7 h8⟩
  gs_rel := by
    have hgs := hInstRel.gs_rel
    rw [hgs_cli, hgs_m] at hgs
    dsimp only
    rcases hgs with ⟨hb, hrest⟩
    refine ⟨hb, ?_⟩
    split_ifs at hrest ⊢
    · rfl
    · exact ⟨hrest.1, rfl, hrest.2.2⟩

private theorem cliAdapterInstRel_of_bob_recv_accept {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem q' : ℕ} (hq' : q' ≤ q_rem)
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e im' : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInstRel : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    {gs_cli gs_cli' : SM.GameState BinState (Plain ℓ) Bytes}
    {gs_m gs_m' : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hgs_cli : bi.gs = some gs_cli) (hgs_m : d.gs = some gs_m)
    (hCorr : im.ikACorrAtAccept = false)
    (g' : GhostState Bytes)
    (him'_acc : im'.bobAccepted = true) (him'_corr : im'.ikACorrAtAccept = false)
    (him'_resp : im'.respPrin = im.respPrin ∧ im'.respSpkIdx = im.respSpkIdx)
    (hs_b : gs_cli'.b = gs_m'.b) (hs_win : gs_cli'.win = gs_m'.win)
    (hs_ep : gs_cli'.epoch = gs_m'.epoch) (hs_idx : gs_cli'.idx = gs_m'.idx)
    (hs_max : gs_cli'.maxAcc = gs_m'.maxAcc) (hs_ch : gs_cli'.chall = gs_m'.chall)
    (hs_comp : gs_cli'.comp = gs_m'.comp) (hs_tL : gs_cli'.tL = gs_m'.tL)
    (hs_lk : gs_cli'.leaks = gs_m'.leaks) (hs_cr : gs_cli'.corrs = gs_m'.corrs)
    (hs_tr : List.Forall₂ (CliAdapterTransEntryRel im.bobAccepted d.sid d.hdr)
      gs_cli'.trans gs_m'.trans)
    (hs_st_m : gs_m'.st = Function.update gs_m.st .B g')
    (hs_st_cli : gs_cli'.st =
      Function.update gs_cli.st .B (bhBinStateOfParty { inst with bobAccepted := true } g'))
    (hg'_party : g'.party = .B)
    (hg'_ppk : g'.session.pendingPreKey = false)
    (hg'_epB : 0 < g'.epoch)
    (hg'_actB : CliPartyActiveInv W (cliPqxdhDirBobAfterAccept bi (cliPqSigsOf st_cli bi))
      (bhInstExtrasB inst) g' q') :
    CliAdapterInstRel X W q' st_cli ds_cli
      { bi with gs := some gs_cli' } { d with gs := some gs_m' }
      im' im' { inst with bobAccepted := true } ack := by
  have hgs := hInstRel.gs_rel
  rw [hgs_cli, hgs_m] at hgs
  rcases hgs with ⟨_, hrest⟩
  simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
  rcases hrest with
    ⟨_, _, _, _, _, _, _, _, _, _,
     _, h_ppkA, _, h_idA, _, _, _, _, _, _,
     _, h_stA, _, _, h_pA, _, h_actA, _⟩
  have hXA : bhInstExtrasA { inst with bobAccepted := true } = bhInstExtrasA inst := rfl
  have hXB : bhInstExtrasB { inst with bobAccepted := true } = bhInstExtrasB inst := rfl
  have hbin : ∀ g, bhBinStateOfParty { inst with bobAccepted := true } g =
      bhBinStateOfParty inst g := fun _ => rfl
  have hneAB : Party.A ≠ Party.B := by decide
  refine
    { im_eq := rfl
      sid_eq := hInstRel.sid_eq
      hdr_eq := hInstRel.hdr_eq
      idB_eq := hInstRel.idB_eq
      respSlot_eq := hInstRel.respSlot_eq
      respMeta_eq := ⟨him'_resp.1.trans hInstRel.respMeta_eq.1,
        him'_resp.2.trans hInstRel.respMeta_eq.2⟩
      regIdA_eq := hInstRel.regIdA_eq
      regIdB_eq := hInstRel.regIdB_eq
      aliceAcked_false := hInstRel.aliceAcked_false
      idA_pub_eq := hInstRel.idA_pub_eq
      idB_pub_eq := hInstRel.idB_pub_eq
      extrasB_eq := hInstRel.extrasB_eq
      stB0_empty := hInstRel.stB0_empty
      resp_bundle_rel := hInstRel.resp_bundle_rel
      handshake_rel := ?_
      gs_rel := ?_ }
  · obtain ⟨bundleE, dk, aliceCoins, u_init, bnd, t_init, ss, h1, h2, h3, _⟩ :=
      hInstRel.handshake_rel
    refine ⟨bundleE, dk, aliceCoins, u_init, bnd, t_init, ss, h1, h2, h3,
      fun _ _ _ _ _ hacc₁ => ?_⟩
    rw [him'_acc] at hacc₁; cases hacc₁
  · dsimp only
    refine ⟨hs_b, ?_⟩
    simp only [him'_corr, him'_acc, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    refine ⟨trivial, hs_win, hs_ep, hs_idx, hs_max, hs_ch, hs_comp, hs_tL, hs_lk, hs_cr,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hs_tr.imp (fun _ _ h => cliAdapterTransEntryRel_of_bobAccepted_true h)
    · rw [hs_st_m]; simp [Function.update, hneAB, h_ppkA]
    · rw [hs_st_m]; simp [Function.update, hg'_ppk]
    · rw [hs_st_m]; simp [Function.update, hneAB, h_idA]
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · intro _; rw [hs_st_m]; simp [Function.update, hg'_epB]
    · rw [hs_st_cli, hs_st_m]; simp [Function.update, hneAB, hbin, h_stA]
    · intro h; cases h
    · intro _; rw [hs_st_cli, hs_st_m]; simp [Function.update]
    · rw [hs_st_m]; simp [Function.update, hneAB, h_pA]
    · rw [hs_st_m]; simp [Function.update, hg'_party]
    · rw [hXA, hs_st_m]
      simp only [Function.update, hneAB, ↓reduceDIte]
      exact cliPartyActiveInv_mono_q_rem hq' h_actA
    · intro _
      rw [hXB, hs_st_m]
      simp only [Function.update, ↓reduceDIte]
      exact hg'_actB

private theorem bhAdapterUpdateInstMeta_bob_eq_cli {S : SignalPqxdh.Setup} {Pt : Type}
    (_decT : PublicKey → Option Pt) (_encT : Pt → PublicKey)
    (inst : BHAdapterInstMeta S) (c : Bytes)
    (hreg : ∀ m, bhDecodePreKeyMsgE c = some m → inst.bobAccepted = false →
      m.regId = inst.bobRemoteRegId) :
    (bhShallowUpdateInstMeta inst false true c).2 = { inst with bobAccepted := true } := by
  cases inst with
  | mk sid u_resp hdr idB aliceAcked bobAccepted bobRemoteRegId =>
    dsimp [bhShallowUpdateInstMeta] at hreg ⊢
    cases bobAccepted <;> cases hm : bhDecodePreKeyMsgE c <;>
      simp [hm] at hreg ⊢
    rw [hreg]

private theorem bhAdapterInstMeta_with_bobAccepted_self_cli {S : SignalPqxdh.Setup}
    (inst : BHAdapterInstMeta S) (h : inst.bobAccepted = true) :
    { inst with bobAccepted := true } = inst := by
  cases inst; dsimp only at h; subst h; rfl

private theorem cliAdapterStepCoupled_bind_pure {S : SignalPqxdh.Setup} {ℓ : ℕ} {α β : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    (m : ProbComp β)
    (f_cli : β → (α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)
    (f_ad : β → (α × CliAdapterState S) × BHE2EDrvState S ℓ)
    (h : ∀ x ∈ support m,
      (f_cli x).1.1 = (f_ad x).1.1 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem'
        (f_cli x).2 (f_cli x).1.2 (f_ad x).1.2 (f_ad x).2) :
    cliAdapterStepCoupled X W b qStart' qs_rem'
      (m >>= fun x => pure (f_cli x))
      (m >>= fun x => pure (f_ad x)) := by
  refine ⟨(fun x => (f_cli x, f_ad x)) <$> m, ?_, ?_, ?_⟩
  · intro F
    simp [map_eq_bind_pure_comp, bind_assoc]
  · intro F
    simp [map_eq_bind_pure_comp, bind_assoc]
  · intro u v huv
    simp only [support_map, Set.mem_image, Prod.mk.injEq] at huv
    rcases huv with ⟨x, hx, rfl, rfl⟩
    exact h x hx

private theorem cliAdapterStepCoupled_deliver {S : SignalPqxdh.Setup} {ℓ : ℕ} {GB GM : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    (m_cli : ProbComp (Option (SM.RecvResult (Plain ℓ)) × GB))
    (m_m : ProbComp (Option (SM.RecvResult (Plain ℓ)) × GM))
    (c_cli c_m : Bool) (s_cli : GB) (s_m : GM)
    (D_cli : BitVec 256 → Option (SM.RecvResult (Plain ℓ)) × GB)
    (D_m : BitVec 256 → Option (SM.RecvResult (Plain ℓ)) × GM)
    (hm_cli : m_cli = if c_cli then pure (none, s_cli)
      else ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (D_cli rc))
    (hm_m : m_m = if c_m then pure (none, s_m)
      else ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (D_m rc))
    (hc : c_cli = c_m)
    (F_cli : Option (SM.RecvResult (Plain ℓ)) × GB →
      (Option (SM.RecvResult (Plain ℓ)) × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)
    (F_m : Option (SM.RecvResult (Plain ℓ)) × GM →
      (Option (SM.RecvResult (Plain ℓ)) × CliAdapterState S) × BHE2EDrvState S ℓ)
    (h0 : c_m = true →
      (F_cli (none, s_cli)).1.1 = (F_m (none, s_m)).1.1 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem'
        (F_cli (none, s_cli)).2 (F_cli (none, s_cli)).1.2 (F_m (none, s_m)).1.2 (F_m (none, s_m)).2)
    (h1 : c_m = false → ∀ rc,
      (F_cli (D_cli rc)).1.1 = (F_m (D_m rc)).1.1 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem'
        (F_cli (D_cli rc)).2 (F_cli (D_cli rc)).1.2 (F_m (D_m rc)).1.2 (F_m (D_m rc)).2) :
    cliAdapterStepCoupled X W b qStart' qs_rem'
      (m_cli >>= fun x => pure (F_cli x)) (m_m >>= fun x => pure (F_m x)) := by
  subst hm_cli hm_m hc
  cases hcm : c_cli
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
    exact cliAdapterStepCoupled_bind_pure _ (fun rc => F_cli (D_cli rc)) (fun rc => F_m (D_m rc))
      (fun rc _ => h1 hcm rc)
  · simp only [↓reduceIte, pure_bind]
    have h := h0 hcm
    rcases hF : F_cli (none, s_cli) with ⟨⟨r1, ds1⟩, st1⟩
    rcases hG : F_m (none, s_m) with ⟨⟨r2, sa2⟩, se2⟩
    rw [hF, hG] at h
    obtain ⟨h_eq, h_rel⟩ := h
    dsimp only at h_eq h_rel
    subst h_eq
    exact cliAdapterStepCoupled_ret _ _ _ _ _ h_rel

private theorem cliAdapterStepCoupled_congr_cli {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    {c c' : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)}
    {c_ad : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ)}
    (h : c = c') (h' : cliAdapterStepCoupled X W b qStart' qs_rem' c' c_ad) :
    cliAdapterStepCoupled X W b qStart' qs_rem' c c_ad := h ▸ h'

private theorem cliAdapterStepCoupled_discard {S : SignalPqxdh.Setup} {ℓ : ℕ} {α β : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    (r : α) (st_cli' : SignalPqxdh.KeyIndState S) (ds_cli' : ModelDriverState S ℓ)
    (σ_ad' : CliAdapterState S) (σ_e2e' : BHE2EDrvState S ℓ)
    (m : ProbComp β) (g : β → BHE2EDrvState S ℓ)
    (hm : ∀ x ∈ support m, g x = σ_e2e')
    (hRel' : CliAdapterDrvRel S ℓ X W b qStart' qs_rem' st_cli' ds_cli' σ_ad' σ_e2e') :
    cliAdapterStepCoupled X W b qStart' qs_rem'
      (pure ((r, ds_cli'), st_cli'))
      (m >>= fun x => pure ((r, σ_ad'), g x)) := by
  have h : (m >>= fun x => pure ((r, σ_ad'), g x)) = (m >>= fun _ => pure ((r, σ_ad'), σ_e2e')) :=
    OracleComp.bind_congr_of_forall_mem_support m (fun x hx => by rw [hm x hx])
  rw [h]
  exact cliAdapterStepCoupled_of_deq (cliAdapterStepCoupled_ret r st_cli' ds_cli' σ_ad' σ_e2e' hRel')
    (CryptoGames.Lazy.DEq.refl _) (CryptoGames.Lazy.DEq.bind_const _ _)

private theorem cliOracleImplR_deliver_run {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (s : SM.GameState St Msg C) :
    (SM.oracleImplR sm Δ qep cfg (.inl (.inl (.inr (P, c))))).run s =
      if s.win || (s.inTransit P.other c).isNone then pure (none, s)
      else ($ᵗ RCoins : ProbComp RCoins) >>= fun rc => pure (deliverRPure sm cfg P c rc s) :=
  stepR_deliver_eq sm Δ qep cfg P c s

private theorem cliDeliverRPure_reject {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (rc : RCoins) (s : SM.GameState St Msg C) (r : SM.Record Msg C)
    (hwin : s.win = false) (htr : s.inTransit P.other c = some r)
    (hmust : cfg.must s P r = false) (hrcv : sm.receive (s.st P) c rc = none) :
    deliverRPure sm cfg P c rc s = (some .rejected, s) := by
  unfold deliverRPure; simp [hwin, htr, hmust, hrcv]

private theorem cliDeliverRPure_accept {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (rc : RCoins) (s : SM.GameState St Msg C) (r : SM.Record Msg C)
    (st' : St) (t' i' : ℕ) (m' : Msg)
    (hwin : s.win = false) (htr : s.inTransit P.other c = some r)
    (hmust : cfg.must s P r = false) (hrcv : sm.receive (s.st P) c rc = some (st', t', i', m')) :
    deliverRPure sm cfg P c rc s =
      (some (.accepted t' i' (if s.chall.contains r.pos then none else some m')),
        s.accept P st' r.pos) := by
  unfold deliverRPure; simp [hwin, htr, hmust, hrcv]

private theorem bhConfigSpkS_must_cli {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) {ℓ : ℕ} (s : SM.GameState BinState (Plain ℓ) Bytes)
    (P : Party) (r : SM.Record (Plain ℓ) Bytes) :
    (bhConfigSpkS (Msg := Plain ℓ) decT encT).must s P r = false := rfl

open CryptoVerification.E2E.BhAdapterIjHelpersV1 in
private theorem cliOracleImplR_inject_run {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (s : SM.GameState St Msg C) :
    (SM.oracleImplR sm Δ qep cfg (.inl (.inr (P, c)))).run s =
      if s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c) then
        pure (none, s)
      else ($ᵗ RCoins : ProbComp RCoins) >>= fun rc => pure (injectPost sm Δ qep cfg s P c rc) :=
  injectR_run sm Δ qep cfg s P c

private theorem cliOracleImplR_inject_run_pure {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (s : SM.GameState St Msg C) :
    (SM.oracleImplR sm Δ qep cfg (.inl (.inr (P, c)))).run s =
      if s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c) then
        pure (none, s)
      else ($ᵗ RCoins : ProbComp RCoins) >>= fun rc =>
        pure (injectRPure sm Δ qep cfg P c rc s) :=
  stepR_inject_eq sm Δ qep cfg P c s

private theorem bhWireInnerBytes_nil_cli : bhWireInnerBytes [] = none := by
  unfold bhWireInnerBytes; rfl

private theorem bhDecodePreKeyMsgE_head_ne_cli (t : BitVec 8) (xs : Bytes) (ht : t ≠ wirePrekey) :
    bhDecodePreKeyMsgE (t :: xs) = none := by
  unfold bhDecodePreKeyMsgE bhDecodePreKeyMsgERaw
  rcases xs with _ | ⟨v, proto⟩ <;> simp [ht]

private theorem bhE2EStepLocalSm_inject_B_noop_cli {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (hi_e2e : i < σ.insts.length) (hi_me : i < σ.instMeta.length)
    (gs_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hgs_m : σ.insts[i].gs = some gs_m)
    (hNC : (!σ.instMeta[i].bobAccepted && bhE2EInstIkACorr σ σ.insts[i]) = false)
    (c : Bytes) (hc : c = [] ∨ ∃ body, c = wireWhisper :: body) :
    ∀ x ∈ support (bhE2EStepLocalSm C K qep decT encT σ i (.inl (.inr (.B, c)))), x.2 = σ := by
  have hd_opt : σ.insts[i]? = some σ.insts[i] := List.getElem?_eq_getElem hi_e2e
  have hime_opt : σ.instMeta[i]? = some σ.instMeta[i] := List.getElem?_eq_getElem hi_me
  have he2e_same := bhE2EDrvState_set_same_gs_cli σ i hi_e2e hi_me gs_m hgs_m
  have hdec : bhDecodePreKeyMsgE c = none := by
    rcases hc with rfl | ⟨body, rfl⟩
    · unfold bhDecodePreKeyMsgE; rfl
    · exact bhDecodePreKeyMsgE_head_ne_cli _ _ (by decide)
  intro x hx
  unfold bhE2EStepLocalSm at hx
  by_cases hClean : bhE2EDrvInstClean σ i = true
  · simp only [hClean, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd_opt, hime_opt,
      bhIsBobRecvSMQuery, Bool.and_true, hNC, hgs_m] at hx
    cases hacc : σ.instMeta[i].bobAccepted
    · simp only [hacc, Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hx
      rw [hx]
    · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hdec] at hx
      have hrcv : ∀ rc, (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
          σ.insts[i].idA σ.insts[i].idB) ℓ σ.insts[i].spkCoins).receive (gs_m.st .B) c rc = none := by
        intro rc
        rcases hc with rfl | ⟨body, rfl⟩
        · simp [sessionSchemeFixedSpk, CryptoVerification.E2E.BhAdapterIjHelpersV1.params_receive_nil]
        · simp [sessionSchemeFixedSpk,
            CryptoVerification.E2E.BhAdapterIjHelpersV1.params_receive_wireWhisper_cons]
      rw [cliOracleImplR_inject_run_pure] at hx
      split_ifs at hx with hcond
      · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hx
        rw [hx]
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact he2e_same
      · simp only [bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
          Set.mem_singleton_iff, exists_prop] at hx
        obtain ⟨rc, -, rfl⟩ := hx
        have hinj : injectRPure (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
            σ.insts[i].idA σ.insts[i].idB) ℓ σ.insts[i].spkCoins) (2 + 1) qep
            (configRefuseEarlyBobCorr decT encT) .B c rc gs_m = (some .rejected, gs_m) := by
          unfold injectRPure
          simp only [hcond]
          rw [hrcv rc]
          simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hinj]
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact he2e_same
  · simp only [Bool.not_eq_true] at hClean
    simp only [hClean, Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hx
    rw [hx]

section
variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {bobAccepted : Bool}
  {sid : SignalPqxdh.SessionId S} {hdr : SignalPqxdh.HandshakeHdr}

private theorem cliAdapterTrans_filter_pos
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (pos : SM.Pos) :
    List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr)
      (trans_cli.filter (fun rec => rec.pos != pos))
      (trans_m.filter (fun rec => rec.pos != pos)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    have hpos : (r_cli.pos != pos) = (r_m.pos != pos) := by rw [hrel.1]
    simp only [List.filter_cons, hpos]
    cases r_m.pos != pos
    · exact ih
    · exact List.Forall₂.cons hrel ih

private theorem cliAdapterTrans_any_pos
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (f : SM.Pos → Bool) :
    trans_cli.any (fun r => f r.pos) = trans_m.any (fun r => f r.pos) := by
  induction h with
  | nil => rfl
  | cons hrel _ ih =>
    simp [List.any_cons, hrel.1, ih]

private theorem cliAdapterTrans_find?_m_ww_none
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (p : Party) (rest : Bytes) :
    trans_m.find? (fun r => r.pos.sender == p && decide (r.ct = wireWhisper :: rest)) = none := by
  induction h with
  | nil => rfl
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    rcases hrel with ⟨_, _, hct⟩
    have hp : (r_m.pos.sender == p && decide (r_m.ct = wireWhisper :: rest)) = false := by
      rcases hct with ⟨_, h2⟩ | ⟨_, _, hww, _⟩
      · simp [h2]
      · simp [hww rest]
    simp only [List.find?_cons, hp]
    exact ih

private theorem cliAdapterAlignTransList_find?_A
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    {c inner : Bytes} (hc : bhWireInnerBytes c = some inner) (hinner : inner ≠ []) :
    ((bhAlignTransList inner c trans_cli).find?
        (fun r => r.pos.sender == .A && decide (r.ct = c))).map (fun r => (r.pos, r.msg)) =
      (trans_m.find? (fun r => r.pos.sender == .A && decide (r.ct = inner))).map
        (fun r => (r.pos, r.msg)) := by
  induction h with
  | nil => rfl
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    rcases hrel with ⟨hpos, hmsg, hct⟩
    have hA_iff : r_cli.pos.sender = .A →
        (bhWireInnerBytes r_cli.ct = some inner ↔ r_m.ct = inner) := by
      intro hs
      rcases hct with ⟨h1, h2⟩ | ⟨_, _, _, _, hA, _⟩
      · rw [h1, h2, bhWireInnerBytes_nil_cli]
        exact ⟨fun h => (by cases h), fun h => absurd h.symm hinner⟩
      · rw [(hA hs).1]; exact ⟨fun h => Option.some.inj h, fun h => by rw [h]⟩
    unfold bhAlignTransList
    by_cases hmatch : (r_m.pos.sender == .A && decide (r_m.ct = inner)) = true
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmatch
      have hs_cli : r_cli.pos.sender = .A := by rw [hpos, hmatch.1]
      have hw : bhWireInnerBytes r_cli.ct = some inner := (hA_iff hs_cli).2 hmatch.2
      simp [hw, hmatch.1, hmatch.2, hpos, hmsg]
    · have hnot_align :
          (r_cli.pos.sender == .A && bhWireInnerBytes r_cli.ct == some inner) = false := by
        rw [Bool.eq_false_iff]; intro hal
        simp only [Bool.and_eq_true, beq_iff_eq] at hal
        have hs_m : r_m.pos.sender = .A := by rw [← hpos, hal.1]
        exact hmatch (by simp [hs_m, (hA_iff hal.1).1 hal.2])
      have hnot_c : (r_cli.pos.sender == .A && decide (r_cli.ct = c)) = false := by
        rw [Bool.eq_false_iff]; intro hc_eq
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc_eq
        have hs_m : r_m.pos.sender = .A := by rw [← hpos, hc_eq.1]
        have hw : bhWireInnerBytes r_cli.ct = some inner := by rw [hc_eq.2, hc]
        exact hmatch (by simp [hs_m, (hA_iff hc_eq.1).1 hw])
      have hnot_m : (r_m.pos.sender == .A && decide (r_m.ct = inner)) = false :=
        Bool.eq_false_iff.mpr hmatch
      simp only [hnot_align, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hnot_c, hnot_m]
      exact ih

private theorem cliAdapterTrans_find?_A_prekey
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel false sid hdr) trans_cli trans_m)
    (inner : Bytes) (hinner : inner ≠ []) :
    (trans_cli.find? (fun r => r.pos.sender == .A && decide
        (r.ct = wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId sid) hdr inner).bytes))).map
        (fun r => (r.pos, r.msg)) =
      (trans_m.find? (fun r => r.pos.sender == .A && decide (r.ct = inner))).map
        (fun r => (r.pos, r.msg)) := by
  induction h with
  | nil => rfl
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    rcases hrel with ⟨hpos, hmsg, hct⟩
    have hpred :
        (r_cli.pos.sender == .A && decide
          (r_cli.ct = wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId sid) hdr inner).bytes)) =
        (r_m.pos.sender == .A && decide (r_m.ct = inner)) := by
      rw [hpos]
      cases hs : r_m.pos.sender
      · have hs_cli : r_cli.pos.sender = .A := by rw [hpos, hs]
        have h1 : (Party.A == Party.A) = true := rfl
        simp only [h1, Bool.true_and, decide_eq_decide]
        rcases hct with ⟨h1, h2⟩ | ⟨_, _, _, _, hA, _⟩
        · rw [h1, h2]; exact ⟨fun h => (by cases h), fun h => absurd h.symm hinner⟩
        · obtain ⟨hw, hpk⟩ := hA hs_cli
          rw [hpk rfl]
          constructor
          · intro heq
            have := congrArg bhWireInnerBytes heq
            rw [← hpk rfl, hw] at this
            unfold bhWireInnerBytes at this
            rw [bhDecodePreKeyMsgE_wirePrekey] at this
            simpa [bhExpectedPreKeyMsg] using this
          · intro heq; rw [heq]
      · rfl
    simp only [List.find?_cons, hpred]
    cases r_m.pos.sender == .A && decide (r_m.ct = inner)
    · exact ih
    · simp [hpos, hmsg]

private theorem cliAdapterTrans_A_noop
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    {c inner : Bytes} (hc : bhWireInnerBytes c = some inner)
    (hbad : inner = [] ∨ (bhDecodePreKeyMsgE inner).isSome) :
    bhAlignTransList inner c trans_cli = trans_cli ∧
      trans_cli.find? (fun r => r.pos.sender == .A && decide (r.ct = c)) = none := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hno : r_cli.pos.sender = .A → bhWireInnerBytes r_cli.ct ≠ some inner := by
      intro hs hw
      rcases hrel.2.2 with ⟨h1, _⟩ | ⟨hne, hdec, _, _, hA, _⟩
      · rw [h1, bhWireInnerBytes_nil_cli] at hw; cases hw
      · have := (hA hs).1
        rw [hw] at this
        obtain rfl := Option.some.inj this
        rcases hbad with h0 | h0
        · exact hne h0
        · rw [hdec] at h0; cases h0
    have hal : (r_cli.pos.sender == .A && bhWireInnerBytes r_cli.ct == some inner) = false := by
      rw [Bool.eq_false_iff]; intro hm
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      exact hno hm.1 hm.2
    have hfc : (r_cli.pos.sender == .A && decide (r_cli.ct = c)) = false := by
      rw [Bool.eq_false_iff]; intro hm
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
      exact hno hm.1 (by rw [hm.2, hc])
    refine ⟨?_, ?_⟩
    · unfold bhAlignTransList
      simp only [hal, Bool.false_eq_true, ↓reduceIte, ih1]
    · simp only [List.find?_cons, hfc]
      exact ih2

private theorem cliAdapterTrans_m_ct_len
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (r : SM.Record (Plain ℓ) Bytes) (hr : r ∈ trans_m) (hne : r.ct ≠ []) :
    r.ct.length ≤ 1_000_300 ∧ r.ct.length + 2048 < 2 ^ 32 := by
  revert hr
  induction h with
  | nil => intro hr; simp at hr
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    intro hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · rcases hrel.2.2 with ⟨_, h2⟩ | ⟨_, _, _, hlen, _, _⟩
      · exact absurd h2 hne
      · exact hlen
    · exact ih hr'

private theorem cliAdapterTrans_any_A_inner_eq
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (inner : Bytes) (hinner : inner ≠ []) :
    trans_cli.any (fun r => r.pos.sender == .A && bhWireInnerBytes r.ct == some inner) =
      trans_m.any (fun r => r.pos.sender == .A && decide (r.ct = inner)) := by
  induction h with
  | nil => rfl
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    rcases hrel with ⟨hpos, _, hct⟩
    have hp : (r_cli.pos.sender == .A && bhWireInnerBytes r_cli.ct == some inner) =
        (r_m.pos.sender == .A && decide (r_m.ct = inner)) := by
      rw [hpos]
      cases hs : r_m.pos.sender
      · have hs_cli : r_cli.pos.sender = .A := by rw [hpos, hs]
        rcases hct with ⟨h1, h2⟩ | ⟨_, _, _, _, hA, _⟩
        · rw [h1, h2, bhWireInnerBytes_nil_cli]
          simp [Ne.symm hinner]
        · rw [(hA hs_cli).1]
          by_cases hq : r_m.ct = inner <;> simp [hq]
      · rfl
    simp only [List.any_cons, hp, ih]

private theorem cliAdapterTrans_any_A_inner_bad
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (inner : Bytes) (hbad : inner = [] ∨ (bhDecodePreKeyMsgE inner).isSome) :
    trans_cli.any (fun r => r.pos.sender == .A && bhWireInnerBytes r.ct == some inner) = false := by
  induction h with
  | nil => rfl
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    rcases hrel with ⟨_, _, hct⟩
    have hp : (r_cli.pos.sender == .A && bhWireInnerBytes r_cli.ct == some inner) = false := by
      rw [Bool.eq_false_iff]; intro hm
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      rcases hct with ⟨h1, _⟩ | ⟨hne, hdec, _, _, hA, _⟩
      · rw [h1, bhWireInnerBytes_nil_cli] at hm; exact absurd hm.2 (by simp)
      · have h2 := (hA hm.1).1
        rw [hm.2] at h2
        obtain rfl := Option.some.inj h2
        rcases hbad with h0 | h0
        · exact hne h0
        · rw [hdec] at h0; cases h0
    simp only [List.any_cons, hp, ih, Bool.false_or]

end

private theorem list_find?_none_of_any_false_cli {α : Type} (l : List α) (p q : α → Bool)
    (hpq : ∀ a, p a = true → q a = true) (hq : l.any q = false) : l.find? p = none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at hq
    have hpa : p a = false := by
      rw [Bool.eq_false_iff]; intro h; have := hpq a h; rw [hq.1] at this; cases this
    simp only [List.find?_cons, hpa]
    exact ih hq.2

private theorem bhPartneredInnerBytes_wire_cli (acc : Bool) (regIdA : BitVec 32)
    (sessionHdr : SignalPqxdh.HandshakeHdr) (c inner : Bytes)
    (h : bhPartneredInnerBytes acc regIdA sessionHdr c = some inner) :
    bhWireInnerBytes c = some inner := by
  unfold bhPartneredInnerBytes at h
  unfold bhWireInnerBytes
  cases hd : bhDecodePreKeyMsgE c with
  | some m =>
    rw [hd] at h
    dsimp only
    cases acc <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h <;>
      split_ifs at h <;> exact h
  | none =>
    rw [hd] at h
    dsimp only
    cases acc
    · simp at h
    · simpa only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] using h

private theorem bhWireInnerBytes_wireWhisper_cli (body : Bytes) :
    bhWireInnerBytes (wireWhisper :: body) = some body := by
  unfold bhWireInnerBytes
  rw [bhDecodePreKeyMsgE_head_ne_cli wireWhisper body (by decide)]
  simp

set_option linter.unusedSimpArgs false in
private theorem cliStepLocalSM_dlB_noop {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S) (i : ℕ)
    (hi : i < ds.bhInsts.length) (hm : i < ds.instMeta.length)
    (gs : SM.GameState BinState (Plain ℓ) Bytes) (hgs : ds.bhInsts[i].gs = some gs)
    {sid : SignalPqxdh.SessionId S} {hdr' : SignalPqxdh.HandshakeHdr}
    {trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (htr : List.Forall₂ (CliAdapterTransEntryRel ds.instMeta[i].bobAccepted sid hdr') gs.trans trans_m)
    (c : Bytes)
    (hbad : ∀ inner, bhPartneredInnerBytes ds.instMeta[i].bobAccepted ds.bhInsts[i].meA.regId
        ds.bhInsts[i].hdr c = some inner → inner = [] ∨ (bhDecodePreKeyMsgE inner).isSome) :
    ((StateT.run
        (if (bhPartneredInnerBytes ds.instMeta[i].bobAccepted ds.bhInsts[i].meA.regId
            ds.bhInsts[i].hdr c).isNone = true then pure none
        else cliRunStdSM S ℓ run W qep decT encT ds i ds.bhInsts[i] ds.instMeta[i] gs
          (Sum.inl (Sum.inl (Sum.inr (Party.B, c)))))
        ds).run st) = pure ((none, ds), st) := by
  have hds_same := bhDrvState_set_same_gs_cli ds i hi hm gs hgs
  cases hp : bhPartneredInnerBytes ds.instMeta[i].bobAccepted ds.bhInsts[i].meA.regId
      ds.bhInsts[i].hdr c with
  | none => simp only [Option.isNone_none, ↓reduceIte, StateT.run_pure]
  | some inner =>
    have hw := bhPartneredInnerBytes_wire_cli _ _ _ _ _ hp
    obtain ⟨hal, hfind⟩ := cliAdapterTrans_A_noop htr hw (hbad inner hp)
    have hgsIn : bhAlignTransForBob ds.instMeta[i].bobAccepted ds.bhInsts[i].meA.regId
        ds.bhInsts[i].hdr c gs = gs := by
      unfold bhAlignTransForBob
      cases hacc : ds.instMeta[i].bobAccepted
      · rfl
      · rw [hacc] at hp
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hp, hal]
    have hnone : gs.inTransit Party.B.other c = none := by
      simp only [SM.GameState.inTransit, Party.other]; exact hfind
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    dsimp [cliRunStdSM]
    simp only [hgsIn, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      StateT.run_monadLift, monadLift_self, stateT_lift_run_cli, pure_bind, bind_assoc,
      map_eq_bind_pure_comp, Function.comp_def]
    rw [cliOracleImplR_deliver_run, hnone]
    simp only [pure_bind, Option.isNone_none, Bool.or_true, ↓reduceIte, bhMetaAfterSM,
      bhIsBobAcceptSMResp, Bool.and_false, Bool.false_eq_true]
    exact congrArg (fun z => (pure ((none, z), st) : ProbComp _)) hds_same

private theorem cliDrvSM_early_exit_coupled {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    {b : Bool} {qStart : ℕ} {qs_rem qs_rem' : ℕ → ℕ}
    (hqs : ∀ k, qs_rem' k ≤ qs_rem k)
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (i : ℕ) (q : (cliGameSmSpec ℓ (BitVec 512)).Domain)
    (hExit :
      bhDrvInstClean ds_cli i = false ∨
      ds_cli.bhInsts.length ≤ i ∨
      ∃ (hi_cli : i < ds_cli.bhInsts.length) (hi_mb : i < ds_cli.instMeta.length),
        (!(ds_cli.instMeta[i]'hi_mb).bobAccepted && bhIsBobRecvSMQuery q &&
          bhInstIkACorrupted ds_cli (ds_cli.bhInsts[i]'hi_cli)) = true) :
    cliAdapterStepCoupled X W b qStart qs_rem'
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e) := by
  have hRel_mono := cliAdapterDrvRel_mono_qs_rem hqs hRel
  by_cases hClean : bhDrvInstClean ds_cli i = true
  · have hClean_e2e : bhE2EDrvInstClean σ_e2e i = true :=
      (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
    rcases hExit with hC_false | hge_cli | ⟨hi_cli, hi_mb, hIkACorr⟩
    · rw [hClean] at hC_false; cases hC_false
    · have hge_e2e : σ_e2e.insts.length ≤ i := hRel.insts_len_eq ▸ hge_cli
      have hbi_none : ds_cli.bhInsts[i]? = none := List.getElem?_eq_none hge_cli
      have hd_none : σ_e2e.insts[i]? = none := List.getElem?_eq_none hge_e2e
      have h_cli_run :
          (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds_cli).run st_cli) =
            pure ((bhSmDefaultWithSpqr q, ds_cli), st_cli) := by
        unfold cliDrvSM
        simp [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hClean, hbi_none]
      have h_ad_run :
          (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
              (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e) =
            pure ((bhSmDefaultWithSpqr q, σ_ad), σ_e2e) := by
        refine cliComposedAdapterImplWith_sm_of_stepLocalSm_none (modelPrims X W) ki W.C W.Q.K qep
          decT encT i q σ_ad σ_e2e σ_e2e (fun sq _ => ?_) (Or.inl rfl)
        unfold bhE2EStepLocalSm
        simp [hClean_e2e, hd_none]
      rw [h_cli_run, h_ad_run]
      exact cliAdapterStepCoupled_ret (bhSmDefaultWithSpqr q) st_cli ds_cli σ_ad σ_e2e hRel_mono
    · have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
      have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
      have hCorr : (ds_cli.instMeta[i]'hi_mb).ikACorrAtAccept = false := by
        exact bhDrvInstClean_imp_ikACorrAtAccept_false hClean hi_cli hi_mb
      obtain ⟨inst, hinst_ad, hInstRel⟩ := hRel_mono.insts_rel i hi_cli hi_e2e hi_mb hi_me
      have hbi_opt : ds_cli.bhInsts[i]? = some ds_cli.bhInsts[i] := List.getElem?_eq_getElem hi_cli
      have hd_opt : σ_e2e.insts[i]? = some σ_e2e.insts[i] := List.getElem?_eq_getElem hi_e2e
      have him_opt : ds_cli.instMeta[i]? = some ds_cli.instMeta[i] := List.getElem?_eq_getElem hi_mb
      have hime_opt : σ_e2e.instMeta[i]? = some σ_e2e.instMeta[i] := List.getElem?_eq_getElem hi_me
      have hikA_eq :
          bhInstIkACorrupted ds_cli ds_cli.bhInsts[i] = bhE2EInstIkACorr σ_e2e σ_e2e.insts[i] :=
        bhInstIkACorrupted_eq_bhE2EInstIkACorr_of_cliRel hRel_mono hInstRel
      have h_cli_run :
          (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds_cli).run st_cli) =
            pure ((bhSmDefaultWithSpqr q,
              { ds_cli with
                instMeta := ds_cli.instMeta.set i
                  { ds_cli.instMeta[i] with bobAccepted := true, ikACorrAtAccept := true } }),
              st_cli) := by
        unfold cliDrvSM
        simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          pure_bind, hClean, hbi_opt, him_opt, hIkACorr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hq_bob : bhIsBobRecvSMQuery q = true := by
        simp only [Bool.and_eq_true] at hIkACorr
        exact hIkACorr.1.2
      have h_ad_run :
          (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
              (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e) =
            pure ((bhSmDefaultWithSpqr q, σ_ad),
              { σ_e2e with
                instMeta := σ_e2e.instMeta.set i
                  { σ_e2e.instMeta[i] with bobAccepted := true, ikACorrAtAccept := true } }) := by
        refine cliComposedAdapterImplWith_sm_of_stepLocalSm_none (modelPrims X W) ki W.C W.Q.K qep
          decT encT i q σ_ad σ_e2e _ (fun sq hsq => ?_) (Or.inr ⟨hq_bob, by rw [hinst_ad]; rfl⟩)
        have hIkACorr_e2e :
            (!σ_e2e.instMeta[i].bobAccepted && bhIsBobRecvSMQuery sq &&
              bhE2EInstIkACorr σ_e2e σ_e2e.insts[i]) = true := by
          rw [← hInstRel.im_eq, hsq, ← hikA_eq]
          exact hIkACorr
        unfold bhE2EStepLocalSm
        simp only [hClean_e2e, hd_opt, hime_opt, hIkACorr_e2e,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [h_cli_run, h_ad_run]
      refine cliAdapterStepCoupled_ret (bhSmDefaultWithSpqr q) st_cli _ σ_ad _ ?_
      refine
        { b_eq := hRel_mono.b_eq
          st_rel := hRel_mono.st_rel
          ki_inv := cliAdapterKeyIndInv_with_insts hRel_mono.ki_inv ds_cli.bhInsts _
          base_e2e_eq := hRel_mono.base_e2e_eq
          base_ad_eq := hRel_mono.base_ad_eq
          corrPrins_eq := hRel_mono.corrPrins_eq
          revealedSpks_eq := hRel_mono.revealedSpks_eq
          insts_len_le := hRel_mono.insts_len_le
          insts_len_eq := hRel_mono.insts_len_eq
          meta_cli_len_eq := by simp [hRel_mono.meta_cli_len_eq]
          meta_e2e_len_eq := by simp [hRel_mono.meta_e2e_len_eq]
          ad_none_of_ge := hRel_mono.ad_none_of_ge
          insts_rel := fun k hk_cli hk_e2e hk_mb hk_me => ?_ }
      simp only [List.length_set] at hk_mb hk_me
      by_cases hk : k = i
      · subst hk
        refine ⟨inst, hinst_ad, ?_⟩
        simp only [List.getElem_set_self]
        refine
          { im_eq := by rw [hInstRel.im_eq]
            sid_eq := hInstRel.sid_eq
            hdr_eq := hInstRel.hdr_eq
            idB_eq := hInstRel.idB_eq
            respSlot_eq := hInstRel.respSlot_eq
            respMeta_eq := hInstRel.respMeta_eq
            regIdA_eq := hInstRel.regIdA_eq
            regIdB_eq := hInstRel.regIdB_eq
            aliceAcked_false := hInstRel.aliceAcked_false
            idA_pub_eq := hInstRel.idA_pub_eq
            idB_pub_eq := hInstRel.idB_pub_eq
            extrasB_eq := hInstRel.extrasB_eq
            stB0_empty := hInstRel.stB0_empty
            resp_bundle_rel := hInstRel.resp_bundle_rel
            handshake_rel := ?_
            gs_rel := ?_ }
        · obtain ⟨bundleE, dk, aliceCoins, u_init, bnd, t_init, ss, h1, h2, h3, _⟩ :=
            hInstRel.handshake_rel
          exact ⟨bundleE, dk, aliceCoins, u_init, bnd, t_init, ss, h1, h2, h3,
            fun _ _ _ _ hcorr₁ _ => by cases hcorr₁⟩
        · have hgs := hInstRel.gs_rel
          cases h1 : ds_cli.bhInsts[k].gs with
          | none => rw [h1] at hgs; exact hgs
          | some gs_cli =>
            cases h2 : σ_e2e.insts[k].gs with
            | none => rw [h1, h2] at hgs; exact hgs
            | some gs_m =>
              rw [h1, h2] at hgs
              rcases hgs with ⟨hb_eq, hrest⟩
              simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
              exact ⟨hb_eq, hrest.2.1⟩
      · obtain ⟨inst_k, hinst_k, hRel_k⟩ := hRel_mono.insts_rel k hk_cli hk_e2e hk_mb hk_me
        refine ⟨inst_k, hinst_k, ?_⟩
        simp only [List.getElem_set_ne (Ne.symm hk)]
        exact cliAdapterInstRel_with_insts hRel_k ds_cli.bhInsts _
  · simp only [Bool.not_eq_true] at hClean
    have hClean_e2e : bhE2EDrvInstClean σ_e2e i = false :=
      (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
    have h_cli_run :
        (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds_cli).run st_cli) =
          pure ((bhSmDefaultWithSpqr q, ds_cli), st_cli) := by
      unfold cliDrvSM
      simp [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hClean]
    have h_ad_run :
        (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
            (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e) =
          pure ((bhSmDefaultWithSpqr q, σ_ad), σ_e2e) := by
      refine cliComposedAdapterImplWith_sm_of_stepLocalSm_none (modelPrims X W) ki W.C W.Q.K qep
        decT encT i q σ_ad σ_e2e σ_e2e (fun sq _ => ?_) (Or.inl rfl)
      unfold bhE2EStepLocalSm
      simp [hClean_e2e]
    rw [h_cli_run, h_ad_run]
    exact cliAdapterStepCoupled_ret (bhSmDefaultWithSpqr q) st_cli ds_cli σ_ad σ_e2e hRel_mono

/-! ## Bob deliver and inject step coupling -/

private theorem cliDrvSM_run_active {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (st_cli : SignalPqxdh.KeyIndState S) (ds_cli : ModelDriverState S ℓ) (i : ℕ)
    (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S) (gs_cli : SM.GameState BinState (Plain ℓ) Bytes)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain)
    (hClean : bhDrvInstClean ds_cli i = true)
    (hbi_opt : ds_cli.bhInsts[i]? = some bi)
    (him_opt : ds_cli.instMeta[i]? = some im)
    (hgs_cli : bi.gs = some gs_cli)
    (hNC : (!im.bobAccepted && bhIsBobRecvSMQuery q && bhInstIkACorrupted ds_cli bi) = false) :
    (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds_cli).run st_cli) =
      (((cliStepLocalSM S ℓ run W qep decT encT ds_cli i bi im gs_cli q).run ds_cli).run st_cli) := by
  unfold cliDrvSM
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hClean, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, hbi_opt, him_opt, hNC, hgs_cli]

set_option linter.unusedSimpArgs false in
private theorem cliRunStdSM_dlB_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (st_cli : SignalPqxdh.KeyIndState S) (ds_cli : ModelDriverState S ℓ) (i : ℕ)
    (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S) (gs_cli : SM.GameState BinState (Plain ℓ) Bytes)
    (c : Bytes) :
    (((cliRunStdSM S ℓ run W qep decT encT ds_cli i bi im gs_cli
        (.inl (.inl (.inr (.B, c))))).run ds_cli).run st_cli) =
      let gsIn := bhAlignTransForBob im.bobAccepted bi.meA.regId bi.hdr c gs_cli
      ((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
          (2 + 1) qep (bhConfigSpkS decT encT) (.inl (.inl (.inr (.B, c))))).run gsIn >>= fun x =>
        let gs' : SM.GameState BinState (Plain ℓ) Bytes :=
          match x.1 with
          | some (.accepted _ _ _) =>
            match gsIn.inTransit .A c with
            | some rMatched =>
              { x.2 with trans := gs_cli.trans.filter (fun rec => rec.pos != rMatched.pos) }
            | none => { x.2 with trans := gs_cli.trans }
          | _ => { x.2 with trans := gs_cli.trans }
        let im' := bhMetaAfterSM ds_cli bi im (.inl (.inl (.inr (.B, c)))) x.1
        pure ((x.1, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gs' },
                                  instMeta := ds_cli.instMeta.set i im' }), st_cli)) := by
  dsimp [cliRunStdSM]
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
    StateT.run_monadLift, monadLift_self, stateT_lift_run_cli, pure_bind, bind_assoc,
    map_eq_bind_pure_comp, Function.comp_def, liftM, monadLift, MonadLift.monadLift]
  congr 1
  funext x
  cases x.1 with
  | none => rfl
  | some r => cases r <;> rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem cliDrvSM_bob_dl_active {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hSpec : CliSpecPqxdh run X W)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliE2ERemoteIdInv σ_e2e)
    (hGood : cliClause2BadKemBool S (modelPrims X W) st_cli ds_cli = false)
    (i : ℕ) (c : Bytes)
    (hClean : bhDrvInstClean ds_cli i = true)
    (hi_cli : i < ds_cli.bhInsts.length)
    (hNC : (!(ds_cli.instMeta[i]'(hRel.meta_cli_len_eq.symm ▸ hi_cli)).bobAccepted &&
      bhInstIkACorrupted ds_cli ds_cli.bhInsts[i]) = false)
    (hq_pos : 0 < qs_rem i) :
    cliAdapterStepCoupled X W b qStart (fun k => if k = i then qs_rem k - 1 else qs_rem k)
      (((cliDrvSM S ℓ run W qep decT encT ext
          ⟨i, .inl (.inl (.inr (.B, c)))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inr (.B, c)))⟩)).run σ_ad).run σ_e2e) := by
  have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
  have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
  have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
  have hCorr : (ds_cli.instMeta[i]'hi_mb).ikACorrAtAccept = false := by
    exact bhDrvInstClean_imp_ikACorrAtAccept_false hClean hi_cli hi_mb
  obtain ⟨inst, hinst_ad, hInstRel⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
  have hikA_eq :
      bhInstIkACorrupted ds_cli ds_cli.bhInsts[i] = bhE2EInstIkACorr σ_e2e σ_e2e.insts[i] :=
    bhInstIkACorrupted_eq_bhE2EInstIkACorr_of_cliRel hRel hInstRel
  have hNC_e2e :
      (!σ_e2e.instMeta[i].bobAccepted && bhE2EInstIkACorr σ_e2e σ_e2e.insts[i]) = false := by
    rw [← hInstRel.im_eq, ← hikA_eq]; exact hNC
  set bi := ds_cli.bhInsts[i]
  set d := σ_e2e.insts[i]
  set im := ds_cli.instMeta[i]
  set im_e2e := σ_e2e.instMeta[i]
  have hbi_opt : ds_cli.bhInsts[i]? = some bi := List.getElem?_eq_getElem hi_cli
  have hd_opt : σ_e2e.insts[i]? = some d := List.getElem?_eq_getElem hi_e2e
  have him_opt : ds_cli.instMeta[i]? = some im := List.getElem?_eq_getElem hi_mb
  have hime_opt : σ_e2e.instMeta[i]? = some im_e2e := List.getElem?_eq_getElem hi_me
  have hClean_e2e : bhE2EDrvInstClean σ_e2e i = true :=
    (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
  have hgs := hInstRel.gs_rel
  cases hgs_cli : bi.gs with
  | none => rw [hgs_cli] at hgs; exact False.elim hgs
  | some gs_cli =>
    cases hgs_m : d.gs with
    | none => rw [hgs_cli, hgs_m] at hgs; exact False.elim hgs
    | some gs_m =>
      have hremB : (gs_m.st .B).session.remoteIdentity = some d.idA :=
        (hRem d (List.getElem_mem hi_e2e) gs_m hgs_m).2
      rw [hgs_cli, hgs_m] at hgs
      rcases hgs with ⟨hb_eq, hrest⟩
      simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
      rcases hrest with
        ⟨h_acc, h_win, h_ep, h_idx, h_max, h_ch, h_comp, h_tL, h_lk, h_cr,
         h_tr, _, _, _, _, _, _, _, _, _,
         h_epB1, _, h_stB0, h_stB1, _, h_pB, _, h_actB⟩
      have hds_same := bhDrvState_set_same_gs_cli ds_cli i hi_cli hi_mb gs_cli hgs_cli
      have he2e_same := bhE2EDrvState_set_same_gs_cli σ_e2e i hi_e2e hi_me gs_m hgs_m
      have hR := cliAdapterDrvRel_decrement_i i hRel
      rw [cliDrvSM_run_active run W qep decT encT ext st_cli ds_cli i bi im gs_cli
            (.inl (.inl (.inr (.B, c)))) hClean hbi_opt him_opt hgs_cli
            (by simpa [bhIsBobRecvSMQuery] using hNC),
          cliComposedAdapterImplWith_dl_B_run, hinst_ad]
      dsimp only [cliStepLocalSM]
      have hreg : bi.meA.regId = bhInitRegId d.sid := hInstRel.regIdA_eq.1
      have hhdr : bi.hdr = d.hdr := hInstRel.hdr_eq.1
      have hacc_e : im_e2e.bobAccepted = im.bobAccepted := by rw [hInstRel.im_eq]
      have hidA_bi : d.idA = bhIdKeyOf bi.hdr.ikAPk := by
        rw [hInstRel.idB_eq.2.1, hhdr]
      have hdummy : ∀ c', (c' = [] ∨ ∃ body, c' = wireWhisper :: body) →
          cliAdapterStepCoupled X W b qStart (fun k => if k = i then qs_rem k - 1 else qs_rem k)
            (pure (((none : Option (SM.RecvResult (Plain ℓ))), ds_cli), st_cli))
            (bhE2EStepLocalSm W.C W.Q.K qep decT encT σ_e2e i (.inl (.inr (.B, c'))) >>=
              fun (x : BHE2ESmResp ℓ × BHE2EDrvState S ℓ) =>
                pure (((none : Option (SM.RecvResult (Plain ℓ))), σ_ad), x.2)) := fun c' hc' =>
        cliAdapterStepCoupled_discard (none : Option (SM.RecvResult (Plain ℓ))) st_cli ds_cli σ_ad σ_e2e _
          (fun (x : BHE2ESmResp ℓ × BHE2EDrvState S ℓ) => x.2)
          (bhE2EStepLocalSm_inject_B_noop_cli W.C W.Q.K qep decT encT σ_e2e i hi_e2e hi_me gs_m
            hgs_m hNC_e2e c' hc') hR
      have hnoop := cliStepLocalSM_dlB_noop run W qep decT encT ds_cli st_cli i hi_cli hi_mb gs_cli
        hgs_cli h_tr c
      cases hd : bhDecodePreKeyMsgE c with
      | some m =>
        dsimp only
        cases hinner : m.inner with
        | nil =>
          dsimp only
          refine cliAdapterStepCoupled_congr_cli (hnoop ?_) (hdummy [] (Or.inl rfl))
          intro inner hp
          left
          have h1 := bhPartneredInnerBytes_wire_cli _ _ _ _ _ hp
          unfold bhWireInnerBytes at h1
          simp only [hd, hinner, Option.some.injEq] at h1
          exact h1.symm
        | cons x xs =>
          dsimp only
          have hne : m.inner ≠ [] := by rw [hinner]; exact List.cons_ne_nil _ _
          obtain ⟨hc_eq, _⟩ := bhDecodePreKeyMsgE_eq_some_imp hd
          subst hc_eq
          cases hacc : im.bobAccepted
          ·
            have hacc_m : im_e2e.bobAccepted = false := hacc_e.trans hacc
            have hik : bhE2EInstIkACorr σ_e2e d = false := by simpa [hacc_m] using hNC_e2e
            have hikcli : bhInstIkACorrupted ds_cli bi = false := by simpa [hacc] using hNC
            unfold bhE2EStepLocalSm
            simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, hacc_m, hd, hik, bhIsBobRecvSMQuery,
              Bool.not_false, Bool.not_true, Bool.true_and, Bool.and_true, Bool.and_false,
              Bool.false_eq_true, ↓reduceIte, pure_bind]
            by_cases hexp : (wirePrekey :: m.bytes) =
                wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes
            · have hexpb : ((wirePrekey :: m.bytes) ==
                  wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes) = true :=
                beq_iff_eq.mpr hexp
              have hp : bhPartneredInnerBytes false bi.meA.regId bi.hdr (wirePrekey :: m.bytes) =
                  some m.inner := by
                unfold bhPartneredInnerBytes
                simp only [Bool.not_false, ↓reduceIte, hd, hreg, hhdr, hexpb]
              have htr0 := h_tr
              rw [hacc] at htr0
              have hfind := cliAdapterTrans_find?_A_prekey htr0 m.inner hne
              rw [← hexp] at hfind
              have hcond :
                  (gs_cli.win || (gs_cli.inTransit Party.B.other (wirePrekey :: m.bytes)).isNone) =
                    (gs_m.win || (gs_m.inTransit Party.B.other m.inner).isNone) := by
                have := congrArg Option.isNone hfind
                simp only [Option.isNone_map] at this
                simp only [SM.GameState.inTransit, Party.other]
                rw [this, h_win]
              simp only [hexpb, hacc, hp, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
                bind_assoc, pure_bind]
              rw [cliRunStdSM_dlB_run]
              have hgsIn_eq :
                  bhAlignTransForBob false bi.meA.regId bi.hdr (wirePrekey :: m.bytes) gs_cli = gs_cli := by
                unfold bhAlignTransForBob; rfl
              simp only [hacc, hgsIn_eq]
              refine cliAdapterStepCoupled_deliver _ _ _ _ gs_cli gs_m
                (fun rc => deliverRPure (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                  (bhConfigSpkS decT encT) .B (wirePrekey :: m.bytes) rc gs_cli)
                (fun rc => deliverRPure
                  (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                    ℓ d.spkCoins)
                  (configRefuseEarlyBobCorr decT encT) .B m.inner rc gs_m)
                (cliOracleImplR_deliver_run _ _ _ _ _ _ _)
                (cliOracleImplR_deliver_run _ _ _ _ _ _ _) hcond
                _ _ ?_ ?_
              · intro _
                refine ⟨rfl, ?_⟩
                simp only [bhMetaAfterSM, bhIsBobAcceptSMResp, Bool.and_false, Bool.false_eq_true,
                  ↓reduceIte, cliBobAdapterUpdate, bhPackSmResp]
                rw [hds_same, he2e_same]
                exact hR
              · intro hf rc
                have hf_cli := hcond.trans hf
                rcases hr_m : gs_m.inTransit Party.B.other m.inner with _ | r_m
                · rw [hr_m] at hf; simp at hf
                rcases hr_cli : gs_cli.inTransit Party.B.other (wirePrekey :: m.bytes) with _ | r_cli
                · rw [hr_cli] at hf_cli; simp at hf_cli
                have hw_m : gs_m.win = false := (Bool.or_eq_false_iff.mp hf).1
                have hw_cli : gs_cli.win = false := (Bool.or_eq_false_iff.mp hf_cli).1
                have hr_m' := hr_m
                have hr_cli' := hr_cli
                simp only [SM.GameState.inTransit, Party.other] at hr_m' hr_cli'
                have hpm := hfind
                rw [hr_m', hr_cli'] at hpm
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpm
                obtain ⟨hpos, -⟩ := hpm
                have hmem : r_m ∈ gs_m.trans := List.mem_of_find?_eq_some hr_m'
                have hsat := List.find?_some hr_m'
                simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsat
                obtain ⟨_, hct⟩ := hsat
                have hlenm := cliAdapterTrans_m_ct_len h_tr r_m hmem (by rw [hct]; exact hne)
                rw [hct] at hlenm
                have hexp_bi : wirePrekey :: m.bytes =
                    wirePrekey :: (bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner).bytes := by
                  rw [hreg, hhdr]; exact hexp
                have hm_exp_bi : m = bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner := by
                  have h1 := congrArg bhDecodePreKeyMsgE hexp_bi
                  rw [bhDecodePreKeyMsgE_wirePrekey, bhDecodePreKeyMsgE_wirePrekey] at h1
                  exact Option.some.inj h1
                obtain ⟨bEntry, hb_mem, hd_spkCoins, hspk_gen, _, _⟩ := hInstRel.resp_bundle_rel
                obtain ⟨_, dk, aliceCoins, u_init, bnd, t_init, ss, _, hTape, hSpkRel, hInitB⟩ :=
                  hInstRel.handshake_rel
                obtain ⟨hPk_eq, hEnc_eq, hDecImp⟩ := hSpkRel bEntry hb_mem
                have hDec : (modelPrims X W).kemDecaps bEntry.pqspkSk d.hdr.kemCt = some ss :=
                  not_cliClause2BadKemBool_decaps_eq hGood hTape hb_mem hPk_eq.symm
                    (by rw [hPk_eq]; exact hEnc_eq)
                obtain ⟨hspkId, hkpkId, hacc_dk⟩ := hDecImp hDec m.inner
                have hfirst := cliPqRecv_prekey_first_spec hSpec bi (cliPqSigsOf st_cli bi)
                  d.idA d.idB d.spkCoins aliceCoins dk (qs_rem i) m.inner rc
                  hidA_bi
                  (hInstRel.idB_eq.2.2.trans hInstRel.idB_pub_eq)
                  (by rw [hd_spkCoins]; exact hspk_gen)
                  hlenm.2
                  (wirePrekey_len_le_stdinCap_of_inner_le
                    (m := bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner) hlenm.1)
                  ⟨hspkId, hkpkId⟩
                  hacc_dk
                have hgB0_m :
                    (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                      ℓ d.spkCoins).initB (bhKeySOf dk aliceCoins) = gs_m.st .B :=
                  (hInitB gs_cli gs_m hgs_cli hgs_m (by simp [hCorr]) (by simp [hacc])).symm
                have hxB_inst : bhRecvExtrasOfHdr bi.meA bi.meB bi.hdr = bhInstExtrasB inst := by
                  rw [hInstRel.extrasB_eq, hhdr]
                dsimp only at hfirst
                rw [← hm_exp_bi, ← hInstRel.stB0_empty, hgB0_m, hxB_inst] at hfirst
                have hstB_cli : gs_cli.st .B = bi.stB0 := h_stB0 (by simp [hacc])
                rcases hrm : (sessionSchemeFixedSpk
                    (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                    ℓ d.spkCoins).receive (gs_m.st .B) m.inner rc with _ | ⟨g', t', i', m'⟩
                · have hrb : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                      (gs_cli.st .B) (wirePrekey :: m.bytes) rc = none := by
                    rw [hstB_cli, hfirst.1, hrm]; rfl
                  rw [cliDeliverRPure_reject _ _ _ _ _ _ r_cli hw_cli hr_cli
                        (bhConfigSpkS_must_cli _ _ _ _ _) hrb,
                      cliDeliverRPure_reject _ _ _ _ _ _ r_m hw_m hr_m rfl hrm]
                  refine ⟨rfl, ?_⟩
                  simp only [bhMetaAfterSM, bhIsBobAcceptSMResp, Bool.and_false, Bool.false_eq_true,
                    ↓reduceIte, cliBobAdapterUpdate, bhPackSmResp]
                  rw [hds_same, he2e_same]
                  exact hR
                · have hrb : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                      (gs_cli.st .B) (wirePrekey :: m.bytes) rc =
                      some (binStateOfUnderExtras (fun _ => bhInstExtrasB inst) g', t', i', m') := by
                    rw [hstB_cli, hfirst.1, hrm]; rfl
                  obtain ⟨hg'_party, hg'_ep1, hg'_ppk, _, hg'_actB⟩ :=
                    hfirst.2 g' t' i' m' hrm hq_pos
                  rw [cliDeliverRPure_accept _ _ _ _ _ _ r_cli _ _ _ _ hw_cli hr_cli
                        (bhConfigSpkS_must_cli _ _ _ _ _) hrb,
                      cliDeliverRPure_accept _ _ _ _ _ _ r_m _ _ _ _ hw_m hr_m rfl hrm]
                  refine ⟨by simp only [hpos, h_ch, bhPackSmResp], ?_⟩
                  have hregm : m.regId = inst.bobRemoteRegId := by
                    rw [hInstRel.regIdA_eq.2, hm_exp_bi, hreg]; rfl
                  have hinst' : (bhShallowUpdateInstMeta inst false true
                      (wirePrekey :: m.bytes)).2 =
                      { inst with bobAccepted := true } :=
                    bhAdapterUpdateInstMeta_bob_eq_cli decT encT inst _
                      (fun m0 hm0 _ => by rw [hd] at hm0; cases hm0; exact hregm)
                  have hrA : gs_cli.inTransit Party.A (wirePrekey :: m.bytes) = some r_cli := hr_cli
                  simp only [hrA, bhMetaAfterSM, bhIsBobAcceptSMResp, hacc, hikcli, hik,
                    Bool.not_false, Bool.true_and, ↓reduceIte]
                  refine cliAdapterDrvRel_update_inst hRel hi_cli _ _ _ _
                    { inst with bobAccepted := true } (σ_ad.2.1 i) rfl
                    (by simp only [cliBobAdapterUpdate, bhPackSmResp, ↓reduceIte]; exact congrArg some hinst')
                    rfl
                    (fun k hk => by simp only [cliBobAdapterUpdate, bhPackSmResp, hk, ↓reduceIte])
                    (fun _ _ => rfl) ?_
                  rw [← hInstRel.im_eq]
                  refine cliAdapterInstRel_with_insts
                    (cliAdapterInstRel_of_bob_recv_accept (Nat.sub_le _ _) hInstRel hgs_cli hgs_m
                      hCorr g' rfl (by simp [hCorr]) (by exact ⟨rfl, rfl⟩)
                      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                      hg'_party hg'_ppk (by omega) hg'_actB) _ _
                  · simpa [SM.GameState.accept, SM.GameState.delete] using hb_eq
                  · simpa [SM.GameState.accept, SM.GameState.delete] using h_win
                  · simp only [SM.GameState.accept, SM.GameState.delete, h_ep, hpos]
                  · simpa [SM.GameState.accept, SM.GameState.delete] using h_idx
                  · simp only [SM.GameState.accept, SM.GameState.delete, h_max, hpos]
                  · simp only [SM.GameState.accept, SM.GameState.delete, h_ch, hpos]
                  · simp only [SM.GameState.accept, SM.GameState.delete, h_comp, hpos]
                  · simpa [SM.GameState.accept, SM.GameState.delete] using h_tL
                  · simpa [SM.GameState.accept, SM.GameState.delete] using h_lk
                  · simpa [SM.GameState.accept, SM.GameState.delete] using h_cr
                  · simp only [SM.GameState.accept, SM.GameState.delete]
                    rw [hpos]; exact cliAdapterTrans_filter_pos h_tr r_m.pos
                  · rfl
                  · show Function.update _ _ _ = _
                    simp only [bhBinStateOfParty, hg'_party]; rfl
            · have hexpb : ((wirePrekey :: m.bytes) ==
                  wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes) = false := by
                simpa using hexp
              have hp : bhPartneredInnerBytes false bi.meA.regId bi.hdr (wirePrekey :: m.bytes) = none := by
                unfold bhPartneredInnerBytes
                simp only [Bool.not_false, ↓reduceIte, hd, hreg, hhdr, hexpb, Bool.false_eq_true]
              simp only [hexpb, hacc, hp, Option.isNone_none, Bool.false_eq_true, ↓reduceIte,
                StateT.run_pure, pure_bind]
              exact cliAdapterStepCoupled_ret _ _ _ _ _ hR
          ·
            have hacc_m : im_e2e.bobAccepted = true := hacc_e.trans hacc
            unfold bhE2EStepLocalSm
            simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, hacc_m, hd, bhIsBobRecvSMQuery,
              Bool.not_false, Bool.not_true, Bool.true_and, Bool.and_true, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte, pure_bind]
            by_cases hh : bhHdrOfPreKeyMsg m = d.hdr
            · have hhb : (bhHdrOfPreKeyMsg m == d.hdr) = true := beq_iff_eq.mpr hh
              have hhb_bi : (bhHdrOfPreKeyMsg m == bi.hdr) = true := beq_iff_eq.mpr (hh.trans hhdr.symm)
              have hp : bhPartneredInnerBytes true bi.meA.regId bi.hdr (wirePrekey :: m.bytes) =
                  some m.inner := by
                unfold bhPartneredInnerBytes
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, hhb_bi]
              have hw := bhPartneredInnerBytes_wire_cli _ _ _ _ _ hp
              have hfind := cliAdapterAlignTransList_find?_A h_tr hw hne
              have hcond :
                  (({ gs_cli with trans := bhAlignTransList m.inner (wirePrekey :: m.bytes) gs_cli.trans } :
                        SM.GameState BinState (Plain ℓ) Bytes).win ||
                      (({ gs_cli with trans := bhAlignTransList m.inner (wirePrekey :: m.bytes) gs_cli.trans } :
                        SM.GameState BinState (Plain ℓ) Bytes).inTransit Party.B.other (wirePrekey :: m.bytes)).isNone) =
                    (gs_m.win || (gs_m.inTransit Party.B.other m.inner).isNone) := by
                have := congrArg Option.isNone hfind
                simp only [Option.isNone_map] at this
                simp only [SM.GameState.inTransit, Party.other]
                rw [this, h_win]
              simp only [hhb, hacc, hp, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
                bind_assoc, pure_bind]
              rw [cliRunStdSM_dlB_run]
              have hgsIn :
                  bhAlignTransForBob true bi.meA.regId bi.hdr (wirePrekey :: m.bytes) gs_cli =
                    { gs_cli with trans := bhAlignTransList m.inner (wirePrekey :: m.bytes) gs_cli.trans } := by
                unfold bhAlignTransForBob
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hp]
              simp only [hacc, hgsIn]
              set gsIn : SM.GameState BinState (Plain ℓ) Bytes :=
                { gs_cli with trans := bhAlignTransList m.inner (wirePrekey :: m.bytes) gs_cli.trans }
                with hgsIn_def
              have hbinB : gs_cli.st .B = binStateOfUnderExtras (fun _ => bhInstExtrasB inst) (gs_m.st .B) := by
                rw [h_stB1 hacc]; simp only [bhBinStateOfParty, h_pB]
              refine cliAdapterStepCoupled_deliver _ _ _ _ gsIn gs_m
                (fun rc => deliverRPure (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                  (bhConfigSpkS decT encT) .B (wirePrekey :: m.bytes) rc gsIn)
                (fun rc => deliverRPure
                  (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                    ℓ d.spkCoins)
                  (configRefuseEarlyBobCorr decT encT) .B m.inner rc gs_m)
                (cliOracleImplR_deliver_run _ _ _ _ _ _ _)
                (cliOracleImplR_deliver_run _ _ _ _ _ _ _) hcond
                _ _ ?_ ?_
              · intro _
                refine ⟨rfl, ?_⟩
                simp only [bhMetaAfterSM, hacc, Bool.not_true, Bool.false_and, Bool.false_eq_true,
                  ↓reduceIte, cliBobAdapterUpdate, bhPackSmResp, hgsIn_def]
                rw [hds_same, he2e_same]
                exact hR
              · intro hf rc
                have hf_cli := hcond.trans hf
                rcases hr_m : gs_m.inTransit Party.B.other m.inner with _ | r_m
                · rw [hr_m] at hf; simp at hf
                rcases hr_cli : gsIn.inTransit Party.B.other (wirePrekey :: m.bytes) with _ | r_cli
                · rw [hr_cli] at hf_cli; simp at hf_cli
                have hw_m : gs_m.win = false := (Bool.or_eq_false_iff.mp hf).1
                have hw_cli : gsIn.win = false := (Bool.or_eq_false_iff.mp hf_cli).1
                have hr_m' := hr_m
                have hr_cli' := hr_cli
                simp only [SM.GameState.inTransit, Party.other] at hr_m' hr_cli'
                have hpm := hfind
                rw [hr_m'] at hpm
                rw [hgsIn_def] at hr_cli'
                rw [hr_cli'] at hpm
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpm
                obtain ⟨hpos, -⟩ := hpm
                have hmem : r_m ∈ gs_m.trans := List.mem_of_find?_eq_some hr_m'
                have hsat := List.find?_some hr_m'
                simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsat
                obtain ⟨_, hct⟩ := hsat
                have hlenm := cliAdapterTrans_m_ct_len h_tr r_m hmem (by rw [hct]; exact hne)
                rw [hct] at hlenm
                have hmatched := cliPqRecv_prekey_matched_spec hSpec bi (cliPqSigsOf st_cli bi)
                  d.idA d.idB d.spkCoins (bhInstExtrasB inst) (gs_m.st .B) (qs_rem i)
                  (wirePrekey :: m.bytes) m rc
                  (h_actB hacc) hq_pos h_pB (h_epB1 hacc)
                  (by rw [hInstRel.extrasB_eq, ← hhdr]; rfl)
                  hidA_bi hremB hd hhb_bi hlenm.2
                  (wirePrekey_len_le_stdinCap_of_inner_le hlenm.1)
                dsimp only at hmatched
                have hstIn : gsIn.st .B = binStateOfUnderExtras (fun _ => bhInstExtrasB inst) (gs_m.st .B) := hbinB
                rcases hrm : (sessionSchemeFixedSpk
                    (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                    ℓ d.spkCoins).receive (gs_m.st .B) m.inner rc with _ | ⟨g', t', i', m'⟩
                · have hrb : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                      (gsIn.st .B) (wirePrekey :: m.bytes) rc = none := by
                    rw [hstIn, hmatched.1, hrm]; rfl
                  rw [cliDeliverRPure_reject _ _ _ _ _ _ r_cli hw_cli hr_cli
                        (bhConfigSpkS_must_cli _ _ _ _ _) hrb,
                      cliDeliverRPure_reject _ _ _ _ _ _ r_m hw_m hr_m rfl hrm]
                  refine ⟨rfl, ?_⟩
                  simp only [bhMetaAfterSM, hacc, Bool.not_true, Bool.false_and, Bool.false_eq_true,
                    ↓reduceIte, cliBobAdapterUpdate, bhPackSmResp, hgsIn_def]
                  rw [hds_same, he2e_same]
                  exact hR
                · have hrb : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                      (gsIn.st .B) (wirePrekey :: m.bytes) rc =
                      some (binStateOfUnderExtras (fun _ => bhInstExtrasB inst) g', t', i', m') := by
                    rw [hstIn, hmatched.1, hrm]; rfl
                  obtain ⟨hg'_party, hg'_ep, hg'_ppk, _, hg'_actB⟩ :=
                    hmatched.2 g' t' i' m' hrm
                  rw [cliDeliverRPure_accept _ _ _ _ _ _ r_cli _ _ _ _ hw_cli hr_cli
                        (bhConfigSpkS_must_cli _ _ _ _ _) hrb,
                      cliDeliverRPure_accept _ _ _ _ _ _ r_m _ _ _ _ hw_m hr_m rfl hrm]
                  refine ⟨by simp only [hgsIn_def, hpos, h_ch, bhPackSmResp], ?_⟩
                  have hib : inst.bobAccepted = true := h_acc ▸ hacc
                  have hinst' : (bhShallowUpdateInstMeta inst false true
                      (wirePrekey :: m.bytes)).2 = inst := by
                    rw [bhAdapterUpdateInstMeta_bob_eq_cli decT encT inst _
                      (fun _ _ h => by rw [hib] at h; cases h)]
                    exact bhAdapterInstMeta_with_bobAccepted_self_cli inst hib
                  have hrA : gsIn.inTransit Party.A (wirePrekey :: m.bytes) = some r_cli := hr_cli
                  simp only [hrA, bhMetaAfterSM, hacc, Bool.not_true, Bool.false_and,
                    Bool.false_eq_true, ↓reduceIte]
                  refine cliAdapterDrvRel_update_inst hRel hi_cli _ _ im im_e2e inst (σ_ad.2.1 i) rfl
                    (by simp only [cliBobAdapterUpdate, bhPackSmResp, ↓reduceIte]; exact congrArg some hinst')
                    rfl
                    (fun k hk => by simp only [cliBobAdapterUpdate, bhPackSmResp, hk, ↓reduceIte])
                    (fun _ _ => rfl) ?_
                  rw [← hInstRel.im_eq, ← bhAdapterInstMeta_with_bobAccepted_self_cli inst hib]
                  refine cliAdapterInstRel_with_insts
                    (cliAdapterInstRel_of_bob_recv_accept (Nat.sub_le _ _) hInstRel hgs_cli hgs_m
                      hCorr g' hacc hCorr (by exact ⟨rfl, rfl⟩)
                      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                      hg'_party hg'_ppk hg'_ep hg'_actB) _ _
                  · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using hb_eq
                  · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using h_win
                  · simp only [hgsIn_def, SM.GameState.accept, SM.GameState.delete, h_ep, hpos]
                  · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using h_idx
                  · simp only [hgsIn_def, SM.GameState.accept, SM.GameState.delete, h_max, hpos]
                  · simp only [hgsIn_def, SM.GameState.accept, SM.GameState.delete, h_ch, hpos]
                  · simp only [hgsIn_def, SM.GameState.accept, SM.GameState.delete, h_comp, hpos]
                  · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using h_tL
                  · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using h_lk
                  · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using h_cr
                  · simp only [SM.GameState.accept, SM.GameState.delete]
                    rw [hpos]; exact cliAdapterTrans_filter_pos h_tr r_m.pos
                  · rfl
                  · show Function.update _ _ _ = _
                    simp only [hgsIn_def, bhBinStateOfParty, hg'_party]; rfl
            · have hhb : (bhHdrOfPreKeyMsg m == d.hdr) = false := by simpa using hh
              have hhb_bi : (bhHdrOfPreKeyMsg m == bi.hdr) = false := by rw [hhdr]; exact hhb
              have hp : bhPartneredInnerBytes true bi.meA.regId bi.hdr (wirePrekey :: m.bytes) = none := by
                unfold bhPartneredInnerBytes
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, hhb_bi]
              simp only [hhb, hacc, hp, Option.isNone_none, Bool.false_eq_true, ↓reduceIte,
                StateT.run_pure, pure_bind]
              exact cliAdapterStepCoupled_ret _ _ _ _ _ hR
      | none =>
        dsimp only
        rcases c with _ | ⟨t, body⟩
        · refine cliAdapterStepCoupled_congr_cli (hnoop ?_) (hdummy [] (Or.inl rfl))
          intro inner hp
          have h1 := bhPartneredInnerBytes_wire_cli _ _ _ _ _ hp
          rw [bhWireInnerBytes_nil_cli] at h1; cases h1
        · by_cases ht : t = wireWhisper
          · subst ht
            simp only [beq_self_eq_true, ↓reduceIte]
            have hw : bhWireInnerBytes (wireWhisper :: body) = some body :=
              bhWireInnerBytes_wireWhisper_cli body
            cases hdb : bhDecodePreKeyMsgE body with
            | some mb =>
              dsimp only
              refine cliAdapterStepCoupled_congr_cli (hnoop ?_) (hdummy _ (Or.inr ⟨body, rfl⟩))
              intro inner hp
              have h1 := bhPartneredInnerBytes_wire_cli _ _ _ _ _ hp
              rw [hw] at h1; obtain rfl := Option.some.inj h1
              right; rw [hdb]; rfl
            | none =>
              dsimp only
              rcases body with _ | ⟨b0, bs⟩
              · refine cliAdapterStepCoupled_congr_cli (hnoop ?_) (hdummy [] (Or.inl rfl))
                intro inner hp
                have h1 := bhPartneredInnerBytes_wire_cli _ _ _ _ _ hp
                rw [hw] at h1; left; exact (Option.some.inj h1).symm
              · dsimp only
                have hdc6 : bhDecodePreKeyMsgE (wireWhisper :: b0 :: bs) = none := hd
                cases hacc : im.bobAccepted
                · have hp : bhPartneredInnerBytes false bi.meA.regId bi.hdr
                      (wireWhisper :: b0 :: bs) = none := by
                    unfold bhPartneredInnerBytes; rw [hdc6]; rfl
                  have hacc_m : im_e2e.bobAccepted = false := hacc_e.trans hacc
                  simp only [hp, Option.isNone_none, ↓reduceIte, StateT.run_pure]
                  unfold bhE2EStepLocalSm
                  simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, hacc_m, hdb, bhIsBobRecvSMQuery,
                    Bool.not_false, Bool.not_true, Bool.true_and, Bool.and_true, Bool.false_eq_true,
                    ↓reduceIte, pure_bind]
                  have hik : bhE2EInstIkACorr σ_e2e d = false := by simpa [hacc_m] using hNC_e2e
                  simp only [hik, Bool.false_eq_true, ↓reduceIte, pure_bind]
                  exact cliAdapterStepCoupled_ret _ _ _ _ _ hR
                · have hp : bhPartneredInnerBytes true bi.meA.regId bi.hdr
                      (wireWhisper :: b0 :: bs) = some (b0 :: bs) := by
                    unfold bhPartneredInnerBytes; rw [hdc6]; simp
                  have hacc_m : im_e2e.bobAccepted = true := hacc_e.trans hacc
                  have hne : (b0 :: bs) ≠ [] := List.cons_ne_nil _ _
                  have hgsIn :
                      bhAlignTransForBob true bi.meA.regId bi.hdr (wireWhisper :: b0 :: bs) gs_cli =
                        { gs_cli with trans := bhAlignTransList (b0 :: bs) (wireWhisper :: b0 :: bs) gs_cli.trans } := by
                    unfold bhAlignTransForBob
                    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hp]
                  have hfind := cliAdapterAlignTransList_find?_A h_tr hw hne
                  have hcond :
                      (({ gs_cli with trans := bhAlignTransList (b0 :: bs) (wireWhisper :: b0 :: bs) gs_cli.trans } :
                            SM.GameState BinState (Plain ℓ) Bytes).win ||
                          (({ gs_cli with trans := bhAlignTransList (b0 :: bs) (wireWhisper :: b0 :: bs) gs_cli.trans } :
                            SM.GameState BinState (Plain ℓ) Bytes).inTransit Party.B.other (wireWhisper :: b0 :: bs)).isNone) =
                        (gs_m.win || (gs_m.inTransit Party.B.other (b0 :: bs)).isNone) := by
                    have := congrArg Option.isNone hfind
                    simp only [Option.isNone_map] at this
                    simp only [SM.GameState.inTransit, Party.other]
                    rw [this, h_win]
                  simp only [hp, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
                  rw [cliRunStdSM_dlB_run]
                  simp only [hacc, hgsIn]
                  unfold bhE2EStepLocalSm
                  simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, hacc_m, hdb, bhIsBobRecvSMQuery,
                    Bool.not_false, Bool.not_true, Bool.true_and, Bool.and_true, Bool.false_and,
                    Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
                  set gsIn : SM.GameState BinState (Plain ℓ) Bytes :=
                    { gs_cli with trans := bhAlignTransList (b0 :: bs) (wireWhisper :: b0 :: bs) gs_cli.trans }
                    with hgsIn_def
                  have hbinB : gs_cli.st .B = binStateOfUnderExtras (fun _ => bhInstExtrasB inst) (gs_m.st .B) := by
                    rw [h_stB1 hacc]; simp only [bhBinStateOfParty, h_pB]
                  refine cliAdapterStepCoupled_deliver _ _ _ _ gsIn gs_m
                    (fun rc => deliverRPure (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                      (bhConfigSpkS decT encT) .B (wireWhisper :: b0 :: bs) rc gsIn)
                    (fun rc => deliverRPure
                      (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                        ℓ d.spkCoins)
                      (configRefuseEarlyBobCorr decT encT) .B (b0 :: bs) rc gs_m)
                    (cliOracleImplR_deliver_run _ _ _ _ _ _ _)
                    (cliOracleImplR_deliver_run _ _ _ _ _ _ _) hcond
                    _ _ ?_ ?_
                  · intro _
                    refine ⟨rfl, ?_⟩
                    simp only [bhMetaAfterSM, hacc, Bool.not_true, Bool.false_and,
                      Bool.false_eq_true, ↓reduceIte, hgsIn_def]
                    rw [hds_same, he2e_same]
                    exact hR
                  · intro hf rc
                    have hf_cli := hcond.trans hf
                    rcases hr_m : gs_m.inTransit Party.B.other (b0 :: bs) with _ | r_m
                    · rw [hr_m] at hf; simp at hf
                    rcases hr_cli : gsIn.inTransit Party.B.other (wireWhisper :: b0 :: bs) with _ | r_cli
                    · rw [hr_cli] at hf_cli; simp at hf_cli
                    have hw_m : gs_m.win = false := (Bool.or_eq_false_iff.mp hf).1
                    have hw_cli : gsIn.win = false := (Bool.or_eq_false_iff.mp hf_cli).1
                    have hr_m' := hr_m
                    have hr_cli' := hr_cli
                    simp only [SM.GameState.inTransit, Party.other] at hr_m' hr_cli'
                    have hpm := hfind
                    rw [hr_m'] at hpm
                    rw [hgsIn_def] at hr_cli'
                    rw [hr_cli'] at hpm
                    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpm
                    obtain ⟨hpos, -⟩ := hpm
                    have hmem : r_m ∈ gs_m.trans := List.mem_of_find?_eq_some hr_m'
                    have hsat := List.find?_some hr_m'
                    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsat
                    obtain ⟨_, hct⟩ := hsat
                    have hlenm := cliAdapterTrans_m_ct_len h_tr r_m hmem (by rw [hct]; exact hne)
                    rw [hct] at hlenm
                    have hc32 : (wireWhisper :: b0 :: bs).length < 2 ^ 32 := by
                      simp only [List.length_cons] at hlenm ⊢; omega
                    have hcap : (wireWhisper :: b0 :: bs).length ≤ stdinCapBytes := by
                      unfold stdinCapBytes; simp only [List.length_cons] at hlenm ⊢; omega
                    have hwhisp := cliPqRecv_whisper_spec hSpec bi (cliPqSigsOf st_cli bi)
                      d.idA d.idB d.spkCoins (bhInstExtrasB inst) (gs_m.st .B) (qs_rem i)
                      (b0 :: bs) rc
                      (h_actB hacc) hq_pos h_pB (h_epB1 hacc) hidA_bi hremB hc32 hcap
                    dsimp only at hwhisp
                    have hstIn : gsIn.st .B = binStateOfUnderExtras (fun _ => bhInstExtrasB inst) (gs_m.st .B) := hbinB
                    rcases hrm : (sessionSchemeFixedSpk
                        (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                        ℓ d.spkCoins).receive (gs_m.st .B) (b0 :: bs) rc with _ | ⟨g', t', i', m'⟩
                    · have hrb : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                          (gsIn.st .B) (wireWhisper :: b0 :: bs) rc = none := by
                        rw [hstIn, hwhisp.1, hrm]; rfl
                      rw [cliDeliverRPure_reject _ _ _ _ _ _ r_cli hw_cli hr_cli
                            (bhConfigSpkS_must_cli _ _ _ _ _) hrb,
                          cliDeliverRPure_reject _ _ _ _ _ _ r_m hw_m hr_m rfl hrm]
                      refine ⟨rfl, ?_⟩
                      simp only [bhMetaAfterSM, hacc, Bool.not_true, Bool.false_and,
                        Bool.false_eq_true, ↓reduceIte, hgsIn_def]
                      rw [hds_same, he2e_same]
                      exact hR
                    · have hrb : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                          (gsIn.st .B) (wireWhisper :: b0 :: bs) rc =
                          some (binStateOfUnderExtras (fun _ => bhInstExtrasB inst) g', t', i', m') := by
                        rw [hstIn, hwhisp.1, hrm]; rfl
                      obtain ⟨hg'_party, hg'_ep, hg'_ppk, _, hg'_actB⟩ :=
                        hwhisp.2 g' t' i' m' hrm
                      rw [cliDeliverRPure_accept _ _ _ _ _ _ r_cli _ _ _ _ hw_cli hr_cli
                            (bhConfigSpkS_must_cli _ _ _ _ _) hrb,
                          cliDeliverRPure_accept _ _ _ _ _ _ r_m _ _ _ _ hw_m hr_m rfl hrm]
                      refine ⟨by simp only [hgsIn_def, hpos, h_ch, bhPackSmResp], ?_⟩
                      have hib : inst.bobAccepted = true := h_acc ▸ hacc
                      have hrA : gsIn.inTransit Party.A (wireWhisper :: b0 :: bs) = some r_cli := hr_cli
                      simp only [hrA, bhMetaAfterSM, hacc, Bool.not_true, Bool.false_and,
                        Bool.false_eq_true, ↓reduceIte]
                      refine cliAdapterDrvRel_update_inst hRel hi_cli _ _ im im_e2e inst (σ_ad.2.1 i) rfl
                        hinst_ad rfl (fun _ _ => rfl) (fun _ _ => rfl) ?_
                      rw [← hInstRel.im_eq, ← bhAdapterInstMeta_with_bobAccepted_self_cli inst hib]
                      refine cliAdapterInstRel_with_insts
                        (cliAdapterInstRel_of_bob_recv_accept (Nat.sub_le _ _) hInstRel hgs_cli hgs_m
                          hCorr g' hacc hCorr (by exact ⟨rfl, rfl⟩)
                          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                          hg'_party hg'_ppk hg'_ep hg'_actB) _ _
                      · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using hb_eq
                      · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using h_win
                      · simp only [hgsIn_def, SM.GameState.accept, SM.GameState.delete, h_ep, hpos]
                      · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using h_idx
                      · simp only [hgsIn_def, SM.GameState.accept, SM.GameState.delete, h_max, hpos]
                      · simp only [hgsIn_def, SM.GameState.accept, SM.GameState.delete, h_ch, hpos]
                      · simp only [hgsIn_def, SM.GameState.accept, SM.GameState.delete, h_comp, hpos]
                      · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using h_tL
                      · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using h_lk
                      · simpa [hgsIn_def, SM.GameState.accept, SM.GameState.delete] using h_cr
                      · simp only [SM.GameState.accept, SM.GameState.delete]
                        rw [hpos]; exact cliAdapterTrans_filter_pos h_tr r_m.pos
                      · rfl
                      · show Function.update _ _ _ = _
                        simp only [hgsIn_def, bhBinStateOfParty, hg'_party]; rfl
          · have htb : (t == wireWhisper) = false := by simpa using ht
            simp only [htb, Bool.false_eq_true, ↓reduceIte]
            refine cliAdapterStepCoupled_congr_cli (hnoop ?_) (hdummy _ (Or.inr ⟨t :: body, rfl⟩))
            intro inner hp
            have h1 := bhPartneredInnerBytes_wire_cli _ _ _ _ _ hp
            unfold bhWireInnerBytes at h1
            simp [hd, htb] at h1

/-- Bob's deliver (`dl_B`) SM step coupling outside `cliClause2BadKemBool`. -/
theorem cliDrvSM_bob_dl_coupled {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hSpec : CliSpecPqxdh run X W)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliE2ERemoteIdInv σ_e2e)
    (hGood : cliClause2BadKemBool S (modelPrims X W) st_cli ds_cli = false)
    (i : ℕ) (c : Bytes)
    (hq_pos : i < ds_cli.bhInsts.length → 0 < qs_rem i) :
    cliAdapterStepCoupled X W b qStart (fun k => if k = i then qs_rem k - 1 else qs_rem k)
      (((cliDrvSM S ℓ run W qep decT encT ext
          ⟨i, .inl (.inl (.inr (.B, c)))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inr (.B, c)))⟩)).run σ_ad).run σ_e2e) := by
  have hqs_dec : ∀ k, (if k = i then qs_rem k - 1 else qs_rem k) ≤ qs_rem k :=
    fun k => by split_ifs <;> omega
  cases hClean : bhDrvInstClean ds_cli i
  · exact cliDrvSM_early_exit_coupled run X W ki qep decT encT ext hqs_dec hRel i _ (Or.inl hClean)
  · by_cases hi_cli : i < ds_cli.bhInsts.length
    · have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
      cases hNC : (!(ds_cli.instMeta[i]'hi_mb).bobAccepted &&
          bhInstIkACorrupted ds_cli (ds_cli.bhInsts[i]'hi_cli))
      · exact cliDrvSM_bob_dl_active run X W hSpec ki qep decT encT ext hRel hRem hGood i c
          hClean hi_cli hNC (hq_pos hi_cli)
      · exact cliDrvSM_early_exit_coupled run X W ki qep decT encT ext hqs_dec hRel i _
          (Or.inr (Or.inr ⟨hi_cli, hi_mb, by simpa [bhIsBobRecvSMQuery] using hNC⟩))
    · exact cliDrvSM_early_exit_coupled run X W ki qep decT encT ext hqs_dec hRel i _
        (Or.inr (Or.inl (Nat.le_of_not_lt hi_cli)))

set_option linter.unusedSimpArgs false in
private theorem cli_ijB_run_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (st_cli : SignalPqxdh.KeyIndState S) (ds_cli : ModelDriverState S ℓ) (i : ℕ)
    (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S) (gs_cli : SM.GameState BinState (Plain ℓ) Bytes)
    (hClean : bhDrvInstClean ds_cli i = true) (hbi_opt : ds_cli.bhInsts[i]? = some bi)
    (him_opt : ds_cli.instMeta[i]? = some im) (hgs_cli : bi.gs = some gs_cli)
    (hacc : im.bobAccepted = true) (c : Bytes) :
    (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inr (.B, c))⟩).run ds_cli).run st_cli) =
      if (bhPartneredInnerBytes true bi.meA.regId bi.hdr c).isNone ||
          bhPartneredInTransitA true bi.meA.regId bi.hdr c gs_cli then
        pure ((none, ds_cli), st_cli)
      else
        (SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
            (2 + 1) qep (bhConfigSpkS decT encT) (.inl (.inr (.B, c)))).run gs_cli >>= fun x =>
          pure ((x.1, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some x.2 },
                                    instMeta := ds_cli.instMeta.set i im }), st_cli) := by
  dsimp [cliDrvSM, cliStepLocalSM, cliRunStdSM]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hClean, hbi_opt, him_opt, hgs_cli, hacc,
    bhIsBobRecvSMQuery, Bool.not_true, Bool.false_eq_true, Bool.and_false, Bool.false_and,
    ↓reduceIte]
  split_ifs with h
  · simp only [StateT.run_pure]
  · simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      StateT.run_monadLift, monadLift_self, stateT_lift_run_cli, pure_bind, bind_assoc,
      map_eq_bind_pure_comp, Function.comp_def, bhIsBobAcceptSMResp, bhMetaAfterSM, hacc,
      Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      liftM, monadLift, MonadLift.monadLift]

set_option linter.unusedSimpArgs false in
private theorem cli_ijB_run_pre {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (st_cli : SignalPqxdh.KeyIndState S) (ds_cli : ModelDriverState S ℓ) (i : ℕ)
    (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S) (gs_cli : SM.GameState BinState (Plain ℓ) Bytes)
    (hClean : bhDrvInstClean ds_cli i = true) (hbi_opt : ds_cli.bhInsts[i]? = some bi)
    (him_opt : ds_cli.instMeta[i]? = some im) (hgs_cli : bi.gs = some gs_cli)
    (hacc : im.bobAccepted = false) (hNC : bhInstIkACorrupted ds_cli bi = false) (c : Bytes) :
    (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inr (.B, c))⟩).run ds_cli).run st_cli) =
      pure ((none, ds_cli), st_cli) := by
  dsimp [cliDrvSM, cliStepLocalSM]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hClean, hbi_opt, him_opt, hgs_cli, hacc,
    hNC, bhIsBobRecvSMQuery, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.and_false,
    Bool.and_true, Bool.false_and, ↓reduceIte, StateT.run_pure]

set_option linter.unusedSimpArgs false in
private theorem e2e_ijB_run_none_cli {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ_e2e : BHE2EDrvState S ℓ) (i : ℕ) (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (gs_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hClean_e2e : bhE2EDrvInstClean σ_e2e i = true) (hd_opt : σ_e2e.insts[i]? = some d)
    (hime_opt : σ_e2e.instMeta[i]? = some im) (hgs_m : d.gs = some gs_m)
    (hacc : im.bobAccepted = true)
    (c : Bytes) (hdc : bhDecodePreKeyMsgE c = none) :
    bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, c))) =
      (SM.oracleImplR (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ
          d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) (.inl (.inr (.B, c)))).run gs_m >>= fun x =>
        pure ((none, x.1, none), { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 },
                                              instMeta := σ_e2e.instMeta.set i im }) := by
  unfold bhE2EStepLocalSm
  simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, hdc, hacc, bhIsBobRecvSMQuery, Bool.not_true,
    Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_true, ↓reduceIte,
    bhIsBobAcceptSMResp, bhPackSmResp, pure_bind]

set_option linter.unusedSimpArgs false in
private theorem e2e_ijB_run_some_cli {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ_e2e : BHE2EDrvState S ℓ) (i : ℕ) (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (gs_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hClean_e2e : bhE2EDrvInstClean σ_e2e i = true) (hd_opt : σ_e2e.insts[i]? = some d)
    (hime_opt : σ_e2e.instMeta[i]? = some im) (hgs_m : d.gs = some gs_m)
    (hacc : im.bobAccepted = true)
    (c : Bytes) (m : PreKeyMessageFields) (hdc : bhDecodePreKeyMsgE c = some m) :
    bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, c))) =
      if bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
          decide (m.inner.length + 2048 < 2 ^ 32) then
        (SM.oracleImplR (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ
          d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) (.inl (.inr (.B, m.inner)))).run gs_m >>= fun x =>
        pure ((none, x.1, none), { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 },
                                              instMeta := σ_e2e.instMeta.set i im })
      else pure ((none, none, none), σ_e2e) := by
  unfold bhE2EStepLocalSm
  simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, hdc, hacc, bhIsBobRecvSMQuery, Bool.not_true,
    Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_true, ↓reduceIte,
    bhIsBobAcceptSMResp, bhPackSmResp, pure_bind]

set_option linter.unusedSimpArgs false in
private theorem e2e_ijB_run_pre_cli {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ_e2e : BHE2EDrvState S ℓ) (i : ℕ) (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (gs_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hClean_e2e : bhE2EDrvInstClean σ_e2e i = true) (hd_opt : σ_e2e.insts[i]? = some d)
    (hime_opt : σ_e2e.instMeta[i]? = some im) (hgs_m : d.gs = some gs_m)
    (hacc : im.bobAccepted = false) (hNC : bhE2EInstIkACorr σ_e2e d = false) (c : Bytes) :
    bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.B, c))) =
      pure ((none, none, none), σ_e2e) := by
  unfold bhE2EStepLocalSm
  simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, hacc, hNC, bhIsBobRecvSMQuery, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_true, ↓reduceIte]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
open CryptoVerification.E2E.BhAdapterIjHelpersV1 in
private theorem cliDrvSM_bob_ij_active {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hSpec : CliSpecPqxdh run X W)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliE2ERemoteIdInv σ_e2e)
    (i : ℕ) (c : Bytes)
    (hClean : bhDrvInstClean ds_cli i = true)
    (hi_cli : i < ds_cli.bhInsts.length)
    (hNC : (!(ds_cli.instMeta[i]'(hRel.meta_cli_len_eq.symm ▸ hi_cli)).bobAccepted &&
      bhInstIkACorrupted ds_cli ds_cli.bhInsts[i]) = false)
    (hq_pos : 0 < qs_rem i) :
    cliAdapterStepCoupled X W b qStart (fun k => if k = i then qs_rem k - 1 else qs_rem k)
      (((cliDrvSM S ℓ run W qep decT encT ext
          ⟨i, .inl (.inr (.B, c))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inr (.B, c))⟩)).run σ_ad).run σ_e2e) := by
  have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
  have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
  have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
  have hCorr : (ds_cli.instMeta[i]'hi_mb).ikACorrAtAccept = false := by
    exact bhDrvInstClean_imp_ikACorrAtAccept_false hClean hi_cli hi_mb
  obtain ⟨inst, hinst_ad, hInstRel⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
  have hikA_eq :
      bhInstIkACorrupted ds_cli ds_cli.bhInsts[i] = bhE2EInstIkACorr σ_e2e σ_e2e.insts[i] :=
    bhInstIkACorrupted_eq_bhE2EInstIkACorr_of_cliRel hRel hInstRel
  have hNC_e2e :
      (!σ_e2e.instMeta[i].bobAccepted && bhE2EInstIkACorr σ_e2e σ_e2e.insts[i]) = false := by
    rw [← hInstRel.im_eq, ← hikA_eq]; exact hNC
  set bi := ds_cli.bhInsts[i]
  set d := σ_e2e.insts[i]
  set im := ds_cli.instMeta[i]
  set im_e2e := σ_e2e.instMeta[i]
  have hbi_opt : ds_cli.bhInsts[i]? = some bi := List.getElem?_eq_getElem hi_cli
  have hd_opt : σ_e2e.insts[i]? = some d := List.getElem?_eq_getElem hi_e2e
  have him_opt : ds_cli.instMeta[i]? = some im := List.getElem?_eq_getElem hi_mb
  have hime_opt : σ_e2e.instMeta[i]? = some im_e2e := List.getElem?_eq_getElem hi_me
  have hClean_e2e : bhE2EDrvInstClean σ_e2e i = true :=
    (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
  have hacc_e : im_e2e.bobAccepted = im.bobAccepted := by rw [hInstRel.im_eq]
  have hgs := hInstRel.gs_rel
  cases hgs_cli : bi.gs with
  | none => rw [hgs_cli] at hgs; exact False.elim hgs
  | some gs_cli =>
    cases hgs_m : d.gs with
    | none => rw [hgs_cli, hgs_m] at hgs; exact False.elim hgs
    | some gs_m =>
      have hremB : (gs_m.st .B).session.remoteIdentity = some d.idA :=
        (hRem d (List.getElem_mem hi_e2e) gs_m hgs_m).2
      rw [hgs_cli, hgs_m] at hgs
      rcases hgs with ⟨hb_eq, hrest⟩
      simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
      rcases hrest with
        ⟨h_acc, h_win, h_ep, h_idx, h_max, h_ch, h_comp, h_tL, h_lk, h_cr,
         h_tr, _, _, _, _, _, _, _, _, _,
         h_epB1, _, _, h_stB1, _, h_pB, _, h_actB⟩
      have hR := cliAdapterDrvRel_decrement_i i hRel
      have hds_same := bhDrvState_set_same_gs_cli ds_cli i hi_cli hi_mb gs_cli hgs_cli
      have he2e_same := bhE2EDrvState_set_same_gs_cli σ_e2e i hi_e2e hi_me gs_m hgs_m
      cases hacc : im.bobAccepted
      ·
        have hacc_m : im_e2e.bobAccepted = false := hacc_e.trans hacc
        have hikcli : bhInstIkACorrupted ds_cli bi = false := by simpa [hacc] using hNC
        have hik : bhE2EInstIkACorr σ_e2e d = false := by simpa [hacc_m] using hNC_e2e
        have hB : ∀ x, bhE2EStepLocalSm W.C W.Q.K qep decT encT σ_e2e i (.inl (.inr (.B, x))) =
            pure ((none, none, none), σ_e2e) := fun x =>
          e2e_ijB_run_pre_cli W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m hClean_e2e hd_opt
            hime_opt hgs_m hacc_m hik x
        rw [cli_ijB_run_pre run W qep decT encT ext st_cli ds_cli i bi im gs_cli hClean hbi_opt
          him_opt hgs_cli hacc hikcli]
        have had : (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
            (.inr ⟨i, .inl (.inr (.B, c))⟩)).run σ_ad).run σ_e2e) =
            pure (((none : Option (SM.RecvResult (Plain ℓ))), σ_ad), σ_e2e) := by
          rw [cliComposedAdapterImplWith_ij_B_run]
          rcases c with _ | ⟨t, body⟩
          · rcases Option.eq_none_or_eq_some (bhDecodePreKeyMsgE []) with hd | ⟨m, hd⟩
            · simp only [hd, hB, pure_bind]
            · simp only [hd]; split_ifs <;> simp only [hB, pure_bind]
          · cases ht : (t == wireWhisper)
            · simp only [ht, Bool.false_eq_true, ↓reduceIte]
              rcases Option.eq_none_or_eq_some (bhDecodePreKeyMsgE (t :: body)) with hd | ⟨m, hd⟩
              · simp only [hd, hB, pure_bind]
              · simp only [hd]; split_ifs <;> simp only [hB, pure_bind]
            · simp only [ht, ↓reduceIte]
              cases hs : (decide ((t :: body).length ≤ stdinCapBytes) && shortCiphertext (t :: body))
              · simp only [hs, Bool.false_eq_true, ↓reduceIte, hB, pure_bind]
              · simp only [hs, ↓reduceIte]
                rcases Option.eq_none_or_eq_some (bhDecodePreKeyMsgE body) with hd | ⟨m, hd⟩
                · simp only [hd]
                  cases he : body.isEmpty
                  · simp only [he, Bool.false_eq_true, ↓reduceIte, hB, pure_bind]
                  · simp only [he, ↓reduceIte, hB, pure_bind]
                · simp only [hd, hB, pure_bind]
        rw [had]
        exact cliAdapterStepCoupled_ret _ _ _ _ _ hR
      ·
        have hacc_m : im_e2e.bobAccepted = true := hacc_e.trans hacc
        have hib : inst.bobAccepted = true := h_acc ▸ hacc
        have hhdr : bi.hdr = d.hdr := hInstRel.hdr_eq.1
        have hihdr : inst.hdr = d.hdr := hInstRel.hdr_eq.2
        have hidA_bi : d.idA = bhIdKeyOf bi.hdr.ikAPk := by
          rw [hInstRel.idB_eq.2.1, hhdr]
        have hbinB : gs_cli.st .B = binStateOfUnderExtras (fun _ => bhInstExtrasB inst) (gs_m.st .B) := by
          rw [h_stB1 hacc]; simp only [bhBinStateOfParty, h_pB]
        have hsafe : gs_cli.safeInj (2 + 1) = gs_m.safeInj (2 + 1) := by
          simp only [SM.GameState.safeInj, h_tL, h_ep]
        have hspecW : ∀ (body' : Bytes) (rc : BitVec 256),
            (wireWhisper :: body').length < 2 ^ 32 →
            (wireWhisper :: body').length ≤ stdinCapBytes →
            (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                (gs_cli.st .B) (wireWhisper :: body') rc =
              ((sessionSchemeFixedSpk
                (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                ℓ d.spkCoins).receive (gs_m.st .B) body' rc).map
                (fun (g', t, idx, pt) => (binStateOfUnderExtras (fun _ => bhInstExtrasB inst) g', t, idx, pt)) ∧
            (∀ g' t idx pt,
              (sessionSchemeFixedSpk
                (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                ℓ d.spkCoins).receive (gs_m.st .B) body' rc = some (g', t, idx, pt) →
              g'.party = .B ∧
              0 < g'.epoch ∧
              g'.session.pendingPreKey = false ∧
              g'.session.remoteIdentity = some d.idA ∧
              CliPartyActiveInv W (cliPqxdhDirBobAfterAccept bi (cliPqSigsOf st_cli bi))
                (bhInstExtrasB inst) g' (qs_rem i - 1)) := by
          intro body' rc hc32 hcap
          rw [hbinB]
          exact cliPqRecv_whisper_spec hSpec bi (cliPqSigsOf st_cli bi) d.idA d.idB d.spkCoins
            (bhInstExtrasB inst) (gs_m.st .B) (qs_rem i) body' rc
            (h_actB hacc) hq_pos h_pB (h_epB1 hacc) hidA_bi hremB hc32 hcap
        have hspecP : ∀ (c' : Bytes) (m : PreKeyMessageFields) (rc : BitVec 256),
            bhDecodePreKeyMsgE c' = some m →
            bhHdrOfPreKeyMsg m = d.hdr →
            m.inner.length + 2048 < 2 ^ 32 →
            c'.length ≤ stdinCapBytes →
            (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                (gs_cli.st .B) c' rc =
              ((sessionSchemeFixedSpk
                (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                ℓ d.spkCoins).receive (gs_m.st .B) m.inner rc).map
                (fun (g', t, idx, pt) => (binStateOfUnderExtras (fun _ => bhInstExtrasB inst) g', t, idx, pt)) ∧
            (∀ g' t idx pt,
              (sessionSchemeFixedSpk
                (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                ℓ d.spkCoins).receive (gs_m.st .B) m.inner rc = some (g', t, idx, pt) →
              g'.party = .B ∧
              0 < g'.epoch ∧
              g'.session.pendingPreKey = false ∧
              g'.session.remoteIdentity = some d.idA ∧
              CliPartyActiveInv W (cliPqxdhDirBobAfterAccept bi (cliPqSigsOf st_cli bi))
                (bhInstExtrasB inst) g' (qs_rem i - 1)) := by
          intro c' m rc hdc_c hh hlen hcap
          rw [hbinB]
          exact cliPqRecv_prekey_matched_spec hSpec bi (cliPqSigsOf st_cli bi) d.idA d.idB d.spkCoins
            (bhInstExtrasB inst) (gs_m.st .B) (qs_rem i) c' m rc
            (h_actB hacc) hq_pos h_pB (h_epB1 hacc)
            (by rw [hInstRel.extrasB_eq, ← hhdr]; rfl)
            hidA_bi hremB hdc_c (beq_iff_eq.mpr (hh.trans hhdr.symm)) hlen hcap
        have hcli_noop : ∀ c_cli : Bytes, (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK c_cli = false →
            ((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                (2 + 1) qep (bhConfigSpkS decT encT) (.inl (.inr (.B, c_cli)))).run gs_cli >>= fun x =>
              pure ((x.1, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some x.2 },
                                        instMeta := ds_cli.instMeta.set i im }), st_cli)) =
              pure ((none, ds_cli), st_cli) := by
          intro c_cli hinj
          rw [cliOracleImplR_inject_run]
          simp only [hinj, Bool.not_false, Bool.or_true, ↓reduceIte, pure_bind]
          rw [hds_same]
        have hdummy : ∀ c', (c' = [] ∨ ∃ body, c' = wireWhisper :: body) →
            cliAdapterStepCoupled X W b qStart (fun k => if k = i then qs_rem k - 1 else qs_rem k)
              (pure (((none : Option (SM.RecvResult (Plain ℓ))), ds_cli), st_cli))
              (bhE2EStepLocalSm W.C W.Q.K qep decT encT σ_e2e i (.inl (.inr (.B, c'))) >>=
                fun (x : BHE2ESmResp ℓ × BHE2EDrvState S ℓ) =>
                  pure (((none : Option (SM.RecvResult (Plain ℓ))), σ_ad), x.2)) := fun c' hc' =>
          cliAdapterStepCoupled_discard (none : Option (SM.RecvResult (Plain ℓ))) st_cli ds_cli σ_ad σ_e2e _
            (fun (x : BHE2ESmResp ℓ × BHE2EDrvState S ℓ) => x.2)
            (bhE2EStepLocalSm_inject_B_noop_cli W.C W.Q.K qep decT encT σ_e2e i hi_e2e hi_me gs_m
              hgs_m hNC_e2e c' hc') hR
        have hboth_rej : ∀ (c_cli c_m : Bytes),
            ((gs_cli.win || (gs_cli.inTransit Party.B.other c_cli).isSome || !(gs_cli.safeInj (2 + 1)) ||
                !((bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK c_cli)) =
              (gs_m.win || (gs_m.inTransit Party.B.other c_m).isSome || !(gs_m.safeInj (2 + 1)) ||
                !((configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK c_m))) →
            (∀ rc, (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                (gs_cli.st .B) c_cli rc = none) →
            (∀ rc, (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ
                d.spkCoins).receive (gs_m.st .B) c_m rc = none) →
            cliAdapterStepCoupled X W b qStart (fun k => if k = i then qs_rem k - 1 else qs_rem k)
              ((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                  (2 + 1) qep (bhConfigSpkS decT encT) (.inl (.inr (.B, c_cli)))).run gs_cli >>= fun x =>
                pure ((x.1, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some x.2 },
                                          instMeta := ds_cli.instMeta.set i im }), st_cli))
              ((SM.oracleImplR (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ
                  d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) (.inl (.inr (.B, c_m)))).run gs_m >>= fun x =>
                pure ((x.1, σ_ad), { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 },
                                                   instMeta := σ_e2e.instMeta.set i im_e2e })) := by
          intro c_cli c_m hg hrb hrm
          refine cliAdapterStepCoupled_deliver _ _ _ _ gs_cli gs_m
            (fun rc => injectPost (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
              (2 + 1) qep (bhConfigSpkS decT encT) gs_cli .B c_cli rc)
            (fun rc => injectPost (sessionSchemeFixedSpk
              (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ
              d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) gs_m .B c_m rc)
            (cliOracleImplR_inject_run _ _ _ _ _ _ _) (cliOracleImplR_inject_run _ _ _ _ _ _ _) hg
            (fun x => ((x.1, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some x.2 }, instMeta := ds_cli.instMeta.set i im }), st_cli))
            (fun x => ((x.1, σ_ad), { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 }, instMeta := σ_e2e.instMeta.set i im_e2e })) ?_ ?_
          · intro _
            refine ⟨rfl, ?_⟩
            dsimp only
            rw [hds_same, he2e_same]
            exact hR
          · intro _ rc
            dsimp only [injectPost]
            rw [hrb rc, hrm rc]
            refine ⟨rfl, ?_⟩
            dsimp only
            rw [hds_same, he2e_same]
            exact hR
        have hmodel_dead : ∀ c_m : Bytes, (gs_m.inTransit Party.B.other c_m).isSome = true →
            cliAdapterStepCoupled X W b qStart (fun k => if k = i then qs_rem k - 1 else qs_rem k)
              (pure (((none : Option (SM.RecvResult (Plain ℓ))), ds_cli), st_cli))
              ((SM.oracleImplR (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ
                  d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) (.inl (.inr (.B, c_m)))).run gs_m >>= fun x =>
                pure ((x.1, σ_ad), { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 },
                                                   instMeta := σ_e2e.instMeta.set i im_e2e })) := by
          intro c_m hin
          rw [cliOracleImplR_inject_run]
          simp only [hin, Bool.or_true, Bool.true_or, ↓reduceIte, pure_bind]
          rw [he2e_same]
          exact cliAdapterStepCoupled_ret _ _ _ _ _ hR
        have hreal : ∀ (c_cli c_m : Bytes),
            ((gs_cli.win || (gs_cli.inTransit Party.B.other c_cli).isSome || !(gs_cli.safeInj (2 + 1)) ||
                !((bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK c_cli)) =
              (gs_m.win || (gs_m.inTransit Party.B.other c_m).isSome || !(gs_m.safeInj (2 + 1)) ||
                !((configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK c_m))) →
            (∀ rc,
              (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                  (gs_cli.st .B) c_cli rc =
                ((sessionSchemeFixedSpk
                  (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                  ℓ d.spkCoins).receive (gs_m.st .B) c_m rc).map
                  (fun (g', t, idx, pt) => (binStateOfUnderExtras (fun _ => bhInstExtrasB inst) g', t, idx, pt)) ∧
              (∀ g' t idx pt,
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                  ℓ d.spkCoins).receive (gs_m.st .B) c_m rc = some (g', t, idx, pt) →
                g'.party = .B ∧
                0 < g'.epoch ∧
                g'.session.pendingPreKey = false ∧
                g'.session.remoteIdentity = some d.idA ∧
                CliPartyActiveInv W (cliPqxdhDirBobAfterAccept bi (cliPqSigsOf st_cli bi))
                  (bhInstExtrasB inst) g' (qs_rem i - 1))) →
            cliAdapterStepCoupled X W b qStart (fun k => if k = i then qs_rem k - 1 else qs_rem k)
              ((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                  (2 + 1) qep (bhConfigSpkS decT encT) (.inl (.inr (.B, c_cli)))).run gs_cli >>= fun x =>
                pure ((x.1, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some x.2 },
                                          instMeta := ds_cli.instMeta.set i im }), st_cli))
              ((SM.oracleImplR (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ
                  d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) (.inl (.inr (.B, c_m)))).run gs_m >>= fun x =>
                pure ((x.1, σ_ad), { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 },
                                                   instMeta := σ_e2e.instMeta.set i im_e2e })) := by
          intro c_cli c_m hcond hrcv
          refine cliAdapterStepCoupled_deliver _ _ _ _ gs_cli gs_m
            (fun rc => injectPost (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
              (2 + 1) qep (bhConfigSpkS decT encT) gs_cli .B c_cli rc)
            (fun rc => injectPost (sessionSchemeFixedSpk
              (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ d.spkCoins)
              (2 + 1) qep (configRefuseEarlyBobCorr decT encT) gs_m .B c_m rc)
            (cliOracleImplR_inject_run _ _ _ _ _ _ _) (cliOracleImplR_inject_run _ _ _ _ _ _ _) hcond
            (fun x => ((x.1, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some x.2 }, instMeta := ds_cli.instMeta.set i im }), st_cli))
            (fun x => ((x.1, σ_ad), { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 }, instMeta := σ_e2e.instMeta.set i im_e2e })) ?_ ?_
          · intro _
            refine ⟨rfl, ?_⟩
            dsimp only
            rw [hds_same, he2e_same]
            exact hR
          · intro _ rc
            obtain ⟨hrcv_eq, hpost⟩ := hrcv rc
            rcases hrm : (sessionSchemeFixedSpk
                (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ d.spkCoins).receive
                (gs_m.st .B) c_m rc with _ | ⟨g', t', i', m'⟩
            · have hrb : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                  (gs_cli.st .B) c_cli rc = none := by
                rw [hrcv_eq, hrm]; rfl
              dsimp only [injectPost]
              rw [hrb, hrm]
              refine ⟨rfl, ?_⟩
              dsimp only
              rw [hds_same, he2e_same]
              exact hR
            · have hrb : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                  (gs_cli.st .B) c_cli rc =
                  some (binStateOfUnderExtras (fun _ => bhInstExtrasB inst) g', t', i', m') := by
                rw [hrcv_eq, hrm]; rfl
              have hany := cliAdapterTrans_any_pos h_tr (fun p => p == (⟨Party.B.other, t', i'⟩ : SM.Pos))
              have htriv : gs_cli.trivial (2 + 1) ⟨Party.B.other, t', i'⟩ =
                  gs_m.trivial (2 + 1) ⟨Party.B.other, t', i'⟩ := by
                simp only [SM.GameState.trivial, h_comp, h_tL]
                rw [hany]
              have hbase : (bhConfigSpkS (Msg := Plain ℓ) decT encT).base.injectFull t' =
                  (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).base.injectFull t' := rfl
              dsimp only [injectPost]
              rw [hrb, hrm]
              dsimp only
              rw [htriv, hbase]
              by_cases hq : qep + 1 < t'
              · constructor
                · simp only [hq, ↓reduceIte]
                · simp only [hq, ↓reduceIte]
                  rw [hds_same, he2e_same]
                  exact hR
              · by_cases htr : gs_m.trivial (2 + 1) ⟨Party.B.other, t', i'⟩ = true
                · obtain ⟨hg'_party, hg'_ep, hg'_ppk, _, hg'_actB⟩ := hpost g' t' i' m' hrm
                  constructor
                  · simp only [hq, htr, ↓reduceIte]
                  · simp only [hq, htr, ↓reduceIte]
                    refine cliAdapterDrvRel_update_inst hRel hi_cli _ _ im im_e2e inst (σ_ad.2.1 i) rfl
                      hinst_ad rfl (fun _ _ => rfl) (fun _ _ => rfl) ?_
                    rw [← hInstRel.im_eq, ← bhAdapterInstMeta_with_bobAccepted_self_cli inst hib]
                    refine cliAdapterInstRel_with_insts
                      (cliAdapterInstRel_of_bob_recv_accept (Nat.sub_le _ _) hInstRel hgs_cli hgs_m
                        hCorr g' hacc hCorr (by exact ⟨rfl, rfl⟩)
                        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                        hg'_party hg'_ppk hg'_ep hg'_actB) _ _
                    · simpa [SM.GameState.accept, SM.GameState.delete] using hb_eq
                    · simpa [SM.GameState.accept, SM.GameState.delete] using h_win
                    · simp only [SM.GameState.accept, SM.GameState.delete, h_ep]
                    · simpa [SM.GameState.accept, SM.GameState.delete] using h_idx
                    · simp only [SM.GameState.accept, SM.GameState.delete, h_max]
                    · simp only [SM.GameState.accept, SM.GameState.delete, h_ch]
                    · simp only [SM.GameState.accept, SM.GameState.delete, h_comp]
                    · simpa [SM.GameState.accept, SM.GameState.delete] using h_tL
                    · simpa [SM.GameState.accept, SM.GameState.delete] using h_lk
                    · simpa [SM.GameState.accept, SM.GameState.delete] using h_cr
                    · simp only [SM.GameState.accept, SM.GameState.delete]
                      exact cliAdapterTrans_filter_pos h_tr _
                    · rfl
                    · show Function.update _ _ _ = _
                      simp only [bhBinStateOfParty, hg'_party]; rfl
                · by_cases hfull : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).base.injectFull t' = true
                  · constructor
                    · simp only [hq, htr, hfull, Bool.false_eq_true, ↓reduceIte]
                    · simp only [hq, htr, hfull, Bool.false_eq_true, ↓reduceIte]
                      refine cliAdapterDrvRel_update_inst hRel hi_cli _ _ im im_e2e inst (σ_ad.2.1 i) rfl
                        hinst_ad rfl (fun _ _ => rfl) (fun _ _ => rfl) ?_
                      exact cliAdapterInstRel_with_insts
                        (cliAdapterInstRel_set_win
                          (cliAdapterInstRel_mono_q_rem (Nat.sub_le _ _) hInstRel) hgs_cli hgs_m) _ _
                  · constructor
                    · simp only [hq, htr, hfull, Bool.false_eq_true, ↓reduceIte]
                    · simp only [hq, htr, hfull, Bool.false_eq_true, ↓reduceIte]
                      rw [hds_same, he2e_same]
                      exact hR
        have hfindCLI : ∀ (cb inner : Bytes), bhWireInnerBytes cb = some inner →
            gs_cli.trans.any (fun r => r.pos.sender == .A && bhWireInnerBytes r.ct == some inner) = false →
            gs_cli.inTransit Party.B.other cb = none := by
          intro cb inner hw hany
          simp only [SM.GameState.inTransit, Party.other]
          refine list_find?_none_of_any_false_cli _ _ _ (fun r hr => ?_) hany
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr ⊢
          exact ⟨hr.1, by rw [hr.2, hw]⟩
        have hfindM : ∀ (cm : Bytes),
            gs_m.trans.any (fun r => r.pos.sender == .A && decide (r.ct = cm)) = false →
            gs_m.inTransit Party.B.other cm = none := by
          intro cm hany
          simp only [SM.GameState.inTransit, Party.other]
          exact list_find?_none_of_any_false_cli _ _ _ (fun r hr => hr) hany
        have hsomeM : ∀ (cm : Bytes),
            gs_m.trans.any (fun r => r.pos.sender == .A && decide (r.ct = cm)) = true →
            (gs_m.inTransit Party.B.other cm).isSome = true := by
          intro cm hany
          simp only [SM.GameState.inTransit, Party.other]
          rw [List.find?_isSome]
          simpa [List.any_eq_true] using hany
        have hmww : ∀ rest : Bytes, gs_m.inTransit Party.B.other (wireWhisper :: rest) = none := by
          intro rest
          simp only [SM.GameState.inTransit, Party.other]
          exact cliAdapterTrans_find?_m_ww_none h_tr _ _
        rw [cli_ijB_run_eq run W qep decT encT ext st_cli ds_cli i bi im gs_cli hClean hbi_opt
            him_opt hgs_cli hacc,
          cliComposedAdapterImplWith_ij_B_run]
        rcases c with _ | ⟨t, body⟩
        · have hdec : bhDecodePreKeyMsgE ([] : Bytes) = none := by unfold bhDecodePreKeyMsgE; rfl
          have hp : bhPartneredInnerBytes true bi.meA.regId bi.hdr [] = none := by
            unfold bhPartneredInnerBytes; rw [hdec]; rfl
          simp only [hp, hdec, Option.isNone_none, Bool.true_or, List.isEmpty_nil, ↓reduceIte]
          exact hdummy [] (Or.inl rfl)
        · by_cases ht : t = wireWhisper
          · subst ht
            have hdc : bhDecodePreKeyMsgE (wireWhisper :: body) = none :=
              bhDecodePreKeyMsgE_head_ne_cli _ _ (by decide)
            have hw : bhWireInnerBytes (wireWhisper :: body) = some body :=
              bhWireInnerBytes_wireWhisper_cli body
            have hp : bhPartneredInnerBytes true bi.meA.regId bi.hdr (wireWhisper :: body) = some body := by
              unfold bhPartneredInnerBytes; rw [hdc]; simp
            have hpit : bhPartneredInTransitA true bi.meA.regId bi.hdr (wireWhisper :: body) gs_cli =
                gs_cli.trans.any (fun r => r.pos.sender == .A && bhWireInnerBytes r.ct == some body) := by
              unfold bhPartneredInTransitA; rw [hp]
            simp only [hp, hpit, Option.isNone_some, Bool.false_or, beq_self_eq_true, ↓reduceIte]
            by_cases hcs : (decide ((wireWhisper :: body).length ≤ stdinCapBytes) &&
                shortCiphertext (wireWhisper :: body)) = true
            · have hcap : (wireWhisper :: body).length ≤ stdinCapBytes :=
                of_decide_eq_true (Bool.and_eq_true_iff.mp hcs).1
              have hshort : shortCiphertext (wireWhisper :: body) = true :=
                (Bool.and_eq_true_iff.mp hcs).2
              have hc32 : (wireWhisper :: body).length < 2 ^ 32 := of_decide_eq_true hshort
              simp only [hcs, ↓reduceIte]
              rcases hdb : bhDecodePreKeyMsgE body with _ | mb
              · rcases body with _ | ⟨b0, bs⟩
                · have hany0 := cliAdapterTrans_any_A_inner_bad h_tr [] (Or.inl rfl)
                  simp only [hany0, Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil,
                    List.isEmpty_cons]
                  have hdc2 : bhDecodePreKeyMsgE [wireWhisper, wireWhisper] = none :=
                    bhDecodePreKeyMsgE_head_ne_cli _ _ (by decide)
                  rw [e2e_ijB_run_none_cli W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m hClean_e2e
                    hd_opt hime_opt hgs_m hacc_m _ hdc2]
                  simp only [bind_assoc, pure_bind]
                  refine hboth_rej _ _ ?_ ?_ ?_
                  · have hi1 : (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK [wireWhisper] = true := by
                      simp only [bhConfigSpkS, bhInjOK, decide_eq_true hcap, hdc, Bool.true_and]
                      simp [shortCiphertext, ratchetKeyAdmissible]
                    have hi2 : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK
                        [wireWhisper, wireWhisper] = true := by
                      simp [configRefuseEarlyBobCorr, configR1OnCurve, ratchetKeyAdmissible]
                    rw [hfindCLI _ _ hw hany0, hmww, hsafe, h_win, hi1, hi2]
                  · intro rc
                    rw [(hspecW [] rc hc32 hcap).1]
                    simp [sessionSchemeFixedSpk, params_receive_nil]
                  · intro rc
                    simp only [sessionSchemeFixedSpk, params_receive_wireWhisper_cons, Option.map_none]
                · have hne : (b0 :: bs) ≠ [] := List.cons_ne_nil _ _
                  have hanyeq := cliAdapterTrans_any_A_inner_eq h_tr (b0 :: bs) hne
                  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
                  rw [e2e_ijB_run_none_cli W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m hClean_e2e
                    hd_opt hime_opt hgs_m hacc_m _ hdb]
                  simp only [bind_assoc, pure_bind]
                  by_cases hpitv : gs_cli.trans.any
                      (fun r => r.pos.sender == .A && bhWireInnerBytes r.ct == some (b0 :: bs)) = true
                  · simp only [hpitv, ↓reduceIte]
                    exact hmodel_dead _ (hsomeM _ (hanyeq ▸ hpitv))
                  · have hpitf : gs_cli.trans.any
                        (fun r => r.pos.sender == .A && bhWireInnerBytes r.ct == some (b0 :: bs)) = false := by
                      simpa using hpitv
                    simp only [hpitf, Bool.false_eq_true, ↓reduceIte]
                    refine hreal _ _ ?_ (fun rc => hspecW _ rc hc32 hcap)
                    have hinj : (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK (wireWhisper :: b0 :: bs) =
                        (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK (b0 :: bs) := by
                      simp only [bhConfigSpkS, bhInjOK, decide_eq_true hcap, hdc, hshort, Bool.true_and,
                        beq_self_eq_true, configRefuseEarlyBobCorr, configR1OnCurve]
                    rw [hfindCLI _ _ hw hpitf, hfindM _ (hanyeq ▸ hpitf), hsafe, h_win, hinj]
              · rcases body with _ | ⟨b0, bs⟩
                · have hd0 : bhDecodePreKeyMsgE ([] : Bytes) = none := by unfold bhDecodePreKeyMsgE; rfl
                  rw [hd0] at hdb; cases hdb
                by_cases hb0 : b0 = wirePrekey
                swap
                · rw [bhDecodePreKeyMsgE_head_ne_cli _ _ hb0] at hdb; cases hdb
                subst hb0
                have hany0 := cliAdapterTrans_any_A_inner_bad h_tr (wirePrekey :: bs)
                  (Or.inr (by rw [hdb]; rfl))
                simp only [hany0, Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons]
                have hdc2 : bhDecodePreKeyMsgE (wireWhisper :: wirePrekey :: bs) = none :=
                  bhDecodePreKeyMsgE_head_ne_cli _ _ (by decide)
                rw [e2e_ijB_run_none_cli W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m hClean_e2e
                  hd_opt hime_opt hgs_m hacc_m _ hdc2]
                simp only [bind_assoc, pure_bind]
                refine hboth_rej _ _ ?_ ?_ ?_
                · have hi1 : (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK (wireWhisper :: wirePrekey :: bs) = true := by
                    simp only [bhConfigSpkS, bhInjOK, decide_eq_true hcap, hdc, hshort, Bool.true_and,
                      beq_self_eq_true, ratchetKeyOnCurve_wirePrekey_cons]
                  have hi2 : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK
                      (wireWhisper :: wirePrekey :: bs) = true :=
                    ratchetKeyOnCurve_wireWhisper_cons _ _ _ _
                  rw [hfindCLI _ _ hw hany0, hmww, hsafe, h_win, hi1, hi2]
                · intro rc
                  rw [(hspecW _ rc hc32 hcap).1]
                  simp [sessionSchemeFixedSpk, params_receive_wirePrekey_cons]
                · intro rc
                  simp only [sessionSchemeFixedSpk, params_receive_wireWhisper_cons, Option.map_none]
            · have hcsf : (decide ((wireWhisper :: body).length ≤ stdinCapBytes) &&
                  shortCiphertext (wireWhisper :: body)) = false :=
                Bool.eq_false_iff.mpr hcs
              have hinj : (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK (wireWhisper :: body) = false := by
                rw [Bool.eq_false_iff]
                intro h
                apply hcs
                unfold bhConfigSpkS bhInjOK at h
                dsimp only at h
                simp only [Bool.and_eq_true] at h ⊢
                exact h.1
              simp only [hcsf, Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons]
              split_ifs
              · exact hdummy _ (Or.inr ⟨_, rfl⟩)
              · rw [hcli_noop _ hinj]; exact hdummy _ (Or.inr ⟨_, rfl⟩)
          · have htb : (t == wireWhisper) = false := by simpa using ht
            simp only [htb, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
            rcases Option.eq_none_or_eq_some (bhDecodePreKeyMsgE (t :: body)) with hd | ⟨m, hd⟩
            · simp only [hd]
              have hp : bhPartneredInnerBytes true bi.meA.regId bi.hdr (t :: body) = none := by
                unfold bhPartneredInnerBytes; rw [hd]; simp [htb]
              simp only [hp, Option.isNone_none, Bool.true_or, ↓reduceIte]
              exact hdummy _ (Or.inr ⟨_, rfl⟩)
            · simp only [hd]
              by_cases hcs : (decide ((t :: body).length ≤ stdinCapBytes) &&
                  shortCiphertext (t :: body) &&
                  decide (m.inner.length + 2048 < 2 ^ 32)) = true
              · simp only [hcs, ↓reduceIte]
                have hcs12 := (Bool.and_eq_true _ _).mp hcs
                have hcs1 := (Bool.and_eq_true _ _).mp hcs12.1
                have hcap : (t :: body).length ≤ stdinCapBytes := of_decide_eq_true hcs1.1
                have hshort : shortCiphertext (t :: body) = true := hcs1.2
                have hlen : m.inner.length + 2048 < 2 ^ 32 := of_decide_eq_true hcs12.2
                have hw : bhWireInnerBytes (t :: body) = some m.inner := by
                  unfold bhWireInnerBytes; rw [hd]
                simp only [hinst_ad, bhShallowUpdateInstMeta, hd, hib, Bool.not_true,
                  Bool.false_eq_true, ↓reduceIte, hihdr]
                by_cases hh : bhHdrOfPreKeyMsg m = d.hdr
                · have hhb : (bhHdrOfPreKeyMsg m == d.hdr) = true := beq_iff_eq.mpr hh
                  have hhb' : (bhHdrOfPreKeyMsg m == bi.hdr) = true := by rw [hhdr]; exact hhb
                  have hp : bhPartneredInnerBytes true bi.meA.regId bi.hdr (t :: body) = some m.inner := by
                    unfold bhPartneredInnerBytes
                    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, hhb']
                  have hpit : bhPartneredInTransitA true bi.meA.regId bi.hdr (t :: body) gs_cli =
                      gs_cli.trans.any (fun r => r.pos.sender == .A && bhWireInnerBytes r.ct == some m.inner) := by
                    unfold bhPartneredInTransitA; rw [hp]
                  simp only [hp, hpit, Option.isNone_some, Bool.false_or, hhb, Bool.and_true]
                  by_cases hin : m.inner = []
                  · have hany0 := cliAdapterTrans_any_A_inner_bad h_tr [] (Or.inl rfl)
                    have hw0 : bhWireInnerBytes (t :: body) = some [] := by rw [hw, hin]
                    simp only [hany0, Bool.false_eq_true, ↓reduceIte, hin, List.isEmpty_nil,
                      List.isEmpty_cons]
                    have hdc2 : bhDecodePreKeyMsgE (wireWhisper :: t :: body) = none :=
                      bhDecodePreKeyMsgE_head_ne_cli _ _ (by decide)
                    rw [e2e_ijB_run_none_cli W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m hClean_e2e
                      hd_opt hime_opt hgs_m hacc_m _ hdc2]
                    simp only [bind_assoc, pure_bind]
                    refine hboth_rej _ _ ?_ ?_ ?_
                    · have hi1 : (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK (t :: body) = true := by
                        simp only [bhConfigSpkS, bhInjOK, hd, decide_eq_true hcap, hshort, hin, Bool.true_and]
                        simp [ratchetKeyAdmissible]
                      have hi2 : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK
                          (wireWhisper :: t :: body) = true :=
                        ratchetKeyOnCurve_wireWhisper_cons _ _ _ _
                      rw [hfindCLI _ _ hw0 hany0, hmww, hsafe, h_win, hi1, hi2]
                    · intro rc
                      rw [(hspecP (t :: body) m rc hd hh hlen hcap).1]
                      simp [sessionSchemeFixedSpk, hin, params_receive_nil]
                    · intro rc
                      simp only [sessionSchemeFixedSpk, params_receive_wireWhisper_cons, Option.map_none]
                  · have hie : m.inner.isEmpty = false := List.isEmpty_eq_false_iff.mpr hin
                    have hanyeq := cliAdapterTrans_any_A_inner_eq h_tr m.inner hin
                    simp only [hie, Bool.false_eq_true, ↓reduceIte]
                    rw [e2e_ijB_run_some_cli W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m hClean_e2e
                      hd_opt hime_opt hgs_m hacc_m _ m hd]
                    have hsl : (shortCiphertext (t :: body) && decide (m.inner.length + 2048 < 2 ^ 32)) = true :=
                      Bool.and_eq_true_iff.mpr ⟨hshort, decide_eq_true hlen⟩
                    simp only [hhb, Bool.true_and, hsl, ↓reduceIte, bind_assoc, pure_bind]
                    by_cases hpitv : gs_cli.trans.any
                        (fun r => r.pos.sender == .A && bhWireInnerBytes r.ct == some m.inner) = true
                    · simp only [hpitv, ↓reduceIte]
                      exact hmodel_dead _ (hsomeM _ (hanyeq ▸ hpitv))
                    · have hpitf : gs_cli.trans.any
                          (fun r => r.pos.sender == .A && bhWireInnerBytes r.ct == some m.inner) = false := by
                        simpa using hpitv
                      simp only [hpitf, Bool.false_eq_true, ↓reduceIte]
                      refine hreal _ _ ?_ (fun rc => hspecP (t :: body) m rc hd hh hlen hcap)
                      have hinj : (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK (t :: body) =
                          (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK m.inner := by
                        have hlen' : m.inner.length + 2048 < 4294967296 := hlen
                        simp only [bhConfigSpkS, bhInjOK, hd, decide_eq_true hcap, hshort,
                          decide_eq_true hlen, decide_eq_true hlen', Bool.true_and,
                          configRefuseEarlyBobCorr, configR1OnCurve]
                      rw [hfindCLI _ _ hw hpitf, hfindM _ (hanyeq ▸ hpitf), hsafe, h_win, hinj]
                · have hhb : (bhHdrOfPreKeyMsg m == d.hdr) = false := by simpa using hh
                  have hhb' : (bhHdrOfPreKeyMsg m == bi.hdr) = false := by rw [hhdr]; exact hhb
                  have hp : bhPartneredInnerBytes true bi.meA.regId bi.hdr (t :: body) = none := by
                    unfold bhPartneredInnerBytes
                    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, hhb']
                  simp only [hp, Option.isNone_none, Bool.true_or, ↓reduceIte, hhb, Bool.and_false,
                    Bool.false_eq_true]
                  rw [e2e_ijB_run_some_cli W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m hClean_e2e
                    hd_opt hime_opt hgs_m hacc_m _ m hd]
                  simp only [hhb, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pure_bind]
                  exact cliAdapterStepCoupled_ret _ _ _ _ _ hR
              · have hcsf : (decide ((t :: body).length ≤ stdinCapBytes) &&
                    shortCiphertext (t :: body) &&
                    decide (m.inner.length + 2048 < 2 ^ 32)) = false :=
                  Bool.eq_false_iff.mpr hcs
                have hinj : (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK (t :: body) = false := by
                  rw [Bool.eq_false_iff]
                  intro h
                  unfold bhConfigSpkS bhInjOK at h
                  dsimp only at h
                  rw [hd] at h
                  have h12 := (Bool.and_eq_true _ _).mp h
                  have h3 := (Bool.and_eq_true _ _).mp h12.2
                  exact hcs (Bool.and_eq_true_iff.mpr ⟨h12.1, h3.1⟩)
                simp only [hcsf, Bool.false_eq_true, ↓reduceIte]
                split_ifs
                · exact hdummy _ (Or.inr ⟨_, rfl⟩)
                · rw [hcli_noop _ hinj]; exact hdummy _ (Or.inr ⟨_, rfl⟩)

/-- Bob's inject (`ij_B`) SM step coupling. -/
theorem cliDrvSM_bob_ij_coupled {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hSpec : CliSpecPqxdh run X W)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliE2ERemoteIdInv σ_e2e)
    (i : ℕ) (c : Bytes)
    (hq_pos : i < ds_cli.bhInsts.length → 0 < qs_rem i) :
    cliAdapterStepCoupled X W b qStart (fun k => if k = i then qs_rem k - 1 else qs_rem k)
      (((cliDrvSM S ℓ run W qep decT encT ext
          ⟨i, .inl (.inr (.B, c))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inr (.B, c))⟩)).run σ_ad).run σ_e2e) := by
  have hqs_dec : ∀ k, (if k = i then qs_rem k - 1 else qs_rem k) ≤ qs_rem k :=
    fun k => by split_ifs <;> omega
  cases hClean : bhDrvInstClean ds_cli i
  · exact cliDrvSM_early_exit_coupled run X W ki qep decT encT ext hqs_dec hRel i _ (Or.inl hClean)
  · by_cases hi_cli : i < ds_cli.bhInsts.length
    · have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
      cases hNC : (!(ds_cli.instMeta[i]'hi_mb).bobAccepted &&
          bhInstIkACorrupted ds_cli (ds_cli.bhInsts[i]'hi_cli))
      · exact cliDrvSM_bob_ij_active run X W hSpec ki qep decT encT ext hRel hRem i c
          hClean hi_cli hNC (hq_pos hi_cli)
      · exact cliDrvSM_early_exit_coupled run X W ki qep decT encT ext hqs_dec hRel i _
          (Or.inr (Or.inr ⟨hi_cli, hi_mb, by simpa [bhIsBobRecvSMQuery] using hNC⟩))
    · exact cliDrvSM_early_exit_coupled run X W ki qep decT encT ext hqs_dec hRel i _
        (Or.inr (Or.inl (Nat.le_of_not_lt hi_cli)))

end CryptoVerification.E2E


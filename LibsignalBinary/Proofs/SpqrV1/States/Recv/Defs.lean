/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerialize
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefs
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: Definitions, Specifications, and Contracts

**Checked by Lean.** Binary layout predicates (`optEpochSecretAt`, `v1RecvAt`, `resultV1RecvAt`),
decoder strict-sortedness invariants, `.rodata` and callee contract bundles (`StatesRecvContracts`),
and specifications (`statesRecvSpecX`, `statesRecvVariantSpec`) for `<States>::recv` (`0x55454`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `V1Recv` and `Result<V1Recv, spqr::Error>` Representation (`960`B = `0x3c0`) -/

/-- Byte size of `V1Recv` and `Result<V1Recv, spqr::Error>` (`960` bytes = `0x3c0`, align `8`). -/
abbrev v1RecvSize : Nat := 960

/-- Binary layout of `Option<EpochSecret>` at `a` (`32` bytes = `0x20`, align `8`):
    - `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 24` (`Vec<u8>.cap = noneCap` niche at `+0`)
    - `some sec`: `epochSecretAt A a sec` (`vecU8 A a sec.secret ∗ ((a + 24#64) ↦₆₄ sec.epoch)`). -/
def optEpochSecretAt (A : RustAlloc) (a : BitVec 64) : Option EpochSecret → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 24
  | some sec => epochSecretAt A a sec

@[simp]
theorem optEpochSecretAt_none (A : RustAlloc) (a : BitVec 64) :
    optEpochSecretAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 24) := rfl

@[simp]
theorem optEpochSecretAt_some (A : RustAlloc) (a : BitVec 64) (sec : EpochSecret) :
    optEpochSecretAt A a (some sec) = epochSecretAt A a sec := rfl

/-- Binary layout of `spqr::v1::V1Recv` at `a` (`960` bytes = `0x3c0`, align `8`):
    - `+0x000..+0x3a0` (`928`B): `state : States` (`chunkedStatesAt A a v.state`)
    - `+0x3a0..+0x3c0` (`32`B): `key : Option<EpochSecret>` (`optEpochSecretAt A (a + 928#64) v.key`). -/
def v1RecvAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) : SepProp :=
  chunkedStatesAt A a v.state ∗
    optEpochSecretAt A (a + 928#64) v.key

/-- Binary layout of `Result<spqr::v1::V1Recv, spqr::Error>` at `out` (`960` bytes = `0x3c0`, align `8`):
    - `.ok v`: `v1RecvAt A out v` (`960`B, with `States` discriminant `≠ noneCap` at `out + 0`)
    - `.error (.err err)`: `(out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ spqrErrorByte err) ∗ memRegion (out + 9#64) 951`
    - `.error (.panic _)`: `⌜False⌝` (panics take the `onPanic` continuation). -/
def resultV1RecvAt (A : RustAlloc) {F : ShaCompress} (out : BitVec 64) :
    StatesResult (V1Recv spqrPolyApi (spqrAuthApi F)) → SepProp
  | .ok v => v1RecvAt A out v
  | .error (.err err) =>
    (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ spqrErrorByte err) ∗ memRegion (out + 9#64) 951
  | .error (.panic _) => ⌜False⌝

theorem memRegion_out_960_split_states_key (out : BitVec 64) :
    memRegion out v1RecvSize =
      memRegion out chunkedStatesSize ∗ memRegion (out + 928#64) 32 := by
  unfold v1RecvSize chunkedStatesSize
  exact ProofLib.memRegion_split out 928 32 (by decide)

theorem memRegion_out_960_split_err (out : BitVec 64) :
    memRegion out v1RecvSize =
      (∃∗ v0 : BitVec 64, (out ↦₆₄ v0)) ∗
      (∃∗ b8 : BitVec 8, ((out + 8#64) ↦₈ b8)) ∗
      (∃∗ v16 : BitVec 64, ((out + 16#64) ↦₆₄ v16)) ∗
      memRegion (out + 9#64) 7 ∗
      memRegion (out + 24#64) 936 := by
  unfold v1RecvSize
  rw [ProofLib.memRegion_split out 8 952 (by decide),
      ProofLib.memRegion_eight out,
      ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 951)
        (b' := out + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one (out + 8#64),
      ProofLib.memRegion_split' (b := out + 9#64) (n := 7) (k := 944)
        (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 936)
        (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (out + 16#64)]
  ac_rfl

theorem err_epochOutOfRange_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress}
    (out ep : BitVec 64) :
    (out ↦₆₄ noneCap) ∗
      ((out + 8#64) ↦₈ 4#8) ∗
      ((out + 16#64) ↦₆₄ ep) ∗
      memRegion (out + 9#64) 7 ∗
      memRegion (out + 24#64) 936 ⊢
    resultV1RecvAt A (F := F) out (.error (.err (.epochOutOfRange ep))) := by
  dsimp only [resultV1RecvAt, spqrErrorByte]
  have h16 : ((out + 16#64) ↦₆₄ ep) ∗ memRegion (out + 24#64) 936 ⊢
      memRegion (out + 16#64) 944 := by
    rw [ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 936)
      (b' := out + 24#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (out + 16#64) ep)
  have h9 : memRegion (out + 9#64) 7 ∗ memRegion (out + 16#64) 944 ⊢
      memRegion (out + 9#64) 951 := by
    rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 7) (k := 944)
      (b' := out + 16#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine Entails.trans
    (Entails.of_eq (show _ =
      (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 4#8) ∗
      (memRegion (out + 9#64) 7 ∗ (((out + 16#64) ↦₆₄ ep) ∗ memRegion (out + 24#64) 936)) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right
    (Entails.trans (sepConj_mono_right h16) h9))

/-! ## Decoder Strict-Sortedness and Root-Key Preconditions -/

/-- Active `PolyDecoder` strict-sortedness invariant on `States`. -/
def statesDecoderStrictSorted {F : ShaCompress} :
    States spqrPolyApi (spqrAuthApi F) → Prop
  | .headerSent s => PolyDecoderStrictSorted s.receiving_ct1
  | .ekSentCt1Received s => PolyDecoderStrictSorted s.receiving_ct2
  | .noHeaderReceived s => PolyDecoderStrictSorted s.receiving_hdr
  | .ct1Sampled s => PolyDecoderStrictSorted s.receiving_ek
  | .ct1Acknowledged s => PolyDecoderStrictSorted s.receiving_ek
  | _ => True

/-- Precondition invariant required by `<States>::recv` on its input `self : States`:
    active `PolyDecoder`s are strictly sorted, `.ekSentCt1Received s` has
    `s.uc.auth.rootKey.length + 32 < 2 ^ 63`, and `.keysSampled`, `.ct1Sampled`,
    `.ekReceivedCt1Sampled`, `.ct1Acknowledged` satisfy the `from_pb` / `spqrDecodeState`
    field byte-length bounds (`ek.length = 1152`, `es.length = 2080`, `ct1.length = 960`,
    `macKey.length < 2 ^ 32`). -/
def statesRecvPreInv {F : ShaCompress} :
    States spqrPolyApi (spqrAuthApi F) → Prop
  | .keysSampled s => s.uc.ek.length = 1152
  | .headerSent s => PolyDecoderStrictSorted s.receiving_ct1
  | .ekSentCt1Received s =>
      PolyDecoderStrictSorted s.receiving_ct2 ∧
      s.uc.auth.rootKey.length + 32 < 2 ^ 63
  | .noHeaderReceived s => PolyDecoderStrictSorted s.receiving_hdr
  | .ct1Sampled s =>
      PolyDecoderStrictSorted s.receiving_ek ∧
      s.uc.es.length = 2080 ∧ s.uc.ct1.length = 960 ∧ s.uc.auth.macKey.length < 2 ^ 32
  | .ekReceivedCt1Sampled s =>
      s.uc.es.length = 2080 ∧ s.uc.ek.length = 1152 ∧
      s.uc.ct1.length = 960 ∧ s.uc.auth.macKey.length < 2 ^ 32
  | .ct1Acknowledged s =>
      PolyDecoderStrictSorted s.receiving_ek ∧
      s.uc.es.length = 2080 ∧ s.uc.ct1.length = 960 ∧ s.uc.auth.macKey.length < 2 ^ 32
  | _ => True

theorem statesRecvPreInv_implies_strictSorted {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)} (h : statesRecvPreInv st) :
    statesDecoderStrictSorted st := by
  cases st <;> try exact trivial
  · exact h
  · exact h.1
  · exact h
  · exact h.1
  · exact h.1

theorem swapAdjacentPairs_length : ∀ xs : Bytes, (swapAdjacentPairs xs).length = xs.length
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: rest => by
    simp only [swapAdjacentPairs, List.length_cons, swapAdjacentPairs_length rest]

theorem flipEndiannessOfEncapsulationStateBytes_length (es : EncapsulationState) :
    (flipEndiannessOfEncapsulationStateBytes es).length = es.length := by
  simp only [flipEndiannessOfEncapsulationStateBytes, List.length_append,
    swapAdjacentPairs_length, List.length_take, List.length_drop]
  omega

theorem potentiallyFixState_eq_ok_of_len (es : EncapsulationState) (hes : es.length = 2080) :
    ∃ maybeFix,
      potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es = .ok maybeFix ∧
      (maybeFix.getD es).length = 2080 := by
  unfold potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 ENCAPSULATION_STATE_SIZE
  have h1 : (es.length != 2080) = false := by rw [hes]; decide
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  split_ifs with hflip
  · unfold flip_endianness_of_encapsulation_state
    have h2 : (es.length % 2 != 0 || !(es.length > 32)) = false := by rw [hes]; decide
    simp only [h2, Bool.false_eq_true, ↓reduceIte]
    exact ⟨some (flipEndiannessOfEncapsulationStateBytes es), rfl, by
      simp [flipEndiannessOfEncapsulationStateBytes_length, hes]⟩
  · exact ⟨none, rfl, hes⟩

theorem encaps2_eq_ok_of_len (K : MlKem) (ek : EncapsulationKey) (es : EncapsulationState)
    (hes : es.length = 2080) (hek : ek.length = 1152) :
    ∃ ct2, encaps2 K ek es = .ok ct2 ∧ ct2.length = 128 := by
  obtain ⟨maybeFix, hfix, hes'⟩ := potentiallyFixState_eq_ok_of_len es hes
  unfold encaps2
  rw [hfix]
  change ∃ ct2,
    (match (if h : (maybeFix.getD es).length = ENCAPSULATION_STATE_SIZE then
              some (⟨maybeFix.getD es, h⟩ : List.Vector (BitVec 8) ENCAPSULATION_STATE_SIZE) else none),
           (if h : ek.length = ENCAPSULATION_KEY_SIZE then
              some (⟨ek, h⟩ : List.Vector (BitVec 8) ENCAPSULATION_KEY_SIZE) else none) with
     | some esVec, some ekVec => Except.ok (K.encaps2 esVec ekVec).toList
     | _, _ => Except.error (StatesPanic.encaps2BadSize (maybeFix.getD es).length ek.length)) =
      Except.ok ct2 ∧ ct2.length = 128
  have hes_eq : (maybeFix.getD es).length = ENCAPSULATION_STATE_SIZE := hes'
  have hek_eq : ek.length = ENCAPSULATION_KEY_SIZE := hek
  simp only [hes_eq, hek_eq, ↓reduceDIte]
  exact ⟨_, rfl, (K.encaps2 ⟨maybeFix.getD es, hes_eq⟩ ⟨ek, hek_eq⟩).2⟩

theorem send_ct2_and_encoder_eq_ok_of_lengths {F : ShaCompress} (K : MlKem)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (hes : uc_ek.es.length = 2080) (hek : uc_ek.ek.length = 1152)
    (hct1 : uc_ek.ct1.length = 960) (hmac : uc_ek.auth.macKey.length < 2 ^ 32) :
    ∃ uc2 ct2 mac enc2,
      uc_ek.send_ct2 K = .ok (uc2, ct2, mac) ∧
      Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc2 := by
  obtain ⟨ct2, hct2, hct2_len⟩ := encaps2_eq_ok_of_len K uc_ek.ek uc_ek.es hes hek
  have hctLabel : Authenticator.ctLabel.length = 35 := rfl
  have hdata_lt :
      (Authenticator.ctLabel ++ CryptoGames.HMAC.toBEBytes 8 uc_ek.epoch ++ (uc_ek.ct1 ++ ct2)).length < 2 ^ 32 := by
    simp only [List.length_append, hctLabel, toBEBytes_8_length, hct1, hct2_len]
    decide
  have hmac_ok : (spqrAuthApi F).mac_ct uc_ek.auth uc_ek.epoch (uc_ek.ct1 ++ ct2) =
      .ok (Authenticator.macCtUnchecked F uc_ek.auth uc_ek.epoch (uc_ek.ct1 ++ ct2)) :=
    Authenticator.macCt_of_lt F uc_ek.auth uc_ek.epoch (uc_ek.ct1 ++ ct2) hmac hdata_lt
  set mac := Authenticator.macCtUnchecked F uc_ek.auth uc_ek.epoch (uc_ek.ct1 ++ ct2)
  have hmac_len : mac.length = 32 :=
    Authenticator.length_macCtUnchecked F uc_ek.auth uc_ek.epoch (uc_ek.ct1 ++ ct2)
  have hsend : uc_ek.send_ct2 K = .ok ({ epoch := uc_ek.epoch, auth := uc_ek.auth }, ct2, mac) := by
    unfold Unchunked.SendCt.Ct1SentEkReceived.send_ct2
    rw [hct2]
    dsimp only [Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
    rw [hmac_ok]
  let pts := distributeMsgChunksTotal 0 (ct2 ++ mac) (List.replicate NUM_POLYS { value := [] })
  let enc2 : PolyEncoder := { idx := 0#32, s := .points pts }
  have henc2 : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc2 := by
    unfold Chunked.SendCt.send_ct2_encoder expectEncodeBytes spqrPolyApi
    dsimp only [Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
    rw [encodeBytes_eq_ok]
    unfold encodeBytesResult
    have hlen : (ct2 ++ mac).length = 160 := by
      simp only [List.length_append, hct2_len, hmac_len]
    have h1 : ((ct2 ++ mac).length % 2 != 0) = false := by rw [hlen]; decide
    have h2 : ((ct2 ++ mac).length > (1 <<< 16) * NUM_POLYS) = false := by rw [hlen]; decide
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    rfl
  exact ⟨{ epoch := uc_ek.epoch, auth := uc_ek.auth }, ct2, mac, enc2, hsend, henc2⟩

theorem ekReceivedCt1Sampled_recv_ct1_ack_ok_of_preInv {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (hinv : statesRecvPreInv (.ekReceivedCt1Sampled st)) :
    ∃ outSt, st.recv_ct1_ack K st.uc.epoch = .ok outSt := by
  rcases hinv with ⟨hes, hek, hct1, hmac⟩
  obtain ⟨uc2, ct2, mac, enc2, hsend, henc2⟩ :=
    send_ct2_and_encoder_eq_ok_of_lengths K st.uc hes hek hct1 hmac
  refine ⟨{ uc := uc2, sending_ct2 := enc2 }, ?_⟩
  unfold Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hsend]
  dsimp only [Bind.bind, Except.bind]
  rw [henc2]

/-! ## Stack Budget, Read-Only Bundle, and Callee Contracts -/

/-- Own stack frame of `<States>::recv` (`96 + 4096 + 48 = 4240` bytes = `0x1090`). -/
abbrev statesRecvFrame : Nat := 4240

/-- Maximum callee stack budget of `<States>::recv` (`recvCt2ChunkStackX = 3168 + extHookStack`). -/
abbrev statesRecvCalleeStackX : Nat := recvCt2ChunkStackX

/-- Total stack budget of `<States>::recv` (`4240 + recvCt2ChunkStackX = 7408 + extHookStack`). -/
abbrev statesRecvStackX : Nat := statesRecvFrame + statesRecvCalleeStackX

/-- Extended (`+ extHookStack = + 16384`B) callee stack budget of `<States>::recv` (`35936`B). -/
abbrev statesRecvCalleeStackXExt : Nat := statesRecvCalleeStackX + extHookStack

/-- Extended (`+ extHookStack = + 16384`B) total stack budget of `<States>::recv` (`40176`B). -/
abbrev statesRecvStackXExt : Nat := statesRecvFrame + statesRecvCalleeStackXExt

/-- Read-only `.rodata` + `MAX_LOG_LEVEL_FILTER` + `TOKEN` bundle used across `<States>::recv`:
    - `statesRecvJumpTableAt b` (`22`B jump table at `b + 0xa1418`)
    - `unchunkedSendCt2RoAt b` (`(b + 0xaa080#64) ↦₆₄ 0#64` for `logOff` + `(b + 0xa2748#64) ↦ᵣ Authenticator.ctLabel`)
    - `tokenInitAt b` (`(b + 0xaa088#64) ↦₈ 1#8`)
    - `reduceTableAt b` (`(b + 0xa1450#64) ↦ᵣ reduceTableBytes`). -/
def statesRecvRoAt (b : BitVec 64) : SepProp :=
  statesRecvJumpTableAt b ∗
    unchunkedSendCt2RoAt b ∗
    tokenInitAt b ∗
    reduceTableAt b

theorem rodata_statesRecvJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesRecvJumpTableAt img.base ∗ P :=
  rodata_statesRecvJumpTableAt himg hF hP

/-- Bundle of callee `subroutine_ok` contracts used by `<States>::recv` (`0x55454..0x5a0a0`):
    1. `<KeysSampled>::recv_ct1_chunk` (`0x61768`, `keysSampledRecvCt1ChunkSpec`)
    2. `<HeaderSent>::recv_ct1_chunk` (`0x5d8fc`, `headerSentRecvCt1ChunkSpec`)
    3. `<Ct1Received>::recv_ct2_chunk` (`0x5e2f4`, `ct1ReceivedRecvCt2ChunkSpec`)
    4. `<EkSentCt1Received>::recv_ct2_chunk` (`0x5ec2c`, `RecvCt2ChunkOkX`)
    5. `<NoHeaderReceived>::recv_hdr_chunk` (`0x61254`, `NoHeaderReceivedRecvHdrChunkOkX`)
    6. `<PolyDecoder>::add_chunk` (`0x6c420`, `AddChunkOkX` — inlined `Ct1Sampled::recv_ek_chunk`)
    7. `<PolyDecoder as Decoder>::decoded_message` (`0x6bb80`, `polyDecoderDecodedMessageSpec` — inlined `Ct1Sampled::recv_ek_chunk`)
    8. `<Unchunked.SendCt.Ct1Sent>::recv_ek` (`0x5dac0`, `unchunkedCt1SentRecvEkSpec` — inlined `Ct1Sampled::recv_ek_chunk`)
    9. `<Unchunked.SendCt.Ct1SentEkReceived>::send_ct2` (`0x5e400`, `unchunkedCt1SentEkReceivedSendCt2Spec` — inlined `Ct1Sampled::recv_ek_chunk`)
    10. `send_ct2_encoder` (`0x63b28`, `sendCt2EncoderSpec` — inlined `Ct1Sampled::recv_ek_chunk`)
    11. `<EkReceivedCt1Sampled>::recv_ct1_ack` (`0x5e0fc`, `ekReceivedCt1SampledRecvCt1AckSpec`)
    12. `<Ct1Acknowledged>::recv_ek_chunk` (`0x5e9c8`, `ct1AcknowledgedRecvEkChunkSpec`)
    13. `<Ct2Sampled>::recv_next_epoch` (`0x5fa5c`, `ct2SampledRecvNextEpochSpec`).
    (Drop glue `0x4bd18`, `0x4bebc`, `0x4c78c`, `0x4c7d4`, `0x4c858`, `0x4c8bc`, `0x4c92c` are
    already unconditionally proved in `Drop/PolyDecoder.lean`, `Drop/PolyEncoder.lean`, and `Drop/Chunked.lean`.) -/
structure StatesRecvContracts (img : Obj.Image) (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  keysSampledRecvCt1Chunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName)
      (keysSampledRecvCt1ChunkSpec A F)
  headerSentRecvCt1Chunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName)
      (headerSentRecvCt1ChunkSpec A F img.base)
  ct1ReceivedRecvCt2Chunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      (ct1ReceivedRecvCt2ChunkSpec A F)
  ekSentCt1ReceivedRecvCt2Chunk_ok :
    RecvCt2ChunkOkX img K F A ext
  noHeaderReceivedRecvHdrChunk_ok :
    NoHeaderReceivedRecvHdrChunkOkX img F A ext
  polyAddChunk_ok :
    AddChunkOkX img A ext
  polyDecodedMessage_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A img.base)
  unchunkedCt1SentRecvEk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A F K)
  unchunkedCt1SentEkReceivedSendCt2_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base)
  sendCt2Encoder_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      (sendCt2EncoderSpec A)
  ekReceivedCt1SampledRecvCt1Ack_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      (ekReceivedCt1SampledRecvCt1AckSpec A F K img.base)
  ct1AcknowledgedRecvEkChunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName)
      (ct1AcknowledgedRecvEkChunkSpec A F K img.base)
  ct2SampledRecvNextEpoch_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct2SampledRecvNextEpochName)
      (ct2SampledRecvNextEpochSpec A F)

/-- Contract-backed (`*Ext`) callee `subroutine_ok` bundle for `<States>::recv` (`0x55454..0x5a0a0`),
    replacing `RecvCt2ChunkOkX` with `RecvCt2ChunkOkExt`. -/
structure StatesRecvContractsExt (img : Obj.Image) (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  keysSampledRecvCt1Chunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr keysSampledRecvCt1ChunkName)
      (keysSampledRecvCt1ChunkSpec A F)
  headerSentRecvCt1Chunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr headerSentRecvCt1ChunkName)
      (headerSentRecvCt1ChunkSpec A F img.base)
  ct1ReceivedRecvCt2Chunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1ReceivedRecvCt2ChunkName)
      (ct1ReceivedRecvCt2ChunkSpec A F)
  ekSentCt1ReceivedRecvCt2Chunk_ok :
    RecvCt2ChunkOkExt img K F A ext
  noHeaderReceivedRecvHdrChunk_ok :
    NoHeaderReceivedRecvHdrChunkOkX img F A ext
  polyAddChunk_ok :
    AddChunkOkX img A ext
  polyDecodedMessage_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A img.base)
  unchunkedCt1SentRecvEk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A F K)
  unchunkedCt1SentEkReceivedSendCt2_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base)
  sendCt2Encoder_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      (sendCt2EncoderSpec A)
  ekReceivedCt1SampledRecvCt1Ack_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      (ekReceivedCt1SampledRecvCt1AckSpec A F K img.base)
  ct1AcknowledgedRecvEkChunk_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct1AcknowledgedRecvEkChunkName)
      (ct1AcknowledgedRecvEkChunkSpec A F K img.base)
  ct2SampledRecvNextEpoch_ok :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ct2SampledRecvNextEpochName)
      (ct2SampledRecvNextEpochSpec A F)

/-! ## Top-Level and Per-Variant Specifications of `<States>::recv` (`0x55454`) -/

/-- Ghost arguments of `<spqr::v1::chunked::states::States>::recv` (`0x55454`). -/
structure StatesRecvGhost (F : ShaCompress) where
  /-- Sret pointer (`x0`, 960-byte `Result<V1Recv, spqr::Error>` output). -/
  outA : BitVec 64
  /-- Pointer to consumed `self : States` (`x1`, 928 bytes). -/
  selfA : BitVec 64
  /-- Pointer to borrowed `msg : &Message` (`x2`, 48 bytes, preserved). -/
  msgA : BitVec 64
  self : States spqrPolyApi (spqrAuthApi F)
  msg : Message spqrPolyApi

/-- Panic postcondition of `<States>::recv` (`0x55454`):
    either `x.self.recv K x.msg` panics in the pure model, or heap allocation fails (`allocFailedIn`). -/
def statesRecvOnPanic {F : ShaCompress} (K : MlKem) (x : StatesRecvGhost F) (s0 sf : State) : SepProp :=
  ⌜((x.self.recv K x.msg).isPanic = true ∨ allocFailedIn s0 sf) ∧
    s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Specification of `<spqr::v1::chunked::states::States>::recv` (`0x55454..0x5a0a0`, 4,884 insns):
    - Entry registers: `x0 = x.outA` (`960`B `Result<V1Recv, Error>` sret), `x1 = x.selfA` (`928`B `States`
      consumed by value), `x2 = x.msgA` (`48`B `&Message` preserved).
    - Consumes `chunkedStatesAt A x.selfA x.self` (leaving `memRegion x.selfA 928`), preserves
      `messageAt spqrPolyApi x.msgA x.msg`, and writes `resultV1RecvAt A x.outA (x.self.recv K x.msg)` at `x.outA`,
      or panics via `statesRecvOnPanic`. -/
def statesRecvSpec (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64) :
    Spec (StatesRecvGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.msgA ∧
      statesRecvPreInv x.self⌝ ∗
      memRegion x.outA v1RecvSize ∗
      chunkedStatesAt A x.selfA x.self ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoAt b ∗
      A.pool ∗ stackAt s.sp statesRecvStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultV1RecvAt A (F := F) x.outA (x.self.recv K x.msg) ∗
      memRegion x.selfA chunkedStatesSize ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoAt b ∗
      A.pool ∗ stackAt s0.sp statesRecvStackX
  onPanic := fun x s0 sf => statesRecvOnPanic K x s0 sf

/-- Per-variant specification of `0x55454` (`States::recv`) for a fixed `(self, msg)`. -/
def statesRecvVariantSpec (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun ⟨outA, selfA, msgA⟩ s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = outA ∧
      s.readReg64 .x1 = selfA ∧
      s.readReg64 .x2 = msgA ∧
      statesRecvPreInv self⌝ ∗
      memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA self ∗
      messageAt spqrPolyApi msgA msg ∗
      statesRecvRoAt b ∗
      A.pool ∗ stackAt s.sp statesRecvStackX
  post := fun ⟨outA, selfA, msgA⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultV1RecvAt A (F := F) outA (self.recv K msg) ∗
      memRegion selfA chunkedStatesSize ∗
      messageAt spqrPolyApi msgA msg ∗
      statesRecvRoAt b ∗
      A.pool ∗ stackAt s0.sp statesRecvStackX
  onPanic := fun ⟨outA, selfA, msgA⟩ s0 sf =>
    statesRecvOnPanic K ⟨outA, selfA, msgA, self, msg⟩ s0 sf

/-- In-image specification of `<States>::recv` (`0x55454`). -/
def statesRecvSpecX (A : RustAlloc) (F : ShaCompress) (K : MlKem) (img : Obj.Image) :
    Spec (StatesRecvGhost F) :=
  (statesRecvSpec A F K img.base).inImage img

/-- `<States>::recv` (`0x55454`) meets `statesRecvSpec A F K b` on `tripleRatchetProgAtExt b ext`. -/
def StatesRecvOkExt (b : BitVec 64) (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
    (statesRecvSpec A F K b)

/-- `<States>::recv` (`0x55454`) meets `statesRecvSpecX A F K img` on `tripleRatchetProgAtExt img.base ext`. -/
def StatesRecvOkX (img : Obj.Image) (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
    (statesRecvSpecX A F K img)

/-- Extended (`+ extHookStack = + 16384`B) specification of `<spqr::v1::chunked::states::States>::recv` (`0x55454`). -/
def statesRecvSpecExt (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64) :
    Spec (StatesRecvGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.msgA ∧
      statesRecvPreInv x.self⌝ ∗
      memRegion x.outA v1RecvSize ∗
      chunkedStatesAt A x.selfA x.self ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoAt b ∗
      A.pool ∗ stackAt s.sp statesRecvStackXExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultV1RecvAt A (F := F) x.outA (x.self.recv K x.msg) ∗
      memRegion x.selfA chunkedStatesSize ∗
      messageAt spqrPolyApi x.msgA x.msg ∗
      statesRecvRoAt b ∗
      A.pool ∗ stackAt s0.sp statesRecvStackXExt
  onPanic := fun x s0 sf => statesRecvOnPanic K x s0 sf

/-- Extended (`+ extHookStack = + 16384`B) per-variant specification of `0x55454` (`States::recv`). -/
def statesRecvVariantSpecExt (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun ⟨outA, selfA, msgA⟩ s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = outA ∧
      s.readReg64 .x1 = selfA ∧
      s.readReg64 .x2 = msgA ∧
      statesRecvPreInv self⌝ ∗
      memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA self ∗
      messageAt spqrPolyApi msgA msg ∗
      statesRecvRoAt b ∗
      A.pool ∗ stackAt s.sp statesRecvStackXExt
  post := fun ⟨outA, selfA, msgA⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultV1RecvAt A (F := F) outA (self.recv K msg) ∗
      memRegion selfA chunkedStatesSize ∗
      messageAt spqrPolyApi msgA msg ∗
      statesRecvRoAt b ∗
      A.pool ∗ stackAt s0.sp statesRecvStackXExt
  onPanic := fun ⟨outA, selfA, msgA⟩ s0 sf =>
    statesRecvOnPanic K ⟨outA, selfA, msgA, self, msg⟩ s0 sf

/-- Extended (`+ extHookStack = + 16384`B) in-image specification of `<States>::recv` (`0x55454`). -/
def statesRecvSpecXExt (A : RustAlloc) (F : ShaCompress) (K : MlKem) (img : Obj.Image) :
    Spec (StatesRecvGhost F) :=
  (statesRecvSpecExt A F K img.base).inImage img

/-- `<States>::recv` (`0x55454`) meets `statesRecvSpecXExt A F K img` on `tripleRatchetProgAtExt img.base ext`. -/
def StatesRecvOkXExt (img : Obj.Image) (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
    (statesRecvSpecXExt A F K img)

private theorem stackAt_split_grow_recv (sp : BitVec 64) (nX nExt : Nat)
    (hle : nX ≤ nExt := by decide) (hbd : nExt ≤ 131072 := by decide) :
    stackAt sp nExt = memRegion (sp - BitVec.ofNat 64 nExt) (nExt - nX) ∗ stackAt sp nX := by
  have hbd' : nX + (nExt - nX) ≤ 2 ^ 64 := by omega
  have h := ProofLib.stackAt_split_bottom sp nX (nExt - nX) hbd'
  rwa [Nat.add_sub_of_le hle] at h

theorem sub_ok_inImage_grow_stack_recv {α : Type} {prog : Program} {img : Obj.Image}
    {entry : BitVec 64} {specX specExt : Spec α} (nX nExt : Nat)
    (hpre_imp : ∀ x s,
      specExt.pre x s ⊢
        specX.pre x s ∗ memRegion (s.sp - BitVec.ofNat 64 nExt) (nExt - nX))
    (hpost_imp : ∀ x s sf,
      specX.post x s sf ∗ memRegion (s.sp - BitVec.ofNat 64 nExt) (nExt - nX) ⊢
        specExt.post x s sf)
    (hpan_eq : ∀ x s sf, ∃ φ : Prop,
      specX.onPanic x s sf = (⌜φ⌝ ∗ anyHeap) ∧ specExt.onPanic x s sf = (⌜φ⌝ ∗ anyHeap))
    (hexit : ∀ x code s sf, specX.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ x s sf, specX.onOom x s sf = ⌜False⌝)
    (h : subroutine_ok prog entry (specX.inImage img)) :
    subroutine_ok prog entry (specExt.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let Fr := memRegion (s0.sp - BitVec.ofNat 64 nExt) (nExt - nX)
  have hpre' : s0.mem ⊨ (specX.inImage img).pre x s0 ∗ (Fr ∗ R) := by
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ specExt.pre x s0) ∗ R at hpre
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ specX.pre x s0) ∗ (Fr ∗ R)
    refine Satisfies.mono ?_ hpre
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (hpre_imp x s0))) ?_
    exact Entails.of_eq (by dsimp only [Fr]; ac_rfl)
  refine h.mono_outcome x (Fr ∗ R) s0 hpc hrun hpre' hsp ?_
  intro sf hout
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    change sf.mem ⊨ specX.post x s0 sf ∗ (Fr ∗ R) at hpost
    change sf.mem ⊨ specExt.post x s0 sf ∗ R
    refine Satisfies.mono ?_ hpost
    exact Entails.trans (Entails.of_eq (by dsimp only [Fr]; ac_rfl))
      (sepConj_mono_left (hpost_imp x s0 sf))
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    obtain ⟨φ, hpX, hpE⟩ := hpan_eq x s0 sf
    change sf.mem ⊨ specX.onPanic x s0 sf ∗ (Fr ∗ R) at hpost
    change sf.mem ⊨ specExt.onPanic x s0 sf ∗ R
    rw [hpX] at hpost; rw [hpE]
    refine Satisfies.mono ?_ hpost
    exact Entails.trans
      (Entails.of_eq (show (⌜φ⌝ ∗ anyHeap) ∗ (Fr ∗ R) = (⌜φ⌝ ∗ (anyHeap ∗ Fr)) ∗ R by ac_rfl))
      (sepConj_mono_left (sepConj_mono_right (entails_anyHeap (anyHeap ∗ Fr))))
  · change sf.mem ⊨ specX.onExit x code s0 sf ∗ (Fr ∗ R) at hpost
    rw [hexit] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · change sf.mem ⊨ specX.onOom x s0 sf ∗ (Fr ∗ R) at hpost
    rw [hoom] at hpost; exact (not_satisfies_false_sepConj hpost).elim

theorem recvCt2ChunkOkExt_of_okX {img : Obj.Image} {K : MlKem} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : RecvCt2ChunkOkX img K F A ext) :
    RecvCt2ChunkOkExt img K F A ext := by
  refine sub_ok_inImage_grow_stack_recv recvCt2ChunkStackX recvCt2ChunkStackExt ?_ ?_
    (fun _ _ _ => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s; dsimp only [recvCt2ChunkSpecExt, recvCt2ChunkSpec]
    rw [stackAt_split_grow_recv s.sp recvCt2ChunkStackX recvCt2ChunkStackExt]
    exact Entails.of_eq (by ac_rfl)
  · intro x s sf; dsimp only [recvCt2ChunkSpecExt, recvCt2ChunkSpec]
    rw [stackAt_split_grow_recv s.sp recvCt2ChunkStackX recvCt2ChunkStackExt]
    exact Entails.of_eq (by ac_rfl)

theorem StatesRecvContracts.toExt {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)} (h : StatesRecvContracts img A F K ext) :
    StatesRecvContractsExt img A F K ext :=
  { h with ekSentCt1ReceivedRecvCt2Chunk_ok := recvCt2ChunkOkExt_of_okX h.ekSentCt1ReceivedRecvCt2Chunk_ok }

theorem statesRecvVariant_inImage_grow_stack {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {K : MlKem} {ext : String → Option (State → State)}
    {self : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpec A F K img.base self msg).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base self msg).inImage img) := by
  refine sub_ok_inImage_grow_stack_recv statesRecvStackX statesRecvStackXExt ?_ ?_
    (fun _ _ _ => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro ⟨outA, selfA, msgA⟩ s
    dsimp only [statesRecvVariantSpecExt, statesRecvVariantSpec]
    rw [stackAt_split_grow_recv s.sp statesRecvStackX statesRecvStackXExt]
    exact Entails.of_eq (by ac_rfl)
  · intro ⟨outA, selfA, msgA⟩ s sf
    dsimp only [statesRecvVariantSpecExt, statesRecvVariantSpec]
    rw [stackAt_split_grow_recv s.sp statesRecvStackX statesRecvStackXExt]
    exact Entails.of_eq (by ac_rfl)

theorem StatesRecvOkX.toExt {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)} (h : StatesRecvOkX img A F K ext) :
    StatesRecvOkXExt img A F K ext := by
  refine sub_ok_inImage_grow_stack_recv statesRecvStackX statesRecvStackXExt ?_ ?_
    (fun _ _ _ => ⟨_, rfl, rfl⟩) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h
  · intro x s
    dsimp only [statesRecvSpecExt, statesRecvSpec]
    rw [stackAt_split_grow_recv s.sp statesRecvStackX statesRecvStackXExt]
    exact Entails.of_eq (by ac_rfl)
  · intro x s sf
    dsimp only [statesRecvSpecExt, statesRecvSpec]
    rw [stackAt_split_grow_recv s.sp statesRecvStackX statesRecvStackXExt]
    exact Entails.of_eq (by ac_rfl)

/-! ## Stack Frame and Saved-Register Helpers (`4240`B = `0x1090` frame) -/

/-- Saved callee-saved registers at `[s0.sp - 96 .. s0.sp)` (`12` words = `96` bytes):
    `fp, lr, x28, x27, x26, x25, x24, x23, x22, x21, x20, x19`. -/
def statesRecvSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem stackAt_statesRecv_split_96 (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      stackAt (sp - 96#64) (statesRecvCalleeStackX + 4144) ∗ cells (sp - 96#64) 12 :=
  ProofLib.stackAt_split_cells sp (statesRecvCalleeStackX + 4144) 12 (by decide)

theorem stackAt_statesRecv_split_fsp (sp : BitVec 64) :
    stackAt (sp - 96#64) (statesRecvCalleeStackX + 4144) =
      stackAt (sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (sp - 4240#64) 4144 := by
  simp only [stackAt]
  rw [ProofLib.memRegion_split ((sp - 96#64) - BitVec.ofNat 64 (statesRecvCalleeStackX + 4144))
    statesRecvCalleeStackX 4144 (by decide)]
  have h1 : (sp - 96#64) - BitVec.ofNat 64 (statesRecvCalleeStackX + 4144) =
      (sp - 4240#64) - BitVec.ofNat 64 statesRecvCalleeStackX := by
    change (sp - 96#64) - 23696#64 = (sp - 4240#64) - 19552#64
    bv_omega
  have h2 : (sp - 96#64) - BitVec.ofNat 64 (statesRecvCalleeStackX + 4144) +
      BitVec.ofNat 64 statesRecvCalleeStackX = sp - 4240#64 := by
    change (sp - 96#64) - 23696#64 + 19552#64 = sp - 4240#64
    bv_omega
  rw [h2, h1]

theorem memRegion_4144_split_cell48 (fsp : BitVec 64) :
    memRegion fsp 4144 =
      memRegion fsp 48 ∗
      (∃∗ v48 : BitVec 64, ((fsp + 48#64) ↦₆₄ v48)) ∗
      memRegion (fsp + 56#64) 4088 := by
  rw [ProofLib.memRegion_split fsp 48 4096 (by decide),
      ProofLib.memRegion_split' (b := fsp + 48#64) (n := 8) (k := 4088)
        (b' := fsp + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 48#64)]

theorem cell48_4088_entails_memRegion_4144 (fsp v48 : BitVec 64) :
    memRegion fsp 48 ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ⊢
      memRegion fsp 4144 := by
  rw [ProofLib.memRegion_split fsp 48 4096 (by decide),
      ProofLib.memRegion_split' (b := fsp + 48#64) (n := 8) (k := 4088)
        (b' := fsp + 56#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 48#64) v48))

theorem statesRecvSavedCells_entails_cells12 (s0 : State) :
    statesRecvSavedCells s0 ⊢ cells (s0.sp - 96#64) 12 := by
  unfold statesRecvSavedCells
  cells_unfold
  exact Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x27)
          (Entails.sepExists_right (s0.readReg64 .x26)
            (Entails.sepExists_right (s0.readReg64 .x25)
              (Entails.sepExists_right (s0.readReg64 .x24)
                 (Entails.sepExists_right (s0.readReg64 .x23)
                  (Entails.sepExists_right (s0.readReg64 .x22)
                    (Entails.sepExists_right (s0.readReg64 .x21)
                      (Entails.sepExists_right (s0.readReg64 .x20)
                        (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))))))

theorem stack_restore_statesRecv (s0 : State) :
    stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 ⊢
      stackAt s0.sp statesRecvStackX := by
  rw [stackAt_statesRecv_split_96 s0.sp, stackAt_statesRecv_split_fsp s0.sp, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (statesRecvSavedCells_entails_cells12 s0))

theorem stackAt_statesRecv_ext_split_96 (sp : BitVec 64) :
    stackAt sp statesRecvStackXExt =
      stackAt (sp - 96#64) (statesRecvCalleeStackXExt + 4144) ∗ cells (sp - 96#64) 12 :=
  ProofLib.stackAt_split_cells sp (statesRecvCalleeStackXExt + 4144) 12 (by decide)

theorem stackAt_statesRecv_ext_split_fsp (sp : BitVec 64) :
    stackAt (sp - 96#64) (statesRecvCalleeStackXExt + 4144) =
      stackAt (sp - 4240#64) statesRecvCalleeStackXExt ∗ memRegion (sp - 4240#64) 4144 := by
  simp only [stackAt]
  rw [ProofLib.memRegion_split ((sp - 96#64) - BitVec.ofNat 64 (statesRecvCalleeStackXExt + 4144))
    statesRecvCalleeStackXExt 4144 (by decide)]
  have h1 : (sp - 96#64) - BitVec.ofNat 64 (statesRecvCalleeStackXExt + 4144) =
      (sp - 4240#64) - BitVec.ofNat 64 statesRecvCalleeStackXExt := by
    change (sp - 96#64) - 40080#64 = (sp - 4240#64) - 35936#64
    bv_omega
  have h2 : (sp - 96#64) - BitVec.ofNat 64 (statesRecvCalleeStackXExt + 4144) +
      BitVec.ofNat 64 statesRecvCalleeStackXExt = sp - 4240#64 := by
    change (sp - 96#64) - 40080#64 + 35936#64 = sp - 4240#64
    bv_omega
  rw [h2, h1]

theorem stack_restore_statesRecv_ext (s0 : State) :
    stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 ⊢
      stackAt s0.sp statesRecvStackXExt := by
  rw [stackAt_statesRecv_ext_split_96 s0.sp, stackAt_statesRecv_ext_split_fsp s0.sp, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (statesRecvSavedCells_entails_cells12 s0))

theorem stackAt_statesRecvStackXExt_eq_X (sp : BitVec 64) :
    stackAt sp statesRecvStackXExt =
      memRegion (sp - 40176#64) 16384 ∗ stackAt sp statesRecvStackX :=
  ProofLib.stackAt_split_bottom sp statesRecvStackX 16384 (by decide)

theorem stackAt_statesRecvCalleeExt_eq_X (sp : BitVec 64) :
    stackAt (sp - 4240#64) statesRecvCalleeStackXExt =
      memRegion (sp - 40176#64) 16384 ∗ stackAt (sp - 4240#64) statesRecvCalleeStackX := by
  have h := ProofLib.stackAt_split_bottom (sp - 4240#64) statesRecvCalleeStackX 16384 (by decide)
  have hsub : (sp - 4240#64) - BitVec.ofNat 64 (statesRecvCalleeStackX + 16384) = sp - 40176#64 := by
    change (sp - 4240#64) - 35936#64 = sp - 40176#64
    bv_omega
  have hlen : statesRecvCalleeStackX + 16384 = statesRecvCalleeStackXExt := rfl
  rw [hsub, hlen] at h
  exact h

theorem stackAt_statesRecvCalleeExt_eq_recvCt2Ext (sp : BitVec 64) :
    stackAt (sp - 4240#64) statesRecvCalleeStackXExt =
      memRegion (sp - 40176#64) 15664 ∗ stackAt (sp - 4240#64) recvCt2ChunkStackExt := by
  have h := ProofLib.stackAt_split_bottom (sp - 4240#64) recvCt2ChunkStackExt 15664 (by decide)
  have hsub : (sp - 4240#64) - BitVec.ofNat 64 (recvCt2ChunkStackExt + 15664) = sp - 40176#64 := by
    change (sp - 4240#64) - 35936#64 = sp - 40176#64
    bv_omega
  have hlen : recvCt2ChunkStackExt + 15664 = statesRecvCalleeStackXExt := rfl
  rw [hsub, hlen] at h
  exact h

theorem memRegion_statesRecv_15664_720 (sp : BitVec 64) :
    memRegion (sp - 40176#64) 15664 ∗ memRegion ((sp - 4240#64) - 20272#64) 720 =
      memRegion (sp - 40176#64) 16384 := by
  have hsplit := memRegion_split (sp - 40176#64) 15664 720 (by decide)
  have hadd : (sp - 40176#64) + BitVec.ofNat 64 15664 = (sp - 4240#64) - 20272#64 := by bv_omega
  have h16384 : 15664 + 720 = 16384 := rfl
  rw [hadd, h16384] at hsplit
  exact hsplit.symm

def recvCt2ChunkSpecWithStack (stk : Nat) (K : MlKem) (F : ShaCompress) (A : RustAlloc) (b : BitVec 64) :
    Spec (RecvCt2ChunkGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.self.receiving_ct2 ∧
      x.self.uc.auth.rootKey.length + 32 < 2 ^ 63⌝ ∗
      memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗
      stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedRecvChunkResultAt A x.outA (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
      memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗
      stackAt s0.sp stk
  onPanic := fun x s0 sf =>
    ⌜((x.self.recv_ct2_chunk K x.epoch x.chunk).isPanic = true ∨
        allocFailedIn s0 sf) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

@[simp] theorem recvCt2ChunkSpecWithStack_X (K : MlKem) (F : ShaCompress) (A : RustAlloc) (b : BitVec 64) :
    recvCt2ChunkSpecWithStack recvCt2ChunkStackX K F A b = recvCt2ChunkSpec K F A b := rfl

@[simp] theorem recvCt2ChunkSpecWithStack_Ext (K : MlKem) (F : ShaCompress) (A : RustAlloc) (b : BitVec 64) :
    recvCt2ChunkSpecWithStack recvCt2ChunkStackExt K F A b = recvCt2ChunkSpecExt K F A b := rfl

theorem sepWPp_of_statesRecv_exit_ext {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (P R : SepProp)
    (h : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          statesRecvRoAt b ∗
          A.pool ∗ stackAt s0.sp statesRecvStackXExt) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpecExt A F K b self msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpecExt A F K b self msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨hPf, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesRecvVariantSpecExt]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨htrf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by ac_rfl))) hmem_f⟩

@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_16 (sp : BitVec 64) : (sp - 96#64) + 16#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_32 (sp : BitVec 64) : (sp - 96#64) + 32#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_48 (sp : BitVec 64) : (sp - 96#64) + 48#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_64 (sp : BitVec 64) : (sp - 96#64) + 64#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_80 (sp : BitVec 64) : (sp - 96#64) + 80#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_sub_4096 (sp : BitVec 64) : (sp - 96#64) - 4096#64 = sp - 4192#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_4192_sub_48 (sp : BitVec 64) : (sp - 4192#64) - 48#64 = sp - 4240#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_4240_add_48 (sp : BitVec 64) : (sp - 4240#64) + 48#64 = sp - 4192#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_4240_add_4096 (sp : BitVec 64) : (sp - 4240#64) + 4096#64 = sp - 144#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_144_add_48 (sp : BitVec 64) : (sp - 144#64) + 48#64 = sp - 96#64 := by bv_omega

theorem sepWPp_of_statesRecv_exit {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (P R : SepProp)
    (h : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          statesRecvRoAt b ∗
          A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesRecvVariantSpec A F K b self msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesRecvVariantSpec A F K b self msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨hPf, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesRecvVariantSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨htrf, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by ac_rfl))) hmem_f⟩

/-- Combined trace and callee-saved SIMD register preservation from `s0` to `s`. -/
abbrev TraceCalleeSaved (s s0 : State) : Prop :=
  s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

theorem _root_.And.trans {α β : Type _} {a1 a2 a3 : α} {b1 b2 b3 : β}
    (h1 : a1 = a2 ∧ b1 = b2) (h2 : a2 = a3 ∧ b2 = b3) :
    a1 = a3 ∧ b1 = b3 :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

end CryptoVerification.SpqrV1.States.Recv

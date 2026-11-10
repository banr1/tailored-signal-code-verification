/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.TRREF.GrowthRecv.HelpersB
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvB.Defs
import Symbolic.Proofs.Swarm.TRREF.GrowthOoo.State
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers3APure

/-!
# SPQR V1 Receive Growth and OOO Bounds: Version-Greater Branch and V1 Helpers

Proves `≤ st.length + 2^17` byte-length growth and `SpqrOooBounded` preservation for the
`Ordering::Greater` branch of `Top.recv`, `SpqrOooBounded` preservation for the V1 branch, and
polynomial encoder/decoder weight bounds for V1 state decoding.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecvPure

open Symbolic.Swarm.CREF (SpqrOooBounded)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open Symbolic.Swarm.TRREF.SpqrSemOf
open CryptoVerification.SpqrV1.Top.StateSize.SymP3
open Symbolic.Swarm.TRREF.GrowthRecv

/-! ## `Ordering::Greater` Branch -/

/-- State byte-length growth bound (`≤ st.length + 2^17`) for the `Ordering::Greater` branch of
`Top.recv`. -/
theorem spqr_recv_greater_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st : Bytes)
    (prenegotiatedStatePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (chain0 chain1 : Chain)
    (rawKey : Bytes)
    (idx : BitVec 32)
    (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hcf : chainFrom (spqrHkdfWith F) prenegotiatedStatePb.chain prenegotiatedStatePb.versionNegotiation = .ok chain0)
    (hrk : chain0.recvKey (spqrHkdfWith F) 0#64 idx = .ok (chain1, rawKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      chain := some chain1.intoPb
      versionNegotiation := prenegotiatedStatePb.versionNegotiation
      inner := prenegotiatedStatePb.inner
    }).length ≤ st.length + 2^17 := by
  have hd := decodeState_fullWeight_le F K mac st prenegotiatedStatePb hdec
  rcases statePbOooBounded_of_decodeState F K mac st prenegotiatedStatePb hb hdec with ⟨hc_ooo, hvn_ooo⟩
  rcases chainFrom_weight_and_ooo hc_ooo hvn_ooo hcf with ⟨hcf_w, hooo0⟩
  have hrk_w := chain_recvKey_weight_le hooo0 hrk
  change (PqRatchetState.encodeRaw (pbToPqRatchetState {
    chain := some chain1.intoPb
    versionNegotiation := prenegotiatedStatePb.versionNegotiation
    inner := prenegotiatedStatePb.inner
  })).length ≤ st.length + 2^17
  unfold PqRatchetState.encodeRaw pbToPqRatchetState
  simp only [List.length_append]
  have h1 := vnPB_encodeOptMessage_length_le prenegotiatedStatePb.versionNegotiation
  have h2 := chainPB_encodeOptMessage_length_le chain1.intoPb
  cases hinner : prenegotiatedStatePb.inner with
  | none =>
    simp only [hinner, Option.map, optWeight, List.length_nil] at hd ⊢; omega
  | some v =>
    rw [hinner] at hd
    dsimp only [Option.map, PqRatchetState.Inner.encode, optWeight] at hd ⊢
    have hm := encodeMessage_length_le V1State.encodeRaw 3#32 v
    have hv := v1State_encodeRaw_le_fullWeight v; omega

namespace BranchHelpers

theorem chain_recvKey_params_eq {hkdf : HkdfFn} {c1 c2 : Chain} {ep : Epoch} {idx : BitVec 32} {out : Bytes}
    (h : c1.recvKey hkdf ep idx = .ok (c2, out)) :
    c2.params = c1.params := by
  unfold Chain.recvKey at h; split at h
  · injection h with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩; rfl
  · rcases except_bind_eq_ok h with ⟨epochIndex, _, h⟩; dsimp only at h
    cases hget : c1.links[epochIndex]? with
    | none => simp [hget] at h
    | some link =>
      rw [hget] at h; dsimp only [Bind.bind, Except.bind] at h
      rcases except_bind_eq_ok h with ⟨⟨recv', out'⟩, _, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩; rfl

end BranchHelpers
open BranchHelpers

/-- `SpqrOooBounded` preservation for the `Ordering::Greater` branch of `Top.recv`. -/
theorem spqr_recv_greater_oooBounded
    (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st : Bytes)
    (prenegotiatedStatePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (chain0 chain1 : Chain)
    (rawKey : Bytes)
    (idx : BitVec 32)
    (hb : SpqrOooBounded st)
    (hlen : st.length < 2 ^ 32)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hcf : chainFrom (spqrHkdfWith F) prenegotiatedStatePb.chain prenegotiatedStatePb.versionNegotiation = .ok chain0)
    (hrk : chain0.recvKey (spqrHkdfWith F) 0#64 idx = .ok (chain1, rawKey)) :
    SpqrOooBounded
      ((spqrDepsWithMac F K mac).encodeState {
        chain := some chain1.intoPb
        versionNegotiation := prenegotiatedStatePb.versionNegotiation
        inner := prenegotiatedStatePb.inner
      }) := by
  have hle := spqr_recv_greater_length_le F K mac st prenegotiatedStatePb chain0 chain1 rawKey idx hb hdec hcf hrk
  have hout_len : ((spqrDepsWithMac F K mac).encodeState {
    chain := some chain1.intoPb
    versionNegotiation := prenegotiatedStatePb.versionNegotiation
    inner := prenegotiatedStatePb.inner
  }).length < 2 ^ 64 := by omega
  rcases statePbOooBounded_of_decodeState F K mac st prenegotiatedStatePb hb hdec with ⟨hc_ooo, hvn_ooo⟩
  rcases chainFrom_weight_and_ooo hc_ooo hvn_ooo hcf with ⟨_, hooo0⟩
  refine GrowthOoo.ooo_of_decodeState (m := pbToPqRatchetState {
    chain := some chain1.intoPb
    versionNegotiation := prenegotiatedStatePb.versionNegotiation
    inner := prenegotiatedStatePb.inner
  }) hout_len (fun ch hch p hp => ?_) hvn_ooo
  cases hch; cases hp
  rw [chain_recvKey_params_eq hrk]
  exact hooo0

/-! ## V1 Branch `SpqrOooBounded` Preservation -/

namespace BranchHelpers

theorem recvAddEpochOpt_weight_and_ooo {hkdf : HkdfFn} {c0 c1 : Chain} {key : Option EpochSecret}
    (hooo : c0.params.maxOooKeysOrDefault.toNat ≤ 2000)
    (hadd : recvAddEpochOpt hkdf c0 key = .ok c1) :
    chainWeight c1.intoPb ≤ chainWeight c0.intoPb + 206 ∧
      c1.params.maxOooKeysOrDefault.toNat ≤ 2000 := by
  unfold recvAddEpochOpt at hadd
  cases key with
  | none => injection hadd with hc; subst hc; exact ⟨by omega, hooo⟩
  | some es =>
    dsimp only [SpqrApiResult.ofChainPanic] at hadd
    cases hae : c0.addEpoch hkdf es with
    | error _ => simp [hae] at hadd
    | ok c' =>
      rw [hae] at hadd; injection hadd with hc; subst hc
      have hw := chain_addEpoch_weight_le hae
      unfold Chain.addEpoch at hae
      split at hae; · contradiction
      · split at hae; · contradiction
        · injection hae with hc'; subst hc'; exact ⟨hw, hooo⟩

theorem v1_recv_chain2_ooo
    {F : ShaCompress} {K : MlKem} {mac : HmacFn} {st : Bytes}
    {prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB}
    {key : Option EpochSecret}
    {chain0 chain1 chain2 : Chain} {msgKeyEpoch : Epoch} {idx : BitVec 32} {msgKey : Bytes}
    (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    chain2.params.maxOooKeysOrDefault.toNat ≤ 2000 := by
  rcases statePbOooBounded_of_decodeState F K mac st prenegotiatedStatePb hb hdec with ⟨hc_ooo, hvn_ooo⟩
  have hpre_ooo : StatePbOooBounded statePb := by
    cases hpre with
    | equal => exact ⟨hc_ooo, hvn_ooo⟩
    | less vn v dir inner' chain' hvn _ _ hcf_less =>
      have hvn_ooo' : ∀ v0 ∈ (some vn : Option VersionNegotiationPB), ∀ p ∈ v0.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000 := by
        intro v0 hv0; rw [← hvn] at hv0; exact hvn_ooo v0 hv0
      rcases chainFrom_weight_and_ooo hc_ooo hvn_ooo' hcf_less with ⟨_, hooo'⟩
      refine ⟨?_, by intro v0 hv0; cases hv0⟩
      intro ch hch p hp
      simp only [Option.mem_def, Option.some.injEq] at hch; subst hch
      simp only [Chain.intoPb, Option.mem_def, Option.some.injEq] at hp; subst hp
      exact hooo'
  rcases hpre_ooo with ⟨hc_ooo1, hvn_ooo1⟩
  rcases chainFrom_weight_and_ooo hc_ooo1 hvn_ooo1 hcf with ⟨_, hooo0⟩
  rcases recvAddEpochOpt_weight_and_ooo hooo0 hadd with ⟨_, hooo1⟩
  rw [chain_recvKey_params_eq hrk]
  exact hooo1

end BranchHelpers
open BranchHelpers

/-- `SpqrOooBounded` preservation for the V1 branch of `Top.recv`. -/
theorem spqr_recv_v1_oooBounded
    (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (st1 : (spqrDepsWithMac F K mac).States)
    (key : Option EpochSecret)
    (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch)
    (idx : BitVec 32)
    (msgKey : Bytes)
    (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey))
    (hout_len : ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length < 2 ^ 64) :
    SpqrOooBounded
      ((spqrDepsWithMac F K mac).encodeState {
        inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
        versionNegotiation := none
        chain := some chain2.intoPb
      }) := by
  have hc2 := v1_recv_chain2_ooo hb hdec hpre hcf hadd hrk
  refine GrowthOoo.ooo_of_decodeState (m := pbToPqRatchetState {
    inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
    versionNegotiation := none
    chain := some chain2.intoPb
  }) hout_len (fun ch hch p hp => ?_) (fun v hv => by cases hv)
  cases hch; cases hp
  exact hc2

/-! ## Polynomial Codec and `SendCt` Encoding Weight Bounds -/

namespace BranchHelpers

@[scoped simp] theorem pure_bind_except {ε α β : Type} (x : α) (k : α → Except ε β) :
    (pure x >>= k) = k x := rfl

@[scoped simp] theorem ok_bind_except {ε α β : Type} (x : α) (k : α → Except ε β) :
    (Except.ok x >>= k) = k x := rfl

@[scoped simp] theorem except_mapError_eq_ok_iff {ε ε' α : Type} {f : ε → ε'} {e : Except ε α} {x : α} :
    e.mapError f = .ok x ↔ e = .ok x := by
  cases e <;> simp [Except.mapError]

@[scoped simp] theorem liftSpqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    liftSpqrPanic r = .ok v ↔ r = .ok v := by
  cases r <;> simp [liftSpqrPanic]

@[scoped simp] theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε]
    {r : Except ε α} {v : α} : StatesResult.ofPanic r = .ok v ↔ r = .ok v := by
  cases r <;> simp [StatesResult.ofPanic]

theorem poly_addChunk_ofPanic_eq_ok {dec dec' : PolyDecoder} {chunk : Chunk}
    (h : StatesResult.ofPanic (spqrPolyApi.add_chunk dec chunk) = .ok dec') :
    PolyDecoder.addChunk dec chunk = .ok dec' := by
  unfold spqrPolyApi at h; dsimp only [] at h
  exact except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h)

theorem statesFromPb_eq_ok {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApiWithMac F mac)}
    (h : (spqrDepsWithMac F K mac).statesFromPb pb = .ok st0) :
    States.from_pb spqrPolyApi (spqrAuthApiWithMac F mac) pb = .ok st0 := by
  unfold spqrDepsWithMac liftStatesResult at h; dsimp only [] at h
  cases hs : States.from_pb spqrPolyApi (spqrAuthApiWithMac F mac) pb with
  | error e => rw [hs] at h; cases e <;> contradiction
  | ok s => rw [hs] at h; injection h with h; subst h; rfl

def bytesSum (xs : List Bytes) : Nat := (xs.map List.length).sum

theorem bytesSum_le_encodeRepeatedBytes (tag : BitVec 32) :
    ∀ (xs : List Bytes), bytesSum xs ≤ (Proto.encodeRepeatedBytes tag xs).length
  | [] => by simp [bytesSum]
  | x :: xs => by
    simp only [bytesSum, List.map_cons, List.sum_cons, encodeRepeatedBytes_cons, List.length_append]
    have hx : x.length ≤ (Proto.encodeBytesUncond tag x).length := by
      unfold Proto.encodeBytesUncond; simp only [List.length_append]; omega
    have ih := bytesSum_le_encodeRepeatedBytes tag xs
    simp only [bytesSum] at ih; omega

theorem sum_map_add_const (xs : List Bytes) (c : Nat) :
    (xs.map (fun b => b.length + c)).sum = bytesSum xs + c * xs.length := by
  induction xs with
  | nil => simp [bytesSum]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, bytesSum, List.length_cons, Nat.mul_succ, ih]; omega

theorem polyEncoder_fromPb_raw_le_fullW {pb : PolynomialEncoder} {enc : PolyEncoder}
    (h : PolyEncoder.fromPb (pbToProtoPolyEncoder pb) = .ok (.ok enc)) :
    rawPolyEnc pb ≤ encFullW pb + 352 := by
  have hpts_le := bytesSum_le_encodeRepeatedBytes 2#32 pb.pts
  have hpol_le := bytesSum_le_encodeRepeatedBytes 3#32 pb.polys
  unfold PolyEncoder.fromPb at h; split at h
  · split at h
    · simp [pure, Except.pure] at h
    · split at h
      · simp [pure, Except.pure] at h
      · rename_i h1 h2 h3
        have hpts : pb.pts.length = 16 := by simpa [pbToProtoPolyEncoder, NUM_POLYS, CHUNK_SIZE, bne_iff_ne] using h3
        have hpolys : pb.polys.length = 0 := by
          cases hpol : pb.polys with
          | nil => rfl
          | cons _ _ => simp [pbToProtoPolyEncoder, hpol] at h2
        simp only [rawPolyEnc, encFullW, sum_map_add_const, hpts, hpolys]; omega
  · split at h
    · rename_i h1 h2
      have hpts : pb.pts.length = 0 := by
        cases hpt : pb.pts with
        | nil => rfl
        | cons _ _ => simp [pbToProtoPolyEncoder, hpt] at h1
      have hpolys : pb.polys.length = 16 := by simpa [pbToProtoPolyEncoder, NUM_POLYS, CHUNK_SIZE, beq_iff_eq] using h2
      simp only [rawPolyEnc, encFullW, sum_map_add_const, hpts, hpolys]; omega
    · simp [pure, Except.pure] at h

theorem encoderFromPbStateDecode_raw_le_fullW {pb? : Option PolynomialEncoder} {enc : PolyEncoder}
    (h : encoderFromPbStateDecode spqrPolyApi pb? = .ok enc) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ optWeight encFullW pb? + 352 := by
  have hraw := encoderFromPbStateDecode_raw_le h
  unfold encoderFromPbStateDecode spqrPolyApi at h
  cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' := except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h1)
    cases res with
    | error _ => contradiction
    | ok enc' =>
      have hinj := Except.ok.inj h2; subst hinj
      have hpb := polyEncoder_fromPb_raw_le_fullW h1'
      simp only [optRaw_some, optWeight] at hraw ⊢; omega

theorem polyDecoder_fromPb_raw_le_fullW {pb : PolynomialDecoder} {dec : PolyDecoder}
    (h : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) = .ok (.ok dec)) :
    rawPolyDec pb ≤ decFullW pb + 352 := by
  have hpts_le := bytesSum_le_encodeRepeatedBytes 3#32 pb.pts
  unfold PolyDecoder.fromPb at h; split at h
  · simp [pure, Except.pure] at h
  · rename_i h1
    have hpts : pb.pts.length = 16 := by simpa [pbToProtoPolyDecoder, NUM_POLYS, CHUNK_SIZE, bne_iff_ne] using h1
    simp only [rawPolyDec, decFullW, sum_map_add_const, hpts]; omega

theorem decoderFromPbStateDecode_raw_le_fullW {pb? : Option PolynomialDecoder} {dec : PolyDecoder}
    (h : decoderFromPbStateDecode spqrPolyApi pb? = .ok dec) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ optWeight decFullW pb? + 352 := by
  have hraw := (decoderFromPbStateDecode_raw_le h).1
  unfold decoderFromPbStateDecode spqrPolyApi at h
  cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' := except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h1)
    cases res with
    | error _ => contradiction
    | ok dec' =>
      have hinj := Except.ok.inj h2; subst hinj
      have hpb := polyDecoder_fromPb_raw_le_fullW h1'
      simp only [optRaw_some, optWeight] at hraw ⊢; omega

theorem flatMap_u16ToBeBytes_length (l : List GF16) :
    (l.flatMap (fun g => u16ToBeBytes g.value)).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]
    have : (u16ToBeBytes g.value).length = 2 := rfl; omega

def pointRaw' (pt : Point) : Nat := 2 * pt.value.length + 22

theorem map_intoPb_encoder_pts' (pts : List Point) :
    ((pts.map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))).map (fun b => b.length + 22)) =
    pts.map pointRaw' := by
  induction pts with
  | nil => rfl
  | cons pt ps ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]; simp only [pointRaw', flatMap_u16ToBeBytes_length]

theorem sum_map_set_le' {α : Type} (f : α → Nat) (xs : List α) (idx : Nat) (x x' : α) (c : Nat)
    (hget : xs[idx]? = some x) (hle : f x' ≤ f x + c) :
    ((xs.set idx x').map f).sum ≤ (xs.map f).sum + c := by
  induction xs generalizing idx with
  | nil => simp at hget
  | cons a rest ih =>
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget; subst hget
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]; omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      have hih := ih i hget
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]; omega

theorem distributeMsgChunks_sum_le' (i : Nat) (msg : List (BitVec 8)) (pts : List Point)
    {pts' : List Point} (h : PolyEncoder.distributeMsgChunks i msg pts = .ok pts') :
    (pts'.map pointRaw').sum ≤ (pts.map pointRaw').sum + msg.length := by
  suffices ∀ n i (msg : List (BitVec 8)) (pts : List Point), msg.length ≤ n →
      PolyEncoder.distributeMsgChunks i msg pts = .ok pts' →
      (pts'.map pointRaw').sum ≤ (pts.map pointRaw').sum + msg.length from
    this msg.length i msg pts (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro i msg pts hn h; cases msg with
    | nil => unfold PolyEncoder.distributeMsgChunks at h; simp only [Except.ok.injEq] at h; subst h; omega
    | cons _ _ => simp at hn
  | succ n ih =>
    intro i msg pts hn h
    rcases msg with _ | ⟨c0, _ | ⟨c1, rest⟩⟩
    · unfold PolyEncoder.distributeMsgChunks at h; simp only [Except.ok.injEq] at h; subst h; omega
    · unfold PolyEncoder.distributeMsgChunks at h; contradiction
    · unfold PolyEncoder.distributeMsgChunks at h; dsimp only [] at h; split at h
      · rename_i pt hpt
        have hih := ih (i + 1) rest _ (by simp only [List.length_cons] at hn; omega) h
        have hset := sum_map_set_le' pointRaw' pts (i % pts.length) pt
          { value := pt.value ++ [GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)] } 2 hpt
          (by simp only [pointRaw', List.length_append, List.length_singleton]; omega)
        simp only [List.length_cons]; omega
      · contradiction

theorem polyEncoder_encodeBytes_raw_le_msg {msg : List (BitVec 8)} {enc : PolyEncoder}
    (h : PolyEncoder.encodeBytes msg = .ok (.ok enc)) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ msg.length + 352 := by
  unfold PolyEncoder.encodeBytes PolyEncoder.encodeBytesBase at h; split at h
  · simp [pure, Except.pure] at h
  · split at h
    · simp [pure, Except.pure] at h
    · rcases hpts : PolyEncoder.distributeMsgChunks 0 msg (List.replicate NUM_POLYS { value := [] }) with e | pts
      · simp [hpts, Bind.bind, Except.bind] at h
      · simp only [hpts, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; subst h
        have hsum := distributeMsgChunks_sum_le' 0 msg (List.replicate NUM_POLYS { value := [] }) hpts
        have hinit : ((List.replicate NUM_POLYS ({ value := [] } : Point)).map pointRaw').sum = 352 := rfl
        simp only [PolyEncoder.intoPb, protoPolyEncoderToPb, rawPolyEnc,
          map_intoPb_encoder_pts', List.map_nil, List.sum_nil]; omega

theorem expectEncodeBytes_raw_le_msg {site : String} {msg : Bytes} {enc : PolyEncoder}
    (h : expectEncodeBytes spqrPolyApi site msg = .ok enc) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ msg.length + 352 := by
  unfold expectEncodeBytes spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
  have h1' := except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h1); cases res with
  | error _ => contradiction
  | ok enc' => have hinj := Except.ok.inj h2; subst hinj; exact polyEncoder_encodeBytes_raw_le_msg h1'

theorem encaps2_length {K : MlKem} {ek es ct2 : Bytes}
    (h : encaps2 K ek es = .ok ct2) : ct2.length = 128 := by
  unfold encaps2 at h
  rcases except_bind_eq_ok h with ⟨maybeFix, _, h⟩; dsimp only [] at h
  split at h <;> try contradiction
  injection h with h; subst h; exact List.Vector.toList_length _

theorem macCtWithMac_length_le {mac : HmacFn} {self : Authenticator} {ep : Epoch} {ct macBytes : Bytes}
    (h : macCtWithMac mac self ep ct = .ok macBytes) : macBytes.length ≤ 32 := by
  unfold macCtWithMac at h; dsimp only [] at h; split at h
  · cases hmac : mac self.macKey (Authenticator.ctLabel ++ CryptoGames.HMAC.toBEBytes 8 ep ++ ct) with
    | none => rw [hmac] at h; contradiction
    | some tag =>
      rw [hmac] at h; dsimp only [] at h; split at h
      · injection h with h; subst h; exact List.length_take_le 32 tag
      · contradiction
  · contradiction

theorem send_ct2_encode_raw_le {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {uc : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApiWithMac F mac)}
    {uc2 : Unchunked.SendCt.Ct2Sent (spqrAuthApiWithMac F mac)}
    {ct2 macB : Bytes} {sendingCt2 : PolyEncoder}
    (hct2 : uc.send_ct2 K = .ok (uc2, ct2, macB))
    (henc2 : expectEncodeBytes spqrPolyApi "v1/chunked/send_ct.rs:162" (ct2 ++ macB) = .ok sendingCt2) :
    uc2 = { epoch := uc.epoch, auth := uc.auth } ∧
      rawPolyEnc (protoPolyEncoderToPb sendingCt2.intoPb) ≤ 512 := by
  unfold Unchunked.SendCt.Ct1SentEkReceived.send_ct2 at hct2; dsimp only [] at hct2
  rcases except_bind_eq_ok hct2 with ⟨ct2', hcap, hct2b⟩
  rcases except_bind_eq_ok hct2b with ⟨mac', hmac, hct2c⟩
  have hinj := Except.ok.inj hct2c
  have huc2 : uc2 = { epoch := uc.epoch, auth := uc.auth } := (Prod.mk.inj hinj).1.symm
  have hct2_eq : ct2 = ct2' := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
  have hmac_eq : macB = mac' := (Prod.mk.inj (Prod.mk.inj hinj).2).2.symm
  subst huc2 hct2_eq hmac_eq
  have hlen1 := encaps2_length hcap
  have hlen2 : macB.length ≤ 32 := macCtWithMac_length_le (liftSpqrPanic_eq_ok.mp hmac)
  have henc := expectEncodeBytes_raw_le_msg henc2
  rw [List.length_append] at henc; exact ⟨rfl, by omega⟩

end BranchHelpers
open BranchHelpers

end Symbolic.Swarm.TRREF.GrowthRecvPure

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: V1 Ratchet `Ok` Tail (`+2664..+2916 -> +876 -> +1040`)

**Checked by Lean.** Symbolic execution of `<States>::into_pb`, `<Chain>::into_pb`,
`PqRatchetState::encode_to_vec`, result writing, and `PqRatchetState` / `versionNegotiation` drop
cleanup on the V1 ratchet `Ok` tail of `spqr::recv` (`0x5462c`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

/-! ## 1. Pure Model & Encoded State Length Lemmas for V1 Ratchet `Ok` -/

theorem spqrDeps_statesIntoPb_eq (F : ShaCompress) (K : MlKem)
    (st1 : States spqrPolyApi (spqrAuthApi F)) :
    (spqrDeps F K).statesIntoPb st1 = st1.into_pb := rfl

theorem spqrV1Recv_v1_ratchet_of_ok {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {st1 : States spqrPolyApi (spqrAuthApi F)} {chain2 : Chain} {rawKey : Bytes}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hbody : (do
      let sckaMsg ← (spqrDeps F K).msgDeserialize pre.epoch pre.remaining
      let st0 ← (spqrDeps F K).statesFromPb pb
      let (key, st1') ← (spqrDeps F K).statesRecv st0 sckaMsg
      if pre.epoch == 0#64 then .error (.panic .recvEpochUnderflow)
      else do
        let msgKeyEpoch : Epoch := pre.epoch - 1#64
        let chain0 ← SpqrApiResult.ofError (chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation)
        let chain1 ← match key with
          | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
          | none => pure chain0
        let (chain2', msgKey) ← SpqrApiResult.ofChainResult (chain1.recvKey (spqrHkdfWith F) msgKeyEpoch pre.index)
        let newStateBytes := (spqrDeps F K).encodeState {
          inner := some ((spqrDeps F K).statesIntoPb st1'), versionNegotiation := none, chain := some chain2'.intoPb }
        let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
        (.ok ({ state := newStateBytes, key := outKey } : Recv) : SpqrApiResult Recv)) =
      .ok {
        state := PqRatchetState.encodeRaw {
          versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }
        key := if rawKey.isEmpty then none else some rawKey }) :
    (spqrV1Recv F K).recv stateBytes msgBytes =
      .ok (PqRatchetState.encodeRaw {
        versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb)
      }, if rawKey.isEmpty then none else some rawKey) := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have heq := recv_v1_ratchet_eq (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok
    (pqRatchetStateToPb_inner_some hinner) hmv hmin
  have hch : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  have hvn : (pqRatchetStateToPb pre_pb).versionNegotiation = pre_pb.versionNegotiation := rfl
  rw [hch, hvn] at heq
  exact spqrV1Recv_recv_of_ok (heq.trans hbody)

theorem spqrV1Recv_v1_ratchet_ok {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 st1 : States spqrPolyApi (spqrAuthApi F)}
    {key : Option EpochSecret} {chain0 chain1 chain2 : Chain} {rawKey : Bytes}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok ⟨key, st1⟩)
    (hep_ne : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hadd : (match key with
      | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
      | none => .ok chain0) = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey)) :
    (spqrV1Recv F K).recv stateBytes msgBytes =
      .ok (PqRatchetState.encodeRaw {
        versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb)
      }, if rawKey.isEmpty then none else some rawKey) := by
  refine spqrV1Recv_v1_ratchet_of_ok hpre hdec hinner hmv hmin ?_
  dsimp only [spqrDeps]
  rw [hmsg]; dsimp only [Bind.bind, Except.bind]
  rw [hst0]; dsimp only [liftStatesResult, Bind.bind, Except.bind]
  rw [hrecv]; dsimp only [Bind.bind, Except.bind]
  rw [hep_ne, hcf]
  cases key with
  | none =>
    cases hadd
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
      Proto.encodeState, pbToPqRatchetState, ↓reduceIte, hrk]; rfl
  | some es =>
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
      Proto.encodeState, pbToPqRatchetState, ↓reduceIte] at hadd ⊢
    rw [hadd]; simp only [hrk]; rfl

theorem encodeRaw_len_lt_of_recv_ok {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes stBytes : Bytes} {outKey : Option Bytes}
    (hst_len : stateBytes.length < 2 ^ 32)
    (hok : (spqrV1Recv F K).recv stateBytes msgBytes = .ok (stBytes, outKey)) :
    stBytes.length < 2 ^ 63 :=
  (encodeState_len_lt_spqrV1Recv F K stateBytes msgBytes stBytes outKey hst_len hok).2.2.1

/-! ## 2. 224-Byte `Option<Inner>` Relocation (`s0.sp - 2096#64 -> s0.sp - 2928#64`) -/

private theorem exists_words27_of_length_216_v1 (bs : List (BitVec 8)) (h : bs.length = 216) :
    ∃ d : Words27, ∀ out : BitVec 64, (out ↦ₛ bs) = words27At out d := by
  have hsplit (k : Nat) (l : List (BitVec 8)) : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 (bs := bs.take 8) (by simp [h])
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 8).take 8) (by simp [h])
  obtain ⟨w2, hw2⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 16).take 8) (by simp [h])
  obtain ⟨w3, hw3⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 24).take 8) (by simp [h])
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 32).take 8) (by simp [h])
  obtain ⟨w5, hw5⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 40).take 8) (by simp [h])
  obtain ⟨w6, hw6⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 48).take 8) (by simp [h])
  obtain ⟨w7, hw7⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 56).take 8) (by simp [h])
  obtain ⟨w8, hw8⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 64).take 8) (by simp [h])
  obtain ⟨w9, hw9⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 72).take 8) (by simp [h])
  obtain ⟨w10, hw10⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 80).take 8) (by simp [h])
  obtain ⟨w11, hw11⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 88).take 8) (by simp [h])
  obtain ⟨w12, hw12⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 96).take 8) (by simp [h])
  obtain ⟨w13, hw13⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 104).take 8) (by simp [h])
  obtain ⟨w14, hw14⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 112).take 8) (by simp [h])
  obtain ⟨w15, hw15⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 120).take 8) (by simp [h])
  obtain ⟨w16, hw16⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 128).take 8) (by simp [h])
  obtain ⟨w17, hw17⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 136).take 8) (by simp [h])
  obtain ⟨w18, hw18⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 144).take 8) (by simp [h])
  obtain ⟨w19, hw19⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 152).take 8) (by simp [h])
  obtain ⟨w20, hw20⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 160).take 8) (by simp [h])
  obtain ⟨w21, hw21⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 168).take 8) (by simp [h])
  obtain ⟨w22, hw22⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 176).take 8) (by simp [h])
  obtain ⟨w23, hw23⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 184).take 8) (by simp [h])
  obtain ⟨w24, hw24⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 192).take 8) (by simp [h])
  obtain ⟨w25, hw25⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 200).take 8) (by simp [h])
  obtain ⟨w26, hw26⟩ := exists_unpack64_of_length_8 (bs := bs.drop 208) (by simp [h])
  refine ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
           w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26⟩, fun out => ?_⟩
  have hbs : bs =
      unpack64 w0 ++ (unpack64 w1 ++ (unpack64 w2 ++ (unpack64 w3 ++
      (unpack64 w4 ++ (unpack64 w5 ++ (unpack64 w6 ++ (unpack64 w7 ++
      (unpack64 w8 ++ (unpack64 w9 ++ (unpack64 w10 ++ (unpack64 w11 ++
      (unpack64 w12 ++ (unpack64 w13 ++ (unpack64 w14 ++ (unpack64 w15 ++
      (unpack64 w16 ++ (unpack64 w17 ++ (unpack64 w18 ++ (unpack64 w19 ++
      (unpack64 w20 ++ (unpack64 w21 ++ (unpack64 w22 ++ (unpack64 w23 ++
      (unpack64 w24 ++ (unpack64 w25 ++ unpack64 w26))))))))))))))))))))))))) := by
    rw [← hw0, ← hw1, ← hw2, ← hw3, ← hw4, ← hw5, ← hw6, ← hw7, ← hw8,
        ← hw9, ← hw10, ← hw11, ← hw12, ← hw13, ← hw14, ← hw15, ← hw16, ← hw17,
        ← hw18, ← hw19, ← hw20, ← hw21, ← hw22, ← hw23, ← hw24, ← hw25, ← hw26]
    conv_lhs =>
      rw [hsplit 8 bs]
      rw [hsplit 8 (bs.drop 8)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 16)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 24)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 32)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 40)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 48)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 56)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 64)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 72)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 80)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 88)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 96)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 104)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 112)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 120)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 128)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 136)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 144)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 152)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 160)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 168)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 176)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 184)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 192)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 200)]; simp only [List.drop_drop, Nat.reduceAdd]
  conv_lhs => rw [hbs]
  dsimp only [words27At]
  simp only [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]

private theorem bytes224_expose_words28_move_2096_to_2928 (sp0 : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 224) :
    ((sp0 - 2096#64) ↦ₛ bs) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ d : Words27,
        ⌜((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d ⊢ ((sp0 - 2928#64) ↦ₛ bs)⌝ ∗
        ((sp0 - 2096#64) ↦₆₄ w0) ∗ words27SubAt sp0 2096 d := by
  have hsplit : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  have htake : (bs.take 8).length = 8 := by simp [hlen]
  have hdrop : (bs.drop 8).length = 216 := by simp [hlen]
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 htake
  obtain ⟨d, hd⟩ := exists_words27_of_length_216_v1 (bs.drop 8) hdrop
  have h_at (m : Nat) (h0 : m < 2 ^ 64) (h216 : 216 < m) :
      ((sp0 - BitVec.ofNat 64 m) ↦ₛ bs) = ((sp0 - BitVec.ofNat 64 m) ↦₆₄ w0) ∗ words27SubAt sp0 m d := by
    conv_lhs => rw [hsplit]
    rw [pointsToBytes_append, htake, hw0, ← pointsTo64_eq_pointsToBytes,
        hd ((sp0 - BitVec.ofNat 64 m) + 8#64), words27At_sub_eq sp0 m d h0 h216]
  rw [h_at 2096 (by decide) (by decide)]
  refine Entails.sepExists_right w0 (Entails.sepExists_right d ?_)
  refine Entails.pure_right ?_ (Entails.refl _)
  rw [h_at 2928 (by decide) (by decide)]; exact Entails.refl _

private theorem optProtoInnerStateAt_expose_224 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (sp0 : BitVec 64) (opt : Option V1State.InnerState) :
    Drop.optProtoInnerStateAt A (sp0 - 2096#64) opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ d : Words27, ∃∗ P_heap : SepProp,
        ⌜((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d ∗ P_heap ⊢
          Drop.optProtoInnerStateAt A (sp0 - 2928#64) opt⌝ ∗
        ((sp0 - 2096#64) ↦₆₄ w0) ∗ words27SubAt sp0 2096 d ∗ P_heap := by
  have hto := (relocOptProtoInnerStateAt H_inner A opt).2.to_bytes (sp0 - 2096#64)
  rw [h_inner_eq] at hto
  refine Entails.trans hto ?_
  apply sepExists_left_entails; intro bs
  refine Entails.pure_left fun hbs => ?_
  refine Entails.trans (sepConj_mono_left (bytes224_expose_words28_move_2096_to_2928 sp0 bs hbs)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply sepExists_left_entails; intro w0; apply sepExists_left_entails; intro d
  refine Entails.pure_left fun hmove => ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right d
    (Entails.sepExists_right ((relocOptProtoInnerStateAt H_inner A opt).1 bs) ?_))
  refine Entails.pure_right ?_ (Entails.of_eq (by ac_rfl))
  have hof := (relocOptProtoInnerStateAt H_inner A opt).2.of_bytes (sp0 - 2928#64) bs hbs
  rw [h_inner_eq] at hof
  refine Entails.trans ?_ hof
  refine Entails.trans (Entails.of_eq (show
    ((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d ∗ (relocOptProtoInnerStateAt H_inner A opt).1 bs =
    (((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d) ∗ (relocOptProtoInnerStateAt H_inner A opt).1 bs by ac_rfl)) ?_
  exact sepConj_mono_left hmove

/-! ## 3. Result Writing & `PqRatchetState` Drop Helpers (`+2820 .. +2916`) -/

private theorem vecU8_sub_entails_header_payload_v1 (A : RustAlloc) (sp0 : BitVec 64) (m : Nat)
    (bs : List (BitVec 8)) (h0 : m < 2 ^ 64 := by decide) (h16 : 16 < m := by decide) :
    vecU8 A (sp0 - BitVec.ofNat 64 m) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((sp0 - BitVec.ofNat 64 m) ↦₆₄ cap) ∗
        ((sp0 - BitVec.ofNat 64 (m - 8)) ↦₆₄ ptr) ∗
        ((sp0 - BitVec.ofNat 64 (m - 16)) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs := by
  unfold vecU8
  apply sepExists_left_entails; intro cap
  apply sepExists_left_entails; intro ptr
  rw [RustHeap.vecU8At_eq_header_sep_buf A (sp0 - BitVec.ofNat 64 m) cap ptr bs]
  dsimp only [RustHeap.vecHeader]
  have h8 : (sp0 - BitVec.ofNat 64 m) + 8#64 = sp0 - BitVec.ofNat 64 (m - 8) :=
    bv_sub_add_lit sp0 m 8 (by omega) h0
  have h16_eq : (sp0 - BitVec.ofNat 64 m) + 16#64 = sp0 - BitVec.ofNat 64 (m - 16) :=
    bv_sub_add_lit sp0 m 16 (by omega) h0
  rw [h8, h16_eq]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

private theorem vecU8_of_header_buf_v1 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      RustHeap.vecU8Buf A cap ptr bs ⊢
    vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [RustHeap.vecU8At_eq_header_sep_buf A a cap ptr bs]
  dsimp only [RustHeap.vecHeader]
  exact Entails.of_eq (by ac_rfl)

private theorem ret_48_split_6_v1 (ret : BitVec 64) :
    memRegion ret 48 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
      ∃∗ r3 : BitVec 64, ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64,
        (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
        ((ret + 24#64) ↦₆₄ r3) ∗ ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) := by
  rw [ret_48_split ret,
      ProofLib.memRegion_split' (b := ret + 32#64) (n := 8) (k := 8)
        (b' := ret + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (ret + 32#64),
      ProofLib.memRegion_eight (ret + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepExists_left_entails; intro r5
  apply sepExists_left_entails; intro r4
  apply sepExists_left_entails; intro r3
  apply sepExists_left_entails; intro r2
  apply sepExists_left_entails; intro r1
  apply sepExists_left_entails; intro r0
  refine Entails.sepExists_right r0 (Entails.sepExists_right r1 (Entails.sepExists_right r2
    (Entails.sepExists_right r3 (Entails.sepExists_right r4 (Entails.sepExists_right r5 ?_)))))
  exact Entails.refl _

private theorem recv_ok_some_foldX_v1 (A : RustAlloc) (ret : BitVec 64)
    (cap_st ptr_st cap_rk ptr_rk : BitVec 64) (stBytes rawKey : List (BitVec 8)) :
    (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
      ((ret + 24#64) ↦₆₄ cap_rk) ∗ ((ret + 32#64) ↦₆₄ ptr_rk) ∗
      ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
      RustHeap.vecU8Buf A cap_st ptr_st stBytes ∗
      RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ⊢
    recvResultExactKeyAt A ret (.ok (stBytes, some rawKey)) := by
  dsimp only [recvResultExactKeyAt, optKeyBytesAt]
  have hst := vecU8_of_header_buf_v1 A ret cap_st ptr_st stBytes
  have hrk := vecU8_of_header_buf_v1 A (ret + 24#64) cap_rk ptr_rk rawKey
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrk
  refine Entails.trans
    (Entails.of_eq (show
      (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        ((ret + 24#64) ↦₆₄ cap_rk) ∗ ((ret + 32#64) ↦₆₄ ptr_rk) ∗
        ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
        RustHeap.vecU8Buf A cap_st ptr_st stBytes ∗
        RustHeap.vecU8Buf A cap_rk ptr_rk rawKey =
      ((ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        RustHeap.vecU8Buf A cap_st ptr_st stBytes) ∗
      (((ret + 24#64) ↦₆₄ cap_rk) ∗ ((ret + 32#64) ↦₆₄ ptr_rk) ∗
        ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
        RustHeap.vecU8Buf A cap_rk ptr_rk rawKey) by ac_rfl)) ?_
  exact sepConj_mono hst hrk

private theorem recv_ok_none_foldX_v1 (A : RustAlloc) (ret : BitVec 64)
    (cap_st ptr_st r4 r5 : BitVec 64) (stBytes : List (BitVec 8)) :
    (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
      ((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) ∗
      RustHeap.vecU8Buf A cap_st ptr_st stBytes ⊢
    recvResultExactKeyAt A ret (.ok (stBytes, none)) := by
  dsimp only [recvResultExactKeyAt, optKeyBytesAt, noneCap]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hst := vecU8_of_header_buf_v1 A ret cap_st ptr_st stBytes
  have h16 : ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) ⊢ memRegion (ret + 32#64) 16 := by
    rw [ProofLib.memRegion_split' (b := ret + 32#64) (n := 8) (k := 8)
          (b' := ret + 40#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (ret + 32#64),
        ProofLib.memRegion_eight (ret + 40#64)]
    exact sepConj_mono (Entails.sepExists_right r4 (Entails.refl _))
      (Entails.sepExists_right r5 (Entails.refl _))
  refine Entails.trans
    (Entails.of_eq (show
      (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        ((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) ∗
        RustHeap.vecU8Buf A cap_st ptr_st stBytes =
      ((ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        RustHeap.vecU8Buf A cap_st ptr_st stBytes) ∗
      (((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        (((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5))) by ac_rfl)) ?_
  exact sepConj_mono hst (sepConj_mono_right h16)

private theorem spqrRecvRoAt_expose_dropJumpTable_v1 (b : BitVec 64) :
    spqrRecvRoAt b ⊢
      Drop.optProtoInnerStateJumpTableAt b ∗
      (∃∗ P_ro : SepProp, ⌜Drop.optProtoInnerStateJumpTableAt b ∗ P_ro ⊢ spqrRecvRoAt b⌝ ∗ P_ro) := by
  unfold spqrRecvRoAt Prost.MessageMerge.v1StateJumpTablesAt
  refine Entails.trans
    (Entails.of_eq (show
      (Prost.MessageMerge.v1StateMergeJumpTableExpanded b ∗ Drop.optProtoInnerStateJumpTableAt b) ∗
        statesFromPbJumpTableAt b ∗
        States.Recv.statesRecvRoAt b ∗
        statesIntoPbJumpTableAt b =
      Drop.optProtoInnerStateJumpTableAt b ∗
        (Prost.MessageMerge.v1StateMergeJumpTableExpanded b ∗
          statesFromPbJumpTableAt b ∗
          States.Recv.statesRecvRoAt b ∗
          statesIntoPbJumpTableAt b) by ac_rfl)) ?_
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right _ (Entails.pure_right ?_ (Entails.refl _))
  exact Entails.of_eq (by ac_rfl)

private theorem protoPqRatchetState_entails_drop_v1 (A : RustAlloc) (sp0 : BitVec 64)
    (chPb : ChainPB) (pb1 : V1State) :
    ((sp0 - 3056#64) ↦₆₄ noneCap) ∗
      memRegion (sp0 - 3048#64) 40 ∗
      ProtoRepr.chainPBAt A (sp0 - 3008#64) chPb ∗
      Drop.optProtoInnerStateAt A (sp0 - 2928#64) pb1.innerState ⊢
    Drop.protoPqRatchetStateAt A (sp0 - 3056#64)
      { versionNegotiation := none, chain := some chPb, inner := some (.v1 pb1) } := by
  dsimp only [Drop.protoPqRatchetStateAt, optVersionNegotiationPBAt, ProtoRepr.optChainPBAt, Drop.optProtoPqRatchetInnerAt]
  have h8 : (sp0 - 3056#64) + 8#64 = sp0 - 3048#64 := bv_sub_add_lit sp0 3056 8
  have h48 : (sp0 - 3056#64) + 48#64 = sp0 - 3008#64 := bv_sub_add_lit sp0 3056 48
  have h128 : (sp0 - 3056#64) + 128#64 = sp0 - 2928#64 := bv_sub_add_lit sp0 3056 128
  rw [h8, h48, h128]
  exact Entails.of_eq (by ac_rfl)

/-! ## 4. Stack Frame Splits and Reassembly for `+2664 .. +2916` -/

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_sub_96_sub_32 (sp0 : BitVec 64) :
    (sp0 - 96#64) + 18446744073709551584#64 = sp0 - 128#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_sub_96_sub_136 (sp0 : BitVec 64) :
    (sp0 - 96#64) - 136#64 = sp0 - 232#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
private theorem hsp_add_544 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 544#64 = s0.sp - 144#64 := by
  unfold Kdf.HkdfToSliceProof.hsp; bv_omega

@[local simp, local arm64_norm, local wp_norm]
private theorem hsp_add_560 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 560#64 = s0.sp - 128#64 := by
  unfold Kdf.HkdfToSliceProof.hsp; bv_omega

@[local simp, local arm64_norm, local wp_norm]
private theorem hsp_add_456 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 456#64 = s0.sp - 232#64 := by
  unfold Kdf.HkdfToSliceProof.hsp; bv_omega

private theorem memRegion_2856_split_v1_ok (sp0 : BitVec 64) :
    memRegion (sp0 - 3088#64) 2856 ⊢
      memRegion (sp0 - 3088#64) 32 ∗
      (∃∗ w790 : BitVec 64, (sp0 - 3056#64) ↦₆₄ w790) ∗
      memRegion (sp0 - 3048#64) 40 ∗
      memRegion (sp0 - 3008#64) 80 ∗
      memRegion (sp0 - 2928#64) 224 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      memRegion (sp0 - 2096#64) Drop.optProtoInnerStateSize ∗
      memRegion (sp0 - 1872#64) 1640 := by
  unfold Drop.optProtoInnerStateSize
  rw [show (2856 : Nat) = 32 + (8 + (40 + (80 + (224 + (608 + (224 + 1640)))))) by decide,
      memRegion_split (sp0 - 3088#64) 32 (8 + (40 + (80 + (224 + (608 + (224 + 1640)))))) (by decide),
      show (sp0 - 3088#64) + 32#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 8 (40 + (80 + (224 + (608 + (224 + 1640))))) (by decide),
      show (sp0 - 3056#64) + 8#64 = sp0 - 3048#64 by bv_omega,
      memRegion_split (sp0 - 3048#64) 40 (80 + (224 + (608 + (224 + 1640)))) (by decide),
      show (sp0 - 3048#64) + 40#64 = sp0 - 3008#64 by bv_omega,
      memRegion_split (sp0 - 3008#64) 80 (224 + (608 + (224 + 1640))) (by decide),
      show (sp0 - 3008#64) + 80#64 = sp0 - 2928#64 by bv_omega,
      memRegion_split (sp0 - 2928#64) 224 (608 + (224 + 1640)) (by decide),
      show (sp0 - 2928#64) + 224#64 = sp0 - 2704#64 by bv_omega,
      memRegion_split (sp0 - 2704#64) 608 (224 + 1640) (by decide),
      show (sp0 - 2704#64) + 608#64 = sp0 - 2096#64 by bv_omega,
      memRegion_split (sp0 - 2096#64) 224 1640 (by decide),
      show (sp0 - 2096#64) + 224#64 = sp0 - 1872#64 by bv_omega,
      ProofLib.memRegion_eight (sp0 - 3056#64)]
  exact Entails.refl _

private theorem memRegion_224_split_24_200_v1 (sp0 : BitVec 64) :
    memRegion (sp0 - 2096#64) 224 ⊢
      memRegion (sp0 - 2096#64) 24 ∗ memRegion (sp0 - 2072#64) 200 := by
  rw [show (224 : Nat) = 24 + 200 by decide,
      memRegion_split (sp0 - 2096#64) 24 200 (by decide),
      show (sp0 - 2096#64) + 24#64 = sp0 - 2072#64 by bv_omega]
  exact Entails.refl _

private theorem memRegion_48_split_144_v1 (sp0 : BitVec 64) :
    memRegion (sp0 - 144#64) 48 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ((sp0 - 144#64) ↦₆₄ w0) ∗ ((sp0 - 136#64) ↦₆₄ w1) ∗
        ((sp0 - 128#64) ↦₆₄ w2) ∗ memRegion (sp0 - 120#64) 24 := by
  rw [show (48 : Nat) = 24 + 24 by decide,
      memRegion_split (sp0 - 144#64) 24 24 (by decide),
      show (sp0 - 144#64) + 24#64 = sp0 - 120#64 by bv_omega,
      memRegion_24_words3 (sp0 - 144#64),
      show (sp0 - 144#64) + 8#64 = sp0 - 136#64 by bv_omega,
      show (sp0 - 144#64) + 16#64 = sp0 - 128#64 by bv_omega]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepExists_left_entails; intro w2; apply sepExists_left_entails; intro w1; apply sepExists_left_entails; intro w0
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.refl _)))

private theorem ownFrame_join_v1_ok_2892 (sp0 w0_st w1_st w2_st w0_144 w1_144 w2_144 : BitVec 64) :
    memRegion (sp0 - 4992#64) 352 ∗ memRegion (sp0 - 4640#64) 48 ∗ memRegion (sp0 - 4592#64) 576 ∗
      memRegion (sp0 - 4016#64) chunkedStatesSize ∗ memRegion (sp0 - 3088#64) 32 ∗
      memRegion (sp0 - 3056#64) 352 ∗ memRegion (sp0 - 2704#64) 608 ∗
      ((sp0 - 2096#64) ↦₆₄ w0_st) ∗ ((sp0 - 2088#64) ↦₆₄ w1_st) ∗ ((sp0 - 2080#64) ↦₆₄ w2_st) ∗
      memRegion (sp0 - 2072#64) 200 ∗ memRegion (sp0 - 1872#64) 1640 ∗ memRegion (sp0 - 232#64) 88 ∗
      ((sp0 - 144#64) ↦₆₄ w0_144) ∗ ((sp0 - 136#64) ↦₆₄ w1_144) ∗ ((sp0 - 128#64) ↦₆₄ w2_144) ∗
      memRegion (sp0 - 120#64) 24 ⊢
    memRegion (sp0 - 4992#64) 0x1320 := by
  unfold chunkedStatesSize
  have h24_st := words3_to_memRegion_24 (sp0 - 2096#64) w0_st w1_st w2_st
  rw [show (sp0 - 2096#64) + 8#64 = sp0 - 2088#64 by bv_omega,
      show (sp0 - 2096#64) + 16#64 = sp0 - 2080#64 by bv_omega] at h24_st
  have h24_144 := words3_to_memRegion_24 (sp0 - 144#64) w0_144 w1_144 w2_144
  rw [show (sp0 - 144#64) + 8#64 = sp0 - 136#64 by bv_omega,
      show (sp0 - 144#64) + 16#64 = sp0 - 128#64 by bv_omega] at h24_144
  rw [show (0x1320 : Nat) = 352 + (48 + (576 + (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))))))) by decide,
      memRegion_split (sp0 - 4992#64) 352 (48 + (576 + (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))))))) (by decide),
      show (sp0 - 4992#64) + 352#64 = sp0 - 4640#64 by bv_omega,
      memRegion_split (sp0 - 4640#64) 48 (576 + (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24)))))))))) (by decide),
      show (sp0 - 4640#64) + 48#64 = sp0 - 4592#64 by bv_omega,
      memRegion_split (sp0 - 4592#64) 576 (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))))) (by decide),
      show (sp0 - 4592#64) + 576#64 = sp0 - 4016#64 by bv_omega,
      memRegion_split (sp0 - 4016#64) 928 (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24)))))))) (by decide),
      show (sp0 - 4016#64) + 928#64 = sp0 - 3088#64 by bv_omega,
      memRegion_split (sp0 - 3088#64) 32 (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))) (by decide),
      show (sp0 - 3088#64) + 32#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 352 (608 + (24 + (200 + (1640 + (88 + (24 + 24)))))) (by decide),
      show (sp0 - 3056#64) + 352#64 = sp0 - 2704#64 by bv_omega,
      memRegion_split (sp0 - 2704#64) 608 (24 + (200 + (1640 + (88 + (24 + 24))))) (by decide),
      show (sp0 - 2704#64) + 608#64 = sp0 - 2096#64 by bv_omega,
      memRegion_split (sp0 - 2096#64) 24 (200 + (1640 + (88 + (24 + 24)))) (by decide),
      show (sp0 - 2096#64) + 24#64 = sp0 - 2072#64 by bv_omega,
      memRegion_split (sp0 - 2072#64) 200 (1640 + (88 + (24 + 24))) (by decide),
      show (sp0 - 2072#64) + 200#64 = sp0 - 1872#64 by bv_omega,
      memRegion_split (sp0 - 1872#64) 1640 (88 + (24 + 24)) (by decide),
      show (sp0 - 1872#64) + 1640#64 = sp0 - 232#64 by bv_omega,
      memRegion_split (sp0 - 232#64) 88 (24 + 24) (by decide),
      show (sp0 - 232#64) + 88#64 = sp0 - 144#64 by bv_omega,
      memRegion_split (sp0 - 144#64) 24 24 (by decide),
      show (sp0 - 144#64) + 24#64 = sp0 - 120#64 by bv_omega]
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 4992#64) 352 ∗ memRegion (sp0 - 4640#64) 48 ∗ memRegion (sp0 - 4592#64) 576 ∗
        memRegion (sp0 - 4016#64) 928 ∗ memRegion (sp0 - 3088#64) 32 ∗ memRegion (sp0 - 3056#64) 352 ∗
        memRegion (sp0 - 2704#64) 608 ∗ ((sp0 - 2096#64) ↦₆₄ w0_st) ∗ ((sp0 - 2088#64) ↦₆₄ w1_st) ∗
        ((sp0 - 2080#64) ↦₆₄ w2_st) ∗ memRegion (sp0 - 2072#64) 200 ∗ memRegion (sp0 - 1872#64) 1640 ∗
        memRegion (sp0 - 232#64) 88 ∗ ((sp0 - 144#64) ↦₆₄ w0_144) ∗ ((sp0 - 136#64) ↦₆₄ w1_144) ∗
        ((sp0 - 128#64) ↦₆₄ w2_144) ∗ memRegion (sp0 - 120#64) 24 =
      memRegion (sp0 - 4992#64) 352 ∗ memRegion (sp0 - 4640#64) 48 ∗ memRegion (sp0 - 4592#64) 576 ∗
        memRegion (sp0 - 4016#64) 928 ∗ memRegion (sp0 - 3088#64) 32 ∗ memRegion (sp0 - 3056#64) 352 ∗
        memRegion (sp0 - 2704#64) 608 ∗
        (((sp0 - 2096#64) ↦₆₄ w0_st) ∗ ((sp0 - 2088#64) ↦₆₄ w1_st) ∗ ((sp0 - 2080#64) ↦₆₄ w2_st)) ∗
        memRegion (sp0 - 2072#64) 200 ∗ memRegion (sp0 - 1872#64) 1640 ∗ memRegion (sp0 - 232#64) 88 ∗
        (((sp0 - 144#64) ↦₆₄ w0_144) ∗ ((sp0 - 136#64) ↦₆₄ w1_144) ∗ ((sp0 - 128#64) ↦₆₄ w2_144)) ∗
        memRegion (sp0 - 120#64) 24 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono h24_st
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h24_144)))))))))))

/-! ## 5. Result Epilogue & Drop Cleanup (`+2820 .. +2916 -> +876 -> +1040 -> ret`) -/

private theorem vecU8Buf_expose_len_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    RustHeap.vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ RustHeap.vecU8Buf A cap ptr bs := by
  unfold RustHeap.vecU8Buf
  exact Entails.pure_left fun h => Entails.pure_right h (Entails.pure_right h (Entails.refl _))

private theorem vecU8Buf_nil_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64) :
    RustHeap.vecU8Buf A cap ptr [] ⊢
      ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      if cap = 0#64 then emp
      else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold RustHeap.vecU8Buf
  apply Entails.pure_left; rintro ⟨_, hcap, hptr⟩
  refine Entails.pure_right ⟨hcap, hptr⟩ ?_
  by_cases hc : cap = 0#64
  · simp only [hc, ↓reduceIte]; exact Entails.refl _
  · simp only [hc, ↓reduceIte, List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero,
      pointsToBytes_nil, emp_sepConj]; exact Entails.refl _

private theorem ofNat64_beq_zero_false_of_ne_nil {bs : List (BitVec 8)}
    (hne : bs.isEmpty = false) (hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  have hpos : 0 < bs.length := by
    cases bs with
    | nil => contradiction
    | cons _ _ => exact Nat.succ_pos _
  rw [beq_eq_false_iff_ne]; intro h0
  have h0n := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at h0n; omega

/-- Shared cleanup at `+2884 .. +2916 -> +876 -> +1040` (`0x55170 .. 0x55190 -> 0x54998 ->
    0x54a3c`): calls `drop_in_place<PqRatchetState>` on `newPb` at `s0.sp - 3056#64`, drops
    `pre_pb.versionNegotiation` at `s0.sp - 4640#64` (`x23 = w0`), jumps to `+876` (`cbz w26,
    +1040`), joins the stack frame, and returns via `step_epilogue`. -/
theorem step_v1_drop_newPb_and_vn_2884 (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb newPb : PqRatchetState)
    (w0 w1 w0_st w1_st w2_st w0_144 w1_144 w2_144 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 2884#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hP : P =
      spqrRecvRoAt b ∗ st.at A ∗ msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      pqRatchetStatePBAt A (s0.sp - 3056#64) newPb ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ w0_st) ∗ ((s0.sp - 2088#64) ↦₆₄ w1_st) ∗ ((s0.sp - 2080#64) ↦₆₄ w2_st) ∗
      memRegion (s0.sp - 2072#64) 200 ∗ memRegion (s0.sp - 1872#64) 1640 ∗ memRegion (s0.sp - 232#64) 88 ∗
      ((s0.sp - 144#64) ↦₆₄ w0_144) ∗ ((s0.sp - 136#64) ↦₆₄ w1_144) ∗ ((s0.sp - 128#64) ↦₆₄ w2_144) ∗
      memRegion (s0.sp - 120#64) 24 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hdrop_pq := spqrRecv_dropPqRatchetState_ok hdealloc
  simp only [Drop.dropProtoPqRatchetStateSpec] at hdrop_pq
  have hdealloc_raw := spqrRecv_dealloc_ok hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hdrop_pq hdealloc_raw hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 2884 36
  spqr_recv_fetches_range b (Rust.withPanics ext) 876 4
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  rw [← protoPqRatchetStateAt_eq_pqRatchetStatePBAt A (s0.sp - 3056#64) newPb]
  refine SepWP.focus_weaken (spqrRecvRoAt_expose_dropJumpTable_v1 b) (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro_drop
  wp_focus_pure; intro hP_ro_drop
  wp_steps 2
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide))) (by sep_focus) ?_
  wp_call hdrop_pq ⟨s0.sp - 3056#64, newPb⟩
  have hsp_eq : stackAt s.sp dropStack96 = stackAt (s0.sp - 4992#64) dropStack96 := by rw [hsp]
  refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken hP_ro_drop (by sep_focus) ?_
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    dsimp only [optVersionNegotiationPBTailAt]
    wp_focus_pure; intro hw0; subst hw0
    have hsle : (1#64).sle noneCap = false := rfl
    wp_steps 3
    refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (ownFrame_join_v1_ok_2892 s0.sp w0_st w1_st w2_st w0_144 w1_144 w2_144) (by sep_focus) ?_
    exact step_epilogue b A M ext st msg ret s0 _ _ R post hpost
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
      (by simp only [arm64_norm, *]) (by ac_rfl)
  | some vn =>
    refine SepWP.focus_weaken (vnTail_sub4640_some_entails_dealloc A s0.sp w0 w1 vn) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc]
    by_cases hc0 : (w0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hw0
      wp_steps 3
      refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (ownFrame_join_v1_ok_2892 s0.sp w0_st w1_st w2_st w0_144 w1_144 w2_144) (by sep_focus) ?_
      exact step_epilogue b A M ext st msg ret s0 _ _ R post hpost
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
        (by simp only [arm64_norm, *]) (by ac_rfl)
    · have hslt := Drop.cap_ne_zero_slt_one_false hcap_lt hc0
      have hsle := cap_ne_zero_one_sle_true hcap_lt hc0
      have hlt_false := Drop.cap_ne_zero_lt_one_false hcap_lt hc0
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide))) (by sep_focus) ?_
      wp_steps 6
      wp_call hdealloc_raw ⟨w1, w0.toNat, 1⟩
      wp_conv_pre => simp only [arm64_norm, *]
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm) (by sep_focus) ?_
      wp_steps 2
      refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp w0 w1) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (ownFrame_join_v1_ok_2892 s0.sp w0_st w1_st w2_st w0_144 w1_144 w2_144) (by sep_focus) ?_
      exact step_epilogue b A M ext st msg ret s0 _ _ R post hpost
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
        (by simp only [arm64_norm, *]) (by ac_rfl)

/-- (`+2820 .. +2916 -> +876 -> +1040 -> ret`): writes `Ok((PqRatchetState.encodeRaw newPb, if
    rawKey.isEmpty then none else some rawKey))` at `ret`, drops `newPb` and
    `pre_pb.versionNegotiation`, and returns via `step_epilogue`. -/
theorem step_v1_ok_epilogue_2820_to_ret {img : Obj.Image} (A : RustAlloc)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt img.base A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb newPb : PqRatchetState)
    (rawKey : Bytes)
    (w0 w1 cap_rk ptr_rk : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw newPb, if rawKey.isEmpty then none else some rawKey))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx25 : s.readReg64 .x25 = 0xFFFFFFFFFFFFFFFF#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      pqRatchetStatePBAt A (s0.sp - 3056#64) newPb ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      vecU8 A (s0.sp - 2096#64) (PqRatchetState.encodeRaw newPb) ∗
      memRegion (s0.sp - 2072#64) 200 ∗ memRegion (s0.sp - 1872#64) 1640 ∗
      memRegion (s0.sp - 232#64) 88 ∗ memRegion (s0.sp - 144#64) 48 ∗
      RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hdealloc_raw := spqrRecv_dealloc_ok hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  apply SepWPpI.of_sepWP_ret
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 2820 64
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken
    (vecU8_sub_entails_header_payload_v1 A s0.sp 2096 (PqRatchetState.encodeRaw newPb)) (by sep_focus) ?_
  wp_pull_exists; rename_i cap_st ptr_st
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  refine SepWP.focus_weaken (ret_48_split_6_v1 ret) (by sep_focus) ?_
  wp_pull_exists; rename_i r0 r1 r2 r3 r4 r5
  refine SepWP.focus_weaken (memRegion_48_split_144_v1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w0_144 w1_144 w2_144
  refine SepWP.focus_weaken (vecU8Buf_expose_len_lt A cap_rk ptr_rk rawKey) (by sep_focus) ?_
  wp_focus_pure; rintro ⟨hrk_le, hcap_rk_lt, hptr_rk_ne⟩
  cases hrk_empty : rawKey.isEmpty with
  | true =>
    have hrk_nil : rawKey = [] := List.isEmpty_iff.mp hrk_empty
    subst hrk_nil
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx24
    have hok' : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok (PqRatchetState.encodeRaw newPb, none) := by
      simpa [hrk_empty] using hok
    have hfold_none := recv_ok_none_foldX_v1 A ret cap_st ptr_st r4 r5 (PqRatchetState.encodeRaw newPb)
    rw [← hok'] at hfold_none
    refine SepWP.focus_weaken (vecU8Buf_nil_entails_dealloc A cap_rk ptr_rk) (by sep_focus) ?_
    wp_focus_pure; rintro ⟨_, _⟩
    by_cases hc_rk : cap_rk = 0#64
    · subst hc_rk
      simp only [↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps 9
      refine SepWP.focus_weaken hfold_none (by sep_focus) ?_
      refine sepWP_spqrRecvPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_v1_drop_newPb_and_vn_2884 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret pre_pb newPb
        w0 w1 cap_st ptr_st (BitVec.ofNat 64 (PqRatchetState.encodeRaw newPb).length)
        cap_st ptr_st (BitVec.ofNat 64 (PqRatchetState.encodeRaw newPb).length)
        s0 _ _ R _ rfl hs0_align
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl)
    · have hc_beq : (cap_rk == 0#64) = false := beq_eq_false_iff_ne.mpr hc_rk
      simp only [hc_rk, ↓reduceIte]
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide))) (by sep_focus) ?_
      wp_steps 13
      wp_call hdealloc_raw ⟨ptr_rk, cap_rk.toNat, 1⟩
      have hsp_eq : stackAt s.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp]
      refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hfold_none (by sep_focus) ?_
      refine sepWP_spqrRecvPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_v1_drop_newPb_and_vn_2884 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret pre_pb newPb
        w0 w1 cap_st ptr_st (BitVec.ofNat 64 (PqRatchetState.encodeRaw newPb).length)
        cap_st ptr_st (BitVec.ofNat 64 (PqRatchetState.encodeRaw newPb).length)
        s0 _ _ R _ rfl hs0_align
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl)
  | false =>
    have hrk_len_lt : rawKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrk_le hcap_rk_lt
    have hrk_ne0 : (BitVec.ofNat 64 rawKey.length == 0#64) = false :=
      ofNat64_beq_zero_false_of_ne_nil hrk_empty hrk_len_lt
    have hok' : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok (PqRatchetState.encodeRaw newPb, some rawKey) := by
      simpa [hrk_empty] using hok
    have hfold_some := recv_ok_some_foldX_v1 A ret cap_st ptr_st cap_rk ptr_rk
      (PqRatchetState.encodeRaw newPb) rawKey
    rw [← hok'] at hfold_some
    wp_steps 10
    refine SepWP.focus_weaken hfold_some (by sep_focus) ?_
    refine sepWP_spqrRecvPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
    exact step_v1_drop_newPb_and_vn_2884 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret pre_pb newPb
      w0 w1 cap_st ptr_st (BitVec.ofNat 64 (PqRatchetState.encodeRaw newPb).length)
      cap_st ptr_st (BitVec.ofNat 64 (PqRatchetState.encodeRaw newPb).length)
      s0 _ _ R _ rfl hs0_align
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl)

/-! ## 6. `<States>::into_pb`, `<Chain>::into_pb`, and `<PqRatchetState>::encode_to_vec` (`+2664 .. +2820`) -/

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_writeVReg128_v1 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).sp = s.sp := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_setPState_v1 (s : State) (p : PState) :
    (s.setPState p).sp = s.sp := rfl

/-- (`+2688 .. +2820`, `0x550ac .. 0x55130`): copies `st1.into_pb.innerState` (`224`B) from
    `s0.sp - 2096#64` to `s0.sp - 2928#64`, stores `noneCap` (`-1`) at `s0.sp - 3056#64`, calls
    `<PqRatchetState>::encode_to_vec`, and continues via `step_v1_ok_epilogue_2820_to_ret`. -/
theorem step_v1_encodeToVec_2688_to_2820 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (st1 : States spqrPolyApi (spqrAuthApi F))
    (chain2 : Chain) (rawKey : Bytes)
    (w0 w1 w790 cap_rk ptr_rk : BitVec 64)
    (hlen_enc : (PqRatchetState.encodeRaw
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }).length < 2 ^ 63)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) },
        if rawKey.isEmpty then none else some rawKey))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2688#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ w790) ∗
      memRegion (s0.sp - 3048#64) 40 ∗
      ProtoRepr.chainPBAt A (s0.sp - 3008#64) chain2.intoPb ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      Drop.optProtoInnerStateAt A (s0.sp - 2096#64) st1.into_pb.innerState ∗
      memRegion (s0.sp - 1872#64) 1640 ∗
      memRegion (s0.sp - 232#64) 88 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have henc_ok := spqrRecv_encodeToVec_ok hC
  subst hP
  apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
    bv% (ls_rel% "spqr::recv" "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 2688 132
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken
    (optProtoInnerStateAt_expose_224 H_inner A hC.h_inner_eq s0.sp st1.into_pb.innerState) (by sep_focus) ?_
  wp_pull_exists; rename_i w0_in d_in H_in
  wp_focus_pure; intro hpack_in
  refine SepWP.focus_weaken (memRegion_224_sub_entails_words28 s0.sp 2928) (by sep_focus) ?_
  wp_pull_exists; rename_i u0 uDst
  have hjoin_src :
      ((s0.sp - 2096#64) ↦₆₄ w0_in) ∗ words27SubAt s0.sp 2096 d_in ⊢
      memRegion (s0.sp - 2096#64) 24 ∗ memRegion (s0.sp - 2072#64) 200 :=
    Entails.trans (words27SubAt_to_memRegion_224 s0.sp 2096 w0_in d_in)
      (memRegion_224_split_24_200_v1 s0.sp)
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hpack_in hjoin_src ⊢
  simp only [sepConj_assoc]
  wp_steps 33
  refine SepWP.focus_weaken hpack_in (by sep_focus) ?_
  refine SepWP.focus_weaken hjoin_src (by sep_focus) ?_
  have hpack_pq :
      ((s0.sp - 3056#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        memRegion (s0.sp - 3048#64) 40 ∗
        ProtoRepr.chainPBAt A (s0.sp - 3008#64) chain2.intoPb ∗
        Drop.optProtoInnerStateAt A (s0.sp - 2928#64) st1.into_pb.innerState ⊢
      pqRatchetStatePBAt A (s0.sp - 3056#64)
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) } := by
    rw [← protoPqRatchetStateAt_eq_pqRatchetStatePBAt A (s0.sp - 3056#64)]
    exact protoPqRatchetState_entails_drop_v1 A s0.sp chain2.intoPb st1.into_pb
  refine SepWP.focus_weaken hpack_pq (by sep_focus) ?_
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) (by decide))) (by sep_focus) ?_
  refine SepWPpI.call_inImage henc_ok
    ⟨s0.sp - 2096#64, s0.sp - 3056#64,
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }⟩
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, *]; exact hs0_align)
    (rfl : _ = entry + 2820#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed) (fun _ _ => rfl)
    (by
      dsimp only [pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], hlen_enc⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128_v1, sp_setPState_v1, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, _, _, hxfp_c, hvregs_c⟩
  dsimp only [pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = cap_rk := by rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = ptr_rk := by rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = BitVec.ofNat 64 rawKey.length := by rw [hx24_c]; simp only [arm64_norm, *]
  have hx25_sm : sm.readReg64 .x25 = 0xFFFFFFFFFFFFFFFF#64 := by rw [hx25_c]; simp only [arm64_norm, *]
  have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128_v1, sp_setPState_v1, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) (by decide)).symm) (by sep_focus) ?_
  exact step_v1_ok_epilogue_2820_to_ret A F K ext hC.base_aligned hC.hA.dealloc
    st msg ret pre_pb
    { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }
    rawKey w0 w1 cap_rk ptr_rk hok s0 sm _ R hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; exact hpcm)
    hrunm hspm' htr_sm' hx19_sm hx21_sm hx22_sm hx23_sm hx24_sm hx25_sm hx26_sm hx29_sm (by ac_rfl)

/-- (`+2676 .. +2688`, `0x550a0 .. 0x550ac`): calls `<Chain>::into_pb` on `chain2` at `s0.sp -
    232#64`, writing `chain2.intoPb` to `s0.sp - 3008#64`, joins `memRegion (s0.sp - 232#64)
    88`, and continues via `step_v1_encodeToVec_2688_to_2820`. -/
theorem step_v1_chainIntoPb_2676_to_2688 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (st1 : States spqrPolyApi (spqrAuthApi F))
    (G : ChainProofs.ChainGhost) (chain2 : Chain) (rawKey : Bytes)
    (w0 w1 w790 cap_rk ptr_rk : BitVec 64)
    (hlen_enc : (PqRatchetState.encodeRaw
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }).length < 2 ^ 63)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) },
        if rawKey.isEmpty then none else some rawKey))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2676#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx25 : s.readReg64 .x25 = s0.sp - 3056#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ w790) ∗
      memRegion (s0.sp - 3048#64) 40 ∗
      memRegion (s0.sp - 3008#64) 80 ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      Drop.optProtoInnerStateAt A (s0.sp - 2096#64) st1.into_pb.innerState ∗
      memRegion (s0.sp - 1872#64) 1640 ∗
      ChainProofs.chainAt A (s0.sp - 232#64) G chain2 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hchain_into := spqrRecv_chainIntoPb_ok hC
  subst hP
  apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
    bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::into_pb"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 2676 12
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  wp_steps 3
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide))) (by sep_focus) ?_
  refine SepWPpI.call_inImage hchain_into ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; exact sp_sub_4992_aligned s0 hs0_align)
    (rfl : _ = entry + 2688#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed) (fun _ _ => rfl)
    (by
      dsimp only [chainIntoPbSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, _, hx26_c, _, _, hxfp_c, hvregs_c⟩
  dsimp only [chainIntoPbSpecX]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = cap_rk := by rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = ptr_rk := by rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = BitVec.ofNat 64 rawKey.length := by rw [hx24_c]; simp only [arm64_norm, *]
  have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)).symm) (by sep_focus) ?_
  exact step_v1_encodeToVec_2688_to_2820 hC st msg ret pre_pb st1 chain2 rawKey
    w0 w1 w790 cap_rk ptr_rk hlen_enc hok s0 sm _ R hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; exact hpcm)
    hrunm hspm' htr_sm' hx19_sm hx21_sm hx22_sm hx23_sm hx24_sm hx26_sm hx29_sm (by ac_rfl)

/-- Combined V1 ratchet `Ok` tail (`+2664 .. +2916 -> +876 -> +1040 -> ret`): calls
    `<States>::into_pb`, `<Chain>::into_pb`, `<PqRatchetState>::encode_to_vec`, writes
    `Ok((newStateBytes, outKey))` to `ret`, drops `newPb` and `pre_pb.versionNegotiation`, and
    returns via `step_epilogue`. -/
theorem step_v1_ok_2664_to_ret {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (sckaMsg : Message spqrPolyApi)
    (st0 st1 : States spqrPolyApi (spqrAuthApi F))
    (key : Option EpochSecret) (chain0 chain1 chain2 : Chain)
    (G : ChainProofs.ChainGhost) (rawKey : Bytes)
    (w0 w1 cap_rk ptr_rk : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok ⟨key, st1⟩)
    (hep_ne : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hadd : (match key with
      | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
      | none => .ok chain0) = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2664#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx25 : s.readReg64 .x25 = s0.sp - 3056#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      chunkedStatesAt A (s0.sp - 4016#64) st1 ∗
      memRegion (s0.sp - 3088#64) 2856 ∗
      ChainProofs.chainAt A (s0.sp - 232#64) G chain2 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hstates_into := spqrRecv_statesIntoPb_ok hC
  have hok := spqrV1Recv_v1_ratchet_ok hpre hdec hinner hmv hmin hmsg hst0 hrecv hep_ne hcf hadd hrk
  have hlen_enc := encodeRaw_len_lt_of_recv_ok hst_len hok
  subst hP
  apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
    bv% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::States>::into_pb"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 2664 12
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken (memRegion_2856_split_v1_ok s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w790
  refine SepWP.focus_weaken (spqrRecvRoAt_expose_statesIntoPb img.base) (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro_into
  wp_focus_pure; intro hP_ro_into
  wp_steps 3
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesIntoPbStackX (by decide))) (by sep_focus) ?_
  refine SepWPpI.call_inImage hstates_into ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; exact sp_sub_4992_aligned s0 hs0_align)
    (rfl : _ = entry + 2676#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed) (fun _ _ => rfl)
    (by
      dsimp only [statesIntoPbSpecX, statesIntoPbSpec]
      have hmem_eq : memRegion (s0.sp - 2096#64) Drop.optProtoInnerStateSize =
          memRegion (s0.sp - 2096#64) DecodeState.optProtoInnerStateSize := rfl
      rw [hmem_eq]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], hC.base_aligned⟩
        (by simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, _, _, hxfp_c, hvregs_c⟩
  dsimp only [statesIntoPbSpecX, statesIntoPbSpec]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = cap_rk := by rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = ptr_rk := by rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = BitVec.ofNat 64 rawKey.length := by rw [hx24_c]; simp only [arm64_norm, *]
  have hx25_sm : sm.readReg64 .x25 = s0.sp - 3056#64 := by rw [hx25_c]; simp only [arm64_norm, *]
  have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesIntoPbStackX (by decide)).symm) (by sep_focus) ?_
  refine SepWPpI.focus_weaken hP_ro_into (by sep_focus) ?_
  exact step_v1_chainIntoPb_2676_to_2688 hC st msg ret pre_pb st1 G chain2 rawKey
    w0 w1 w790 cap_rk ptr_rk hlen_enc hok s0 sm _ R hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; exact hpcm)
    hrunm hspm' htr_sm' hx19_sm hx21_sm hx22_sm hx23_sm hx24_sm hx25_sm hx26_sm hx29_sm (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv

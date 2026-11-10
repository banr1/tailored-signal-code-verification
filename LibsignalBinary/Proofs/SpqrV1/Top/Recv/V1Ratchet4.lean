/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet2
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1RatchetErr2500
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: V1 Ratchet Chain Segment (`+1856..+2024 -> +2664`)

Symbolic execution of `spqr::chain_from` (`+1856..+1884`), 88-byte `Chain` relocation and optional
`<Chain>::add_epoch` (`+1888..+1976`), and `<Chain>::recv_key` (`+1976..+2024`) on the V1 ratchet
path of `spqr::recv` (`0x5462c`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.DecodeState CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
open CryptoVerification.SpqrV1.Top.MessageDeserialize CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize CryptoVerification.SpqrV1.ChainProofs CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

/-! ## 1. Pure Model, Size/Fit, & `Words11` Helpers -/

private theorem length_le_map_sum_add_200 (ls : List ChainEpochPB) :
    ls.length ≤ (ls.map (fun ep => StateSize.rawChainEpoch ep + 200)).sum := by
  induction ls with
  | nil => simp
  | cons _ _ ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

theorem chain_links_length_le_rawChain (c : Chain) :
    c.links.length ≤ StateSize.rawChain c.intoPb := by
  have h := length_le_map_sum_add_200 c.intoPb.links
  have hlen : c.intoPb.links.length = c.links.length := by dsimp [Chain.intoPb]; simp
  unfold StateSize.rawChain; omega

theorem chainFrom_rawChain_le {F : ShaCompress} {K : MlKem}
    {stateBytes : Bytes} {pre_pb : PqRatchetState} {chain0 : Chain}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0) :
    StateSize.rawChain chain0.intoPb ≤ 201 * stateBytes.length + 296 := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hraw : StateSize.optRaw StateSize.rawVN (pqRatchetStateToPb pre_pb).versionNegotiation +
      StateSize.optRaw StateSize.rawChain pre_pb.chain +
      StateSize.optRaw StateSize.rawPqInner ((pqRatchetStateToPb pre_pb).inner.map PqRatchetState.Inner.v1) ≤
      201 * stateBytes.length := decodeState_spqrDeps_raw_le hd
  have hcf_raw := chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation hcf
  omega

theorem chainFrom_links_length_le {F : ShaCompress} {K : MlKem}
    {stateBytes : Bytes} {pre_pb : PqRatchetState} {chain0 : Chain} (hst_len : stateBytes.length < 2 ^ 32)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0) :
    chain0.links.length ≤ 2 ^ 54 := by
  have hraw := chainFrom_rawChain_le (F := F) (K := K) hdec hcf
  have hlen := chain_links_length_le_rawChain chain0
  omega

theorem recvPrevFits_of_rawChain_le {stateBytes : Bytes} {c : Chain} (hlen : stateBytes.length < 2 ^ 32)
    (hchain_le : StateSize.rawChain c.intoPb ≤ 201 * stateBytes.length + 600) :
    ChainProofs.RecvPrevFits c := by
  intro link hlink
  have hmem_into : ({ send := some link.send.intoPb, recv := some link.recv.intoPb } : ChainEpochPB) ∈ c.intoPb.links :=
    List.mem_map.mpr ⟨link, hlink, rfl⟩
  have hmem_map : StateSize.rawChainEpoch { send := some link.send.intoPb, recv := some link.recv.intoPb } + 200 ∈
      c.intoPb.links.map (fun ep => StateSize.rawChainEpoch ep + 200) := List.mem_map.mpr ⟨_, hmem_into, rfl⟩
  have hle_sum := List.le_sum_of_mem hmem_map
  have hprev_le : link.recv.prev.data.length ≤
      StateSize.rawChainEpoch { send := some link.send.intoPb, recv := some link.recv.intoPb } + 200 := by
    dsimp only [StateSize.rawChainEpoch, StateSize.optRaw, ChainEpochDirection.intoPb, StateSize.rawEpochDir]; omega
  unfold StateSize.rawChain at hchain_le; omega

/-- Helper: running the `v.key` step (`match v.key with | some k => chain0.addEpoch ... | none
    => .ok chain0`) produces `.ok chain1`. -/
def v1ChainAfterKey (hkdf : HkdfFn) (chain0 : Chain) (key : Option EpochSecret) : Except ChainPanic Chain :=
  match key with | some k => chain0.addEpoch hkdf k | none => .ok chain0

theorem recvPrevFits_of_v1ChainAfterKey {F : ShaCompress} {K : MlKem}
    {stateBytes : Bytes} {pre_pb : PqRatchetState} {chain0 chain1 : Chain} {key : Option EpochSecret}
    (hst_len : stateBytes.length < 2 ^ 32) (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hkey : v1ChainAfterKey (spqrHkdfWith F) chain0 key = .ok chain1) :
    ChainProofs.RecvPrevFits chain1 := by
  have hc0 := chainFrom_rawChain_le (F := F) (K := K) hdec hcf
  apply recvPrevFits_of_rawChain_le hst_len
  cases key with
  | none => dsimp [v1ChainAfterKey] at hkey; injection hkey with h; subst h; omega
  | some es =>
    dsimp [v1ChainAfterKey] at hkey; have hadd := Chain.addEpoch_raw_le (spqrHkdfWith F) chain0 es hkey; omega

theorem chainAt_extract_links_len_or_grow_ok (A : RustAlloc) (ptr : BitVec 64)
    (G0 : ChainProofs.ChainGhost) (chain0 : Chain) (hlen54 : chain0.links.length ≤ 2 ^ 54) :
    ChainProofs.chainAt A ptr G0 chain0 ⊢
      ⌜chain0.links.length < G0.linksCap.toNat ∨ max (2 * G0.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63⌝ ∗
      ChainProofs.chainAt A ptr G0 chain0 := by
  let P_ring : Prop := G0.linksPtr ≠ 0 ∧ (G0.epochs.zip chain0.links).length ≤ G0.linksCap.toNat ∧
    chainEpochSize * G0.linksCap.toNat < 2 ^ 63 ∧
    if G0.linksCap = 0 then G0.linksHead = 0 else G0.linksHead.toNat < G0.linksCap.toNat
  have hpull : ChainProofs.chainAt A ptr G0 chain0 = ⌜G0.epochs.length = chain0.links.length⌝ ∗ ⌜P_ring⌝ ∗
      ((vecDequeHeader ptr G0.linksCap G0.linksPtr G0.linksHead
          (BitVec.ofNat 64 (G0.epochs.zip chain0.links).length) ∗
        if G0.linksCap = 0 then emp
        else A.live G0.linksPtr (G0.linksCap.toNat * chainEpochSize) chainEpochAlign ∗
          vecDequeSlotsAt (chainEpochAt A) chainEpochSize G0.linksCap.toNat G0.linksHead.toNat
            G0.linksPtr (G0.epochs.zip chain0.links) 0 G0.linksCap.toNat) ∗
      vecU8At A (ptr + 0x20#64) G0.nextRoot.cap G0.nextRoot.ptr chain0.nextRoot ∗
      (ptr + 0x38#64) ↦₆₄ chain0.currentEpoch ∗ (ptr + 0x40#64) ↦₆₄ chain0.sendEpoch ∗
      chainParamsAt (ptr + 0x48#64) chain0.params ∗ directionAt (ptr + 0x50#64) chain0.dir ∗
      memRegion (ptr + 0x54#64) 4) := by
    unfold ChainProofs.chainAt vecDequeAt vecDequeRingBuf; dsimp only [P_ring]; ac_rfl
  conv_lhs => rw [hpull]
  apply Entails.pure_left; intro hlen_eq; apply Entails.pure_left; intro hring
  have hzip : (G0.epochs.zip chain0.links).length = chain0.links.length := by simp [hlen_eq]
  have hle : chain0.links.length ≤ G0.linksCap.toNat := by rw [← hzip]; exact hring.2.1
  have hgrow : chain0.links.length < G0.linksCap.toNat ∨
      max (2 * G0.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63 := by unfold chainEpochSize; omega
  apply Entails.pure_right hgrow; conv_rhs => rw [hpull]
  exact Entails.pure_right hlen_eq (Entails.pure_right hring (Entails.refl _))

theorem spqrV1Recv_v1_addEpoch_panic {F : ShaCompress} {K : MlKem} {stateBytes msgBytes : Bytes}
    {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)} {chain0 : Chain} {es : EpochSecret}
    (hpre : msgPreamble msgBytes = .ok pre) (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb)) (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hv_key : v.key = some es) (hpan : (chain0.addEpoch (spqrHkdfWith F) es).isOk = false) :
    (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have heq := recv_v1_after_statesRecv_eq hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0
  rw [hcf, hv_key] at heq; dsimp only [SpqrApiResult.ofError, Bind.bind, Except.bind] at heq
  cases hadd : chain0.addEpoch (spqrHkdfWith F) es with
  | ok _ => rw [hadd] at hpan; contradiction
  | error p => rw [hadd] at heq; exact spqrV1Recv_recvPanics_of_panic heq

theorem onPanic_of_v1_chainAddEpoch {F : ShaCompress} {K : MlKem} {st msg : VecArg}
    {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)} {chain0 : Chain} {es : EpochSecret}
    (hpre : msgPreamble msg.bytes = .ok pre) (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb)) (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hv_key : v.key = some es) (s sm : State) :
    (⌜((Chain.addEpoch (spqrHkdfWith F) chain0 es).isOk = false ∧ sm.trace = s.trace) ∨
        (allocFailedIn s sm ∧ s.trace <+: sm.trace)⌝ ∗ anyHeap : SepProp) ⊢
      ⌜(allocFailedIn s sm ∨ (spqrV1Recv F K).recvPanics st.bytes msg.bytes) ∧ s.trace <+: sm.trace⌝ ∗ anyHeap := by
  apply Entails.pure_left; rintro (⟨hpan, htr⟩ | ⟨haf, hsub⟩)
  · exact Entails.pure_right ⟨Or.inr (spqrV1Recv_v1_addEpoch_panic hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hv_key hpan), htr ▸ List.prefix_refl _⟩ (Entails.refl _)
  · exact Entails.pure_right ⟨Or.inl haf, hsub⟩ (Entails.refl _)

theorem spqrV1Recv_v1_recvKey_panic {F : ShaCompress} {K : MlKem} {stateBytes msgBytes : Bytes}
    {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)} {chain0 chain1 : Chain}
    (hpre : msgPreamble msgBytes = .ok pre) (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb)) (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hkey : v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1)
    (hrk : (chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index).isPanic = true) :
    (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have heq := recv_v1_after_statesRecv_eq hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0
  rw [hcf] at heq; dsimp only [SpqrApiResult.ofError, Bind.bind, Except.bind] at heq
  cases hvk : v.key with
  | none =>
    rw [hvk] at hkey heq; dsimp [v1ChainAfterKey] at hkey; injection hkey with h; subst h
    dsimp only [Pure.pure, Except.pure, Bind.bind, Except.bind] at heq
    cases hres : chain0.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
    | ok _ => rw [hres] at hrk; contradiction
    | error ce => cases ce with
      | err _ => rw [hres] at hrk; contradiction
      | panic _ => rw [hres] at heq; exact spqrV1Recv_recvPanics_of_panic heq
  | some es =>
    rw [hvk] at hkey heq; dsimp [v1ChainAfterKey] at hkey heq; rw [hkey] at heq
    dsimp only [SpqrApiResult.ofChainPanic, Bind.bind, Except.bind] at heq
    cases hres : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
    | ok _ => rw [hres] at hrk; contradiction
    | error ce => cases ce with
      | err _ => rw [hres] at hrk; contradiction
      | panic _ => rw [hres] at heq; exact spqrV1Recv_recvPanics_of_panic heq

theorem onPanic_of_v1_chainRecvKey {F : ShaCompress} {K : MlKem} {st msg : VecArg}
    {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)} {chain0 chain1 : Chain}
    (hpre : msgPreamble msg.bytes = .ok pre) (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb)) (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hkey : v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1) (s sm : State) :
    (⌜((Chain.recvKey (spqrHkdfWith F) chain1 (pre.epoch - 1#64) pre.index).isPanic = true ∧ sm.trace = s.trace) ∨
        (allocFailedIn s sm ∧ s.trace <+: sm.trace)⌝ ∗ anyHeap : SepProp) ⊢
      ⌜(allocFailedIn s sm ∨ (spqrV1Recv F K).recvPanics st.bytes msg.bytes) ∧ s.trace <+: sm.trace⌝ ∗ anyHeap := by
  apply Entails.pure_left; rintro (⟨hpan, htr⟩ | ⟨haf, hsub⟩)
  · exact Entails.pure_right ⟨Or.inr (spqrV1Recv_v1_recvKey_panic hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hkey hpan), htr ▸ List.prefix_refl _⟩ (Entails.refl _)
  · exact Entails.pure_right ⟨Or.inl haf, hsub⟩ (Entails.refl _)

/-! ## 2. `spqr::chain_from` Call & Error Branch (`+1856 .. +1884`) -/

theorem sp_writeVReg128_v1_r4 (s : State) (r : BitVec 5) (v : BitVec 128) : (s.writeVReg128 r v).sp = s.sp := rfl
theorem sp_setPState_v1_r4 (s : State) (p : PState) : (s.setPState p).sp = s.sp := rfl

theorem vnTail_entails_optVersionNegotiationRefAt (A : RustAlloc) (sp0 w0 w1 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (hsp4640_ne : sp0 - 4640#64 ≠ 0#64) :
    ((sp0 - 4640#64) ↦₆₄ w0) ∗ ((sp0 - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4624#64) optVn ⊢
    ∃∗ P_vn_keep : SepProp,
      ⌜ChainFrom.optVersionNegotiationRefAt A ⟨w0, w1⟩
          (if (w0 + 1#64 == 0#64) then 0#64 else sp0 - 4640#64) optVn ∗ P_vn_keep ⊢
        ((sp0 - 4640#64) ↦₆₄ w0) ∗ ((sp0 - 4632#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4624#64) optVn⌝ ∗
      ChainFrom.optVersionNegotiationRefAt A ⟨w0, w1⟩
        (if (w0 + 1#64 == 0#64) then 0#64 else sp0 - 4640#64) optVn ∗ P_vn_keep := by
  cases optVn with
  | none =>
    dsimp only [optVersionNegotiationPBTailAt]
    refine Entails.trans (Entails.of_eq (show
      ((sp0 - 4640#64) ↦₆₄ w0) ∗ ((sp0 - 4632#64) ↦₆₄ w1) ∗
        (⌜w0 = Top.ChainFromVersionNegotiation.noneCap⌝ ∗ memRegion (sp0 - 4624#64) 32) =
      ⌜w0 = Top.ChainFromVersionNegotiation.noneCap⌝ ∗
        (((sp0 - 4640#64) ↦₆₄ w0) ∗ ((sp0 - 4632#64) ↦₆₄ w1) ∗ memRegion (sp0 - 4624#64) 32) by ac_rfl)) ?_
    refine Entails.pure_left fun hw0 => ?_
    have hcond : (w0 + 1#64 == 0#64) = true := by subst hw0; rfl
    let P_keep := ((sp0 - 4640#64) ↦₆₄ w0) ∗ ((sp0 - 4632#64) ↦₆₄ w1) ∗
      (⌜w0 = Top.ChainFromVersionNegotiation.noneCap⌝ ∗ memRegion (sp0 - 4624#64) 32)
    refine Entails.sepExists_right P_keep (Entails.pure_right ?_ ?_)
    · rw [hcond]; simp only [↓reduceIte, ChainFrom.optVersionNegotiationRefAt]
      exact Entails.pure_left fun _ => Entails.of_eq (by dsimp only [P_keep]; ac_rfl)
    · rw [hcond]; simp only [↓reduceIte, ChainFrom.optVersionNegotiationRefAt]
      refine Entails.pure_right trivial ?_; dsimp only [P_keep]
      exact Entails.trans (Entails.pure_right hw0 (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some vn =>
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (optVersionNegotiationPBTailAt_some_cap_lt A w0 w1 (sp0 - 4624#64) vn))) ?_
    refine Entails.trans (Entails.of_eq (show
      ((sp0 - 4640#64) ↦₆₄ w0) ∗ ((sp0 - 4632#64) ↦₆₄ w1) ∗
        (⌜w0.toNat < 2 ^ 63⌝ ∗ optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4624#64) (some vn)) =
      ⌜w0.toNat < 2 ^ 63⌝ ∗ (((sp0 - 4640#64) ↦₆₄ w0) ∗ ((sp0 - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4624#64) (some vn)) by ac_rfl)) ?_
    refine Entails.pure_left fun hcap_lt => ?_
    have hcond : (w0 + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr (Drop.cap_add_one_beq_zero_false hcap_lt)
    have heq := vnTail_some_eq_versionNegotiationPBAt A (sp0 - 4640#64) w0 w1 vn
    have h8 : (sp0 - 4640#64) + 8#64 = sp0 - 4632#64 := bv_sub_add_lit sp0 4640 8
    have h16 : (sp0 - 4640#64) + 16#64 = sp0 - 4624#64 := bv_sub_add_lit sp0 4640 16
    rw [h8, h16] at heq
    refine Entails.sepExists_right emp (Entails.pure_right ?_ ?_)
    · rw [hcond, sepConj_emp]; simp only [Bool.false_eq_true, ↓reduceIte, ChainFrom.optVersionNegotiationRefAt]
      refine Entails.pure_left fun _ => ?_; rw [heq]; exact Entails.refl _
    · rw [hcond, sepConj_emp]; simp only [Bool.false_eq_true, ↓reduceIte, ChainFrom.optVersionNegotiationRefAt]
      refine Entails.pure_right hsp4640_ne ?_; rw [← heq]; exact Entails.of_eq (by ac_rfl)

theorem memRegion_3088_split_for_chainFrom (sp0 : BitVec 64) :
    memRegion (sp0 - 3088#64) 2992 ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        memRegion (sp0 - 3088#64) 32 ∗ memRegion (sp0 - 3056#64) 88 ∗ memRegion (sp0 - 2968#64) 872 ∗
        ((sp0 - 2096#64) ↦₆₄ d0) ∗ ((sp0 - 2088#64) ↦₆₄ d1) ∗ ((sp0 - 2080#64) ↦₆₄ d2) ∗
        memRegion (sp0 - 2072#64) 1976 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 3088#64) (n := 32) (k := 2960) (b' := sp0 - 3056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3056#64) (n := 88) (k := 2872) (b' := sp0 - 2968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2968#64) (n := 872) (k := 2000) (b' := sp0 - 2096#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2096#64) (n := 24) (k := 1976) (b' := sp0 - 2072#64) rfl (by bv_omega) (by decide),
      memRegion_24_words3 (sp0 - 2096#64), bv_sub_add_lit sp0 2096 8, bv_sub_add_lit sp0 2096 16]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun d2 => Entails.sepExists_elim fun d1 => Entails.sepExists_elim fun d0 => ?_
  exact Entails.sepExists_right d0 (Entails.sepExists_right d1 (Entails.sepExists_right d2 (Entails.refl _)))

theorem chainErrorAt_sub3056_entails_words4 (sp0 : BitVec 64) (err : Error) :
    Top.ChainFromVersionNegotiation.chainErrorAt (sp0 - 3056#64) err ⊢
      ∃∗ q0 : BitVec 128, ∃∗ w3 : BitVec 64,
        ⌜BitVec.truncate 8 q0 = Top.ChainFromVersionNegotiation.spqrErrorTag err⌝ ∗
        ((sp0 - 3056#64) ↦₆₄ Top.ChainFromVersionNegotiation.noneCap) ∗
        ((sp0 - 3048#64) ↦₆₄ q0.extractLsb' 0 64) ∗ ((sp0 - 3040#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((sp0 - 3032#64) ↦₆₄ w3) ∗ memRegion (sp0 - 3024#64) 56 := by
  unfold Top.ChainFromVersionNegotiation.chainErrorAt pointsTo128
  rw [show (sp0 - 3056#64) + 8#64 + 8#64 = (sp0 - 3056#64) + 16#64 by bv_omega,
      bv_sub_add_lit sp0 3056 8, bv_sub_add_lit sp0 3056 16,
      bv_sub_add_lit sp0 3056 24, bv_sub_add_lit sp0 3056 32]
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]; simp only [sepConj_assoc]; exact Entails.refl _

/-- Step `+1856 .. +1884` (`0x54d6c .. 0x54d88`): `spqr::chain_from` call and error branch
    (`+2568`). -/
theorem step_v1_chainFrom_1856 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (w0 w1 kw0 kw1 kw2 kw3 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) (P_key R : SepProp) (s0 s : State) (P : SepProp)
    (hs0_align : s0.spAligned = true) (hsp4640_ne : s0.sp - 4640#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1856#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 3056#64) (hx1 : s.readReg64 .x1 = s0.sp - 4592#64)
    (hx2 : s.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64))
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = w0) (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1) (hx26 : s.readReg64 .x26 = s0.sp - 1160#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      ProtoRepr.optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗ chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcont_err : ∀ (e : Error) (q0_err : BitVec 128) (w3_err : BitVec 64) (s1 : State) (P1 : SepProp),
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .error e →
      BitVec.truncate 8 q0_err = Top.ChainFromVersionNegotiation.spqrErrorTag e →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2568#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x8 = Top.ChainFromVersionNegotiation.noneCap → s1.readReg64 .x9 = w3_err →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 → s1.readReg64 .x25 = kw1 →
      s1.readReg64 .x26 = s0.sp - 1160#64 → s1.readReg64 .x27 = s0.sp - 3056#64 →
      s1.readReg64 .x28 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
        P_key ∗ chunkedStatesAt A (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ Top.ChainFromVersionNegotiation.noneCap) ∗
        ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗ ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 3024#64) 56 ∗ memRegion (s0.sp - 2968#64) 872 ∗
        ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗ ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 2072#64) 1976 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_ok : ∀ (chain0 : Chain) (G0 : ChainProofs.ChainGhost) (pad0 : BitVec 32) (s1 : State) (P1 : SepProp),
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      G0.linksCap ≠ Top.ChainFromVersionNegotiation.noneCap →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1888#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x8 = G0.linksCap → s1.readReg64 .x9 = (chainWords11 G0 chain0 pad0).w3 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 → s1.readReg64 .x25 = kw1 →
      s1.readReg64 .x26 = s0.sp - 1160#64 → s1.readReg64 .x27 = s0.sp - 3056#64 →
      s1.readReg64 .x28 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
        P_key ∗ chunkedStatesAt A (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        words11SubAt s0.sp 3056 (chainWords11 G0 chain0 pad0) ∗ chainAtHeap A G0 chain0 ∗
        memRegion (s0.sp - 2968#64) 872 ∗
        ((s0.sp - 2096#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w1) ∗
        ((s0.sp - 2088#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w2) ∗
        ((s0.sp - 2080#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w3) ∗
        memRegion (s0.sp - 2072#64) 1976 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hcf_ok := spqrRecv_chainFrom_ok hC
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hcf_ok hpc hcont_err hcont_ok ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1856 32
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  apply SepWPpI.of_sepWP (mid := entry + bv% (2 ^ 64 - ls_rel% "spqr::chain_from" "spqr::recv"))
  refine SepWP.focus_weaken
    (Entails.of_eq (optChainPBAt_protoRepr_eq_exists A (s0.sp - 4592#64) pre_pb.chain)) (by sep_focus) ?_
  wp_pull_exists; rename_i gPb
  refine SepWP.focus_weaken (memRegion_3088_split_for_chainFrom s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i d2096_0 d2096_1 d2096_2
  refine SepWP.focus_weaken
    (vnTail_entails_optVersionNegotiationRefAt A s0.sp w0 w1 pre_pb.versionNegotiation hsp4640_ne) (by sep_focus) ?_
  wp_pull_exists; rename_i P_vn_keep; wp_focus_pure; intro hfold_vn; wp_steps 1
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackX (by decide))) (by sep_focus) ?_
  refine SepWPpI.call_inImage hcf_ok
    (⟨s0.sp - 3056#64, s0.sp - 4592#64, if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64,
      gPb, ⟨w0, w1⟩, pre_pb.chain, pre_pb.versionNegotiation⟩ : ChainFromCall)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align) (rfl : _ = entry + 1860#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed) (fun _ _ => rfl)
    (by
      dsimp only [chainFromSpecX]
      refine frame_pure_pre ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128_v1_r4, sp_setPState_v1_r4, reduceCtorEq, ↓reduceIte, hsp]; sep_focus)) ?_
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hxfp_c, hvregs_c⟩
  dsimp only [chainFromSpecX]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = pre.epoch := by rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = kw0 := by rw [hx24_c]; simp only [arm64_norm, *]
  have hx25_sm : sm.readReg64 .x25 = kw1 := by rw [hx25_c]; simp only [arm64_norm, *]
  have hx26_sm : sm.readReg64 .x26 = s0.sp - 1160#64 := by rw [hx26_c]; simp only [arm64_norm, *]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c]; simp only [arm64_norm, *]
  have hx28_sm : sm.readReg64 .x28 = 0#64 := by rw [hx28_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; simp only [arm64_norm, *]
  have hsp_eq := congrArg (stackAt · chainFromStackX) (hspm.symm.trans hspm')
  refine SepWPpI.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  clear hsp_eq htr_sm hspm hx19_c hx20_c hx21_c hx22_c hx23_c hx24_c hx25_c hx26_c hx27_c hx28_c hxfp_c hvregs_c
  clear hpc hrun hsp htr hx0 hx1 hx2 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 s
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackX (by decide)).symm)
    (by sep_focus) ?_
  refine SepWPpI.focus_weaken hfold_vn (by sep_focus) ?_
  cases hcf_res : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation with
  | error e =>
    have hnone1 : (Top.ChainFromVersionNegotiation.noneCap + 1#64 == 0#64) = true := rfl
    apply SepWPpI.of_sepWP (mid := entry + 2568#64); dsimp only [chainResultAt]
    refine SepWP.focus_weaken (chainErrorAt_sub3056_entails_words4 s0.sp e) (by sep_focus) ?_
    wp_pull_exists; rename_i q0_err w3_err; wp_focus_pure; intro htag_q0
    wp_steps 7
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact hcont_err e q0_err w3_err _ _ hcf_res htag_q0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
  | ok chain0 =>
    apply SepWPpI.of_sepWP (mid := entry + 1888#64); dsimp only [chainResultAt]
    refine SepWP.focus_weaken (chainRepr_sub_entails_words11 A s0.sp 3056 chain0) (by sep_focus) ?_
    wp_pull_exists; rename_i G0 pad0; wp_focus_pure; intro hcap_ne
    have hc0 : (G0.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ne
    dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
    wp_steps 7
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact hcont_ok chain0 G0 pad0 _ _ hcf_res hcap_ne
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [chainWords11, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]; ac_rfl)

/-! ## 3. `Chain` Relocation & `<Chain>::add_epoch` (`+1888 .. +1976`) -/

@[local arm64_norm, local wp_norm]
theorem sp_sub_96_sub_56 (sp0 : BitVec 64) : (sp0 - 96#64) + 18446744073709551560#64 = sp0 - 152#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_sub_112 (sp0 : BitVec 64) : (sp0 - 96#64) + 18446744073709551504#64 = sp0 - 208#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_sub_128 (sp0 : BitVec 64) : (sp0 - 96#64) + 18446744073709551488#64 = sp0 - 224#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_sub_136_add (sp0 : BitVec 64) : (sp0 - 96#64) + 18446744073709551480#64 = sp0 - 232#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_sub_136_r4 (sp0 : BitVec 64) : (sp0 - 96#64) - 136#64 = sp0 - 232#64 := by bv_omega

theorem vecU8Buf_expose_len_lt_v1 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    RustHeap.vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ RustHeap.vecU8Buf A cap ptr bs := by
  unfold RustHeap.vecU8Buf
  exact Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

theorem optEpochSecret_some_entails_of_hfold_v1 (A : RustAlloc) (a kw0 kw1 kw2 kw3 : BitVec 64)
    (P_key : SepProp) (sec : EpochSecret)
    (hfold : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        States.Recv.optEpochSecretAt A dst (some sec)) :
    memRegion a 16 ∗ (((a + 16#64) ↦₆₄ kw2) ∗ ((a + 24#64) ↦₆₄ kw3) ∗ P_key) ⊢
      ⌜kw0.toNat < 2 ^ 63⌝ ∗ memRegion a 16 ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 sec.secret.length) ∗
      ((a + 24#64) ↦₆₄ sec.epoch) ∗ RustHeap.vecU8Buf A kw0 kw1 sec.secret := by
  have hQ : ∀ p : BitVec 64 × BitVec 64,
      IsBlock ((a ↦₆₄ p.1) ∗ ((a + 8#64) ↦₆₄ p.2)) a 16 (fun m => m.read64 a = p.1 ∧ m.read64 (a + 8#64) = p.2) :=
    fun p => (IsBlock.pointsTo64 a p.1).sepConj (IsBlock.pointsTo64 (a + 8#64) p.2) rfl (by decide)
  have hent : ((a ↦₆₄ kw0) ∗ ((a + 8#64) ↦₆₄ kw1)) ∗ (((a + 16#64) ↦₆₄ kw2) ∗ ((a + 24#64) ↦₆₄ kw3) ∗ P_key) ⊢
      ∃∗ p : BitVec 64 × BitVec 64, ((a ↦₆₄ p.1) ∗ ((a + 8#64) ↦₆₄ p.2)) ∗
        (⌜p.1.toNat < 2 ^ 63⌝ ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 sec.secret.length) ∗
          ((a + 24#64) ↦₆₄ sec.epoch) ∗ RustHeap.vecU8Buf A p.1 p.2 sec.secret) := by
    refine Entails.trans (Entails.of_eq (by simp only [sepConj_assoc])) (Entails.trans (hfold a) ?_)
    dsimp only [States.Recv.optEpochSecretAt, States.RecvCt2Chunk.epochSecretAt, vecU8]
    rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun cap => ?_
    rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun ptr => ?_
    rw [RustHeap.vecU8At_eq_header_sep_buf A a cap ptr sec.secret]; dsimp only [RustHeap.vecHeader]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (vecU8Buf_expose_len_lt_v1 A cap ptr sec.secret))) ?_
    refine Entails.trans (Entails.of_eq (show
      (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 sec.secret.length)) ∗
        (⌜cap.toNat < 2 ^ 63⌝ ∗ RustHeap.vecU8Buf A cap ptr sec.secret)) ∗ ((a + 24#64) ↦₆₄ sec.epoch) =
      ⌜cap.toNat < 2 ^ 63⌝ ∗ (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr)) ∗
        (((a + 16#64) ↦₆₄ BitVec.ofNat 64 sec.secret.length) ∗ ((a + 24#64) ↦₆₄ sec.epoch) ∗
          RustHeap.vecU8Buf A cap ptr sec.secret)) by ac_rfl)) ?_
    refine Entails.pure_left fun hcap_lt => Entails.sepExists_right (cap, ptr) ?_
    exact sepConj_mono_right (Entails.pure_right hcap_lt (Entails.refl _))
  refine Entails.trans (memRegion16_replace_pointsTo64_pair hQ hent) ?_
  refine Entails.sepExists_elim fun ⟨cap, ptr⟩ => Entails.pure_left fun ⟨m, hm0, hm1, hmc, hmp⟩ => ?_
  have hcap : cap = kw0 := hmc.symm.trans hm0; have hptr : ptr = kw1 := hmp.symm.trans hm1; subst hcap hptr
  rw [sepConj_pure_left_comm]; exact Entails.pure_left fun hcap_lt => Entails.pure_right hcap_lt (Entails.of_eq (by ac_rfl))

@[local arm64_norm, local wp_norm]
theorem sp_sub_1160_add_960 (sp0 : BitVec 64) : (sp0 - 1160#64) + 960#64 = sp0 - 200#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_1160_add_992 (sp0 : BitVec 64) : (sp0 - 1160#64) + 992#64 = sp0 - 168#64 := by bv_omega

theorem memRegion_1976_split_for_1888 (sp0 : BitVec 64) :
    memRegion (sp0 - 2072#64) 1976 ⊢
      ∃∗ u232 : Words11, memRegion (sp0 - 2072#64) 1840 ∗ words11SubAt sp0 232 u232 ∗ memRegion (sp0 - 144#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 2072#64) (n := 1840) (k := 136) (b' := sp0 - 232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 232#64) (n := 88) (k := 48) (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (memRegion_88_sub_entails_words11 sp0 232))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; exact Entails.refl _

theorem memRegion_2792_join_after_reloc (sp0 w4 w5 w6 w7 w8 w9 w10 d0 d1 d2 : BitVec 64) :
    ((sp0 - 3024#64) ↦₆₄ w4) ∗ ((sp0 - 3016#64) ↦₆₄ w5) ∗ ((sp0 - 3008#64) ↦₆₄ w6) ∗ ((sp0 - 3000#64) ↦₆₄ w7) ∗
      ((sp0 - 2992#64) ↦₆₄ w8) ∗ ((sp0 - 2984#64) ↦₆₄ w9) ∗ ((sp0 - 2976#64) ↦₆₄ w10) ∗
      memRegion (sp0 - 2968#64) 872 ∗
      ((sp0 - 2096#64) ↦₆₄ d0) ∗ ((sp0 - 2088#64) ↦₆₄ d1) ∗ ((sp0 - 2080#64) ↦₆₄ d2) ∗
      memRegion (sp0 - 2072#64) 1840 ⊢
    memRegion (sp0 - 3024#64) 2792 := by
  have h56 : ((sp0 - 3024#64) ↦₆₄ w4) ∗ ((sp0 - 3016#64) ↦₆₄ w5) ∗ ((sp0 - 3008#64) ↦₆₄ w6) ∗
      ((sp0 - 3000#64) ↦₆₄ w7) ∗ ((sp0 - 2992#64) ↦₆₄ w8) ∗ ((sp0 - 2984#64) ↦₆₄ w9) ∗
      ((sp0 - 2976#64) ↦₆₄ w10) ⊢ memRegion (sp0 - 3024#64) 56 := by
    rw [ProofLib.memRegion_split' (b := sp0 - 3024#64) (n := 24) (k := 32) (b' := sp0 - 3000#64) rfl (by bv_omega) (by decide),
        ← sepConj_assoc, ← sepConj_assoc]
    refine sepConj_mono ?_ ?_
    · have h := words3_to_memRegion_24 (sp0 - 3024#64) w4 w5 w6
      rw [bv_sub_add_lit sp0 3024 8, bv_sub_add_lit sp0 3024 16] at h
      dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h; simpa only [sepConj_assoc] using h
    · have h := words4_to_memRegion_32 (sp0 - 3000#64) w7 w8 w9 w10
      rw [bv_sub_add_lit sp0 3000 8, bv_sub_add_lit sp0 3000 16, bv_sub_add_lit sp0 3000 24] at h
      dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h; exact h
  have h24 : ((sp0 - 2096#64) ↦₆₄ d0) ∗ ((sp0 - 2088#64) ↦₆₄ d1) ∗ ((sp0 - 2080#64) ↦₆₄ d2) ⊢
      memRegion (sp0 - 2096#64) 24 := by
    have h := words3_to_memRegion_24 (sp0 - 2096#64) d0 d1 d2
    rw [bv_sub_add_lit sp0 2096 8, bv_sub_add_lit sp0 2096 16] at h
    dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h; exact h
  rw [ProofLib.memRegion_split' (b := sp0 - 3024#64) (n := 56) (k := 2736) (b' := sp0 - 2968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2968#64) (n := 872) (k := 1864) (b' := sp0 - 2096#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2096#64) (n := 24) (k := 1840) (b' := sp0 - 2072#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show
    ((sp0 - 3024#64) ↦₆₄ w4) ∗ ((sp0 - 3016#64) ↦₆₄ w5) ∗ ((sp0 - 3008#64) ↦₆₄ w6) ∗ ((sp0 - 3000#64) ↦₆₄ w7) ∗
      ((sp0 - 2992#64) ↦₆₄ w8) ∗ ((sp0 - 2984#64) ↦₆₄ w9) ∗ ((sp0 - 2976#64) ↦₆₄ w10) ∗
      memRegion (sp0 - 2968#64) 872 ∗
      ((sp0 - 2096#64) ↦₆₄ d0) ∗ ((sp0 - 2088#64) ↦₆₄ d1) ∗ ((sp0 - 2080#64) ↦₆₄ d2) ∗
      memRegion (sp0 - 2072#64) 1840 =
    (((sp0 - 3024#64) ↦₆₄ w4) ∗ ((sp0 - 3016#64) ↦₆₄ w5) ∗ ((sp0 - 3008#64) ↦₆₄ w6) ∗ ((sp0 - 3000#64) ↦₆₄ w7) ∗
      ((sp0 - 2992#64) ↦₆₄ w8) ∗ ((sp0 - 2984#64) ↦₆₄ w9) ∗ ((sp0 - 2976#64) ↦₆₄ w10)) ∗
    memRegion (sp0 - 2968#64) 872 ∗
    (((sp0 - 2096#64) ↦₆₄ d0) ∗ ((sp0 - 2088#64) ↦₆₄ d1) ∗ ((sp0 - 2080#64) ↦₆₄ d2)) ∗
    memRegion (sp0 - 2072#64) 1840 by ac_rfl)) ?_
  exact sepConj_mono h56 (sepConj_mono_right (sepConj_mono_left h24))

theorem epochSecretAt_sub3056_fold (A : RustAlloc) (sp0 kw0 kw1 : BitVec 64) (es : EpochSecret) :
    ((sp0 - 3056#64) ↦₆₄ kw0) ∗ ((sp0 - 3048#64) ↦₆₄ kw1) ∗
      ((sp0 - 3040#64) ↦₆₄ BitVec.ofNat 64 es.secret.length) ∗ ((sp0 - 3032#64) ↦₆₄ es.epoch) ∗
      RustHeap.vecU8Buf A kw0 kw1 es.secret ⊢
    ChainProofs.epochSecretAt A (sp0 - 3056#64) ⟨kw0, kw1⟩ es := by
  unfold ChainProofs.epochSecretAt
  rw [RustHeap.vecU8At_eq_header_sep_buf A (sp0 - 3056#64) kw0 kw1 es.secret]; dsimp only [RustHeap.vecHeader]
  rw [bv_sub_add_lit sp0 3056 8, bv_sub_add_lit sp0 3056 16, show (sp0 - 3056#64) + 0x18#64 = sp0 - 3032#64 by bv_omega]
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl)

theorem memRegion_4064_join_some (sp0 w0 w1 : BitVec 64) :
    memRegion (sp0 - 4064#64) 16 ∗ memRegion (sp0 - 4048#64) 16 ∗
      ((sp0 - 4032#64) ↦₆₄ w0) ∗ ((sp0 - 4024#64) ↦₆₄ w1) ⊢ memRegion (sp0 - 4064#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 4064#64) (n := 16) (k := 32) (b' := sp0 - 4048#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4048#64) (n := 16) (k := 16) (b' := sp0 - 4032#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4032#64) (n := 8) (k := 8) (b' := sp0 - 4024#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (ProofLib.pointsTo64_entails_memRegion _ _)))

theorem words4_sub3056_to_memRegion_32 (sp0 w0 w1 w2 w3 : BitVec 64) :
    ((sp0 - 3056#64) ↦₆₄ w0) ∗ ((sp0 - 3048#64) ↦₆₄ w1) ∗ ((sp0 - 3040#64) ↦₆₄ w2) ∗ ((sp0 - 3032#64) ↦₆₄ w3) ⊢
    memRegion (sp0 - 3056#64) 32 := by
  have h := words4_to_memRegion_32 (sp0 - 3056#64) w0 w1 w2 w3
  rw [bv_sub_add_lit sp0 3056 8, bv_sub_add_lit sp0 3056 16, bv_sub_add_lit sp0 3056 24] at h
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h; exact h

theorem memRegion_4064_join_none (sp0 : BitVec 64) :
    memRegion (sp0 - 4064#64) 16 ∗ memRegion (sp0 - 4048#64) 32 ⊢ memRegion (sp0 - 4064#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 4064#64) (n := 16) (k := 32) (b' := sp0 - 4048#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem SepWPpI.exists_left {α : Type} {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} (hrun : s.status = .Running) {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (hwp : ∀ x, SepWPpI img prog ret s (P x) Q Qp) :
    SepWPpI img prog ret s (∃∗ x, P x) Q Qp := by
  apply SepWPpI.of_sepWP (mid := s.pc); wp_pull_exists; exact ProofLib.SepWP.done rfl hrun (hwp _)

/-- Step `+1888 .. +1976` (`0x54d8c .. 0x54de4`): relocates `chain0` (88 bytes) from `s0.sp -
    3056#64` to `s0.sp - 232#64` (`x29 - 136`), computes `x22 := pre.epoch - 1#64`, checks
    `v.key : Option EpochSecret`, and if `v.key = some es`, calls `<Chain>::add_epoch`
    (`+1972`), unifying at `+1976`. -/
theorem step_v1_chain_reloc_and_addEpoch_1888 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 kw0 kw1 kw2 kw3 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (v : V1Recv spqrPolyApi (spqrAuthApi F)) (P_key R : SepProp)
    (chain0 : Chain) (G0 : ChainProofs.ChainGhost) (pad0 : BitVec 32) (s0 s : State) (P : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32) (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb) (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8) (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        States.Recv.optEpochSecretAt A dst v.key)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1888#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = G0.linksCap) (hx9 : s.readReg64 .x9 = (chainWords11 G0 chain0 pad0).w3)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = w0) (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1) (hx26 : s.readReg64 .x26 = s0.sp - 1160#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗ chunkedStatesAt A (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
      words11SubAt s0.sp 3056 (chainWords11 G0 chain0 pad0) ∗ chainAtHeap A G0 chain0 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      ((s0.sp - 2096#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w1) ∗
      ((s0.sp - 2088#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w2) ∗
      ((s0.sp - 2080#64) ↦₆₄ (chainWords11 G0 chain0 pad0).w3) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcont_1976 : ∀ (chain1 : Chain) (G1 : ChainProofs.ChainGhost) (s1 : State) (P1 : SepProp),
      v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1976#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch - 1#64 →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x28 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        memRegion (s0.sp - 3056#64) 32 ∗ memRegion (s0.sp - 3024#64) 2792 ∗
        ChainProofs.chainAt A (s0.sp - 232#64) G1 chain1 ∗ memRegion (s0.sp - 144#64) 48 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hadd_ok := spqrRecv_chainAddEpoch_ok hC
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  have hfp : s.readReg64 .fp = s0.sp - 96#64 := hx29
  dsimp only [chainWords11] at hx9
  have hlen54 : chain0.links.length ≤ 2 ^ 54 := chainFrom_links_length_le (F := F) (K := K) hst_len hdec hcf
  have hchainAt_232 := words11SubAt_entails_chainAt A s0.sp 232 G0 chain0 pad0
  subst hP
  rw [ProofLib.memRegion_split' (b := s0.sp - 4064#64) (n := 16) (k := 16) (b' := s0.sp - 4048#64) rfl (by bv_omega) (by decide)]
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hadd_ok hpc hcont_1976 ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1888 88
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  cases hvk : v.key with
  | none =>
    have hfold_none : ∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          States.Recv.optEpochSecretAt A dst none := fun dst => hvk ▸ hfold_key dst
    have hent_none := optEpochSecret_none_entails_of_hfold A (s0.sp - 4048#64) kw0 kw1 kw2 kw3 P_key hfold_none
    rw [bv_sub_add_lit s0.sp 4048 16, bv_sub_add_lit s0.sp 4048 24] at hent_none
    dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hent_none
    refine SepWPpI.focus_weaken hent_none (by sep_focus) ?_
    refine SepWPpI.focus_pure (by sep_focus) ?_; intro hkw0
    have hkw0_beq : (kw0 + 1#64 == 0#64) = true := by subst hkw0; rfl
    refine SepWPpI.focus_weaken (memRegion_4064_join_none s0.sp) (by sep_focus) ?_
    apply SepWPpI.of_sepWP (mid := entry + 1976#64)
    refine SepWP.focus_weaken (memRegion_1976_split_for_1888 s0.sp) (by sep_focus) ?_
    wp_pull_exists; rename_i u232
    dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hchainAt_232 ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit, Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepConj_assoc]
    wp_steps 15
    refine SepWP.focus_weaken hchainAt_232 (by sep_focus) ?_
    refine SepWP.focus_weaken (words4_sub3056_to_memRegion_32 s0.sp G0.linksCap G0.linksPtr G0.linksHead
      (BitVec.ofNat 64 (G0.epochs.zip chain0.links).length)) (by sep_focus) ?_
    refine SepWP.focus_weaken (memRegion_2792_join_after_reloc s0.sp
      G0.nextRoot.cap G0.nextRoot.ptr (BitVec.ofNat 64 chain0.nextRoot.length)
      chain0.currentEpoch chain0.sendEpoch (chain0.params.maxOooKeys ++ chain0.params.maxJump)
      (pad0 ++ chain0.dir.toI32) G0.linksPtr G0.linksHead
      (BitVec.ofNat 64 (G0.epochs.zip chain0.links).length)) (by sep_focus) ?_
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact hcont_1976 chain0 G0 _ _ (by simp [v1ChainAfterKey, hvk])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
  | some es =>
    have hfold_some : ∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          States.Recv.optEpochSecretAt A dst (some es) := fun dst => hvk ▸ hfold_key dst
    have hent_some := optEpochSecret_some_entails_of_hfold_v1 A (s0.sp - 4048#64) kw0 kw1 kw2 kw3 P_key es hfold_some
    rw [bv_sub_add_lit s0.sp 4048 16, bv_sub_add_lit s0.sp 4048 24] at hent_some
    dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hent_some
    refine SepWPpI.focus_weaken hent_some (by sep_focus) ?_
    refine SepWPpI.focus_pure (by sep_focus) ?_; intro hkw0_lt
    have hkw0_beq : (kw0 + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr (Drop.cap_add_one_beq_zero_false hkw0_lt)
    apply SepWPpI.of_sepWP (mid := entry + bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::add_epoch"))
    refine SepWP.focus_weaken (memRegion_1976_split_for_1888 s0.sp) (by sep_focus) ?_
    wp_pull_exists; rename_i u232
    dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hchainAt_232 ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit, Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepConj_assoc]
    wp_steps 22
    refine SepWP.focus_weaken hchainAt_232 (by sep_focus) ?_
    refine SepWP.focus_weaken (chainAt_extract_links_len_or_grow_ok A (s0.sp - 232#64) G0 chain0 hlen54) (by sep_focus) ?_
    wp_focus_pure; intro hgrow
    refine SepWP.focus_weaken (epochSecretAt_sub3056_fold A s0.sp kw0 kw1 es) (by sep_focus) ?_
    refine SepWP.focus_weaken (memRegion_4064_join_some s0.sp (BitVec.ofNat 64 es.secret.length) es.epoch) (by sep_focus) ?_
    refine SepWP.focus_weaken (memRegion_2792_join_after_reloc s0.sp
      G0.nextRoot.cap G0.nextRoot.ptr (BitVec.ofNat 64 chain0.nextRoot.length)
      chain0.currentEpoch chain0.sendEpoch (chain0.params.maxOooKeys ++ chain0.params.maxJump)
      (pad0 ++ chain0.dir.toI32) G0.linksPtr G0.linksHead
      (BitVec.ofNat 64 (G0.epochs.zip chain0.links).length)) (by sep_focus) ?_
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpI.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainAddEpochStackX (by decide))) (by sep_focus) ?_
    refine SepWPpI.call_inImage hadd_ok
      (⟨s0.sp - 232#64, s0.sp - 3056#64, G0, ⟨kw0, kw1⟩, chain0, es⟩ : ChainAddEpochGhost)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align) (rfl : _ = entry + 1976#64)
      (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
      (fun sm => by
        dsimp only [chainAddEpochSpecX]
        have hpan := onPanic_of_v1_chainAddEpoch hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hvk s0 sm
        simpa only [State.trace_setPC, State.trace_setMem, State.trace_writeReg64,
          State.trace_writeVReg128, State.trace_setPState, allocFailedIn, htr] using hpan)
      (fun _ _ => rfl)
      (by
        dsimp only [chainAddEpochSpecX]
        refine frame_pure_pre ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], hgrow⟩
          (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
              sp_writeVReg128_v1_r4, sp_setPState_v1_r4, reduceCtorEq, ↓reduceIte, hsp]; sep_focus)) ?_
    intro sm hpcm hrunm hspm hcsm
    rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, hx23_c, _, _, _, _, hx28_c, hxfp_c, hvregs_c⟩
    dsimp only [chainAddEpochSpecX]
    have hspm' : sm.sp = s0.sp - 4992#64 := by
      rw [hspm]; simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
        sp_writeVReg128_v1_r4, sp_setPState_v1_r4, reduceCtorEq, ↓reduceIte, arm64_norm, *]
    have hsp_eq := congrArg (stackAt · chainAddEpochStackX) (hspm.symm.trans hspm')
    cases hadd_res : Chain.addEpoch (spqrHkdfWith F) chain0 es with
    | error _ => dsimp only; exact SepWPpI.focus_pure (by sep_focus) False.elim
    | ok chain1 =>
      dsimp only
      refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
      have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
      have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
      have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
      have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c]; simp only [arm64_norm, *]
      have hx22_sm : sm.readReg64 .x22 = pre.epoch - 1#64 := by rw [hx22_c]; simp only [arm64_norm, *]
      have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c]; simp only [arm64_norm, *]
      have hx28_sm : sm.readReg64 .x28 = 0#64 := by rw [hx28_c]; simp only [arm64_norm, *]
      have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
        change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; simp only [arm64_norm, *]
      refine SepWPpI.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
      refine SepWPpI.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainAddEpochStackX (by decide)).symm)
        (by sep_focus) ?_
      unfold ChainProofs.chainRepr; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPpI.exists_left hrunm; intro G1
      exact hcont_1976 chain1 G1 sm _ (by simp [v1ChainAfterKey, hvk, hadd_res])
        hpcm hrunm hspm' htr_sm' hx19_sm hx20_sm hx21_sm hx22_sm hx23_sm hx28_sm hx29_sm (by ac_rfl)

/-! ## 4. `<Chain>::recv_key` Call & Dispatch (`+1976 .. +2024`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem setWidth32_zeroExtend64 (idx : BitVec 32) :
    BitVec.setWidth 32 (BitVec.zeroExtend 64 idx) = idx := by bv_omega

theorem recvKeyOkAt_sub3056_expose (A : RustAlloc) (sp0 : BitVec 64) (rawKey : Bytes) :
    recvKeyOkAt A (sp0 - 3056#64) rawKey ⊢
      ∃∗ cap_rk : BitVec 64, ∃∗ ptr_rk : BitVec 64,
        ((sp0 - 3056#64) ↦₆₄ 0#64) ∗ ((sp0 - 3048#64) ↦₆₄ cap_rk) ∗ ((sp0 - 3040#64) ↦₆₄ ptr_rk) ∗
        ((sp0 - 3032#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗ RustHeap.vecU8Buf A cap_rk ptr_rk rawKey := by
  unfold recvKeyOkAt vecU8; rw [bv_sub_add_lit sp0 3056 8]; dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  rw [sepExists_sepConj_right]; refine Entails.sepExists_elim fun cap_rk => ?_
  rw [sepExists_sepConj_right]; refine Entails.sepExists_elim fun ptr_rk => ?_
  rw [RustHeap.vecU8At_eq_header_sep_buf A (sp0 - 3048#64) cap_rk ptr_rk rawKey]; dsimp only [RustHeap.vecHeader]
  rw [bv_sub_add_lit sp0 3048 8, bv_sub_add_lit sp0 3048 16]; dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  exact Entails.sepExists_right cap_rk (Entails.sepExists_right ptr_rk (Entails.of_eq (by ac_rfl)))

theorem memRegion_576_join_v1_ok (sp0 : BitVec 64) (sckaMsg : Message spqrPolyApi) :
    memRegion (sp0 - 4592#64) 80 ∗ memRegion (sp0 - 4512#64) 224 ∗ memRegion (sp0 - 4288#64) 176 ∗
      MessageSerialize.messageAt spqrPolyApi (sp0 - 4112#64) sckaMsg ∗ memRegion (sp0 - 4064#64) 48 ⊢
    memRegion (sp0 - 4592#64) 576 := by
  have hmsg := messageAt_entails_memRegion_48 (sp0 - 4112#64) sckaMsg
  rw [ProofLib.memRegion_split' (b := sp0 - 4592#64) (n := 80) (k := 496) (b' := sp0 - 4512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4512#64) (n := 224) (k := 272) (b' := sp0 - 4288#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4288#64) (n := 176) (k := 96) (b' := sp0 - 4112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4112#64) (n := 48) (k := 48) (b' := sp0 - 4064#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmsg)))

theorem memRegion_2856_join_v1_ok (sp0 w0 w1 w2 w3 : BitVec 64) :
    memRegion (sp0 - 3088#64) 32 ∗
      (((sp0 - 3056#64) ↦₆₄ w0) ∗ ((sp0 - 3048#64) ↦₆₄ w1) ∗ ((sp0 - 3040#64) ↦₆₄ w2) ∗ ((sp0 - 3032#64) ↦₆₄ w3)) ∗
      memRegion (sp0 - 3024#64) 2792 ⊢ memRegion (sp0 - 3088#64) 2856 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 3088#64) (n := 32) (k := 2824) (b' := sp0 - 3056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3056#64) (n := 32) (k := 2792) (b' := sp0 - 3024#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_left (words4_sub3056_to_memRegion_32 sp0 w0 w1 w2 w3))

/-- Step `+1976 .. +2024` (`0x54de4 .. 0x54e14`): calls `<Chain>::recv_key` at `+1996`, loads
    the 4-word `Result` from `s0.sp - 3056#64`, sets `x26 := 0#64`, and branches at `+2024`
    (`b.ne +2664` on `Ok`, fallthrough `+2028` on `Err`). -/
theorem step_v1_chainRecvKey_1976 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) (R : SepProp)
    (chain0 chain1 : Chain) (G1 : ChainProofs.ChainGhost) (s0 s : State) (P : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32) (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb) (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8) (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hkey : v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1) (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1976#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch - 1#64)
    (hx23 : s.readReg64 .x23 = w0) (hx28 : s.readReg64 .x28 = 0#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
      chunkedStatesAt A (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
      memRegion (s0.sp - 3056#64) 32 ∗ memRegion (s0.sp - 3024#64) 2792 ∗
      ChainProofs.chainAt A (s0.sp - 232#64) G1 chain1 ∗ memRegion (s0.sp - 144#64) 48 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcont_err_2028 : ∀ (err : Error) (w1_err w2_err w3_err : BitVec 64)
        (G1' : ChainProofs.ChainGhost) (s1 : State) (P1 : SepProp),
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .error (.err err) →
      (∀ r : BitVec 64,
        ((r + 8#64) ↦₆₄ w1_err) ⊢
          ((r + 8#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag err) ∗ memRegion (r + 9#64) 7) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2028#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = w1_err →
      s1.readReg64 .x22 = w2_err → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = w3_err → s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗ ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
        ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗ ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
        memRegion (s0.sp - 3024#64) 2792 ∗ ChainProofs.chainAt A (s0.sp - 232#64) G1' chain1 ∗
        memRegion (s0.sp - 144#64) 48 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_ok_2664 : ∀ (chain2 : Chain) (G2 : ChainProofs.ChainGhost) (rawKey : Bytes)
        (cap_rk ptr_rk : BitVec 64) (s1 : State) (P1 : SepProp),
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2664#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = cap_rk →
      s1.readReg64 .x22 = ptr_rk → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = BitVec.ofNat 64 rawKey.length → s1.readReg64 .x25 = s0.sp - 3056#64 →
      s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 576 ∗ chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2856 ∗ ChainProofs.chainAt A (s0.sp - 232#64) G2 chain2 ∗
        memRegion (s0.sp - 144#64) 48 ∗ RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hrk_ok := spqrRecv_chainRecvKey_ok hC
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  have hfp : s.readReg64 .fp = s0.sp - 96#64 := hx29
  have hfits : ChainProofs.RecvPrevFits chain1 :=
    recvPrevFits_of_v1ChainAfterKey (F := F) (K := K) hst_len hdec hcf hkey
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hrk_ok hpc hcont_err_2028 hcont_ok_2664 ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1976 52
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  apply SepWPpI.of_sepWP (mid := entry + bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::recv_key")); wp_steps 6
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainRecvKeyStackX (by decide))) (by sep_focus) ?_
  refine SepWPpI.call_inImage hrk_ok
    (⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩ : ChainRecvKeyGhost)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align) (rfl : _ = entry + 2000#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun sm => by
      dsimp only [chainRecvKeySpecX]
      have hpan := onPanic_of_v1_chainRecvKey hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hkey s0 sm
      simpa only [State.trace_setPC, State.trace_writeReg64, allocFailedIn, htr] using hpan)
    (fun _ _ => rfl)
    (by
      dsimp only [chainRecvKeySpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], hfits⟩
        (by simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; sep_focus)) ?_
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_c, hx20_c, _, _, hx23_c, _, hx25_c, _, _, hx28_c, hxfp_c, hvregs_c⟩
  dsimp only [chainRecvKeySpecX]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx25_sm : sm.readReg64 .x25 = s0.sp - 3056#64 := by rw [hx25_c]; simp only [arm64_norm, *]
  have hx28_sm : sm.readReg64 .x28 = 0#64 := by rw [hx28_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; simp only [arm64_norm, *]
  have hsp_eq := congrArg (stackAt · chainRecvKeyStackX) (hspm.symm.trans hspm')
  refine SepWPpI.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainRecvKeyStackX (by decide)).symm)
    (by sep_focus) ?_
  cases hrk_res : Chain.recvKey (spqrHkdfWith F) chain1 (pre.epoch - 1#64) pre.index with
  | error ce =>
    cases ce with
    | panic _ => dsimp only [recvKeyPostAt]; exact SepWPpI.focus_pure (by sep_focus) False.elim
    | err err =>
      dsimp only [recvKeyPostAt]; unfold ChainProofs.chainRepr
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPpI.exists_left hrunm; intro G1'
      apply SepWPpI.of_sepWP (mid := entry + 2028#64)
      refine SepWP.focus_weaken (recvKeyErrAt_sub3056_expose_words4 s0.sp err) (by sep_focus) ?_
      wp_pull_exists; rename_i w1_err w2_err w3_err
      wp_focus_pure; intro hw1_err; wp_steps 7
      apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact hcont_err_2028 err w1_err w2_err w3_err G1' _ _ hrk_res hw1_err
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
  | ok pair =>
    rcases pair with ⟨chain2, rawKey⟩
    dsimp only [recvKeyPostAt]; unfold ChainProofs.chainRepr
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPpI.exists_left hrunm; intro G2
    apply SepWPpI.of_sepWP (mid := entry + 2664#64)
    refine SepWP.focus_weaken (recvKeyOkAt_sub3056_expose A s0.sp rawKey) (by sep_focus) ?_
    wp_pull_exists; rename_i cap_rk ptr_rk; wp_steps 7
    refine SepWP.focus_weaken (memRegion_576_join_v1_ok s0.sp sckaMsg) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (memRegion_2856_join_v1_ok s0.sp 0#64 cap_rk ptr_rk (BitVec.ofNat 64 rawKey.length)) (by sep_focus) ?_
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact hcont_ok_2664 chain2 G2 rawKey cap_rk ptr_rk _ _ hrk_res
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)

/-! ## 5. Composed V1 Ratchet Chain Segment (`+1856 -> +2664`) -/

/-- Top-level V1 ratchet chain composition (`+1856 -> +2568 / +2028 / +2664`): composes
    `step_v1_chainFrom_1856`, `step_v1_chain_reloc_and_addEpoch_1888`, and
    `step_v1_chainRecvKey_1976`. -/
theorem step_v1_ratchet_1856_to_2664 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64) (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 kw0 kw1 kw2 kw3 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (v : V1Recv spqrPolyApi (spqrAuthApi F)) (P_key R : SepProp)
    (s0 s : State) (P : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32) (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb) (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8) (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v) (hep0 : (pre.epoch == 0#64) = false)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        States.Recv.optEpochSecretAt A dst v.key)
    (hs0_align : s0.spAligned = true) (hsp4640_ne : s0.sp - 4640#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1856#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 3056#64) (hx1 : s.readReg64 .x1 = s0.sp - 4592#64)
    (hx2 : s.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64))
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = w0) (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1) (hx26 : s.readReg64 .x26 = s0.sp - 1160#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      ProtoRepr.optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗ chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcont_err_2568 : ∀ (e : Error) (q0_err : BitVec 128) (w3_err : BitVec 64) (s1 : State) (P1 : SepProp),
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .error e →
      BitVec.truncate 8 q0_err = Top.ChainFromVersionNegotiation.spqrErrorTag e →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2568#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x8 = Top.ChainFromVersionNegotiation.noneCap → s1.readReg64 .x9 = w3_err →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 32 ∗ ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
        P_key ∗ chunkedStatesAt A (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ Top.ChainFromVersionNegotiation.noneCap) ∗
        ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 3024#64) 56 ∗
        memRegion (s0.sp - 2968#64) 872 ∗
        ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗ memRegion (s0.sp - 2072#64) 1976 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_err_2028 : ∀ (chain0 chain1 : Chain) (err : Error) (w1_err w2_err w3_err : BitVec 64)
        (G1' : ChainProofs.ChainGhost) (s1 : State) (P1 : SepProp),
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .error (.err err) →
      (∀ r : BitVec 64,
        ((r + 8#64) ↦₆₄ w1_err) ⊢
          ((r + 8#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag err) ∗ memRegion (r + 9#64) 7) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2028#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = w1_err →
      s1.readReg64 .x22 = w2_err → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = w3_err → s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 80 ∗ memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 48 ∗
        chunkedStatesAt A (s0.sp - 4016#64) v.state ∗ memRegion (s0.sp - 3088#64) 32 ∗
        ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗ ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
        ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗ ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
        memRegion (s0.sp - 3024#64) 2792 ∗ ChainProofs.chainAt A (s0.sp - 232#64) G1' chain1 ∗
        memRegion (s0.sp - 144#64) 48 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R))
    (hcont_ok_2664 : ∀ (chain0 chain1 chain2 : Chain) (G2 : ChainProofs.ChainGhost) (rawKey : Bytes)
        (cap_rk ptr_rk : BitVec 64) (s1 : State) (P1 : SepProp),
      chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 →
      v1ChainAfterKey (spqrHkdfWith F) chain0 v.key = .ok chain1 →
      chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2664#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x21 = cap_rk →
      s1.readReg64 .x22 = ptr_rk → s1.readReg64 .x23 = w0 →
      s1.readReg64 .x24 = BitVec.ofNat 64 rawKey.length → s1.readReg64 .x25 = s0.sp - 3056#64 →
      s1.readReg64 .x26 = 0#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 =
        spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 576 ∗ chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2856 ∗ ChainProofs.chainAt A (s0.sp - 232#64) G2 chain2 ∗
        memRegion (s0.sp - 144#64) 48 ∗ RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0 →
      SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  refine step_v1_chainFrom_1856 hC st msg ret pre pre_pb w0 w1 kw0 kw1 kw2 kw3 sckaMsg v P_key R
    s0 s P hs0_align hsp4640_ne hpc hrun hsp htr
    hx0 hx1 hx2 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hP hcont_err_2568 ?_
  intro chain0 G0 pad0 s1888 P1888 hcf _ hpc1888 hrun1888 hsp1888 htr1888
    hx8_1888 hx9_1888 hx19_1888 hx20_1888 hx21_1888 hx22_1888 hx23_1888 hx24_1888 hx25_1888
    hx26_1888 hx27_1888 hx28_1888 hx29_1888 hP1888
  refine step_v1_chain_reloc_and_addEpoch_1888 hC st msg ret pre pre_pb pb
    w0 w1 kw0 kw1 kw2 kw3 sckaMsg st0 v P_key R chain0 G0 pad0 s0 s1888 P1888
    hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hfold_key hs0_align
    hpc1888 hrun1888 hsp1888 htr1888 hx8_1888 hx9_1888 hx19_1888 hx20_1888 hx21_1888 hx22_1888
    hx23_1888 hx24_1888 hx25_1888 hx26_1888 hx27_1888 hx28_1888 hx29_1888 hP1888 ?_
  intro chain1 G1 s1976 P1976 hkey hpc1976 hrun1976 hsp1976 htr1976
    hx19_1976 hx20_1976 hx21_1976 hx22_1976 hx23_1976 hx28_1976 hx29_1976 hP1976
  exact step_v1_chainRecvKey_1976 hC st msg ret pre pre_pb pb w0 w1 sckaMsg st0 v R
    chain0 chain1 G1 s0 s1976 P1976
    hst_len hpre hdec hinner hmv hmin hmsg hfrom hrecv hep0 hcf hkey hs0_align
    hpc1976 hrun1976 hsp1976 htr1976
    hx19_1976 hx20_1976 hx21_1976 hx22_1976 hx23_1976 hx28_1976 hx29_1976 hP1976
    (fun err w1_err w2_err w3_err G1' s1 P1 => hcont_err_2028 chain0 chain1 err w1_err w2_err w3_err G1' s1 P1 hcf hkey)
    (fun chain2 G2 rawKey cap_rk ptr_rk s1 P1 => hcont_ok_2664 chain0 chain1 chain2 G2 rawKey cap_rk ptr_rk s1 P1 hcf hkey)

end CryptoVerification.SpqrV1.Top.Recv

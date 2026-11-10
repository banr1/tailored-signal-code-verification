/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Derive
import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1DomIdle
import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL45R
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathB
import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel
import LibsignalBinary.Specifications.LibsignalSpqrV1.Init

/-!
# Paths A and B Envelope Inclusion for Post-Bob `decryptPrekey` (`W4`)

Proves `w4pb_armAB_sub_dom0'`, embedding the Path-A and Path-B (`Matched`) disjuncts of
`W4r2PollCustomP3GvSeqFreeEnv` into
`realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmAB

open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession
  (ChainKey Crypto IdentityKey MessageType Mut PrivateKey PublicKey RatchetState ReceiverChain
   SenderChain SessionState SignalMessage SignalProtocolError Spqr TripleRatchet aesCbcDecrypt
   liftE maxForwardJumps zoom)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.E2E
  (PreKeyMessageFields UnreachedPqxdhPrimitives acceptInput modelPrims pqxdhSpqrSession)
open CryptoVerification.E2E.Record
  (bytesField encChainKey encMessageKey encPendingKyber encPendingPreKey encReceiverChain
   encSenderChain encSession encodeRecord int32Field lenField msgField optUint32Field uint32Field
   uint64Field)
open CryptoVerification.LibsignalProtoCodec
  (WireType encodeKey encodeVarint encodeVarintAux protoSignalCodec)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SessionGhost SignalMessageGhost coinsOf serializeAddresses serviceIdParse uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOkD2c pkStoreKeys pkToE? pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0 (pkToE?_pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKitPlaced
   loadRec_scopeKit_eq pathAInitSession pathAInitState pmPreKeyId scope_of_loadRec_some
   tryDecryptFromRecord_preKey_recOk_of_scopeIn version_eq_zeroExtend_iff)
open CryptoVerification.SignalSession.Cli.Slots
  (FilesOkPeer cliSessLoadRel_eq_loadRec encodeInjOn_deserializeScopeP_Q loadRec scopeIn scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget
  (StageP2MatchedBridgeEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
  (StageP2MatchedEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX
  (dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed dpx_deserEnv dpx_p2PathAErrEnv
   dpx_p2PathAErrEnv_sub_w4StageP2PathAFull9 dpx_p2PathAOkEnv
   dpx_p2PathAOkEnv_sub_w4StageP2PathAFull9
   dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide
   dpx_stageP2MatchedEnv_sub_w4StageP2MatchedWide
   dpx_stageP4MatchedSeqFree_sub_w4StageP4MatchedAllFixed
   dpx_stageP4PathASeqFree_sub_w4StageP4PathAAllFixed)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (W4CloneACDomEnv W4CloneBDomEnv)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryStageP2PathAWideEnvAllFixed W4BinaryStageP4PathAWideEnvAllFixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_length_le topStateTight_spqrV1_recv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid SessionCloneDom ghostCloneValid_of_sessionGhostValid sessionCloneDom_of_scopeIn
   sessionCloneDom_of_scopeKit_pq)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4StageP3WideEnv optStageEnv_nil w4StageP3WideEnv_of_err
   w4StageP3WideEnv_of_okPrefix w4StageP3WideEnv_of_verNe)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Derive
  (encodeRecord_some_length_le_of_rc_le_one sessionCloneDom_postBob_of_genP3S5Model_ok)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (PostBobPrev1Dom SessionGetPrev0Guard W4BinaryCallSiteDomCmk0' postBobRecordCapOf_286K_eq
   realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4PostBobPqCap)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1DomIdle (postBobPrev1Dom_idle_exists)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
  (W4RecvPrekeyTryDecACCmkSrEnvOf)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
  (w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4BinaryRecvPrekeyParamsCmk W4FailedTryDecryptCallCmk W4TryDecryptCallCmk
   W4TryDecryptCallDomCmkOf W4TryDecryptPathACDomCmkOf w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL45R
  (h7l45r_pathAInit_segClone_sub_w4CloneACDomEnv h7l45r_pathAInit_tdAC_dom
   h7l45r_pathAInit_topStateTight)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (StageP3Env StageP3ErrEnv StageP3OkPrefixEnv StageP3VerNeEnv stageP3TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (StageP2PathAEnv StageP4MatchedEnv StageP4PathAEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
  (CliStageP1OkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
  (cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessSeqFreeBudgetEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2 (W4r2SessionGhostValid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
  (w4s2_TryDecryptTopStateGuardedEnv w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (FromMEnv FromVPostTdEnv SegCloneEnv TryDecryptEnvArgs)

/-! ## `encodeRecord` and `tryDecryptWithState` Helpers -/

private theorem w4pb_seqEnv_mono {A1 A2 B1 B2 : List AllocEvent → Prop} {evs : List AllocEvent}
    (hA : ∀ e, A1 e → A2 e) (hB : ∀ e, B1 e → B2 e) (h : SeqEnv A1 B1 evs) :
    SeqEnv A2 B2 evs := by
  rcases h with ha | ⟨e1, e2, rfl, ha, hb⟩
  · exact Or.inl (hA evs ha)
  · exact Or.inr ⟨e1, e2, rfl, hA e1 ha, hB e2 hb⟩

private theorem w4pb_seqEnv_split_opt {E1 E2 : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv E1 E2 evs) :
    ∃ e1 e2, evs = e1 ++ e2 ∧ E1 e1 ∧ (e2 = [] ∨ E2 e2) := by
  rcases h with h1 | ⟨e1, e2, rfl, h1, h2⟩
  · exact ⟨evs, [], (List.append_nil evs).symm, h1, Or.inl rfl⟩
  · exact ⟨e1, e2, rfl, h1, Or.inr h2⟩

private theorem w4pb_forall_of_zip_eq_len {α β : Type} {P : β → Prop} :
    ∀ {xs : List α} {ys : List β},
      xs.length = ys.length →
      (∀ p ∈ xs.zip ys, P p.2) →
      ∀ y ∈ ys, P y
  | [], [], _, _ => fun _ hy => nomatch hy
  | x :: xs, _ :: ys, hlen, hzip => fun z hz => by
    rcases List.mem_cons.mp hz with rfl | hrest
    · exact hzip (x, z) (List.Mem.head _)
    · exact w4pb_forall_of_zip_eq_len (Nat.succ.inj hlen)
        (fun p hp => hzip p (List.Mem.tail _ hp)) z hrest

private theorem w4pb_mk_len_le_of_sessionGhostValid {G : SessionGhost}
    {s : Session (List (BitVec 8))} (hgv : SessionGhostValid G s) :
    ∀ c ∈ s.state.receiverChains, c.messageKeys.length ≤ 2000 := by
  have hcl := ghostCloneValid_of_sessionGhostValid hgv
  exact w4pb_forall_of_zip_eq_len hcl.chains_len (fun gc hmem => (hcl.chains_ok gc hmem).2.2)

private theorem w4pb_encodeVarintAux_length_le :
    ∀ (k : Nat) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold encodeVarintAux
    split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.add_le_add_right (w4pb_encodeVarintAux_length_le k (v >>> 7)) 1

private theorem w4pb_encodeVarint_length_le (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  w4pb_encodeVarintAux_length_le 10 v

private theorem w4pb_encodeKey_length_le (tag : Nat) (wt : WireType) :
    (encodeKey tag wt).length ≤ 10 :=
  w4pb_encodeVarint_length_le _

private theorem w4pb_lenField_length_le (tag : Nat) (payload : List (BitVec 8)) :
    (lenField tag payload).length ≤ 20 + payload.length := by
  unfold lenField
  simp only [List.length_append]
  have h1 := w4pb_encodeKey_length_le tag .lengthDelimited
  have h2 := w4pb_encodeVarint_length_le (BitVec.ofNat 64 payload.length)
  omega

private theorem w4pb_bytesField_length_le (tag : Nat) (v : List (BitVec 8)) :
    (bytesField tag v).length ≤ 20 + v.length := by
  unfold bytesField
  split_ifs <;> [simp; exact w4pb_lenField_length_le tag v]

private theorem w4pb_uint32Field_length_le (tag : Nat) (v : BitVec 32) :
    (uint32Field tag v).length ≤ 20 := by
  unfold uint32Field
  split_ifs
  · simp
  · rw [List.length_append]
    have h1 := w4pb_encodeKey_length_le tag .varint
    have h2 := w4pb_encodeVarint_length_le (v.setWidth 64)
    omega

private theorem w4pb_uint64Field_length_le (tag : Nat) (v : BitVec 64) :
    (uint64Field tag v).length ≤ 20 := by
  unfold uint64Field
  split_ifs
  · simp
  · rw [List.length_append]
    have h1 := w4pb_encodeKey_length_le tag .varint
    have h2 := w4pb_encodeVarint_length_le v
    omega

private theorem w4pb_int32Field_length_le (tag : Nat) (v : BitVec 32) :
    (int32Field tag v).length ≤ 20 := by
  unfold int32Field
  split_ifs
  · simp
  · rw [List.length_append]
    have h1 := w4pb_encodeKey_length_le tag .varint
    have h2 := w4pb_encodeVarint_length_le (v.signExtend 64)
    omega

private theorem w4pb_optUint32Field_length_le (tag : Nat) (ov : Option (BitVec 32)) :
    (optUint32Field tag ov).length ≤ 20 := by
  cases ov with
  | none => simp [optUint32Field]
  | some v =>
    unfold optUint32Field
    rw [List.length_append]
    have h1 := w4pb_encodeKey_length_le tag .varint
    have h2 := w4pb_encodeVarint_length_le (v.setWidth 64)
    omega

private theorem w4pb_msgField_length_le (tag : Nat) (ob : Option (List (BitVec 8))) (B : Nat)
    (hB : ∀ b, ob = some b → b.length ≤ B) : (msgField tag ob).length ≤ 20 + B := by
  cases ob with
  | none => simp [msgField]
  | some b =>
    dsimp only [msgField]
    have h1 := w4pb_lenField_length_le tag b
    have h2 := hB b rfl
    omega

private theorem w4pb_length_flatten_map_le {α : Type} :
    ∀ (l : List α) (f : α → List (BitVec 8)) (B : Nat),
      (∀ a ∈ l, (f a).length ≤ B) → ((l.map f).flatten).length ≤ B * l.length
  | [], _, _, _ => by simp
  | a :: tl, f, B, hf => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have ha := hf a (List.mem_cons_self ..)
    have htl := w4pb_length_flatten_map_le tl f B (fun y hy => hf y (List.mem_cons_of_mem a hy))
    rw [Nat.mul_add, Nat.mul_one]
    omega

private theorem w4pb_keyToBytes32_length (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

private theorem w4pb_publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]

private theorem w4pb_identityKey_serialize_length (ik : IdentityKey) : ik.serialize.length = 33 := by
  simp [IdentityKey.serialize, PublicKey.serialize]

private theorem w4pb_privateKey_bytes_length (sk : PrivateKey) : sk.bytes.toList.length = 32 :=
  sk.bytes.toList_length

private theorem w4pb_encChainKey_length_le (ck : ChainKey) : (encChainKey ck).length ≤ 72 := by
  unfold encChainKey
  rw [List.length_append]
  have h1 := w4pb_uint32Field_length_le 1 ck.index
  have h2 := w4pb_bytesField_length_le 2 (keyToBytes32 ck.key)
  rw [w4pb_keyToBytes32_length] at h2
  omega

private theorem w4pb_encSenderChain_length_le (c : SenderChain) :
    (encSenderChain c).length ≤ 197 := by
  unfold encSenderChain
  simp only [List.length_append]
  have h1 := w4pb_bytesField_length_le 1 c.ratchetKey.publicKey.serialize
  rw [w4pb_publicKey_serialize_length] at h1
  have h2 := w4pb_bytesField_length_le 2 c.ratchetKey.privateKey.bytes.toList
  rw [w4pb_privateKey_bytes_length] at h2
  have h3 := w4pb_msgField_length_le 3 (some (encChainKey c.chainKey)) 72
    (fun _ hb => Option.some.inj hb ▸ w4pb_encChainKey_length_le c.chainKey)
  omega

private theorem w4pb_encReceiverChain_length_le (c : ReceiverChain)
    (hlen : c.messageKeys.length ≤ 2000)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32) :
    (encReceiverChain c).length ≤ 184145 := by
  unfold encReceiverChain
  simp only [List.length_append]
  have h1 := w4pb_bytesField_length_le 1 c.senderRatchetKey.serialize
  rw [w4pb_publicKey_serialize_length] at h1
  have h2 := w4pb_msgField_length_le 3 (c.chainKey.map encChainKey) 72 (by
    intro b hb
    rcases hck : c.chainKey with _ | ck <;> rw [hck] at hb
    · cases hb
    · injection hb with hb'; subst hb'; exact w4pb_encChainKey_length_le ck)
  have h3 := w4pb_length_flatten_map_le c.messageKeys (fun mk => lenField 4 (encMessageKey mk)) 92
    (by
      intro mk hmk
      have hmk_len : (encMessageKey mk).length ≤ 72 := by
        unfold encMessageKey
        rw [List.length_append]
        have hu := w4pb_uint32Field_length_le 1 mk.counter
        have hb := w4pb_bytesField_length_le 5 mk.seed
        rw [hseeds mk hmk] at hb
        omega
      have hl := w4pb_lenField_length_le 4 (encMessageKey mk)
      omega)
  omega

private theorem w4pb_encodeRecord_some_length_le {G : SessionGhost} {s : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G s) (hdom : SessionCloneDom 286196 s) :
    (encodeRecord ⟨some s⟩).length ≤ 2097152 := by
  have hmk_le := w4pb_mk_len_le_of_sessionGhostValid hgv
  obtain ⟨hrc_len, hseeds, halice_len, hkyb_cap, hpq_len⟩ := hdom
  change (lenField 1 (encSession s)).length ≤ 2097152
  have houter := w4pb_lenField_length_le 1 (encSession s)
  have henc : (encSession s).length ≤ 1209311 := by
    unfold encSession
    dsimp only
    simp only [List.length_append]
    have hf1 := w4pb_uint32Field_length_le 1 s.state.sessionVersion
    have hf2 := w4pb_bytesField_length_le 2 s.state.localIdentity.serialize
    rw [w4pb_identityKey_serialize_length] at hf2
    have hf3 :
        (bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length ≤ 53 := by
      cases hrem : s.state.remoteIdentity with
      | none =>
        have h := w4pb_bytesField_length_le 3 []
        simpa using Nat.le_trans h (by decide)
      | some rem =>
        dsimp only [Option.map, Option.getD]
        have h := w4pb_bytesField_length_le 3 rem.serialize
        rw [w4pb_identityKey_serialize_length] at h
        omega
    have hf4 := w4pb_bytesField_length_le 4 (keyToBytes32 s.state.rootKey)
    rw [w4pb_keyToBytes32_length] at hf4
    have hf5 := w4pb_uint32Field_length_le 5 s.state.previousCounter
    have hf6 := w4pb_msgField_length_le 6 (s.state.senderChain.map encSenderChain) 197 (by
      intro b hb
      rcases hsc : s.state.senderChain with _ | sc <;> rw [hsc] at hb
      · cases hb
      · injection hb with hb'; subst hb'; exact w4pb_encSenderChain_length_le sc)
    have hf7 := w4pb_length_flatten_map_le s.state.receiverChains
      (fun c => lenField 7 (encReceiverChain c)) 184165 (by
        intro rc hrc
        have hl := w4pb_lenField_length_le 7 (encReceiverChain rc)
        have he := w4pb_encReceiverChain_length_le rc (hmk_le rc hrc) (hseeds rc hrc)
        omega)
    have hf9 := w4pb_msgField_length_le 9 (s.pendingPreKey.map encPendingPreKey) 113 (by
      intro b hb
      rcases hpp : s.pendingPreKey with _ | pp <;> rw [hpp] at hb
      · cases hb
      · injection hb with hb'; subst hb'
        unfold encPendingPreKey
        simp only [List.length_append]
        have p1 := w4pb_optUint32Field_length_le 1 pp.preKeyId
        have p2 := w4pb_bytesField_length_le 2 pp.baseKey.serialize
        rw [w4pb_publicKey_serialize_length] at p2
        have p3 := w4pb_int32Field_length_le 3 pp.signedPreKeyId
        have p4 := w4pb_uint64Field_length_le 4 pp.timestamp
        omega)
    have hf10 := w4pb_uint32Field_length_le 10 s.remoteRegistrationId
    have hf11 := w4pb_uint32Field_length_le 11 s.localRegistrationId
    have hf13 := w4pb_bytesField_length_le 13 s.aliceBaseKey
    have hf14 := w4pb_msgField_length_le 14 (s.pendingKyberPreKey.map encPendingKyber) 1609 (by
      intro b hb
      rcases hky : s.pendingKyberPreKey with _ | ky <;> rw [hky] at hb
      · cases hb
      · injection hb with hb'; subst hb'
        unfold encPendingKyber
        rw [List.length_append]
        have k1 := w4pb_uint32Field_length_le 1 ky.preKeyId
        have k2 := w4pb_bytesField_length_le 2 ky.ciphertext
        have hkcap := hkyb_cap ky hky
        omega)
    have hf15 := w4pb_bytesField_length_le 15 s.state.pqRatchetState
    omega
  omega

private theorem w4pb_Mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  cases h : m s with
  | mk r s' =>
    cases r <;>
      (simp [Mut.exec, h, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont,
        StateT.run, ExceptT.run]; try rfl)

private theorem w4pb_Mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

private theorem w4pb_Mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem w4pb_Mut_exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem w4pb_Mut_exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl

private theorem w4pb_Mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl

private theorem w4pb_Mut_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

private theorem w4pb_Mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

private theorem w4pb_onRatchet_pq {PQ α : Type} (m : Mut RatchetState α) (t t' : TripleRatchet PQ)
    (a : α) (h : Mut.exec (TripleRatchet.onRatchet m) t = (.ok a, t')) :
    t'.pqrState = t.pqrState := by
  unfold TripleRatchet.onRatchet zoom at h
  simp only [w4pb_Mut_exec_bind, w4pb_Mut_exec_get] at h
  rcases hm : Mut.exec m t.ratchet with ⟨_ | _, _⟩
  · simp [hm, w4pb_Mut_exec_set, w4pb_Mut_exec_liftE] at h
  · simp only [hm, w4pb_Mut_exec_set, w4pb_Mut_exec_liftE, Prod.mk.injEq, Except.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl

private theorem w4pb_tryDecryptWithState_spqr {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8))) (m : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (record s : SessionState PQ)
    (pt : List (BitVec 8))
    (hd : Mut.exec (SessionState.tryDecryptWithState C spqr expected m msgType coins) record =
      (.ok pt, s)) :
    ∃ salt, spqr.recv record.pqRatchetState m.pqRatchet = .ok (s.pqRatchetState, salt) := by
  unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
    SessionState.takeRatchetState SessionState.takePqRatchetState at hd
  simp only [w4pb_Mut_exec_bind, w4pb_Mut_exec_get, w4pb_Mut_exec_modifyGet] at hd
  rcases hrem : record.remoteIdentity with _ | rem
  · simp [hrem, w4pb_Mut_exec_throw] at hd
  · simp only [hrem, w4pb_Mut_exec_pure] at hd
    set tr0 : TripleRatchet PQ := ⟨⟨record.rootKey, record.senderChain, record.receiverChains,
      record.previousCounter, maxForwardJumps⟩, record.pqRatchetState, record.localIdentity, rem⟩
    rcases hdec : Mut.exec (TripleRatchet.decrypt C spqr expected m msgType coins) tr0 with
      ⟨_ | _, _⟩
    · simp [hdec, w4pb_Mut_exec_liftE] at hd
    · simp only [hdec, w4pb_Mut_exec_liftE, w4pb_Mut_exec_modify, Prod.mk.injEq] at hd
      rcases hd with ⟨-, rfl⟩
      unfold TripleRatchet.decrypt at hdec
      simp only [w4pb_Mut_exec_bind] at hdec
      rcases hens : Mut.exec (TripleRatchet.onRatchet
          (RatchetState.ensureReceiverChain C m.senderRatchetKey coins)) tr0 with ⟨_ | ck, tr1⟩
      · rw [hens] at hdec; cases hdec
      · rw [hens] at hdec; dsimp only at hdec
        have hpq1 := w4pb_onRatchet_pq _ tr0 tr1 ck hens
        rcases hcons : Mut.exec (TripleRatchet.onRatchet
            (RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType)) tr1 with
          ⟨_ | mkg, tr2⟩
        · rw [hcons] at hdec; cases hdec
        · rw [hcons] at hdec; dsimp only at hdec
          have hpq2 := w4pb_onRatchet_pq _ tr1 tr2 mkg hcons
          simp only [w4pb_Mut_exec_get] at hdec
          cases hpan : spqr.recvPanics tr2.pqrState m.pqRatchet
          · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hdec
            rcases hspqr : spqr.recv tr2.pqrState m.pqRatchet with err | ⟨_, salt⟩
            · cases err <;> simp [hspqr, w4pb_Mut_exec_throw] at hdec
            · simp only [hspqr, w4pb_Mut_exec_bind, w4pb_Mut_exec_pure] at hdec
              split_ifs at hdec
              · simp [w4pb_Mut_exec_throw] at hdec
              · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F salt).cipherKey
                    (mkg.generateKeys C.F salt).iv m.ciphertext with _ | _
                · simp [haes, w4pb_Mut_exec_throw] at hdec
                · simp only [haes, w4pb_Mut_exec_bind, w4pb_Mut_exec_modify, w4pb_Mut_exec_pure,
                    Prod.mk.injEq] at hdec
                  rcases hdec with ⟨-, rfl⟩
                  exact ⟨salt, by
                    simpa [TripleRatchet.applyToSessionState,
                      SessionState.clearUnacknowledgedPreKeyMessage, hpq2, hpq1, tr0] using hspqr⟩
          · simp [hpan, w4pb_Mut_exec_throw] at hdec

/-! ## Witness Builders and Path-A / Path-B Inclusions -/

private def w4pb_dummyReserve : DoReserveCall :=
  ⟨0#64, 0#64, 0#64, [], 0⟩

private theorem w4pb_dummyReserve_old : w4pb_dummyReserve.cap.toNat ≤ 4096 := by
  decide

private theorem w4pb_dummyReserve_new :
    reserveCap w4pb_dummyReserve.cap.toNat w4pb_dummyReserve.bs.length
      w4pb_dummyReserve.additional ≤ 4096 := by
  decide

private def w4pb_dummyInitialStateGhost : InitialStateGhost :=
  ⟨0#64, 0#64, 0#64, { direction := .b2a, version := .v1, minVersion := .v1, authKey := [] }⟩

private theorem w4pb_dummyInitialStateGhost_key :
    w4pb_dummyInitialStateGhost.p.authKey.length ≤ 32 := by
  decide

private def w4pb_noneRecordGhost : RecordGhost :=
  ⟨0#64, 0#64, none⟩

private def w4pb_emptySessionRecord : SessionRecord (List (BitVec 8)) :=
  ⟨none⟩

private theorem w4pb_emptySessionRecord_enc :
    (encodeRecord w4pb_emptySessionRecord).length ≤ 2097152 := by
  decide

private theorem w4pb_none_out0_valid :
    ∀ G ses, w4pb_noneRecordGhost.cur = some G →
      w4pb_emptySessionRecord.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses :=
  fun _ _ hg _ => nomatch hg

private def w4pb_dummyWhisperGhost : SignalMessageGhost :=
  ⟨0#64, 0#64, 0#64, 0#64, 0#64⟩

private def w4pb_dummyTdCall
    (G_d : SessionGhost) (st_d : SessionState (List (BitVec 8))) (g : DecPkGhost) :
    W4TryDecryptCallCmk :=
  ⟨stageP3TryDecryptEnvArgs G_d st_d g.peer g.me w4pb_dummyWhisperGhost g.msg.message g.coins⟩

private def w4pb_dummyFailedTdCall
    (G_d : SessionGhost) (st_d : SessionState (List (BitVec 8))) (g : DecPkGhost) :
    W4FailedTryDecryptCallCmk :=
  ⟨w4pb_dummyTdCall G_d st_d g, []⟩

private def w4pb_mkPathAParams
    (W : CliHooks) (g : DecPkGhost)
    (G_idle : SessionGhost) (ses_idle : Session (List (BitVec 8)))
    (hasOpk : Bool) (spkId kpkId opkId : BitVec 32)
    (x_spqr : InitialStateGhost)
    (isPathAC : Bool) (td_AC : W4TryDecryptCallCmk)
    (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8))) :
    W4BinaryRecvPrekeyParamsCmk where
  base := {
    C := W.C
    K := W.Q.K
    rd := cliIo.rd
    files := g.F
    kpkDir := StoresGhost.opened.kyber.oneTime
    peer := g.peer
    hasOpk := hasOpk
    spkId := spkId
    kpkId := kpkId
    opkId := opkId
    kpkMarkName := []
    ownKeyName := []
    ownRegName := []
    x_res := w4pb_dummyReserve
    x_spqr := x_spqr
    hasCurSession := false
    G_cur := G_idle
    st_cur := ses_idle.state
    fc_cur := w4pb_dummyFailedTdCall G_idle ses_idle.state g
    archivedTrials := []
    isPathB := false
    td_B := w4pb_dummyTdCall G_idle ses_idle.state g
    isPathAC := isPathAC
    td_AC := td_AC
    g_arch := w4pb_noneRecordGhost
    r_arch := w4pb_emptySessionRecord
    g_out0 := g_out0
    r_out0 := r_out0
    G_out1 := G_idle
    sess_out1 := ses_idle
    enc_prev1 := []
  }
  remoteIdKey := g.msg.identityKey
  baseKey := g.msg.baseKey

private theorem w4pb_mkPathAParams_dom0'
    {maxCt : Nat} (W : CliHooks) (g : DecPkGhost)
    (G_idle : SessionGhost) (ses_idle : Session (List (BitVec 8)))
    (hOut1 : PostBobPrev1Dom 286196 2097152 2469364 G_idle ses_idle [])
    (hasOpk : Bool) (spkId kpkId opkId : BitVec 32)
    (x_spqr : InitialStateGhost) (hspqr : x_spqr.p.authKey.length ≤ 32)
    (isPathAC : Bool) (td_AC : W4TryDecryptCallCmk)
    (htdAC : isPathAC = true → W4TryDecryptPathACDomCmkOf W.C.F W.Q.K maxCt td_AC)
    (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8)))
    (hout0_valid : ∀ G ses, g_out0.cur = some G → r_out0.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hout0_enc : (encodeRecord r_out0).length ≤ 2097152) :
    W4BinaryCallSiteDomCmk0' W.C W.Q.K maxCt g.peer.val g.F
      (w4pb_mkPathAParams W g G_idle ses_idle hasOpk spkId kpkId opkId x_spqr
        isPathAC td_AC g_out0 r_out0).base :=
  ⟨{ eq_C := rfl
     eq_K := rfl
     eq_rd := rfl
     eq_files := rfl
     eq_peerVal := rfl
     kpk_dir := Or.inl rfl
     ownKey_len := Nat.zero_le 64
     ownReg_len := Nat.zero_le 64
     kpkMark_len := Nat.zero_le 64
     res_old := w4pb_dummyReserve_old
     res_new := w4pb_dummyReserve_new
     spqr_key := hspqr
     cur_dom := Or.inl rfl
     arch_valid := fun _ _ hg _ => nomatch hg
     arch_enc := w4pb_emptySessionRecord_enc
     out0_valid := hout0_valid
     out0_enc := hout0_enc
     out1_postBob := hOut1
     trials_len4 := Nat.zero_le 4
     cur_fail_dom := fun h => Bool.noConfusion h
     trials_dom := fun _ hy => nomatch hy
     tdB_dom := fun h => Bool.noConfusion h
     tdAC_dom := htdAC },
   rfl⟩

private def w4pb_mkPathBParams
    (W : CliHooks) (g : DecPkGhost)
    (G_idle : SessionGhost) (ses_idle : Session (List (BitVec 8)))
    (isPathB : Bool) (td_B : W4TryDecryptCallCmk)
    (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8))) :
    W4BinaryRecvPrekeyParamsCmk where
  base := {
    C := W.C
    K := W.Q.K
    rd := cliIo.rd
    files := g.F
    kpkDir := StoresGhost.opened.kyber.oneTime
    peer := g.peer
    hasOpk := false
    spkId := 0#32
    kpkId := 0#32
    opkId := 0#32
    kpkMarkName := []
    ownKeyName := []
    ownRegName := []
    x_res := w4pb_dummyReserve
    x_spqr := w4pb_dummyInitialStateGhost
    hasCurSession := false
    G_cur := G_idle
    st_cur := ses_idle.state
    fc_cur := w4pb_dummyFailedTdCall G_idle ses_idle.state g
    archivedTrials := []
    isPathB := isPathB
    td_B := td_B
    isPathAC := false
    td_AC := w4pb_dummyTdCall G_idle ses_idle.state g
    g_arch := w4pb_noneRecordGhost
    r_arch := w4pb_emptySessionRecord
    g_out0 := g_out0
    r_out0 := r_out0
    G_out1 := G_idle
    sess_out1 := ses_idle
    enc_prev1 := []
  }
  remoteIdKey := g.msg.identityKey
  baseKey := g.msg.baseKey

private theorem w4pb_mkPathBParams_dom0'
    {maxCt : Nat} (W : CliHooks) (g : DecPkGhost)
    (G_idle : SessionGhost) (ses_idle : Session (List (BitVec 8)))
    (hOut1 : PostBobPrev1Dom 286196 2097152 2469364 G_idle ses_idle [])
    (isPathB : Bool) (td_B : W4TryDecryptCallCmk)
    (htdB : isPathB = true → W4TryDecryptCallDomCmkOf W.C.F W.Q.K maxCt td_B)
    (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8)))
    (hout0_valid : ∀ G ses, g_out0.cur = some G → r_out0.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hout0_enc : (encodeRecord r_out0).length ≤ 2097152) :
    W4BinaryCallSiteDomCmk0' W.C W.Q.K maxCt g.peer.val g.F
      (w4pb_mkPathBParams W g G_idle ses_idle isPathB td_B g_out0 r_out0).base :=
  ⟨{ eq_C := rfl
     eq_K := rfl
     eq_rd := rfl
     eq_files := rfl
     eq_peerVal := rfl
     kpk_dir := Or.inl rfl
     ownKey_len := Nat.zero_le 64
     ownReg_len := Nat.zero_le 64
     kpkMark_len := Nat.zero_le 64
     res_old := w4pb_dummyReserve_old
     res_new := w4pb_dummyReserve_new
     spqr_key := w4pb_dummyInitialStateGhost_key
     cur_dom := Or.inl rfl
     arch_valid := fun _ _ hg _ => nomatch hg
     arch_enc := w4pb_emptySessionRecord_enc
     out0_valid := hout0_valid
     out0_enc := hout0_enc
     out1_postBob := hOut1
     trials_len4 := Nat.zero_le 4
     cur_fail_dom := fun h => Bool.noConfusion h
     trials_dom := fun _ hy => nomatch hy
     tdB_dom := htdB
     tdAC_dom := fun h => Bool.noConfusion h },
   rfl⟩

private theorem w4pb_mkPathATrace {P1 P2 P3 P4 : List AllocEvent → Prop}
    {e1 e2 e3 e4 : List AllocEvent}
    (h1 : P1 e1) (h2 : OptStageEnv P2 e2) (h3 : OptStageEnv P3 e3) (h4 : OptStageEnv P4 e4) :
    SeqEnv P1 (SeqEnv (OptStageEnv P2) (SeqEnv (OptStageEnv P3) (OptStageEnv P4)))
      (e1 ++ (e2 ++ (e3 ++ e4))) :=
  Or.inr ⟨e1, e2 ++ (e3 ++ e4), rfl, h1,
    Or.inr ⟨e2, e3 ++ e4, rfl, h2,
      Or.inr ⟨e3, e4, rfl, h3, h4⟩⟩⟩

private theorem w4pb_tdGuarded_eq_w4c (W : CliHooks) (a : TryDecryptEnvArgs)
    (hTop : TopStateTight W.C.F W.Q.K a.st.pqRatchetState) :
    w4s2_TryDecryptTopStateGuardedEnv W a =
      w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam
        CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps W.C W.Q.K a :=
  w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top W a hTop

private theorem w4pb_p2AOk_opt_fixed [LibsignalPlacement]
    {A : RustAlloc} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {g : DecPkGhost} {m : PreKeyMessageFields} {i : SignalMessage}
    (hmsg : g.msg = pmOfE m i)
    (htry : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    {e2 : List AllocEvent}
    (h2 : e2 = [] ∨ dpx_p2PathAOkEnv A X W g e2) :
    ∃ (x_spqr : InitialStateGhost),
      x_spqr.p.authKey.length ≤ 32 ∧
      OptStageEnv
        (W4BinaryStageP2PathAWideEnvAllFixed m.opkId.isSome cliIo.rd g.F
          m.spkId m.kpkId (m.opkId.getD 0#32) W.C.F w4pb_dummyReserve x_spqr) e2 := by
  rcases h2 with rfl | hp2
  · exact ⟨w4pb_dummyInitialStateGhost, w4pb_dummyInitialStateGhost_key, optStageEnv_nil _⟩
  · obtain ⟨m', x_spqr, hpk, _, hspqr_len, hp2_w4⟩ :=
      dpx_p2PathAOkEnv_sub_w4StageP2PathAFull9 w4pb_dummyReserve hp2
    have hpk_m : pkToE? g.msg = some m := hmsg ▸ pkToE?_pmOfE m i htry
    have hm_eq : m' = m := Option.some.inj (hpk.symm.trans hpk_m)
    subst hm_eq
    exact ⟨x_spqr, hspqr_len, Or.inr hp2_w4⟩

private theorem w4pb_out0_bounds_postBob
    {g_out0 : RecordGhost} {r_out0 : SessionRecord (List (BitVec 8))}
    {ss : Session (List (BitVec 8))}
    (hgv : RecordGhostValid g_out0 r_out0)
    (hr : r_out0 = ⟨none⟩ ∨ r_out0 = ⟨some ss⟩)
    (hdom : SessionCloneDom w4PostBobPqCap ss)
    (hrc1 : ss.state.receiverChains.length = 1) :
    (∀ G ses, g_out0.cur = some G → r_out0.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
    (encodeRecord r_out0).length ≤ 2097152 := by
  rcases hr with rfl | rfl
  · exact ⟨(fun _ _ _ hs => nomatch hs), w4pb_emptySessionRecord_enc⟩
  · cases hcur : g_out0.cur with
    | none =>
      unfold RecordGhostValid at hgv
      rw [hcur] at hgv
      exact nomatch hgv
    | some G_out =>
      have hgv_ss : SessionGhostValid G_out ss := by
        unfold RecordGhostValid at hgv
        rw [hcur] at hgv
        exact hgv
      have henc372K : (encodeRecord ⟨some ss⟩).length ≤ 372207 := by
        have hle := encodeRecord_some_length_le_of_rc_le_one hgv_ss hdom (Nat.le_of_eq hrc1)
        rw [postBobRecordCapOf_286K_eq] at hle
        exact hle
      refine ⟨?_, Nat.le_trans henc372K (by decide)⟩
      intro G ses hg hs
      injection hg with hG
      injection hs with hses
      subst hG hses
      exact ⟨hgv_ss, hdom⟩

private theorem w4pb_out0_bounds_of_p4
    {g_out0 : RecordGhost} {r_out0 : SessionRecord (List (BitVec 8))}
    {ss : Session (List (BitVec 8))}
    (hgv : RecordGhostValid g_out0 r_out0)
    (hr : r_out0 = ⟨none⟩ ∨ r_out0 = ⟨some ss⟩)
    (hdom : SessionCloneDom 286196 ss) :
    (∀ G ses, g_out0.cur = some G → r_out0.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
    (encodeRecord r_out0).length ≤ 2097152 := by
  rcases hr with rfl | rfl
  · exact ⟨(fun _ _ _ hs => nomatch hs), w4pb_emptySessionRecord_enc⟩
  · cases hcur : g_out0.cur with
    | none =>
      unfold RecordGhostValid at hgv
      rw [hcur] at hgv
      exact nomatch hgv
    | some G_out =>
      have hgv_ss : SessionGhostValid G_out ss := by
        unfold RecordGhostValid at hgv
        rw [hcur] at hgv
        exact hgv
      refine ⟨?_, w4pb_encodeRecord_some_length_le hgv_ss hdom⟩
      intro G ses hg hs
      injection hg with hG
      injection hs with hses
      subst hG hses
      exact ⟨hgv_ss, hdom⟩

private theorem w4pb_preSession_bounds [LibsignalPlacement]
    {A : RustAlloc} {W : CliHooks} {g : DecPkGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val)
    (hload_rel : (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk cliRunBudgets)).loadRel
      StoresGhost.opened.sessions g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some sess) :
    scopeIn ⟨some sess⟩ ∧
    TopStateTight W.C.F W.Q.K sess.state.pqRatchetState ∧
    SessionCloneDom 286196 sess := by
  have hr_eq : r = ⟨some sess⟩ := by cases r; simpa using hcur
  subst hr_eq
  dsimp only [cliPollSessKitPlaced] at hload_rel
  have hloadK : (.ok (some ⟨some sess⟩)) = loadRec scopeKit g.F g.peer.val :=
    cliSessLoadRel_eq_loadRec encodeInjOn_deserializeScopeP_Q hload_rel
  have hloadS : loadRec scopeIn g.F g.peer.val = .ok (some ⟨some sess⟩) :=
    (loadRec_scopeKit_eq encodeInjOn_deserializeScopeP_Q (fun _ h => h) hfPeer).symm.trans
      hloadK.symm
  have hIn : scopeIn ⟨some sess⟩ := scope_of_loadRec_some hfPeer hloadS
  have hTop : TopStateTight W.C.F W.Q.K sess.state.pqRatchetState := by
    unfold PeerSpqrStateTight640 at hTight
    rw [← hloadK] at hTight
    exact hTight sess rfl
  have hdom4G := sessionCloneDom_of_scopeIn hIn rfl
  exact ⟨hIn, hTop,
    ⟨hdom4G.rc_len, hdom4G.seeds32, hdom4G.alice_len, hdom4G.kyber_cap,
      topStateTight_length_le hTop⟩⟩

private theorem w4pb_postSession_bounds_of_scopeIn
    (W : CliHooks) {g : DecPkGhost} {ses : Session (List (BitVec 8))} {pt : List (BitVec 8)}
    (hIn : scopeIn ⟨some ses⟩)
    (hTop_pre : TopStateTight W.C.F W.Q.K ses.state.pqRatchetState)
    (hver : ses.state.version = g.msg.message.messageVersion.zeroExtend 32)
    (hok : (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins ses.state).1 = .ok pt) :
    SessionCloneDom 286196
      { ses with
        state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins ses.state).2
        pendingPreKey := none
        pendingKyberPreKey := none } := by
  rcases hm : genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins ses.state with ⟨res, st'⟩
  rw [hm] at hok
  dsimp only at hok ⊢
  subst hok
  have hTryV1 : SessionState.tryDecryptFromRecord W.C (spqrV1 W.C.F W.Q.K).spqr
      (serializeAddresses (serviceIdParse uuidTryParse) g.peer g.me)
      g.msg.message .preKey (coinsOf g.coins) ses.state = (.ok pt, st') := by
    unfold SessionState.tryDecryptFromRecord
    have hnot_ne : ¬ (ses.state.version.toNat ≠ g.msg.message.messageVersion.toNat) :=
      not_not.mpr ((version_eq_zeroExtend_iff ses.state g.msg.message).mpr hver)
    simp only [hnot_ne, ↓reduceIte]
    have hm' : (SessionState.tryDecryptWithState W.C (spqrV1 W.C.F W.Q.K).spqr
        (serializeAddresses (serviceIdParse uuidTryParse) g.peer g.me)
        g.msg.message .preKey (coinsOf g.coins)).exec ses.state = (.ok pt, st') := hm
    rw [hm']
  have hTry : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession ⟨W.C, W.Q⟩)
      (serializeAddresses (serviceIdParse uuidTryParse) g.peer g.me)
      g.msg.message .preKey (coinsOf g.coins) ses.state = (.ok pt, st') := hTryV1
  have hKit_post :=
    (tryDecryptFromRecord_preKey_recOk_of_scopeIn (W := ⟨W.C, W.Q⟩) hIn hTry).1
  obtain ⟨salt, hspqr⟩ := w4pb_tryDecryptWithState_spqr W.C (spqrV1 W.C.F W.Q.K).spqr _ _ _ _
    ses.state st' pt hm
  have hTop_post := topStateTight_spqrV1_recv hTop_pre hspqr
  exact sessionCloneDom_of_scopeKit_pq hKit_post rfl (topStateTight_length_le hTop_post)

private theorem w4pb_stageP3OkPrefixEnv_sub_w4StageP3Wide
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : CryptoVerification.LibsignalTripleRatchetRepr.AddrGhost}
    {msgG : SignalMessageGhost} {msg : SignalMessage}
    {rest : List (BitVec 8)}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    (hTd : ∀ e, tdEnv (stageP3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) e → TryDecEnv e)
    {evs : List AllocEvent}
    (h : StageP3OkPrefixEnv tdEnv recG G₁ st rem loc msgG msg rest evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  w4StageP3WideEnv_of_okPrefix
    (w4pb_seqEnv_mono hClone (fun _ ht => w4pb_seqEnv_mono hTd (fun _ hf => hf) ht) h)

private theorem w4pb_stageP3ErrEnv_sub_w4StageP3Wide
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : CryptoVerification.LibsignalTripleRatchetRepr.AddrGhost}
    {msgG : SignalMessageGhost} {msg : SignalMessage}
    {rest : List (BitVec 8)}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    (hTd : ∀ e, tdEnv (stageP3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) e → TryDecEnv e)
    {evs : List AllocEvent}
    (h : StageP3ErrEnv tdEnv recG G₁ st rem loc msgG msg rest evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  w4StageP3WideEnv_of_err
    (w4pb_seqEnv_mono hClone (fun _ ht => w4pb_seqEnv_mono hTd (fun _ hv => hv) ht) h)

private theorem w4pb_stageP3VerNeEnv_sub_w4StageP3Wide
    {CloneEnv : List AllocEvent → Prop} (TryDecEnv : List AllocEvent → Prop)
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hClone : ∀ e, SegCloneEnv recG st e → CloneEnv e)
    {evs : List AllocEvent}
    (h : StageP3VerNeEnv recG st evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  w4StageP3WideEnv_of_verNe (w4pb_seqEnv_mono hClone (fun _ hm => hm) h)

/-- Embeds the Path-A disjunct of `W4r2PollCustomP3GvSeqFreeEnv` into `realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed`. -/
private theorem w4pb_pathA_sub_dom0' [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent)
    (hPathA :
      let σ := cliKitStk cliRunBudgets
      let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
      let sessKit := cliPollSessKitPlaced A g.F scopeKit g.peer σ
      let kitEnv := cliPollSessSeqFreeBudgetEnv A g.F g.peer σ dpx_deserEnv ReadEnv
      let idKit := cliPollIdKitPlaced A g.F g.peer σ
      let ikitEnv := cliPollIdBudgetEnv A g.F g.peer σ ReadEnv
      let P1 := CliStageP1OkEnv (A := A) cliRunBudgets ReadEnv dpx_deserEnv g
      let P2AErr := dpx_p2PathAErrEnv A X W
      let P2AOk := dpx_p2PathAOkEnv A X W
      let tdEnv := w4s2_TryDecryptTopStateGuardedEnv W
      sessKit.loadRel StoresGhost.opened.sessions g.peer.val (.ok none) ∧
        (SeqEnv P1 (StageP2PathAEnv P2AErr P2AOk g) evs ∨
         ∃ m i k kp reg dk recG,
           g.msg = pmOfE m i ∧
           SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
           pkStoreKeys g.F m = some k ∧
           StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
           StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
           SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
             (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
           W4r2SessionGhostValid recG
             (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
           (SeqEnv (SeqEnv P1 (P2AOk g))
              (StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
                g.peer g.me g.msgG.msg g.msg.message
                (g.msg.message.messageVersion.zeroExtend 32) g.coins) evs ∨
            ∃ G₁ G' pt,
              (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
                g.msg.message.messageVersion.zeroExtend 32 ∧
              CloneRel recG G₁ ∧
              G₁.AfterTryDecrypt true G' ∧
              (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
                (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt ∧
              let pid := pmPreKeyId g.msg
              let pkKit := cliPollPkKitPlaced A g.F pid σ
              let pkKitEnv := cliPollPkBudgetEnv A g.F pid σ ReadEnv
              let kpkKit := cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey σ
              let kpkKitEnv := cliPollKpkBudgetEnv A g.F m.kpkId m.spkId g.msg.baseKey σ ReadEnv
              let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
              SeqEnv
                (SeqEnv (SeqEnv P1 (P2AOk g))
                  (StageP3OkPrefixEnv tdEnv recG G₁ st0
                    g.peer g.me g.msgG.msg g.msg.message g.coins))
                (StageP4PathAEnv sessKit kitEnv idKit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
                  StoresGhost.opened.sessions StoresGhost.opened.identity
                  StoresGhost.opened.oneTime StoresGhost.opened.kyber
                  g.peer.val g.msg.identityKey m.opkId m.kpkId m.spkId g.msg.baseKey
                  { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
                    state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).2
                    pendingPreKey := none
                    pendingKyberPreKey := none }) evs))) :
    realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam X W g evs := by
  obtain ⟨G_idle, ses_idle, hOut1⟩ := postBobPrev1Dom_idle_exists
  dsimp only at hPathA
  rcases hPathA with ⟨_hloadNone, hA1 | ⟨m, i, k, kp, reg, dk, recG,
      hmsg, htry, _hpk, _hkp, _hreg, _hdk, hgv, hA2 | hA3⟩⟩
  · obtain ⟨e1, e2, rfl, hp1, rfl | hp2⟩ := w4pb_seqEnv_split_opt hA1
    · rw [List.append_nil]
      let w := w4pb_mkPathAParams W g G_idle ses_idle false 0#32 0#32 0#32
        w4pb_dummyInitialStateGhost false (w4pb_dummyTdCall G_idle ses_idle.state g)
        w4pb_noneRecordGhost w4pb_emptySessionRecord
      exact ⟨w,
        w4pb_mkPathAParams_dom0' W g G_idle ses_idle hOut1 false 0#32 0#32 0#32
          w4pb_dummyInitialStateGhost w4pb_dummyInitialStateGhost_key
          false (w4pb_dummyTdCall G_idle ses_idle.state g) (fun h => Bool.noConfusion h)
          w4pb_noneRecordGhost w4pb_emptySessionRecord w4pb_none_out0_valid w4pb_emptySessionRecord_enc,
        rfl, rfl,
        Or.inr (Or.inl (Or.inr (Or.inr (Or.inl
          (Or.inl (dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1))))))⟩
    · have hp1' := dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1
      have hp2_ex : ∃ (m' : PreKeyMessageFields) (x_spqr : InitialStateGhost),
          x_spqr.p.authKey.length ≤ 32 ∧
          W4BinaryStageP2PathAWideEnvAllFixed m'.opkId.isSome cliIo.rd g.F
            m'.spkId m'.kpkId (m'.opkId.getD 0#32) W.C.F w4pb_dummyReserve x_spqr e2 := by
        rcases hp2 with hp2e | hp2ok
        · obtain ⟨m', x_spqr, _, _, hlen, hw4⟩ :=
            dpx_p2PathAErrEnv_sub_w4StageP2PathAFull9 w4pb_dummyReserve hp2e
          exact ⟨m', x_spqr, hlen, hw4⟩
        · obtain ⟨m', x_spqr, _, _, hlen, hw4⟩ :=
            dpx_p2PathAOkEnv_sub_w4StageP2PathAFull9 w4pb_dummyReserve hp2ok
          exact ⟨m', x_spqr, hlen, hw4⟩
      obtain ⟨m', x_spqr, hspqr_len, hp2_w4⟩ := hp2_ex
      let w := w4pb_mkPathAParams W g G_idle ses_idle m'.opkId.isSome m'.spkId m'.kpkId
        (m'.opkId.getD 0#32) x_spqr false (w4pb_dummyTdCall G_idle ses_idle.state g)
        w4pb_noneRecordGhost w4pb_emptySessionRecord
      have htr := w4pb_mkPathATrace hp1' (Or.inr hp2_w4)
        (optStageEnv_nil (W4StageP3WideEnv W4CloneACDomEnv
          (W4RecvPrekeyTryDecACCmkSrEnvOf w4c_repairedStatesRecvEnvFam
            CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps w.base)))
        (optStageEnv_nil (W4BinaryStageP4PathAWideEnvAllFixed w.base.hasOpk w.base.rd
          w.base.files w.base.peer w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId
          w.baseKey w.base.g_out0 w.base.r_out0))
      simp only [List.append_nil] at htr
      exact ⟨w,
        w4pb_mkPathAParams_dom0' W g G_idle ses_idle hOut1 m'.opkId.isSome m'.spkId m'.kpkId
          (m'.opkId.getD 0#32) x_spqr hspqr_len
          false (w4pb_dummyTdCall G_idle ses_idle.state g) (fun h => Bool.noConfusion h)
          w4pb_noneRecordGhost w4pb_emptySessionRecord w4pb_none_out0_valid w4pb_emptySessionRecord_enc,
        rfl, rfl,
        Or.inr (Or.inl (Or.inr (Or.inr (Or.inl htr))))⟩
  · let me0 := (⟨kp.privateKey.bytes, reg⟩ : CryptoVerification.E2E.LocalIdentity)
    let st0 := pathAInitState ⟨W.C, W.Q⟩ me0 k m dk
    have hgv0 : SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ me0 k m dk) := hgv
    have hTop0 : TopStateTight W.C.F W.Q.K st0.pqRatchetState :=
      h7l45r_pathAInit_topStateTight ⟨W.C, W.Q⟩ me0 k m dk
    have hClone : ∀ e, SegCloneEnv recG st0 e → W4CloneACDomEnv e :=
      fun _ he => h7l45r_pathAInit_segClone_sub_w4CloneACDomEnv ⟨W.C, W.Q⟩ me0 k m dk recG hgv0 he
    obtain ⟨e12, e3, rfl, hp12, h3_or⟩ := w4pb_seqEnv_split_opt hA2
    obtain ⟨e1, e2, rfl, hp1, h2_or⟩ := w4pb_seqEnv_split_opt hp12
    have hp1' := dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1
    obtain ⟨x_spqr, hspqr_len, hp2_opt⟩ := w4pb_p2AOk_opt_fixed hmsg htry h2_or
    have hp3_ex :
        ∃ (isPathAC : Bool) (td_AC : W4TryDecryptCallCmk),
          (isPathAC = true →
            W4TryDecryptPathACDomCmkOf W.C.F W.Q.K g.msg.message.ciphertext.length td_AC) ∧
          OptStageEnv
            (W4StageP3WideEnv W4CloneACDomEnv
              (fun evs =>
                if isPathAC then
                  w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam
                    CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps W.C W.Q.K td_AC.a evs
                else False)) e3 := by
      rcases h3_or with rfl | hp3env
      · exact ⟨false, w4pb_dummyTdCall G_idle ses_idle.state g,
          fun h => Bool.noConfusion h, optStageEnv_nil _⟩
      · unfold StageP3Env at hp3env
        split at hp3env
        · obtain ⟨G₁, _, hp3err⟩ := hp3env
          let td_AC : W4TryDecryptCallCmk :=
            ⟨stageP3TryDecryptEnvArgs G₁ st0 g.peer g.me g.msgG.msg g.msg.message g.coins⟩
          have htd_dom :
              W4TryDecryptPathACDomCmkOf W.C.F W.Q.K g.msg.message.ciphertext.length td_AC :=
            h7l45r_pathAInit_tdAC_dom ⟨W.C, W.Q⟩ me0 k m dk td_AC rfl (Nat.le_refl _)
          have hp3err' :
              SeqEnv W4CloneACDomEnv
                (SeqEnv
                  (w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam
                    CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps W.C W.Q.K td_AC.a)
                  FromVPostTdEnv) e3 := by
            have heq := w4pb_tdGuarded_eq_w4c W td_AC.a hTop0
            unfold StageP3ErrEnv at hp3err
            exact w4pb_seqEnv_mono hClone
              (fun _ ht => w4pb_seqEnv_mono (fun _ hd => heq ▸ hd) (fun _ hv => hv) ht)
              hp3err
          exact ⟨true, td_AC, fun _ => htd_dom, Or.inr (w4StageP3WideEnv_of_err hp3err')⟩
        · have hp3vn : SeqEnv W4CloneACDomEnv FromMEnv e3 :=
            w4pb_seqEnv_mono hClone (fun _ hm => hm) hp3env
          exact ⟨false, w4pb_dummyTdCall G_idle ses_idle.state g,
            fun h => Bool.noConfusion h, Or.inr (w4StageP3WideEnv_of_verNe hp3vn)⟩
    obtain ⟨isPathAC, td_AC, htd_dom, hp3_opt⟩ := hp3_ex
    let w := w4pb_mkPathAParams W g G_idle ses_idle m.opkId.isSome m.spkId m.kpkId
      (m.opkId.getD 0#32) x_spqr isPathAC td_AC
      w4pb_noneRecordGhost w4pb_emptySessionRecord
    have htr := w4pb_mkPathATrace hp1' hp2_opt hp3_opt
      (optStageEnv_nil (W4BinaryStageP4PathAWideEnvAllFixed w.base.hasOpk w.base.rd
        w.base.files w.base.peer w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId
        w.baseKey w.base.g_out0 w.base.r_out0))
    simp only [List.append_nil] at htr
    rw [← List.append_assoc] at htr
    exact ⟨w,
      w4pb_mkPathAParams_dom0' W g G_idle ses_idle hOut1 m.opkId.isSome m.spkId m.kpkId
        (m.opkId.getD 0#32) x_spqr hspqr_len isPathAC td_AC htd_dom
        w4pb_noneRecordGhost w4pb_emptySessionRecord w4pb_none_out0_valid w4pb_emptySessionRecord_enc,
      rfl, rfl,
      Or.inr (Or.inl (Or.inr (Or.inr (Or.inl htr))))⟩
  · obtain ⟨G₁, _G', pt, _hver, _hclone, _hafter, hok, hseq4⟩ := hA3
    let me0 := (⟨kp.privateKey.bytes, reg⟩ : CryptoVerification.E2E.LocalIdentity)
    let st0 := pathAInitState ⟨W.C, W.Q⟩ me0 k m dk
    have hgv0 : SessionGhostValid recG (pathAInitSession ⟨W.C, W.Q⟩ me0 k m dk) := hgv
    have hTop0 : TopStateTight W.C.F W.Q.K st0.pqRatchetState :=
      h7l45r_pathAInit_topStateTight ⟨W.C, W.Q⟩ me0 k m dk
    have hClone : ∀ e, SegCloneEnv recG st0 e → W4CloneACDomEnv e :=
      fun _ he => h7l45r_pathAInit_segClone_sub_w4CloneACDomEnv ⟨W.C, W.Q⟩ me0 k m dk recG hgv0 he
    have hp_ok :
        genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0 =
          (.ok pt, (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).2) :=
      Prod.ext hok rfl
    obtain ⟨hdom_ss', hrc1_ss'⟩ :=
      sessionCloneDom_postBob_of_genP3S5Model_ok ⟨W.C, W.Q⟩ me0 k m dk
        g.peer g.me g.msg.message g.coins hp_ok
    obtain ⟨e123, e4, rfl, hp123, h4_or⟩ := w4pb_seqEnv_split_opt hseq4
    obtain ⟨e12, e3, rfl, hp12, h3_or⟩ := w4pb_seqEnv_split_opt hp123
    obtain ⟨e1, e2, rfl, hp1, h2_or⟩ := w4pb_seqEnv_split_opt hp12
    have hp1' := dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1
    obtain ⟨x_spqr, hspqr_len, hp2_opt⟩ := w4pb_p2AOk_opt_fixed hmsg htry h2_or
    let td_AC : W4TryDecryptCallCmk :=
      ⟨stageP3TryDecryptEnvArgs G₁ st0 g.peer g.me g.msgG.msg g.msg.message g.coins⟩
    have htd_dom :
        W4TryDecryptPathACDomCmkOf W.C.F W.Q.K g.msg.message.ciphertext.length td_AC :=
      h7l45r_pathAInit_tdAC_dom ⟨W.C, W.Q⟩ me0 k m dk td_AC rfl (Nat.le_refl _)
    have hp3_opt :
        OptStageEnv
          (W4StageP3WideEnv W4CloneACDomEnv
            (w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam
              CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps W.C W.Q.K td_AC.a)) e3 := by
      rcases h3_or with rfl | hp3ok
      · exact optStageEnv_nil _
      · have heq := w4pb_tdGuarded_eq_w4c W td_AC.a hTop0
        unfold StageP3OkPrefixEnv at hp3ok
        have hp3ok' :
            SeqEnv W4CloneACDomEnv
              (SeqEnv
                (w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam
                  CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps W.C W.Q.K td_AC.a)
                FreeOnlyEvs) e3 :=
          w4pb_seqEnv_mono hClone
            (fun _ ht => w4pb_seqEnv_mono (fun _ hd => heq ▸ hd) (fun _ hf => hf) ht)
            hp3ok
        exact Or.inr (w4StageP3WideEnv_of_okPrefix hp3ok')
    have hp4_ex :
        ∃ (g_out0 : RecordGhost) (r_out0 : SessionRecord (List (BitVec 8))),
          (∀ G ses, g_out0.cur = some G → r_out0.currentSession = some ses →
            SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
          (encodeRecord r_out0).length ≤ 2097152 ∧
          OptStageEnv
            (W4BinaryStageP4PathAWideEnvAllFixed m.opkId.isSome cliIo.rd g.F g.peer
              g.msg.identityKey m.kpkId m.spkId (m.opkId.getD 0#32) g.msg.baseKey
              g_out0 r_out0) e4 := by
      rcases h4_or with rfl | hp4
      · exact ⟨w4pb_noneRecordGhost, w4pb_emptySessionRecord,
          w4pb_none_out0_valid, w4pb_emptySessionRecord_enc, optStageEnv_nil _⟩
      · obtain ⟨g_out0, r_out0, hgv_out0, hr_or, hp4_w4⟩ :=
          dpx_stageP4PathASeqFree_sub_w4StageP4PathAAllFixed hp4
        obtain ⟨hout0_valid, hout0_enc⟩ :=
          w4pb_out0_bounds_postBob hgv_out0 hr_or hdom_ss' hrc1_ss'
        exact ⟨g_out0, r_out0, hout0_valid, hout0_enc, Or.inr hp4_w4⟩
    obtain ⟨g_out0, r_out0, hout0_valid, hout0_enc, hp4_opt⟩ := hp4_ex
    let w := w4pb_mkPathAParams W g G_idle ses_idle m.opkId.isSome m.spkId m.kpkId
      (m.opkId.getD 0#32) x_spqr true td_AC g_out0 r_out0
    have htr := w4pb_mkPathATrace hp1' hp2_opt hp3_opt hp4_opt
    have hevs_eq : ((e1 ++ e2) ++ e3) ++ e4 = e1 ++ (e2 ++ (e3 ++ e4)) := by
      simp [List.append_assoc]
    rw [← hevs_eq] at htr
    exact ⟨w,
      w4pb_mkPathAParams_dom0' W g G_idle ses_idle hOut1 m.opkId.isSome m.spkId m.kpkId
        (m.opkId.getD 0#32) x_spqr hspqr_len true td_AC (fun _ => htd_dom)
        g_out0 r_out0 hout0_valid hout0_enc,
      rfl, rfl,
      Or.inr (Or.inl (Or.inr (Or.inr (Or.inl htr))))⟩

/-- Embeds the Path-B (`Matched`) disjunct of `W4r2PollCustomP3GvSeqFreeEnv` into `realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed`. -/
private theorem w4pb_pathB_sub_dom0' [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent)
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val)
    (hPathB :
      let σ := cliKitStk cliRunBudgets
      let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
      let sessKit := cliPollSessKitPlaced A g.F scopeKit g.peer σ
      let kitEnv := cliPollSessSeqFreeBudgetEnv A g.F g.peer σ dpx_deserEnv ReadEnv
      let idKit := cliPollIdKitPlaced A g.F g.peer σ
      let ikitEnv := cliPollIdBudgetEnv A g.F g.peer σ ReadEnv
      let P1 := CliStageP1OkEnv (A := A) cliRunBudgets ReadEnv dpx_deserEnv g
      let tdEnv := w4s2_TryDecryptTopStateGuardedEnv W
      ∃ (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8))),
        sessKit.loadRel StoresGhost.opened.sessions g.peer.val (.ok (some r)) ∧
        r.currentSession = some sess ∧
        (SeqEnv P1 (StageP2MatchedEnv sess g.msg.identityKey) evs ∨
         (sess.state.remoteIdentity = some g.msg.identityKey ∧
          ∃ recG, W4r2SessionGhostValid recG sess ∧
            (SeqEnv (SeqEnv P1 StageP2MatchedBridgeEnv)
               (StageP3Env tdEnv recG sess.state g.peer g.me g.msgG.msg g.msg.message
                 (g.msg.message.messageVersion.zeroExtend 32) g.coins) evs ∨
             (sess.state.version = g.msg.message.messageVersion.zeroExtend 32 ∧
              ∃ G₁ G' pt,
                CloneRel recG G₁ ∧
                G₁.AfterTryDecrypt true G' ∧
                (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).1 = .ok pt ∧
                SeqEnv
                  (SeqEnv (SeqEnv P1 StageP2MatchedBridgeEnv)
                    (StageP3OkPrefixEnv tdEnv recG G₁ sess.state
                      g.peer g.me g.msgG.msg g.msg.message g.coins))
                  (StageP4MatchedEnv sessKit kitEnv idKit ikitEnv
                    StoresGhost.opened.sessions StoresGhost.opened.identity
                    g.peer.val g.msg.identityKey
                    { sess with
                      state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).2
                      pendingPreKey := none
                      pendingKyberPreKey := none })
                  evs))))) :
    realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam X W g evs := by
  obtain ⟨G_idle, ses_idle, hOut1⟩ := postBobPrev1Dom_idle_exists
  dsimp only at hPathB
  let w_idle := w4pb_mkPathBParams W g G_idle ses_idle false
    (w4pb_dummyTdCall G_idle ses_idle.state g) w4pb_noneRecordGhost w4pb_emptySessionRecord
  have hdom_idle :
      W4BinaryCallSiteDomCmk0' W.C W.Q.K g.msg.message.ciphertext.length g.peer.val g.F
        w_idle.base :=
    w4pb_mkPathBParams_dom0' W g G_idle ses_idle hOut1 false
      (w4pb_dummyTdCall G_idle ses_idle.state g) (fun h => Bool.noConfusion h)
      w4pb_noneRecordGhost w4pb_emptySessionRecord w4pb_none_out0_valid w4pb_emptySessionRecord_enc
  obtain ⟨r, sess, hload_rel, hcur, hmain⟩ := hPathB
  obtain ⟨hIn, hTop_pre, hdom_pre⟩ := w4pb_preSession_bounds hfPeer hTight hload_rel hcur
  rcases hmain with hB1 | ⟨_hrem, recG, hgv, hB2 | ⟨hver, G₁, _G', pt, _hclone, _hafter, hok, hB3⟩⟩
  ·
    obtain ⟨e1, e2, rfl, hp1, rfl | hp2m⟩ := w4pb_seqEnv_split_opt hB1
    · rw [List.append_nil]
      exact ⟨w_idle, hdom_idle, rfl, rfl,
        Or.inr (Or.inl (Or.inr (Or.inl
          (Or.inl (dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1)))))⟩
    · exact ⟨w_idle, hdom_idle, rfl, rfl,
        Or.inr (Or.inl (Or.inr (Or.inl (Or.inr
          ⟨e1, e2, rfl, dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1,
            Or.inl (Or.inr (dpx_stageP2MatchedEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2m))⟩))))⟩
  ·
    have hgv0 : SessionGhostValid recG sess := hgv
    have hClone : ∀ e, SegCloneEnv recG sess.state e → W4CloneBDomEnv e :=
      fun e hseg => ⟨recG, sess, hgv0, hdom_pre, hseg⟩
    obtain ⟨e12, e3, rfl, hp12, rfl | hp3env⟩ := w4pb_seqEnv_split_opt hB2
    · rw [List.append_nil]
      obtain ⟨e1, e2, rfl, hp1, rfl | hp2br⟩ := w4pb_seqEnv_split_opt hp12
      · rw [List.append_nil]
        exact ⟨w_idle, hdom_idle, rfl, rfl,
          Or.inr (Or.inl (Or.inr (Or.inl
            (Or.inl (dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1)))))⟩
      · exact ⟨w_idle, hdom_idle, rfl, rfl,
          Or.inr (Or.inl (Or.inr (Or.inl (Or.inr
            ⟨e1, e2, rfl, dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1,
              Or.inl (Or.inr
                (dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2br))⟩))))⟩
    · obtain ⟨e1, e2, rfl, hp1, h2_or⟩ := w4pb_seqEnv_split_opt hp12
      have hp1' := dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1
      unfold StageP3Env at hp3env
      by_cases hver : sess.state.version = g.msg.message.messageVersion.zeroExtend 32
      · simp only [hver, ↓reduceIte] at hp3env
        obtain ⟨G₁, _, hp3err⟩ := hp3env
        let td_B : W4TryDecryptCallCmk :=
          ⟨stageP3TryDecryptEnvArgs G₁ sess.state g.peer g.me g.msgG.msg g.msg.message g.coins⟩
        have htdB_dom :
            W4TryDecryptCallDomCmkOf W.C.F W.Q.K g.msg.message.ciphertext.length td_B :=
          ⟨hdom_pre.rc_len, w4pb_mk_len_le_of_sessionGhostValid hgv0, hTop_pre, Nat.le_refl _⟩
        have heq := w4pb_tdGuarded_eq_w4c W td_B.a hTop_pre
        have hp3' :
            W4StageP3WideEnv W4CloneBDomEnv
              (w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam
                CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps W.C W.Q.K td_B.a) e3 :=
          w4pb_stageP3ErrEnv_sub_w4StageP3Wide hClone (fun _ hd => heq ▸ hd) hp3err
        exact ⟨w4pb_mkPathBParams W g G_idle ses_idle true td_B
            w4pb_noneRecordGhost w4pb_emptySessionRecord,
          w4pb_mkPathBParams_dom0' W g G_idle ses_idle hOut1 true td_B (fun _ => htdB_dom)
            w4pb_noneRecordGhost w4pb_emptySessionRecord
            w4pb_none_out0_valid w4pb_emptySessionRecord_enc,
          rfl, rfl,
          Or.inr (Or.inl (Or.inr (Or.inl (Or.inr
            ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3, hp1',
              Or.inr ⟨e2, e3, rfl,
                by
                  rcases h2_or with rfl | hp2br
                  · exact optStageEnv_nil _
                  · exact Or.inr
                      (dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2br),
                Or.inl (Or.inr hp3')⟩⟩))))⟩
      · simp only [hver, ↓reduceIte] at hp3env
        exact ⟨w_idle, hdom_idle, rfl, rfl,
          Or.inr (Or.inl (Or.inr (Or.inl (Or.inr
            ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3, hp1',
              Or.inr ⟨e2, e3, rfl,
                by
                  rcases h2_or with rfl | hp2br
                  · exact optStageEnv_nil _
                  · exact Or.inr
                      (dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2br),
                Or.inl (Or.inr (w4pb_stageP3VerNeEnv_sub_w4StageP3Wide _ hClone hp3env))⟩⟩))))⟩
  ·
    have hgv0 : SessionGhostValid recG sess := hgv
    have hClone : ∀ e, SegCloneEnv recG sess.state e → W4CloneBDomEnv e :=
      fun e hseg => ⟨recG, sess, hgv0, hdom_pre, hseg⟩
    let td_B : W4TryDecryptCallCmk :=
      ⟨stageP3TryDecryptEnvArgs G₁ sess.state g.peer g.me g.msgG.msg g.msg.message g.coins⟩
    have htdB_dom :
        W4TryDecryptCallDomCmkOf W.C.F W.Q.K g.msg.message.ciphertext.length td_B :=
      ⟨hdom_pre.rc_len, w4pb_mk_len_le_of_sessionGhostValid hgv0, hTop_pre, Nat.le_refl _⟩
    have heq := w4pb_tdGuarded_eq_w4c W td_B.a hTop_pre
    obtain ⟨e123, e4, rfl, hp123, rfl | hp4⟩ := w4pb_seqEnv_split_opt hB3
    · rw [List.append_nil]
      obtain ⟨e12, e3, rfl, hp12, rfl | hp3ok⟩ := w4pb_seqEnv_split_opt hp123
      · rw [List.append_nil]
        obtain ⟨e1, e2, rfl, hp1, rfl | hp2br⟩ := w4pb_seqEnv_split_opt hp12
        · rw [List.append_nil]
          exact ⟨w_idle, hdom_idle, rfl, rfl,
            Or.inr (Or.inl (Or.inr (Or.inl
              (Or.inl (dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1)))))⟩
        · exact ⟨w_idle, hdom_idle, rfl, rfl,
            Or.inr (Or.inl (Or.inr (Or.inl (Or.inr
              ⟨e1, e2, rfl, dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1,
                Or.inl (Or.inr
                  (dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2br))⟩))))⟩
      · obtain ⟨e1, e2, rfl, hp1, h2_or⟩ := w4pb_seqEnv_split_opt hp12
        have hp1' := dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1
        have hp3' :
            W4StageP3WideEnv W4CloneBDomEnv
              (w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam
                CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps W.C W.Q.K td_B.a) e3 :=
          w4pb_stageP3OkPrefixEnv_sub_w4StageP3Wide hClone (fun _ hd => heq ▸ hd) hp3ok
        exact ⟨w4pb_mkPathBParams W g G_idle ses_idle true td_B
            w4pb_noneRecordGhost w4pb_emptySessionRecord,
          w4pb_mkPathBParams_dom0' W g G_idle ses_idle hOut1 true td_B (fun _ => htdB_dom)
            w4pb_noneRecordGhost w4pb_emptySessionRecord
            w4pb_none_out0_valid w4pb_emptySessionRecord_enc,
          rfl, rfl,
          Or.inr (Or.inl (Or.inr (Or.inl (Or.inr
            ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3, hp1',
              Or.inr ⟨e2, e3, rfl,
                by
                  rcases h2_or with rfl | hp2br
                  · exact optStageEnv_nil _
                  · exact Or.inr
                      (dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2br),
                Or.inl (Or.inr hp3')⟩⟩))))⟩
    · obtain ⟨e12, e3, rfl, hp12, h3_or⟩ := w4pb_seqEnv_split_opt hp123
      obtain ⟨e1, e2, rfl, hp1, h2_or⟩ := w4pb_seqEnv_split_opt hp12
      have hp1' := dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1
      have hdom_post := w4pb_postSession_bounds_of_scopeIn W hIn hTop_pre hver hok
      obtain ⟨g_out0, r_out0, hgv_out0, hr_out0, hp4'⟩ :=
        dpx_stageP4MatchedSeqFree_sub_w4StageP4MatchedAllFixed hp4
      obtain ⟨hout0_valid, hout0_enc⟩ := w4pb_out0_bounds_of_p4 hgv_out0 hr_out0 hdom_post
      have hevs_eq : ((e1 ++ e2) ++ e3) ++ e4 = e1 ++ (e2 ++ (e3 ++ e4)) := by
        simp [List.append_assoc]
      have hp3_opt :
          OptStageEnv
            (W4StageP3WideEnv W4CloneBDomEnv
              (w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam
                CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps W.C W.Q.K td_B.a)) e3 := by
        rcases h3_or with rfl | hp3ok
        · exact optStageEnv_nil _
        · exact Or.inr
            (w4pb_stageP3OkPrefixEnv_sub_w4StageP3Wide hClone (fun _ hd => heq ▸ hd) hp3ok)
      exact ⟨w4pb_mkPathBParams W g G_idle ses_idle true td_B g_out0 r_out0,
        w4pb_mkPathBParams_dom0' W g G_idle ses_idle hOut1 true td_B (fun _ => htdB_dom)
          g_out0 r_out0 hout0_valid hout0_enc,
        rfl, rfl,
        Or.inr (Or.inl (Or.inr (Or.inl (Or.inr
          ⟨e1, e2 ++ (e3 ++ e4), hevs_eq, hp1',
            Or.inr ⟨e2, e3 ++ e4, rfl,
              by
                rcases h2_or with rfl | hp2br
                · exact optStageEnv_nil _
                · exact Or.inr
                    (dpx_stageP2MatchedBridgeEnv_sub_w4StageP2MatchedWide _ _ _ _ _ _ hp2br),
              Or.inr ⟨e3, e4, rfl, hp3_opt, Or.inr hp4'⟩⟩⟩))))⟩

/-- Embeds both the Path-A and Path-B disjuncts of `W4r2PollCustomP3GvSeqFreeEnv` into `realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed`. -/
theorem w4pb_armAB_sub_dom0' [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent)
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val)
    (hPrev0 : SessionGetPrev0Guard g.F g.peer.val)
    (h :
      let σ := cliKitStk cliRunBudgets
      let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
      let sessKit := cliPollSessKitPlaced A g.F scopeKit g.peer σ
      let kitEnv := cliPollSessSeqFreeBudgetEnv A g.F g.peer σ dpx_deserEnv ReadEnv
      let idKit := cliPollIdKitPlaced A g.F g.peer σ
      let ikitEnv := cliPollIdBudgetEnv A g.F g.peer σ ReadEnv
      let P1 := CliStageP1OkEnv (A := A) cliRunBudgets ReadEnv dpx_deserEnv g
      let P2AErr := dpx_p2PathAErrEnv A X W
      let P2AOk := dpx_p2PathAOkEnv A X W
      let tdEnv := w4s2_TryDecryptTopStateGuardedEnv W
      (sessKit.loadRel StoresGhost.opened.sessions g.peer.val (.ok none) ∧
        (SeqEnv P1 (StageP2PathAEnv P2AErr P2AOk g) evs ∨
         ∃ m i k kp reg dk recG,
           g.msg = pmOfE m i ∧
           SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
           pkStoreKeys g.F m = some k ∧
           StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
           StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
           SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
             (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
           W4r2SessionGhostValid recG
             (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
           (SeqEnv (SeqEnv P1 (P2AOk g))
              (StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
                g.peer g.me g.msgG.msg g.msg.message
                (g.msg.message.messageVersion.zeroExtend 32) g.coins) evs ∨
            ∃ G₁ G' pt,
              (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
                g.msg.message.messageVersion.zeroExtend 32 ∧
              CloneRel recG G₁ ∧
              G₁.AfterTryDecrypt true G' ∧
              (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
                (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt ∧
              let pid := pmPreKeyId g.msg
              let pkKit := cliPollPkKitPlaced A g.F pid σ
              let pkKitEnv := cliPollPkBudgetEnv A g.F pid σ ReadEnv
              let kpkKit := cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey σ
              let kpkKitEnv := cliPollKpkBudgetEnv A g.F m.kpkId m.spkId g.msg.baseKey σ ReadEnv
              let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
              SeqEnv
                (SeqEnv (SeqEnv P1 (P2AOk g))
                  (StageP3OkPrefixEnv tdEnv recG G₁ st0
                    g.peer g.me g.msgG.msg g.msg.message g.coins))
                (StageP4PathAEnv sessKit kitEnv idKit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
                  StoresGhost.opened.sessions StoresGhost.opened.identity
                  StoresGhost.opened.oneTime StoresGhost.opened.kyber
                  g.peer.val g.msg.identityKey m.opkId m.kpkId m.spkId g.msg.baseKey
                  { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
                    state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).2
                    pendingPreKey := none
                    pendingKyberPreKey := none }) evs))) ∨
      (∃ (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8))),
        sessKit.loadRel StoresGhost.opened.sessions g.peer.val (.ok (some r)) ∧
        r.currentSession = some sess ∧
        (SeqEnv P1 (StageP2MatchedEnv sess g.msg.identityKey) evs ∨
         (sess.state.remoteIdentity = some g.msg.identityKey ∧
          ∃ recG, W4r2SessionGhostValid recG sess ∧
            (SeqEnv (SeqEnv P1 StageP2MatchedBridgeEnv)
               (StageP3Env tdEnv recG sess.state g.peer g.me g.msgG.msg g.msg.message
                 (g.msg.message.messageVersion.zeroExtend 32) g.coins) evs ∨
             (sess.state.version = g.msg.message.messageVersion.zeroExtend 32 ∧
              ∃ G₁ G' pt,
                CloneRel recG G₁ ∧
                G₁.AfterTryDecrypt true G' ∧
                (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).1 = .ok pt ∧
                SeqEnv
                  (SeqEnv (SeqEnv P1 StageP2MatchedBridgeEnv)
                    (StageP3OkPrefixEnv tdEnv recG G₁ sess.state
                      g.peer g.me g.msgG.msg g.msg.message g.coins))
                  (StageP4MatchedEnv sessKit kitEnv idKit ikitEnv
                    StoresGhost.opened.sessions StoresGhost.opened.identity
                    g.peer.val g.msg.identityKey
                    { sess with
                      state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins sess.state).2
                      pendingPreKey := none
                      pendingKyberPreKey := none })
                  evs)))))) :
    realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam X W g evs := by
  let _ := hdecOk
  let _ := hPrev0
  rcases h with hPathA | hPathB
  · exact w4pb_pathA_sub_dom0' A X W g evs hPathA
  · exact w4pb_pathB_sub_dom0' A X W g evs hfPeer hTight hPathB

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmAB

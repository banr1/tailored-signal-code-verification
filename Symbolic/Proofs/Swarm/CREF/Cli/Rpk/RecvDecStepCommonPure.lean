/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Actions.ProtocolEvent
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Receiver-Chain State Relation, Chain Stepping, and Trace Tail Lemmas

Relates model receiver chains to `TRState.recv` under `StateRel`, connects `chainStepN` and
`skippedKeys` to `chainKeyAt` and `kdfCk` under `gamma`, and proves trace-event lemmas for
`decTailTr` and `logSkippedKeysTr`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR

cref_open
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain setRecvChain chainKeyAt kdfCk litByte)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.SessionModel (chainStepN skippedKeys)
open CryptoVerification.SessionModel.AdvanceAndFrame
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec
  receiverChainToChainRec)

theorem recChainOfErased_modelRecvChainOfTr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (c : RecvChain) (hrk : (gamma interpretation S g c.ratchetKey).length = 32)
    (hck : (gamma interpretation S g c.chainKey).length = 32) :
    recChainOfErased (modelRecvChainOfTr interpretation S g c) =
      { senderRatchetKey := Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g c.ratchetKey), senderRatchetKeyPrivate := []
        chainKey := some (c.index.toBitVec, gamma interpretation S g c.chainKey), messageKeys := [] } := by
  unfold recChainOfErased modelRecvChainOfTr
  simp only [Option.map_some, PublicKey.serialize, djbType,
    Symbolic.Swarm.CREF.TR.serializedKey, ecKey,
    keyToBytes32_bytesToKey32_tr _ hck, vec32_toList_of_length_eq_tr hrk]; rfl
theorem receiverChains_of_stateRel_tr {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s)) :
    (s.state.receiverChains.map eraseRecvChain).map recChainOfErased =
      (sessionOf interpretation (gamma interpretation S g) st).receiverChains := by
  rw [← congrArg SessionRec.receiverChains ((stateRel_sessionToRecordRec_iff_tr interpretation S g st s).mp hrel)]
  simp only [eraseSkipped, eraseUnmodelled, sessionToSessionRec, List.map_map]; rfl
theorem rkLens_of_stateRel_tr {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s)) :
    ∀ c ∈ st.recv, (gamma interpretation S g c.ratchetKey).length = 32 := by
  intro c hc
  have h1 := congrArg (List.map ChainRec.senderRatchetKey) (receiverChains_of_stateRel_tr hrel)
  simp only [sessionOf, List.map_map, Function.comp_def] at h1
  have hmem : Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g c.ratchetKey) ∈
      List.map (fun x => Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g x.ratchetKey)) st.recv :=
    List.mem_map_of_mem hc
  rw [← h1, List.mem_map] at hmem
  obtain ⟨rc, _, hrc⟩ := hmem
  unfold recChainOfErased eraseRecvChain PublicKey.serialize
    Symbolic.Swarm.CREF.TR.serializedKey ecKey at hrc
  dsimp only at hrc
  injection hrc with _ hbytes
  rw [← hbytes]
  exact rc.senderRatchetKey.bytes.2
theorem recvMap_of_stateRel_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32) :
    s.state.receiverChains.map eraseRecvChain = st.recv.map (modelRecvChainOfTr interpretation S g) := by
  have hRkLens := rkLens_of_stateRel_tr hrel
  have hmodel : st.recv.map (modelRecvChainOfTr interpretation S g) =
      (st.recv.map (modelRecvChainOfTr interpretation S g)).map eraseRecvChain := by simp [List.map_map, Function.comp_def]
  rw [hmodel]; apply map_erase_eq_of_map_recChainOfErased
  rw [← hmodel, receiverChains_of_stateRel_tr hrel, List.map_map]; unfold sessionOf; dsimp only
  exact List.map_congr_left fun c hc => (recChainOfErased_modelRecvChainOfTr interpretation S g c (hRkLens c hc) (hCkLens c hc)).symm
theorem stateRel_of_recvMap_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    {recv' : List RecvChain} {chains' : List ReceiverChain} {spqr' : DY.Bytes} {newPqrState : List (BitVec 8)}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (hRkLens' : ∀ c ∈ recv', (gamma interpretation S g c.ratchetKey).length = 32)
    (hCkLens' : ∀ c ∈ recv', (gamma interpretation S g c.chainKey).length = 32)
    (hspqr' : gamma interpretation S g spqr' = newPqrState)
    (hMap' : chains'.map eraseRecvChain = recv'.map (modelRecvChainOfTr interpretation S g)) :
    StateRel interpretation S g { st with recv := recv', spqr := spqr' }
      (sessionToRecordRec { s with state := { s.state with receiverChains := chains', pqRatchetState := newPqrState } }) := by
  have heq := (stateRel_sessionToRecordRec_iff_tr interpretation S g st s).mp hrel
  rw [stateRel_sessionToRecordRec_iff_tr]
  have hrc' : (chains'.map eraseRecvChain).map recChainOfErased = recv'.map fun c =>
      ({ senderRatchetKey := Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g c.ratchetKey), senderRatchetKeyPrivate := []
         chainKey := some (c.index.toBitVec, gamma interpretation S g c.chainKey), messageKeys := [] } : ChainRec) := by
    rw [hMap', List.map_map]
    exact List.map_congr_left fun c hc => recChainOfErased_modelRecvChainOfTr interpretation S g c (hRkLens' c hc) (hCkLens' c hc)
  have hrc'' : chains'.map (fun rc => { receiverChainToChainRec rc with messageKeys := [] }) =
      recv'.map fun c =>
        ({ senderRatchetKey := Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g c.ratchetKey), senderRatchetKeyPrivate := []
           chainKey := some (c.index.toBitVec, gamma interpretation S g c.chainKey), messageKeys := [] } : ChainRec) := by
    rw [← hrc', List.map_map]; rfl
  simp only [eraseSkipped, eraseUnmodelled, sessionToSessionRec, List.map_map] at heq ⊢
  unfold sessionOf at heq ⊢; dsimp only at heq ⊢
  injection heq with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rw [Function.comp_def, hrc'', h1, h2, h3, h4, h5, h6, hspqr']
theorem stateRel_sessionToRecordRec_congr_tr {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost} {st : TRState}
    {s₁ s₂ : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hVer : s₂.state.sessionVersion = s₁.state.sessionVersion) (hLocal : s₂.state.localIdentity = s₁.state.localIdentity)
    (hRemote : s₂.state.remoteIdentity = s₁.state.remoteIdentity) (hRoot : s₂.state.rootKey = s₁.state.rootKey)
    (hPrev : s₂.state.previousCounter = s₁.state.previousCounter) (hSend : s₂.state.senderChain = s₁.state.senderChain)
    (hRecv : s₂.state.receiverChains = s₁.state.receiverChains) (hPqr : s₂.state.pqRatchetState = s₁.state.pqRatchetState)
    (hrel : StateRel interpretation S g st (sessionToRecordRec s₁)) :
    StateRel interpretation S g st (sessionToRecordRec s₂) := by
  rw [stateRel_sessionToRecordRec_iff_tr] at hrel ⊢; rw [← hrel]
  simp only [eraseSkipped, eraseUnmodelled, sessionToSessionRec, hVer, hLocal, hRemote, hRoot, hPrev, hSend, hRecv, hPqr]
theorem stateRel_of_decrypt_update_tr {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost} {st' : TRState}
    {s s' : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))} {r2 : RatchetState} {newPqrState : List (BitVec 8)}
    (hr2_root : r2.rootKey = (ratchetStateOf s.state).rootKey) (hr2_prev : r2.previousCounter = (ratchetStateOf s.state).previousCounter)
    (hr2_send : r2.senderChain = (ratchetStateOf s.state).senderChain)
    (hs' : s'.state = { s.state with
      rootKey := r2.rootKey, previousCounter := r2.previousCounter, senderChain := r2.senderChain,
      receiverChains := r2.receiverChains, pqRatchetState := newPqrState, pendingPreKey := false })
    (hrel : StateRel interpretation S g st' (sessionToRecordRec
      { s with state := { s.state with receiverChains := r2.receiverChains, pqRatchetState := newPqrState } })) :
    StateRel interpretation S g st' (sessionToRecordRec s') := by
  refine stateRel_sessionToRecordRec_congr_tr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hrel <;>
    simp [hs', hr2_root, hr2_prev, hr2_send, ratchetStateOf]
theorem nodup_ratchetKey_of_stateRel_tr {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {st : TRState} {rec : RecordRec} (hrel : StateRel interpretation S g st rec)
    (hnd : (rec.current.receiverChains.map ChainRec.senderRatchetKey).Nodup) :
    (st.recv.map RecvChain.ratchetKey).Nodup := by
  have h1 := congrArg (fun s : SessionRec => s.receiverChains.map ChainRec.senderRatchetKey) hrel.2
  have hlhs : (eraseSkipped (eraseUnmodelled rec.current)).receiverChains.map ChainRec.senderRatchetKey =
      rec.current.receiverChains.map ChainRec.senderRatchetKey := by
    simp [eraseSkipped, eraseUnmodelled, List.map_map, Function.comp_def]
  have hrhs : (sessionOf interpretation (gamma interpretation S g) st).receiverChains.map ChainRec.senderRatchetKey =
      (st.recv.map RecvChain.ratchetKey).map (fun pk => Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g pk)) := by
    simp [sessionOf, List.map_map, Function.comp_def]
  rw [hlhs, hrhs] at h1; rw [h1] at hnd; exact List.Nodup.of_map _ hnd

theorem receiverChains_getElem?_of_map_erase_tr {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {rcs : List ReceiverChain} {recv : List RecvChain} {i : Nat} {rc : ReceiverChain}
    (hMap : rcs.map eraseRecvChain = recv.map (modelRecvChainOfTr interpretation S g)) (hRc : rcs[i]? = some rc) :
    ∃ c : RecvChain, recv[i]? = some c ∧ eraseRecvChain rc = modelRecvChainOfTr interpretation S g c ∧
      rc.senderRatchetKey = ⟨vec32 (gamma interpretation S g c.ratchetKey)⟩ ∧
      rc.chainKey = some ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g c.chainKey), c.index.toBitVec⟩ := by
  have hAt := congrArg (fun l : List ReceiverChain => l[i]?) hMap
  simp only [List.getElem?_map, hRc, Option.map_some] at hAt
  cases hRecv : recv[i]? with
  | none => rw [hRecv] at hAt; simp at hAt
  | some c =>
    rw [hRecv, Option.map_some, Option.some.injEq] at hAt
    have hSrk : rc.senderRatchetKey = (modelRecvChainOfTr interpretation S g c).senderRatchetKey := by
      simpa using congrArg ReceiverChain.senderRatchetKey hAt
    have hCk : rc.chainKey = (modelRecvChainOfTr interpretation S g c).chainKey := by
      simpa using congrArg ReceiverChain.chainKey hAt
    exact ⟨c, rfl, hAt, hSrk, hCk⟩
theorem findReceiverChainKey_some_of_map_erase_tr {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {r : RatchetState} {st : TRState} {their : PublicKey} {ck : ChainKey}
    (hMap : r.receiverChains.map eraseRecvChain = st.recv.map (modelRecvChainOfTr interpretation S g))
    (hFind : r.findReceiverChainKey their = .ok (some ck)) :
    ∃ ci : Nat, ∃ rc : ReceiverChain, ∃ c : RecvChain,
      r.findReceiverChainIndex their = some ci ∧ r.receiverChains[ci]? = some rc ∧
      st.recv[ci]? = some c ∧ rc.senderRatchetKey = their ∧
      their = ⟨vec32 (gamma interpretation S g c.ratchetKey)⟩ ∧
      ck = ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g c.chainKey), c.index.toBitVec⟩ ∧
      rc.chainKey = some ck := by
  obtain ⟨ci, rc, hci, hrc, hsrk, hck⟩ := findReceiverChainKey_ok_some r their ck hFind
  obtain ⟨c, hc, _, hsrk_c, hck_c⟩ := receiverChains_getElem?_of_map_erase_tr hMap hrc
  rw [hck] at hck_c; injection hck_c with hck_eq
  exact ⟨ci, rc, c, hci, hrc, hc, hsrk, hsrk.symm.trans hsrk_c, hck_eq, hck⟩
unseal DY.Bytes in
private instance subKdf0Tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subLit0Tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
theorem gamma_hmac_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (k m : DY.Bytes) :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.hmac k m) =
      CryptoGames.HMAC.hmacWith (sha256CompressFunction interpretation)
        (gamma interpretation S g k) (gamma interpretation S g m) := by
  show (gamma' interpretation S g (({salt := k, ikm := m} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack)).bytes = _
  unfold gamma'; rw [DY.Bytes.rec_eq (concretizeKdf interpretation) (concretizeAll interpretation S g)]; rfl
theorem length_gamma_hmac_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (k m : DY.Bytes) :
    (gamma interpretation S g (DY.Libsignal.TripleRatchet.hmac k m)).length = 32 := by
  rw [gamma_hmac_tr]; exact length_hmacWith_tr _ _ _
theorem gamma_litByte_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (b : UInt8) :
    gamma interpretation S g (litByte b) = [BitVec.ofNat 8 b.toNat] := by
  unfold litByte
  have hlit : gamma interpretation S g (DY.Literal.literalToBytes ⟨#[b]⟩) = ofByteArray ⟨#[b]⟩ := by
    unfold gamma gamma'
    show ((({lit := ⟨#[b]⟩} : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
    rw [DY.Bytes.rec_eq concretizeLit (concretizeAll interpretation S g)]; rfl
  rw [hlit]; simp [ofByteArray]
theorem length_gamma_kdfCk_fst_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (ckTerm : DY.Bytes) :
    (gamma interpretation S g (kdfCk ckTerm).1).length = 32 := length_gamma_hmac_tr interpretation S g ckTerm (litByte 0x02)
theorem length_gamma_kdfCk_snd_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (ckTerm : DY.Bytes) :
    (gamma interpretation S g (kdfCk ckTerm).2).length = 32 := length_gamma_hmac_tr interpretation S g ckTerm (litByte 0x01)
theorem length_gamma_chainKeyAt_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (ckTerm : DY.Bytes) (n : Nat) (hLen : (gamma interpretation S g ckTerm).length = 32) :
    (gamma interpretation S g (chainKeyAt ckTerm n)).length = 32 := by
  induction n generalizing ckTerm with
  | zero => exact hLen
  | succ m ih => simpa [chainKeyAt] using ih (kdfCk ckTerm).1 (length_gamma_kdfCk_fst_tr interpretation S g ckTerm)
theorem chainStep_eq_gamma_kdfCk_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (ckTerm : DY.Bytes) (hLen : (gamma interpretation S g ckTerm).length = 32) :
    CryptoGames.Ratchet.chainHmac (sha256CompressFunction interpretation)
        (CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g ckTerm)) CryptoGames.Ratchet.chainKeySeed =
      gamma interpretation S g (kdfCk ckTerm).1 ∧
    CryptoGames.Ratchet.chainHmac (sha256CompressFunction interpretation)
        (CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g ckTerm)) CryptoGames.Ratchet.messageKeySeed =
      gamma interpretation S g (kdfCk ckTerm).2 := by
  unfold CryptoGames.Ratchet.chainHmac kdfCk
  rw [keyToBytes32_bytesToKey32_tr _ hLen, gamma_hmac_tr, gamma_hmac_tr, gamma_litByte_tr, gamma_litByte_tr]
  exact ⟨rfl, rfl⟩
theorem step1_key_eq_gamma_kdfCk_fst_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (ckTerm : DY.Bytes) (idx : BitVec 32) (hLen : (gamma interpretation S g ckTerm).length = 32) :
    step1 (sha256CompressFunction interpretation) ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g ckTerm), idx⟩ =
      ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g (kdfCk ckTerm).1), idx + 1⟩ := by
  unfold step1; rw [(chainStep_eq_gamma_kdfCk_tr interpretation S g ckTerm hLen).1]
theorem chainStepN_eq_gamma_chainKeyAt_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (ckTerm : DY.Bytes) (idx : BitVec 32) (n : Nat) (hLen : (gamma interpretation S g ckTerm).length = 32) :
    (chainStepN (sha256CompressFunction interpretation) n
      ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g ckTerm), idx⟩).key =
      CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g (chainKeyAt ckTerm n)) := by
  induction n generalizing ckTerm idx with
  | zero => rfl
  | succ m ih =>
    simp only [chainStepN, chainKeyAt]
    change (chainStepN (sha256CompressFunction interpretation) m
      (step1 (sha256CompressFunction interpretation) ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g ckTerm), idx⟩)).key = _
    rw [step1_key_eq_gamma_kdfCk_fst_tr interpretation S g ckTerm idx hLen]
    exact ih (kdfCk ckTerm).1 (idx + 1) (length_gamma_kdfCk_fst_tr interpretation S g ckTerm)
theorem chainStepN_messageKeys_seed_eq_gamma_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (ckTerm : DY.Bytes) (idx : BitVec 32) (n : Nat) (hLen : (gamma interpretation S g ckTerm).length = 32) :
    ((chainStepN (sha256CompressFunction interpretation) n
      ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g ckTerm), idx⟩).messageKeys
        (sha256CompressFunction interpretation)).seed =
      gamma interpretation S g (kdfCk (chainKeyAt ckTerm n)).2 := by
  unfold ChainKey.messageKeys; rw [chainStepN_eq_gamma_chainKeyAt_tr interpretation S g ckTerm idx n hLen]
  exact (chainStep_eq_gamma_kdfCk_tr interpretation S g (chainKeyAt ckTerm n)
    (length_gamma_chainKeyAt_tr interpretation S g ckTerm n hLen)).2
theorem skippedKeys_mem_gamma_kdfCk_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (ckTerm : DY.Bytes) (idx : BitVec 32) (n : Nat) (hLen : (gamma interpretation S g ckTerm).length = 32)
    (k : MessageKeyGenerator)
    (hk : k ∈ skippedKeys (sha256CompressFunction interpretation) n
      ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g ckTerm), idx⟩) :
    ∃ j < n, k.counter = idx + BitVec.ofNat 32 j ∧
      k.seed = gamma interpretation S g (kdfCk (chainKeyAt ckTerm j)).2 := by
  induction n generalizing ckTerm idx with
  | zero => simp [skippedKeys] at hk
  | succ m ih =>
    simp only [skippedKeys, List.mem_append, List.mem_singleton] at hk
    change k ∈ skippedKeys (sha256CompressFunction interpretation) m
        (step1 (sha256CompressFunction interpretation) ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g ckTerm), idx⟩) ∨
      k = (ChainKey.mk (CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g ckTerm)) idx).messageKeys
        (sha256CompressFunction interpretation) at hk
    rw [step1_key_eq_gamma_kdfCk_fst_tr interpretation S g ckTerm idx hLen] at hk
    rcases hk with hTail | rfl
    · obtain ⟨j, hjLt, hjCnt, hjSeed⟩ :=
        ih (kdfCk ckTerm).1 (idx + 1) (length_gamma_kdfCk_fst_tr interpretation S g ckTerm) hTail
      refine ⟨j + 1, Nat.succ_lt_succ hjLt, ?_, by simpa [chainKeyAt] using hjSeed⟩
      rw [hjCnt, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_comm 1 j]
    · exact ⟨0, Nat.zero_lt_succ m, by simp [ChainKey.messageKeys],
        chainStepN_messageKeys_seed_eq_gamma_tr interpretation S g ckTerm idx 0 hLen⟩

theorem hsk'_decTailTr_of_new_exact_tr (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) {j : Nat} (hj : j < n.toNat - c.index.toNat) :
    (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.SkippedKeyStored (st1.sessionInfo me) pk (c.index + UInt32.ofNat j)
        (kdfCk (chainKeyAt c.chainKey j)).2 c.rIdx stateIdx) (tr_pre.length + j) := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  unfold decTailTr; dsimp only
  have hlen := logSkippedKeysTr_length (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index (n.toNat - c.index.toNat) tr_pre
  rw [at?_append_non_entry _ _ rfl,
      at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
      at?_append_of_lt _ _ (by omega)]
  exact at?_trEntry_logSkippedKeysTr_add (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index (n.toNat - c.index.toNat) tr_pre hj
theorem at?_stEntry_decTailTr_lt (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes)
    (n : UInt32) {i : Nat} (hi : i < tr_pre.length + (n.toNat - c.index.toNat) + 2) :
    ((decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).at? i : Option StEntry) =
      (tr_pre.at? i : Option StEntry) := by
  unfold decTailTr; dsimp only
  have hlen := logSkippedKeysTr_length (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index (n.toNat - c.index.toNat) tr_pre
  rw [at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
      at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, at?_stEntry_logSkippedKeysTr]
theorem at?_stEntry_decTailTr_last (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    ((decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).at?
        (tr_pre.length + (n.toNat - c.index.toNat) + 2) : Option StEntry) =
      some ⟨⟨me, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ := by
  unfold decTailTr; dsimp only
  have hlen := logSkippedKeysTr_length (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index (n.toNat - c.index.toNat) tr_pre
  let tr_sk := logSkippedKeysTr (st1.sessionInfo me) pk c.rIdx stateIdx c.chainKey c.index (n.toNat - c.index.toNat) tr_pre
  let tr_rcv := tr_sk.append (⟨TREvent.Received me st1.peer pk n ptTerm⟩ : TREntry)
  let tr_mid := tr_rcv.append (⟨TREvent.MessageKey (st1.sessionInfo me) .receiver seed pqSalt n c.rIdx stateIdx⟩ : TREntry)
  have hmid : tr_pre.length + (n.toNat - c.index.toNat) + 2 = tr_mid.length := by
    dsimp only [tr_mid, tr_rcv, tr_sk]
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    omega
  rw [hmid]; exact Trace.at?_append tr_mid (⟨⟨me, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ : StEntry)
theorem getLocalState_decTailTr_last (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    ((PersistentLocalState.getLocalState me (tr_pre.length + (n.toNat - c.index.toNat) + 2) : Traceful TRState).run
      (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n)).1 =
      some { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } := by
  rw [getLocalState_fst, at?_stEntry_decTailTr_last]; simp only [↓reduceIte]
theorem isCurrentSnapshot_decTailTr_last (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    isCurrentSnapshot (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n)
      (tr_pre.length + (n.toNat - c.index.toNat) + 2) = true := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]; rw [at?_stEntry_decTailTr_last]; dsimp only
  have hlen : (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).length -
      ((tr_pre.length + (n.toNat - c.index.toNat) + 2) + 1) = 0 := by rw [decTailTr_length]; omega
  rw [hlen]; rfl
theorem someEventOnTraceB_append_non_tr_a2 {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (P : TREvent → Bool) : (DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent) (tr.append e) P = (DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent) tr P := by
  apply Bool.eq_iff_iff.mpr
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  simp only [List.any_eq_true, List.mem_range, at?_append_non_entry tr e hnone]
  refine ⟨fun ⟨i, _, hp⟩ => ⟨i, ?_, hp⟩, fun ⟨i, hi, hp⟩ =>
    ⟨i, by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega, hp⟩⟩
  rcases h : (tr.at? i : Option TREntry) with _ | ev
  · rw [h] at hp; cases hp
  · have := Trace.at?_eq_some_implies_length_le (EntryT := TREntry) tr i; rwa [h] at this
theorem someEventOnTraceB_append_trEntry_a2 (tr : ExecTrace) (ev : TREvent) (P : TREvent → Bool) :
    (DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent) (tr.append (⟨ev⟩ : TREntry)) P = ((DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.TripleRatchet.TREvent) tr P || P ev) := by
  apply Bool.eq_iff_iff.mpr
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  simp only [List.any_eq_true, List.mem_range, Bool.or_eq_true]
  constructor
  · rintro ⟨i, hi, hp⟩
    by_cases hlt : i < tr.length
    · left; rw [at?_append_of_lt tr _ hlt] at hp; exact ⟨i, hlt, hp⟩
    · right; have heq : i = tr.length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hi; omega
      subst heq; rwa [Trace.at?_append] at hp
  · rintro (⟨i, hi, hp⟩ | hp)
    · refine ⟨i, by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega, ?_⟩
      rwa [at?_append_of_lt tr _ hi]
    · refine ⟨tr.length, by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega, ?_⟩
      rwa [Trace.at?_append]
theorem skippedKeyUsedB_append_non_tr_a2 {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (skIdx : Nat) : skippedKeyUsedB (tr.append e) skIdx = skippedKeyUsedB tr skIdx :=
  someEventOnTraceB_append_non_tr_a2 tr e hnone _
theorem skippedKeyUsedB_append_trEntry_other_a2 (tr : ExecTrace) (ev : TREvent)
    (hne : ∀ s idx, ev ≠ TREvent.SkippedKeyUsed s idx) (skIdx : Nat) :
    skippedKeyUsedB (tr.append (⟨ev⟩ : TREntry)) skIdx = skippedKeyUsedB tr skIdx := by
  unfold skippedKeyUsedB; rw [someEventOnTraceB_append_trEntry_a2]
  cases ev <;> try exact Bool.or_false _
  next s idx => exfalso; exact hne s idx rfl
theorem skippedKeyUsedB_logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes) (rIdx srcIdx : Nat)
    (ck : DY.Bytes) (idx : UInt32) (count : Nat) (tr : ExecTrace) (skIdx : Nat) :
    skippedKeyUsedB (logSkippedKeysTr s pk rIdx srcIdx ck idx count tr) skIdx = skippedKeyUsedB tr skIdx := by
  induction count generalizing ck idx tr with
  | zero => rfl
  | succ k ih => unfold logSkippedKeysTr; rw [ih, skippedKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ h => by cases h)]
theorem skippedKeyUsedB_decTailTr (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) (skIdx : Nat) :
    skippedKeyUsedB (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n) skIdx =
      skippedKeyUsedB tr_pre skIdx := by
  unfold decTailTr; dsimp only
  rw [skippedKeyUsedB_append_non_tr_a2 _ _ rfl, skippedKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ h => by cases h),
      skippedKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ h => by cases h), skippedKeyUsedB_logSkippedKeysTr]
theorem receiverKeyUsedB_append_non_tr_a2 {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (s : SessionInfo) (seed : DY.Bytes) (cnt : UInt32) (rIdx : Nat) :
    receiverKeyUsedB (tr.append e) s seed cnt rIdx = receiverKeyUsedB tr s seed cnt rIdx :=
  someEventOnTraceB_append_non_tr_a2 tr e hnone _
theorem receiverKeyUsedB_append_trEntry_other_a2 (tr : ExecTrace) (ev : TREvent)
    (hne : ∀ s1 seed1 pq1 cnt1 r1 st1,
      ev ≠ TREvent.MessageKey s1 .receiver seed1 pq1 cnt1 r1 st1)
    (s : SessionInfo) (seed : DY.Bytes) (cnt : UInt32) (rIdx : Nat) :
    receiverKeyUsedB (tr.append (⟨ev⟩ : TREntry)) s seed cnt rIdx = receiverKeyUsedB tr s seed cnt rIdx := by
  unfold receiverKeyUsedB; rw [someEventOnTraceB_append_trEntry_a2]
  cases ev with
  | MessageKey s1 dir seed1 pq1 cnt1 r1 st1 =>
    cases dir with
    | sender => exact Bool.or_false _
    | receiver => exfalso; exact hne s1 seed1 pq1 cnt1 r1 st1 rfl
  | _ => exact Bool.or_false _
theorem receiverKeyUsedB_append_messageKey_receiver_a2 (tr : ExecTrace)
    (s0 : SessionInfo) (seed0 pq0 : DY.Bytes) (cnt0 : UInt32) (r0 st0 : Nat)
    (s : SessionInfo) (seed : DY.Bytes) (cnt : UInt32) (rIdx : Nat) :
    receiverKeyUsedB (tr.append (⟨TREvent.MessageKey s0 .receiver seed0 pq0 cnt0 r0 st0⟩ : TREntry))
      s seed cnt rIdx =
      (receiverKeyUsedB tr s seed cnt rIdx || decide (s0 = s ∧ seed0 = seed ∧ cnt0 = cnt ∧ r0 = rIdx)) := by
  unfold receiverKeyUsedB; rw [someEventOnTraceB_append_trEntry_a2]
theorem receiverKeyUsedB_logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes) (rIdx srcIdx : Nat)
    (ck : DY.Bytes) (idx : UInt32) (count : Nat) (tr : ExecTrace)
    (s' : SessionInfo) (seed : DY.Bytes) (cnt : UInt32) (rIdx' : Nat) :
    receiverKeyUsedB (logSkippedKeysTr s pk rIdx srcIdx ck idx count tr) s' seed cnt rIdx' =
      receiverKeyUsedB tr s' seed cnt rIdx' := by
  induction count generalizing ck idx tr with
  | zero => rfl
  | succ k ih =>
    unfold logSkippedKeysTr; rw [ih, receiverKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ _ _ _ _ h => by cases h)]
theorem receiverKeyUsedB_decTailTr (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32)
    (s' : SessionInfo) (seed' : DY.Bytes) (cnt' : UInt32) (rIdx' : Nat) :
    receiverKeyUsedB (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n) s' seed' cnt' rIdx' =
      (receiverKeyUsedB tr_pre s' seed' cnt' rIdx' ||
        decide (st1.sessionInfo me = s' ∧ seed = seed' ∧ n = cnt' ∧ c.rIdx = rIdx')) := by
  unfold decTailTr; dsimp only
  rw [receiverKeyUsedB_append_non_tr_a2 _ _ rfl, receiverKeyUsedB_append_messageKey_receiver_a2,
      receiverKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ _ _ _ _ h => by cases h),
      receiverKeyUsedB_logSkippedKeysTr]
theorem eventLoggedAt_decTailTr_lt (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32)
    {ev : TREvent} {i : Nat} (hi : i < tr_pre.length) :
    (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).EventLoggedAt ev i ↔ tr_pre.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  rw [at?_trEntry_decTailTr_lt _ _ _ _ _ _ _ _ _ _ _ _ hi]
theorem eventLoggedAt_append_non_tr_a2 {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (ev : TREvent) (i : Nat) : (tr.append e).EventLoggedAt ev i ↔ tr.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  rw [at?_append_non_entry tr e hnone]
theorem trKeyShape_setRecvChain_spqr {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {st : TRState} (hks : TRKeyShape interpretation S g st) (c' : RecvChain) (spqr' : DY.Bytes) :
    TRKeyShape interpretation S g { st with recv := setRecvChain st.recv c', spqr := spqr' } := by
  rcases hks with ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

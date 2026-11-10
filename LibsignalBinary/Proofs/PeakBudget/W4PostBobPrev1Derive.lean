/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Placed
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathACore
public import LibsignalBinary.Proofs.SignalSession.SessionCap.TopStateTight
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3d
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen

/-!
# Post-Decrypt Arm-4 `prev1` Derivation Leaves & `PostBobPrev1Dom` Closer

Derivation leaves and Arm-4 `PostBobPrev1Dom` closers for post-`try_decrypt` Path C sessions:
1. `rfl` cross-checks against the per-field protobuf and clone constants in `W4PostBobPrev1Dom`.
2. Extraction of `SessionGhostValid G' ses'`, `rc.messageKeys.length ≤ 2000`, and
   `SessionCloneDom 286196 ses'` on Arm-4 post-decrypt sessions.
3. Preservation of `ses'.state.receiverChains.length ≤ 1` from `st0.receiverChains = []` across
   `tryDecryptWithState` / `genP3S5Model`.
4. Per-field protobuf length bound `(encodeRecordPrev1Mem G ses enc).length ≤
   postBobTotalPrev1CapOf bobPqCap prevEncCap` (`= 2,469,364` at `(286196, 2097152)`) and 1-chain
   clone/serialize credit bounds.
5. Arm-4 `PostBobPrev1Dom` closers (`postBobPrev1Dom_of_leaves`, `postBobPrev1Dom_of_arm4`,
   `postBobPrev1Dom_of_arm4_midPrev1Placed`).
-/

@[expose] public section

namespace LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Derive

set_option autoImplicit false

open Arm64 (Memory Satisfies SepProp State)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession
  (ChainKey Crypto IdentityKey MessageKeyGenerator MessageType Mut PrivateKey PublicKey
   RatchetState ReceiverChain SenderChain SessionState ShaCompress SignalMessage
   SignalProtocolError Spqr TripleRatchet aesCbcDecrypt initializeRecipientSession liftE
   maxForwardJumps maxMessageKeys zoom)
open CryptoGames.LibsignalSessionApi (PendingKyberPreKey PendingPreKey Session)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (SessionExtraRel)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (encodeRecordPrev1 encodeRecordPrev1Mem encodeRecordPrev1Mem_eq_of_canon
   stageP3DispatchOkMidPrev1Placed)
open CryptoVerification.E2E
  (LocalIdentity PEParams PreKeyMessageFields ResponderPreKeySecrets djbKey ofU8)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
  (ensureReceiverChain_index_zero_or_err_ne_panic)
open CryptoVerification.E2E.Record
  (bytesField encChainKey encMessageKey encPendingKyber encPendingPreKey
   encReceiverChain encSenderChain encSession encodeRecord int32Field lenField msgField
   optUint32Field uint32Field uint64Field)
open CryptoVerification.LibsignalProtoCodec (WireType encodeKey encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalSpqrV1 (length_hmacWith spqrV1 spqrV1Init)
open CryptoVerification.LibsignalTripleRatchet.Prost (varintLenBV varintLenBV_eq_encodeVarint_length)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SenderChainGhost SessionGhost sessionStateAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (pathAInitSession pathAInitState)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (chainCloneLarge optLargeCost optTailCloneLen segCloneLarge segCloneTightCum vecCloneLarge)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (serializePrev1TightCum serializePrev1TightCum_fine_le_of_clone)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_length_le topStateTight_spqrV1Init topStateTight_spqrV1_recv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (SessionCloneDom ghostCloneValid_of_sessionGhostValid)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
  (fineOptLarge fineOptLarge_mono fineOptLarge_of_le optLargeCost_fine_eq)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (PostBobPrev1Dom lenFieldCap1_15 postBobPrev1Overhead286K postBobRecordCapOf postBobSessionCapOf
   postBobTotalPrev1Cap286K postBobTotalPrev1CapOf varintMaxLen w4PostBobChainKeyBytes
   w4PostBobCloneTightCum w4PostBobEncReceiverChainBytes w4PostBobFixedNonChainBytes
   w4PostBobMaxSkippedKeys w4PostBobMsgKeyFieldBytes w4PostBobOneChainBytes w4PostBobOneChainLarge
   w4PostBobPendingKyberFieldBytes w4PostBobPendingPreKeyFieldBytes w4PostBobPqCap
   w4PostBobSenderChainFieldBytes w4PostBobSerializePrev1TightCum)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (senderChainAsProtoGhost)
open ProofLib (sepConj_assoc sepConj_comm)

/-! ## `rfl` Cross-Checks Against `W4PostBobPrev1Dom` Constants -/

theorem derive_w4PostBobMaxSkippedKeys_eq : w4PostBobMaxSkippedKeys = maxMessageKeys := rfl
theorem derive_w4PostBobOneChainBytes_eq : w4PostBobOneChainBytes = 84081 := rfl
theorem derive_w4PostBobFixedNonChainBytes_eq : w4PostBobFixedNonChainBytes = 1922 := rfl
theorem derive_postBobRecordCapOf_286K_eq : postBobRecordCapOf w4PostBobPqCap = 372207 := rfl
theorem derive_postBobPrev1Overhead286K_eq : postBobPrev1Overhead286K = 372212 := rfl
theorem derive_postBobTotalPrev1Cap286K_eq : postBobTotalPrev1Cap286K = 2469364 := rfl
theorem derive_postBobTotalPrev1Cap286K_decomp :
    postBobTotalPrev1Cap286K = 2097152 + postBobPrev1Overhead286K := rfl
theorem derive_w4PostBobCloneTightCum_eq : w4PostBobCloneTightCum = 2373456 := rfl
theorem derive_w4PostBobSerializePrev1TightCum_eq : w4PostBobSerializePrev1TightCum = 2660912 := rfl

/-! ## `SessionGhostValid G' ses'`, `mk ≤ 2000`, & `SessionCloneDom 286196` on Arm 4 -/

/-- Extract `SessionGhostValid G ses` from `SessionExtraRel G ses` and spatial `sessionStateAt`. -/
theorem sessionGhostValid_of_extraRel_and_stateAt
    {A : RustAlloc} {ss : BitVec 64} {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {m : Memory} {R : SepProp}
    (hExtra : SessionExtraRel G ses)
    (hm : Arm64.Satisfies (Arm64.sepConj (sessionStateAt A ss G ses.state) R) m) :
    SessionGhostValid G ses :=
  ⟨hExtra, A, ss, m, R, hm⟩

private theorem h10b_ex_frame_drop_left {m : Memory} {P Q : SepProp}
    (h : ∃ R, Satisfies (Arm64.sepConj (Arm64.sepConj P Q) R) m) :
    ∃ R, Satisfies (Arm64.sepConj Q R) m :=
  let ⟨R, hR⟩ := h
  ⟨Arm64.sepConj P R, by rwa [sepConj_comm P Q, sepConj_assoc] at hR⟩

/-- Extract `SessionGhostValid G' ses'` directly on Path C Arm-4 Stage-P4 entry (`+0x34dc#64`,
`stageP3DispatchOkMidPrev1Placed`, `D3NonCanonValidOverPollAuxPlacedBudget.lean:1801`). -/
theorem sessionGhostValid_of_stageP3DispatchOkMidPrev1Placed [LibsignalPlacement]
    {A : RustAlloc} {s0 s : State}
    {coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr : BitVec 64}
    {enc pt : List (BitVec 8)} {b_2c0 : BitVec 8}
    {G' : SessionGhost} {ses' : Session (List (BitVec 8))}
    {m : Memory} {R : SepProp}
    (hExtra : SessionExtraRel G' ses')
    (hm : Arm64.Satisfies
      (Arm64.sepConj
        (stageP3DispatchOkMidPrev1Placed A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
          ptCap ptPtr enc pt b_2c0 G' ses'.state) R) m) :
    SessionGhostValid G' ses' := by
  have h0 : ∃ R', Satisfies
      (Arm64.sepConj
        (stageP3DispatchOkMidPrev1Placed A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
          ptCap ptPtr enc pt b_2c0 G' ses'.state) R') m := ⟨R, hm⟩
  dsimp only [stageP3DispatchOkMidPrev1Placed] at h0
  have h1 := h10b_ex_frame_drop_left h0
  have h2 := h10b_ex_frame_drop_left h1
  have h3 := h10b_ex_frame_drop_left h2
  have h4 := h10b_ex_frame_drop_left h3
  have h5 := h10b_ex_frame_drop_left h4
  have h6 := h10b_ex_frame_drop_left h5
  have h7 := h10b_ex_frame_drop_left h6
  have h8 := h10b_ex_frame_drop_left h7
  have h9 := h10b_ex_frame_drop_left h8
  have h10 := h10b_ex_frame_drop_left h9
  have h11 := h10b_ex_frame_drop_left h10
  have h12 := h10b_ex_frame_drop_left h11
  have h13 := h10b_ex_frame_drop_left h12
  have h14 := h10b_ex_frame_drop_left h13
  obtain ⟨R', h15⟩ := h10b_ex_frame_drop_left h14
  rw [sepConj_assoc] at h15
  exact sessionGhostValid_of_extraRel_and_stateAt hExtra h15

private theorem h10b_exists_mem_zip_of_mem_right {α β : Type} :
    ∀ (xs : List α) (ys : List β) (y : β),
      xs.length = ys.length → y ∈ ys → ∃ x, (x, y) ∈ xs.zip ys
  | [], [], _, _, hy => nomatch hy
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | x :: xs, y₀ :: ys, y, hlen, hy => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact ⟨x, List.mem_cons_self ..⟩
    · obtain ⟨x', hx'⟩ := h10b_exists_mem_zip_of_mem_right xs ys y hlen hmem
      exact ⟨x', List.mem_cons_of_mem _ hx'⟩

/-- `SessionGhostValid G ses` directly implies `rc.messageKeys.length ≤ maxMessageKeys` (`2000`)
for every `rc ∈ ses.state.receiverChains` (`GhostCloneValid.chains_len` + `chains_ok`). -/
theorem receiverChains_messageKeys_le_of_sessionGhostValid
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) :
    ∀ rc ∈ ses.state.receiverChains, rc.messageKeys.length ≤ maxMessageKeys := by
  have hgcv := ghostCloneValid_of_sessionGhostValid hgv
  intro rc hrc
  obtain ⟨cg, hzip⟩ :=
    h10b_exists_mem_zip_of_mem_right G.chains ses.state.receiverChains rc hgcv.chains_len hrc
  exact (hgcv.chains_ok (cg, rc) hzip).2.2

/-- When `ses.state.receiverChains.length ≤ 1`, `SessionGhostValid G ses` bounds the zipped
receiver-chain skipped-key sum by `w4PostBobMaxSkippedKeys` (`2000`). -/
theorem zip_messageKeys_sum_le_2000_of_rc_le_one
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses)
    (hrc : ses.state.receiverChains.length ≤ 1) :
    ((G.chains.zip ses.state.receiverChains).map
      (fun gc => gc.2.messageKeys.length)).sum ≤ w4PostBobMaxSkippedKeys := by
  have hgcv := ghostCloneValid_of_sessionGhostValid hgv
  cases hcs : ses.state.receiverChains with
  | nil => simp
  | cons rc tl =>
    rw [hcs] at hrc
    have htl : tl = [] := by
      cases tl with
      | nil => rfl
      | cons _ _ => simp at hrc
    subst htl
    cases hgs : G.chains with
    | nil => simp
    | cons cg gtl =>
      have hzip : (cg, rc) ∈ G.chains.zip ses.state.receiverChains := by
        simp [hgs, hcs]
      have hmk := (hgcv.chains_ok (cg, rc) hzip).2.2
      simpa [w4PostBobMaxSkippedKeys] using hmk

private theorem h10b_Mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  cases h : m s with
  | mk r s' =>
    cases r <;>
      (simp [Mut.exec, h, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont,
        StateT.run, ExceptT.run]; try rfl)

private theorem h10b_Mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl
private theorem h10b_Mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl
private theorem h10b_Mut_exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl
private theorem h10b_Mut_exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl
private theorem h10b_Mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl
private theorem h10b_Mut_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl
private theorem h10b_Mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by cases r <;> rfl

private theorem h10b_mem_set_or {α : Type} :
    ∀ (l : List α) (i : Nat) (v y : α), y ∈ l.set i v → y = v ∨ y ∈ l
  | [], _, _, _, h => by simp at h
  | a :: _, 0, v, y, h => by
    simp only [List.set_cons_zero, List.mem_cons] at h
    exact h.elim Or.inl (Or.inr ∘ List.mem_cons_of_mem a)
  | a :: tl, i + 1, v, y, h => by
    simp only [List.set_cons_succ, List.mem_cons] at h
    exact h.elim (fun hy => hy ▸ Or.inr (List.mem_cons_self ..)) fun htl =>
      (h10b_mem_set_or tl i v y htl).elim Or.inl (Or.inr ∘ List.mem_cons_of_mem a)

private theorem h10b_length_eraseIdx_le {α : Type} :
    ∀ (l : List α) (i : Nat), (l.eraseIdx i).length ≤ l.length
  | [], _ => Nat.le_refl 0
  | _ :: _, 0 => by simp
  | _ :: tl, i + 1 => by
    simp only [List.eraseIdx_cons_succ, List.length_cons]
    exact Nat.add_le_add_right (h10b_length_eraseIdx_le tl i) 1

private theorem h10b_mem_of_mem_eraseIdx {α : Type} :
    ∀ (l : List α) (i : Nat) (y : α), y ∈ l.eraseIdx i → y ∈ l
  | [], _, _, h => by simp at h
  | a :: _, 0, _, h => List.mem_cons_of_mem a h
  | a :: tl, i + 1, y, h => by
    simp only [List.eraseIdx_cons_succ, List.mem_cons] at h
    exact h.elim (fun hy => hy ▸ List.mem_cons_self ..)
      (List.mem_cons_of_mem a ∘ h10b_mem_of_mem_eraseIdx tl i y)

private theorem h10b_mem_of_mem_dropLast {α : Type} :
    ∀ (l : List α) (y : α), y ∈ l.dropLast → y ∈ l
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: tl, y, h => by
    simp only [List.dropLast_cons_cons, List.mem_cons] at h
    exact h.elim (fun hy => hy ▸ List.mem_cons_self ..)
      (List.mem_cons_of_mem a ∘ h10b_mem_of_mem_dropLast (b :: tl) y)

private theorem h10b_chainKey_messageKeys_seed_length (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 :=
  length_hmacWith F (keyToBytes32 ck.key) [CryptoGames.Ratchet.messageKeySeed]

private def h10b_RecvChainsExact1 (cs : List ReceiverChain) : Prop :=
  cs.length = 1 ∧
    ∀ rc ∈ cs, rc.messageKeys.length ≤ maxMessageKeys ∧ ∀ mk ∈ rc.messageKeys, mk.seed.length = 32

private theorem h10b_takeSkippedKey_exact1 (their : PublicKey) (counter : BitVec 32)
    (r r' : RatchetState) (opt : Option MessageKeyGenerator)
    (hr : h10b_RecvChainsExact1 r.receiverChains)
    (h : Mut.exec (RatchetState.takeSkippedKey their counter) r = (.ok opt, r')) :
    h10b_RecvChainsExact1 r'.receiverChains := by
  unfold RatchetState.takeSkippedKey at h
  simp only [h10b_Mut_exec_bind, h10b_Mut_exec_get] at h
  rcases hidx : r.findReceiverChainIndex their with _ | idx
  · simp only [hidx, h10b_Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr
  · simp only [hidx] at h
    rcases hc : r.receiverChains[idx]? with _ | c
    · simp [hc, h10b_Mut_exec_throw] at h
    · simp only [hc] at h
      rcases hpos : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos
      · simp only [hpos, h10b_Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr
      · simp only [hpos] at h
        rcases hk : c.messageKeys[pos]? with _ | key
        · simp [hk, h10b_Mut_exec_throw] at h
        · simp only [hk, h10b_Mut_exec_bind, h10b_Mut_exec_set, h10b_Mut_exec_pure,
            Prod.mk.injEq] at h
          rcases h with ⟨-, rfl⟩
          have hc_ok := hr.2 c (List.mem_of_getElem? hc)
          refine ⟨by rw [List.length_set]; exact hr.1, fun rc hmem => ?_⟩
          rcases h10b_mem_set_or r.receiverChains idx _ rc hmem with rfl | hmem0
          · exact ⟨Nat.le_trans (h10b_length_eraseIdx_le c.messageKeys pos) hc_ok.1,
              fun mk hmk => hc_ok.2 mk (h10b_mem_of_mem_eraseIdx c.messageKeys pos mk hmk)⟩
          · exact hr.2 rc hmem0

private theorem h10b_storeSkippedKey_exact1 (their : PublicKey) (key : MessageKeyGenerator)
    (r r' : RatchetState) (u : Unit) (hkey : key.seed.length = 32)
    (hr : h10b_RecvChainsExact1 r.receiverChains)
    (h : Mut.exec (RatchetState.storeSkippedKey their key) r = (.ok u, r')) :
    h10b_RecvChainsExact1 r'.receiverChains := by
  unfold RatchetState.storeSkippedKey at h
  simp only [h10b_Mut_exec_bind, h10b_Mut_exec_get] at h
  rcases hidx : r.findReceiverChainIndex their with _ | idx
  · simp [hidx, h10b_Mut_exec_throw] at h
  · simp only [hidx] at h
    rcases hc : r.receiverChains[idx]? with _ | c
    · simp [hc, h10b_Mut_exec_throw] at h
    · simp only [hc, h10b_Mut_exec_set, Prod.mk.injEq] at h
      rcases h with ⟨-, rfl⟩
      have hc_ok := hr.2 c (List.mem_of_getElem? hc)
      refine ⟨by rw [List.length_set]; exact hr.1, fun rc hmem => ?_⟩
      rcases h10b_mem_set_or r.receiverChains idx _ rc hmem with rfl | hmem0
      · dsimp only
        set keys1 := key :: c.messageKeys
        have hk1_elem : ∀ mk ∈ keys1, mk.seed.length = 32 := fun mk hmk =>
          (List.mem_cons.mp hmk).elim (fun e => e ▸ hkey) (hc_ok.2 mk)
        have hk1_len : keys1.length ≤ maxMessageKeys + 1 := by
          simp only [keys1, List.length_cons]
          exact Nat.add_le_add_right hc_ok.1 1
        by_cases hlt : maxMessageKeys < keys1.length
        · simp only [hlt, ↓reduceIte]
          exact ⟨by rw [List.length_dropLast]; omega,
            fun mk hmk => hk1_elem mk (h10b_mem_of_mem_dropLast keys1 mk hmk)⟩
        · simp only [hlt, ↓reduceIte]
          exact ⟨by omega, hk1_elem⟩
      · exact hr.2 rc hmem0

private theorem h10b_advanceChain_exact1 (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) :
    ∀ (fuel : Nat) (ck ck' : ChainKey) (r r' : RatchetState),
      h10b_RecvChainsExact1 r.receiverChains →
      Mut.exec (RatchetState.advanceChain F their counter fuel ck) r = (.ok ck', r') →
      h10b_RecvChainsExact1 r'.receiverChains
  | 0, _, _, _, _, hr, h => by
    unfold RatchetState.advanceChain at h
    simp only [h10b_Mut_exec_pure, Prod.mk.injEq] at h; rcases h with ⟨-, rfl⟩; exact hr
  | fuel + 1, ck, ck', r, r', hr, h => by
    unfold RatchetState.advanceChain at h
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte, h10b_Mut_exec_bind] at h
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with
        ⟨_ | u, r1⟩
      · rw [hs] at h; cases h
      · rw [hs] at h; dsimp only at h
        have hr1 := h10b_storeSkippedKey_exact1 their (ck.messageKeys F) r r1 u
          (h10b_chainKey_messageKeys_seed_length F ck) hr hs
        rcases hn : ck.nextChainKey F with _ | ck1
        · simp [hn, h10b_Mut_exec_liftE] at h
        · simp only [hn, h10b_Mut_exec_liftE] at h
          exact h10b_advanceChain_exact1 F their counter fuel ck1 ck' r1 r' hr1 h
    · simp only [hlt, ↓reduceIte, h10b_Mut_exec_pure, Prod.mk.injEq] at h
      rcases h with ⟨-, rfl⟩; exact hr

private theorem h10b_setReceiverChainKey_exact1 (their : PublicKey) (ck : ChainKey)
    (r r' : RatchetState) (u : Unit) (hr : h10b_RecvChainsExact1 r.receiverChains)
    (h : Mut.exec (RatchetState.setReceiverChainKey their ck) r = (.ok u, r')) :
    h10b_RecvChainsExact1 r'.receiverChains := by
  unfold RatchetState.setReceiverChainKey at h
  simp only [h10b_Mut_exec_bind, h10b_Mut_exec_get] at h
  rcases hidx : r.findReceiverChainIndex their with _ | idx
  · simp [hidx, h10b_Mut_exec_throw] at h
  · simp only [hidx] at h
    rcases hc : r.receiverChains[idx]? with _ | c
    · simp [hc, h10b_Mut_exec_throw] at h
    · simp only [hc, h10b_Mut_exec_set, Prod.mk.injEq] at h
      rcases h with ⟨-, rfl⟩
      have hc_ok := hr.2 c (List.mem_of_getElem? hc)
      refine ⟨by rw [List.length_set]; exact hr.1, fun rc hmem => ?_⟩
      exact (h10b_mem_set_or r.receiverChains idx _ rc hmem).elim
        (fun e => by rw [e]; exact hc_ok) (hr.2 rc)

private theorem h10b_consumeMessageKey_exact1 (F : ShaCompress) (their : PublicKey)
    (ck : ChainKey) (counter : BitVec 32) (msgType : MessageType)
    (r r' : RatchetState) (mkg : MessageKeyGenerator)
    (hr : h10b_RecvChainsExact1 r.receiverChains)
    (h : Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r = (.ok mkg, r')) :
    h10b_RecvChainsExact1 r'.receiverChains := by
  unfold RatchetState.consumeMessageKey at h
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, h10b_Mut_exec_bind] at h
    rcases htk : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨_ | (_ | k), r1⟩
    · rw [htk] at h; cases h
    · rw [htk] at h; simp [h10b_Mut_exec_throw] at h
    · rw [htk] at h; simp only [h10b_Mut_exec_pure, Prod.mk.injEq] at h
      rcases h with ⟨-, rfl⟩
      exact h10b_takeSkippedKey_exact1 their counter r r1 (some k) hr htk
  · simp only [hlt, ↓reduceIte, h10b_Mut_exec_bind, h10b_Mut_exec_get] at h
    split_ifs at h with hjump
    · simp [h10b_Mut_exec_throw] at h
    · simp only [h10b_Mut_exec_bind] at h
      rcases hadv : Mut.exec
          (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r with
        ⟨_ | ck1, r1⟩
      · rw [hadv] at h; cases h
      · rw [hadv] at h; dsimp only at h
        have hr1 := h10b_advanceChain_exact1 F their counter (counter - ck.index).toNat ck ck1
          r r1 hr hadv
        rcases hn : ck1.nextChainKey F with _ | ck2
        · simp [hn, h10b_Mut_exec_liftE] at h
        · simp only [hn, h10b_Mut_exec_liftE] at h
          rcases hset : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with
            ⟨_ | u, r2⟩
          · rw [hset] at h; cases h
          · rw [hset] at h; simp only [h10b_Mut_exec_pure, Prod.mk.injEq] at h
            rcases h with ⟨-, rfl⟩
            exact h10b_setReceiverChainKey_exact1 their ck2 r1 r2 u hr1 hset

private theorem h10b_onRatchet_ok {PQ α : Type} (m : Mut RatchetState α)
    (t t' : TripleRatchet PQ) (a : α)
    (h : Mut.exec (TripleRatchet.onRatchet m) t = (.ok a, t')) :
    Mut.exec m t.ratchet = (.ok a, t'.ratchet) ∧ t'.pqrState = t.pqrState := by
  unfold TripleRatchet.onRatchet zoom at h
  simp only [h10b_Mut_exec_bind, h10b_Mut_exec_get] at h
  rcases hm : Mut.exec m t.ratchet with ⟨_ | a0, r1⟩
  · simp [hm, h10b_Mut_exec_set, h10b_Mut_exec_liftE] at h
  · simp only [hm, h10b_Mut_exec_set, h10b_Mut_exec_liftE, Prod.mk.injEq, Except.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

private theorem h10b_tryDecryptWithState_ok_struct {PQC : Type}
    (C : Crypto) (spqr : Spqr (List (BitVec 8)) PQC) (expected : Option (List (BitVec 8)))
    (msg : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    {st0 st' : SessionState (List (BitVec 8))} {pt : List (BitVec 8)}
    (hrc0 : st0.receiverChains = [])
    (hdec : Mut.exec (SessionState.tryDecryptWithState C spqr expected msg msgType coins) st0 =
      (.ok pt, st')) :
    h10b_RecvChainsExact1 st'.receiverChains ∧
      ∃ salt, spqr.recv st0.pqRatchetState msg.pqRatchet = .ok (st'.pqRatchetState, salt) := by
  unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
    SessionState.takeRatchetState SessionState.takePqRatchetState at hdec
  simp only [h10b_Mut_exec_bind, h10b_Mut_exec_get, h10b_Mut_exec_modifyGet] at hdec
  rcases hrem : st0.remoteIdentity with _ | rem
  · simp [hrem, h10b_Mut_exec_throw] at hdec
  · simp only [hrem, h10b_Mut_exec_pure] at hdec
    set tr0 : TripleRatchet (List (BitVec 8)) :=
      ⟨⟨st0.rootKey, st0.senderChain, st0.receiverChains, st0.previousCounter, maxForwardJumps⟩,
        st0.pqRatchetState, st0.localIdentity, rem⟩
    rcases hd : Mut.exec (TripleRatchet.decrypt C spqr expected msg msgType coins) tr0 with
      ⟨_ | pt0, tr'⟩
    · simp [hd, h10b_Mut_exec_liftE] at hdec
    · simp only [hd, h10b_Mut_exec_liftE, h10b_Mut_exec_modify, Prod.mk.injEq] at hdec
      rcases hdec with ⟨-, rfl⟩
      unfold TripleRatchet.decrypt at hd
      simp only [h10b_Mut_exec_bind] at hd
      rcases hens : Mut.exec
          (TripleRatchet.onRatchet
            (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)) tr0 with
        ⟨_ | ck, tr1⟩
      · rw [hens] at hd; cases hd
      · rw [hens] at hd; dsimp only at hd
        rcases h10b_onRatchet_ok _ tr0 tr1 ck hens with ⟨hens_r, hpq1⟩
        have htr0_rc : tr0.ratchet.receiverChains = [] := hrc0
        have hr1_exact : h10b_RecvChainsExact1 tr1.ratchet.receiverChains := by
          rcases ensureReceiverChain_index_zero_or_err_ne_panic C msg.senderRatchetKey coins
              tr0.ratchet htr0_rc with ⟨e, r1, herr, -⟩ | ⟨recvCk, r1, hok_e, -, -, hr1_eq⟩
          · rw [hens_r] at herr; cases herr
          · rw [hens_r] at hok_e
            injection hok_e with hck hr1
            subst hr1
            rw [hr1_eq]
            refine ⟨rfl, fun rc hmem => ?_⟩
            rw [List.mem_singleton] at hmem
            subst hmem
            exact ⟨Nat.zero_le _, (fun _ hm => nomatch hm)⟩
        rcases hcons : Mut.exec
            (TripleRatchet.onRatchet
              (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType))
            tr1 with
          ⟨_ | mkg, tr2⟩
        · rw [hcons] at hd; cases hd
        · rw [hcons] at hd; dsimp only at hd
          rcases h10b_onRatchet_ok _ tr1 tr2 mkg hcons with ⟨hcons_r, hpq2⟩
          have hr2_exact := h10b_consumeMessageKey_exact1 C.F msg.senderRatchetKey ck msg.counter
            msgType tr1.ratchet tr2.ratchet mkg hr1_exact hcons_r
          simp only [h10b_Mut_exec_get] at hd
          cases hpan : spqr.recvPanics tr2.pqrState msg.pqRatchet
          · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hd
            rcases hspqr : spqr.recv tr2.pqrState msg.pqRatchet with err | ⟨newPq, salt⟩
            · cases err <;> simp [hspqr, h10b_Mut_exec_throw] at hd
            · simp only [hspqr, h10b_Mut_exec_bind, h10b_Mut_exec_pure] at hd
              split_ifs at hd
              · simp [h10b_Mut_exec_throw] at hd
              · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F salt).cipherKey
                    (mkg.generateKeys C.F salt).iv msg.ciphertext with _ | ptext
                · simp [haes, h10b_Mut_exec_throw] at hd
                · simp only [haes, h10b_Mut_exec_bind, h10b_Mut_exec_modify, h10b_Mut_exec_pure,
                    Prod.mk.injEq] at hd
                  rcases hd with ⟨-, rfl⟩
                  refine ⟨?_, salt, ?_⟩
                  · simpa [TripleRatchet.applyToSessionState,
                      SessionState.clearUnacknowledgedPreKeyMessage] using hr2_exact
                  · simpa [TripleRatchet.applyToSessionState,
                      SessionState.clearUnacknowledgedPreKeyMessage, hpq2, hpq1, tr0] using hspqr
          · simp [hpan, h10b_Mut_exec_throw] at hd

/-- Pure model preservation across `SessionState.tryDecryptWithState` from `st0.receiverChains = []`:
on `.ok pt`, `st'.receiverChains` has length `= 1`, every chain has `≤ maxMessageKeys` (`2000`)
skipped keys, and every skipped-key seed has length `32`. -/
theorem tryDecryptWithState_freshBob_chains_bound {PQC : Type}
    (C : Crypto) (spqr : Spqr (List (BitVec 8)) PQC) (expected : Option (List (BitVec 8)))
    (msg : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    {st0 st' : SessionState (List (BitVec 8))} {pt : List (BitVec 8)}
    (hrc0 : st0.receiverChains = [])
    (hdec : Mut.exec (SessionState.tryDecryptWithState C spqr expected msg msgType coins) st0 =
      (.ok pt, st')) :
    st'.receiverChains.length = 1 ∧
      ∀ rc ∈ st'.receiverChains,
        rc.messageKeys.length ≤ maxMessageKeys ∧ ∀ mk ∈ rc.messageKeys, mk.seed.length = 32 :=
  (h10b_tryDecryptWithState_ok_struct C spqr expected msg msgType coins hrc0 hdec).1

/-- On Arm 4 (`genP3S5Model ... (pathAInitState W me k m dk) = (.ok pt, st')`), the post-decrypt
session `ses'` satisfies `SessionCloneDom w4PostBobPqCap ses'` (`pqCap = 286,196`) and
`ses'.state.receiverChains.length = 1`. -/
theorem sessionCloneDom_postBob_of_genP3S5Model_ok
    (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (dk : SignalPqxdh.DRKey) (rem loc : AddrGhost) (msg : SignalMessage) (coins : List (BitVec 8))
    {pt : List (BitVec 8)} {st' : SessionState (List (BitVec 8))}
    (hok : genP3S5Model W.C W.Q.K rem loc msg coins (pathAInitState W me k m dk) = (.ok pt, st')) :
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W me k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    SessionCloneDom w4PostBobPqCap ses' ∧ ses'.state.receiverChains.length = 1 := by
  have hrc0 : (pathAInitState W me k m dk).receiverChains = [] := by
    simp [pathAInitState, initializeRecipientSession, SessionState.new, SessionState.setSenderChain]
  obtain ⟨⟨hrc1, hchains⟩, salt, hspqr⟩ :=
    h10b_tryDecryptWithState_ok_struct W.C (spqrV1 W.C.F W.Q.K).spqr _ msg .preKey _ hrc0 hok
  have hpq0 : TopStateTight W.C.F W.Q.K (pathAInitState W me k m dk).pqRatchetState := by
    change TopStateTight W.C.F W.Q.K
      (spqrV1Init W.C.F W.Q.K .b2a (bytesToKey32 (ofU8 dk.pqrKey)))
    exact topStateTight_spqrV1Init W.C.F W.Q.K .b2a (bytesToKey32 (ofU8 dk.pqrKey))
  have hpq' : TopStateTight W.C.F W.Q.K st'.pqRatchetState :=
    topStateTight_spqrV1_recv hpq0 hspqr
  have hpq_len : st'.pqRatchetState.length ≤ w4PostBobPqCap :=
    topStateTight_length_le hpq'
  dsimp only
  refine ⟨⟨Nat.le_trans (Nat.le_of_eq hrc1) (by decide), ?_, ?_, (fun _ hk => nomatch hk), hpq_len⟩, hrc1⟩
  · intro rc hrc mkg hmkg
    exact (hchains rc hrc).2 mkg hmkg
  · simp [pathAInitSession, djbKey]

/-! ## `ses'.state.receiverChains.length ≤ 1` on Post-Decrypt `ses'.state` -/

/-- Direct `length ≤ 1` corollary on `tryDecryptWithState` from `st0.receiverChains = []`. -/
theorem tryDecryptWithState_receiverChains_length_le_one_of_nil {PQC : Type}
    (C : Crypto) (spqr : Spqr (List (BitVec 8)) PQC) (expected : Option (List (BitVec 8)))
    (msg : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    {st0 st' : SessionState (List (BitVec 8))} {pt : List (BitVec 8)}
    (hrc0 : st0.receiverChains = [])
    (hdec : Mut.exec (SessionState.tryDecryptWithState C spqr expected msg msgType coins) st0 =
      (.ok pt, st')) :
    st'.receiverChains.length ≤ 1 := by
  have h1 := (tryDecryptWithState_freshBob_chains_bound C spqr expected msg msgType coins hrc0 hdec).1
  omega

/-- Direct `length ≤ 1` corollary for Arm-4 `genP3S5Model` on `pathAInitState W me k m dk`. -/
theorem genP3S5Model_postBob_receiverChains_length_le_one
    (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (dk : SignalPqxdh.DRKey) (rem loc : AddrGhost) (msg : SignalMessage) (coins : List (BitVec 8))
    {pt : List (BitVec 8)} {st' : SessionState (List (BitVec 8))}
    (hok : genP3S5Model W.C W.Q.K rem loc msg coins (pathAInitState W me k m dk) = (.ok pt, st')) :
    st'.receiverChains.length ≤ 1 := by
  have h1 := (sessionCloneDom_postBob_of_genP3S5Model_ok W me k m dk rem loc msg coins hok).2
  dsimp only at h1
  omega

/-! ## Serialization Length Bound & 1-Chain `SessionClone` / `SerializePrev1` Bounds -/

private theorem h10b_encodeVarintAux_length_le :
    ∀ (k : Nat) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold encodeVarintAux
    split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.add_le_add_right (h10b_encodeVarintAux_length_le k (v >>> 7)) 1

private theorem h10b_encodeVarint_length_le_10 (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  h10b_encodeVarintAux_length_le 10 v

private theorem h10b_shr_lt_0x80_iff (v : BitVec 64) (s : Nat) :
    (v >>> s < 0x80#64) ↔ v.toNat < 2 ^ (s + 7) := by
  have hlt : (v >>> s < 0x80#64) ↔ (v >>> s).toNat < 128 := BitVec.lt_def
  rw [hlt, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s), Nat.pow_add, Nat.mul_comm]

private theorem h10b_if_pos {α : Type} {p : Prop} [Decidable p] {a b : α} (hp : p) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hnp => exact absurd hp hnp

private theorem h10b_if_neg {α : Type} {p : Prop} [Decidable p] {a b : α} (hnp : ¬ p) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact absurd hp hnp
  | isFalse _ => rfl

private theorem h10b_varintLenBV_toNat_eq (v : BitVec 64) :
    (varintLenBV v).toNat = varintMaxLen v.toNat := by
  have h0 := h10b_shr_lt_0x80_iff v 0
  simp only [BitVec.ushiftRight_zero, Nat.zero_add] at h0
  have h1 : (v >>> 7 < 0x80#64) ↔ v.toNat < 2 ^ 14 := h10b_shr_lt_0x80_iff v 7
  have h2 : (v >>> 14 < 0x80#64) ↔ v.toNat < 2 ^ 21 := h10b_shr_lt_0x80_iff v 14
  have h3 : (v >>> 21 < 0x80#64) ↔ v.toNat < 2 ^ 28 := h10b_shr_lt_0x80_iff v 21
  have h4 : (v >>> 28 < 0x80#64) ↔ v.toNat < 2 ^ 35 := h10b_shr_lt_0x80_iff v 28
  have h5 : (v >>> 35 < 0x80#64) ↔ v.toNat < 2 ^ 42 := h10b_shr_lt_0x80_iff v 35
  have h6 : (v >>> 42 < 0x80#64) ↔ v.toNat < 2 ^ 49 := h10b_shr_lt_0x80_iff v 42
  have h7 : (v >>> 49 < 0x80#64) ↔ v.toNat < 2 ^ 56 := h10b_shr_lt_0x80_iff v 49
  have h8 : (v >>> 56 < 0x80#64) ↔ v.toNat < 2 ^ 63 := h10b_shr_lt_0x80_iff v 56
  unfold varintLenBV varintMaxLen
  by_cases c0 : v < 0x80#64
  · rw [h10b_if_pos c0, h10b_if_pos (h0.mp c0)]; rfl
  · rw [h10b_if_neg c0, h10b_if_neg (mt h0.mpr c0)]
    by_cases c1 : v >>> 7 < 0x80#64
    · rw [h10b_if_pos c1, h10b_if_pos (h1.mp c1)]; rfl
    · rw [h10b_if_neg c1, h10b_if_neg (mt h1.mpr c1)]
      by_cases c2 : v >>> 14 < 0x80#64
      · rw [h10b_if_pos c2, h10b_if_pos (h2.mp c2)]; rfl
      · rw [h10b_if_neg c2, h10b_if_neg (mt h2.mpr c2)]
        by_cases c3 : v >>> 21 < 0x80#64
        · rw [h10b_if_pos c3, h10b_if_pos (h3.mp c3)]; rfl
        · rw [h10b_if_neg c3, h10b_if_neg (mt h3.mpr c3)]
          by_cases c4 : v >>> 28 < 0x80#64
          · rw [h10b_if_pos c4, h10b_if_pos (h4.mp c4)]; rfl
          · rw [h10b_if_neg c4, h10b_if_neg (mt h4.mpr c4)]
            by_cases c5 : v >>> 35 < 0x80#64
            · rw [h10b_if_pos c5, h10b_if_pos (h5.mp c5)]; rfl
            · rw [h10b_if_neg c5, h10b_if_neg (mt h5.mpr c5)]
              by_cases c6 : v >>> 42 < 0x80#64
              · rw [h10b_if_pos c6, h10b_if_pos (h6.mp c6)]; rfl
              · rw [h10b_if_neg c6, h10b_if_neg (mt h6.mpr c6)]
                by_cases c7 : v >>> 49 < 0x80#64
                · rw [h10b_if_pos c7, h10b_if_pos (h7.mp c7)]; rfl
                · rw [h10b_if_neg c7, h10b_if_neg (mt h7.mpr c7)]
                  by_cases c8 : v >>> 56 < 0x80#64
                  · rw [h10b_if_pos c8, h10b_if_pos (h8.mp c8)]; rfl
                  · rw [h10b_if_neg c8, h10b_if_neg (mt h8.mpr c8)]; rfl

private theorem h10b_encodeVarint_length_eq_varintMaxLen (v : BitVec 64) :
    (encodeVarint v).length = varintMaxLen v.toNat := by
  have heq := congrArg BitVec.toNat (varintLenBV_eq_encodeVarint_length v)
  have hlt : (encodeVarint v).length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (h10b_encodeVarint_length_le_10 v) (by decide)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, h10b_varintLenBV_toNat_eq] at heq
  exact heq.symm

private theorem h10b_ite_le {p : Prop} [Decidable p] {k t m : Nat}
    (hk : k ≤ m) (ht : t ≤ m) : (if p then k else t) ≤ m := by
  by_cases hp : p
  · rw [h10b_if_pos hp]; exact hk
  · rw [h10b_if_neg hp]; exact ht

private theorem h10b_ite_ge {p : Prop} [Decidable p] {m k t : Nat}
    (hk : m ≤ k) (ht : m ≤ t) : m ≤ (if p then k else t) := by
  by_cases hp : p
  · rw [h10b_if_pos hp]; exact hk
  · rw [h10b_if_neg hp]; exact ht

private theorem h10b_ite_mono {p q : Prop} [Decidable p] [Decidable q]
    {k ta tb : Nat} (hpq : q → p) (hk : k ≤ tb) (ht : ta ≤ tb) :
    (if p then k else ta) ≤ (if q then k else tb) := by
  by_cases hq : q
  · rw [h10b_if_pos (hpq hq), h10b_if_pos hq]
  · rw [h10b_if_neg hq]
    exact h10b_ite_le hk ht

private theorem h10b_varintMaxLen_le_10 (n : Nat) : varintMaxLen n ≤ 10 := by
  unfold varintMaxLen
  exact h10b_ite_le (by decide) (h10b_ite_le (by decide) (h10b_ite_le (by decide)
    (h10b_ite_le (by decide) (h10b_ite_le (by decide) (h10b_ite_le (by decide)
      (h10b_ite_le (by decide) (h10b_ite_le (by decide)
        (h10b_ite_le (by decide) (Nat.le_refl 10)))))))))

private theorem h10b_varintMaxLen_mono {a b : Nat} (hab : a ≤ b) :
    varintMaxLen a ≤ varintMaxLen b := by
  unfold varintMaxLen
  refine h10b_ite_mono (Nat.lt_of_le_of_lt hab) ?_ ?_
  · exact h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (h10b_ite_ge (by decide)
      (h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (h10b_ite_ge (by decide)
        (h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (by decide))))))))
  · refine h10b_ite_mono (Nat.lt_of_le_of_lt hab) ?_ ?_
    · exact h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (h10b_ite_ge (by decide)
        (h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (h10b_ite_ge (by decide)
          (h10b_ite_ge (by decide) (by decide)))))))
    · refine h10b_ite_mono (Nat.lt_of_le_of_lt hab) ?_ ?_
      · exact h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (h10b_ite_ge (by decide)
          (h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (h10b_ite_ge (by decide)
            (by decide))))))
      · refine h10b_ite_mono (Nat.lt_of_le_of_lt hab) ?_ ?_
        · exact h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (h10b_ite_ge (by decide)
            (h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (by decide)))))
        · refine h10b_ite_mono (Nat.lt_of_le_of_lt hab) ?_ ?_
          · exact h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (h10b_ite_ge (by decide)
              (h10b_ite_ge (by decide) (by decide))))
          · refine h10b_ite_mono (Nat.lt_of_le_of_lt hab) ?_ ?_
            · exact h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (h10b_ite_ge (by decide)
                (by decide)))
            · refine h10b_ite_mono (Nat.lt_of_le_of_lt hab) ?_ ?_
              · exact h10b_ite_ge (by decide) (h10b_ite_ge (by decide) (by decide))
              · refine h10b_ite_mono (Nat.lt_of_le_of_lt hab) ?_ ?_
                · exact h10b_ite_ge (by decide) (by decide)
                · exact h10b_ite_mono (Nat.lt_of_le_of_lt hab) (by decide) (Nat.le_refl 10)

private theorem h10b_lenField_length_le {tag cap : Nat} {payload : List (BitVec 8)}
    (hkey : (encodeKey tag .lengthDelimited).length = 1)
    (hlen : payload.length ≤ cap)
    (hcap64 : cap < 2 ^ 64) :
    (lenField tag payload).length ≤ lenFieldCap1_15 cap := by
  unfold lenField lenFieldCap1_15
  simp only [List.length_append, hkey]
  have hp64 : payload.length < 2 ^ 64 := Nat.lt_of_le_of_lt hlen hcap64
  rw [h10b_encodeVarint_length_eq_varintMaxLen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp64]
  exact Nat.add_le_add (Nat.add_le_add_left (h10b_varintMaxLen_mono hlen) 1) hlen

private theorem h10b_bytesField_length_le {tag cap : Nat} {v : List (BitVec 8)}
    (hkey : (encodeKey tag .lengthDelimited).length = 1)
    (hlen : v.length ≤ cap)
    (hcap64 : cap < 2 ^ 64) :
    (bytesField tag v).length ≤ lenFieldCap1_15 cap := by
  unfold bytesField
  split_ifs
  · simp
  · exact h10b_lenField_length_le hkey hlen hcap64

private theorem h10b_msgField_length_le {tag cap : Nat} {ob : Option (List (BitVec 8))}
    (hkey : (encodeKey tag .lengthDelimited).length = 1)
    (hB : ∀ b, ob = some b → b.length ≤ cap)
    (hcap64 : cap < 2 ^ 64) :
    (msgField tag ob).length ≤ lenFieldCap1_15 cap := by
  cases ob with
  | none => simp [msgField]
  | some b => exact h10b_lenField_length_le hkey (hB b rfl) hcap64

private theorem h10b_varintMaxLen_u32_le_5 (v : BitVec 32) :
    varintMaxLen (v.setWidth 64).toNat ≤ 5 := by
  have hlt : (v.setWidth 64).toNat ≤ 2 ^ 32 := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]
    exact Nat.le_of_lt v.isLt
  exact Nat.le_trans (h10b_varintMaxLen_mono hlt) (by decide)

private theorem h10b_uint32Field_length_le {tag : Nat} (v : BitVec 32)
    (hkey : (encodeKey tag .varint).length = 1) :
    (uint32Field tag v).length ≤ 6 := by
  unfold uint32Field
  split_ifs
  · simp
  · rw [List.length_append, hkey, h10b_encodeVarint_length_eq_varintMaxLen]
    exact Nat.add_le_add_left (h10b_varintMaxLen_u32_le_5 v) 1

private theorem h10b_optUint32Field_length_le {tag : Nat} (ov : Option (BitVec 32))
    (hkey : (encodeKey tag .varint).length = 1) :
    (optUint32Field tag ov).length ≤ 6 := by
  cases ov with
  | none => simp [optUint32Field]
  | some v =>
    unfold optUint32Field
    rw [List.length_append, hkey, h10b_encodeVarint_length_eq_varintMaxLen]
    exact Nat.add_le_add_left (h10b_varintMaxLen_u32_le_5 v) 1

private theorem h10b_int32Field_length_le {tag : Nat} (v : BitVec 32)
    (hkey : (encodeKey tag .varint).length = 1) :
    (int32Field tag v).length ≤ 11 := by
  unfold int32Field
  split_ifs
  · simp
  · rw [List.length_append, hkey]
    exact Nat.add_le_add_left (h10b_encodeVarint_length_le_10 (v.signExtend 64)) 1

private theorem h10b_uint64Field_length_le {tag : Nat} (v : BitVec 64)
    (hkey : (encodeKey tag .varint).length = 1) :
    (uint64Field tag v).length ≤ 11 := by
  unfold uint64Field
  split_ifs
  · simp
  · rw [List.length_append, hkey]
    exact Nat.add_le_add_left (h10b_encodeVarint_length_le_10 v) 1

private theorem h10b_length_flatten_map_le {α : Type} :
    ∀ (l : List α) (f : α → List (BitVec 8)) (B : Nat),
      (∀ a ∈ l, (f a).length ≤ B) → ((l.map f).flatten).length ≤ l.length * B
  | [], _, _, _ => by simp
  | a :: tl, f, B, hf => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have ha := hf a (List.mem_cons_self ..)
    have htl := h10b_length_flatten_map_le tl f B (fun y hy => hf y (List.mem_cons_of_mem a hy))
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (tl.length * B) B]
    exact Nat.add_le_add ha htl

private theorem h10b_keyToBytes32_len (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]
private theorem h10b_publicKey_serialize_len (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]
private theorem h10b_identityKey_serialize_len (ik : IdentityKey) : ik.serialize.length = 33 := by
  simp [IdentityKey.serialize, PublicKey.serialize]
private theorem h10b_privateKey_bytes_len (sk : PrivateKey) : sk.bytes.toList.length = 32 :=
  sk.bytes.toList_length

private theorem h10b_encChainKey_le (ck : ChainKey) :
    (encChainKey ck).length ≤ w4PostBobChainKeyBytes := by
  unfold encChainKey w4PostBobChainKeyBytes
  rw [List.length_append]
  exact Nat.add_le_add
    (h10b_uint32Field_length_le ck.index rfl)
    (h10b_bytesField_length_le rfl (Nat.le_of_eq (h10b_keyToBytes32_len ck.key)) (by decide))

private theorem h10b_msgKeyField_le (mk : MessageKeyGenerator) (hseed : mk.seed.length = 32) :
    (lenField 4 (encMessageKey mk)).length ≤ w4PostBobMsgKeyFieldBytes := by
  unfold w4PostBobMsgKeyFieldBytes
  refine h10b_lenField_length_le rfl ?_ (by decide)
  unfold encMessageKey
  rw [List.length_append]
  exact Nat.add_le_add
    (h10b_uint32Field_length_le mk.counter rfl)
    (h10b_bytesField_length_le rfl (Nat.le_of_eq hseed) (by decide))

private theorem h10b_oneChain_le (c : ReceiverChain)
    (hlen : c.messageKeys.length ≤ maxMessageKeys)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32) :
    (lenField 7 (encReceiverChain c)).length ≤ w4PostBobOneChainBytes := by
  unfold w4PostBobOneChainBytes
  refine h10b_lenField_length_le rfl ?_ (by decide)
  unfold encReceiverChain w4PostBobEncReceiverChainBytes
  simp only [List.length_append]
  have h1 : (bytesField 1 c.senderRatchetKey.serialize).length ≤ lenFieldCap1_15 33 :=
    h10b_bytesField_length_le rfl
      (Nat.le_of_eq (h10b_publicKey_serialize_len c.senderRatchetKey)) (by decide)
  have h2 : (msgField 3 (c.chainKey.map encChainKey)).length ≤
      lenFieldCap1_15 w4PostBobChainKeyBytes :=
    h10b_msgField_length_le rfl (by
      intro b hb
      cases hck : c.chainKey with
      | none => rw [hck] at hb; cases hb
      | some ck =>
        rw [hck] at hb; injection hb with hb'; subst hb'
        exact h10b_encChainKey_le ck) (by decide)
  have h3_step := h10b_length_flatten_map_le c.messageKeys
    (fun mk => lenField 4 (encMessageKey mk)) w4PostBobMsgKeyFieldBytes
    (fun mk hmk => h10b_msgKeyField_le mk (hseeds mk hmk))
  have h3 : ((c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length ≤
      w4PostBobMaxSkippedKeys * w4PostBobMsgKeyFieldBytes :=
    Nat.le_trans h3_step (Nat.mul_le_mul_right w4PostBobMsgKeyFieldBytes hlen)
  exact Nat.add_le_add (Nat.add_le_add h1 h2) h3

private theorem h10b_senderChainField_le (osc : Option SenderChain) :
    (msgField 6 (osc.map encSenderChain)).length ≤ w4PostBobSenderChainFieldBytes := by
  unfold w4PostBobSenderChainFieldBytes
  refine h10b_msgField_length_le rfl ?_ (by decide)
  intro b hb
  cases osc with
  | none => cases hb
  | some c =>
    injection hb with hb'; subst hb'
    unfold encSenderChain
    simp only [List.length_append]
    exact Nat.add_le_add
      (Nat.add_le_add
        (h10b_bytesField_length_le rfl
          (Nat.le_of_eq (h10b_publicKey_serialize_len c.ratchetKey.publicKey)) (by decide))
        (h10b_bytesField_length_le rfl
          (Nat.le_of_eq (h10b_privateKey_bytes_len c.ratchetKey.privateKey)) (by decide)))
      (h10b_msgField_length_le rfl
        (fun _ hs => Option.some.inj hs ▸ h10b_encChainKey_le c.chainKey) (by decide))

private theorem h10b_pendingPreKeyField_le (op : Option PendingPreKey) :
    (msgField 9 (op.map encPendingPreKey)).length ≤ w4PostBobPendingPreKeyFieldBytes := by
  unfold w4PostBobPendingPreKeyFieldBytes
  refine h10b_msgField_length_le rfl ?_ (by decide)
  intro b hb
  cases op with
  | none => cases hb
  | some p =>
    injection hb with hb'; subst hb'
    unfold encPendingPreKey
    simp only [List.length_append]
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (h10b_optUint32Field_length_le p.preKeyId rfl)
          (h10b_bytesField_length_le rfl
            (Nat.le_of_eq (h10b_publicKey_serialize_len p.baseKey)) (by decide)))
        (h10b_int32Field_length_le p.signedPreKeyId rfl))
      (h10b_uint64Field_length_le p.timestamp rfl)

private theorem h10b_pendingKyberField_le (okyb : Option PendingKyberPreKey)
    (hcap : ∀ k, okyb = some k → k.ciphertext.length ≤ 1569) :
    (msgField 14 (okyb.map encPendingKyber)).length ≤ w4PostBobPendingKyberFieldBytes := by
  unfold w4PostBobPendingKyberFieldBytes
  refine h10b_msgField_length_le rfl ?_ (by decide)
  intro b hb
  cases hkyb : okyb with
  | none => rw [hkyb] at hb; cases hb
  | some p =>
    rw [hkyb] at hb; injection hb with hb'; subst hb'
    unfold encPendingKyber
    rw [List.length_append]
    exact Nat.add_le_add
      (h10b_uint32Field_length_le p.preKeyId rfl)
      (h10b_bytesField_length_le rfl (hcap p hkyb) (by decide))

private theorem h10b_add_lt_of_bound {a v c m d : Nat}
    (hv : v ≤ 10) (hc : c < m) (hmd : a + (1 + 10 + m) ≤ d) :
    a + (1 + v + c) < d := by
  omega

private theorem h10b_postBobSessionCap_lt_2pow64 {bobPqCap : Nat} (hpq56 : bobPqCap < 2 ^ 56) :
    postBobSessionCapOf bobPqCap < 2 ^ 64 := by
  unfold postBobSessionCapOf lenFieldCap1_15
  exact h10b_add_lt_of_bound (h10b_varintMaxLen_le_10 bobPqCap) hpq56 (by decide)

private theorem h10b_sum13_reorder
    {f1 f2 f3 f4 f5 f6 f7 f9 f10 f11 f13 f14 f15 : Nat}
    {c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c13 c14 c15 : Nat}
    (h1 : f1 ≤ c1) (h2 : f2 ≤ c2) (h3 : f3 ≤ c3) (h4 : f4 ≤ c4) (h5 : f5 ≤ c5)
    (h6 : f6 ≤ c6) (h7 : f7 ≤ c7) (h9 : f9 ≤ c9) (h10 : f10 ≤ c10) (h11 : f11 ≤ c11)
    (h13 : f13 ≤ c13) (h14 : f14 ≤ c14) (h15 : f15 ≤ c15) :
    (((((((((((f1 + f2 + f3) + f4) + f5) + f6) + f7) + f9) + f10) + f11) + f13) + f14) + f15) ≤
      (c1 + c2 + c3 + c4 + c5 + c6 + c9 + c10 + c11 + c13 + c14) + c7 + c15 := by
  omega

/-- Field-1 record byte bound `(Record.encodeRecord ⟨some ses⟩).length ≤ postBobRecordCapOf bobPqCap`
for any `SessionGhostValid G ses`, `SessionCloneDom bobPqCap ses`, `bobPqCap < 2 ^ 56`, and
`receiverChains.length ≤ 1`. -/
theorem encodeRecord_some_length_le_of_rc_le_one {bobPqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom bobPqCap ses)
    (hrc : ses.state.receiverChains.length ≤ 1)
    (hpq56 : bobPqCap < 2 ^ 56 := by decide) :
    (encodeRecord ⟨some ses⟩).length ≤ postBobRecordCapOf bobPqCap := by
  have hmk := receiverChains_messageKeys_le_of_sessionGhostValid hgv
  unfold encodeRecord msgField Option.map postBobRecordCapOf
  refine h10b_lenField_length_le rfl ?_ (h10b_postBobSessionCap_lt_2pow64 hpq56)
  unfold encSession postBobSessionCapOf w4PostBobFixedNonChainBytes
  dsimp only
  simp only [List.length_append]
  have hf3_len : ((ses.state.remoteIdentity.map IdentityKey.serialize).getD []).length ≤ 33 := by
    cases ses.state.remoteIdentity with
    | none => simp
    | some ik => simp [h10b_identityKey_serialize_len ik]
  have hf7_step := h10b_length_flatten_map_le ses.state.receiverChains
    (fun c => lenField 7 (encReceiverChain c)) w4PostBobOneChainBytes
    (fun c hc => h10b_oneChain_le c (hmk c hc) (hdom.seeds32 c hc))
  have hf7 : ((ses.state.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten).length ≤
      w4PostBobOneChainBytes := by
    have hmul := Nat.mul_le_mul_right w4PostBobOneChainBytes hrc
    rw [Nat.one_mul] at hmul
    exact Nat.le_trans hf7_step hmul
  have hpq64 : bobPqCap < 2 ^ 64 := Nat.lt_trans hpq56 (by decide)
  exact h10b_sum13_reorder
    (h10b_uint32Field_length_le ses.state.sessionVersion rfl)
    (h10b_bytesField_length_le rfl
      (Nat.le_of_eq (h10b_identityKey_serialize_len ses.state.localIdentity)) (by decide))
    (h10b_bytesField_length_le rfl hf3_len (by decide))
    (h10b_bytesField_length_le rfl
      (Nat.le_of_eq (h10b_keyToBytes32_len ses.state.rootKey)) (by decide))
    (h10b_uint32Field_length_le ses.state.previousCounter rfl)
    (h10b_senderChainField_le ses.state.senderChain)
    hf7
    (h10b_pendingPreKeyField_le ses.pendingPreKey)
    (h10b_uint32Field_length_le ses.remoteRegistrationId rfl)
    (h10b_uint32Field_length_le ses.localRegistrationId rfl)
    (h10b_bytesField_length_le rfl hdom.alice_len (by decide))
    (h10b_pendingKyberField_le ses.pendingKyberPreKey hdom.kyber_cap)
    (h10b_bytesField_length_le rfl hdom.pq_len hpq64)

/-- Parameterized `T'` bound: `(encodeRecordPrev1Mem G ses enc).length ≤
postBobTotalPrev1CapOf bobPqCap prevEncCap`. -/
theorem encodeRecordPrev1Mem_length_le_of_postBob {bobPqCap prevEncCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom bobPqCap ses)
    (hrc : ses.state.receiverChains.length ≤ 1)
    (hprev : enc.length ≤ prevEncCap)
    (hpq56 : bobPqCap < 2 ^ 56 := by decide)
    (hprev64 : prevEncCap < 2 ^ 64 := by decide) :
    (encodeRecordPrev1Mem G ses enc).length ≤ postBobTotalPrev1CapOf bobPqCap prevEncCap := by
  rw [encodeRecordPrev1Mem_eq_of_canon enc (ghostCloneValid_of_sessionGhostValid hgv).canon]
  unfold encodeRecordPrev1 postBobTotalPrev1CapOf
  rw [List.length_append]
  exact Nat.add_le_add
    (encodeRecord_some_length_le_of_rc_le_one hgv hdom hrc hpq56)
    (h10b_lenField_length_le rfl hprev hprev64)

/-- Post-decrypt Arm-4 `T'` bound at `(bobPqCap := 286196, prevEncCap := 2097152)`:
`(encodeRecordPrev1Mem G ses enc).length ≤ postBobTotalPrev1Cap286K` (`= 2,469,364` B). -/
theorem encodeRecordPrev1Mem_length_le_postBob286K
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom w4PostBobPqCap ses)
    (hrc : ses.state.receiverChains.length ≤ 1)
    (hprev : enc.length ≤ 2097152) :
    (encodeRecordPrev1Mem G ses enc).length ≤ postBobTotalPrev1Cap286K :=
  encodeRecordPrev1Mem_length_le_of_postBob hgv hdom hrc hprev (by decide) (by decide)

/-- 1-chain `segCloneTightCum` bound (`≤ 2,373,456` B) for `PostBobPrev1Dom` consumers. -/
theorem segCloneTightCum_fine_rc_le_one {bobPqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom bobPqCap ses)
    (hrc : ses.state.receiverChains.length ≤ 1) :
    segCloneTightCum fineCostModel G ses.state ≤ w4PostBobCloneTightCum :=
  LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.segCloneTightCum_fine_keys_le_of_dom
    hgv hdom (zip_messageKeys_sum_le_2000_of_rc_le_one hgv hrc)

private theorem h10b_vecCloneLarge_fine_of_le {len : Nat} (h : len ≤ 135167) :
    vecCloneLarge fineCostModel len = 0 := by
  unfold vecCloneLarge
  split
  · rfl
  · rw [optLargeCost_fine_eq]
    exact fineOptLarge_of_le h

private theorem h10b_senderChainLarge_fine_eq_zero {gs : SenderChainGhost} {sc : SenderChain}
    (hsrk : gs.srk.bytes.length = 33) (hpriv : gs.priv.bytes.length = 32) :
    chainCloneLarge fineCostModel (senderChainAsProtoGhost gs sc) = 0 := by
  unfold chainCloneLarge senderChainAsProtoGhost
  dsimp only
  rw [h10b_vecCloneLarge_fine_of_le (by omega),
      h10b_vecCloneLarge_fine_of_le (by omega),
      optLargeCost_fine_eq 32, fineOptLarge_of_le (by decide)]
  rfl

private theorem h10b_map_sum_eq_zero {α : Type} (f : α → Nat) :
    ∀ (l : List α), (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _ => rfl
  | x :: xs, hf => by
    simp only [List.map_cons, List.sum_cons, hf x (List.mem_cons_self ..), Nat.zero_add]
    exact h10b_map_sum_eq_zero f xs (fun y hy => hf y (List.mem_cons_of_mem x hy))

private theorem h10b_recvChainLarge_fine_le {gc : ChainGhost × ReceiverChain}
    (hsrk : gc.1.srk.bytes.length = 33) (hpriv : gc.1.priv.bytes.length = 0)
    (hmk : gc.2.messageKeys.length ≤ 2000)
    (hseeds : ∀ k ∈ gc.2.messageKeys, k.seed.length = 32) :
    chainCloneLarge fineCostModel gc ≤ w4PostBobOneChainLarge := by
  unfold chainCloneLarge w4PostBobOneChainLarge
  have h1 : vecCloneLarge fineCostModel gc.1.srk.bytes.length = 0 :=
    h10b_vecCloneLarge_fine_of_le (by omega)
  have h2 : vecCloneLarge fineCostModel gc.1.priv.bytes.length = 0 :=
    h10b_vecCloneLarge_fine_of_le (by omega)
  have hmsgs : (if gc.2.messageKeys = [] then 0
      else optLargeCost fineCostModel (104 * gc.2.messageKeys.length) +
        (gc.2.messageKeys.map fun mkg => optLargeCost fineCostModel mkg.seed.length).sum) ≤
      216195 := by
    split_ifs with hnil
    · exact Nat.zero_le _
    · have hbuf : optLargeCost fineCostModel (104 * gc.2.messageKeys.length) ≤ 216195 := by
        rw [optLargeCost_fine_eq]
        exact Nat.le_trans
          (fineOptLarge_mono (Nat.mul_le_mul_left 104 hmk))
          (by decide)
      have hseeds0 :
          (gc.2.messageKeys.map fun mkg => optLargeCost fineCostModel mkg.seed.length).sum = 0 :=
        h10b_map_sum_eq_zero (fun mkg => optLargeCost fineCostModel mkg.seed.length)
          gc.2.messageKeys (fun mkg hm => by
            rw [hseeds mkg hm, optLargeCost_fine_eq 32]
            exact fineOptLarge_of_le (by decide))
      rw [hseeds0, Nat.add_zero]
      exact hbuf
  rw [h1, h2]
  cases gc.2.chainKey with
  | none => simpa only [Nat.zero_add] using hmsgs
  | some _ =>
    dsimp only
    rw [optLargeCost_fine_eq 32, fineOptLarge_of_le (by decide)]
    simpa only [Nat.zero_add] using hmsgs

/-- 1-chain `segCloneLarge` bound (`≤ 216,195 + fineOptLarge bobPqCap`) for `PostBobPrev1Dom`. -/
theorem segCloneLarge_fine_rc_le_one {bobPqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom bobPqCap ses)
    (hrc : ses.state.receiverChains.length ≤ 1) :
    segCloneLarge fineCostModel G ses.state ≤ w4PostBobOneChainLarge + fineOptLarge bobPqCap := by
  obtain ⟨hloc_len, hrem_len, _, hch_ok, hsend_ok, hpend_len, hkyb_len, halice_eq, _⟩ :=
    ghostCloneValid_of_sessionGhostValid hgv
  unfold segCloneLarge
  have hloc : vecCloneLarge fineCostModel G.localIk.bytes.length = 0 :=
    h10b_vecCloneLarge_fine_of_le (by omega)
  have hrem : vecCloneLarge fineCostModel G.remoteIk.bytes.length = 0 :=
    h10b_vecCloneLarge_fine_of_le (by omega)
  have hroot : optLargeCost fineCostModel 32 = 0 := by
    rw [optLargeCost_fine_eq]; exact fineOptLarge_of_le (by decide)
  have hpend : vecCloneLarge fineCostModel (optTailCloneLen G.pending) = 0 :=
    h10b_vecCloneLarge_fine_of_le (by omega)
  have hkyb_le : optTailCloneLen G.kyber ≤ 1569 := by
    rw [hkyb_len]
    cases hk : ses.pendingKyberPreKey with
    | none => simp
    | some k => exact hdom.kyber_cap k hk
  have hkyb : vecCloneLarge fineCostModel (optTailCloneLen G.kyber) = 0 :=
    h10b_vecCloneLarge_fine_of_le (Nat.le_trans hkyb_le (by decide))
  have halice : vecCloneLarge fineCostModel G.alice.bytes.length = 0 :=
    h10b_vecCloneLarge_fine_of_le (by rw [halice_eq]; exact Nat.le_trans hdom.alice_len (by decide))
  have hpq : vecCloneLarge fineCostModel ses.state.pqRatchetState.length ≤
      fineOptLarge bobPqCap := by
    unfold vecCloneLarge
    split
    · exact Nat.zero_le _
    · rw [optLargeCost_fine_eq]
      exact fineOptLarge_mono hdom.pq_len
  have hchains : (if ses.state.receiverChains = [] then 0
      else optLargeCost fineCostModel (104 * ses.state.receiverChains.length) +
        ((G.chains.zip ses.state.receiverChains).map (chainCloneLarge fineCostModel)).sum) ≤
      w4PostBobOneChainLarge := by
    split_ifs with hnil
    · exact Nat.zero_le _
    · have houter : optLargeCost fineCostModel (104 * ses.state.receiverChains.length) = 0 := by
        rw [optLargeCost_fine_eq]
        exact fineOptLarge_of_le (by omega)
      rw [houter, Nat.zero_add]
      cases hcs : ses.state.receiverChains with
      | nil => exact False.elim (hnil hcs)
      | cons rc tl =>
        rw [hcs] at hrc
        have htl : tl = [] := by
          cases tl with
          | nil => rfl
          | cons _ _ => simp at hrc
        subst htl
        cases hgs : G.chains with
        | nil => simp
        | cons cg gtl =>
          have hzip : (cg, rc) ∈ G.chains.zip ses.state.receiverChains := by
            simp [hgs, hcs]
          obtain ⟨hsrk, hpriv, hmk⟩ := hch_ok (cg, rc) hzip
          have hsd := hdom.seeds32 rc (by simp [hcs])
          have h1 := h10b_recvChainLarge_fine_le hsrk hpriv hmk hsd
          simpa using h1
  rw [hloc, hrem, hroot, hpend, hkyb, halice]
  rcases hsend_ok with ⟨h1, h2⟩ | ⟨gs, sc, h1, h2, hsrk, hpriv⟩
  · rw [h1, h2]
    simp only [Nat.zero_add, Nat.add_zero]
    exact Nat.add_le_add hchains hpq
  · rw [h1, h2]
    dsimp only
    rw [h10b_senderChainLarge_fine_eq_zero hsrk hpriv]
    simp only [Nat.zero_add, Nat.add_zero]
    exact Nat.add_le_add hchains hpq

/-- 1-chain `serializePrev1TightCum` bound (`≤ 2,660,912` B) for `PostBobPrev1Dom` consumers. -/
theorem serializePrev1TightCum_fine_rc_le_one {bobPqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom bobPqCap ses)
    (hrc : ses.state.receiverChains.length ≤ 1) :
    serializePrev1TightCum fineCostModel G ses enc ≤ w4PostBobSerializePrev1TightCum :=
  Nat.le_trans
    (serializePrev1TightCum_fine_le_of_clone (segCloneTightCum_fine_rc_le_one hgv hdom hrc))
    (by decide)

/-! ## Arm-4 `PostBobPrev1Dom` Closers -/

/-- Generic `PostBobPrev1Dom` assembly from `rc.length ≤ 1`, `SessionGhostValid`,
`SessionCloneDom bobPqCap`, and `enc.length ≤ prevEncCap`. -/
theorem postBobPrev1Dom_of_leaves {bobPqCap prevEncCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hrc : ses.state.receiverChains.length ≤ 1)
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom bobPqCap ses)
    (hprev : enc.length ≤ prevEncCap)
    (hpq56 : bobPqCap < 2 ^ 56 := by decide)
    (hprev64 : prevEncCap < 2 ^ 64 := by decide) :
    PostBobPrev1Dom bobPqCap prevEncCap (postBobTotalPrev1CapOf bobPqCap prevEncCap) G ses enc :=
  ⟨hrc, hgv, hdom, hprev, encodeRecordPrev1Mem_length_le_of_postBob hgv hdom hrc hprev hpq56 hprev64⟩

/-- Assembles `PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K G' ses' enc`
directly from the `DecPkD3ValidOverOfEnv'` Arm-5 hypotheses and `enc.length ≤ 2097152`. -/
theorem postBobPrev1Dom_of_arm4
    (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (dk : SignalPqxdh.DRKey) (rem loc : AddrGhost) (msg : SignalMessage) (coins : List (BitVec 8))
    {pt : List (BitVec 8)} {G' : SessionGhost} {enc : List (BitVec 8)}
    (hok : (genP3S5Model W.C W.Q.K rem loc msg coins (pathAInitState W me k m dk)).1 = .ok pt)
    (hgv : SessionGhostValid G'
      { pathAInitSession W me k m dk with
        state := (genP3S5Model W.C W.Q.K rem loc msg coins (pathAInitState W me k m dk)).2
        pendingPreKey := none
        pendingKyberPreKey := none })
    (hprev : enc.length ≤ 2097152) :
    PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K G'
      { pathAInitSession W me k m dk with
        state := (genP3S5Model W.C W.Q.K rem loc msg coins (pathAInitState W me k m dk)).2
        pendingPreKey := none
        pendingKyberPreKey := none }
      enc := by
  have hp : genP3S5Model W.C W.Q.K rem loc msg coins (pathAInitState W me k m dk) =
      (.ok pt, (genP3S5Model W.C W.Q.K rem loc msg coins (pathAInitState W me k m dk)).2) :=
    Prod.ext hok rfl
  obtain ⟨hdom, hrc1⟩ := sessionCloneDom_postBob_of_genP3S5Model_ok W me k m dk rem loc msg coins hp
  dsimp only at hdom hrc1
  exact postBobPrev1Dom_of_leaves (by dsimp only; omega) hgv hdom hprev (by decide) (by decide)

/-- Memory-level Arm-4 `PostBobPrev1Dom` closer: extracts `SessionGhostValid G' ses'` from
`stageP3DispatchOkMidPrev1Placed` at `+0x34dc` and `SessionExtraRel G' ses'`, packaging
`PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K G' ses' enc`. -/
theorem postBobPrev1Dom_of_arm4_midPrev1Placed [LibsignalPlacement]
    {A : RustAlloc} {s0 s : State}
    {coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr : BitVec 64}
    {enc pt : List (BitVec 8)} {b_2c0 : BitVec 8}
    (W : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields)
    (dk : SignalPqxdh.DRKey) (rem loc : AddrGhost) (msg : SignalMessage) (coins : List (BitVec 8))
    {st' : SessionState (List (BitVec 8))} {G' : SessionGhost}
    {mem : Memory} {R : SepProp}
    (hok : genP3S5Model W.C W.Q.K rem loc msg coins (pathAInitState W me k m dk) = (.ok pt, st'))
    (hExtra : SessionExtraRel G'
      { pathAInitSession W me k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none })
    (hm : Arm64.Satisfies
      (Arm64.sepConj
        (stageP3DispatchOkMidPrev1Placed A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
          ptCap ptPtr enc pt b_2c0 G' st') R) mem)
    (hprev : enc.length ≤ 2097152) :
    PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K G'
      { pathAInitSession W me k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
      enc := by
  have hgv := sessionGhostValid_of_stageP3DispatchOkMidPrev1Placed hExtra hm
  have h1 : (genP3S5Model W.C W.Q.K rem loc msg coins (pathAInitState W me k m dk)).1 = .ok pt := by
    rw [hok]
  have h2 : (genP3S5Model W.C W.Q.K rem loc msg coins (pathAInitState W me k m dk)).2 = st' := by
    rw [hok]
  rw [← h2] at hgv ⊢
  exact postBobPrev1Dom_of_arm4 W me k m dk rem loc msg coins h1 hgv hprev

end LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Derive

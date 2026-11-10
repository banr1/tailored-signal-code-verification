/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.ClampsLossless
public import Computational.Proofs.SpqrV1Sync.TopStateTight
public import Computational.Specifications.Session.StatementIdsModel

/-!
# Per-Party Session Reachability Invariant

Defines `PartyReachInv C K g` on a model `GhostState Bytes` over `spqrV1SessionUniformCoins C.F K`
and proves initialization, step preservation across `initA`, `initB`, `send`, and `receive`, and
lossless `SessionRecord` serialization bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.SmReachInvParty

open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.Ratchet (chainHmac messageKeySeed)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey IdentityKey InitKeys Params
  GhostState SessionState SenderChain ReceiverChain RatchetState TripleRatchet
  OutgoingTripleRatchet ChainKey MessageKeyGenerator MessageType SignalMessage Mut
  maxReceiverChains maxMessageKeys initializeInitiatorSession initializeRecipientSession)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1 spqrV1SessionUniformCoins
  coinBytes length_hmacWith)
open CryptoVerification.SpqrV1Sync.SendTotal (TopStateTight topStateTight_init topStateTight_send
  topStateTight_recv topStateTight_length_le spqrV1Send_msg_len_le)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser addrBytes serviceIdParse utf8
  uuidTryParse)
open CryptoVerification.E2E (Bytes SampledSessionKey RecordExtras binStateOfUnderExtras
  partyAddressName partyDeviceId serializedPartyAddresses paramsIdsWithSpqr sessionSchemeFixedSpk)
open CryptoVerification.E2E.Costed (hdrT hdrOfV ghostSplitEval ghostJoinEval e2eRecordExtras
  e2eEncodeSessionRecord)
open Computational.Proofs.E2E.Dsl.ClampsLossless (ReachableSessionRecordBounds
  ghostJoinEval_ghostSplitEval e2eEncodeSessionRecord_lossless)

/-- Receiver-chain and skipped-key length bounds on a reachable `RatchetState`. -/
structure RatchetChainsInv (r : RatchetState) : Prop where
  receiverChains_le : r.receiverChains.length ≤ maxReceiverChains
  messageKeys_le : ∀ rc ∈ r.receiverChains, rc.messageKeys.length ≤ maxMessageKeys
  messageKeySeed_eq : ∀ rc ∈ r.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length = 32

/-- Per-party reachable state invariant for `GhostState Bytes` over
`spqrV1SessionUniformCoins C.F K`. -/
structure PartyReachInv (C : Crypto) (K : MlKem) (g : GhostState Bytes) : Prop where
  topTight : TopStateTight C.F K g.session.pqRatchetState
  receiverChains_le : g.session.receiverChains.length ≤ maxReceiverChains
  messageKeys_le : ∀ rc ∈ g.session.receiverChains, rc.messageKeys.length ≤ maxMessageKeys
  messageKeySeed_eq : ∀ rc ∈ g.session.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length = 32
  aligned : g.chainEpochs.length = g.session.receiverChains.length

theorem PartyReachInv.receiverChains_le_five {C : Crypto} {K : MlKem} {g : GhostState Bytes}
    (h : PartyReachInv C K g) : g.session.receiverChains.length ≤ 5 :=
  h.receiverChains_le

theorem PartyReachInv.messageKeys_le_2000 {C : Crypto} {K : MlKem} {g : GhostState Bytes}
    (h : PartyReachInv C K g) :
    ∀ rc ∈ g.session.receiverChains, rc.messageKeys.length ≤ 2000 :=
  h.messageKeys_le

theorem PartyReachInv.messageKeySeed_le_32 {C : Crypto} {K : MlKem} {g : GhostState Bytes}
    (h : PartyReachInv C K g) :
    ∀ rc ∈ g.session.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length ≤ 32 :=
  fun rc hrc mk hmk => Nat.le_of_eq (h.messageKeySeed_eq rc hrc mk hmk)

theorem PartyReachInv.pqRatchetState_length_le {C : Crypto} {K : MlKem} {g : GhostState Bytes}
    (h : PartyReachInv C K g) : g.session.pqRatchetState.length ≤ 286196 :=
  topStateTight_length_le C.F K h.topTight

theorem PartyReachInv.ghostSplitJoin_roundtrip {ℓ : ℕ} {C : Crypto} {K : MlKem}
    {g : GhostState Bytes} (h : PartyReachInv C K g) :
    ghostJoinEval (ghostSplitEval (ℓ := ℓ) g) = g :=
  ghostJoinEval_ghostSplitEval g h.receiverChains_le_five h.messageKeySeed_eq

theorem PartyReachInv.reachableSessionRecordBounds {C : Crypto} {K : MlKem}
    {g : GhostState Bytes} (h : PartyReachInv C K g) (E : Party → RecordExtras)
    (hab : (E g.party).aliceBaseKey.length ≤ 33)
    (hkyb : ∀ k ∈ (E g.party).kyber, k.ciphertext.length ≤ 1569) :
    ReachableSessionRecordBounds E g where
  receiverChains_le := h.receiverChains_le_five
  messageKeys_le := h.messageKeys_le_2000
  messageKeySeed_le := h.messageKeySeed_le_32
  aliceBaseKey_le := hab
  kyberCt_le := hkyb
  pqRatchetState_le := h.pqRatchetState_length_le

theorem PartyReachInv.reachableSessionRecordBounds_e2e {C : Crypto} {K : MlKem}
    {g : GhostState Bytes} (h : PartyReachInv C K g)
    (regIdA regIdB bobRemoteRegId : BitVec 32) (hdr : SignalPqxdh.HandshakeHdr) :
    ReachableSessionRecordBounds (e2eRecordExtras regIdA regIdB bobRemoteRegId hdr) g := by
  refine h.reachableSessionRecordBounds _ ?_ ?_
  · cases g.party <;> simp [e2eRecordExtras, PublicKey.serialize]
  · cases g.party with
    | A =>
      intro k hk
      simp only [e2eRecordExtras, Option.mem_def, Option.some.injEq] at hk
      subst hk
      simp [CryptoVerification.E2E.kyberKey]
    | B =>
      intro k hk
      simp [e2eRecordExtras] at hk

theorem PartyReachInv.encodeSessionRecord_lossless {ℓ : ℕ} {C : Crypto} {K : MlKem}
    {g : GhostState Bytes} (h : PartyReachInv C K g)
    (regIdA regIdB bobRemoteRegId : BitVec 32) (hdrV0 : (hdrT (ℓ := ℓ)).denote) :
    e2eEncodeSessionRecord (ℓ := ℓ) ((regIdA, (regIdB, (bobRemoteRegId, hdrV0))), g) =
      binStateOfUnderExtras (e2eRecordExtras regIdA regIdB bobRemoteRegId (hdrOfV hdrV0)) g :=
  e2eEncodeSessionRecord_lossless regIdA regIdB bobRemoteRegId hdrV0 g
    h.receiverChains_le_five h.messageKeys_le_2000 h.messageKeySeed_le_32 h.pqRatchetState_length_le

theorem spqrV1Send_pqMsg_length_le_96 (F : ShaCompress) (K : MlKem) (st : Bytes) (r : BitVec 512)
    {st' : Bytes} {salt : Salt} {pm : Bytes}
    (h : (spqrV1SessionUniformCoins F K).send st r = some (st', salt, pm)) :
    pm.length ≤ 96 :=
  Nat.le_trans (spqrV1Send_msg_len_le F K st r st' salt pm h) (by decide)

private theorem addrBytes_length (sid : Bool × List.Vector (BitVec 8) 16) (dev : BitVec 8) :
    (addrBytes sid dev).length = 18 := by
  simp [addrBytes, sid.2.toList_length]

theorem serializedPartyAddresses_length_le_128 (u : UuidParser) (p q : Party) :
    ∀ a ∈ serializedPartyAddresses u p q, a.length ≤ 128 := by
  intro a ha
  unfold serializedPartyAddresses at ha
  cases hs : serviceIdParse u (utf8 (partyAddressName p)) with
  | none => simp [hs] at ha
  | some s =>
    cases hr : serviceIdParse u (utf8 (partyAddressName q)) with
    | none => simp [hs, hr] at ha
    | some r =>
      simp only [hs, hr, bind, Option.bind, pure, Option.mem_def, Option.some.injEq] at ha
      subst ha
      simp [List.length_append, addrBytes_length]

private theorem chainKey_messageKeys_seed_length (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 := by
  simp [ChainKey.messageKeys, chainHmac, length_hmacWith]

private theorem mem_set_or {α : Type} :
    ∀ (l : List α) (i : ℕ) (x y : α), y ∈ l.set i x → y = x ∨ y ∈ l
  | [], _, _, _, hy => nomatch hy
  | _ :: as, 0, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ hmem)
  | a :: as, i + 1, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inr List.mem_cons_self
    · rcases mem_set_or as i x y hmem with rfl | hmem'
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem a hmem')

private theorem mem_eraseIdx_mem {α : Type} :
    ∀ (l : List α) (i : ℕ) {y : α}, y ∈ l.eraseIdx i → y ∈ l
  | [], _, _, hy => nomatch hy
  | _ :: as, 0, _, hy => List.mem_cons_of_mem _ hy
  | a :: as, i + 1, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_eraseIdx_mem as i hmem)

private theorem eraseIdx_length_le {α : Type} :
    ∀ (l : List α) (i : ℕ), (l.eraseIdx i).length ≤ l.length
  | [], _ => Nat.le_refl 0
  | _ :: _, 0 => Nat.le_succ _
  | _ :: as, i + 1 => Nat.succ_le_succ (eraseIdx_length_le as i)

private theorem mem_dropLast_mem {α : Type} :
    ∀ (l : List α) {y : α}, y ∈ l.dropLast → y ∈ l
  | [], _, hy => nomatch hy
  | [_], _, hy => nomatch hy
  | a :: b :: rest, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_dropLast_mem (b :: rest) hmem)

private theorem mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    (m >>= f).exec s =
      match m.exec s with
      | (.error e, s') => (.error e, s')
      | (.ok a, s') => (f a).exec s' := by
  unfold Mut.exec
  rw [ExceptT.run_bind, StateT.run_bind]
  cases h : m.run.run s with
  | mk res s' =>
    cases res <;> rfl

private theorem mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    (pure a : Mut σ α).exec s = (.ok a, s) := rfl

private theorem mut_exec_get {σ : Type} (s : σ) :
    (get : Mut σ σ).exec s = (.ok s, s) := rfl

private theorem mut_exec_set {σ : Type} (s' s : σ) :
    (set s' : Mut σ Unit).exec s = (.ok (), s') := rfl

private theorem mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    (modify f : Mut σ Unit).exec s = (.ok (), f s) := rfl

private theorem mut_exec_throw {σ α : Type} (e : CryptoGames.LibsignalSession.SignalProtocolError)
    (s : σ) :
    (throw e : Mut σ α).exec s = (.error e, s) := rfl

private theorem mut_exec_liftE {σ α : Type}
    (r : Except CryptoGames.LibsignalSession.SignalProtocolError α) (s : σ) :
    (CryptoGames.LibsignalSession.liftE r : Mut σ α).exec s = (r, s) := by
  cases r <;> rfl

private theorem dhRatchetStep_preserves (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    {r r' : RatchetState} {ck : ChainKey} (h : RatchetChainsInv r)
    (hstep : (RatchetState.dhRatchetStep C their coins).exec r = (.ok ck, r')) :
    RatchetChainsInv r' ∧
      r'.receiverChains.length =
        (r.receiverChains.length + 1) - ((r.receiverChains.length + 1) - maxReceiverChains) := by
  unfold RatchetState.dhRatchetStep at hstep
  rw [mut_exec_bind, mut_exec_get] at hstep
  dsimp only at hstep
  cases hsc : r.senderChain with
  | none =>
    rw [hsc, mut_exec_throw] at hstep
    cases hstep
  | some sc =>
    rw [hsc] at hstep
    dsimp only at hstep
    rw [mut_exec_bind] at hstep
    have htake : RatchetState.takeRootKey.exec r = (.ok r.rootKey, { r with rootKey := 0 }) := rfl
    rw [htake] at hstep
    dsimp only at hstep
    rw [mut_exec_bind, mut_exec_liftE] at hstep
    cases hrc1 : CryptoGames.LibsignalSession.rootCreateChain C r.rootKey their
        sc.ratchetKey.privateKey with
    | error _ =>
      rw [hrc1] at hstep
      cases hstep
    | ok pair1 =>
      rcases pair1 with ⟨rk1, rck⟩
      rw [hrc1] at hstep
      dsimp only at hstep
      rw [mut_exec_bind, mut_exec_liftE] at hstep
      cases hrc2 : CryptoGames.LibsignalSession.rootCreateChain C rk1 their
          (CryptoGames.LibsignalSession.KeyPair.generate C coins).privateKey with
      | error _ =>
        rw [hrc2] at hstep
        cases hstep
      | ok pair2 =>
        rcases pair2 with ⟨rk2, sck⟩
        rw [hrc2] at hstep
        dsimp only at hstep
        rw [mut_exec_bind, mut_exec_modify] at hstep
        dsimp only at hstep
        rw [mut_exec_pure] at hstep
        injection hstep with _ hr'
        subst hr'
        have hlen_app :
            (r.receiverChains ++ [ReceiverChain.mk their (some rck) []]).length =
              r.receiverChains.length + 1 := by
          simp
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · simp only [RatchetState.evictReceiverChains, List.length_drop, maxReceiverChains]
          rw [hlen_app]
          omega
        · intro rc hrc
          have hmem := List.mem_of_mem_drop hrc
          rcases List.mem_append.mp hmem with hmem0 | hmem1
          · exact h.messageKeys_le rc hmem0
          · simp only [List.mem_singleton] at hmem1
            subst hmem1
            simp
        · intro rc hrc mk hmk
          have hmem := List.mem_of_mem_drop hrc
          rcases List.mem_append.mp hmem with hmem0 | hmem1
          · exact h.messageKeySeed_eq rc hmem0 mk hmk
          · simp only [List.mem_singleton] at hmem1
            subst hmem1
            simp at hmk
        · simp [RatchetState.evictReceiverChains]

private theorem ensureReceiverChain_preserves (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    {r r' : RatchetState} {ck : ChainKey} (h : RatchetChainsInv r)
    (hens : (RatchetState.ensureReceiverChain C their coins).exec r = (.ok ck, r')) :
    RatchetChainsInv r' ∧
      ((r.findReceiverChainIndex their).isSome = true →
        r'.receiverChains.length = r.receiverChains.length) ∧
      ((r.findReceiverChainIndex their) = none →
        r'.receiverChains.length =
          (r.receiverChains.length + 1) - ((r.receiverChains.length + 1) - maxReceiverChains)) := by
  unfold RatchetState.ensureReceiverChain at hens
  rw [mut_exec_bind, mut_exec_get] at hens
  dsimp only at hens
  rw [mut_exec_bind, mut_exec_liftE] at hens
  cases hf : r.findReceiverChainKey their with
  | error _ =>
    rw [hf] at hens
    cases hens
  | ok optCk =>
    rw [hf] at hens
    dsimp only at hens
    cases optCk with
    | some ck0 =>
      rw [mut_exec_pure] at hens
      injection hens with _ hr'
      subst hr'
      refine ⟨h, fun _ => rfl, fun hnone => ?_⟩
      unfold RatchetState.findReceiverChainKey at hf
      rw [hnone] at hf
      cases hf
    | none =>
      have hnone : r.findReceiverChainIndex their = none := by
        unfold RatchetState.findReceiverChainKey at hf
        cases hidx : r.findReceiverChainIndex their with
        | none => rfl
        | some idx =>
          rw [hidx] at hf
          dsimp only at hf
          cases hget : r.receiverChains[idx]? with
          | none => rw [hget] at hf; cases hf
          | some c =>
            rw [hget] at hf
            dsimp only at hf
            cases hck : c.chainKey with
            | none => rw [hck] at hf; cases hf
            | some _ => rw [hck] at hf; cases hf
      obtain ⟨hinv', hlen'⟩ := dhRatchetStep_preserves C their coins h hens
      refine ⟨hinv', fun hsome => ?_, fun _ => hlen'⟩
      rw [hnone] at hsome
      cases hsome

private theorem takeSkippedKey_preserves (their : PublicKey) (counter : BitVec 32)
    {r r' : RatchetState} {optK : Option MessageKeyGenerator} (h : RatchetChainsInv r)
    (htake : (RatchetState.takeSkippedKey their counter).exec r = (.ok optK, r')) :
    RatchetChainsInv r' ∧ r'.receiverChains.length = r.receiverChains.length := by
  unfold RatchetState.takeSkippedKey at htake
  rw [mut_exec_bind, mut_exec_get] at htake
  dsimp only at htake
  cases hidx : r.findReceiverChainIndex their with
  | none =>
    rw [hidx, mut_exec_pure] at htake
    injection htake with _ hr'
    subst hr'
    exact ⟨h, rfl⟩
  | some chainIdx =>
    rw [hidx] at htake
    dsimp only at htake
    cases hc : r.receiverChains[chainIdx]? with
    | none =>
      rw [hc, mut_exec_throw] at htake
      cases htake
    | some c =>
      rw [hc] at htake
      dsimp only at htake
      have hcMem : c ∈ r.receiverChains := List.mem_of_getElem? hc
      cases hpos : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with
      | none =>
        rw [hpos, mut_exec_pure] at htake
        injection htake with _ hr'
        subst hr'
        exact ⟨h, rfl⟩
      | some pos =>
        rw [hpos] at htake
        dsimp only at htake
        cases hk : c.messageKeys[pos]? with
        | none =>
          rw [hk, mut_exec_throw] at htake
          cases htake
        | some key =>
          rw [hk] at htake
          dsimp only at htake
          rw [mut_exec_bind, mut_exec_set] at htake
          dsimp only at htake
          rw [mut_exec_pure] at htake
          injection htake with _ hr'
          subst hr'
          refine ⟨⟨?_, ?_, ?_⟩, by simp⟩
          · simpa using h.receiverChains_le
          · intro rc hrc
            rcases mem_set_or r.receiverChains chainIdx _ rc hrc with rfl | hmem
            · exact Nat.le_trans (eraseIdx_length_le c.messageKeys pos) (h.messageKeys_le c hcMem)
            · exact h.messageKeys_le rc hmem
          · intro rc hrc mk hmk
            rcases mem_set_or r.receiverChains chainIdx _ rc hrc with rfl | hmem
            · exact h.messageKeySeed_eq c hcMem mk (mem_eraseIdx_mem c.messageKeys pos hmk)
            · exact h.messageKeySeed_eq rc hmem mk hmk

private theorem storeSkippedKey_preserves (their : PublicKey) (key : MessageKeyGenerator)
    (hseed : key.seed.length = 32) {r r' : RatchetState} (h : RatchetChainsInv r)
    (hstore : (RatchetState.storeSkippedKey their key).exec r = (.ok (), r')) :
    RatchetChainsInv r' ∧ r'.receiverChains.length = r.receiverChains.length := by
  unfold RatchetState.storeSkippedKey at hstore
  rw [mut_exec_bind, mut_exec_get] at hstore
  dsimp only at hstore
  cases hidx : r.findReceiverChainIndex their with
  | none =>
    rw [hidx, mut_exec_throw] at hstore
    cases hstore
  | some chainIdx =>
    rw [hidx] at hstore
    dsimp only at hstore
    cases hc : r.receiverChains[chainIdx]? with
    | none =>
      rw [hc, mut_exec_throw] at hstore
      cases hstore
    | some c =>
      rw [hc] at hstore
      dsimp only at hstore
      rw [mut_exec_set] at hstore
      injection hstore with _ hr'
      subst hr'
      have hcMem : c ∈ r.receiverChains := List.mem_of_getElem? hc
      have hcmk := h.messageKeys_le c hcMem
      refine ⟨⟨by simpa using h.receiverChains_le, ?_, ?_⟩, by simp⟩
      · intro rc hrc
        rcases mem_set_or r.receiverChains chainIdx _ rc hrc with rfl | hmem
        · dsimp only
          split_ifs with hgt
          · simp only [List.length_cons] at hgt
            simp only [List.length_dropLast, List.length_cons]
            omega
          · omega
        · exact h.messageKeys_le rc hmem
      · intro rc hrc mk hmk
        rcases mem_set_or r.receiverChains chainIdx _ rc hrc with rfl | hmem
        · dsimp only at hmk
          have hmk' : mk ∈ key :: c.messageKeys := by
            split_ifs at hmk with hgt
            · exact mem_dropLast_mem (key :: c.messageKeys) hmk
            · exact hmk
          rcases List.mem_cons.mp hmk' with rfl | hmem_c
          · exact hseed
          · exact h.messageKeySeed_eq c hcMem mk hmem_c
        · exact h.messageKeySeed_eq rc hmem mk hmk

private theorem setReceiverChainKey_preserves (their : PublicKey) (ck : ChainKey)
    {r r' : RatchetState} (h : RatchetChainsInv r)
    (hset : (RatchetState.setReceiverChainKey their ck).exec r = (.ok (), r')) :
    RatchetChainsInv r' ∧ r'.receiverChains.length = r.receiverChains.length := by
  unfold RatchetState.setReceiverChainKey at hset
  rw [mut_exec_bind, mut_exec_get] at hset
  dsimp only at hset
  cases hidx : r.findReceiverChainIndex their with
  | none =>
    rw [hidx, mut_exec_throw] at hset
    cases hset
  | some chainIdx =>
    rw [hidx] at hset
    dsimp only at hset
    cases hc : r.receiverChains[chainIdx]? with
    | none =>
      rw [hc, mut_exec_throw] at hset
      cases hset
    | some c =>
      rw [hc] at hset
      dsimp only at hset
      rw [mut_exec_set] at hset
      injection hset with _ hr'
      subst hr'
      have hcMem : c ∈ r.receiverChains := List.mem_of_getElem? hc
      refine ⟨⟨by simpa using h.receiverChains_le, ?_, ?_⟩, by simp⟩
      · intro rc hrc
        rcases mem_set_or r.receiverChains chainIdx _ rc hrc with rfl | hmem
        · exact h.messageKeys_le c hcMem
        · exact h.messageKeys_le rc hmem
      · intro rc hrc mk hmk
        rcases mem_set_or r.receiverChains chainIdx _ rc hrc with rfl | hmem
        · exact h.messageKeySeed_eq c hcMem mk hmk
        · exact h.messageKeySeed_eq rc hmem mk hmk

private theorem advanceChain_preserves (F : ShaCompress) (their : PublicKey) (counter : BitVec 32) :
    ∀ (fuel : ℕ) (ck : ChainKey) {r r' : RatchetState} {ckOut : ChainKey},
      RatchetChainsInv r →
      (RatchetState.advanceChain F their counter fuel ck).exec r = (.ok ckOut, r') →
      RatchetChainsInv r' ∧ r'.receiverChains.length = r.receiverChains.length
  | 0, ck, r, r', ckOut, h, hadv => by
    unfold RatchetState.advanceChain at hadv
    rw [mut_exec_pure] at hadv
    injection hadv with _ hr'
    subst hr'
    exact ⟨h, rfl⟩
  | fuel + 1, ck, r, r', ckOut, h, hadv => by
    unfold RatchetState.advanceChain at hadv
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte] at hadv
      rw [mut_exec_bind] at hadv
      cases hst : (RatchetState.storeSkippedKey their (ck.messageKeys F)).exec r with
      | mk res1 r1 =>
        rw [hst] at hadv
        cases res1 with
        | error _ => cases hadv
        | ok u =>
          dsimp only at hadv
          obtain ⟨h1, hlen1⟩ := storeSkippedKey_preserves their (ck.messageKeys F)
            (chainKey_messageKeys_seed_length F ck) h hst
          rw [mut_exec_bind, mut_exec_liftE] at hadv
          cases hnext : ck.nextChainKey F with
          | error _ =>
            rw [hnext] at hadv
            cases hadv
          | ok ck' =>
            rw [hnext] at hadv
            dsimp only at hadv
            obtain ⟨h2, hlen2⟩ := advanceChain_preserves F their counter fuel ck' h1 hadv
            exact ⟨h2, hlen2.trans hlen1⟩
    · simp only [hlt, ↓reduceIte] at hadv
      rw [mut_exec_pure] at hadv
      injection hadv with _ hr'
      subst hr'
      exact ⟨h, rfl⟩

private theorem consumeMessageKey_preserves (F : ShaCompress) (their : PublicKey)
    (chainKey : ChainKey) (counter : BitVec 32) (msgType : MessageType)
    {r r' : RatchetState} {mkg : MessageKeyGenerator} (h : RatchetChainsInv r)
    (hcons : (RatchetState.consumeMessageKey F their chainKey counter msgType).exec r =
      (.ok mkg, r')) :
    RatchetChainsInv r' ∧ r'.receiverChains.length = r.receiverChains.length := by
  unfold RatchetState.consumeMessageKey at hcons
  by_cases hlt : counter < chainKey.index
  · simp only [hlt, ↓reduceIte] at hcons
    rw [mut_exec_bind] at hcons
    cases htk : (RatchetState.takeSkippedKey their counter).exec r with
    | mk res1 r1 =>
      rw [htk] at hcons
      cases res1 with
      | error _ => cases hcons
      | ok optK =>
        dsimp only at hcons
        obtain ⟨h1, hlen1⟩ := takeSkippedKey_preserves their counter h htk
        cases optK with
        | none =>
          try rw [mut_exec_bind] at hcons
          rw [mut_exec_throw] at hcons
          cases hcons
        | some k =>
          rw [mut_exec_pure] at hcons
          injection hcons with _ hr'
          subst hr'
          exact ⟨h1, hlen1⟩
  · simp only [hlt, ↓reduceIte] at hcons
    rw [mut_exec_bind, mut_exec_get] at hcons
    dsimp only at hcons
    by_cases hjmp : r.maxForwardJumps < (counter - chainKey.index).toNat
    · simp only [hjmp, ↓reduceIte] at hcons
      try rw [mut_exec_bind] at hcons
      rw [mut_exec_throw] at hcons
      cases hcons
    · simp only [hjmp, ↓reduceIte] at hcons
      try rw [mut_exec_bind, mut_exec_pure] at hcons
      rw [mut_exec_bind] at hcons
      cases hadv : (RatchetState.advanceChain F their counter
          (counter - chainKey.index).toNat chainKey).exec r with
      | mk res1 r1 =>
        rw [hadv] at hcons
        cases res1 with
        | error _ => cases hcons
        | ok ck1 =>
          dsimp only at hcons
          obtain ⟨h1, hlen1⟩ := advanceChain_preserves F their counter _ chainKey h hadv
          rw [mut_exec_bind, mut_exec_liftE] at hcons
          cases hnext : ck1.nextChainKey F with
          | error _ =>
            rw [hnext] at hcons
            cases hcons
          | ok ckNext =>
            rw [hnext] at hcons
            dsimp only at hcons
            rw [mut_exec_bind] at hcons
            cases hset : (RatchetState.setReceiverChainKey their ckNext).exec r1 with
            | mk res2 r2 =>
              rw [hset] at hcons
              cases res2 with
              | error _ => cases hcons
              | ok _ =>
                dsimp only at hcons
                rw [mut_exec_pure] at hcons
                injection hcons with _ hr'
                subst hr'
                obtain ⟨h2, hlen2⟩ := setReceiverChainKey_preserves their ckNext h1 hset
                exact ⟨h2, hlen2.trans hlen1⟩

theorem partyReachInv_initB (C : Crypto) (K : MlKem) {P : Params Bytes (BitVec 512)}
    (hspqr : P.spqr = spqrV1SessionUniformCoins C.F K) (k : InitKeys) :
    PartyReachInv C K (P.initB k) := by
  unfold Params.initB initializeRecipientSession SessionState.setSenderChain SessionState.new
  rw [hspqr]
  refine ⟨?_, by simp [maxReceiverChains], ?_, ?_, rfl⟩
  · exact topStateTight_init C.F K .b2a k.pqrKey
  · intro _ hrc; simp at hrc
  · intro _ hrc; simp at hrc

theorem partyReachInv_initA (C : Crypto) (K : MlKem) {P : Params Bytes (BitVec 512)}
    (hspqr : P.spqr = spqrV1SessionUniformCoins C.F K) (k : InitKeys) :
    PartyReachInv C K (P.initA k) := by
  unfold Params.initA
  dsimp only
  have htop0 : TopStateTight C.F K (P.spqr.init .a2b k.pqrKey) := by
    rw [hspqr]
    exact topStateTight_init C.F K .a2b k.pqrKey
  cases hinit : initializeInitiatorSession P.C P.spqr P.idA P.idB
      (CryptoGames.LibsignalSession.KeyPair.generate P.C k.bobSpkCoins).publicKey
      k.rootKey k.chainKey k.pqrKey k.aliceRatchetCoins with
  | error _ =>
    dsimp only [SessionState.setUnacknowledgedPreKeyMessage, SessionState.addReceiverChain,
      SessionState.new]
    have hnot5 : ¬ (5 < 1) := by decide
    refine ⟨htop0, ?_, ?_, ?_, ?_⟩
    · simp [maxReceiverChains]
    · intro rc hrc
      simp only [maxReceiverChains, List.nil_append, List.length_singleton, hnot5, ↓reduceIte,
        List.mem_singleton] at hrc
      subst hrc
      simp
    · intro rc hrc mk hmk
      simp only [maxReceiverChains, List.nil_append, List.length_singleton, hnot5, ↓reduceIte,
        List.mem_singleton] at hrc
      subst hrc
      simp at hmk
    · simp [maxReceiverChains]
  | ok s =>
    unfold initializeInitiatorSession at hinit
    cases hrc : CryptoGames.LibsignalSession.rootCreateChain P.C k.rootKey
        (CryptoGames.LibsignalSession.KeyPair.generate P.C k.bobSpkCoins).publicKey
        (CryptoGames.LibsignalSession.KeyPair.generate P.C k.aliceRatchetCoins).privateKey with
    | error _ =>
      simp [hrc, bind, Except.bind] at hinit
    | ok pair =>
      rcases pair with ⟨rk', ck'⟩
      simp only [hrc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hinit
      subst hinit
      dsimp only [SessionState.setUnacknowledgedPreKeyMessage, SessionState.setSenderChain,
        SessionState.addReceiverChain, SessionState.new]
      have hnot5 : ¬ (5 < 1) := by decide
      refine ⟨htop0, ?_, ?_, ?_, ?_⟩
      · simp [maxReceiverChains]
      · intro rc hrcMem
        simp only [maxReceiverChains, List.nil_append, List.length_singleton, hnot5, ↓reduceIte,
          List.mem_singleton] at hrcMem
        subst hrcMem
        simp
      · intro rc hrcMem mk hmk
        simp only [maxReceiverChains, List.nil_append, List.length_singleton, hnot5, ↓reduceIte,
          List.mem_singleton] at hrcMem
        subst hrcMem
        simp at hmk
      · simp [maxReceiverChains]

theorem partyReachInv_send (C : Crypto) (K : MlKem) {P : Params Bytes (BitVec 512)}
    (hspqr : P.spqr = spqrV1SessionUniformCoins C.F K)
    {g : GhostState Bytes} (hg : PartyReachInv C K g) (m : Bytes) (r : BitVec 512) :
    PartyReachInv C K (P.send g m r).1 := by
  unfold Params.send SessionState.messageEncrypt
  cases hfrom : OutgoingTripleRatchet.fromSessionState.exec g.session with
  | mk resFrom taken =>
    cases resFrom with
    | error _ =>
      dsimp only
      exact hg
    | ok o0 =>
      dsimp only
      have ho0_pq : o0.pqrState = g.session.pqRatchetState ∧
          taken.receiverChains = g.session.receiverChains := by
        unfold OutgoingTripleRatchet.fromSessionState at hfrom
        rw [mut_exec_bind, mut_exec_get] at hfrom
        dsimp only at hfrom
        cases hsc : g.session.senderChain with
        | none =>
          rw [hsc, mut_exec_throw] at hfrom
          cases hfrom
        | some sc =>
          rw [hsc] at hfrom
          dsimp only at hfrom
          rw [mut_exec_bind] at hfrom
          have htpq : SessionState.takePqRatchetState.exec g.session =
              (.ok g.session.pqRatchetState, { g.session with pqRatchetState := default }) := rfl
          rw [htpq] at hfrom
          dsimp only at hfrom
          rw [mut_exec_bind, mut_exec_get] at hfrom
          dsimp only at hfrom
          by_cases hv : 256 ≤ { g.session with pqRatchetState := (default : Bytes) }.version.toNat
          · simp only [hv, ↓reduceIte] at hfrom
            try rw [mut_exec_bind] at hfrom
            rw [mut_exec_throw] at hfrom
            cases hfrom
          · simp only [hv, ↓reduceIte] at hfrom
            try rw [mut_exec_bind, mut_exec_pure] at hfrom
            cases hrem : g.session.remoteIdentity with
            | none =>
              rw [hrem, mut_exec_throw] at hfrom
              cases hfrom
            | some rem =>
              rw [hrem, mut_exec_pure] at hfrom
              injection hfrom with ho htk
              injection ho with ho'
              rw [← ho', ← htk]
              exact ⟨rfl, rfl⟩
      cases henc : (OutgoingTripleRatchet.encrypt P.C P.codec P.spqr m
          (g.session.encryptAddresses (P.sendAddrs g.party)) r).exec o0 with
      | mk resEnc o1 =>
        cases resEnc with
        | error _ =>
          dsimp only
          exact hg
        | ok msg =>
          dsimp only [OutgoingTripleRatchet.applyToSessionState]
          have htop1 : TopStateTight C.F K o1.pqrState := by
            unfold OutgoingTripleRatchet.encrypt at henc
            rw [mut_exec_bind, mut_exec_get] at henc
            dsimp only at henc
            cases hpan : P.spqr.sendPanics o0.pqrState r
            · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at henc
              try rw [mut_exec_bind, mut_exec_pure] at henc
              cases hsp : P.spqr.send o0.pqrState r with
              | none =>
                rw [hsp, mut_exec_throw] at henc
                cases henc
              | some triple =>
                rcases triple with ⟨newPq, pqKey, pqMsg⟩
                rw [hsp] at henc
                dsimp only at henc
                rw [mut_exec_bind, mut_exec_liftE] at henc
                cases hnext : o0.senderChainKey.nextChainKey P.C.F with
                | error _ =>
                  rw [hnext] at henc
                  cases henc
                | ok ckNext =>
                  rw [hnext] at henc
                  dsimp only at henc
                  rw [mut_exec_bind, mut_exec_set] at henc
                  dsimp only at henc
                  rw [mut_exec_pure] at henc
                  injection henc with _ ho1
                  subst ho1
                  rw [hspqr] at hsp
                  change (spqrV1 C.F K).send o0.pqrState (coinBytes r) =
                    some (newPq, pqKey, pqMsg) at hsp
                  rw [ho0_pq.1] at hsp
                  exact topStateTight_send C.F K hg.topTight hsp
            · simp only [hpan, ↓reduceIte] at henc
              try rw [mut_exec_bind] at henc
              rw [mut_exec_throw] at henc
              cases henc
          refine ⟨htop1, ?_, ?_, ?_, ?_⟩
          · rw [ho0_pq.2]; exact hg.receiverChains_le
          · rw [ho0_pq.2]; exact hg.messageKeys_le
          · rw [ho0_pq.2]; exact hg.messageKeySeed_eq
          · rw [ho0_pq.2]; exact hg.aligned

theorem partyReachInv_receive (C : Crypto) (K : MlKem) {P : Params Bytes (BitVec 512)}
    (hC : P.C = C) (hspqr : P.spqr = spqrV1SessionUniformCoins C.F K)
    {g g' : GhostState Bytes} {c m : Bytes} {rc : BitVec 256} {t idx : ℕ}
    (hg : PartyReachInv C K g)
    (hrecv : P.receive g c rc = some (g', t, idx, m)) :
    PartyReachInv C K g' := by
  unfold Params.receive at hrecv
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => rw [htry] at hrecv; cases hrecv
  | ok msg =>
    rw [htry] at hrecv
    dsimp only at hrecv
    cases hdecRec : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
        msg .whisper rc g.session with
    | mk resRec sOut =>
      rw [hdecRec] at hrecv
      cases resRec with
      | error _ => cases hrecv
      | ok mOut =>
        dsimp only at hrecv
        injection hrecv with hquad
        rcases Prod.mk.inj hquad with ⟨rfl, _⟩
        unfold SessionState.tryDecryptFromRecord at hdecRec
        split_ifs at hdecRec with hver
        · cases hdecRec
        · cases hexec : (SessionState.tryDecryptWithState P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper rc).exec g.session with
          | mk resSt sUpd =>
            rw [hexec] at hdecRec
            cases resSt with
            | error _ => cases hdecRec
            | ok ptext =>
              injection hdecRec with _ hsOut
              subst hsOut
              unfold SessionState.tryDecryptWithState at hexec
              rw [mut_exec_bind] at hexec
              cases hfrom : TripleRatchet.fromSessionState.exec g.session with
              | mk resTr sTaken =>
                rw [hfrom] at hexec
                cases resTr with
                | error _ => cases hexec
                | ok tr0 =>
                  dsimp only at hexec
                  have htr0 : tr0.ratchet = ⟨g.session.rootKey, g.session.senderChain,
                      g.session.receiverChains, g.session.previousCounter,
                      CryptoGames.LibsignalSession.maxForwardJumps⟩ ∧
                      tr0.pqrState = g.session.pqRatchetState := by
                    unfold TripleRatchet.fromSessionState at hfrom
                    rw [mut_exec_bind] at hfrom
                    have htr_take : SessionState.takeRatchetState.exec g.session =
                        (.ok ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
                          g.session.previousCounter,
                          CryptoGames.LibsignalSession.maxForwardJumps⟩,
                          { g.session with receiverChains := [] }) := rfl
                    rw [htr_take] at hfrom
                    dsimp only at hfrom
                    rw [mut_exec_bind] at hfrom
                    have htpq_take : SessionState.takePqRatchetState.exec
                        { g.session with receiverChains := [] } =
                        (.ok g.session.pqRatchetState,
                          { g.session with receiverChains := [], pqRatchetState := default }) := rfl
                    rw [htpq_take] at hfrom
                    dsimp only at hfrom
                    rw [mut_exec_bind, mut_exec_get] at hfrom
                    dsimp only at hfrom
                    cases hrem : g.session.remoteIdentity with
                    | none =>
                      rw [hrem, mut_exec_throw] at hfrom
                      cases hfrom
                    | some rem =>
                      rw [hrem, mut_exec_pure] at hfrom
                      injection hfrom with htr_eq _
                      injection htr_eq with htr_eq'
                      rw [← htr_eq']
                      exact ⟨rfl, rfl⟩
                  cases htrDec : (TripleRatchet.decrypt P.C P.spqr (P.expectedAddrs g.party)
                      msg .whisper rc).exec tr0 with
                  | mk resD tr1 =>
                    rw [htrDec, mut_exec_bind, mut_exec_liftE] at hexec
                    cases resD with
                    | error _ => cases hexec
                    | ok pt =>
                      dsimp only at hexec
                      rw [mut_exec_bind, mut_exec_modify] at hexec
                      dsimp only at hexec
                      rw [mut_exec_pure] at hexec
                      injection hexec with _ hsUpd
                      subst hsUpd
                      unfold TripleRatchet.decrypt at htrDec
                      have honRatchet : ∀ {α : Type} (m : Mut RatchetState α) (t : TripleRatchet Bytes),
                          (TripleRatchet.onRatchet m).exec t =
                            match m.exec t.ratchet with
                            | (.error e, r') => (.error e, { t with ratchet := r' })
                            | (.ok a, r') => (.ok a, { t with ratchet := r' }) := by
                        intro α m t
                        unfold TripleRatchet.onRatchet CryptoGames.LibsignalSession.zoom
                        rw [mut_exec_bind, mut_exec_get]
                        dsimp only
                        cases hm : m.exec t.ratchet with
                        | mk res r' =>
                          dsimp only
                          rw [mut_exec_bind, mut_exec_set]
                          dsimp only
                          rw [mut_exec_liftE]
                          cases res <;> rfl
                      have hr0_inv : RatchetChainsInv tr0.ratchet := by
                        rw [htr0.1]
                        exact ⟨hg.receiverChains_le, hg.messageKeys_le, hg.messageKeySeed_eq⟩
                      rw [mut_exec_bind, honRatchet] at htrDec
                      cases hens : (RatchetState.ensureReceiverChain P.C msg.senderRatchetKey
                          rc).exec tr0.ratchet with
                      | mk resEns r1 =>
                        rw [hens] at htrDec
                        cases resEns with
                        | error _ => cases htrDec
                        | ok ck =>
                          dsimp only at htrDec
                          rw [hC] at hens
                          obtain ⟨hr1_inv, hens_some, hens_none⟩ :=
                            ensureReceiverChain_preserves C msg.senderRatchetKey rc hr0_inv hens
                          rw [mut_exec_bind, honRatchet] at htrDec
                          cases hcons : (RatchetState.consumeMessageKey P.C.F msg.senderRatchetKey
                              ck msg.counter .whisper).exec r1 with
                          | mk resCons r2 =>
                            rw [hcons] at htrDec
                            cases resCons with
                            | error _ => cases htrDec
                            | ok mkg =>
                              dsimp only at htrDec
                              obtain ⟨hr2_inv, hcons_len⟩ := consumeMessageKey_preserves P.C.F
                                msg.senderRatchetKey ck msg.counter .whisper hr1_inv hcons
                              rw [mut_exec_bind, mut_exec_get] at htrDec
                              dsimp only at htrDec
                              cases hpan : P.spqr.recvPanics tr0.pqrState msg.pqRatchet
                              · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at htrDec
                                try rw [mut_exec_bind, mut_exec_pure] at htrDec
                                cases hsp : P.spqr.recv tr0.pqrState msg.pqRatchet with
                                | error b =>
                                  rw [hsp] at htrDec
                                  cases b <;> (rw [mut_exec_bind, mut_exec_throw] at htrDec; cases htrDec)
                                | ok pqPair =>
                                  rcases pqPair with ⟨newPq, pqKey⟩
                                  rw [hsp] at htrDec
                                  rw [mut_exec_bind, mut_exec_pure] at htrDec
                                  dsimp only at htrDec
                                  cases hmac : msg.verifyMacWithAddresses P.C.F
                                      (P.expectedAddrs g.party) tr0.remoteIdentityKey
                                      tr0.localIdentityKey (mkg.generateKeys P.C.F pqKey).macKey
                                  · simp only [hmac, Bool.not_false, ↓reduceIte] at htrDec
                                    try rw [mut_exec_bind] at htrDec
                                    rw [mut_exec_throw] at htrDec
                                    cases htrDec
                                  · simp only [hmac, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htrDec
                                    try rw [mut_exec_bind, mut_exec_pure] at htrDec
                                    cases haes : CryptoGames.LibsignalSession.aesCbcDecrypt P.C.D
                                        (mkg.generateKeys P.C.F pqKey).cipherKey
                                        (mkg.generateKeys P.C.F pqKey).iv msg.ciphertext with
                                    | none =>
                                      rw [haes, mut_exec_throw] at htrDec
                                      cases htrDec
                                    | some ptBytes =>
                                      rw [haes] at htrDec
                                      dsimp only at htrDec
                                      rw [mut_exec_bind, mut_exec_modify] at htrDec
                                      dsimp only at htrDec
                                      rw [mut_exec_pure] at htrDec
                                      injection htrDec with _ htr1
                                      subst htr1
                                      rw [hspqr, htr0.2] at hsp
                                      change (spqrV1 C.F K).recv g.session.pqRatchetState
                                        msg.pqRatchet = .ok (newPq, pqKey) at hsp
                                      have htop' : TopStateTight C.F K newPq :=
                                        topStateTight_recv C.F K hg.topTight hsp
                                      dsimp only [TripleRatchet.applyToSessionState,
                                        SessionState.clearUnacknowledgedPreKeyMessage]
                                      refine ⟨htop', hr2_inv.receiverChains_le,
                                        hr2_inv.messageKeys_le, hr2_inv.messageKeySeed_eq, ?_⟩
                                      have hfIdx : tr0.ratchet.findReceiverChainIndex
                                          msg.senderRatchetKey =
                                          g.session.receiverChains.findIdx?
                                            (·.senderRatchetKey == msg.senderRatchetKey) := by
                                        rw [htr0.1]; rfl
                                      have htr0_len : tr0.ratchet.receiverChains.length =
                                          g.session.receiverChains.length := by
                                        rw [htr0.1]
                                      cases hfind : g.session.receiverChains.findIdx?
                                          (·.senderRatchetKey == msg.senderRatchetKey) with
                                      | some i =>
                                        have hlen_eq : r2.receiverChains.length =
                                            g.session.receiverChains.length := by
                                          rw [hcons_len, hens_some (by rw [hfIdx, hfind]; rfl),
                                            htr0_len]
                                        simp [hlen_eq, hg.aligned]
                                      | none =>
                                        have hlen_eq : r2.receiverChains.length =
                                            (g.session.receiverChains.length + 1) -
                                              ((g.session.receiverChains.length + 1) -
                                                maxReceiverChains) := by
                                          rw [hcons_len, hens_none (by rw [hfIdx, hfind]), htr0_len]
                                        have hrc_le := hg.receiverChains_le
                                        simp only [List.length_drop, List.length_append,
                                          List.length_singleton, hg.aligned, hlen_eq,
                                          maxReceiverChains] at hrc_le ⊢
                                        omega
                              · simp only [hpan, ↓reduceIte] at htrDec
                                try rw [mut_exec_bind] at htrDec
                                rw [mut_exec_throw] at htrDec
                                cases htrDec

theorem partyReachInv_fixedSpk_initA (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ : ℕ) (s : BitVec 256) (k : SampledSessionKey) :
    PartyReachInv C K
      ((sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ s).initA k) :=
  partyReachInv_initA C K rfl _

theorem partyReachInv_fixedSpk_initB (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ : ℕ) (s : BitVec 256) (k : SampledSessionKey) :
    PartyReachInv C K
      ((sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ s).initB k) :=
  partyReachInv_initB C K rfl _

theorem partyReachInv_fixedSpk_send (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ : ℕ) (s : BitVec 256) {g : GhostState Bytes} (hg : PartyReachInv C K g)
    (m : Plain ℓ) (r : BitVec 512) :
    PartyReachInv C K
      ((sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ s).send g m r).1 :=
  partyReachInv_send C K rfl hg m.toList r

theorem partyReachInv_fixedSpk_receive (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ : ℕ) (s : BitVec 256) {g g' : GhostState Bytes} {c : Bytes} {rc : BitVec 256}
    {t idx : ℕ} {m : Plain ℓ} (hg : PartyReachInv C K g)
    (hrecv : (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ s).receive g c rc = some (g', t, idx, m)) :
    PartyReachInv C K g' := by
  dsimp only [sessionSchemeFixedSpk] at hrecv
  rcases Option.mem_map.mp hrecv with ⟨⟨g1, t1, idx1, m1⟩, hraw, htup⟩
  injection htup with hg_eq _
  subst hg_eq
  exact partyReachInv_receive C K rfl rfl hg hraw

end Computational.Proofs.E2E.Dsl.SmReachInvParty

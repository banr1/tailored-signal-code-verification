/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
public import Symbolic.Proofs.Swarm.CREF.TR.PureSessionBounds
public import Symbolic.Proofs.Refinement.RecordBytesBridge
public import Symbolic.Proofs.SR.ModelW
import Symbolic.Proofs.Refinement.LemmasPure
import Symbolic.Proofs.RngG.R3ModelInv
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Returned Record and Message of Accepting Pre-Key Receive

Defines Bob's post-handshake session record `bobNewSession` and proves sender-key clamping
preservation and record canonicality for an accepting `session_recv_prekey` call.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.LibsignalTripleRatchet

/-- Bob's session record after an accepting `session_recv_prekey` call. -/
abbrev bobNewSession (st' : SessionState HwBytes) (aliceBaseBytes : HwBytes)
    (f248 regIdB : BitVec 32) : Session HwBytes :=
  { state := st', pendingPreKey := none, pendingKyberPreKey := none,
    aliceBaseKey := aliceBaseBytes, remoteRegistrationId := f248,
    localRegistrationId := regIdB }

section PureSenderClamp

@[local simp] private theorem rpk_exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl
@[local simp] private theorem rpk_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl
@[local simp] private theorem rpk_exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a) s = (.ok a, s) := rfl
@[local simp] private theorem rpk_exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl
@[local simp] private theorem rpk_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok (), f s) := rfl
@[local simp] private theorem rpk_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl
@[local simp] private theorem rpk_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r) s = (r, s) := by cases r <;> rfl
@[local simp] private theorem rpk_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec; change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]; simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩; cases r <;> rfl

private theorem rpk_clampScalar_idem (v : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar v) = Ratchet.clampScalar v := by
  apply List.Vector.ext; intro j
  by_cases h31 : j = 31
  · subst h31; simp only [Ratchet.clampScalar, List.Vector.get_set_same]
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_self, BitVec.or_assoc]; rfl
  · by_cases h0 : j = 0
    · subst h0; simp only [Ratchet.clampScalar, List.Vector.get_set_of_ne (Ne.symm h31),
        List.Vector.get_set_same]
      rw [BitVec.and_assoc, BitVec.and_self]
    · simp only [Ratchet.clampScalar, List.Vector.get_set_of_ne (Ne.symm h31),
        List.Vector.get_set_of_ne (Ne.symm h0)]

private theorem rpk_takeSkippedKey_senderChain (their : PublicKey) (counter : BitVec 32) (r : RatchetState) :
    (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.senderChain = r.senderChain := by
  unfold RatchetState.takeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp [h1, h2]
    · rcases h3 : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos
      · simp [h1, h2, h3]
      · rcases h4 : c.messageKeys[pos]? with _ | key
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

private theorem rpk_storeSkippedKey_senderChain (their : PublicKey) (key : MessageKeyGenerator)
    (r : RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) r).2.senderChain = r.senderChain := by
  unfold RatchetState.storeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c <;> simp [h1, h2]

private theorem rpk_setReceiverChainKey_senderChain (their : PublicKey) (ck : ChainKey) (r : RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.senderChain = r.senderChain := by
  unfold RatchetState.setReceiverChainKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c <;> simp [h1, h2]

private theorem rpk_advanceChain_senderChain (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) (fuel : Nat) (ck : ChainKey) (r : RatchetState) :
    (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.senderChain = r.senderChain := by
  induction fuel generalizing ck r with
  | zero => rfl
  | succ fuel ih =>
    unfold RatchetState.advanceChain
    split
    · rw [rpk_exec_bind]
      have h1 := rpk_storeSkippedKey_senderChain their (ck.messageKeys F) r
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with ⟨_ | _, r1⟩
      · rw [hs] at h1; exact h1
      · rw [hs] at h1; simp only [rpk_exec_bind, rpk_exec_liftE]
        rcases hn : ck.nextChainKey F with _ | ck'
        · exact h1
        · exact (ih ck' r1).trans h1
    · rfl

private theorem rpk_consumeMessageKey_senderChain (F : ShaCompress) (their : PublicKey) (ck : ChainKey)
    (counter : BitVec 32) (msgType : MessageType) (r : RatchetState) :
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.senderChain =
      r.senderChain := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, rpk_exec_bind]
    have h1 := rpk_takeSkippedKey_senderChain their counter r
    rcases ht : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨_ | opt, r1⟩
    · rw [ht] at h1; exact h1
    · rw [ht] at h1; cases opt <;> simpa using h1
  · simp only [hlt, ↓reduceIte, rpk_exec_bind, rpk_exec_get]
    split
    · rfl
    · rw [rpk_exec_bind]
      have h1 := rpk_advanceChain_senderChain F their counter (counter - ck.index).toNat ck r
      rcases ha : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck)
          r with ⟨_ | ck1, r1⟩
      · rw [ha] at h1; exact h1
      · rw [ha] at h1; simp only [rpk_exec_bind, rpk_exec_liftE]
        rcases hn : ck1.nextChainKey F with _ | ck2
        · exact h1
        · simp only [rpk_exec_pure]
          have h2 := rpk_setReceiverChainKey_senderChain their ck2 r1
          rcases hs : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with ⟨_ | _, r2⟩ <;>
            · rw [hs] at h2; exact h2.trans h1

private theorem rpk_dhRatchetStep_senderClamp (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState)
    (h : ∀ sc, r.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes) :
    ∀ sc, (Mut.exec (RatchetState.dhRatchetStep C their coins) r).2.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes := by
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey
  simp only [rpk_exec_bind, rpk_exec_get]
  rcases hsc : r.senderChain with _ | sc0
  · simpa using h
  · simp only [rpk_exec_bind, rpk_exec_modifyGet, rpk_exec_liftE]
    rcases hrc1 : rootCreateChain C r.rootKey their sc0.ratchetKey.privateKey with _ | ⟨newRootKey, _⟩
    · exact h
    · simp only [rpk_exec_modify, rpk_exec_pure]
      rcases hrc2 : rootCreateChain C newRootKey their (KeyPair.generate C coins).privateKey with _
          | ⟨_, _⟩
      · exact h
      · intro sc hsc'; simp only [Option.some.injEq] at hsc'; subst hsc'
        exact rpk_clampScalar_idem (Ratchet.keyToBytesVec32 coins)

private theorem rpk_ensureReceiverChain_senderClamp (C : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState)
    (h : ∀ sc, r.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes) :
    ∀ sc, (Mut.exec (RatchetState.ensureReceiverChain C their coins) r).2.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes := by
  unfold RatchetState.ensureReceiverChain
  simp only [rpk_exec_bind, rpk_exec_get, rpk_exec_liftE]
  rcases hf : r.findReceiverChainKey their with _ | (_ | _)
  · exact h
  · exact rpk_dhRatchetStep_senderClamp C their coins r h
  · simpa using h

end PureSenderClamp

theorem e5_senderClamp_of_decrypt {PQ PQC : Type} [Inhabited PQ]
    {C : Crypto} {W : Proofs.libsignal.SR.AesW} {spqr : Spqr PQ PQC}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st0 st' : SessionState PQ} {pt : List (BitVec 8)}
    (hcl0 : ∀ sc, st0.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hdec : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W spqr expected msg
      msgType coins) st0 = (.ok pt, st')) :
    (∀ sc, st'.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes) ∧
    st'.remoteIdentity = st0.remoteIdentity := by
  obtain ⟨_remIk, _tr_out, _hrem, htr, hst'⟩ :=
    Proofs.libsignal.RngG.R3.tryDecryptWithStateW_ok_inv hdec
  obtain ⟨ck, r1, r2, _mkGen, _newPqr, _pqrKey, hens, hcons, _, _, _, htr_out⟩ :=
    Proofs.libsignal.RngG.R3.tripleRatchet_decryptW_ok_inv htr
  subst hst'
  subst htr_out
  refine ⟨?_, rfl⟩
  intro sc hsc
  have hsc' : r2.senderChain = some sc := hsc
  have h2 := rpk_consumeMessageKey_senderChain C.F
    msg.senderRatchetKey ck msg.counter msgType r1
  rw [hcons] at h2
  have h1 := rpk_ensureReceiverChain_senderClamp C
    msg.senderRatchetKey coins
    ⟨st0.rootKey, st0.senderChain, st0.receiverChains, st0.previousCounter,
      CryptoGames.LibsignalSession.maxForwardJumps⟩ hcl0
  rw [hens] at h1
  exact h1 sc (h2 ▸ hsc')

structure RpkAcceptBin (pf : PreKeyFields) (sm : StateAndMessage) : Prop where
  record : ∃ (st' : SessionState HwBytes) (f248 regIdB : BitVec 32),
    TR.Pure.slots_RecordInScopeP
      ⟨some (bobNewSession st' (pf.baseKey.take 33) f248 regIdB)⟩ ∧
    TR.Pure.BinSessionInv
      (bobNewSession st' (pf.baseKey.take 33) f248 regIdB) ∧
    (∀ sc, st'.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes =
        sc.ratchetKey.privateKey.bytes) ∧
    sm.state = CryptoVerification.E2E.Record.encodeRecord
      ⟨some (bobNewSession st' (pf.baseKey.take 33) f248 regIdB)⟩
  kyberUsed : (sm.message[kyberUsedIdx]?).any (· != 0#8) = true
  baseKey : slice sm.message 9 33 = pf.baseKey.take 33

private theorem rpk_flatten_map_lenField_length_ge {α : Type} (tag : Nat)
    (f : α → List (BitVec 8)) (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤
      ((l.map fun c => CryptoVerification.E2E.Record.lenField tag (f c)).flatten).length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

private theorem rpk_encReceiverChain_length_le_encSession (s : Session (List (BitVec 8)))
    (rc : ReceiverChain) (hrc : rc ∈ s.state.receiverChains) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  have h1 := rpk_flatten_map_lenField_length_ge 7 CryptoVerification.E2E.Record.encReceiverChain
    s.state.receiverChains rc hrc
  unfold CryptoVerification.E2E.Record.encSession; simp only [List.length_append]; omega

theorem b2_encodeRecord_ne_nil (s : Session (List (BitVec 8))) :
    CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩ ≠ [] := by
  unfold CryptoVerification.E2E.Record.encodeRecord
    CryptoVerification.E2E.Record.msgField
    CryptoVerification.E2E.Record.lenField
  have hk : CryptoVerification.LibsignalProtoCodec.encodeKey 1 .lengthDelimited = [0x0a#8] := rfl
  rw [hk]; simp

theorem recvPrekey_accept_record
    {st' : SessionState HwBytes} {aliceBaseBytes : HwBytes} {f248 regIdB : BitVec 32}
    (_hscope : TR.Pure.slots_RecordInScopeP
      ⟨some (bobNewSession st' aliceBaseBytes f248 regIdB)⟩)
    (hinv : TR.Pure.BinSessionInv
      (bobNewSession st' aliceBaseBytes f248 regIdB))
    (_halice : aliceBaseBytes.length = 33)
    (_hclamp : ∀ sc, st'.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    {smState : HwBytes}
    (hsm : smState = CryptoVerification.E2E.Record.encodeRecord
      ⟨some (bobNewSession st' aliceBaseBytes f248 regIdB)⟩) :
    ∃ rr : DY.Libsignal.Rust.RecordRec,
      smState = DY.Libsignal.Composed.Refinement.recordBytes rr ∧
      rr.previous = [] ∧
      rr.current = Swarm.Phase0WholeFunctionBridge.sessionToSessionRec
        (bobNewSession st' aliceBaseBytes f248 regIdB) ∧
      rr.current.pendingPreKey = none ∧ rr.current.pendingKyberPreKey = none := by
  obtain ⟨_hwf, _hrc_len, hrc_mk, halice_lt, _hkyb, hpq_lt, henc_lt⟩ := hinv
  have hsess_lt : (CryptoVerification.E2E.Record.encSession
      (bobNewSession st' aliceBaseBytes f248 regIdB)).length < 2 ^ 64 := by
    have h62 : (CryptoVerification.E2E.Record.encSession
        (bobNewSession st' aliceBaseBytes f248 regIdB)).length < 2 ^ 62 := henc_lt
    omega
  have hseeds : ∀ rc ∈ (bobNewSession st' aliceBaseBytes f248 regIdB).state.receiverChains,
      ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63 := by
    intro rc hrc mk hmk
    have h32 := (hrc_mk rc hrc).2 mk hmk
    omega
  have htr := Swarm.Phase0WholeFunctionBridge.recordBytes_sessionToRecordRec_eq_encodeRecord
    (bobNewSession st' aliceBaseBytes f248 regIdB) rfl rfl
    (by omega) (by omega) hseeds
    (fun rc hrc' => Nat.lt_of_le_of_lt (rpk_encReceiverChain_length_le_encSession _ rc hrc') hsess_lt)
    hsess_lt
  exact ⟨Swarm.Phase0WholeFunctionBridge.sessionToRecordRec
    (bobNewSession st' aliceBaseBytes f248 regIdB), hsm.trans htr.symm, rfl, rfl, rfl, rfl⟩

theorem e5l_ofFn_getD_toList (l : List (BitVec 8)) (hl : l.length = 32) :
    (List.Vector.ofFn (n := 32) (fun i => l.getD i.val 0#8)).toList = l := by
  apply List.ext_getElem
  · simp [hl]
  · intro n _h1 h2
    simp only [List.Vector.toList_ofFn, List.getElem_ofFn]
    simp [List.getD_eq_getElem?_getD, h2]

theorem e5l_clamp_fix (k : List (BitVec 8)) (hk : k.length = 32) :
    Ratchet.clampScalar (List.Vector.ofFn (n := 32) (fun i =>
        (DY.Libsignal.TripleRatchet.Refinement.clamp k).getD i.val 0#8)) =
      List.Vector.ofFn (n := 32) (fun i =>
        (DY.Libsignal.TripleRatchet.Refinement.clamp k).getD i.val 0#8) := by
  have hcl : (DY.Libsignal.TripleRatchet.Refinement.clamp k).length = 32 := by
    unfold DY.Libsignal.TripleRatchet.Refinement.clamp; simp [hk]
  apply Subtype.ext
  change (Ratchet.clampScalar _).toList = (List.Vector.ofFn _).toList
  rw [Proofs.libsignal.RngG.CliPure.DecCrypto.clampScalar_toList_eq_clamp_toList,
    e5l_ofFn_getD_toList _ hcl, DY.Libsignal.TripleRatchet.Refinement.clamp_clamp]

theorem recvPrekey_accept_canonQ
    {st' : SessionState HwBytes} {aliceBaseBytes : HwBytes} {f248 regIdB : BitVec 32}
    (hscope : TR.Pure.slots_RecordInScopeP
      ⟨some (bobNewSession st' aliceBaseBytes f248 regIdB)⟩)
    (hinv : TR.Pure.BinSessionInv
      (bobNewSession st' aliceBaseBytes f248 regIdB))
    (halice : aliceBaseBytes.length = 33)
    (hclamp : ∀ sc, st'.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes) :
    TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q
      (CryptoVerification.E2E.Record.encodeRecord
        ⟨some (bobNewSession st' aliceBaseBytes f248 regIdB)⟩)
      (bobNewSession st' aliceBaseBytes f248 regIdB) := by
  have ⟨hwf, hrc_len, hrc_mk, halice_lt, _hkyb, hpq, _henc⟩ := hinv
  let s := bobNewSession st' aliceBaseBytes f248 regIdB
  have hq : TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q ⟨some s⟩ := by
    intro s' hs; cases hs; exact hpq
  have hrepr : TR.Pure.PureRecordRepr ⟨some s⟩ := by
    intro s' hs; cases hs
    exact ⟨fun c hc => (hrc_mk c hc).1, hclamp, hwf, halice_lt⟩
  have hsc : TR.Pure.slots_SessionScopeP s :=
    ⟨hrc_len, (fun _ h => by cases h), (fun _ h => by cases h), Or.inr halice⟩
  exact ⟨rfl, ⟨⟨hscope, hq, hrepr⟩, s, rfl, hsc⟩, hinv⟩

theorem recvPrekey_accept_canon (r₀ : ProtocolSetup) (p : DY.Participant)
    {st' : SessionState HwBytes} {aliceBaseBytes : HwBytes} {f248 regIdB : BitVec 32}
    {remIk : IdentityKey}
    (hscope : TR.Pure.slots_RecordInScopeP
      ⟨some (bobNewSession st' aliceBaseBytes f248 regIdB)⟩)
    (hinv : TR.Pure.BinSessionInv
      (bobNewSession st' aliceBaseBytes f248 regIdB))
    (hrem : st'.remoteIdentity = some remIk)
    (halice : aliceBaseBytes.length = 33)
    (hclamp : ∀ sc, st'.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hooo : SpqrOooBounded st'.pqRatchetState)
    (hlen : (CryptoVerification.E2E.Record.encodeRecord
      ⟨some (bobNewSession st' aliceBaseBytes f248 regIdB)⟩).length < 2 ^ 32 - 2 ^ 20) :
    TR.PureTRRecordCanon r₀ p
      (CryptoVerification.E2E.Record.encodeRecord
        ⟨some (bobNewSession st' aliceBaseBytes f248 regIdB)⟩) := by
  have ⟨_hwf, _hrc_len, _hrc_mk, _halice_lt, _hkyb, hpq, _henc⟩ := hinv
  have hq : TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q
      ⟨some (bobNewSession st' aliceBaseBytes f248 regIdB)⟩ := by
    intro s hs; cases hs; exact hpq
  have hc := recvPrekey_accept_canonQ hscope hinv halice hclamp
  have hlt : (CryptoVerification.E2E.Record.encodeRecord
      ⟨some (bobNewSession st' aliceBaseBytes f248 regIdB)⟩).length < 2 ^ 62 := by omega
  refine ⟨bobNewSession st' aliceBaseBytes f248 regIdB, hc, hscope, hq, ?_, hlt, rfl, hlen, hooo⟩
  show st'.remoteIdentity.isSome
  rw [hrem]; rfl

end Symbolic.Swarm.CREF.CliPure

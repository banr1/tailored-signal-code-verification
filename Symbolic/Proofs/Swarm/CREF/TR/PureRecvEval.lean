/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.TRREF.GrowthRecordPure
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.BobKyberNone
public import Symbolic.Proofs.Swarm.CREF.RelPure
public import Symbolic.Proofs.Swarm.TRREF.B3DefsPure
import Symbolic.Proofs.Swarm.CREF.OooPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.TRREF.EncodeRecordPqInj

/-!
# Pure Whisper Receive Evaluation and Canonical Gate Helpers

Defines pure whisper-receive evaluation (`pureDrawsCoins`, `PureDecryptCoinsOk`,
`pureEvalRecvWireWithCoinsW`) and proves canonical record inversion and post-state bounds for
`recv_wire` verification.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval
open Symbolic.Swarm.CREF.TR hiding runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.HwEvents
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin (Role evalOpen storedSession inMemAnswers)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open Proofs.libsignal.SR
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.TRREF.GrowthRecordPure (pureSpqr)

/-! ## Pure Address Serialization, Coins, and `pureEvalRecvWireWithCoinsW` -/

def pureRoleParty : Role → CryptoGames.Party
  | .alice => .A
  | .bob => .B

def pureSerializeRole (sender recipient : Role) : Option (List (BitVec 8)) :=
  CryptoVerification.E2E.serializedPartyAddresses CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
    (pureRoleParty sender) (pureRoleParty recipient)

def pureCoinsOf (rest : List (BitVec 8)) : BitVec 256 :=
  HKDF.bytesToKey32 ((rest ++ List.replicate 32 0#8).take 32)

/-- Pure predicate testing whether `try_decrypt_with_state` reaches `KeyPair.generate`. -/
def pureDrawsCoins {PQ : Type} (C : Crypto) (st : SessionState PQ) (their : PublicKey) : Bool :=
  st.remoteIdentity.isSome &&
    match RatchetState.findReceiverChainKey
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
        their with
    | .ok none =>
      match st.senderChain with
      | some sc =>
        match rootCreateChain C st.rootKey their sc.ratchetKey.privateKey with
        | .ok _ => true
        | .error _ => false
      | none => false
    | _ => false

theorem pureDrawsCoins_false_of_found {PQ : Type} {C : Crypto} {st : SessionState PQ}
    {their : PublicKey} {ck : ChainKey}
    (hfind : RatchetState.findReceiverChainKey
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
        their = .ok (some ck)) :
    pureDrawsCoins C st their = false := by
  unfold pureDrawsCoins
  simp [hfind]

theorem pureDrawsCoins_true_of_ratchet {PQ : Type} {C : Crypto} {st : SessionState PQ}
    {their : PublicKey} {remIk : IdentityKey} {sc : SenderChain} {rk1 : BitVec 256} {ck : ChainKey}
    (hrem : st.remoteIdentity = some remIk)
    (hfind : RatchetState.findReceiverChainKey
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
        their = .ok none)
    (hsc : st.senderChain = some sc)
    (hcc : rootCreateChain C st.rootKey their sc.ratchetKey.privateKey = .ok (rk1, ck)) :
    pureDrawsCoins C st their = true := by
  unfold pureDrawsCoins
  rw [hfind]
  simp [hrem, hsc, hcc]

theorem pureDrawsCoins_cases {PQ : Type} (C : Crypto) (st : SessionState PQ) (their : PublicKey)
    (h : pureDrawsCoins C st their = true) :
    RatchetState.findReceiverChainKey
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
        their = .ok none ∧
      ∃ sc r, st.senderChain = some sc ∧
        rootCreateChain C st.rootKey their sc.ratchetKey.privateKey = .ok r := by
  unfold pureDrawsCoins at h
  rw [Bool.and_eq_true] at h; obtain ⟨_, h⟩ := h
  split at h
  · rename_i hf; refine ⟨hf, ?_⟩
    split at h
    · rename_i sc hsc
      split at h
      · rename_i r hr; exact ⟨sc, r, hsc, hr⟩
      · cases h
    · cases h
  · cases h

/-- Pure coin well-formedness predicate for `pureEvalRecvWireWithCoinsW`. -/
def PureDecryptCoinsOk {PQ : Type} (C : Crypto) (st : SessionState PQ) (their : PublicKey)
    (coins : BitVec 256) : Prop :=
  (pureDrawsCoins C st their = false → coins = 0#256) ∧
  (pureDrawsCoins C st their = true →
    ∃ bs : List (BitVec 8), bs.length = 32 ∧ coins = pureCoinsOf bs)

theorem pureDecryptCoinsOk_of_draws_false {PQ : Type} {C : Crypto} {st : SessionState PQ}
    {their : PublicKey} (h : pureDrawsCoins C st their = false) :
    PureDecryptCoinsOk C st their 0#256 :=
  ⟨fun _ => rfl, fun ht => by rw [h] at ht; cases ht⟩

theorem pureDecryptCoinsOk_of_draws_true {PQ : Type} {C : Crypto} {st : SessionState PQ}
    {their : PublicKey} {bs : List (BitVec 8)}
    (h : pureDrawsCoins C st their = true) (hlen : bs.length = 32) :
    PureDecryptCoinsOk C st their (pureCoinsOf bs) :=
  ⟨(by intro hf; rw [h] at hf; cases hf), fun _ => ⟨bs, hlen, rfl⟩⟩

@[local simp] private theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

@[local simp] private theorem exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

@[local simp] private theorem exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl

@[local simp] private theorem exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok (), f s) := rfl

@[local simp] private theorem exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

@[local simp] private theorem exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

@[local simp] private theorem exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

@[local simp] private theorem exec_onRatchet {PQ α : Type} (m : Mut RatchetState α)
    (t : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) t =
      ((Mut.exec m t.ratchet).1, { t with ratchet := (Mut.exec m t.ratchet).2 }) := by
  unfold TripleRatchet.onRatchet zoom
  simp

theorem ensureReceiverChain_coins_irrel_of_pureDrawsCoins_false {PQ : Type}
    (C : Crypto) (st : SessionState PQ) (their : PublicKey) (c₁ c₂ : BitVec 256)
    (hrem : st.remoteIdentity.isSome = true)
    (hno : pureDrawsCoins C st their = false) :
    let r0 : RatchetState :=
      ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
    Mut.exec (RatchetState.ensureReceiverChain C their c₁) r0 =
      Mut.exec (RatchetState.ensureReceiverChain C their c₂) r0 := by
  intro r0
  unfold pureDrawsCoins at hno
  rw [hrem, Bool.true_and] at hno
  change (match RatchetState.findReceiverChainKey r0 their with
    | .ok none =>
      match st.senderChain with
      | some sc =>
        match rootCreateChain C st.rootKey their sc.ratchetKey.privateKey with
        | .ok _ => true
        | .error _ => false
      | none => false
    | _ => false) = false at hno
  unfold RatchetState.ensureReceiverChain
  simp only [exec_bind, exec_get, exec_liftE]
  rcases hf : r0.findReceiverChainKey their with e | (_ | ck)
  · rfl
  · simp only [hf] at hno
    dsimp only [r0]
    unfold RatchetState.dhRatchetStep RatchetState.takeRootKey
    simp only [exec_bind, exec_get]
    rcases hsc : st.senderChain with _ | sc
    · rfl
    · simp only [hsc] at hno
      simp only [exec_bind, exec_modifyGet, exec_liftE]
      rcases hrc : rootCreateChain C st.rootKey their sc.ratchetKey.privateKey with err | rkck
      · rfl
      · rw [hrc] at hno; cases hno
  · rfl

theorem tryDecryptFromRecordW_coins_irrel_of_pureDrawsCoins_false {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (W_aes : AesW) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (msg : SignalMessage) (msgType : MessageType)
    (c₁ c₂ : BitVec 256) (st : SessionState PQ)
    (hrem : st.remoteIdentity.isSome = true)
    (hno : pureDrawsCoins C st msg.senderRatchetKey = false) :
    Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW C W_aes spqr expected msg msgType c₁ st =
      Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW C W_aes spqr expected msg msgType c₂ st := by
  unfold Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW
  split
  · rfl
  · suffices h : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W_aes spqr
        expected msg msgType c₁) st =
        Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W_aes spqr
          expected msg msgType c₂) st by
      rw [h]
    cases hrem_opt : st.remoteIdentity with
    | none => rw [hrem_opt] at hrem; cases hrem
    | some remIk =>
      have hens := ensureReceiverChain_coins_irrel_of_pureDrawsCoins_false C st msg.senderRatchetKey
        c₁ c₂ hrem hno
      unfold Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
        TripleRatchet.fromSessionState SessionState.takeRatchetState SessionState.takePqRatchetState
      simp only [exec_bind, exec_get, exec_modifyGet, exec_liftE, exec_modify, exec_pure, hrem_opt]
      suffices htr : ∀ (tr : TripleRatchet PQ),
          tr.ratchet = ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ →
          Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C W_aes spqr expected msg msgType c₁) tr =
            Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C W_aes spqr expected msg msgType c₂) tr by
        rw [htr _ rfl]
      intro tr htr_eq
      unfold Proofs.libsignal.SR.TripleRatchet.decryptW
      simp only [exec_bind, exec_onRatchet]
      rw [htr_eq, hens]

/-- Pure `evalRecvWireWithCoinsW` over `pureSpqr S` and `pureSerializeRole`. -/
def pureEvalRecvWireWithCoinsW (C : Crypto) (W : AesW) (S : SpqrModel)
    (g : RecvWireGhost) (coins : BitVec 256) :
    Option (List (BitVec 8) × List (BitVec 8)) :=
  match g.wireBytes with
  | 2#8 :: body =>
    match SignalMessage.tryFrom protoSignalCodec body with
    | .error _ => none
    | .ok msg =>
      match evalOpen g.who g.sess with
      | none => none
      | some (role, sess) =>
        let (res, calls) := messageDecryptSignalW C W (pureSpqr S) pureSerializeRole
          (inMemAnswers sess) msg role.peer role coins
        match res with
        | .ok ptBytes =>
          some (encodeRecord ⟨some (storedSession sess calls)⟩, ptBytes)
        | .error _ => none
  | _ => none

/-! ## Pure `WireRecCanon` and `TRRecordCanon` Inversion and Gate -/

theorem pureEvalRecvWireWithCoinsW_some_inv {C : Crypto} {W : AesW} {S : SpqrModel}
    {g : RecvWireGhost} {coins : BitVec 256} {out : List (BitVec 8) × List (BitVec 8)}
    (h : pureEvalRecvWireWithCoinsW C W S g coins = some out) :
    ∃ (body : List (BitVec 8)) (msg : SignalMessage) (role : Role),
      g.wireBytes = 2#8 :: body ∧
      SignalMessage.tryFrom protoSignalCodec body = .ok msg ∧
      evalOpen g.who g.sess = some (role, g.sess) ∧
      out.1 = encodeRecord ⟨some (storedSession g.sess
        (messageDecryptSignalW C W (pureSpqr S) pureSerializeRole (inMemAnswers g.sess) msg
          role.peer role coins).2)⟩ := by
  unfold pureEvalRecvWireWithCoinsW at h
  split at h
  · rename_i body hw
    rcases hm : SignalMessage.tryFrom protoSignalCodec body with _ | msg
    · rw [hm] at h; cases h
    · rw [hm] at h; dsimp only at h
      rcases ho : evalOpen g.who g.sess with _ | ⟨role, sess⟩
      · rw [ho] at h; cases h
      · have hsess : sess = g.sess := by
          have ho' := ho; unfold evalOpen at ho'
          cases hwho : Role.ofWho g.who with
          | none => simp [hwho] at ho'
          | some r => simp [hwho] at ho'; exact ho'.2.symm
        subst hsess
        rw [ho] at h; dsimp only at h
        rcases hdc : messageDecryptSignalW C W (pureSpqr S) pureSerializeRole
            (inMemAnswers g.sess) msg role.peer role coins with ⟨err | ptBytes, calls⟩
        · rw [hdc] at h; cases h
        · rw [hdc] at h; simp only [Option.some.injEq] at h; subst h
          exact ⟨body, msg, role, hw, hm, rfl, by rw [hdc]⟩
  · cases h

private theorem flatten_map_lenField_length_ge_pure {α : Type} (tag : Nat) (f : α → HwBytes)
    (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤
      (l.map fun c => CryptoVerification.E2E.Record.lenField tag (f c)).flatten.length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

private theorem encReceiverChain_length_le_encSession_pure (s : Session HwBytes)
    (rc : ReceiverChain) (hrc : rc ∈ s.state.receiverChains) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  have h1 := flatten_map_lenField_length_ge_pure 7
    CryptoVerification.E2E.Record.encReceiverChain s.state.receiverChains rc hrc
  unfold CryptoVerification.E2E.Record.encSession
  simp only [List.length_append]; omega

theorem recordBytes_sessionToRecordRecPending_of_pureCanonical_Q
    {Q : HwBytes → Prop} {bs : HwBytes} {s : Session HwBytes}
    (hc : TR.Pure.slots_RecordCanonical_Q Q bs s) :
    recordBytes (sessionToRecordRecPending s) = encodeRecord ⟨some s⟩ ∧
      bs = recordBytes (sessionToRecordRecPending s) := by
  obtain ⟨henc_eq, _, ⟨_, _, hchains_sc, halice_lt, _, hpq_lt, hsess_lt⟩⟩ := hc
  have hsess_len : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 64 := by omega
  have hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63 := by
    intro rc hrc mk hmk; have h32 := (hchains_sc rc hrc).2 mk hmk; omega
  have hrec := recordBytes_sessionToRecordRecPending_eq_encodeRecord s
    (by omega) (by omega) hseeds
    (fun rc hrc' => Nat.lt_of_le_of_lt (encReceiverChain_length_le_encSession_pure s rc hrc') hsess_len)
    hsess_len
  exact ⟨hrec, henc_eq.trans hrec.symm⟩

theorem pqStateOf_of_pureCanonical_Q
    {Q : HwBytes → Prop} {bs : HwBytes} {s : Session HwBytes}
    (hc : TR.Pure.slots_RecordCanonical_Q Q bs s) :
    pqStateOf bs = s.state.pqRatchetState := by
  have ⟨_, hbs⟩ := recordBytes_sessionToRecordRecPending_of_pureCanonical_Q hc
  rw [hbs, pqStateOf_recordBytes, sessionToRecordRecPending_pqRatchetState]

theorem pqStateOf_eq_of_pureWireRecCanon {bs : List (BitVec 8)} {s : Session (List (BitVec 8))}
    (hwc : TR.Pure.WireRecCanon bs) (henc : bs = encodeRecord ⟨some s⟩) :
    pqStateOf bs = s.state.pqRatchetState := by
  obtain ⟨w, hrc_w, -, -, -, h62, -⟩ := hwc
  have hpq_eq : w.state.pqRatchetState = s.state.pqRatchetState :=
    Symbolic.Swarm.TRREF.EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc_w.1 henc h62
  rw [pqStateOf_of_pureCanonical_Q hrc_w, hpq_eq]

theorem trRecordCanon_of_pureWireRecCanon_pqInj
    (r₀ : ProtocolSetup) (p : Participant) {bs : List (BitVec 8)} {s : Session (List (BitVec 8))}
    (hwc : TR.Pure.WireRecCanon bs)
    (henc : bs = encodeRecord ⟨some s⟩)
    (hooo : SpqrOooBounded s.state.pqRatchetState)
    (hreclen : bs.length < 2 ^ 32 - 2 ^ 20) :
    TR.Pure.TRRecordCanon r₀ p bs := by
  obtain ⟨sess, hrc, hrin, hrq, hrem, hlen62, hnp⟩ := hwc
  have hpq : sess.state.pqRatchetState = s.state.pqRatchetState :=
    Symbolic.Swarm.TRREF.EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc.1 henc hlen62
  refine ⟨sess, hrc, hrin, hrq, hrem, hlen62, hnp, hreclen, ?_⟩
  rw [hpq]; exact hooo

local macro "api_simp" " [" xs:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp [Api.run, CryptoGames.LibsignalSessionApi.storeCall, liftProtocol, modify, modifyGet,
      MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.lift, ExceptT.bindCont, StateT.bind, Pure.pure, ExceptT.pure, StateT.pure,
      StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, Id.run, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.lift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, $xs,*] $(loc)?)

/-- A successful in-memory `messageDecryptSignalW` decrypted at the session level and stored the
updated session (pending pre-keys cleared). -/
theorem storedSession_of_decryptOk {Addr Key : Type}
    (C : Crypto) (W : AesW) (spqr : Spqr (List (BitVec 8)) Key)
    (ser : Addr → Addr → Option (List (BitVec 8)))
    (msg : SignalMessage) (remote loc : Addr) (coins : BitVec 256)
    (sess : Session (List (BitVec 8))) (ptBytes : List (BitVec 8))
    (hres : (messageDecryptSignalW C W spqr ser (inMemAnswers sess) msg remote loc coins).1 =
      .ok ptBytes) :
    ∃ st', SessionState.tryDecryptFromRecordW C W spqr (ser remote loc) msg .whisper coins
        sess.state = (.ok ptBytes, st') ∧
      st'.remoteIdentity.isSome ∧
      storedSession sess (messageDecryptSignalW C W spqr ser (inMemAnswers sess) msg remote loc
          coins).2 =
        { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none } := by
  unfold messageDecryptSignalW inMemAnswers at hres ⊢
  unfold SessionRecord.tryDecryptFromRecordW at hres ⊢
  dsimp only at hres ⊢
  rcases hdec : SessionState.tryDecryptFromRecordW C W spqr (ser remote loc) msg .whisper coins
      sess.state with ⟨ed | pt, st'⟩
  · api_simp [hdec] at hres
  · api_simp [hdec] at hres ⊢
    rcases hr : st'.remoteIdentity with _ | remKey
    · api_simp [hr] at hres
    · api_simp [hr] at hres ⊢
      subst hres
      exact ⟨rfl, rfl⟩

end Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval

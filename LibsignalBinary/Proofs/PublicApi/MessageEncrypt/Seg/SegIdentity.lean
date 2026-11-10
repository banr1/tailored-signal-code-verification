/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegIdentityFetch
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import ProofLib.RegChain

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HKDF CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem taken_remoteIdentity_eq_some
    {st : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState st = .ok (otr, taken)) :
    taken.remoteIdentity = some otr.remoteIdentityKey := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : st.senderChain with _ | sc <;> rcases hr : st.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq] at h
  all_goals
    (try split_ifs at h) <;>
    (try simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.ok.injEq, Prod.mk.injEq] at h)
  rcases h with ⟨rfl, rfl⟩
  rfl

private theorem exists_pointsTo16_of_memRegion2 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 2 ∗ R) :
    ∃ v : BitVec 16, m ⊨ (a ↦₁₆ v) ∗ R := by
  rw [memRegion_split a 1 1 (by decide), ProofLib.memRegion_one a,
      ProofLib.memRegion_one (a + 1#64)] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨b0, b1, hm⟩ := hm
  rw [pointsTo8_pair] at hm
  exact ⟨_, hm⟩

private theorem pointsTo16_entails_memRegion2 (a : BitVec 64) (v : BitVec 16) :
    (a ↦₁₆ v) ⊢ memRegion a 2 := by
  rw [pointsTo16_split8 a v, memRegion_split a 1 1 (by decide)]
  exact sepConj_mono (pointsTo8_entails_memRegion _ _) (pointsTo8_entails_memRegion _ _)

private theorem exists_pointsTo32_of_memRegion4 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 4 ∗ R) :
    ∃ v : BitVec 32, m ⊨ (a ↦₃₂ v) ∗ R := by
  rw [ProofLib.memRegion_four a, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

private theorem exists_pointsTo64_of_memRegion8 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 8 ∗ R) :
    ∃ v : BitVec 64, m ⊨ (a ↦₆₄ v) ∗ R := by
  rw [ProofLib.memRegion_eight a, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

private theorem list_len2 {α : Type} (ws : List α) (h : ws.length = 2) :
    ∃ b0 b1, ws = [b0, b1] := by
  rcases ws with _ | ⟨b0, ws⟩; · nomatch h
  rcases ws with _ | ⟨b1, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨b0, b1, rfl⟩
  · nomatch h

private theorem list_len4 {α : Type} (ws : List α) (h : ws.length = 4) :
    ∃ b0 b1 b2 b3, ws = [b0, b1, b2, b3] := by
  rcases ws with _ | ⟨b0, ws⟩; · nomatch h
  rcases ws with _ | ⟨b1, ws⟩; · nomatch h
  rcases ws with _ | ⟨b2, ws⟩; · nomatch h
  rcases ws with _ | ⟨b3, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨b0, b1, b2, b3, rfl⟩
  · nomatch h

theorem exists_ikChunks6_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (c0 : BitVec 32) (c4 : BitVec 16) (c6 c14 c22 : BitVec 64) (c30 : BitVec 16),
      ∀ o : BitVec 64, (o ↦ₛ bs) = ikChunks6 o c0 c4 c6 c14 c22 c30 := by
  have s22 : bs.drop 22 = (bs.drop 22).take 8 ++ bs.drop 30 := by
    have := (List.take_append_drop 8 (bs.drop 22)).symm
    rwa [List.drop_drop] at this
  have s14 : bs.drop 14 = (bs.drop 14).take 8 ++ bs.drop 22 := by
    have := (List.take_append_drop 8 (bs.drop 14)).symm
    rwa [List.drop_drop] at this
  have s6 : bs.drop 6 = (bs.drop 6).take 8 ++ bs.drop 14 := by
    have := (List.take_append_drop 8 (bs.drop 6)).symm
    rwa [List.drop_drop] at this
  have s4 : bs.drop 4 = (bs.drop 4).take 2 ++ bs.drop 6 := by
    have := (List.take_append_drop 2 (bs.drop 4)).symm
    rwa [List.drop_drop] at this
  have s0 : bs = bs.take 4 ++ bs.drop 4 := (List.take_append_drop 4 bs).symm
  have hsplit : bs = bs.take 4 ++ ((bs.drop 4).take 2 ++ ((bs.drop 6).take 8 ++
      ((bs.drop 14).take 8 ++ ((bs.drop 22).take 8 ++ bs.drop 30)))) :=
    s0.trans (congrArg (bs.take 4 ++ ·)
      (s4.trans (congrArg ((bs.drop 4).take 2 ++ ·)
        (s6.trans (congrArg ((bs.drop 6).take 8 ++ ·)
          (s14.trans (congrArg ((bs.drop 14).take 8 ++ ·) s22)))))))
  have hl4 : (bs.take 4).length = 4 := by simp [h]
  have hl2 : ((bs.drop 4).take 2).length = 2 := by simp [h]
  have hl6 : ((bs.drop 6).take 8).length = 8 := by simp [h]
  have hl14 : ((bs.drop 14).take 8).length = 8 := by simp [h]
  have hl22 : ((bs.drop 22).take 8).length = 8 := by simp [h]
  have hl30 : (bs.drop 30).length = 2 := by simp [h]
  obtain ⟨b0, b1, b2, b3, h4⟩ := list_len4 (bs.take 4) hl4
  obtain ⟨b4, b5, h2⟩ := list_len2 ((bs.drop 4).take 2) hl2
  obtain ⟨b30, b31, h30⟩ := list_len2 (bs.drop 30) hl30
  obtain ⟨c6, hc6⟩ := exists_unpack64_of_length_8 hl6
  obtain ⟨c14, hc14⟩ := exists_unpack64_of_length_8 hl14
  obtain ⟨c22, hc22⟩ := exists_unpack64_of_length_8 hl22
  refine ⟨b3 ++ b2 ++ b1 ++ b0, b5 ++ b4, c6, c14, c22, b31 ++ b30, ?_⟩
  intro o
  conv_lhs => rw [hsplit]
  rw [h4, h2, hc6, hc14, hc22, h30]
  simp only [pointsToBytes_append, List.length_cons, List.length_nil, unpack64_length,
    pointsToBytes4_eq_pointsTo32, pointsToBytes2_eq_pointsTo16,
    ← pointsTo64_eq_pointsToBytes]
  unfold ikChunks6
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]

theorem ikChunks6_entails_memRegion (o : BitVec 64) (c0 : BitVec 32) (c4 : BitVec 16)
    (c6 c14 c22 : BitVec 64) (c30 : BitVec 16) :
    ikChunks6 o c0 c4 c6 c14 c22 c30 ⊢ memRegion o 32 := by
  unfold ikChunks6
  rw [memRegion_split o 4 28 (by decide),
      memRegion_split (o + 4#64) 2 26 (by decide),
      memRegion_split (o + 4#64 + 2#64) 8 18 (by decide),
      memRegion_split (o + 4#64 + 2#64 + 8#64) 8 10 (by decide),
      memRegion_split (o + 4#64 + 2#64 + 8#64 + 8#64) 8 2 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo16_entails_memRegion2 _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (pointsTo16_entails_memRegion2 _ _)))))

theorem exists_ikChunks6_of_memRegion32 (o : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion o 32 ∗ R) :
    ∃ (d0 : BitVec 32) (d4 : BitVec 16) (d6 d14 d22 : BitVec 64) (d30 : BitVec 16),
      m ⊨ ikChunks6 o d0 d4 d6 d14 d22 d30 ∗ R := by
  rw [memRegion_eq_exists_bytes o 32 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨bs, hm⟩ := hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨d0, d4, d6, d14, d22, d30, heq⟩ := exists_ikChunks6_of_length_32 hlen
  exact ⟨d0, d4, d6, d14, d22, d30, (heq o) ▸ hm⟩

def sessionPure (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
    G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat

def sessionRecordWithoutRemIk (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (st : SessionState (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
  ⌜sessionPure G { sess with state := st }⌝ ∗
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.localIk (sp + 0x128#64) ∗
  vecU8At A ((sp + 0x128#64) + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) ((sp + 0x128#64) + 0x48#64) G.chainsCap G.chainsPtr
    (G.chains.zip st.receiverChains) ∗
  vecGhostAt A G.alice ((sp + 0x128#64) + 0x60#64) ∗
  vecU8At A ((sp + 0x128#64) + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A ((sp + 0x128#64) + 0x90#64) G.sender st.senderChain ∗
  optTailVecAt A 48 ((sp + 0x128#64) + 0xf8#64) G.pending ∗
  optTailVecAt A 32 ((sp + 0x128#64) + 0x128#64) G.kyber ∗
  (((sp + 0x128#64) + 0x148#64) ↦₃₂ st.sessionVersion) ∗
  (((sp + 0x128#64) + 0x14c#64) ↦₃₂ st.previousCounter) ∗
  (((sp + 0x128#64) + 0x150#64) ↦ₛ G.regIds)

theorem sessionRecordAt_taken_eq (A : RustAlloc) (sp : BitVec 64)
    (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (st : SessionState (List (BitVec 8)))
    (hcur : g.cur = some G) :
    sessionRecordAt A (sp + 0x110#64) g (takenRecord sess st) =
      vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
      sessionRecordWithoutRemIk A sp g G sess st := by
  unfold sessionRecordAt takenRecord
  rw [hcur]
  dsimp only
  unfold sessionStateReprAt sessionStateAt sessionRecordWithoutRemIk sessionPure
  have heq : (sp + 0x110#64) + 0x18#64 = sp + 0x128#64 := by bv_omega
  rw [heq]
  ac_rfl

theorem sessionRecordAt_taken_extract_remIk (A : RustAlloc) (sp : BitVec 64)
    (sess : Session (List (BitVec 8))) (st : SessionState (List (BitVec 8)))
    {m : Memory} {R : SepProp}
    (hm : m ⊨ (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess st)) ∗ R) :
    ∃ (g : RecordGhost) (G : SessionGhost),
      g.cur = some G ∧
      (match st.remoteIdentity with
       | none => G.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
      (m ⊨ vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
        sessionRecordWithoutRemIk A sp g G sess st ∗ R) := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨g, hm⟩ := hm
  cases hcur : g.cur with
  | none =>
    unfold sessionRecordAt takenRecord at hm
    rw [hcur] at hm
    dsimp only at hm
    have hfalse : m ⊨ ⌜False⌝ ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗ R) :=
      Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
    exact False.elim ((satisfies_pure_sepConj _ _ _).1 hfalse).1
  | some G =>
    rw [sessionRecordAt_taken_eq A sp g G sess st hcur] at hm
    have hm_copy := hm
    unfold sessionRecordWithoutRemIk at hm_copy
    have hm1 : m ⊨
        ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
          (match st.remoteIdentity with
           | none => G.remoteIk.bytes = []
           | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
          G.chains.length = st.receiverChains.length ∧
          G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
          G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
        (vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
          ⌜sessionPure G { sess with state := st }⌝ ∗
          vecGhostAt A G.localIk (sp + 0x128#64) ∗
          vecU8At A ((sp + 0x128#64) + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
          vecAt A 104 8 (chainAt A) ((sp + 0x128#64) + 0x48#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains) ∗
          vecGhostAt A G.alice ((sp + 0x128#64) + 0x60#64) ∗
          vecU8At A ((sp + 0x128#64) + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
          optSenderChainAt A ((sp + 0x128#64) + 0x90#64) G.sender st.senderChain ∗
          optTailVecAt A 48 ((sp + 0x128#64) + 0xf8#64) G.pending ∗
          optTailVecAt A 32 ((sp + 0x128#64) + 0x128#64) G.kyber ∗
          (((sp + 0x128#64) + 0x148#64) ↦₃₂ st.sessionVersion) ∗
          (((sp + 0x128#64) + 0x14c#64) ↦₃₂ st.previousCounter) ∗
          (((sp + 0x128#64) + 0x150#64) ↦ₛ G.regIds) ∗ R) :=
      Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm_copy
    have hrem := ((satisfies_pure_sepConj _ _ _).1 hm1).1.2.1
    rw [sepConj_assoc] at hm
    exact ⟨g, G, hcur, hrem, hm⟩

theorem sessionRecordAt_taken_restore_remIk (A : RustAlloc) (sp : BitVec 64)
    (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (st : SessionState (List (BitVec 8)))
    (hcur : g.cur = some G) :
    vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
      sessionRecordWithoutRemIk A sp g G sess st ⊢
      ∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st) := by
  refine Entails.sepExists_right g ?_
  rw [sessionRecordAt_taken_eq A sp g G sess st hcur]
  exact Entails.refl _

open CryptoVerification.LibsignalPublicApi.StoreKit

theorem SegExit.next {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop} (h : next s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next :=
  fun _ => ⟨s, Steps.refl s, Or.inl h⟩

theorem SegExit.of_sepWP {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {mid : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hm : s.mem ⊨ P ∗ (F ∗ R))
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) mid s P post)
    (hcont : ∀ sm Pm, (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      Steps (tripleRatchetProgAt img.base C ctl abs) s sm →
      sm.pc = mid → sm.status = .Running → (sm.mem ⊨ Pm ∗ (F ∗ R)) →
      post sm Pm → SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hcont sm Pm hL hsteps hpc hrun hmm hpost (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem SegExit.call {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit xc code s sf ∗ R') → False)
    (hpanic : ∀ sf, Steps (tripleRatchetProgAt img.base C ctl abs) s sf → sf.status = .Panicked →
      (sf.mem ⊨ (spec.onPanic xc s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0))
    (hnext : ∀ sm : State, (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      Steps (tripleRatchetProgAt img.base C ctl abs) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm →
      (sm.mem ⊨ (spec.post xc s sm ∗ F) ∗ R) →
      SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom xc s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome xc (F ∗ R) s hpc hrun hm hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hL hsteps hpcm hrunm hspm hcsm hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hpanic sm hsteps hpan hpost⟩))⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact (hoom sm _ _hoom_st _hoom_post).elim

theorem callInv_steps {P : Program} {img : Obj.Image} {s s' : State}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hsteps : Steps P s s') (_ : P.CodeLoaded s.mem) :
    img.FrozenLoaded s' ∧ s'.symtab = img.symtab :=
  ⟨hsteps.frozenLoaded hfl, hsteps.symtab_eq.trans hsym⟩

theorem spAligned_of_sp_eq {s sm : State} (hal : s.spAligned = true) (hsp : sm.sp = s.sp) :
    sm.spAligned = true := by
  unfold State.spAligned at hal ⊢
  rw [hsp]
  exact hal

def identityRestFrame (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (_img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (sp : BitVec 64) (s0 : State) : SepProp :=
  sessionRecordWithoutRemIk A sp g G sess taken ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
  memRegion (sp + 0x350#64) 0x118 ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗
  memRegion x.ret 248 ∗
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest 0 ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - remoteIdentityKeyStack) ∗
  encSavedRegs s0.sp s0 ∗ A.pool

theorem otrState_mem_unpack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr sp : BitVec 64)
    (R : SepProp) (s0 : State) {m : Memory}
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hm : m ⊨ (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      memRegion (sp + 0x350#64) 0x118) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x 0 s0 ∗ R) :
    ∃ (g : RecordGhost) (G : SessionGhost),
      g.cur = some G ∧
      (match taken.remoteIdentity with
       | none => G.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
      (m ⊨ emp ∗
        ((vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
          memRegion (sp + 0x580#64) 34 ∗
          logOff img ∗
          stackAt sp remoteIdentityKeyStack ∗
          identityRestFrame ss_vt id_vt A ctl img x g G sess taken pqCap pqPtr otr sp s0) ∗ R)) := by
  unfold takenSlots at hm
  simp only [sepConj_assoc] at hm
  obtain ⟨g, G, hgcur, hrem, hm⟩ := sessionRecordAt_taken_extract_remIk A sp sess taken hm
  have h46a : memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 34 ∗
        memRegion (sp + 0x5a2#64) 0x5de := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide),
        mr_cut_add sp (0x46a + 0x116) 34 0x5de (by decide)]
  unfold encCommon at hm
  rw [hsp0, h46a, stackAt_sub sp encSubStack remoteIdentityKeyStack] at hm
  refine ⟨g, G, hgcur, hrem, ?_⟩
  unfold identityRestFrame
  rw [emp_sepConj]
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm

theorem remoteIk_pre_frame {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (sp : BitVec 64) (R Pm1 : SepProp) (s0 s1 : State)
    (hrem : match taken.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)
    (hsp1 : s1.sp = sp)
    (hx0 : s1.readReg64 .x0 = sp + 0x128#64)
    (hx8 : s1.readReg64 .x8 = sp + 0x580#64)
    (hPm1 : Pm1 ⊢ emp)
    (hm1 : s1.mem ⊨ Pm1 ∗
      ((vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
        memRegion (sp + 0x580#64) 34 ∗
        logOff img ∗
        stackAt sp remoteIdentityKeyStack ∗
        identityRestFrame ss_vt id_vt A ctl img x g G sess taken pqCap pqPtr otr sp s0) ∗ R)) :
    s1.mem ⊨
      (remoteIdentityKeySpec A img).pre
        ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ s1 ∗
      (identityRestFrame ss_vt id_vt A ctl img x g G sess taken pqCap pqPtr otr sp s0 ∗ R) := by
  have hm1' := Satisfies.mono (sepConj_mono_left hPm1) hm1
  rw [emp_sepConj] at hm1'
  unfold remoteIdentityKeySpec
  dsimp only
  rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hx0, hx8, hrem⟩, ?_⟩
  exact Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm1'

theorem remoteIk_post_repack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (sp : BitVec 64) (R : SepProp) (s0 s1 s2 : State)
    (hgcur : g.cur = some G)
    (htaken_rem : taken.remoteIdentity = some otr.remoteIdentityKey)
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hsp1 : s1.sp = sp)
    (hpost : s2.mem ⊨
      ((remoteIdentityKeySpec A img).post
        ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ s1 s2 ∗
        identityRestFrame ss_vt id_vt A ctl img x g G sess taken pqCap pqPtr otr sp s0) ∗ R) :
    s2.trace = s1.trace ∧
    (s2.mem ⊨
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x 0 s0 ∗ R) := by
  unfold remoteIdentityKeySpec at hpost
  dsimp only at hpost
  rw [hsp1, htaken_rem] at hpost
  dsimp only [remoteIdentityOkAt] at hpost
  have h581 : (sp + 0x580#64) + 1#64 = sp + 0x581#64 := by bv_omega
  have h582 : (sp + 0x580#64) + 2#64 = sp + 0x582#64 := by bv_omega
  rw [h581, h582] at hpost
  have h1 : s2.mem ⊨ ⌜s2.trace = s1.trace⌝ ∗
      ((vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
        logOff img ∗ stackAt sp remoteIdentityKeyStack ∗
        identityRestFrame ss_vt id_vt A ctl img x g G sess taken pqCap pqPtr otr sp s0) ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨htr, hmem⟩
  refine ⟨htr, ?_⟩
  unfold identityRestFrame at hmem
  have hrec := sessionRecordAt_taken_restore_remIk A sp g G sess taken hgcur
  have hmem_rearr : s2.mem ⊨
      (vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
        sessionRecordWithoutRemIk A sp g G sess taken) ∗
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - remoteIdentityKeyStack) ∗
        stackAt sp remoteIdentityKeyStack) ∗
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗
      memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest 0 ∗ logOff img ∗
      encSavedRegs s0.sp s0 ∗ A.pool ∗ R :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack remoteIdentityKeyStack] at hmem_rearr
  have hmem_fold := Satisfies.mono (sepConj_mono_left hrec) hmem_rearr
  unfold encCommon
  rw [hsp0]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hmem_fold

def identityStepFrame (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (sp : BitVec 64) (s0 : State) : SepProp :=
  (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
  memRegion (sp + 0x370#64) 0xf8 ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗
  memRegion (sp + 0x5a2#64) 0x2c6 ∗
  memRegion (sp + 0x86e#64) 0x292 ∗
  memRegion (sp + 0xb0a#64) 0x76 ∗
  memRegion x.ret 248 ∗ encCommon A ctl img x 0 s0

theorem remoteIk_ok_unpack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (sp : BitVec 64)
    (R : SepProp) (s0 s2 : State)
    (hm : s2.mem ⊨
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x 0 s0 ∗ R) :
    ∃ (c0 d0 u868 : BitVec 32) (c4 c30 d4 d30 u86c ub08 : BitVec 16)
      (c6 c14 c22 d6 d14 d22 ub00 : BitVec 64),
      (∀ o : BitVec 64,
        (o ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) =
          ikChunks6 o c0 c4 c6 c14 c22 c30) ∧
      (s2.mem ⊨
        (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
          ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
          ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
          ((sp + 0x868#64) ↦₃₂ u868) ∗ ((sp + 0x86c#64) ↦₁₆ u86c) ∗
          ((sp + 0xb00#64) ↦₆₄ ub00) ∗ ((sp + 0xb08#64) ↦₁₆ ub08)) ∗
        (identityStepFrame ss_vt id_vt A ctl img x sess taken pqCap pqPtr otr sp s0 ∗ R)) := by
  obtain ⟨c0, c4, c6, c14, c22, c30, hpack⟩ :=
    exists_ikChunks6_of_length_32 (bs := otr.remoteIdentityKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  rw [hpack (sp + 0x582#64)] at hm
  have h350 : memRegion (sp + 0x350#64) 0x118 =
      memRegion (sp + 0x350#64) 32 ∗ memRegion (sp + 0x370#64) 0xf8 :=
    mr_cut_add sp 0x350 32 0xf8 (by decide)
  have h5a2 : memRegion (sp + 0x5a2#64) 0x5de =
      memRegion (sp + 0x5a2#64) 0x2c6 ∗ memRegion (sp + 0x868#64) 4 ∗
        memRegion (sp + 0x86c#64) 2 ∗ memRegion (sp + 0x86e#64) 0x292 ∗
        memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗
        memRegion (sp + 0xb0a#64) 0x76 := by
    rw [show sp + 0x5a2#64 = sp + BitVec.ofNat 64 0x5a2 from rfl,
        mr_cut_add sp 0x5a2 0x2c6 0x318 (by decide),
        mr_cut_add sp (0x5a2 + 0x2c6) 4 0x314 (by decide),
        mr_cut_add sp (0x5a2 + 0x2c6 + 4) 2 0x312 (by decide),
        mr_cut_add sp (0x5a2 + 0x2c6 + 4 + 2) 0x292 0x80 (by decide),
        mr_cut_add sp (0x5a2 + 0x2c6 + 4 + 2 + 0x292) 8 0x78 (by decide),
        mr_cut_add sp (0x5a2 + 0x2c6 + 4 + 2 + 0x292 + 8) 2 0x76 (by decide)]
  rw [h350, h5a2] at hm
  have hm_d : s2.mem ⊨ memRegion (sp + 0x350#64) 32 ∗
      (memRegion (sp + 0x868#64) 4 ∗ memRegion (sp + 0x86c#64) 2 ∗
        memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        identityStepFrame ss_vt id_vt A ctl img x sess taken pqCap pqPtr otr sp s0 ∗ R) := by
    unfold identityStepFrame
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm
  obtain ⟨d0, d4, d6, d14, d22, d30, hm_d⟩ :=
    exists_ikChunks6_of_memRegion32 (sp + 0x350#64) hm_d
  have hm_868 : s2.mem ⊨ memRegion (sp + 0x868#64) 4 ∗
      (memRegion (sp + 0x86c#64) 2 ∗ memRegion (sp + 0xb00#64) 8 ∗
        memRegion (sp + 0xb08#64) 2 ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        identityStepFrame ss_vt id_vt A ctl img x sess taken pqCap pqPtr otr sp s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm_d
  obtain ⟨u868, hm_868⟩ := exists_pointsTo32_of_memRegion4 (sp + 0x868#64) hm_868
  have hm_86c : s2.mem ⊨ memRegion (sp + 0x86c#64) 2 ∗
      (memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗
        ((sp + 0x868#64) ↦₃₂ u868) ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        identityStepFrame ss_vt id_vt A ctl img x sess taken pqCap pqPtr otr sp s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm_868
  obtain ⟨u86c, hm_86c⟩ := exists_pointsTo16_of_memRegion2 (sp + 0x86c#64) hm_86c
  have hm_b00 : s2.mem ⊨ memRegion (sp + 0xb00#64) 8 ∗
      (memRegion (sp + 0xb08#64) 2 ∗
        ((sp + 0x86c#64) ↦₁₆ u86c) ∗ ((sp + 0x868#64) ↦₃₂ u868) ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        identityStepFrame ss_vt id_vt A ctl img x sess taken pqCap pqPtr otr sp s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm_86c
  obtain ⟨ub00, hm_b00⟩ := exists_pointsTo64_of_memRegion8 (sp + 0xb00#64) hm_b00
  have hm_b08 : s2.mem ⊨ memRegion (sp + 0xb08#64) 2 ∗
      (((sp + 0xb00#64) ↦₆₄ ub00) ∗
        ((sp + 0x86c#64) ↦₁₆ u86c) ∗ ((sp + 0x868#64) ↦₃₂ u868) ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        identityStepFrame ss_vt id_vt A ctl img x sess taken pqCap pqPtr otr sp s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm_b00
  obtain ⟨ub08, hm_b08⟩ := exists_pointsTo16_of_memRegion2 (sp + 0xb08#64) hm_b08
  refine ⟨c0, d0, u868, c4, c30, d4, d30, u86c, ub08, c6, c14, c22, d6, d14, d22, ub00,
    hpack, ?_⟩
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm_b08

theorem remoteIk_ok_pack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (c0 : BitVec 32) (c4 c30 : BitVec 16) (c6 c14 c22 : BitVec 64)
    (sp : BitVec 64) (R Pm3 : SepProp) (s0 s3 : State)
    (hpack : ∀ o : BitVec 64,
      (o ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) =
        ikChunks6 o c0 c4 c6 c14 c22 c30)
    (hPm3 : Pm3 ⊢
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ikChunks6 (sp + 0x350#64) c0 c4 c6 c14 c22 c30 ∗
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
      ((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4) ∗
      ((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30))
    (hm3 : s3.mem ⊨ Pm3 ∗ (identityStepFrame ss_vt id_vt A ctl img x sess taken pqCap pqPtr otr sp s0 ∗ R)) :
    s3.mem ⊨
      (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x370#64) 0xf8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x 0 s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left hPm3) hm3
  rw [← hpack (sp + 0x350#64)] at hm1
  have h580_ent :
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ⊢
      memRegion (sp + 0x580#64) 34 := by
    rw [show sp + 0x580#64 = sp + BitVec.ofNat 64 0x580 from rfl,
        mr_cut_add sp 0x580 1 33 (by decide),
        mr_cut_add sp (0x580 + 1) 1 32 (by decide)]
    exact sepConj_mono (pointsTo8_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _)
        (ikChunks6_entails_memRegion _ _ _ _ _ _ _))
  have h868_ent :
      ((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4) ⊢
      memRegion (sp + 0x868#64) 4 ∗ memRegion (sp + 0x86c#64) 2 :=
    sepConj_mono (pointsTo32_entails_memRegion _ _) (pointsTo16_entails_memRegion2 _ _)
  have hb00_ent :
      ((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30) ⊢
      memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 :=
    sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo16_entails_memRegion2 _ _)
  have h46a_eq :
      memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 34 ∗
        memRegion (sp + 0x5a2#64) 0x2c6 ∗ memRegion (sp + 0x868#64) 4 ∗
        memRegion (sp + 0x86c#64) 2 ∗ memRegion (sp + 0x86e#64) 0x292 ∗
        memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗
        memRegion (sp + 0xb0a#64) 0x76 := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide),
        mr_cut_add sp (0x46a + 0x116) 34 0x5de (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34) 0x2c6 0x318 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6) 4 0x314 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4) 2 0x312 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4 + 2) 0x292 0x80 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4 + 2 + 0x292) 8 0x78 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4 + 2 + 0x292 + 8) 2 0x76 (by decide)]
  unfold identityStepFrame at hm1
  have hm_rearr : s3.mem ⊨
      (((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30) ∗
      (((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4)) ∗
      (((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30)) ∗
      ((∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x370#64) 0xf8 ∗
        curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x5a2#64) 0x2c6 ∗
        memRegion (sp + 0x86e#64) 0x292 ∗
        memRegion (sp + 0xb0a#64) 0x76 ∗
        memRegion x.ret 248 ∗ encCommon A ctl img x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_mono := Satisfies.mono
    (sepConj_mono h580_ent (sepConj_mono h868_ent (sepConj_mono_left hb00_ent))) hm_rearr
  have hm_poll : s3.mem ⊨
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 34 ∗
        memRegion (sp + 0x5a2#64) 0x2c6 ∗ memRegion (sp + 0x868#64) 4 ∗
        memRegion (sp + 0x86c#64) 2 ∗ memRegion (sp + 0x86e#64) 0x292 ∗
        memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗
        memRegion (sp + 0xb0a#64) 0x76) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x 0 s0 ∗ R :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm_mono
  rw [← h46a_eq] at hm_poll
  unfold takenSlots
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm_poll

theorem segIdentity_okV {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegIdentitySpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs := by
  intro env x r sess otr taken pqCap pqPtr R0 s0 s hotrState
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hotrState with ⟨hcur, hsc, hfrom, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, ⟨hx0, hx8, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hsp_x29 : s0.sp - 0x60#64 = sp + 0xb80#64 := by
    rw [← hsp0]; bv_omega
  have hentry : encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt env.loads encryptWithStoresName
  have hs_pc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 712#64 := by
    simpa only [otrPC, hentry] using hs_pc
  have htaken_rem : taken.remoteIdentity = some otr.remoteIdentityKey :=
    taken_remoteIdentity_eq_some hfrom
  obtain ⟨g, G, hgcur, hrem, hm_unp⟩ :=
    otrState_mem_unpack A ctl img x sess otr taken pqCap pqPtr sp R s0 hsp0 hm
  refine SegExit.of_sepWP hm_unp
    (segIdentity_step_pre hs_pc' hrun hsp) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x22, hs1_x23, hs1_x24, hs1_x25,
      hs1_x26, hs1_x27, hs1_x28, hs1_x29, hs1_lr, hs1_vregs, hPm1⟩
  have ⟨hfl1, hsym1⟩ := callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hs1_pc' : s1.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr remoteIdentityKeyName := by
    rw [hs1_pc, remoteIk_addr_eq]
  have hm1_pre := remoteIk_pre_frame A ctl img x g G sess taken pqCap pqPtr otr sp R Pm1 s0 s1
    hrem hs1_sp (hs1_x0.trans hx0) (hs1_x8.trans hx8) hPm1 hm1
  refine SegExit.call env.callees.remoteIk
    ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩
    hs1_pc' hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (remoteIdentityKeySpec A img).onExit
            ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ code s1 _ = ⌜False⌝
            from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun _ _ _ hpan => by
      rw [show (remoteIdentityKeySpec A img).onPanic
            ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ s1 _ = ⌜False⌝
            from rfl,
          sepConj_assoc, satisfies_pure_sepConj] at hpan
      exact hpan.1.elim)
    ?_
  intro s2 hL1 hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have ⟨hfl2, hsym2⟩ := callInv_steps hfl1 hsym1 hsteps12 hL1
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x23 : s2.readReg64 .x23 = sp + 0x58#64 := by reg_chain
  have hs2_x24 : s2.readReg64 .x24 = sp + 0x58#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  have hs2_x29 : s2.readReg64 .x29 = sp + 0xb80#64 := by reg_chain
  obtain ⟨hs2_tr, hm2⟩ := remoteIk_post_repack A ctl img x g G sess taken pqCap pqPtr otr
    sp R s0 s1 s2 hgcur htaken_rem hsp0 hs1_sp hpost2
  obtain ⟨c0, d0, u868, c4, c30, d4, d30, u86c, ub08, c6, c14, c22, d6, d14, d22, ub00,
    hpack, hm2_unp⟩ :=
    remoteIk_ok_unpack A ctl img x sess taken pqCap pqPtr otr sp R s0 s2 hm2
  refine SegExit.of_sepWP hm2_unp
    (segIdentity_step_ok hs2_pc hs2_run hs2_sp' hs2_al hs2_x23 hs2_x24 hs2_x25 hs2_x29) ?_
  intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hs3_sp, hs3_tr, hs3_x0, hs3_x8, hs3_x19, hs3_x20, hs3_x22, hs3_x23, hs3_x25, hs3_x26,
      hs3_x27, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
  have ⟨hfl3, hsym3⟩ := callInv_steps hfl2 hsym2 hsteps23 hL2
  have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
  have hm3_ok := remoteIk_ok_pack A ctl img x sess taken pqCap pqPtr otr
    c0 c4 c30 c6 c14 c22 sp R Pm3 s0 s3 hpack hPm3 hm3
  refine SegExit.next ⟨otr.remoteIdentityKey, hcur, hsc, hfrom, htaken_rem, ?_⟩
  refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hfl3, hsym3,
    by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩, by reg_chain,
    ⟨hs3_x0, hs3_x8, by reg_chain, by reg_chain, hs3_x23, hs3_x25,
      by reg_chain, by reg_chain, by reg_chain⟩,
    hpt, hrest, hloc, hnow, hstk, hm3_ok⟩
  rw [hs3_pc, keyPC, hentry]

theorem segIdentity_ok {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegIdentitySpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  segIdentity_okV

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegApplyStoreSteps
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustFrame
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommon
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# OTR Relocation and Frame Helpers for `segApplyStore_ok`

Pure `SessionRecord` lemmas, 200-byte `otrAt` relocation helpers, and active/passive frame bundles
for the `store_session` phase (`+0xd9c..+0xe88`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HKDF CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Pure Model and `SessionRecord` Lemmas -/

/-- `OutgoingTripleRatchet.fromSessionState` succeeds only when `s.senderChain` is `some _`, and
`takePqRatchetState` preserves `senderChain`. -/
theorem fromSessionState_senderChain_isSome {s taken : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (otr, taken)) :
    taken.senderChain.isSome := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq] at h
  all_goals (try split_ifs at h) <;>
    simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  rfl

def sessionPure (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
    G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat

theorem sessionRecordAt_taken_unpack (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    {m : Memory} {R : SepProp}
    (hm : m ⊨ sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗ R) :
    ∃ G : SessionGhost,
      g.cur = some G ∧ sessionPure G sess ∧
      (m ⊨ (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G taken) ∗ R) := by
  unfold sessionRecordAt takenRecord at hm
  dsimp only at hm
  cases hgc : g.cur with
  | none =>
    rw [hgc] at hm
    dsimp only at hm
    have hfalse : m ⊨ ⌜False⌝ ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗ R) :=
      Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
    exact False.elim ((satisfies_pure_sepConj _ _ _).1 hfalse).1
  | some G =>
    rw [hgc] at hm
    dsimp only at hm
    unfold sessionStateReprAt at hm
    have heq : (sp + 0x110#64) + 0x18#64 = sp + 0x128#64 := by bv_omega
    rw [heq] at hm
    have hpure : m ⊨ ⌜sessionPure G sess⌝ ∗
        ((vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G taken) ∗ R) := by
      unfold sessionPure
      exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
    rw [satisfies_pure_sepConj] at hpure
    exact ⟨G, rfl, hpure.1, hpure.2⟩

theorem sessionRecordAt_stored_fold (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (G G' : SessionGhost)
    (hpure : sessionPure G sess) (hrel : G.AfterOutgoingRatchetApply G') :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
      sessionStateAt A (sp + 0x128#64) G' (otr'.applyToSessionState taken) ⊢
      sessionRecordAt A (sp + 0x110#64) { g with cur := some G' }
        (storedRecord sess otr' taken) := by
  unfold sessionRecordAt storedRecord sessionStateReprAt
  dsimp only
  have heq : (sp + 0x110#64) + 0x18#64 = sp + 0x128#64 := by bv_omega
  rw [heq]
  rcases hrel with ⟨sg, sg', _, _, _, hG'⟩
  have hpure' : sessionPure G' { sess with state := otr'.applyToSessionState taken } := by
    rw [hG']
    exact hpure
  exact sepConj_mono_right (Entails.pure_right hpure' (Entails.refl _))

/-! ## 200-Byte `otrAt` Relocation Lemmas -/

theorem otrWords25_eq_words64At (o : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64) :
    otrWords25 o w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
      w23 w24 =
    words64At o [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17,
      w18, w19, w20, w21, w22, w23, w24] := by
  simp only [otrWords25, words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem otrWords25_entails_memRegion (o : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64) :
    otrWords25 o w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
      w23 w24 ⊢ memRegion o 200 := by
  rw [otrWords25_eq_words64At]
  exact words64At_entails_memRegion
    [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17,
      w18, w19, w20, w21, w22, w23, w24] o (by simp only [List.length_cons, List.length_nil]; decide)

theorem memRegion_200_exists_otrWords25 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 200 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
        BitVec 64,
      m ⊨ otrWords25 a d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20
        d21 d22 d23 d24 ∗ R := by
  obtain ⟨ws, hlen, hws⟩ := memRegion_exists_words64At 25 a (by decide) hm
  rcases ws with _ | ⟨d0, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d1, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d2, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d3, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d4, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d5, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d6, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d7, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d8, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d9, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d10, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d11, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d12, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d13, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d14, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d15, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d16, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d17, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d18, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d19, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d20, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d21, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d22, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d23, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d24, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨_, _⟩
  · rw [← otrWords25_eq_words64At] at hws
    exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
      d19, d20, d21, d22, d23, d24, hws⟩
  · nomatch hlen

theorem otrAt_relocate (A : RustAlloc) (src : BitVec 64) (pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) {m : Memory} {R : SepProp}
    (hm : m ⊨ otrAt A src pqCap pqPtr ot ∗ R) :
    ∃ (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
        BitVec 64) (H : SepProp),
      (m ⊨ otrWords25 src pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
        w19 w20 w21 w22 w23 w24 ∗ H ∗ R) ∧
      (∀ dst : BitVec 64,
        otrWords25 dst pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
          w19 w20 w21 w22 w23 w24 ∗ H ⊢ otrAt A dst pqCap pqPtr ot) := by
  obtain ⟨w3, w4, w5, w6, _, heq1⟩ :=
    exists_unpack64_of_length_32 (bs := ot.senderRatchetKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  obtain ⟨w7, w8, w9, w10, _, heq2⟩ :=
    exists_unpack64_of_length_32 (bs := ot.senderRatchetKey.privateKey.bytes.toList)
      (List.Vector.toList_length _)
  obtain ⟨w11, w12, w13, w14, _, heq3⟩ :=
    exists_unpack64_of_length_32 (bs := ot.localIdentityKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  obtain ⟨w15, w16, w17, w18, _, heq4⟩ :=
    exists_unpack64_of_length_32 (bs := ot.remoteIdentityKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  obtain ⟨w19, w20, w21, w22, _, heq5⟩ :=
    exists_unpack64_of_length_32 (bs := keyToBytes32 ot.senderChainKey.key)
      (length_keyToBytes32 _)
  have hbody : ∀ o : BitVec 64,
      otrAt A o pqCap pqPtr ot =
        ((o ↦₆₄ pqCap) ∗ ((o + 0x08#64) ↦₆₄ pqPtr) ∗
          ((o + 0x10#64) ↦₆₄ BitVec.ofNat 64 ot.pqrState.length) ∗
          ((o + 0x18#64) ↦₆₄ w3) ∗ ((o + 0x20#64) ↦₆₄ w4) ∗
          ((o + 0x28#64) ↦₆₄ w5) ∗ ((o + 0x30#64) ↦₆₄ w6) ∗
          ((o + 0x38#64) ↦₆₄ w7) ∗ ((o + 0x40#64) ↦₆₄ w8) ∗
          ((o + 0x48#64) ↦₆₄ w9) ∗ ((o + 0x50#64) ↦₆₄ w10) ∗
          ((o + 0x58#64) ↦₆₄ w11) ∗ ((o + 0x60#64) ↦₆₄ w12) ∗
          ((o + 0x68#64) ↦₆₄ w13) ∗ ((o + 0x70#64) ↦₆₄ w14) ∗
          ((o + 0x78#64) ↦₆₄ w15) ∗ ((o + 0x80#64) ↦₆₄ w16) ∗
          ((o + 0x88#64) ↦₆₄ w17) ∗ ((o + 0x90#64) ↦₆₄ w18) ∗
          ((o + 0x98#64) ↦₆₄ w19) ∗ ((o + 0xa0#64) ↦₆₄ w20) ∗
          ((o + 0xa8#64) ↦₆₄ w21) ∗ ((o + 0xb0#64) ↦₆₄ w22) ∗
          ((o + 0xb8#64) ↦₆₄ (ot.previousCounter ++ ot.senderChainKey.index))) ∗
        (((o + 0xc0#64) ↦₈ ot.sessionVersion) ∗ memRegion (o + 0xc1#64) 7) ∗
        vecU8Buf A pqCap pqPtr ot.pqrState := by
    intro o
    unfold otrAt
    rw [vecU8At_eq_header_sep_buf, vecHeader, chainKeyBytes_split,
        heq1 (o + 0x18#64), heq2 (o + 0x38#64), heq3 (o + 0x58#64),
        heq4 (o + 0x78#64), heq5 (o + 0x98#64)]
    have hpair :
        (((o + 0x98#64 + 32#64) ↦₃₂ ot.senderChainKey.index) ∗
          ((o + 0xbc#64) ↦₃₂ ot.previousCounter)) =
        ((o + 0xb8#64) ↦₆₄ (ot.previousCounter ++ ot.senderChainKey.index)) := by
      have hp := pointsTo32_pair (o + 0xb8#64) ot.senderChainKey.index ot.previousCounter
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hp
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpair ⊢
    rw [← hpair]
    ac_rfl
  rw [hbody src] at hm
  have hv_unp :
      ((src + 0xc0#64) ↦₈ ot.sessionVersion) ∗ memRegion (src + 0xc1#64) 7 ⊢
        ∃∗ w24 : BitVec 64, ⌜versionPadProp ot.sessionVersion w24⌝ ∗ ((src + 0xc0#64) ↦₆₄ w24) := by
    have hv := versionPad_unpack (src + 0xc0#64) ot.sessionVersion
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hv
  have hm' := Satisfies.mono
    (sepConj_mono_left
      (sepConj_mono (Entails.refl _)
        (sepConj_mono_left hv_unp))) hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm'
  obtain ⟨w24, hm'⟩ := hm'
  have hm_pure : m ⊨ ⌜versionPadProp ot.sessionVersion w24⌝ ∗
      (otrWords25 src pqCap pqPtr (BitVec.ofNat 64 ot.pqrState.length)
        w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
        (ot.previousCounter ++ ot.senderChainKey.index) w24 ∗
      vecU8Buf A pqCap pqPtr ot.pqrState ∗ R) := by
    unfold otrWords25
    exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm'
  rw [satisfies_pure_sepConj] at hm_pure
  rcases hm_pure with ⟨hvp, hm_out⟩
  refine ⟨pqPtr, BitVec.ofNat 64 ot.pqrState.length,
    w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
    w19, w20, w21, w22, ot.previousCounter ++ ot.senderChainKey.index, w24,
    vecU8Buf A pqCap pqPtr ot.pqrState, hm_out, ?_⟩
  intro dst
  rw [hbody dst]
  have hv_pack : ((dst + 0xc0#64) ↦₆₄ w24) ⊢
      ((dst + 0xc0#64) ↦₈ ot.sessionVersion) ∗ memRegion (dst + 0xc1#64) 7 := by
    have hp := Entails.trans (Entails.pure_right hvp (Entails.refl _))
      (versionPad_pack (dst + 0xc0#64) ot.sessionVersion w24)
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hp
  unfold otrWords25
  rw [show ((dst ↦₆₄ pqCap) ∗ ((dst + 0x08#64) ↦₆₄ pqPtr) ∗
      ((dst + 0x10#64) ↦₆₄ BitVec.ofNat 64 ot.pqrState.length) ∗
      ((dst + 0x18#64) ↦₆₄ w3) ∗ ((dst + 0x20#64) ↦₆₄ w4) ∗
      ((dst + 0x28#64) ↦₆₄ w5) ∗ ((dst + 0x30#64) ↦₆₄ w6) ∗
      ((dst + 0x38#64) ↦₆₄ w7) ∗ ((dst + 0x40#64) ↦₆₄ w8) ∗
      ((dst + 0x48#64) ↦₆₄ w9) ∗ ((dst + 0x50#64) ↦₆₄ w10) ∗
      ((dst + 0x58#64) ↦₆₄ w11) ∗ ((dst + 0x60#64) ↦₆₄ w12) ∗
      ((dst + 0x68#64) ↦₆₄ w13) ∗ ((dst + 0x70#64) ↦₆₄ w14) ∗
      ((dst + 0x78#64) ↦₆₄ w15) ∗ ((dst + 0x80#64) ↦₆₄ w16) ∗
      ((dst + 0x88#64) ↦₆₄ w17) ∗ ((dst + 0x90#64) ↦₆₄ w18) ∗
      ((dst + 0x98#64) ↦₆₄ w19) ∗ ((dst + 0xa0#64) ↦₆₄ w20) ∗
      ((dst + 0xa8#64) ↦₆₄ w21) ∗ ((dst + 0xb0#64) ↦₆₄ w22) ∗
      ((dst + 0xb8#64) ↦₆₄ (ot.previousCounter ++ ot.senderChainKey.index)) ∗
      ((dst + 0xc0#64) ↦₆₄ w24)) ∗ vecU8Buf A pqCap pqPtr ot.pqrState =
    ((dst ↦₆₄ pqCap) ∗ ((dst + 0x08#64) ↦₆₄ pqPtr) ∗
      ((dst + 0x10#64) ↦₆₄ BitVec.ofNat 64 ot.pqrState.length) ∗
      ((dst + 0x18#64) ↦₆₄ w3) ∗ ((dst + 0x20#64) ↦₆₄ w4) ∗
      ((dst + 0x28#64) ↦₆₄ w5) ∗ ((dst + 0x30#64) ↦₆₄ w6) ∗
      ((dst + 0x38#64) ↦₆₄ w7) ∗ ((dst + 0x40#64) ↦₆₄ w8) ∗
      ((dst + 0x48#64) ↦₆₄ w9) ∗ ((dst + 0x50#64) ↦₆₄ w10) ∗
      ((dst + 0x58#64) ↦₆₄ w11) ∗ ((dst + 0x60#64) ↦₆₄ w12) ∗
      ((dst + 0x68#64) ↦₆₄ w13) ∗ ((dst + 0x70#64) ↦₆₄ w14) ∗
      ((dst + 0x78#64) ↦₆₄ w15) ∗ ((dst + 0x80#64) ↦₆₄ w16) ∗
      ((dst + 0x88#64) ↦₆₄ w17) ∗ ((dst + 0x90#64) ↦₆₄ w18) ∗
      ((dst + 0x98#64) ↦₆₄ w19) ∗ ((dst + 0xa0#64) ↦₆₄ w20) ∗
      ((dst + 0xa8#64) ↦₆₄ w21) ∗ ((dst + 0xb0#64) ↦₆₄ w22) ∗
      ((dst + 0xb8#64) ↦₆₄ (ot.previousCounter ++ ot.senderChainKey.index))) ∗
      ((dst + 0xc0#64) ↦₆₄ w24) ∗ vecU8Buf A pqCap pqPtr ot.pqrState by ac_rfl]
  exact sepConj_mono_right (sepConj_mono_left hv_pack)

/-! ## Poll Buffer and Seam Frame Bundles -/

theorem poll46a_split_200 (sp : BitVec 64) :
    memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x580#64) 200 ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538) := by
  rw [show (0x716 : Nat) = 0x116 + (200 + 0x538) by decide,
      memRegion_split (sp + 0x46a#64) 0x116 (200 + 0x538) (by decide),
      memRegion_split _ 200 0x538 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

def storePollRest (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x46a#64) 6 ∗
  memRegion (sp + 0x480#64) 0x100 ∗
  memRegion (sp + 0x5b0#64) 0x400 ∗
  memRegion (sp + 0x9c8#64) 0x1b8

theorem storePoll_split (sp : BitVec 64) :
    memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x9b0#64) 24 ∗
      storePollRest sp := by
  unfold storePollRest
  rw [show (0x716 : Nat) = 6 + (16 + (0x100 + (48 + (0x400 + (24 + 0x1b8))))) by decide,
      memRegion_split (sp + 0x46a#64) 6 _ (by decide),
      memRegion_split _ 16 _ (by decide),
      memRegion_split _ 0x100 _ (by decide),
      memRegion_split _ 48 _ (by decide),
      memRegion_split _ 0x400 _ (by decide),
      memRegion_split _ 24 0x1b8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem storePoll_merge_ok (sp : BitVec 64) :
    memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x9b0#64) 24 ∗
      storePollRest sp ⊢
    memRegion (sp + 0x46a#64) 0x716 := by
  rw [storePoll_split sp]
  exact Entails.refl _

theorem storePoll_merge_9b0 (sp w3 w4 w5 : BitVec 64) :
    memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      (((sp + 0x9b0#64) ↦₆₄ w3) ∗ ((sp + 0x9b8#64) ↦₆₄ w4) ∗ ((sp + 0x9c0#64) ↦₆₄ w5)) ∗
      storePollRest sp ⊢
    pollWith sp 0x9b0 [w3, w4, w5] := by
  unfold pollWith storePollRest
  dsimp only [words64At, List.length]
  change _ ⊢ memRegion (sp + 0x46a#64) 0x546 ∗
    (((sp + 0x9b0#64) ↦₆₄ w3) ∗ ((sp + 0x9b0#64 + 8#64) ↦₆₄ w4) ∗
      ((sp + 0x9b0#64 + 8#64 + 8#64) ↦₆₄ w5) ∗ emp) ∗
    memRegion (sp + 0x9c8#64) 0x1b8
  rw [show (0x546 : Nat) = 6 + (16 + (0x100 + (48 + 0x400))) by decide,
      memRegion_split (sp + 0x46a#64) 6 _ (by decide),
      memRegion_split _ 16 _ (by decide),
      memRegion_split _ 0x100 _ (by decide),
      memRegion_split _ 48 0x400 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  exact Entails.of_eq

theorem cmScratch_eq_38 (sp : BitVec 64) :
    cmScratch sp =
      ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
      (memRegion sp 0x38 ∗ ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
        memRegion (sp + 0x48#64) 8 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) := by
  unfold cmScratch; ac_rfl

def encSpillsStoreRest (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) : SepProp :=
  ((sp + 0x58#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0x60#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0x64#64) 4 ∗ ((sp + 0x68#64) ↦₆₄ x.ptA) ∗
  ((sp + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0x78#64) ↦₆₄ x.remA) ∗
  ((sp + 0x80#64) ↦₆₄ x.locA) ∗ ((sp + 0x88#64) ↦₆₄ x.ssA) ∗ ((sp + 0x90#64) ↦₆₄ ss_vt) ∗
  ((sp + 0x98#64) ↦₆₄ x.idA) ∗ ((sp + 0xa0#64) ↦₆₄ id_vt) ∗
  ((sp + 0xa8#64) ↦₆₄ (sp + 0xb6f#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
  ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
  ((sp + 0xc8#64) ↦₆₄ x.locA) ∗
  ((sp + 0xe0#64) ↦₆₄ x.idA) ∗ ((sp + 0xe8#64) ↦₆₄ id_vt) ∗
  ((sp + 0xf0#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0xf8#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0xfc#64) 4 ∗ ((sp + 0x100#64) ↦₆₄ (sp + 0xb6f#64)) ∗
  ((sp + 0x108#64) ↦₆₄ x.remA)

theorem encSpillsAt_store_eq (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) :
    encSpillsAtV ss_vt id_vt sp x =
      ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xd0#64) ↦₆₄ x.ssA) ∗
      ((sp + 0xd8#64) ↦₆₄ ss_vt) ∗ encSpillsStoreRest ss_vt id_vt sp x := by
  unfold encSpillsAtV encSpillsStoreRest; ac_rfl

def storeBaseActive {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (st : kit.StoreState) (ikit : IdentityStoreSpec A b) (sp : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost)
    (rec' : SessionRecord (List (BitVec 8))) : SepProp :=
  ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
  ((sp + 0xd0#64) ↦₆₄ x.ssA) ∗
  ((sp + 0xd8#64) ↦₆₄ kit.ss_vt) ∗
  sessionRecordAt A (sp + 0x110#64) g' rec' ∗
  protocolAddressAt A x.rem x.remA ∗
  stackAt sp (encSubStackV kit ikit) ∗
  A.pool ∗
  kit.storeAt x.ssA st

def storePassive {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) : SepProp :=
  let sp := s0.sp - 0xbe0#64
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
  memRegion (sp + 0x288#64) 200 ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗
  ((sp + 0x469#64) ↦₈ 0#8) ∗
  cmScratch sp ∗
  encSpillsStoreRest kit.ss_vt ikit.id_vt sp x ∗
  storePollRest sp ∗
  memRegion x.ret 248 ∗
  logOff img ∗
  ikit.identityAt x.idA ist ∗
  encCommonRest A ctl x draws s0

theorem store_mem_split {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (st : kit.StoreState) (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64) :
    ((sessionRecordAt A (sp + 0x110#64) g' rec' ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 0#8)) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x draws s0) ∗ encStoreExtra kit st ikit ist x s0 ⊢
    ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    ((storeBaseActive kit st ikit sp x g' rec' ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x9b0#64) 24) ∗
    storePassive kit ikit ist ctl x k m draws s0) := by
  subst hsp
  dsimp only [storeBaseActive, storePassive]
  set sp := s0.sp - 0xbe0#64
  have hpre :
      ((sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        memRegion (sp + 0x288#64) 200 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 0#8)) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x draws s0) ∗ encStoreExtra kit st ikit ist x s0 =
      ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      ((kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
        stackAt sp encSubStack) ∗
      (((sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        memRegion (sp + 0x288#64) 200 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 0#8)) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      protocolAddressAt A x.rem x.remA ∗ logOff img ∗ A.pool ∗
      encCommonRest A ctl x draws s0))) := by
    rw [encCommon_eq]
    unfold encStoreExtra
    ac_rfl
  rw [hpre]
  refine Entails.pure_left fun hbound => Entails.pure_right hbound ?_
  have hj :
      kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
        stackAt sp encSubStack ⊢
      kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt sp (encSubStackV kit ikit) := by
    have h1 := encSubStack_join_extra kit st ikit ist x s0 hbound
    unfold encStoreExtra at h1
    have h0 : kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
        stackAt sp encSubStack ⊢
      (⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack)) ∗
        stackAt sp encSubStack :=
      Entails.trans (Entails.pure_right hbound (Entails.refl _)) (Entails.of_eq (by ac_rfl))
    exact Entails.trans h0 h1
  refine Entails.trans (sepConj_mono_left hj) ?_
  rw [encSpillsAt_store_eq, storePoll_split]
  exact Entails.of_eq (by ac_rfl)

theorem store_mem_to_stored {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (st : kit.StoreState) (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    (storeBaseActive kit st ikit sp x g' rec' ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x9b0#64) 24) ∗
    storePassive kit ikit ist ctl x k m draws s0 ⊢
    (((∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g rec') ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ memRegion (sp + 0x469#64) 1) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x draws s0) ∗ encStoreExtra kit st ikit ist x s0 := by
  subst hsp
  set sp := s0.sp - 0xbe0#64
  have hsp_split := encSubStack_split_extra kit st ikit ist x s0 hbound
  have hrec : sessionRecordAt A (sp + 0x110#64) g' rec' ⊢
      ∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g rec' :=
    Entails.sepExists_right g' (Entails.refl _)
  have h469 := pointsTo8_entails_memRegion (sp + 0x469#64) 0#8
  dsimp only [storeBaseActive, storePassive]
  have hreord1 :
      ((((sp + 0xc0#64) ↦₆₄ x.remA ∗ (sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        protocolAddressAt A x.rem x.remA ∗ stackAt sp (encSubStackV kit ikit) ∗ A.pool ∗
        kit.storeAt x.ssA st) ∗
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x9b0#64) 24) ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      cmScratch sp ∗ encSpillsStoreRest kit.ss_vt ikit.id_vt sp x ∗ storePollRest sp ∗
      memRegion x.ret 248 ∗ logOff img ∗ ikit.identityAt x.idA ist ∗
      encCommonRest A ctl x draws s0)) =
      (kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt sp (encSubStackV kit ikit)) ∗
      sessionRecordAt A (sp + 0x110#64) g' rec' ∗
      ((sp + 0x469#64) ↦₈ 0#8) ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ cmScratch sp ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
        protocolAddressAt A x.rem x.remA ∗ logOff img ∗ A.pool ∗
        encCommonRest A ctl x draws s0) := by
    rw [encSpillsAt_store_eq, storePoll_split]
    ac_rfl
  rw [hreord1]
  refine Entails.trans (sepConj_mono hsp_split (sepConj_mono hrec (sepConj_mono_left h469))) ?_
  rw [encCommon_eq]
  exact Entails.of_eq (by ac_rfl)

theorem store_mem_to_tail {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (st : kit.StoreState) (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (w3 w4 w5 : BitVec 64) (H : SepProp) :
    (storeBaseActive kit st ikit sp x g' rec' ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      (((sp + 0x9b0#64) ↦₆₄ w3) ∗ ((sp + 0x9b8#64) ↦₆₄ w4) ∗ ((sp + 0x9c0#64) ↦₆₄ w5)) ∗
      H) ∗
    storePassive kit ikit ist ctl x k m draws s0 ⊢
    (dropRecordSlots A sp cmScratch g' rec' none (some m) (pollWith sp 0x9b0 [w3, w4, w5]) ∗ H) ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x draws s0 ∗ encStoreExtra kit st ikit ist x s0 := by
  subst hsp
  dsimp only [storeBaseActive, storePassive]
  set sp := s0.sp - 0xbe0#64
  have hsp_split := encSubStack_split_extra kit st ikit ist x s0 hbound
  have hpoll := storePoll_merge_9b0 sp w3 w4 w5
  have hk : ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ⊢ memRegion (sp + 0x350#64) 0x20 := by
    have h := pointsToBytes_entails_memRegion (sp + 0x350#64) k.publicKey.bytes.toList
    have hlen : k.publicKey.bytes.toList.length = 0x20 := k.publicKey.bytes.property
    rwa [hlen] at h
  have h280 := pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64)
  have h468 := pointsTo8_entails_memRegion (sp + 0x468#64) 0#8
  have hreord :
      ((((sp + 0xc0#64) ↦₆₄ x.remA ∗ (sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        protocolAddressAt A x.rem x.remA ∗ stackAt sp (encSubStackV kit ikit) ∗ A.pool ∗
        kit.storeAt x.ssA st) ∗
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗
      (((sp + 0x9b0#64) ↦₆₄ w3) ∗ ((sp + 0x9b8#64) ↦₆₄ w4) ∗ ((sp + 0x9c0#64) ↦₆₄ w5)) ∗ H) ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      cmScratch sp ∗ encSpillsStoreRest kit.ss_vt ikit.id_vt sp x ∗ storePollRest sp ∗
      memRegion x.ret 248 ∗ logOff img ∗ ikit.identityAt x.idA ist ∗
      encCommonRest A ctl x draws s0)) =
      (kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt sp (encSubStackV kit ikit)) ∗
      ((cmScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        (memRegion (sp + 0x288#64) 200 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
        (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
          apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
          ((sp + 0x468#64) ↦₈ 0#8)) ∗
        (memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗
          (((sp + 0x9b0#64) ↦₆₄ w3) ∗ ((sp + 0x9b8#64) ↦₆₄ w4) ∗ ((sp + 0x9c0#64) ↦₆₄ w5)) ∗
          storePollRest sp)) ∗
        H ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        protocolAddressAt A x.rem x.remA ∗ logOff img ∗ A.pool ∗
        encCommonRest A ctl x draws s0) := by
    rw [encSpillsAt_store_eq]
    ac_rfl
  rw [hreord]
  have hslots :
      cmScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g' rec' ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        (memRegion (sp + 0x288#64) 200 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
        (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
          apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
          ((sp + 0x468#64) ↦₈ 0#8)) ∗
        (memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗
          (((sp + 0x9b0#64) ↦₆₄ w3) ∗ ((sp + 0x9b8#64) ↦₆₄ w4) ∗ ((sp + 0x9c0#64) ↦₆₄ w5)) ∗
          storePollRest sp) ⊢
      dropRecordSlots A sp cmScratch g' rec' none (some m) (pollWith sp 0x9b0 [w3, w4, w5]) := by
    dsimp only [dropRecordSlots, otrSlotAt, cmSlotAt]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono h280
      (sepConj_mono_right (sepConj_mono (sepConj_mono hk (sepConj_mono_right h468)) hpoll))))
  refine Entails.trans (sepConj_mono hsp_split (sepConj_mono_left hslots)) ?_
  rw [encCommon_eq]
  exact Entails.of_eq (by ac_rfl)

/-- Normalizes `storePollOutAt` after `kit.storePoll` into six 64-bit words at `sp + 0x580` plus
the staged error resource. -/
theorem storePollOut_words (_A : RustAlloc) (b out : BitVec 64) (ans : Except Unit Unit) :
    storePollOutAt b out ans ⊢
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ H : SepProp,
      ⌜(w0 = 0xFFFFFFFFFFFFFFFE#64 ∨ w0 = 0x800000000000001A#64) ∧
        w0 = pollTag ans ∧
        (ans = .ok () → H = emp) ∧
        (ans = .error () →
          H = ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∧ w1 = b + bv% (ls_reloc% 0x77cc) ∧ w2 = 10#64 ∧ w3 = 1#64 ∧ w4 = b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))⌝ ∗
      (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
      ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
      ((out + 0x28#64) ↦₆₄ w5) ∗ H := by
  rcases ans with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · dsimp only [storePollOutAt, pollTag]
    rw [ProofLib.memRegion_eight (out + 0x28#64)]
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    refine Entails.sepExists_right 0x800000000000001A#64 (Entails.sepExists_right (b + bv% (ls_reloc% 0x77cc))
      (Entails.sepExists_right 10#64 (Entails.sepExists_right 1#64
      (Entails.sepExists_right (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) (Entails.sepExists_right w5
      (Entails.sepExists_right ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ?_))))))
    refine Entails.pure_right ⟨Or.inr rfl, rfl, (fun h => nomatch h),
      fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [storePollOutAt, pollTag]
    rw [show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) by decide,
        memRegion_split (out + 8#64) 8 _ (by decide),
        memRegion_split _ 8 _ (by decide),
        memRegion_split _ 8 _ (by decide),
        memRegion_split _ 8 8 (by decide),
        ProofLib.memRegion_eight (out + 8#64),
        ProofLib.memRegion_eight (out + 8#64 + 8#64),
        ProofLib.memRegion_eight (out + 8#64 + 8#64 + 8#64),
        ProofLib.memRegion_eight (out + 8#64 + 8#64 + 8#64 + 8#64),
        ProofLib.memRegion_eight (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w4 =>
      Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 =>
      Entails.sepExists_elim fun w1 => ?_
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFE#64 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5
      (Entails.sepExists_right emp ?_))))))
    refine Entails.pure_right ⟨Or.inl rfl, rfl, fun _ => rfl, (fun h => nomatch h)⟩ ?_
    rw [sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore

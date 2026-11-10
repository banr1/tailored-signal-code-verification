/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Fetch
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Raw
import LibsignalBinary.Specifications.AsmConstants
import ProofLib.SepLogic.WPp

/-!
# `SessionRecord::promote_matching_session` on a Matched Current Session

Proves `promote_matching_session_match_ok` on `tripleRatchetProgAtExt b ext` when
`r.currentSession = some s` matches `(msgVer, serBytes)` (`s.state.version = msgVer.zeroExtend 32`,
`s.aliceBaseKey = serBytes`, `serBytes.length = 33`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Stack budget of `<SessionRecord>::promote_matching_session` on the matched `current_session`
fast path (`0x60` saved registers + `0x440` local frame = `0x4a0` = `1184` bytes; `black_box` is
an extern hook using `0` stack). -/
abbrev promoteMatchingSessionMatchStack : Nat := 1184

private theorem stackAt_promoteMatch_eq (sp : BitVec 64) :
    stackAt sp promoteMatchingSessionMatchStack =
      (∃∗ w4a0 : BitVec 64, (sp - 1184#64) ↦₆₄ w4a0) ∗
      memRegion (sp - 1176#64) 40 ∗
      (∃∗ w470 : BitVec 64, (sp - 1136#64) ↦₆₄ w470) ∗
      memRegion (sp - 1128#64) 1032 ∗
      cells (sp - 96#64) 12 := by
  change memRegion (sp - 1184#64) 1184 = _
  rw [show (1184 : Nat) = 8 + (40 + (8 + (1032 + 96))) by decide,
    memRegion_split (sp - 1184#64) 8 _ (by decide),
    ProofLib.memRegion_eight (sp - 1184#64),
    show sp - 1184#64 + 8#64 = sp - 1176#64 by bv_omega,
    memRegion_split (sp - 1176#64) 40 _ (by decide),
    show sp - 1176#64 + 40#64 = sp - 1136#64 by bv_omega,
    memRegion_split (sp - 1136#64) 8 _ (by decide),
    ProofLib.memRegion_eight (sp - 1136#64),
    show sp - 1136#64 + 8#64 = sp - 1128#64 by bv_omega,
    memRegion_split (sp - 1128#64) 1032 96 (by decide),
    show sp - 1128#64 + 1032#64 = sp - 96#64 by bv_omega,
    show (96 : Nat) = 8 * 12 by decide,
    ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]

structure PromoteMatchGhost where
  recPtr : BitVec 64
  msgVer : BitVec 8
  serPtr : BitVec 64
  serBytes : List (BitVec 8)
  outPtr : BitVec 64
  g : RecordGhost
  r : SessionRecord (List (BitVec 8))
  s : Session (List (BitVec 8))

/-- Specification of `<SessionRecord>::promote_matching_session` on a matched `current_session`:
when `r.currentSession = some s`, `s.state.version = msgVer.zeroExtend 32`,
`s.aliceBaseKey = serBytes`, and `serBytes.length = 33`, returns `Ok(true)`
(`outPtr ↦₆₄ 0#64 ∗ (outPtr + 8#64) ↦₈ 1#8`) with `sessionRecordAt A recPtr g r` unchanged. -/
def promoteMatchingSessionMatchSpec (A : RustAlloc) : Spec PromoteMatchGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.r.currentSession = some x.s ∧
     x.s.state.version = x.msgVer.zeroExtend 32 ∧
     x.s.aliceBaseKey = x.serBytes ∧
     x.serBytes.length = 33⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    memRegion x.outPtr 16 ∗
    stackAt st.sp promoteMatchingSessionMatchStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 1#8) ∗
    memRegion (x.outPtr + 9#64) 7 ∗
    stackAt s0.sp promoteMatchingSessionMatchStack

private theorem outRegion16_split (outPtr : BitVec 64) :
    memRegion outPtr 16 =
      (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
      (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
      memRegion (outPtr + 9#64) 7 := by
  rw [show (16 : Nat) = 8 + (1 + 7) by decide,
    memRegion_split outPtr 8 (1 + 7) (by decide),
    ProofLib.memRegion_eight outPtr,
    memRegion_split (outPtr + 8#64) 1 7 (by decide),
    ProofLib.memRegion_one (outPtr + 8#64),
    show outPtr + 8#64 + 1#64 = outPtr + 9#64 by bv_omega]

private theorem pure_keep {ψ φ : Prop} (h : ψ → φ) :
    (⌜ψ⌝ : SepProp) = ⌜φ⌝ ∗ ⌜ψ⌝ := by
  rw [pure_sepConj_pure]
  congr 1
  exact propext ⟨fun hψ => ⟨h hψ, hψ⟩, fun ⟨_, hψ⟩ => hψ⟩

private def vecGhostRest0 (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) : SepProp :=
  ((v + 8#64) ↦₆₄ vg.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vg.bytes.length) ∗
  ⌜vg.bytes.length ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
  (if vg.cap = 0 then emp
   else A.live vg.ptr vg.cap.toNat 1 ∗ (vg.ptr ↦ₛ vg.bytes) ∗
     memRegion (vg.ptr + BitVec.ofNat 64 vg.bytes.length) (vg.cap.toNat - vg.bytes.length))

private theorem vecGhostAt_eq_split0 (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) :
    vecGhostAt A vg v =
      ⌜vg.cap.toNat < 2 ^ 63⌝ ∗ (v ↦₆₄ vg.cap) ∗ vecGhostRest0 A v vg := by
  have hk := pure_keep
    (ψ := vg.bytes.length ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0)
    (fun h => h.2.1)
  unfold vecGhostAt vecU8At vecHeader vecGhostRest0
  conv_lhs => rw [hk]
  ac_rfl

private theorem vecGhostAt_restore0 (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) :
    (v ↦₆₄ vg.cap) ∗ vecGhostRest0 A v vg = vecGhostAt A vg v := by
  unfold vecGhostAt vecU8At vecHeader vecGhostRest0
  ac_rfl

private def vecGhostRestAlice (A : RustAlloc) (v : BitVec 64) (vg : VecGhost) : SepProp :=
  (v ↦₆₄ vg.cap) ∗
  ⌜vg.bytes.length ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
  A.live vg.ptr vg.cap.toNat 1 ∗
  memRegion (vg.ptr + BitVec.ofNat 64 vg.bytes.length) (vg.cap.toNat - vg.bytes.length)

private theorem vecGhostAt_eq_split_alice (A : RustAlloc) (v : BitVec 64) (vg : VecGhost)
    (serBytes : List (BitVec 8)) (heq : vg.bytes = serBytes) (hlen : serBytes.length = 33) :
    vecGhostAt A vg v =
      ((v + 8#64) ↦₆₄ vg.ptr) ∗ ((v + 16#64) ↦₆₄ 33#64) ∗
      (vg.ptr ↦ₛ serBytes) ∗ vecGhostRestAlice A v vg := by
  unfold vecGhostAt vecU8At vecHeader vecGhostRestAlice
  rw [heq, hlen]
  have hcongr :
      (⌜33 ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
        if vg.cap = 0 then emp
        else A.live vg.ptr vg.cap.toNat 1 ∗ (vg.ptr ↦ₛ serBytes) ∗
          memRegion (vg.ptr + BitVec.ofNat 64 33) (vg.cap.toNat - 33)) =
      (⌜33 ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
        (A.live vg.ptr vg.cap.toNat 1 ∗ (vg.ptr ↦ₛ serBytes) ∗
          memRegion (vg.ptr + BitVec.ofNat 64 33) (vg.cap.toNat - 33))) := by
    refine pure_sepConj_congr fun ⟨hle, _, _⟩ => ?_
    have hc : vg.cap ≠ 0#64 := by intro hc0; rw [hc0] at hle; simp at hle
    simp [hc]
  rw [hcongr]
  change _ = ((v + 8#64) ↦₆₄ vg.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 33) ∗ _
  ac_rfl

private def ssPureProp (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Prop :=
  PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
  (match st.remoteIdentity with
   | none => G.remoteIk.bytes = []
   | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
  G.chains.length = st.receiverChains.length ∧
  G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
  G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)

private def ssMid1 (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  vecGhostAt A G.remoteIk (ss + asm64% ssRemoteIdentityOff) ∗
  vecU8At A (ss + asm64% ssRootKeyOff) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
  vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A) (ss + asm64% ssReceiverChainsOff)
    G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains)

private def ssMid2 (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  vecU8At A (ss + asm64% ssPqRatchetStateOff) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + asm64% ssSenderChainOff) G.sender st.senderChain ∗
  optTailVecAt A (asm% pendingPreKeySize) (ss + asm64% ssPendingPreKeyOff) G.pending ∗
  optTailVecAt A (asm% pendingKyberPreKeySize) (ss + asm64% ssPendingKyberPreKeyOff) G.kyber

private def ssTail (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ((ss + asm64% ssPreviousCounterOff) ↦₃₂ st.previousCounter) ∗
  ((ss + asm64% ssRegistrationIdsOff) ↦ₛ G.regIds)

private theorem sessionStateAt_eq_chunks (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜ssPureProp G st⌝ ∗
      vecGhostAt A G.localIk ss ∗
      ssMid1 A ss G st ∗
      vecGhostAt A G.alice (ss + 0x60#64) ∗
      ssMid2 A ss G st ∗
      ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
      ssTail ss G st := by
  unfold sessionStateAt ssPureProp ssMid1 ssMid2 ssTail
  simp only [sepConj_assoc]
  rfl

private def sessPureProp (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
  G.alice.bytes = s.aliceBaseKey ∧
  G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
  (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat

private theorem sessionAt_eq_chunks (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s =
      ⌜G.alice.bytes = s.aliceBaseKey⌝ ∗
      ⌜sessPureProp G s⌝ ∗
      sessionStateAt A ss G s.state := by
  change ⌜sessPureProp G s⌝ ∗ sessionStateAt A ss G s.state = _
  conv_lhs => rw [pure_keep (ψ := sessPureProp G s) (fun h => h.2.2.1)]
  rw [sepConj_assoc]

private theorem sessionAt_restore_chunks (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) :
    ⌜sessPureProp G s⌝ ∗ sessionStateAt A ss G s.state = sessionStateReprAt A ss G s :=
  rfl

private def promoteMatchFrame (A : RustAlloc) (recPtr outPtr sp : BitVec 64)
    (g : RecordGhost) (G : SessionGhost) (s : Session (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) recPtr g.prevCap g.prevPtr [] ∗
  ⌜sessPureProp G s⌝ ∗
  ⌜ssPureProp G s.state⌝ ∗
  vecGhostRest0 A (recPtr + 0x18#64) G.localIk ∗
  ssMid1 A (recPtr + 0x18#64) G s.state ∗
  vecGhostRestAlice A (recPtr + 0x78#64) G.alice ∗
  ssMid2 A (recPtr + 0x18#64) G s.state ∗
  ssTail (recPtr + 0x18#64) G s.state ∗
  memRegion (outPtr + 9#64) 7 ∗
  memRegion (sp - 1176#64) 40 ∗
  memRegion (sp - 1128#64) 1032

set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
private theorem promoteMatch_pre_entails (A : RustAlloc) (x : PromoteMatchGhost)
    (G : SessionGhost) (s0 : State)
    (hgc : x.g.cur = some G)
    (hx0 : s0.readReg64 .x0 = x.recPtr)
    (hx1 : s0.readReg64 .x1 = x.msgVer.zeroExtend 64)
    (hx2 : s0.readReg64 .x2 = x.serPtr)
    (hx3 : s0.readReg64 .x3 = 33#64)
    (hx8 : s0.readReg64 .x8 = x.outPtr)
    (hcur : x.r.currentSession = some x.s)
    (hver : x.s.state.version = x.msgVer.zeroExtend 32)
    (halice : x.s.aliceBaseKey = x.serBytes)
    (hlen : x.serBytes.length = 33) :
    sessionRecordAt A x.recPtr x.g x.r ∗
      (x.serPtr ↦ₛ x.serBytes) ∗
      memRegion x.outPtr 16 ∗
      stackAt s0.sp promoteMatchingSessionMatchStack ⊢
    promoteMatchingSessionRawSpec.pre
      ⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
       x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩ s0 ∗
      promoteMatchFrame A x.recPtr x.outPtr s0.sp x.g G x.s := by
  dsimp only [promoteMatchingSessionRawSpec, promoteMatchFrame]
  simp only [sessionRecordAt, hgc, hcur,
    sessionAt_eq_chunks A (x.recPtr + 0x18#64) G x.s,
    sessionStateAt_eq_chunks A (x.recPtr + 0x18#64) G x.s.state,
    vecGhostAt_eq_split0 A (x.recPtr + 0x18#64) G.localIk,
    outRegion16_split x.outPtr, stackAt_promoteMatch_eq s0.sp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.trans (Entails.of_eq (by sep_focus : _ =
    (⌜G.alice.bytes = x.s.aliceBaseKey⌝ ∗ ⌜G.localIk.cap.toNat < 2 ^ 63⌝) ∗ _)) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hal_g => Entails.pure_left fun hcap => ?_
  have hal_eq : G.alice.bytes = x.serBytes := hal_g.trans halice
  have hver' : (if x.s.state.sessionVersion = 0#32 then 2#32 else x.s.state.sessionVersion) =
      x.msgVer.zeroExtend 32 := hver
  simp only [vecGhostAt_eq_split_alice A (x.recPtr + 0x78#64) G.alice x.serBytes hal_eq hlen,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx8, hcap, hver', hlen⟩ ?_
  exact Entails.of_eq (by ac_rfl)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
private theorem promoteMatch_post_entails (A : RustAlloc) (x : PromoteMatchGhost)
    (G : SessionGhost) (s0 sf : State)
    (hgc : x.g.cur = some G)
    (hcur : x.r.currentSession = some x.s)
    (halice : x.s.aliceBaseKey = x.serBytes)
    (hlen : x.serBytes.length = 33) :
    promoteMatchingSessionRawSpec.post
      ⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
       x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩ s0 sf ∗
      promoteMatchFrame A x.recPtr x.outPtr s0.sp x.g G x.s ⊢
    (promoteMatchingSessionMatchSpec A).post x s0 sf := by
  dsimp only [promoteMatchingSessionRawSpec, promoteMatchingSessionMatchSpec, promoteMatchFrame]
  simp only [sepConj_assoc]
  refine Entails.trans (Entails.of_eq (by sep_focus : _ = ⌜sessPureProp G x.s⌝ ∗ _)) ?_
  refine Entails.pure_left fun hsess => ?_
  have hal_eq : G.alice.bytes = x.serBytes := hsess.2.2.1.trans halice
  simp only [sessionRecordAt, hgc, hcur,
    ← sessionAt_restore_chunks A (x.recPtr + 0x18#64) G x.s,
    sessionStateAt_eq_chunks A (x.recPtr + 0x18#64) G x.s.state,
    ← vecGhostAt_restore0 A (x.recPtr + 0x18#64) G.localIk,
    vecGhostAt_eq_split_alice A (x.recPtr + 0x78#64) G.alice x.serBytes hal_eq hlen,
    stackAt_promoteMatch_eq s0.sp,
    pure_sepConj_of_true hsess,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem promote_matching_session_match_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      (promoteMatchingSessionMatchSpec A) := by
  refine subroutine_ok_refine_frame (promote_matching_session_raw_ok (b := b) (ext := ext) h_bb) ?_
  intro x R s0 hpre
  have hpre' : s0.mem ⊨
      ⌜s0.readReg64 .x0 = x.recPtr ∧
       s0.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
       s0.readReg64 .x2 = x.serPtr ∧
       s0.readReg64 .x3 = 33#64 ∧
       s0.readReg64 .x8 = x.outPtr ∧
       x.r.currentSession = some x.s ∧
       x.s.state.version = x.msgVer.zeroExtend 32 ∧
       x.s.aliceBaseKey = x.serBytes ∧
       x.serBytes.length = 33⌝ ∗
      ((sessionRecordAt A x.recPtr x.g x.r ∗
        (x.serPtr ↦ₛ x.serBytes) ∗
        memRegion x.outPtr 16 ∗
        stackAt s0.sp promoteMatchingSessionMatchStack) ∗ R) := by
    dsimp only [promoteMatchingSessionMatchSpec] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx8, hcur, hver, halice, hlen⟩, hpre_sp⟩ := hpre'
  cases hgc : x.g.cur with
  | none =>
    exfalso
    have hfalse : s0.mem ⊨ ⌜False⌝ ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.g.prevCap x.g.prevPtr [] ∗
         (x.serPtr ↦ₛ x.serBytes) ∗ memRegion x.outPtr 16 ∗
         stackAt s0.sp promoteMatchingSessionMatchStack ∗ R) := by
      simp only [sessionRecordAt, hgc, hcur] at hpre_sp
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_sp
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1
  | some G =>
    refine ⟨⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
             x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩,
            promoteMatchFrame A x.recPtr x.outPtr s0.sp x.g G x.s, ?_, ?_⟩
    · rw [← sepConj_assoc]
      exact Satisfies.mono
        (sepConj_mono_left
          (promoteMatch_pre_entails A x G s0 hgc hx0 hx1 hx2 hx3 hx8 hcur hver halice hlen))
        hpre_sp
    · intro sf hpost
      rw [← sepConj_assoc] at hpost
      exact Satisfies.mono
        (sepConj_mono_left (promoteMatch_post_entails A x G s0 sf hgc hcur halice hlen))
        hpost

/-! ## 32-bit stacked `CliExt.blackBoxSpec` generalization -/

abbrev promoteMatchingSessionMatchStackExt : Nat :=
  promoteMatchingSessionMatchStack + extHookStack

private theorem stackAt_promoteMatchExt_split (sp : BitVec 64) :
    stackAt sp promoteMatchingSessionMatchStackExt =
      stackAt (sp - 1184#64) extHookStack ∗
      stackAt sp promoteMatchingSessionMatchStack := by
  change memRegion (sp - 17568#64) 17568 =
    memRegion ((sp - 1184#64) - 16384#64) 16384 ∗ memRegion (sp - 1184#64) 1184
  rw [show (17568 : Nat) = 16384 + 1184 by decide,
    memRegion_split (sp - 17568#64) 16384 1184 (by decide),
    show (sp - 1184#64) - 16384#64 = sp - 17568#64 by bv_omega,
    show sp - 17568#64 + 16384#64 = sp - 1184#64 by bv_omega]

def promoteMatchingSessionMatchSpecExt (A : RustAlloc) : Spec PromoteMatchGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.r.currentSession = some x.s ∧
     x.s.state.version = x.msgVer.zeroExtend 32 ∧
     x.s.aliceBaseKey = x.serBytes ∧
     x.serBytes.length = 33⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    memRegion x.outPtr 16 ∗
    stackAt st.sp promoteMatchingSessionMatchStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 1#8) ∗
    memRegion (x.outPtr + 9#64) 7 ∗
    stackAt s0.sp promoteMatchingSessionMatchStackExt

private theorem rawPreExt32_eq (y : PromoteRawGhost) (st : State) :
    promoteMatchingSessionRawSpecExt32.pre y st =
      promoteMatchingSessionRawSpec.pre y st ∗ stackAt (st.sp - 1184#64) extHookStack := by
  dsimp only [promoteMatchingSessionRawSpecExt32, promoteMatchingSessionRawSpec]
  ac_rfl

private theorem rawPostExt32_eq (y : PromoteRawGhost) (s0 sf : State) :
    promoteMatchingSessionRawSpecExt32.post y s0 sf =
      promoteMatchingSessionRawSpec.post y s0 sf ∗ stackAt (s0.sp - 1184#64) extHookStack := by
  dsimp only [promoteMatchingSessionRawSpecExt32, promoteMatchingSessionRawSpec]
  ac_rfl

private theorem promoteMatch_pre_entails_ext32 (A : RustAlloc) (x : PromoteMatchGhost)
    (G : SessionGhost) (s0 : State)
    (hgc : x.g.cur = some G)
    (hx0 : s0.readReg64 .x0 = x.recPtr)
    (hx1 : s0.readReg64 .x1 = x.msgVer.zeroExtend 64)
    (hx2 : s0.readReg64 .x2 = x.serPtr)
    (hx3 : s0.readReg64 .x3 = 33#64)
    (hx8 : s0.readReg64 .x8 = x.outPtr)
    (hcur : x.r.currentSession = some x.s)
    (hver : x.s.state.version = x.msgVer.zeroExtend 32)
    (halice : x.s.aliceBaseKey = x.serBytes)
    (hlen : x.serBytes.length = 33) :
    sessionRecordAt A x.recPtr x.g x.r ∗
      (x.serPtr ↦ₛ x.serBytes) ∗
      memRegion x.outPtr 16 ∗
      stackAt s0.sp promoteMatchingSessionMatchStackExt ⊢
    promoteMatchingSessionRawSpecExt32.pre
      ⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
       x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩ s0 ∗
      promoteMatchFrame A x.recPtr x.outPtr s0.sp x.g G x.s := by
  rw [stackAt_promoteMatchExt_split s0.sp, rawPreExt32_eq]
  refine Entails.trans (Entails.of_eq (by ac_rfl : _ =
    (sessionRecordAt A x.recPtr x.g x.r ∗
      (x.serPtr ↦ₛ x.serBytes) ∗
      memRegion x.outPtr 16 ∗
      stackAt s0.sp promoteMatchingSessionMatchStack) ∗
    stackAt (s0.sp - 1184#64) extHookStack)) ?_
  refine Entails.trans
    (sepConj_mono_left
      (promoteMatch_pre_entails A x G s0 hgc hx0 hx1 hx2 hx3 hx8 hcur hver halice hlen))
    (Entails.of_eq (by ac_rfl))

private theorem promoteMatch_post_entails_ext32 (A : RustAlloc) (x : PromoteMatchGhost)
    (G : SessionGhost) (s0 sf : State)
    (hgc : x.g.cur = some G)
    (hcur : x.r.currentSession = some x.s)
    (halice : x.s.aliceBaseKey = x.serBytes)
    (hlen : x.serBytes.length = 33) :
    promoteMatchingSessionRawSpecExt32.post
      ⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
       x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩ s0 sf ∗
      promoteMatchFrame A x.recPtr x.outPtr s0.sp x.g G x.s ⊢
    (promoteMatchingSessionMatchSpecExt A).post x s0 sf := by
  rw [rawPostExt32_eq]
  dsimp only [promoteMatchingSessionMatchSpecExt]
  rw [stackAt_promoteMatchExt_split s0.sp]
  refine Entails.trans (Entails.of_eq (by ac_rfl : _ =
    (promoteMatchingSessionRawSpec.post
      ⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
       x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩ s0 sf ∗
     promoteMatchFrame A x.recPtr x.outPtr s0.sp x.g G x.s) ∗
    stackAt (s0.sp - 1184#64) extHookStack)) ?_
  refine Entails.trans
    (sepConj_mono_left (promoteMatch_post_entails A x G s0 sf hgc hcur halice hlen)) ?_
  dsimp only [promoteMatchingSessionMatchSpec]
  exact Entails.of_eq (by ac_rfl)

theorem promote_matching_session_match_ok_ext32 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>"
      CryptoVerification.SignalSession.CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      (promoteMatchingSessionMatchSpecExt A) := by
  refine subroutine_ok_refine_frame
    (promote_matching_session_raw_ok_ext32 (b := b) (ext := ext) h_bb) ?_
  intro x R s0 hpre
  have hpre' : s0.mem ⊨
      ⌜s0.readReg64 .x0 = x.recPtr ∧
       s0.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
       s0.readReg64 .x2 = x.serPtr ∧
       s0.readReg64 .x3 = 33#64 ∧
       s0.readReg64 .x8 = x.outPtr ∧
       x.r.currentSession = some x.s ∧
       x.s.state.version = x.msgVer.zeroExtend 32 ∧
       x.s.aliceBaseKey = x.serBytes ∧
       x.serBytes.length = 33⌝ ∗
      ((sessionRecordAt A x.recPtr x.g x.r ∗
        (x.serPtr ↦ₛ x.serBytes) ∗
        memRegion x.outPtr 16 ∗
        stackAt s0.sp promoteMatchingSessionMatchStackExt) ∗ R) := by
    dsimp only [promoteMatchingSessionMatchSpecExt] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx8, hcur, hver, halice, hlen⟩, hpre_sp⟩ := hpre'
  cases hgc : x.g.cur with
  | none =>
    exfalso
    have hfalse : s0.mem ⊨ ⌜False⌝ ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.g.prevCap x.g.prevPtr [] ∗
         (x.serPtr ↦ₛ x.serBytes) ∗ memRegion x.outPtr 16 ∗
         stackAt s0.sp promoteMatchingSessionMatchStackExt ∗ R) := by
      simp only [sessionRecordAt, hgc, hcur] at hpre_sp
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_sp
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1
  | some G =>
    refine ⟨⟨x.recPtr, G.localIk.cap, G.alice.ptr, x.s.state.sessionVersion,
             x.msgVer, x.serPtr, x.serBytes, x.outPtr⟩,
            promoteMatchFrame A x.recPtr x.outPtr s0.sp x.g G x.s, ?_, ?_⟩
    · rw [← sepConj_assoc]
      exact Satisfies.mono
        (sepConj_mono_left
          (promoteMatch_pre_entails_ext32 A x G s0 hgc hx0 hx1 hx2 hx3 hx8 hcur hver halice hlen))
        hpre_sp
    · intro sf hpost
      rw [← sepConj_assoc] at hpost
      exact Satisfies.mono
        (sepConj_mono_left (promoteMatch_post_entails_ext32 A x G s0 sf hgc hcur halice hlen))
        hpost

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

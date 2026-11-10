/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.RecordX.Scope
public import LibsignalBinary.Specifications.SignalSession.PqDir
public import LibsignalBinary.Specifications.AsmConstants -- shake: keep

/-!
# `SessionRecord::promote_matching_session` Miss Contracts and Decompositions

Specifications, record/stack decompositions, and constant-time byte-comparison accumulators for
`<SessionRecord>::promote_matching_session` on a populated `SessionRecord` with empty
`previous_sessions` when `¬ SessMatchesMsg s msgVer serBytes`:
1. Version mismatch (`s.state.version ≠ msgVer.zeroExtend 32`).
2. Base-key length mismatch (`s.aliceBaseKey.length ≠ 33`), invoking `subtle::black_box::<u8>(0)`.
3. 33-byte base-key mismatch (`s.aliceBaseKey ≠ serBytes`), running the 33-byte constant-time
   comparison loop (`+0x80..+0x9c`) and final `subtle::black_box::<u8>`.

All three paths converge at `+0xec`, step `Map<Iter<Vec<u8>>, ...>::next` on the empty slice, and
write `Ok(false)` (`0#64` at `outPtr`, `0#8` at `outPtr + 8`) with `sessionRecordAt` preserved.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.SignalSession

/-! ## 1. Stack Budgets & Match Predicate -/

/-- Minimal stack budget of `<SessionRecord>::promote_matching_session` on the miss path when
`subtle::black_box::<u8>` is `blackBoxHook` (`0` stack): `1184` bytes (`0x60 + 0x440`) for
`promote_matching_session` plus `64` bytes (`8` words) for `Map<Iter<Vec<u8>>, ...>::next` on the
empty `previous_sessions` slice. -/
abbrev promoteMatchingSessionMissStack : Nat := 1248

/-- Compatibility stack budget (`1184 + 16384 = 17568` bytes) matching callers that allocate
`extHookStack` below the `1184`-byte frame. -/
abbrev rpkPromoteMatchStackX : Nat := 1184 + 16384

/-- Stack budget of `<SessionRecord>::promote_matching_session` on the matched `current_session`
fast path under `CliExt.blackBoxSpec` (`1184 + extHookStack = 17568` bytes, `rfl`-equal to
`rpkPromoteMatchStackX`). -/
abbrev promoteMatchingSessionMatchStackExt : Nat := 1184 + extHookStack

/-- Stack budget of `<SessionRecord>::promote_matching_session` on any miss path under
`CliExt.blackBoxSpec` (`1248 + extHookStack = 17632` bytes). -/
abbrev p2PromoteMissStackExt : Nat := 1248 + extHookStack

/-- Alias for `p2PromoteMissStackExt` (`1248 + extHookStack = 17632` bytes), mirroring
`promoteMatchingSessionMissStack`. -/
abbrev promoteMatchingSessionMissStackExt : Nat := p2PromoteMissStackExt

/-- Whether a `Session` matches `(msgVer, serBytes)` in `SessionRecord::promote_matching_session`:
its effective protocol version (`2` if raw `sessionVersion = 0`, else `sessionVersion`) equals
`msgVer.zeroExtend 32` and its `alice_base_key` equals `serBytes`. -/
def SessMatchesMsg (s : Session (List (BitVec 8))) (msgVer : BitVec 8)
    (serBytes : List (BitVec 8)) : Prop :=
  s.state.version = msgVer.zeroExtend 32 ∧ s.aliceBaseKey = serBytes

/-- At `msgVer = 4#8` and `serBytes = djbKey m.baseKey`, `SessMatchesMsg` on
`sessionOfX (fun _ => x) g` is equivalent to the trusted `PqSessionMatches x g m`. -/
theorem sessMatchesMsg_sessionOfX_iff_pqSessionMatches
    (x : RecordExtras) (g : GhostState (List (BitVec 8))) (m : PreKeyMessageFields) :
    SessMatchesMsg (sessionOfX (fun _ => x) g) 4#8 (djbKey m.baseKey) ↔
      PqSessionMatches x g m := by
  unfold SessMatchesMsg PqSessionMatches sessionOfX SessionState.version
  dsimp only
  have h4 : (4#8).zeroExtend 32 = 4#32 := rfl
  rw [h4]
  constructor
  · rintro ⟨hv, ha⟩
    refine ⟨ha, ?_⟩
    split at hv
    · cases hv
    · exact hv
  · rintro ⟨ha, hv⟩
    refine ⟨?_, ha⟩
    rw [hv]; rfl

/-! ## 2. Cells-Level Miss Contracts -/

/-- `SessionRecord` fields read by `promote_matching_session` when `current_session = Some` and
`previous_sessions` is empty:
- `recPtr + 0x08`: `previous_sessions.ptr` (`prevPtr`)
- `recPtr + 0x10`: `previous_sessions.len` (`0#64`)
- `recPtr + 0x18`: `current_session` niche word (`curDiscr`, `< 2^63` so `≠ -1`)
- `recPtr + 0x80`: `alice_base_key.ptr` (`abkPtr`)
- `recPtr + 0x88`: `alice_base_key.len` (`abkLen`)
- `recPtr + 0x160`: `session_version` (`sessVer`) -/
def sessionRecordMissPromoteFieldsAt
    (recPtr prevPtr curDiscr abkPtr abkLen : BitVec 64) (sessVer : BitVec 32) : SepProp :=
  ((recPtr + 8#64) ↦₆₄ prevPtr) ∗
  ((recPtr + 16#64) ↦₆₄ 0#64) ∗
  ((recPtr + 0x18#64) ↦₆₄ curDiscr) ∗
  ((recPtr + 0x80#64) ↦₆₄ abkPtr) ∗
  ((recPtr + 0x88#64) ↦₆₄ abkLen) ∗
  ((recPtr + 0x160#64) ↦₃₂ sessVer)

/-- Stack slots touched by `promote_matching_session` on any miss path with empty
`previous_sessions`:
- `cells (sp - 1248) 8`: callee frame of `Map<Iter<Vec<u8>>, ...>::next`
- `cells (sp - 1184) 10`: local scratch slots `[sp .. sp + 0x50)` at `sp_inner = sp - 1184`
- `(sp - 448) ↦₆₄ _`: iterator return tag at `sp_inner + 0x2e0` (`-2` = `None`)
- `cells (sp - 96) 12`: saved frame/callee-saved registers `[sp - 96 .. sp)` -/
def promoteMissStackCells (sp : BitVec 64) : SepProp :=
  cells (sp - 1248#64) 8 ∗
  cells (sp - 1184#64) 10 ∗
  (∃∗ w2e0 : BitVec 64, (sp - 448#64) ↦₆₄ w2e0) ∗
  cells (sp - 96#64) 12

/-- Ghost bundle for the version-mismatch cells contract (`effectiveVer ≠ msgVer.zeroExtend 32`). -/
structure PromoteVerMissRawGhost where
  recPtr : BitVec 64
  prevPtr : BitVec 64
  curDiscr : BitVec 64
  abkPtr : BitVec 64
  abkLen : BitVec 64
  sessVer : BitVec 32
  msgVer : BitVec 8
  serPtr : BitVec 64
  outPtr : BitVec 64

def promoteMatchingSessionVerMissRawSpec : Spec PromoteVerMissRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧
     s.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     s.readReg64 .x2 = x.serPtr ∧
     s.readReg64 .x3 = 33#64 ∧
     s.readReg64 .x8 = x.outPtr ∧
     x.curDiscr ≠ 0xffffffffffffffff#64 ∧
     (if x.sessVer = 0#32 then 2#32 else x.sessVer) ≠ x.msgVer.zeroExtend 32⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr x.abkLen x.sessVer ∗
    (∃∗ w0 : BitVec 64, x.outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (x.outPtr + 8#64) ↦₈ b8) ∗
    promoteMissStackCells s.sp
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr x.abkLen x.sessVer ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    promoteMissStackCells s0.sp

/-- Ghost bundle for the length-mismatch cells contract (`effectiveVer = msgVer.zeroExtend 32`,
`abkLen ≠ 33#64`). -/
structure PromoteLenMissRawGhost where
  recPtr : BitVec 64
  prevPtr : BitVec 64
  curDiscr : BitVec 64
  abkPtr : BitVec 64
  abkLen : BitVec 64
  sessVer : BitVec 32
  msgVer : BitVec 8
  serPtr : BitVec 64
  outPtr : BitVec 64

def promoteMatchingSessionLenMissRawSpec : Spec PromoteLenMissRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧
     s.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     s.readReg64 .x2 = x.serPtr ∧
     s.readReg64 .x3 = 33#64 ∧
     s.readReg64 .x8 = x.outPtr ∧
     x.curDiscr ≠ 0xffffffffffffffff#64 ∧
     (if x.sessVer = 0#32 then 2#32 else x.sessVer) = x.msgVer.zeroExtend 32 ∧
     x.abkLen ≠ 33#64⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr x.abkLen x.sessVer ∗
    (∃∗ w0 : BitVec 64, x.outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (x.outPtr + 8#64) ↦₈ b8) ∗
    promoteMissStackCells s.sp
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr x.abkLen x.sessVer ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    promoteMissStackCells s0.sp

/-- Ghost bundle for the 33-byte key-mismatch cells contract (`effectiveVer = msgVer.zeroExtend 32`,
`ak.length = 33`, `serBytes.length = 33`, `serBytes ≠ ak`). -/
structure PromoteKeyMissRawGhost where
  recPtr : BitVec 64
  prevPtr : BitVec 64
  curDiscr : BitVec 64
  abkPtr : BitVec 64
  sessVer : BitVec 32
  msgVer : BitVec 8
  serPtr : BitVec 64
  outPtr : BitVec 64
  serBytes : List (BitVec 8)
  ak : List (BitVec 8)

def promoteMatchingSessionKeyMissRawSpec : Spec PromoteKeyMissRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧
     s.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     s.readReg64 .x2 = x.serPtr ∧
     s.readReg64 .x3 = 33#64 ∧
     s.readReg64 .x8 = x.outPtr ∧
     x.curDiscr ≠ 0xffffffffffffffff#64 ∧
     (if x.sessVer = 0#32 then 2#32 else x.sessVer) = x.msgVer.zeroExtend 32 ∧
     x.serBytes.length = 33 ∧
     x.ak.length = 33 ∧
     x.serBytes ≠ x.ak⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr 33#64 x.sessVer ∗
    (x.abkPtr ↦ₛ x.ak) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (∃∗ w0 : BitVec 64, x.outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (x.outPtr + 8#64) ↦₈ b8) ∗
    promoteMissStackCells s.sp
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr 33#64 x.sessVer ∗
    (x.abkPtr ↦ₛ x.ak) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    promoteMissStackCells s0.sp

/-! ## 3. Record-Level Contracts (`promoteMatchingSessionMissSpec` & `promoteMatchingSessionRecordOverSpec`) -/

/-- Ghost bundle for `promoteMatchingSessionMissSpec`, mirroring `Matched.PromoteMatchGhost`. -/
structure PromoteMissGhost where
  recPtr : BitVec 64
  msgVer : BitVec 8
  serPtr : BitVec 64
  serBytes : List (BitVec 8)
  outPtr : BitVec 64
  g : RecordGhost
  r : SessionRecord (List (BitVec 8))
  s : Session (List (BitVec 8))

/-- Public specification of `<SessionRecord>::promote_matching_session` on ANY non-matching
populated `SessionRecord` (`r.currentSession = some s`, `¬ SessMatchesMsg s msgVer serBytes`,
empty `previous_sessions` of arbitrary capacity `g.prevCap`): returns `Ok(false)` (`outPtr ↦₆₄ 0#64
∗ (outPtr + 8#64) ↦₈ 0#8`) with `sessionRecordAt A recPtr g r` unchanged. -/
def promoteMatchingSessionMissSpec (A : RustAlloc) : Spec PromoteMissGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.r.currentSession = some x.s ∧
     ¬ SessMatchesMsg x.s x.msgVer x.serBytes ∧
     x.serBytes.length = 33⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    memRegion x.outPtr 16 ∗
    stackAt st.sp promoteMatchingSessionMissStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    memRegion (x.outPtr + 9#64) 7 ∗
    stackAt s0.sp promoteMatchingSessionMissStack

/-- Tuple-shaped 9-byte-outPtr / `rpkPromoteMatchStackX` form for callers with pre-split `outPtr`
cells (`(outPtr ↦₆₄ _) ∗ ((outPtr + 8) ↦₈ _)`) and arbitrary `prevCap` / `¬ SessMatchesMsg`. -/
def promoteMatchingSessionRecordOverSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
      BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key) s =>
    ⌜s.readReg64 .x0 = recPtr ∧
     s.readReg64 .x1 = msgVer.zeroExtend 64 ∧
     s.readReg64 .x2 = serPtr ∧
     s.readReg64 .x3 = 33#64 ∧
     s.readReg64 .x8 = outPtr ∧
     ¬ SessMatchesMsg sess msgVer key ∧
     key.length = 33⌝ ∗
    sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
    (serPtr ↦ₛ key) ∗
    (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
    stackAt s.sp promoteMatchingSessionMissStack
  post := fun (recPtr, prevCap, prevPtr, G, sess, _msgVer, serPtr, outPtr, key) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
    (serPtr ↦ₛ key) ∗
    (outPtr ↦₆₄ 0#64) ∗
    ((outPtr + 8#64) ↦₈ 0#8) ∗
    stackAt s0.sp promoteMatchingSessionMissStack

/-! ## 4. Record & Stack Decompositions -/

/-- The `alice_base_key` heap buffer of `sessionRecordAt`. -/
def aliceBufOverAt (A : RustAlloc) (G : SessionGhost) : SepProp :=
  if G.alice.cap = 0 then emp
  else A.live G.alice.ptr G.alice.cap.toNat 1 ∗ (G.alice.ptr ↦ₛ G.alice.bytes) ∗
    memRegion (G.alice.ptr + BitVec.ofNat 64 G.alice.bytes.length)
      (G.alice.cap.toNat - G.alice.bytes.length)

/-- Rest of `VecGhost` after exposing the capacity word at `v`. -/
def vecGhostCapRestAt (A : RustAlloc) (vg : VecGhost) (v : BitVec 64) : SepProp :=
  ((v + 8#64) ↦₆₄ vg.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vg.bytes.length) ∗
  ⌜vg.bytes.length ≤ vg.cap.toNat ∧ vg.cap.toNat < 2 ^ 63 ∧ vg.ptr ≠ 0⌝ ∗
  (if vg.cap = 0 then emp
   else A.live vg.ptr vg.cap.toNat 1 ∗ (vg.ptr ↦ₛ vg.bytes) ∗
     memRegion (vg.ptr + BitVec.ofNat 64 vg.bytes.length) (vg.cap.toNat - vg.bytes.length))

theorem vecGhostAt_split_cap_over (A : RustAlloc) (vg : VecGhost) (v : BitVec 64) :
    vecGhostAt A vg v = (v ↦₆₄ vg.cap) ∗ vecGhostCapRestAt A vg v := by
  unfold vecGhostAt vecU8At vecHeader vecGhostCapRestAt
  ac_rfl

/-- Rest of `sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some s⟩` after exposing
`sessionRecordMissPromoteFieldsAt` and `aliceBufOverAt`. -/
def sessionRecordMissRestAt (A : RustAlloc) (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) : SepProp :=
  (recPtr ↦₆₄ prevCap) ∗
  vecBuf A 24 8 (fun (_ : Unit) _ => emp) prevCap prevPtr [] ∗
  ⌜PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
    G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat⌝ ∗
  ⌜PublicKey.deserialize G.localIk.bytes = .ok s.state.localIdentity.publicKey ∧
    (match s.state.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = s.state.receiverChains.length ∧
    G.pending.isSome = s.state.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (s.state.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostCapRestAt A G.localIk (recPtr + 0x18#64) ∗
  vecGhostAt A G.remoteIk (recPtr + 0x18#64 + asm64% ssRemoteIdentityOff) ∗
  vecU8At A (recPtr + 0x18#64 + asm64% ssRootKeyOff) G.root.cap G.root.ptr
    (HMAC.keyToBytes32 s.state.rootKey) ∗
  vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A)
    (recPtr + 0x18#64 + asm64% ssReceiverChainsOff)
    G.chainsCap G.chainsPtr (G.chains.zip s.state.receiverChains) ∗
  ((recPtr + 0x18#64 + asm64% ssAliceBaseKeyOff) ↦₆₄ G.alice.cap) ∗
  ⌜G.alice.bytes.length ≤ G.alice.cap.toNat ∧ G.alice.cap.toNat < 2 ^ 63 ∧ G.alice.ptr ≠ 0⌝ ∗
  vecU8At A (recPtr + 0x18#64 + asm64% ssPqRatchetStateOff) G.pq.cap G.pq.ptr s.state.pqRatchetState ∗
  optSenderChainAt A (recPtr + 0x18#64 + asm64% ssSenderChainOff) G.sender s.state.senderChain ∗
  optTailVecAt A (asm% pendingPreKeySize) (recPtr + 0x18#64 + asm64% ssPendingPreKeyOff) G.pending ∗
  optTailVecAt A (asm% pendingKyberPreKeySize) (recPtr + 0x18#64 + asm64% ssPendingKyberPreKeyOff) G.kyber ∗
  ((recPtr + 0x18#64 + asm64% ssPreviousCounterOff) ↦₃₂ s.state.previousCounter) ∗
  ((recPtr + 0x18#64 + asm64% ssRegistrationIdsOff) ↦ₛ G.regIds)

theorem sessionRecordAt_expose_miss (A : RustAlloc) (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) :
    sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some s⟩ =
      sessionRecordMissPromoteFieldsAt recPtr prevPtr G.localIk.cap G.alice.ptr
        (BitVec.ofNat 64 G.alice.bytes.length) s.state.sessionVersion ∗
      aliceBufOverAt A G ∗
      sessionRecordMissRestAt A recPtr prevCap prevPtr G s := by
  unfold sessionRecordAt sessionStateReprAt sessionStateAt sessionRecordMissPromoteFieldsAt
    sessionRecordMissRestAt aliceBufOverAt
  dsimp only
  have hprev : vecAt A 24 8 (fun (_ : Unit) _ => emp) recPtr prevCap prevPtr [] =
      (recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
      vecBuf A 24 8 (fun (_ : Unit) _ => emp) prevCap prevPtr [] := by
    unfold vecAt vecHeader
    ac_rfl
  have hal : vecGhostAt A G.alice (recPtr + 0x18#64 + asm64% ssAliceBaseKeyOff) =
      ((recPtr + 0x18#64 + asm64% ssAliceBaseKeyOff) ↦₆₄ G.alice.cap) ∗
      ((recPtr + 0x80#64) ↦₆₄ G.alice.ptr) ∗
      ((recPtr + 0x88#64) ↦₆₄ BitVec.ofNat 64 G.alice.bytes.length) ∗
      ⌜G.alice.bytes.length ≤ G.alice.cap.toNat ∧ G.alice.cap.toNat < 2 ^ 63 ∧ G.alice.ptr ≠ 0⌝ ∗
      (if G.alice.cap = 0 then emp
       else A.live G.alice.ptr G.alice.cap.toNat 1 ∗ (G.alice.ptr ↦ₛ G.alice.bytes) ∗
         memRegion (G.alice.ptr + BitVec.ofNat 64 G.alice.bytes.length)
           (G.alice.cap.toNat - G.alice.bytes.length)) := by
    unfold vecGhostAt vecU8At vecHeader
    have h80 : (recPtr + 0x18#64 + asm64% ssAliceBaseKeyOff) + 8#64 = recPtr + 0x80#64 := by
      bv_omega
    have h88 : (recPtr + 0x18#64 + asm64% ssAliceBaseKeyOff) + 16#64 = recPtr + 0x88#64 := by
      bv_omega
    rw [h80, h88]
    ac_rfl
  have h160 : (recPtr + 0x18#64 + asm64% ssSessionVersionOff) = recPtr + 0x160#64 := by bv_omega
  rw [hprev, vecGhostAt_split_cap_over A G.localIk (recPtr + 0x18#64), hal, h160]
  ac_rfl

/-- Extracts `G.localIk.cap ≠ -1`, `G.alice.bytes = s.aliceBaseKey`, and
`G.alice.bytes.length ≤ G.alice.cap.toNat < 2 ^ 63` from `sessionRecordAt`. -/
theorem sessionRecordAt_miss_facts {A : RustAlloc} {recPtr prevCap prevPtr : BitVec 64}
    {G : SessionGhost} {s : Session (List (BitVec 8))} {m : Memory} {R : SepProp}
    (h : m ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some s⟩ ∗ R) :
    G.localIk.cap ≠ 0xffffffffffffffff#64 ∧
    G.alice.bytes = s.aliceBaseKey ∧
    G.alice.bytes.length ≤ G.alice.cap.toNat ∧ G.alice.cap.toNat < 2 ^ 63 := by
  have hrec := Satisfies.of_sep_left h
  unfold sessionRecordAt sessionStateReprAt at hrec
  dsimp only at hrec
  have hsess := Satisfies.of_sep_right hrec
  have hpure_sess := Satisfies.of_sep_left hsess
  rw [satisfies_pure] at hpure_sess
  have hss := Satisfies.of_sep_right hsess
  unfold sessionStateAt at hss
  have hloc := Satisfies.of_sep_left (Satisfies.of_sep_right hss)
  unfold vecGhostAt vecU8At at hloc
  have hcap := Satisfies.of_sep_left (Satisfies.of_sep_right hloc)
  rw [satisfies_pure] at hcap
  have hal := Satisfies.of_sep_left (Satisfies.of_sep_right (Satisfies.of_sep_right
    (Satisfies.of_sep_right (Satisfies.of_sep_right (Satisfies.of_sep_right hss)))))
  unfold vecGhostAt vecU8At at hal
  have hal_cap := Satisfies.of_sep_left (Satisfies.of_sep_right hal)
  rw [satisfies_pure] at hal_cap
  have hlt : G.localIk.cap.toNat < 2 ^ 63 := hcap.2.1
  refine ⟨?_, hpure_sess.2.2.1, hal_cap.1, hal_cap.2.1⟩
  intro heq; rw [heq] at hlt; revert hlt; decide

theorem aliceBufOverAt_expose_33 (A : RustAlloc) (G : SessionGhost) (ak : List (BitVec 8))
    (halice : G.alice.bytes = ak) (hlen : ak.length = 33) (hcap : G.alice.cap ≠ 0) :
    aliceBufOverAt A G =
      (G.alice.ptr ↦ₛ ak) ∗
      (A.live G.alice.ptr G.alice.cap.toNat 1 ∗
        memRegion (G.alice.ptr + 33#64) (G.alice.cap.toNat - 33)) := by
  unfold aliceBufOverAt
  simp only [hcap, ↓reduceIte]
  rw [halice, hlen]
  ac_rfl

/-- Splits `stackAt sp promoteMatchingSessionMissStack` (`1248` bytes) into `promoteMissStackCells`
plus the untouched local regions. -/
theorem stackAt_promoteMissStack_eq (sp : BitVec 64) :
    stackAt sp promoteMatchingSessionMissStack =
      promoteMissStackCells sp ∗
      (memRegion (sp - 1104#64) 656 ∗ memRegion (sp - 440#64) 344) := by
  unfold promoteMatchingSessionMissStack promoteMissStackCells
  change memRegion (sp - 1248#64) 1248 = _
  rw [show (1248 : Nat) = 64 + (80 + (656 + (8 + (344 + 96)))) by decide,
      memRegion_split (sp - 1248#64) 64 _ (by decide),
      show sp - 1248#64 + BitVec.ofNat 64 64 = sp - 1184#64 by bv_omega,
      memRegion_split (sp - 1184#64) 80 _ (by decide),
      show sp - 1184#64 + BitVec.ofNat 64 80 = sp - 1104#64 by bv_omega,
      memRegion_split (sp - 1104#64) 656 _ (by decide),
      show sp - 1104#64 + BitVec.ofNat 64 656 = sp - 448#64 by bv_omega,
      memRegion_split (sp - 448#64) 8 _ (by decide),
      show sp - 448#64 + BitVec.ofNat 64 8 = sp - 440#64 by bv_omega,
      memRegion_split (sp - 440#64) 344 96 (by decide),
      show sp - 440#64 + BitVec.ofNat 64 344 = sp - 96#64 by bv_omega,
      ← ProofLib.memRegion_cells (sp - 1248#64) 8 (by decide),
      ← ProofLib.memRegion_cells (sp - 1184#64) 10 (by decide),
      ← ProofLib.memRegion_eight (sp - 448#64),
      ← ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  ac_rfl

/-- Splits `stackAt sp rpkPromoteMatchStackX` (`17568` bytes) into a `16320`-byte frame plus
`stackAt sp promoteMatchingSessionMissStack`. -/
theorem stackAt_rpkPromoteMatchStackX_eq (sp : BitVec 64) :
    stackAt sp rpkPromoteMatchStackX =
      memRegion (sp - 17568#64) 16320 ∗ stackAt sp promoteMatchingSessionMissStack := by
  change memRegion (sp - 17568#64) 17568 =
    memRegion (sp - 17568#64) 16320 ∗ memRegion (sp - 1248#64) 1248
  rw [show (17568 : Nat) = 16320 + 1248 by decide,
      memRegion_split (sp - 17568#64) 16320 1248 (by decide),
      show sp - 17568#64 + BitVec.ofNat 64 16320 = sp - 1248#64 by bv_omega]

theorem outRegion16_split_over (outPtr : BitVec 64) :
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

theorem ofNat_len_ne_33 {n : Nat} (hlt : n < 2 ^ 63) (hne : n ≠ 33) :
    BitVec.ofNat 64 n ≠ 33#64 := by
  intro h
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat] at h2
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h3] at h2
  exact hne h2

/-! ## 5. Constant-Time Comparison Accumulator -/

/-- Byte-list comparison accumulator matching the loop `+0x80..+0x9c` of `promote_matching_session`:
processes `(ks, as_)` left-to-right, AND-ing `(k == a)` into `acc`. -/
def ctBytesEqAcc : List (BitVec 8) → List (BitVec 8) → Bool → Bool
  | [], _, acc => acc
  | _, [], acc => acc
  | k :: ks, a :: as_, acc => ctBytesEqAcc ks as_ ((k == a) && acc)

theorem ctBytesEqAcc_false (ks as_ : List (BitVec 8)) :
    ctBytesEqAcc ks as_ false = false := by
  induction ks generalizing as_ with
  | nil => rfl
  | cons k ks ih =>
    cases as_ with
    | nil => rfl
    | cons a as_ =>
      simp only [ctBytesEqAcc, Bool.and_false]
      exact ih as_

theorem ctBytesEqAcc_true_eq {ks as_ : List (BitVec 8)} (hlen : ks.length = as_.length)
    (ht : ctBytesEqAcc ks as_ true = true) : ks = as_ := by
  induction ks generalizing as_ with
  | nil =>
    cases as_ with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons k ks ih =>
    cases as_ with
    | nil => simp at hlen
    | cons a as_ =>
      simp only [ctBytesEqAcc, Bool.and_true] at ht
      by_cases hka : (k == a) = true
      · rw [hka] at ht
        have heq : k = a := beq_iff_eq.mp hka
        subst heq
        congr 1
        exact ih (by simpa using hlen) ht
      · have hkf : (k == a) = false := Bool.eq_false_iff.mpr hka
        rw [hkf, ctBytesEqAcc_false] at ht
        cases ht

theorem ctBytesEqAcc_true_of_ne {ks as_ : List (BitVec 8)} (hlen : ks.length = as_.length)
    (hne : ks ≠ as_) : ctBytesEqAcc ks as_ true = false := by
  cases h : ctBytesEqAcc ks as_ true with
  | false => rfl
  | true => exact absurd (ctBytesEqAcc_true_eq hlen h) hne

/-! ## 6. Contract-Backed `Ext` Specifications & Frame Combinators (`CliExt.blackBoxSpec`) -/

/-- Stack slots touched by `promote_matching_session` on any miss path with empty
`previous_sessions` under `CliExt.blackBoxSpec` (`extHookStack = 16384` bytes below
`sp_inner = sp - 1184`, which also covers `cells (sp - 1248) 8` used sequentially at `+0xec`). -/
def promoteMissStackCellsExt (sp : BitVec 64) : SepProp :=
  stackAt (sp - 1184#64) extHookStack ∗
  cells (sp - 1184#64) 10 ∗
  (∃∗ w2e0 : BitVec 64, (sp - 448#64) ↦₆₄ w2e0) ∗
  cells (sp - 96#64) 12

def promoteMatchingSessionVerMissRawSpecExt : Spec PromoteVerMissRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧
     s.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     s.readReg64 .x2 = x.serPtr ∧
     s.readReg64 .x3 = 33#64 ∧
     s.readReg64 .x8 = x.outPtr ∧
     x.curDiscr ≠ 0xffffffffffffffff#64 ∧
     (if x.sessVer = 0#32 then 2#32 else x.sessVer) ≠ x.msgVer.zeroExtend 32⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr x.abkLen x.sessVer ∗
    (∃∗ w0 : BitVec 64, x.outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (x.outPtr + 8#64) ↦₈ b8) ∗
    promoteMissStackCellsExt s.sp
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr x.abkLen x.sessVer ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    promoteMissStackCellsExt s0.sp

def promoteMatchingSessionLenMissRawSpecExt : Spec PromoteLenMissRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧
     s.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     s.readReg64 .x2 = x.serPtr ∧
     s.readReg64 .x3 = 33#64 ∧
     s.readReg64 .x8 = x.outPtr ∧
     x.curDiscr ≠ 0xffffffffffffffff#64 ∧
     (if x.sessVer = 0#32 then 2#32 else x.sessVer) = x.msgVer.zeroExtend 32 ∧
     x.abkLen ≠ 33#64⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr x.abkLen x.sessVer ∗
    (∃∗ w0 : BitVec 64, x.outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (x.outPtr + 8#64) ↦₈ b8) ∗
    promoteMissStackCellsExt s.sp
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr x.abkLen x.sessVer ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    promoteMissStackCellsExt s0.sp

def promoteMatchingSessionKeyMissRawSpecExt : Spec PromoteKeyMissRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧
     s.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     s.readReg64 .x2 = x.serPtr ∧
     s.readReg64 .x3 = 33#64 ∧
     s.readReg64 .x8 = x.outPtr ∧
     x.curDiscr ≠ 0xffffffffffffffff#64 ∧
     (if x.sessVer = 0#32 then 2#32 else x.sessVer) = x.msgVer.zeroExtend 32 ∧
     x.serBytes.length = 33 ∧
     x.ak.length = 33 ∧
     x.serBytes ≠ x.ak⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr 33#64 x.sessVer ∗
    (x.abkPtr ↦ₛ x.ak) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (∃∗ w0 : BitVec 64, x.outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (x.outPtr + 8#64) ↦₈ b8) ∗
    promoteMissStackCellsExt s.sp
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordMissPromoteFieldsAt x.recPtr x.prevPtr x.curDiscr x.abkPtr 33#64 x.sessVer ∗
    (x.abkPtr ↦ₛ x.ak) ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    promoteMissStackCellsExt s0.sp

/-- Public specification of `<SessionRecord>::promote_matching_session` on any non-matching
populated `SessionRecord` under `CliExt.blackBoxSpec` at `p2PromoteMissStackExt` (`1248 +
extHookStack = 17632` bytes). -/
def promoteMatchingSessionMissSpecExt (A : RustAlloc) : Spec PromoteMissGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.r.currentSession = some x.s ∧
     ¬ SessMatchesMsg x.s x.msgVer x.serBytes ∧
     x.serBytes.length = 33⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    memRegion x.outPtr 16 ∗
    stackAt st.sp p2PromoteMissStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordAt A x.recPtr x.g x.r ∗
    (x.serPtr ↦ₛ x.serBytes) ∗
    (x.outPtr ↦₆₄ 0#64) ∗
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    memRegion (x.outPtr + 9#64) 7 ∗
    stackAt s0.sp p2PromoteMissStackExt

/-- Tuple-shaped 9-byte-`outPtr` miss contract under `CliExt.blackBoxSpec` at
`p2PromoteMissStackExt` (`1248 + extHookStack = 17632` bytes). -/
def promoteMatchingSessionRecordOverSpecExt (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
      BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key) s =>
    ⌜s.readReg64 .x0 = recPtr ∧
     s.readReg64 .x1 = msgVer.zeroExtend 64 ∧
     s.readReg64 .x2 = serPtr ∧
     s.readReg64 .x3 = 33#64 ∧
     s.readReg64 .x8 = outPtr ∧
     ¬ SessMatchesMsg sess msgVer key ∧
     key.length = 33⌝ ∗
    sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
    (serPtr ↦ₛ key) ∗
    (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
    stackAt s.sp p2PromoteMissStackExt
  post := fun (recPtr, prevCap, prevPtr, G, sess, _msgVer, serPtr, outPtr, key) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
    (serPtr ↦ₛ key) ∗
    (outPtr ↦₆₄ 0#64) ∗
    ((outPtr + 8#64) ↦₈ 0#8) ∗
    stackAt s0.sp p2PromoteMissStackExt

/-- Tight `17568`-byte (`promoteMatchingSessionMatchStackExt = rpkPromoteMatchStackX`) variant of
`promoteMatchingSessionRecordOverSpecExt` for callers that allocate `1184 + extHookStack`. -/
def promoteMatchingSessionRecordOverMatchStackSpecExt (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
      BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key) s =>
    ⌜s.readReg64 .x0 = recPtr ∧
     s.readReg64 .x1 = msgVer.zeroExtend 64 ∧
     s.readReg64 .x2 = serPtr ∧
     s.readReg64 .x3 = 33#64 ∧
     s.readReg64 .x8 = outPtr ∧
     ¬ SessMatchesMsg sess msgVer key ∧
     key.length = 33⌝ ∗
    sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
    (serPtr ↦ₛ key) ∗
    (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
    (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
    stackAt s.sp promoteMatchingSessionMatchStackExt
  post := fun (recPtr, prevCap, prevPtr, G, sess, _msgVer, serPtr, outPtr, key) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
    (serPtr ↦ₛ key) ∗
    (outPtr ↦₆₄ 0#64) ∗
    ((outPtr + 8#64) ↦₈ 0#8) ∗
    stackAt s0.sp promoteMatchingSessionMatchStackExt

/-- Tight `17568`-byte (`promoteMatchingSessionMatchStackExt`) variant of
`promoteMatchingSessionMissSpecExt`. -/
def promoteMatchingSessionMissMatchStackSpecExt (A : RustAlloc) : Spec PromoteMissGhost where
  pre := fun x st =>
    ⌜st.readReg64 .x0 = x.recPtr ∧
     st.readReg64 .x1 = x.msgVer.zeroExtend 64 ∧
     st.readReg64 .x2 = x.serPtr ∧
     st.readReg64 .x3 = 33#64 ∧
     st.readReg64 .x8 = x.outPtr ∧
     x.r.currentSession = some x.s ∧
     ¬ SessMatchesMsg x.s x.msgVer x.serBytes ∧
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
    ((x.outPtr + 8#64) ↦₈ 0#8) ∗
    memRegion (x.outPtr + 9#64) 7 ∗
    stackAt s0.sp promoteMatchingSessionMatchStackExt

/-- Splits `stackAt (sp - 1184) extHookStack` (`16384` B) into `16320` B plus `cells (sp - 1248) 8`
(`64` B) for the sequential `+0xec` `Map::next` epilogue. -/
theorem stackAt_inner_extHookStack_eq (sp : BitVec 64) :
    stackAt (sp - 1184#64) extHookStack =
      memRegion (sp - 17568#64) 16320 ∗ cells (sp - 1248#64) 8 := by
  change memRegion ((sp - 1184#64) - 16384#64) 16384 = _
  rw [show (sp - 1184#64) - 16384#64 = sp - 17568#64 by bv_omega,
      show (16384 : Nat) = 16320 + 64 by decide,
      memRegion_split (sp - 17568#64) 16320 64 (by decide),
      show sp - 17568#64 + BitVec.ofNat 64 16320 = sp - 1248#64 by bv_omega,
      ← ProofLib.memRegion_cells (sp - 1248#64) 8 (by decide)]

theorem promoteMissStackCellsExt_eq (sp : BitVec 64) :
    promoteMissStackCellsExt sp =
      memRegion (sp - 17568#64) 16320 ∗ promoteMissStackCells sp := by
  unfold promoteMissStackCellsExt promoteMissStackCells
  rw [stackAt_inner_extHookStack_eq sp]
  ac_rfl

theorem stackAt_promoteMatchStackExt_eq (sp : BitVec 64) :
    stackAt sp promoteMatchingSessionMatchStackExt =
      promoteMissStackCellsExt sp ∗
      (memRegion (sp - 1104#64) 656 ∗ memRegion (sp - 440#64) 344) := by
  change stackAt sp rpkPromoteMatchStackX = _
  rw [stackAt_rpkPromoteMatchStackX_eq sp, stackAt_promoteMissStack_eq sp,
      promoteMissStackCellsExt_eq sp]
  ac_rfl

theorem stackAt_p2PromoteMissStackExt_eq (sp : BitVec 64) :
    stackAt sp p2PromoteMissStackExt =
      memRegion (sp - 17632#64) 64 ∗ stackAt sp promoteMatchingSessionMatchStackExt := by
  change memRegion (sp - 17632#64) 17632 =
    memRegion (sp - 17632#64) 64 ∗ memRegion (sp - 17568#64) 17568
  rw [show (17632 : Nat) = 64 + 17568 by decide,
      memRegion_split (sp - 17632#64) 64 17568 (by decide),
      show sp - 17632#64 + BitVec.ofNat 64 64 = sp - 17568#64 by bv_omega]

theorem promoteMatchingSessionVerMissRawExt_of_raw {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry promoteMatchingSessionVerMissRawSpec) :
    subroutine_ok prog entry promoteMatchingSessionVerMissRawSpecExt := by
  refine subroutine_ok_refine_frame h ?_
  intro x _ s0 hpre
  refine ⟨x, memRegion (s0.sp - 17568#64) 16320, ?_, ?_⟩
  · dsimp only [promoteMatchingSessionVerMissRawSpecExt, promoteMatchingSessionVerMissRawSpec] at hpre ⊢
    rw [promoteMissStackCellsExt_eq s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    dsimp only [promoteMatchingSessionVerMissRawSpecExt, promoteMatchingSessionVerMissRawSpec] at hpost ⊢
    rw [promoteMissStackCellsExt_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

set_option maxHeartbeats 600000 in
theorem promoteMatchingSessionRecordOverMatchStackExt_of_raw
    {prog : Program} {entry : BitVec 64} (A : RustAlloc)
    (hver : subroutine_ok prog entry promoteMatchingSessionVerMissRawSpecExt)
    (hlen : subroutine_ok prog entry promoteMatchingSessionLenMissRawSpecExt)
    (hkey : subroutine_ok prog entry promoteMatchingSessionKeyMissRawSpecExt) :
    subroutine_ok prog entry (promoteMatchingSessionRecordOverMatchStackSpecExt A) := by
  refine subroutine_ok_by_cases
    (fun (x : BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
      BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) =>
        x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32) ?_ ?_
  · refine subroutine_ok_by_cases
      (fun (x : BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
        BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) =>
          x.2.2.2.2.1.aliceBaseKey.length = 33) ?_ ?_
    · refine subroutine_ok_refine_frame hkey ?_
      intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
      dsimp only [promoteMatchingSessionRecordOverMatchStackSpecExt] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨hlen33, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨hver_eq, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, hmiss, hklen⟩, hmem⟩
      have hne_key : key ≠ sess.aliceBaseKey := fun hk => hmiss ⟨hver_eq, hk.symm⟩
      have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
          ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
           (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
           stackAt s0.sp promoteMatchingSessionMatchStackExt ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
      obtain ⟨hcap_ne, halice, hle, _hlt⟩ := sessionRecordAt_miss_facts hrec_mem
      have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
      have hal33 : G.alice.bytes.length = 33 := by rw [halice]; exact hlen33
      have hcapnz : G.alice.cap ≠ 0 := by
        intro h0
        have h1 : G.alice.cap.toNat = 0 := by simp [h0]
        rw [h1, hal33] at hle; omega
      have habk : BitVec.ofNat 64 G.alice.bytes.length = 33#64 := by rw [hal33]
      rw [habk, aliceBufOverAt_expose_33 A G sess.aliceBaseKey halice hlen33 hcapnz] at hexp
      refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr, sess.state.sessionVersion,
          msgVer, serPtr, outPtr, key, sess.aliceBaseKey⟩,
        sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗
          (A.live G.alice.ptr G.alice.cap.toNat 1 ∗
            memRegion (G.alice.ptr + 33#64) (G.alice.cap.toNat - 33)) ∗
          (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
      · dsimp only [promoteMatchingSessionKeyMissRawSpecExt]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver_eq, hklen, hlen33, hne_key⟩, ?_⟩
        rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp] at hrec_mem
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_mem
      · intro sf hpost
        dsimp only [promoteMatchingSessionKeyMissRawSpecExt,
          promoteMatchingSessionRecordOverMatchStackSpecExt] at hpost ⊢
        rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp]
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    · refine subroutine_ok_refine_frame hlen ?_
      intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
      dsimp only [promoteMatchingSessionRecordOverMatchStackSpecExt] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨hlen_ne, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨hver_eq, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, _hmiss, _hklen⟩, hmem⟩
      have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
          ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
           (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
           stackAt s0.sp promoteMatchingSessionMatchStackExt ∗ R) :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
      obtain ⟨hcap_ne, halice, hle, hlt⟩ := sessionRecordAt_miss_facts hrec_mem
      have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
      have habk_ne : BitVec.ofNat 64 G.alice.bytes.length ≠ 33#64 :=
        ofNat_len_ne_33 (Nat.lt_of_le_of_lt hle hlt) (by rw [halice]; exact hlen_ne)
      refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr,
          BitVec.ofNat 64 G.alice.bytes.length, sess.state.sessionVersion,
          msgVer, serPtr, outPtr⟩,
        sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗ aliceBufOverAt A G ∗
          (serPtr ↦ₛ key) ∗
          (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
      · dsimp only [promoteMatchingSessionLenMissRawSpecExt]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver_eq, habk_ne⟩, ?_⟩
        rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp] at hrec_mem
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_mem
      · intro sf hpost
        dsimp only [promoteMatchingSessionLenMissRawSpecExt,
          promoteMatchingSessionRecordOverMatchStackSpecExt] at hpost ⊢
        rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp]
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine subroutine_ok_refine_frame hver ?_
    intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
    dsimp only [promoteMatchingSessionRecordOverMatchStackSpecExt] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hver_ne, hpre⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, _hmiss, _hklen⟩, hmem⟩
    have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
        ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
         (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
         stackAt s0.sp promoteMatchingSessionMatchStackExt ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    obtain ⟨hcap_ne, _halice, _hle, _hlt⟩ := sessionRecordAt_miss_facts hrec_mem
    have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
    refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr,
        BitVec.ofNat 64 G.alice.bytes.length, sess.state.sessionVersion,
        msgVer, serPtr, outPtr⟩,
      sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗ aliceBufOverAt A G ∗
        (serPtr ↦ₛ key) ∗
        (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
    · dsimp only [promoteMatchingSessionVerMissRawSpecExt]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver_ne⟩, ?_⟩
      rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp] at hrec_mem
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_mem
    · intro sf hpost
      dsimp only [promoteMatchingSessionVerMissRawSpecExt,
        promoteMatchingSessionRecordOverMatchStackSpecExt] at hpost ⊢
      rw [hexp, stackAt_promoteMatchStackExt_eq s0.sp]
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

theorem promoteMatchingSessionRecordOverExt_of_matchStack
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog entry (promoteMatchingSessionRecordOverMatchStackSpecExt A)) :
    subroutine_ok prog entry (promoteMatchingSessionRecordOverSpecExt A) := by
  refine subroutine_ok_refine_frame h ?_
  intro x _ s0 hpre
  refine ⟨x, memRegion (s0.sp - 17632#64) 64, ?_, ?_⟩
  · obtain ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ := x
    dsimp only [promoteMatchingSessionRecordOverSpecExt,
      promoteMatchingSessionRecordOverMatchStackSpecExt] at hpre ⊢
    rw [stackAt_p2PromoteMissStackExt_eq s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    obtain ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ := x
    dsimp only [promoteMatchingSessionRecordOverSpecExt,
      promoteMatchingSessionRecordOverMatchStackSpecExt] at hpost ⊢
    rw [stackAt_p2PromoteMissStackExt_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

set_option maxHeartbeats 400000 in
theorem promoteMatchingSessionMissMatchStackExt_of_recordOver
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog entry (promoteMatchingSessionRecordOverMatchStackSpecExt A)) :
    subroutine_ok prog entry (promoteMatchingSessionMissMatchStackSpecExt A) := by
  refine subroutine_ok_refine_frame h ?_
  intro x R s0 hpre
  dsimp only [promoteMatchingSessionMissMatchStackSpecExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, hcur, hmiss, hklen⟩, hmem⟩
  have hrec_sat : s0.mem ⊨ sessionRecordAt A x.recPtr x.g x.r ∗
      ((x.serPtr ↦ₛ x.serBytes) ∗ memRegion x.outPtr 16 ∗
       stackAt s0.sp promoteMatchingSessionMatchStackExt ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  have hg_some : ∃ G : SessionGhost, x.g.cur = some G := by
    have hrec_l := Satisfies.of_sep_left hrec_sat
    unfold sessionRecordAt at hrec_l
    rw [hcur] at hrec_l
    cases hgc : x.g.cur with
    | none =>
      rw [hgc] at hrec_l
      have hf := Satisfies.of_sep_right hrec_l
      rw [satisfies_pure] at hf
      exact False.elim hf
    | some G => exact ⟨G, rfl⟩
  obtain ⟨G, hgc⟩ := hg_some
  have hrec_eq : sessionRecordAt A x.recPtr x.g x.r =
      sessionRecordAt A x.recPtr ⟨x.g.prevCap, x.g.prevPtr, some G⟩ ⟨some x.s⟩ := by
    unfold sessionRecordAt
    rw [hgc, hcur]
  refine ⟨(x.recPtr, x.g.prevCap, x.g.prevPtr, G, x.s, x.msgVer, x.serPtr, x.outPtr, x.serBytes),
    memRegion (x.outPtr + 9#64) 7, ?_, ?_⟩
  · dsimp only [promoteMatchingSessionRecordOverMatchStackSpecExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hmiss, hklen⟩, ?_⟩
    rw [hrec_eq, outRegion16_split_over x.outPtr] at hrec_sat
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hrec_sat
  · intro sf hpost
    dsimp only [promoteMatchingSessionRecordOverMatchStackSpecExt,
      promoteMatchingSessionMissMatchStackSpecExt] at hpost ⊢
    rw [hrec_eq]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

theorem promoteMatchingSessionMissExt_of_matchStack
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog entry (promoteMatchingSessionMissMatchStackSpecExt A)) :
    subroutine_ok prog entry (promoteMatchingSessionMissSpecExt A) := by
  refine subroutine_ok_refine_frame h ?_
  intro x _ s0 hpre
  refine ⟨x, memRegion (s0.sp - 17632#64) 64, ?_, ?_⟩
  · dsimp only [promoteMatchingSessionMissSpecExt,
      promoteMatchingSessionMissMatchStackSpecExt] at hpre ⊢
    rw [stackAt_p2PromoteMissStackExt_eq s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    dsimp only [promoteMatchingSessionMissSpecExt,
      promoteMatchingSessionMissMatchStackSpecExt] at hpost ⊢
    rw [stackAt_p2PromoteMissStackExt_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

set_option maxHeartbeats 400000 in
/-- Inductive `SepWP` combinator for the constant-time byte-comparison loop (`+0x80..+0xb4`)
threading `stackAt s.sp extHookStack`, 32-bit `w0` return, and `CalleeSavedVRegsPreserved`. -/
theorem ctBytesEq_loop_induct_wp {prog : Program} {loop_pc exit_pc : BitVec 64}
    {recPtr outPtr : BitVec 64}
    (hlast : ∀ (k0 a0 : BitVec 8) (acc : Bool) (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loop_pc → s.status = .Running → (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = 1#64 →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr →
      s.readReg64 .x25 = (if acc = true then 1#64 else 0#64) →
      s.readReg64 .x26 = recPtr →
      SepWP prog exit_pc s ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp extHookStack)
        (fun sf Pf =>
          (Pf ⊢ (serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp extHookStack) ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧
          (sf.readReg64 .x0).setWidth 32 = (if ((k0 == a0) && acc) = true then 1#32 else 0#32) ∧
          sf.readReg64 .x23 = outPtr ∧ sf.readReg64 .x26 = recPtr ∧
          CalleeSavedVRegsPreserved s sf))
    (hstep : ∀ (k0 a0 : BitVec 8) (acc : Bool) (m : Nat),
      0 < m → m + 1 < 2 ^ 64 → ∀ (serPtr alicePtr : BitVec 64) (s : State),
      s.pc = loop_pc → s.status = .Running → (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x19 = alicePtr → s.readReg64 .x21 = BitVec.ofNat 64 (m + 1) →
      s.readReg64 .x22 = serPtr → s.readReg64 .x23 = outPtr →
      s.readReg64 .x25 = (if acc = true then 1#64 else 0#64) →
      s.readReg64 .x26 = recPtr →
      SepWP prog loop_pc s ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp extHookStack)
        (fun s1 Pf =>
          (Pf ⊢ (serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp extHookStack) ∧
          s1.trace = s.trace ∧ s1.sp = s.sp ∧
          s1.readReg64 .x19 = alicePtr + 1#64 ∧
          s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
          s1.readReg64 .x22 = serPtr + 1#64 ∧
          s1.readReg64 .x23 = outPtr ∧
          s1.readReg64 .x25 = (if ((k0 == a0) && acc) = true then 1#64 else 0#64) ∧
          s1.readReg64 .x26 = recPtr ∧
          CalleeSavedVRegsPreserved s s1))
    (ks as_ : List (BitVec 8)) (acc : Bool)
    (hlen : ks.length = as_.length) (hne : ks ≠ []) (hlt : ks.length < 2 ^ 64)
    (serPtr alicePtr : BitVec 64) (s : State)
    (hpc : s.pc = loop_pc) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ks.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64)
    (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP prog exit_pc s ((serPtr ↦ₛ ks) ∗ (alicePtr ↦ₛ as_) ∗ stackAt s.sp extHookStack)
      (fun sf Pf =>
        (Pf ⊢ (serPtr ↦ₛ ks) ∗ (alicePtr ↦ₛ as_) ∗ stackAt s.sp extHookStack) ∧
        sf.trace = s.trace ∧ sf.sp = s.sp ∧
        (sf.readReg64 .x0).setWidth 32 =
          (if ctBytesEqAcc ks as_ acc = true then 1#32 else 0#32) ∧
        sf.readReg64 .x23 = outPtr ∧ sf.readReg64 .x26 = recPtr ∧
        CalleeSavedVRegsPreserved s sf) := by
  induction ks generalizing as_ acc serPtr alicePtr s with
  | nil => exact absurd rfl hne
  | cons k0 krest ih =>
    cases as_ with
    | nil => simp at hlen
    | cons a0 arest =>
      have hlen' : krest.length = arest.length := by simpa using hlen
      cases krest with
      | nil =>
        cases arest with
        | nil =>
          dsimp only [List.length_cons, List.length_nil, ctBytesEqAcc] at hx21 ⊢
          have hpre_eq : ((serPtr ↦ₛ [k0]) ∗ (alicePtr ↦ₛ [a0]) ∗ stackAt s.sp extHookStack) =
              ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp extHookStack) := by
            rw [pointsToBytes_cons, pointsToBytes_nil, pointsToBytes_cons, pointsToBytes_nil]
            simp only [sepConj_emp]
          rw [hpre_eq]
          exact hlast k0 a0 acc serPtr alicePtr s hpc hrun hsp_align hx19 hx21 hx22 hx23 hx25 hx26
        | cons _ _ => simp at hlen'
      | cons k1 krest' =>
        cases arest with
        | nil => simp at hlen'
        | cons a1 arest' =>
          have hm_pos : 0 < (k1 :: krest').length := by simp
          have hm_lt : (k1 :: krest').length + 1 < 2 ^ 64 := by simpa using hlt
          have hlt' : (k1 :: krest').length < 2 ^ 64 := by omega
          dsimp only [List.length_cons] at hx21
          conv =>
            arg 4
            rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
            simp only [sepConj_assoc]
          apply SepWP.seq
          · exact SepWP.frame_auto
              (hstep k0 a0 acc (k1 :: krest').length hm_pos hm_lt serPtr alicePtr s
                hpc hrun hsp_align hx19 hx21 hx22 hx23 hx25 hx26)
          · intro s1 _ hpc1 hrun1
              ⟨hent1, htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hv1⟩
            refine SepWP.weaken_pre hent1 ?_
            have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
            conv => arg 4; rw [← hsp1]
            apply SepWP.seq
            · exact SepWP.frame_auto
                (ih (a1 :: arest') ((k0 == a0) && acc) hlen' (by simp) hlt'
                  (serPtr + 1#64) (alicePtr + 1#64) s1 hpc1 hrun1 hsp_align1
                  hx19_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1)
            · intro sf _ hpcf hrunf ⟨hentf, htrf, hspf, hx0_f, hx23_f, hx26_f, hv_f⟩
              refine SepWP.done hpcf hrunf
                ⟨?_, htrf.trans htr1, hspf.trans hsp1, hx0_f, hx23_f, hx26_f, hv1.trans hv_f⟩
              refine Entails.trans hentf ?_
              rw [hsp1, pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
              sep_frame

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

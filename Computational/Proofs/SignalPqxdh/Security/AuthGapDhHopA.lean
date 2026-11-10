/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHandshake
public import Computational.Proofs.SignalPqxdh.Security.AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.SigHopC
import Computational.Proofs.SignalPqxdh.Security.SigHop
import VCVio.EvalDist.Monad.Basic

/-!
# Provenance-parameterized `Auth` games and reduction simulator

Defines the bundle-provenance-parameterized `Auth` game (`pqxdhAuthWithProvImpl`) and the
simplified simulator `pqxdhAuthSimImpl` used by the `SigEufCma` and `KemShCr` reductions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal
open MeasureTheory
open SignalPqxdh
open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security

export _root_.SignalPqxdh.Security (evalRootKdfOrRoPrim runAuthSendSimPrim runAuthRecvStep2SimPrim runAuthRecvFinishSimPrim runAuthRecvOPKSimPrim runAuthRecvNoOPKSimPrim pqxdhAuthSimImplPrim stepAuthForSigPrim simulateAuthForSigPrim sigReductionAuthAt sigReductionAuthRun sigReductionAuth)

/-! ## Provenance-parameterized `Auth` game -/

theorem list_all_congr {α : Type} :
    ∀ {l : List α} {p q : α → Bool}, (∀ x ∈ l, p x = q x) → l.all p = l.all q
  | [], _, _, _ => rfl
  | x :: xs, p, q, h => by
    simp only [List.all_cons, h x List.mem_cons_self,
      list_all_congr (fun y hy => h y (List.mem_cons_of_mem _ hy))]

abbrev ProvFnType :=
  List (Nat × PrincipalEntry) →
  List ((Nat × Nat) × SpkBundleEntry) →
  List ((Nat × Nat × Nat) × OpkEntry) →
  PreKeyBundleInput → Bool × Bool × Bool

def runAuthSendWithProv (S : Setup) (P : Primitives) (provFn : ProvFnType)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) :
    StateT (AuthState S) ProbComp AuthResponse := do
  let st ← get
  if m0.length != m1.length then return .noneResp
  if st.usedSendSessions.contains sid then return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return .noneResp
  let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  if !isFreshPeer && m0 != m1 then
    return .noneResp
  let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
  if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
    return .noneResp
  let ekASk ← liftM sampleScalar32
  let kemCoins ← liftM sampleCoins32
  let ephASk ← liftM sampleScalar32
  let spqrCoins ← liftM sampleCoins32
  let sigPkB := resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return .noneResp
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return .noneResp
  let ekAPk := P.x25519Base ekASk
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
  let ephAPk := P.x25519Base ephASk
  let dhRatchet := P.x25519 ephASk bundle.spkB
  let ((rk1, ck1_0), rootRoCache') ← liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey
    dhRatchet)
  let mkSeed := P.chainKdfSeed ck1_0
  let ck1_1 := P.chainKdfNext ck1_0
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) := P.spqrInitSend drKey.pqrKey spqrCoins
    | return .noneResp
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let wireMsg : PreKeyMsg := {
    hdr          := hdr
    ephAPk       := ephAPk
    pqRatchetMsg := pqRatchetMsg
    aeadCt       := aeadCt
  }
  let (spkHon, opkHon, pqspkHon) :=
    provFn st.principals st.spkBundles st.opkEntries bundle
  let sessEntry : AuthInitiatorEntry S := {
    sid         := sid
    peerIkPk    := bundle.ikB
    peerSpkPk   := bundle.spkB
    peerOpkPk?  := bundle.opkB?.map Prod.snd
    peerPqspkPk := bundle.pqspkB
    spkHonest   := spkHon
    opkHonest   := opkHon
    pqspkHonest := pqspkHon
    ekASk       := ekASk
    ephASk      := ephASk
    fresh       := isFreshPeer
    challenged  := isFreshPeer && (m0 != m1)
  }
  let (sentOPK', sentNoOPK') :=
    match peerPrincipal?, bundle.opkB? with
    | some (_, pEntry), some (_, opkPk) =>
      let ev : SentOPKEvent := {
        a0 := uEntry.ikAPk, b0 := pEntry.ikAPk, sb := bundle.spkB, ob := opkPk,
        a1 := ekAPk, pk1 := bundle.pqspkB, ct := kemCt, m := msgPlain, matched := false
      }
      (ev :: st.sentOPKEvents, st.sentNoOPKEvents)
    | some (_, pEntry), none =>
      let ev : SentNoOPKEvent := {
        a0 := uEntry.ikAPk, b0 := pEntry.ikAPk, sb := bundle.spkB,
        a1 := ekAPk, pk1 := bundle.pqspkB, ct := kemCt, m := msgPlain, matched := false
      }
      (st.sentOPKEvents, ev :: st.sentNoOPKEvents)
    | none, _ => (st.sentOPKEvents, st.sentNoOPKEvents)
  set { st with
    sessions         := sessEntry :: st.sessions
    usedSendSessions := sid :: st.usedSendSessions
    sentOPKEvents    := sentOPK'
    sentNoOPKEvents  := sentNoOPK'
    roCache          := roCache'
    rootRoCache      := rootRoCache' }
  if peerPrincipal?.isSome then
    return .sendFreshResp wireMsg
  else
    return .sendUnfreshResp drKey rk1 ck1_1 wireMsg

/-- `pqxdhAuthImpl true true S P` parameterized by `provFn`. -/
def pqxdhAuthWithProvImpl (S : Setup) (P : Primitives) (provFn : ProvFnType) :
    QueryImpl (authSpec S) (StateT (AuthState S) ProbComp) := fun q =>
  match q with
  | .sendOPK u i bundle m0 m1 => do
    if bundle.opkB?.isNone then return .noneResp
    runAuthSendWithProv S P provFn (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 => do
    if bundle.opkB?.isSome then return .noneResp
    runAuthSendWithProv S P provFn (.sendNoOPK u i) u bundle m0 m1
  | q_other => pqxdhAuthImpl true true S P q_other

@[simp]
theorem pqxdhAuthWithProvImpl_checkBundleProvenance (S : Setup) (P : Primitives) :
    pqxdhAuthWithProvImpl S P (checkBundleProvenance P) = pqxdhAuthImpl true true S P := by
  funext q
  cases q <;> rfl

def mapAuthSessions {S : Setup} (f : AuthInitiatorEntry S → AuthInitiatorEntry S)
    (st : AuthState S) : AuthState S :=
  { st with sessions := st.sessions.map f }

@[simp]
theorem mapAuthSessions_empty {S : Setup} (f : AuthInitiatorEntry S → AuthInitiatorEntry S) (secb :
    Bool) :
    mapAuthSessions f (AuthState.empty S secb) = AuthState.empty S secb := rfl

theorem runAuthSendWithProv_commutes_mapAuthSessions (S : Setup) (P : Primitives)
    (f : Bool × Bool × Bool → Bool × Bool × Bool)
    (prov1 prov2 : ProvFnType)
    (h_prov : ∀ p b o bnd, prov1 p b o bnd = f (prov2 p b o bnd))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := f (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    CommutesRel (mapAuthSessions mapEntry) st
      (runAuthSendWithProv S P prov1 sid u bundle m0 m1)
      (runAuthSendWithProv S P prov2 sid u bundle m0 m1) := by
  intro mapEntry
  unfold runAuthSendWithProv
  apply CommutesRel.get_bind
  dsimp only [mapAuthSessions]
  have hp := h_prov st.principals st.spkBundles st.opkEntries bundle
  rcases h1 : prov1 st.principals st.spkBundles st.opkEntries bundle with ⟨s1, o1, p1⟩
  rcases h2 : prov2 st.principals st.spkBundles st.opkEntries bundle with ⟨s2, o2, p2⟩
  rw [h1, h2] at hp
  repeat (first
    | apply CommutesRel.pure
    | (rw [pure_bind, pure_bind])
    | (apply CommutesRel.liftM_bind; intro _)
    | (apply CommutesRel.set_bind; simp [mapAuthSessions, mapEntry, ← hp])
    | apply CommutesRel.ite
    | split)

theorem pqxdhAuthWithProvImpl_commutes_mapAuthSessions (S : Setup) (P : Primitives)
    (f : Bool × Bool × Bool → Bool × Bool × Bool)
    (prov1 prov2 : ProvFnType)
    (h_prov : ∀ p b o bnd, prov1 p b o bnd = f (prov2 p b o bnd))
    (q : AuthQuery S) (st : AuthState S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := f (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    CommutesRel (mapAuthSessions mapEntry) st
      (pqxdhAuthWithProvImpl S P prov1 q)
      (pqxdhAuthWithProvImpl S P prov2 q) := by
  intro mapEntry
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthWithProvImpl; dsimp only
    by_cases h : bundle.opkB?.isNone = true
    · simp only [h, ↓reduceIte]; exact CommutesRel.pure _ st _
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact runAuthSendWithProv_commutes_mapAuthSessions S P f prov1 prov2 h_prov (.sendOPK u i) u
        bundle m0 m1 st
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthWithProvImpl; dsimp only
    by_cases h : bundle.opkB?.isSome = true
    · simp only [h, ↓reduceIte]; exact CommutesRel.pure _ st _
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact runAuthSendWithProv_commutes_mapAuthSessions S P f prov1 prov2 h_prov (.sendNoOPK u i) u
        bundle m0 m1 st
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _
      | roQuery _ | roRootQuery _ _ | revealDhSecrets | registerKey _ =>
    unfold pqxdhAuthWithProvImpl pqxdhAuthImpl registerAdvKey
    apply CommutesRel.get_bind
    dsimp only [mapAuthSessions]
    repeat (first
      | apply CommutesRel.pure
      | (rw [pure_bind, pure_bind])
      | (apply CommutesRel.liftM_bind; intro _)
      | (apply CommutesRel.set_bind; rfl)
      | apply CommutesRel.ite
      | split)

def checkBundleProvenanceDual (P : Primitives) : ProvFnType :=
  fun principals spkBundles opkEntries bundle =>
    let (spkExact, _, _) :=
      checkBundleProvenanceExact P principals spkBundles opkEntries bundle
    let (spkHon, opkHon, pqspkHon) :=
      checkBundleProvenance P principals spkBundles opkEntries bundle
    (spkExact, spkHon || opkHon, pqspkHon)

def checkBundleProvenanceSquashed (P : Primitives) : ProvFnType :=
  fun principals spkBundles opkEntries bundle =>
    let (spkHon, opkHon, pqspkHon) :=
      checkBundleProvenance P principals spkBundles opkEntries bundle
    (false, spkHon || opkHon, pqspkHon)

def checkBundleProvenanceNoOpk (P : Primitives) : ProvFnType :=
  fun principals spkBundles opkEntries bundle =>
    let (spkExact, _, _) :=
      checkBundleProvenanceExact P principals spkBundles opkEntries bundle
    let (_, _, pqspkHon) :=
      checkBundleProvenance P principals spkBundles opkEntries bundle
    (spkExact, false, pqspkHon)

def squashTriples : Bool × Bool × Bool → Bool × Bool × Bool :=
  fun (s, o, p) => (false, s || o, p)

def eraseOpkTriples : Bool × Bool × Bool → Bool × Bool × Bool :=
  fun (s, _, p) => (s, false, p)

theorem checkBundleProvenanceSquashed_eq_squash_orig (P : Primitives) :
    ∀ p b o bnd,
      checkBundleProvenanceSquashed P p b o bnd =
        squashTriples (checkBundleProvenance P p b o bnd) := by
  intro p b o bnd
  rfl

theorem checkBundleProvenanceSquashed_eq_squash_dual (P : Primitives) :
    ∀ p b o bnd,
      checkBundleProvenanceSquashed P p b o bnd =
        squashTriples (checkBundleProvenanceDual P p b o bnd) := by
  intro principals spkBundles opkEntries bundle
  unfold checkBundleProvenanceSquashed checkBundleProvenanceDual
    checkBundleProvenanceExact checkBundleProvenance squashTriples
  cases findHonestPrincipal P principals bundle.ikB with
  | none => rfl
  | some pair =>
    rcases pair with ⟨k, _⟩
    dsimp only
    cases h_se : spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB) with
    | false => simp
    | true =>
      have h_sh := spkExact_imp_spkHon P k spkBundles bundle.spkB h_se
      simp [h_sh]

theorem checkBundleProvenanceNoOpk_eq_eraseOpk_dual (P : Primitives) :
    ∀ p b o bnd,
      checkBundleProvenanceNoOpk P p b o bnd =
        eraseOpkTriples (checkBundleProvenanceDual P p b o bnd) := by
  intro p b o bnd
  rfl

theorem checkBundleProvenanceNoOpk_eq_eraseOpk_exact (P : Primitives) :
    ∀ p b o bnd,
      checkBundleProvenanceNoOpk P p b o bnd =
        eraseOpkTriples (checkBundleProvenanceExact P p b o bnd) := by
  intro principals spkBundles opkEntries bundle
  unfold checkBundleProvenanceNoOpk checkBundleProvenanceExact checkBundleProvenance eraseOpkTriples
  cases findHonestPrincipal P principals bundle.ikB <;> rfl

/-! ## Simplified reduction simulator -/

theorem simulateQ_evalRootKdfOrRoPrim (useRo : Bool) (P : Primitives)
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (rk dh : Bytes) :
    simulateQ (primBaseImpl P) (evalRootKdfOrRoPrim useRo rootRoCache rk dh) =
      evalRootKdfOrRo useRo P rootRoCache rk dh := by
  unfold evalRootKdfOrRoPrim evalRootKdfOrRo
  cases useRo with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases rootRoCache.find? (fun (inp, _) => inp == (rk, dh)) with
    | some p => rfl
    | none => simp

def runAuthSendSim (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) :
    StateT (AuthState S) ProbComp AuthResponse := do
  let st ← get
  if m0.length != m1.length then return .noneResp
  if st.usedSendSessions.contains sid then return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return .noneResp
  let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  if !isFreshPeer && m0 != m1 then
    return .noneResp
  let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
  if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
    return .noneResp
  let ekASk ← liftM sampleScalar32
  let kemCoins ← liftM sampleCoins32
  let ephASk ← liftM sampleScalar32
  let spqrCoins ← liftM sampleCoins32
  let sigPkB := resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return .noneResp
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return .noneResp
  let ekAPk := P.x25519Base ekASk
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
  let ephAPk := P.x25519Base ephASk
  let dhRatchet := P.x25519 ephASk bundle.spkB
  let ((rk1, ck1_0), rootRoCache') ←
    liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet)
  let mkSeed := P.chainKdfSeed ck1_0
  let ck1_1 := P.chainKdfNext ck1_0
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) := P.spqrInitSend drKey.pqrKey spqrCoins
    | return .noneResp
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let wireMsg : PreKeyMsg := {
    hdr          := hdr
    ephAPk       := ephAPk
    pqRatchetMsg := pqRatchetMsg
    aeadCt       := aeadCt
  }
  let (spkHon, opkHon, pqspkHon) :=
    match peerPrincipal? with
    | none => (false, false, false)
    | some (k, _) =>
      (st.spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB),
       false,
       st.spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB))
  let sessEntry : AuthInitiatorEntry S := {
    sid         := sid
    peerIkPk    := bundle.ikB
    peerSpkPk   := bundle.spkB
    peerOpkPk?  := bundle.opkB?.map Prod.snd
    peerPqspkPk := bundle.pqspkB
    spkHonest   := spkHon
    opkHonest   := opkHon
    pqspkHonest := pqspkHon
    ekASk       := ekASk
    ephASk      := ephASk
    fresh       := isFreshPeer
    challenged  := isFreshPeer && (m0 != m1)
  }
  set { st with
    sessions         := sessEntry :: st.sessions
    usedSendSessions := sid :: st.usedSendSessions
    roCache          := roCache'
    rootRoCache      := rootRoCache' }
  if peerPrincipal?.isSome then
    return .sendFreshResp wireMsg
  else
    return .sendUnfreshResp drKey rk1 ck1_1 wireMsg

/-- Simplified `Auth` oracle for `SigEufCma` and `KemShCr` reductions, omitting win/event logs and caching `(P.pow8 pk, pk)` on `.registerKey`. -/
def pqxdhAuthSimImpl (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthState S) ProbComp) := fun q =>
  match q with
  | .sendOPK u i bundle m0 m1 => do
    if bundle.opkB?.isNone then return .noneResp
    runAuthSendSim S P (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 => do
    if bundle.opkB?.isSome then return .noneResp
    runAuthSendSim S P (.sendNoOPK u i) u bundle m0 m1
  | .recvOPK k j o msg => do
    let st ← get
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return .noneResp
    if st.usedRecvOPK.contains (k.val, j.val, o.val) then return .noneResp
    if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then return .noneResp
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return .noneResp
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return .noneResp
    let some (_, oEntry) := st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
      | return .noneResp
    if oEntry.consumed then return .noneResp
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return .noneResp
    let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
    let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
    let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
    let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
    let ((rk1, ck1_0), rootRoCache') ←
      liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet)
    let mkSeed := P.chainKdfSeed ck1_0
    let ck1_1 := P.chainKdfNext ck1_0
    let some (_pqrStB, spqrSalt?) := P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg
      | return .noneResp
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    let some pt := P.aeadDec deriveMessageKeys ad msg.aeadCt
      | return .noneResp
    let opkEntries' := st.opkEntries.map (fun (idx, e) =>
      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
    match findHonestPrincipal P st.principals msg.hdr.ikAPk with
    | some _ =>
      set { st with
        opkEntries       := opkEntries'
        usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvHonestResp
    | none =>
      set { st with
        opkEntries       := opkEntries'
        usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvUnfreshResp drKey rk1 ck1_1 pt
  | .recvNoOPK k j l msg => do
    let st ← get
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == none &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return .noneResp
    if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then return .noneResp
    if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then return .noneResp
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return .noneResp
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return .noneResp
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return .noneResp
    let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 none ss
    let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
    let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
    let ((rk1, ck1_0), rootRoCache') ←
      liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet)
    let mkSeed := P.chainKdfSeed ck1_0
    let ck1_1 := P.chainKdfNext ck1_0
    let some (_pqrStB, spqrSalt?) := P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg
      | return .noneResp
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    let some pt := P.aeadDec deriveMessageKeys ad msg.aeadCt
      | return .noneResp
    match findHonestPrincipal P st.principals msg.hdr.ikAPk with
    | some _ =>
      set { st with
        usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvHonestResp
    | none =>
      set { st with
        usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvUnfreshResp drKey rk1 ck1_1 pt
  | .registerKey sk => do
    let st ← get
    if sk.length != 32 then return .noneResp
    let pk := P.x25519Base sk
    let pk8 := P.pow8 pk
    set { st with advKeys := (pk8, pk) :: st.advKeys }
    return .pkResp pk
  | q_other => pqxdhAuthImpl true true S P q_other

def projAuthSim (S : Setup) (P : Primitives) (st : AuthState S) : AuthState S :=
  { st with
    hasWonAuth       := false
    sentOPKEvents    := []
    sentNoOPKEvents  := []
    recvdOPKEvents   := []
    recvdNoOPKEvents := []
    advKeys          := st.advKeys.map (fun (_, pk') => (P.pow8 pk', pk')) }

@[simp]
theorem projAuthSim_empty (S : Setup) (P : Primitives) (secb : Bool) :
    projAuthSim S P (AuthState.empty S secb) = AuthState.empty S secb := rfl

theorem runAuthSendSim_commutes_projAuthSim (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) :
    CommutesRel (projAuthSim S P) st
      (runAuthSendSim S P sid u bundle m0 m1)
      (runAuthSendWithProv S P (checkBundleProvenanceNoOpk P) sid u bundle m0 m1) := by
  unfold runAuthSendSim runAuthSendWithProv checkBundleProvenanceNoOpk
    checkBundleProvenanceExact checkBundleProvenance
  apply CommutesRel.get_bind
  dsimp only [projAuthSim]
  rw [koskBundleOk_map_cache]
  repeat (first
    | apply CommutesRel.pure
    | (rw [pure_bind, pure_bind])
    | (apply CommutesRel.liftM_bind; intro _)
    | (apply CommutesRel.set_bind; (cases findHonestPrincipal P st.principals bundle.ikB <;> rfl))
    | apply CommutesRel.ite
    | split)

theorem pqxdhAuthSimImpl_commutes_projAuthSim (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (q : AuthQuery S) (st : AuthState S) :
    CommutesRel (projAuthSim S P) st
      (pqxdhAuthSimImpl S P q)
      (pqxdhAuthWithProvImpl S P (checkBundleProvenanceNoOpk P) q) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthSimImpl pqxdhAuthWithProvImpl; dsimp only
    by_cases h : bundle.opkB?.isNone = true
    · simp only [h, ↓reduceIte]; exact CommutesRel.pure _ st _
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact runAuthSendSim_commutes_projAuthSim S P (.sendOPK u i) u bundle m0 m1 st
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthSimImpl pqxdhAuthWithProvImpl; dsimp only
    by_cases h : bundle.opkB?.isSome = true
    · simp only [h, ↓reduceIte]; exact CommutesRel.pure _ st _
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact runAuthSendSim_commutes_projAuthSim S P (.sendNoOPK u i) u bundle m0 m1 st
  | recvOPK k j o msg =>
    unfold pqxdhAuthSimImpl pqxdhAuthWithProvImpl pqxdhAuthImpl
    apply CommutesRel.get_bind
    dsimp only [projAuthSim]
    rw [koskSenderOk_map_cache]
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    cases st.principals.find? (fun (idx, _) => idx == k.val) with
    | none => exact CommutesRel.pure _ st _
    | some kp =>
      rcases kp with ⟨_, kEntry⟩; dsimp only
      cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => exact CommutesRel.pure _ st _
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only
        cases st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => exact CommutesRel.pure _ st _
        | some op =>
          rcases op with ⟨_, oEntry⟩; dsimp only
          apply CommutesRel.ite; · exact CommutesRel.pure _ st _
          apply CommutesRel.ite; · exact CommutesRel.pure _ st _
          by_cases hct : msg.hdr.kemCt.length = kyberCtLen
          · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = false := by simp [hct]
            simp only [hctb, Bool.false_eq_true, ↓reduceIte]
            cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
            | none => exact CommutesRel.pure _ st _
            | some ss =>
              dsimp only
              apply CommutesRel.liftM_bind; rintro ⟨drKey, roCache'⟩
              apply CommutesRel.liftM_bind; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
              cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
              | none => exact CommutesRel.pure _ st _
              | some spqr =>
                rcases spqr with ⟨_, spqrSalt?⟩; dsimp only
                cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                  (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
                | none => exact CommutesRel.pure _ st _
                | some pt =>
                  dsimp only
                  cases findHonestPrincipal P st.principals msg.hdr.ikAPk with
                  | none => exact CommutesRel.set_bind _ st _ _ rfl (CommutesRel.pure _ _ _)
                  | some sp =>
                    rcases sp with ⟨_, senderEntry⟩; dsimp only
                    cases !senderEntry.corrupted <;>
                      exact CommutesRel.set_bind _ st _ _ rfl (CommutesRel.pure _ _ _)
          · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = true := by simp [hct]
            rw [hP.kemDecaps_len_reject _ _ hct]
            simp only [hctb, ↓reduceIte]
            exact CommutesRel.pure _ st _
  | recvNoOPK k j l msg =>
    unfold pqxdhAuthSimImpl pqxdhAuthWithProvImpl pqxdhAuthImpl
    apply CommutesRel.get_bind
    dsimp only [projAuthSim]
    rw [koskSenderOk_map_cache]
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    cases st.principals.find? (fun (idx, _) => idx == k.val) with
    | none => exact CommutesRel.pure _ st _
    | some kp =>
      rcases kp with ⟨_, kEntry⟩; dsimp only
      cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => exact CommutesRel.pure _ st _
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only
        apply CommutesRel.ite; · exact CommutesRel.pure _ st _
        by_cases hct : msg.hdr.kemCt.length = kyberCtLen
        · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = false := by simp [hct]
          simp only [hctb, Bool.false_eq_true, ↓reduceIte]
          cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none => exact CommutesRel.pure _ st _
          | some ss =>
            dsimp only
            apply CommutesRel.liftM_bind; rintro ⟨drKey, roCache'⟩
            apply CommutesRel.liftM_bind; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
            cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
            | none => exact CommutesRel.pure _ st _
            | some spqr =>
              rcases spqr with ⟨_, spqrSalt?⟩; dsimp only
              cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
              | none => exact CommutesRel.pure _ st _
              | some pt =>
                dsimp only
                cases findHonestPrincipal P st.principals msg.hdr.ikAPk with
                | none => exact CommutesRel.set_bind _ st _ _ rfl (CommutesRel.pure _ _ _)
                | some sp =>
                  rcases sp with ⟨_, senderEntry⟩; dsimp only
                  cases !senderEntry.corrupted <;>
                    exact CommutesRel.set_bind _ st _ _ rfl (CommutesRel.pure _ _ _)
        · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = true := by simp [hct]
          rw [hP.kemDecaps_len_reject _ _ hct]
          simp only [hctb, ↓reduceIte]
          exact CommutesRel.pure _ st _
  | registerKey sk =>
    unfold pqxdhAuthSimImpl pqxdhAuthWithProvImpl pqxdhAuthImpl registerAdvKey
    apply CommutesRel.get_bind
    dsimp only [projAuthSim]
    split_ifs
    · exact CommutesRel.pure _ st _
    · exact CommutesRel.set_bind (projAuthSim S P) st _ _ rfl (CommutesRel.pure _ _ _)
  | initPrin u | corruptIK u | genSPK u j | genOPK u j o | roQuery _ | roRootQuery _ _
      | revealDhSecrets =>
    unfold pqxdhAuthSimImpl pqxdhAuthWithProvImpl pqxdhAuthImpl
    apply CommutesRel.get_bind
    dsimp only [projAuthSim]
    repeat (first
      | apply CommutesRel.pure
      | (rw [pure_bind, pure_bind])
      | (apply CommutesRel.liftM_bind; intro _)
      | (apply CommutesRel.set_bind; rfl)
      | apply CommutesRel.ite
      | split)

@[simp] theorem simulateQ_primQ_rootCreateChain (P : Primitives) (rk dh : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.rootCreateChain rk dh)) =
      (pure (P.rootCreateChain rk dh) : ProbComp (primSpec.Range (.rootCreateChain rk dh))) := rfl
@[simp] theorem simulateQ_primQ_chainKdfSeed (P : Primitives) (ck : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.chainKdfSeed ck)) =
      (pure (P.chainKdfSeed ck) : ProbComp (primSpec.Range (.chainKdfSeed ck))) := rfl
@[simp] theorem simulateQ_primQ_chainKdfNext (P : Primitives) (ck : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.chainKdfNext ck)) =
      (pure (P.chainKdfNext ck) : ProbComp (primSpec.Range (.chainKdfNext ck))) := rfl
@[simp] theorem simulateQ_primQ_spqrInitSend (P : Primitives) (k r : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.spqrInitSend k r)) =
      (pure (P.spqrInitSend k r) : ProbComp (primSpec.Range (.spqrInitSend k r))) := rfl
@[simp] theorem simulateQ_primQ_spqrInitRecv (P : Primitives) (k msg : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.spqrInitRecv k msg)) =
      (pure (P.spqrInitRecv k msg) : ProbComp (primSpec.Range (.spqrInitRecv k msg))) := rfl
@[simp] theorem simulateQ_primQ_deriveMsgKeys (P : Primitives) (s : Bytes) (salt? : Option Bytes) :
    simulateQ (primBaseImpl P) (primQ (.deriveMsgKeys s salt?)) =
      (pure (P.deriveMsgKeys s salt?) : ProbComp (primSpec.Range (.deriveMsgKeys s salt?))) := rfl
@[simp] theorem simulateQ_primQ_aeadEnc (P : Primitives) (mk : MessageKeys) (ad pt : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.aeadEnc mk ad pt)) =
      (pure (P.aeadEnc mk ad pt) : ProbComp (primSpec.Range (.aeadEnc mk ad pt))) := rfl
@[simp] theorem simulateQ_primQ_aeadDec (P : Primitives) (mk : MessageKeys) (ad ct : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.aeadDec mk ad ct)) =
      (pure (P.aeadDec mk ad ct) : ProbComp (primSpec.Range (.aeadDec mk ad ct))) := rfl

theorem simulateQ_runAuthSendSimPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S)
    (hPrin : st.principals.length ≤ S.N_dh)
    (hSpk : st.spkBundles.length ≤ S.N_dh)
    (hOpk : st.opkEntries.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P st.advKeys) :
    simulateQ (primBaseImpl P) ((runAuthSendSimPrim S sid u bundle m0 m1).run st) =
      (runAuthSendSim S P sid u bundle m0 m1).run st := by
  unfold runAuthSendSimPrim runAuthSendSim
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h_len : (m0.length != m1.length) = true
  · simp only [h_len, ↓reduceIte]; rfl
  · simp only [h_len, Bool.false_eq_true, ↓reduceIte]
    by_cases h_sid : st.usedSendSessions.contains sid = true
    · simp only [h_sid, ↓reduceIte]; rfl
    · simp only [h_sid, Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => rfl
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
          simulateQ_bind]
        rw [simulateQ_findHonestPrincipalPrim S P st.principals bundle.ikB hPrin, pure_bind]
        conv =>
          lhs; arg 2; arg 1; arg 1
          change (!(match
              findHonestPrincipal P st.principals bundle.ikB
            with | some (_, pEntry) => !pEntry.corrupted | none => false) &&
            (m0 != m1)) = true
        by_cases h_m :
          (!(match
              findHonestPrincipal P st.principals bundle.ikB
            with | some (_, pEntry) => !pEntry.corrupted | none => false) &&
            (m0 != m1)) = true
        · simp only [h_m, ↓reduceIte]; rfl
        · simp only [h_m, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
            StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc, simulateQ_bind]
          rw [simulateQ_koskBundleOkPrim S P st.principals st.spkBundles st.opkEntries st.advKeys
            bundle hPrin hSpk hOpk hAdv,
              pure_bind]
          by_cases h_kosk : (!koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys
            bundle) = true
          · simp only [h_kosk, ↓reduceIte]; rfl
          · simp only [h_kosk, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
              StateT.run_monadLift,
              monadLift_self, pure_bind, bind_assoc, simulateQ_bind, simulateQ_embedUnif]
            congr 1; ext ekASk
            congr 1; ext kemCoins
            congr 1; ext ephASk
            congr 1; ext spqrCoins
            rw [simulateQ_resolveSigPkPrim S P st.principals bundle.ikB hPrin, pure_bind,
                simulateQ_primQ_sigVerify, pure_bind, simulateQ_primQ_sigVerify, pure_bind]
            by_cases h_sig : (!(P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeEC
              bundle.spkB) bundle.spkSig &&
                P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                  bundle.pqspkSig)) = true
            · simp only [h_sig, ↓reduceIte]; rfl
            · simp only [h_sig, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                StateT.run_monadLift, monadLift_self,
                pure_bind, bind_assoc, simulateQ_bind]
              rw [simulateQ_primQ_kemEncaps, pure_bind]
              cases P.kemEncaps bundle.pqspkB kemCoins with
              | none => rfl
              | some sc =>
                rcases sc with ⟨ss, kemCt⟩
                dsimp only
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
                  bind_assoc,
                  simulateQ_bind]
                rw [simulateQ_primQ_x25519Base, pure_bind,
                    simulateQ_primQ_x25519, pure_bind,
                    simulateQ_primQ_x25519, pure_bind,
                    simulateQ_primQ_x25519, pure_bind,
                    simulateQ_primQ_x25519, pure_bind]
                have h_dh4 : (bundle.opkB?.map (fun _ => P.x25519 ekASk (bundle.opkB?.map Prod.snd
                    |>.getD []))) =
                    bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk) := by
                  cases bundle.opkB? <;> rfl
                rw [h_dh4, simulateQ_evalHkdfOrRoPrim]
                congr 1; ext ⟨drKey, roCache'⟩
                rw [simulateQ_primQ_x25519Base, pure_bind,
                    simulateQ_primQ_x25519, pure_bind,
                    simulateQ_evalRootKdfOrRoPrim]
                congr 1; ext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                rw [simulateQ_primQ_chainKdfSeed, pure_bind,
                    simulateQ_primQ_chainKdfNext, pure_bind,
                    simulateQ_primQ_spqrInitSend, pure_bind]
                cases P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => rfl
                | some spqr =>
                  rcases spqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                  dsimp only
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                    pure_bind, bind_assoc, simulateQ_bind]
                  rw [simulateQ_primQ_deriveMsgKeys, pure_bind,
                      simulateQ_primQ_aeadEnc, pure_bind]
                  cases findHonestPrincipal P st.principals bundle.ikB with
                  | none => split_ifs <;> rfl
                  | some p => rcases p with ⟨_, _⟩; split_ifs <;> rfl

theorem simulateQ_pqxdhAuthSimImplPrim (S : Setup) (P : Primitives)
    (q : AuthQuery S) (st : AuthState S)
    (hPrin : st.principals.length ≤ S.N_dh)
    (hSpk : st.spkBundles.length ≤ S.N_dh)
    (hOpk : st.opkEntries.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P st.advKeys) :
    simulateQ (primBaseImpl P) ((pqxdhAuthSimImplPrim S q).run st) =
      (pqxdhAuthSimImpl S P q).run st := by
  unfold pqxdhAuthSimImplPrim runAuthRecvOPKSimPrim runAuthRecvNoOPKSimPrim runAuthRecvFinishSimPrim
    runAuthRecvStep2SimPrim pqxdhAuthSimImpl pqxdhAuthImpl
  cases q with
  | initPrin u =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
        simulateQ_embedUnif]
      congr 1
  | corruptIK u =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.find? (fun (idx, _) => idx == u.val) <;> rfl
  | genSPK u j =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => rfl
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
          simulateQ_embedUnif, simulateQ_sampleKemKeyGenPrim]
        congr 1
  | genOPK u j o =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
        simulateQ_embedUnif]
      congr 1
  | sendOPK u i bundle m0 m1 =>
    dsimp only
    split_ifs
    · rfl
    · exact simulateQ_runAuthSendSimPrim S P (.sendOPK u i) u bundle m0 m1 st hPrin hSpk hOpk hAdv
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only
    split_ifs
    · rfl
    · exact simulateQ_runAuthSendSimPrim S P (.sendNoOPK u i) u bundle m0 m1 st hPrin hSpk hOpk hAdv
  | recvOPK k j o msg =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32)) = true
    · simp only [h1, ↓reduceIte]; rfl
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : st.usedRecvOPK.contains (k.val, j.val, o.val) = true
    · simp only [h2, ↓reduceIte]; rfl
    simp only [h2, Bool.false_eq_true, ↓reduceIte]
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
      simulateQ_bind]
    rw [simulateQ_koskSenderOkPrim S P st.principals st.advKeys msg.hdr.ikAPk hPrin hAdv, pure_bind]
    by_cases h3 : (!koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk) = true
    · simp only [h3, ↓reduceIte]; rfl
    simp only [h3, Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == k.val) with
    | none => rfl
    | some kp =>
      rcases kp with ⟨_, kEntry⟩; dsimp only
      cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => rfl
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only
        cases st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => rfl
        | some op =>
          rcases op with ⟨_, oEntry⟩; dsimp only
          by_cases h4 : oEntry.consumed = true
          · simp only [h4, ↓reduceIte]; rfl
          simp only [h4, Bool.false_eq_true, ↓reduceIte]
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
            simulateQ_bind]
          rw [simulateQ_primQ_isCanonical, pure_bind, simulateQ_primQ_isCanonical, pure_bind]
          by_cases h5 : (!(checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId
            msg.hdr.spkId msg.hdr.ekAPk).1 || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical
            msg.ephAPk) = true
          · simp only [h5, ↓reduceIte]; rfl
          simp only [h5, Bool.false_eq_true, ↓reduceIte]
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
            simulateQ_bind]
          rw [simulateQ_primQ_kemDecaps, pure_bind]
          cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none => rfl
          | some ss =>
            dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
              simulateQ_bind]
            rw [simulateQ_primQ_x25519, pure_bind,
                simulateQ_primQ_x25519, pure_bind,
                simulateQ_primQ_x25519, pure_bind,
                simulateQ_primQ_x25519, pure_bind,
                simulateQ_evalHkdfOrRoPrim]
            congr 1; ext ⟨drKey, roCache'⟩
            rw [simulateQ_primQ_x25519, pure_bind,
                simulateQ_evalRootKdfOrRoPrim]
            congr 1; ext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
            rw [simulateQ_primQ_chainKdfSeed, pure_bind,
                simulateQ_primQ_chainKdfNext, pure_bind,
                simulateQ_primQ_spqrInitRecv, pure_bind]
            cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
            | none => rfl
            | some spqr =>
              rcases spqr with ⟨_, spqrSalt?⟩; dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
                bind_assoc,
                simulateQ_bind]
              rw [simulateQ_primQ_deriveMsgKeys, pure_bind,
                  simulateQ_primQ_aeadDec, pure_bind]
              cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
              | none => rfl
              | some pt =>
                dsimp only
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                  pure_bind, bind_assoc, simulateQ_bind]
                rw [simulateQ_findHonestPrincipalPrim S P st.principals msg.hdr.ikAPk hPrin,
                  pure_bind]
                cases findHonestPrincipal P st.principals msg.hdr.ikAPk <;> rfl
  | recvNoOPK k j l msg =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == none &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32)) = true
    · simp only [h1, ↓reduceIte]; rfl
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : st.usedRecvNoOPK.contains (k.val, j.val, l.val) = true
    · simp only [h2, ↓reduceIte]; rfl
    simp only [h2, Bool.false_eq_true, ↓reduceIte]
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
      simulateQ_bind]
    rw [simulateQ_koskSenderOkPrim S P st.principals st.advKeys msg.hdr.ikAPk hPrin hAdv, pure_bind]
    by_cases h3 : (!koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk) = true
    · simp only [h3, ↓reduceIte]; rfl
    simp only [h3, Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == k.val) with
    | none => rfl
    | some kp =>
      rcases kp with ⟨_, kEntry⟩; dsimp only
      cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => rfl
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
          simulateQ_bind]
        rw [simulateQ_primQ_isCanonical, pure_bind, simulateQ_primQ_isCanonical, pure_bind]
        by_cases h5 : (!(checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId
          msg.hdr.spkId msg.hdr.ekAPk).1 || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical
          msg.ephAPk) = true
        · simp only [h5, ↓reduceIte]; rfl
        simp only [h5, Bool.false_eq_true, ↓reduceIte]
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
          simulateQ_bind]
        rw [simulateQ_primQ_kemDecaps, pure_bind]
        cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => rfl
        | some ss =>
          dsimp only
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
            simulateQ_bind]
          rw [simulateQ_primQ_x25519, pure_bind,
              simulateQ_primQ_x25519, pure_bind,
              simulateQ_primQ_x25519, pure_bind,
              simulateQ_evalHkdfOrRoPrim]
          congr 1; ext ⟨drKey, roCache'⟩
          rw [simulateQ_primQ_x25519, pure_bind,
              simulateQ_evalRootKdfOrRoPrim]
          congr 1; ext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
          rw [simulateQ_primQ_chainKdfSeed, pure_bind,
              simulateQ_primQ_chainKdfNext, pure_bind,
              simulateQ_primQ_spqrInitRecv, pure_bind]
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none => rfl
          | some spqr =>
            rcases spqr with ⟨_, spqrSalt?⟩; dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
              simulateQ_bind]
            rw [simulateQ_primQ_deriveMsgKeys, pure_bind,
                simulateQ_primQ_aeadDec, pure_bind]
            cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
              (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
            | none => rfl
            | some pt =>
              dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                pure_bind, bind_assoc, simulateQ_bind]
              rw [simulateQ_findHonestPrincipalPrim S P st.principals msg.hdr.ikAPk hPrin,
                pure_bind]
              cases findHonestPrincipal P st.principals msg.hdr.ikAPk <;> rfl
  | roQuery secrets =>
    simp only [ Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, pure_bind, bind_assoc, simulateQ_bind, simulateQ_evalHkdfOrRoPrim]
    rfl
  | roRootQuery rk dh =>
    simp only [ Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, pure_bind, bind_assoc, simulateQ_bind, simulateQ_evalRootKdfOrRoPrim]
    rfl
  | revealDhSecrets =>
    rfl
  | registerKey sk =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        pure_bind, bind_assoc, simulateQ_bind]
      rw [simulateQ_primQ_x25519Base, pure_bind, simulateQ_primQ_pow8, pure_bind]
      rfl

end Proofs.SignalPqxdh.Security

end

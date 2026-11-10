/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptRecordStorePeak
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import LibsignalBinary.Specifications.AsmConstants

/-!
# Ghost-Free `SessionClone`, `SessionRecord::serialize`, and `StorePoll` Bounds

Extracts pure canonical and length invariants (`GhostCloneValid`, `CanonSession`) from
`SessionGhostValid G ses` and `SessionCloneDom pqCap ses`, deriving ghost-free `PhaseCreditSpec` and
`PhaseGroupSpec` bounds for `SegCloneEnv`, `RecordSerializeCancelEnv`, `CliSessStorePollEnv`, and
`RecordDecryptEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (IdentityKey MessageKeyGenerator PublicKey ReceiverChain SenderChain SessionState
   djbType maxMessageKeys maxReceiverChains)
open CryptoGames.LibsignalSessionApi
  (PendingKyberPreKey PendingPreKey Session SessionRecord)
open CryptoVerification.E2E.Record (encSession encodeRecord lenField msgField)
open CryptoVerification.E2E.Record.Serialization
  (CanonChain CanonPending CanonRecord CanonSender CanonSession
   encRecordMem encRecordMem_eq_of_canon encSessionMem encSessionMem_eq_of_canon)
open CryptoVerification.E2E.RecordX (SessionScopeP)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (sessionModelRel)
open CryptoVerification.LibsignalPublicApiRepr
  (KyberRel PendingRel RecordGhost sessionRecordAt sessionStateReprAt)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchet (RecordDecryptGhost SeedsLen32)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SenderChainGhost SessionGhost TailVecGhost optSenderChainAt sessionStateAt)
open CryptoVerification.RustHeap (RustAlloc arrayAt vecAt vecBuf)
open CryptoVerification.SignalSession.Cli (DirGhost)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessStorePollEnv serialize_phaseCredit sessStorePollDeltaCum sessStorePollDeltaLive
   sessStorePollDeltaPeak sessStorePollMaxReq sessStorePoll_phaseCredit
   sessionClone_drop_cancel_phaseCredit sessionClone_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (chainCloneCum chainCloneLarge chainCloneMaxReq dropClonedSessionEvents optLargeCost
   optTailCloneLen segCloneCum segCloneLarge segCloneMaxReq vecCloneCum vecCloneLarge)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (RecordSerializeCancelEnv recordSerializeCum recordSerializeMaxReq recordSerializeOutLarge
   recordSerializePeak)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptRecordStorePeak (phaseCreditSpec_recordDecryptEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (senderChainAsProtoGhost)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (RecordDecryptEnv SegCloneEnv TryDecryptEnvArgs recordTryDecryptEnvArgs)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q)

/-! ## 1. List Helpers -/

private theorem snd_mem_of_mem_zip {α β : Type} :
    ∀ {xs : List α} {ys : List β} {p : α × β}, p ∈ xs.zip ys → p.2 ∈ ys
  | _ :: _, _ :: _, _, h => by
    rcases List.mem_cons.mp h with rfl | hrest
    · exact List.Mem.head _
    · exact List.Mem.tail _ (snd_mem_of_mem_zip hrest)

private theorem zip_length_le_right {α β : Type} :
    ∀ (xs : List α) (ys : List β), (xs.zip ys).length ≤ ys.length
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.le_refl 0
  | _ :: xs, _ :: ys => Nat.succ_le_succ (zip_length_le_right xs ys)

private theorem map_sum_le {α : Type} (f : α → Nat) (k : Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, f x ≤ k) → (xs.map f).sum ≤ xs.length * k
  | [], _ => by simp
  | x :: xs, h => by
    have hx : f x ≤ k := h x (List.Mem.head _)
    have hxs : (xs.map f).sum ≤ xs.length * k :=
      map_sum_le f k xs (fun y hy => h y (List.Mem.tail _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

private theorem map_sum_eq_zero {α : Type} (f : α → Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = 0) → (xs.map f).sum = 0
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, List.sum_cons, h x (List.Mem.head _),
      map_sum_eq_zero f xs (fun y hy => h y (List.Mem.tail _ hy)), Nat.add_zero]

private theorem map_foldr_max_le {α : Type} (f : α → Nat) (k : Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, f x ≤ k) → (xs.map f).foldr max 0 ≤ k
  | [], _ => Nat.zero_le k
  | x :: xs, h => by
    have hx : f x ≤ k := h x (List.Mem.head _)
    have hxs : (xs.map f).foldr max 0 ≤ k :=
      map_foldr_max_le f k xs (fun y hy => h y (List.Mem.tail _ hy))
    simp only [List.map_cons, List.foldr_cons]
    omega

/-! ## 2. Domain and Ghost Validity Predicates -/

/-- Pure session-domain bounds constraining model-determined sizes during `SessionClone` and
`SessionRecord::serialize`. -/
structure SessionCloneDom (pqCap : Nat) (ses : Session (List (BitVec 8))) : Prop where
  rc_len : ses.state.receiverChains.length ≤ 5
  seeds32 : SeedsLen32 ses.state
  alice_len : ses.aliceBaseKey.length ≤ 33
  kyber_cap : ∀ k, ses.pendingKyberPreKey = some k → k.ciphertext.length ≤ 1569
  pq_len : ses.state.pqRatchetState.length ≤ pqCap

/-- Pure ghost-to-model shape invariants implied by `SessionGhostValid G ses`. -/
structure GhostCloneValid (G : SessionGhost) (ses : Session (List (BitVec 8))) : Prop where
  localIk_len : G.localIk.bytes.length = 33
  remoteIk_len : G.remoteIk.bytes.length ≤ 33
  chains_len : G.chains.length = ses.state.receiverChains.length
  chains_ok : ∀ gc ∈ G.chains.zip ses.state.receiverChains,
    gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes.length = 0 ∧
    gc.2.messageKeys.length ≤ 2000
  sender_ok : (G.sender = none ∧ ses.state.senderChain = none) ∨
    ∃ gs sc, G.sender = some gs ∧ ses.state.senderChain = some sc ∧
      gs.srk.bytes.length = 33 ∧ gs.priv.bytes.length = 32
  pending_len : optTailCloneLen G.pending ≤ 33
  kyber_len : optTailCloneLen G.kyber =
    (ses.pendingKyberPreKey.map (·.ciphertext.length)).getD 0
  alice_eq : G.alice.bytes = ses.aliceBaseKey
  canon : CanonSession G ses

/-- Record-level ghost validity (`none/none` or `some G / some ses` satisfying `SessionGhostValid`). -/
def RecordGhostValid (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Prop :=
  match g.cur, r.currentSession with
  | none, none => True
  | some G, some ses => SessionGhostValid G ses
  | _, _ => False

theorem SessionCloneDom.mono {pq₁ pq₂ : Nat} {ses : Session (List (BitVec 8))}
    (h : SessionCloneDom pq₁ ses) (hle : pq₁ ≤ pq₂) : SessionCloneDom pq₂ ses :=
  ⟨h.rc_len, h.seeds32, h.alice_len, h.kyber_cap, Nat.le_trans h.pq_len hle⟩

theorem sessionCloneDom_of_deserializeScopeP_Q {Q : List (BitVec 8) → Prop} {pqCap : Nat}
    {rec : SessionRecord (List (BitVec 8))} {ses : Session (List (BitVec 8))}
    (hSc : DeserializeScopeP_Q Q rec)
    (hCur : rec.currentSession = some ses)
    (hPq : ∀ st, Q st → st.length ≤ pqCap) :
    SessionCloneDom pqCap ses := by
  obtain ⟨⟨hInP, hRecQ, _⟩, ses', hCur', hSessP⟩ := hSc
  have hEq : ses' = ses := by
    rw [hCur] at hCur'
    injection hCur' with hEq
    exact hEq.symm
  subst hEq
  obtain ⟨hSeeds, _, _⟩ := hInP ses' hCur
  obtain ⟨hRc, _, hKyb, hAbk⟩ := hSessP
  have hRc5 : ses'.state.receiverChains.length ≤ 5 := by
    simpa [maxReceiverChains] using hRc
  have hAbk33 : ses'.aliceBaseKey.length ≤ 33 := by
    rcases hAbk with h0 | h33
    · rw [h0]; decide
    · omega
  refine ⟨hRc5, hSeeds, hAbk33, ?_, hPq ses'.state.pqRatchetState (hRecQ ses' hCur)⟩
  intro k hk
  have hkEq := hKyb k hk
  omega

theorem sessionCloneDom_of_scopeKit_pq {pqCap : Nat}
    {rec : SessionRecord (List (BitVec 8))} {ses : Session (List (BitVec 8))}
    (hKit : scopeKit rec)
    (hCur : rec.currentSession = some ses)
    (hPq : ses.state.pqRatchetState.length ≤ pqCap) :
    SessionCloneDom pqCap ses := by
  have h4G : SessionCloneDom (2 ^ 32 - 1) ses :=
    sessionCloneDom_of_deserializeScopeP_Q hKit hCur (fun _ hlt => by omega)
  exact ⟨h4G.rc_len, h4G.seeds32, h4G.alice_len, h4G.kyber_cap, hPq⟩

theorem sessionCloneDom_of_scopeIn
    {rec : SessionRecord (List (BitVec 8))} {ses : Session (List (BitVec 8))}
    (hIn : scopeIn rec) (hCur : rec.currentSession = some ses) :
    SessionCloneDom (2 ^ 31 - 1) ses :=
  sessionCloneDom_of_deserializeScopeP_Q hIn hCur (fun _ hpq => by have := hpq.2; omega)

theorem sessionCloneDom_of_scopeKit
    {rec : SessionRecord (List (BitVec 8))} {ses : Session (List (BitVec 8))}
    (hKit : scopeKit rec) (hCur : rec.currentSession = some ses) :
    SessionCloneDom (2 ^ 32 - 1) ses :=
  sessionCloneDom_of_deserializeScopeP_Q hKit hCur (fun _ hpq => by omega)

/-! ## 3. Extracting `GhostCloneValid` and `CanonSession` -/

private theorem publicKey_eq_serialize_of_deserialize_len33 {bs : List (BitVec 8)} {pk : PublicKey}
    (hd : PublicKey.deserialize bs = .ok pk) (hl : bs.length = 33) :
    bs = pk.serialize := by
  cases bs with
  | nil => simp [PublicKey.deserialize] at hd
  | cons t rest =>
    have hrest : rest.length = 32 := by simpa using hl
    unfold PublicKey.deserialize at hd
    by_cases ht : t ≠ djbType
    · simp [ht] at hd
    · have ht_eq : t = djbType := Decidable.of_not_not ht
      subst ht_eq
      have hge : 32 ≤ rest.length := by omega
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, hge, ↓reduceDIte, Except.ok.injEq] at hd
      rw [← hd]
      dsimp only [PublicKey.serialize]
      congr 1
      exact (List.take_of_length_le (Nat.le_of_eq hrest)).symm

private theorem chainProps_of_satisfies_chainAt {A : RustAlloc} {gc : ChainGhost × ReceiverChain}
    {a : BitVec 64} {m : Memory} (hm : m ⊨ chainAt A gc a) :
    CanonChain gc ∧ gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes.length = 0 ∧
      gc.2.messageKeys.length ≤ 2000 := by
  unfold chainAt at hm
  have hpure := Satisfies.of_sep_left hm
  rw [satisfies_pure] at hpure
  obtain ⟨hd, hmk, _, hl, hpriv⟩ := hpure
  have hmk2000 : gc.2.messageKeys.length ≤ 2000 := by simpa [maxMessageKeys] using hmk
  have hpriv0 : gc.1.priv.bytes.length = 0 := by rw [hpriv]; rfl
  exact ⟨⟨publicKey_eq_serialize_of_deserialize_len33 hd hl, hpriv⟩, hl, hpriv0, hmk2000⟩

private theorem chainsProps_of_satisfies_arrayAt {A : RustAlloc} :
    ∀ (xs : List (ChainGhost × ReceiverChain)) (ptr : BitVec 64) (m : Memory),
      m ⊨ arrayAt (chainAt A) (asm% chainSize) ptr xs →
      ∀ gc ∈ xs, CanonChain gc ∧ gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes.length = 0 ∧
        gc.2.messageKeys.length ≤ 2000
  | [], _, _, _, _, hmem => by simp at hmem
  | gc :: rest, ptr, m, hm, gc', hmem => by
    unfold arrayAt at hm
    rcases List.mem_cons.mp hmem with rfl | hrest
    · exact chainProps_of_satisfies_chainAt (Satisfies.of_sep_left hm)
    · exact chainsProps_of_satisfies_arrayAt rest _ _ (Satisfies.of_sep_right hm) gc' hrest

private theorem chainsProps_of_satisfies_vecAt {A : RustAlloc}
    {v cap ptr : BitVec 64} {xs : List (ChainGhost × ReceiverChain)} {m : Memory}
    (hm : m ⊨ vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A) v cap ptr xs) :
    ∀ gc ∈ xs, CanonChain gc ∧ gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes.length = 0 ∧
      gc.2.messageKeys.length ≤ 2000 := by
  unfold vecAt vecBuf at hm
  have hbuf := Satisfies.of_sep_right hm
  have hpure := Satisfies.of_sep_left hbuf
  rw [satisfies_pure] at hpure
  have hbody := Satisfies.of_sep_right hbuf
  by_cases hc : cap = 0
  · have hlen0 : xs.length ≤ 0 := by simpa [hc] using hpure.1
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen0)
    subst hnil
    intro _ hmem; simp at hmem
  · simp only [hc, ↓reduceIte] at hbody
    have harr := Satisfies.of_sep_left (Satisfies.of_sep_right hbody)
    exact chainsProps_of_satisfies_arrayAt xs ptr _ harr

private theorem senderProps_of_satisfies_optSenderChainAt {A : RustAlloc} {a : BitVec 64}
    {og : Option SenderChainGhost} {os : Option SenderChain} {m : Memory}
    (hm : m ⊨ optSenderChainAt A a og os) :
    CanonSender og os ∧
      ((og = none ∧ os = none) ∨
        ∃ gs sc, og = some gs ∧ os = some sc ∧
          gs.srk.bytes.length = 33 ∧ gs.priv.bytes.length = 32) := by
  match og, os with
  | none, none => exact ⟨trivial, Or.inl ⟨rfl, rfl⟩⟩
  | some gs, some sc =>
    unfold optSenderChainAt at hm
    have hpure := Satisfies.of_sep_left hm
    rw [satisfies_pure] at hpure
    obtain ⟨hd, hpriv, _, hl⟩ := hpure
    have hpriv_len : gs.priv.bytes.length = 32 := by
      rw [hpriv]
      exact sc.ratchetKey.privateKey.bytes.toList_length
    exact ⟨⟨publicKey_eq_serialize_of_deserialize_len33 hd hl, hpriv⟩,
      Or.inr ⟨gs, sc, rfl, rfl, hl, hpriv_len⟩⟩
  | none, some _ =>
    unfold optSenderChainAt at hm
    rw [satisfies_pure] at hm
    exact False.elim hm
  | some _, none =>
    unfold optSenderChainAt at hm
    rw [satisfies_pure] at hm
    exact False.elim hm

private theorem pendingProps_of_pendingRel {og : Option TailVecGhost} {op : Option PendingPreKey}
    (h : PendingRel og op) : CanonPending og op ∧ optTailCloneLen og ≤ 33 := by
  match og, op with
  | none, none => exact ⟨trivial, by simp [optTailCloneLen]⟩
  | some g, some p =>
    obtain ⟨hd, _, _, _, hl⟩ := h
    exact ⟨publicKey_eq_serialize_of_deserialize_len33 hd hl,
      by simp [optTailCloneLen, hl]⟩
  | none, some _ => exact False.elim h
  | some _, none => exact False.elim h

private theorem kyberLen_of_kyberRel {og : Option TailVecGhost} {ok : Option PendingKyberPreKey}
    (h : KyberRel og ok) :
    optTailCloneLen og = (ok.map (·.ciphertext.length)).getD 0 := by
  match og, ok with
  | none, none => rfl
  | some g, some k =>
    obtain ⟨hbytes, _⟩ := h
    simp [optTailCloneLen, hbytes]
  | none, some _ => exact False.elim h
  | some _, none => exact False.elim h

theorem ghostCloneValid_of_sessionGhostValid {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (h : SessionGhostValid G ses) : GhostCloneValid G ses := by
  obtain ⟨⟨hpend, hkyb, halice, _, _⟩, A, ss, m, R, hm⟩ := h
  have hss := Satisfies.of_sep_left hm
  unfold sessionStateAt at hss
  have hp_ss := Satisfies.of_sep_left hss
  rw [satisfies_pure] at hp_ss
  obtain ⟨hloc_d, hrem_d, hch_len, _, _, hloc_l, hrem_l⟩ := hp_ss
  have hr1 := Satisfies.of_sep_right hss
  have hr2 := Satisfies.of_sep_right hr1
  have hr3 := Satisfies.of_sep_right hr2
  have hr4 := Satisfies.of_sep_right hr3
  have hchains_sat := Satisfies.of_sep_left hr4
  have hr5 := Satisfies.of_sep_right hr4
  have hr6 := Satisfies.of_sep_right hr5
  have hr7 := Satisfies.of_sep_right hr6
  have hsender_sat := Satisfies.of_sep_left hr7
  have hchains := chainsProps_of_satisfies_vecAt hchains_sat
  obtain ⟨hsender_can, hsender_ok⟩ := senderProps_of_satisfies_optSenderChainAt hsender_sat
  obtain ⟨hpend_can, hpend_len⟩ := pendingProps_of_pendingRel hpend
  have hkyb_len := kyberLen_of_kyberRel hkyb
  have hrem_props : G.remoteIk.bytes.length ≤ 33 ∧
      G.remoteIk.bytes = (ses.state.remoteIdentity.map IdentityKey.serialize).getD [] := by
    cases hri : ses.state.remoteIdentity with
    | none =>
      rw [hri] at hrem_d
      have hnil : G.remoteIk.bytes = [] := hrem_d
      rw [hnil]
      exact ⟨by decide, rfl⟩
    | some ik =>
      rw [hri] at hrem_d hrem_l
      have hl33 : G.remoteIk.bytes.length = 33 := hrem_l rfl
      exact ⟨by omega, publicKey_eq_serialize_of_deserialize_len33 hrem_d hl33⟩
  have hcanon : CanonSession G ses :=
    ⟨publicKey_eq_serialize_of_deserialize_len33 hloc_d hloc_l,
     hrem_props.2, hsender_can, hch_len,
     fun gc hmem => (hchains gc hmem).1, hpend_can⟩
  exact ⟨hloc_l, hrem_props.1, hch_len,
    fun gc hmem => (hchains gc hmem).2, hsender_ok,
    hpend_len, hkyb_len, halice, hcanon⟩

theorem canonSession_of_sessionGhostValid {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (h : SessionGhostValid G ses) : CanonSession G ses :=
  (ghostCloneValid_of_sessionGhostValid h).canon

theorem encSessionMem_eq_of_sessionGhostValid {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (h : SessionGhostValid G ses) : encSessionMem G ses = encSession ses :=
  encSessionMem_eq_of_canon G ses (canonSession_of_sessionGhostValid h)

theorem recordGhostValid_of_sessionRecordAt {A : RustAlloc} {rA : BitVec 64}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))} {m : Memory} {R : SepProp}
    (hm : m ⊨ sessionRecordAt A rA g r ∗ R) : RecordGhostValid g r := by
  have hrec := Satisfies.of_sep_left hm
  unfold sessionRecordAt at hrec
  have hcur := Satisfies.of_sep_right hrec
  rcases hg : g.cur with _ | G <;> rcases hr : r.currentSession with _ | ses
  · simp [RecordGhostValid, hg, hr]
  · simp [hg, hr, satisfies_pure] at hcur
  · simp [hg, hr, satisfies_pure] at hcur
  · simp only [hg, hr] at hcur
    unfold sessionStateReprAt at hcur
    have hp := Satisfies.of_sep_left hcur
    rw [satisfies_pure] at hp
    have hss := Satisfies.of_sep_right hcur
    have hss_frame : m ⊨ sessionStateAt A (rA + 0x18#64) G ses.state ∗ emp := by
      simpa using hss
    rw [RecordGhostValid, hg, hr]
    exact ⟨hp, A, rA + 0x18#64, m, emp, hss_frame⟩

theorem canonRecord_of_recordGhostValid {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (h : RecordGhostValid g r) : CanonRecord g r := by
  unfold RecordGhostValid at h
  unfold CanonRecord
  rcases hg : g.cur with _ | G <;> rcases hr : r.currentSession with _ | ses
  · trivial
  · simp [hg, hr] at h
  · simp [hg, hr] at h
  · simp only [hg, hr] at h
    exact canonSession_of_sessionGhostValid h

theorem encRecordMem_eq_of_recordGhostValid {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (h : RecordGhostValid g r) : encRecordMem g r = encodeRecord r :=
  encRecordMem_eq_of_canon g r (canonRecord_of_recordGhostValid h)

/-! ## 4. Arithmetic Bounds on `segClone*` and `recordSerialize*` -/

private theorem optLargeCost_eq_zero_of_le (M : AllocCostModel) [HasFineReallocCredit M]
    {req : Nat} (hle : req ≤ HasFineReallocCredit.smallMaxReq M) :
    optLargeCost M req = 0 := by
  unfold optLargeCost
  split_ifs
  rfl

private theorem optLargeCost_le_req_add {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (req : Nat) :
    optLargeCost M req ≤ req + 8195 := by
  unfold optLargeCost
  split_ifs with hle
  · omega
  · exact hM.largeCost_le (by omega)

private theorem vecCloneCum_le_of_le {len : Nat} (cap : Nat) (hle : len ≤ cap) :
    vecCloneCum len ≤ 2 * cap + 9539 := by
  unfold vecCloneCum
  split_ifs <;> omega

private theorem vecCloneLarge_eq_zero_of_le (M : AllocCostModel) [HasFineReallocCredit M]
    {len : Nat} (hle : len ≤ HasFineReallocCredit.smallMaxReq M) :
    vecCloneLarge M len = 0 := by
  unfold vecCloneLarge
  split_ifs
  · rfl
  · exact optLargeCost_eq_zero_of_le M hle

private theorem vecCloneLarge_le_cap_add {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {len : Nat} (cap : Nat) (hle : len ≤ cap) :
    vecCloneLarge M len ≤ cap + 8195 := by
  unfold vecCloneLarge
  split_ifs
  · omega
  · exact Nat.le_trans (optLargeCost_le_req_add hM len) (by omega)

private theorem chainCloneCum_sender_le {gs : SenderChainGhost} (sc : SenderChain)
    (hsrk : gs.srk.bytes.length = 33) (hpriv : gs.priv.bytes.length = 32) :
    chainCloneCum (senderChainAsProtoGhost gs sc) ≤ 28811 := by
  simp [chainCloneCum, senderChainAsProtoGhost, vecCloneCum, hsrk, hpriv]

private theorem chainCloneLarge_sender_eq_zero {M : AllocCostModel} [HasFineReallocCredit M]
    (hsmall : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    {gs : SenderChainGhost} (sc : SenderChain)
    (hsrk : gs.srk.bytes.length = 33) (hpriv : gs.priv.bytes.length = 32) :
    chainCloneLarge M (senderChainAsProtoGhost gs sc) = 0 := by
  unfold chainCloneLarge senderChainAsProtoGhost
  dsimp only
  rw [vecCloneLarge_eq_zero_of_le M (by omega),
    vecCloneLarge_eq_zero_of_le M (by omega),
    optLargeCost_eq_zero_of_le M (by omega)]
  simp

private theorem chainCloneMaxReq_sender_le {gs : SenderChainGhost} (sc : SenderChain)
    (hsrk : gs.srk.bytes.length = 33) (hpriv : gs.priv.bytes.length = 32) :
    chainCloneMaxReq (senderChainAsProtoGhost gs sc) ≤ 33 := by
  unfold chainCloneMaxReq senderChainAsProtoGhost
  simp only [hsrk, hpriv, List.map_nil, List.foldr_nil, List.length_nil]
  omega

private theorem chainCloneCum_recv_le {gc : ChainGhost × ReceiverChain}
    (hsrk : gc.1.srk.bytes.length = 33) (hpriv : gc.1.priv.bytes.length = 0)
    (hmk : gc.2.messageKeys.length ≤ 2000)
    (hseeds : ∀ k ∈ gc.2.messageKeys, k.seed.length = 32) :
    chainCloneCum gc ≤ 19650747 := by
  unfold chainCloneCum
  have h1 : vecCloneCum gc.1.srk.bytes.length = 9605 := by simp [vecCloneCum, hsrk]
  have h2 : vecCloneCum gc.1.priv.bytes.length = 0 := by simp [vecCloneCum, hpriv]
  have h4 : (if gc.2.messageKeys = [] then 0
      else (2 * (104 * gc.2.messageKeys.length) + 9539) +
        (gc.2.messageKeys.map fun mkg => 2 * mkg.seed.length + 9539).sum) ≤ 19631539 := by
    split_ifs with hnil
    · omega
    · have hsum : (gc.2.messageKeys.map fun mkg => 2 * mkg.seed.length + 9539).sum ≤
          gc.2.messageKeys.length * 9603 :=
        map_sum_le (fun mkg => 2 * mkg.seed.length + 9539) 9603 gc.2.messageKeys
          (fun mkg hm => by rw [hseeds mkg hm])
      omega
  refine Nat.le_trans
    (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.le_of_eq h1) (Nat.le_of_eq h2)) (?_ : _ ≤ 9603))
      h4)
    (by omega)
  cases gc.2.chainKey <;> dsimp only <;> decide

private theorem chainCloneLarge_recv_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    {gc : ChainGhost × ReceiverChain}
    (hsrk : gc.1.srk.bytes.length = 33) (hpriv : gc.1.priv.bytes.length = 0)
    (hmk : gc.2.messageKeys.length ≤ 2000)
    (hseeds : ∀ k ∈ gc.2.messageKeys, k.seed.length = 32) :
    chainCloneLarge M gc ≤ 216195 := by
  unfold chainCloneLarge
  have h1 : vecCloneLarge M gc.1.srk.bytes.length = 0 :=
    vecCloneLarge_eq_zero_of_le M (by omega)
  have h2 : vecCloneLarge M gc.1.priv.bytes.length = 0 :=
    vecCloneLarge_eq_zero_of_le M (by omega)
  have h4 : (if gc.2.messageKeys = [] then 0
      else optLargeCost M (104 * gc.2.messageKeys.length) +
        (gc.2.messageKeys.map fun mkg => optLargeCost M mkg.seed.length).sum) ≤ 216195 := by
    split_ifs with hnil
    · omega
    · have hbuf : optLargeCost M (104 * gc.2.messageKeys.length) ≤ 216195 :=
        Nat.le_trans (optLargeCost_le_req_add hM (104 * gc.2.messageKeys.length)) (by omega)
      have hseeds0 : (gc.2.messageKeys.map fun mkg => optLargeCost M mkg.seed.length).sum = 0 :=
        map_sum_eq_zero (fun mkg => optLargeCost M mkg.seed.length) gc.2.messageKeys
          (fun mkg hm => by
            rw [hseeds mkg hm]
            exact optLargeCost_eq_zero_of_le M (by omega))
      omega
  refine Nat.le_trans
    (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.le_of_eq h1) (Nat.le_of_eq h2)) (?_ : _ ≤ 0))
      h4)
    (by omega)
  cases gc.2.chainKey
  · dsimp only; exact Nat.le_refl 0
  · dsimp only; exact Nat.le_of_eq (optLargeCost_eq_zero_of_le M (by omega))

private theorem chainCloneMaxReq_recv_le {gc : ChainGhost × ReceiverChain}
    (hsrk : gc.1.srk.bytes.length = 33) (hpriv : gc.1.priv.bytes.length = 0)
    (hmk : gc.2.messageKeys.length ≤ 2000)
    (hseeds : ∀ k ∈ gc.2.messageKeys, k.seed.length = 32) :
    chainCloneMaxReq gc ≤ 208000 := by
  unfold chainCloneMaxReq
  have hfold : (gc.2.messageKeys.map fun mkg => mkg.seed.length).foldr max 0 ≤ 32 :=
    map_foldr_max_le (fun mkg => mkg.seed.length) 32 gc.2.messageKeys
      (fun mkg hm => by rw [hseeds mkg hm])
  omega

theorem segCloneCum_le_of_dom {pqCap : Nat} {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    segCloneCum G ses.state ≤ 98363364 + 2 * pqCap := by
  obtain ⟨hloc_len, hrem_len, _, hch_ok, hsend_ok, hpend_len, hkyb_len, halice_eq, _⟩ :=
    ghostCloneValid_of_sessionGhostValid hgv
  obtain ⟨hrc_len, hseeds, halice_dom, hkyb_cap, hpq_len⟩ := hdom
  unfold segCloneCum
  have hloc : vecCloneCum G.localIk.bytes.length ≤ 9605 :=
    vecCloneCum_le_of_le 33 (by omega)
  have hrem : vecCloneCum G.remoteIk.bytes.length ≤ 9605 :=
    vecCloneCum_le_of_le 33 hrem_len
  have hrc : (if ses.state.receiverChains = [] then 0
      else (2 * (104 * ses.state.receiverChains.length) + 9539) +
        ((G.chains.zip ses.state.receiverChains).map chainCloneCum).sum) ≤ 98264314 := by
    split_ifs with hnil
    · omega
    · have hzip_len : (G.chains.zip ses.state.receiverChains).length ≤ 5 :=
        Nat.le_trans (zip_length_le_right _ _) hrc_len
      have hsum : ((G.chains.zip ses.state.receiverChains).map chainCloneCum).sum ≤
          (G.chains.zip ses.state.receiverChains).length * 19650747 :=
        map_sum_le chainCloneCum 19650747 (G.chains.zip ses.state.receiverChains)
          (fun gc hmem => by
            obtain ⟨hsrk, hpriv, hmk⟩ := hch_ok gc hmem
            exact chainCloneCum_recv_le hsrk hpriv hmk
              (hseeds gc.2 (snd_mem_of_mem_zip hmem)))
      omega
  have hpend : vecCloneCum (optTailCloneLen G.pending) ≤ 9605 :=
    vecCloneCum_le_of_le 33 hpend_len
  have hkyb_le : optTailCloneLen G.kyber ≤ 1569 := by
    rw [hkyb_len]
    cases hk : ses.pendingKyberPreKey with
    | none => simp
    | some k => exact hkyb_cap k hk
  have hkyb : vecCloneCum (optTailCloneLen G.kyber) ≤ 12677 :=
    vecCloneCum_le_of_le 1569 hkyb_le
  have halice : vecCloneCum G.alice.bytes.length ≤ 9605 := by
    rw [halice_eq]
    exact vecCloneCum_le_of_le 33 halice_dom
  have hpq : vecCloneCum ses.state.pqRatchetState.length ≤ 2 * pqCap + 9539 :=
    vecCloneCum_le_of_le pqCap hpq_len
  refine Nat.le_trans
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add
                  (Nat.add_le_add hloc hrem)
                  (show 2 * 32 + 9539 ≤ 9603 by decide))
                (?_ : _ ≤ 28811))
              hrc)
            hpend)
          hkyb)
        halice)
      hpq)
    (by omega)
  rcases hsend_ok with ⟨h1, h2⟩ | ⟨gs, sc, h1, h2, hsrk, hpriv⟩
  · rw [h1, h2]; dsimp only; exact Nat.zero_le 28811
  · rw [h1, h2]; dsimp only; exact chainCloneCum_sender_le sc hsrk hpriv

theorem segCloneLarge_le_of_dom {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    {pqCap : Nat} {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    segCloneLarge M G ses.state ≤ 1089170 + pqCap := by
  obtain ⟨hloc_len, hrem_len, _, hch_ok, hsend_ok, hpend_len, hkyb_len, halice_eq, _⟩ :=
    ghostCloneValid_of_sessionGhostValid hgv
  obtain ⟨hrc_len, hseeds, halice_dom, hkyb_cap, hpq_len⟩ := hdom
  unfold segCloneLarge
  have hloc : vecCloneLarge M G.localIk.bytes.length = 0 :=
    vecCloneLarge_eq_zero_of_le M (by omega)
  have hrem : vecCloneLarge M G.remoteIk.bytes.length = 0 :=
    vecCloneLarge_eq_zero_of_le M (by omega)
  have hroot : optLargeCost M 32 = 0 :=
    optLargeCost_eq_zero_of_le M (by omega)
  have hrc : (if ses.state.receiverChains = [] then 0
      else optLargeCost M (104 * ses.state.receiverChains.length) +
        ((G.chains.zip ses.state.receiverChains).map (chainCloneLarge M)).sum) ≤ 1080975 := by
    split_ifs with hnil
    · omega
    · have houter : optLargeCost M (104 * ses.state.receiverChains.length) = 0 :=
        optLargeCost_eq_zero_of_le M (by omega)
      have hzip_len : (G.chains.zip ses.state.receiverChains).length ≤ 5 :=
        Nat.le_trans (zip_length_le_right _ _) hrc_len
      have hsum : ((G.chains.zip ses.state.receiverChains).map (chainCloneLarge M)).sum ≤
          (G.chains.zip ses.state.receiverChains).length * 216195 :=
        map_sum_le (chainCloneLarge M) 216195 (G.chains.zip ses.state.receiverChains)
          (fun gc hmem => by
            obtain ⟨hsrk, hpriv, hmk⟩ := hch_ok gc hmem
            exact chainCloneLarge_recv_le hM (by omega) hsrk hpriv hmk
              (hseeds gc.2 (snd_mem_of_mem_zip hmem)))
      omega
  have hpend : vecCloneLarge M (optTailCloneLen G.pending) = 0 :=
    vecCloneLarge_eq_zero_of_le M (by omega)
  have hkyb_le : optTailCloneLen G.kyber ≤ 1569 := by
    rw [hkyb_len]
    cases hk : ses.pendingKyberPreKey with
    | none => simp
    | some k => exact hkyb_cap k hk
  have hkyb : vecCloneLarge M (optTailCloneLen G.kyber) = 0 :=
    vecCloneLarge_eq_zero_of_le M (by omega)
  have halice_le : G.alice.bytes.length ≤ 33 := by
    rw [halice_eq]; exact halice_dom
  have halice : vecCloneLarge M G.alice.bytes.length = 0 :=
    vecCloneLarge_eq_zero_of_le M (by omega)
  have hpq : vecCloneLarge M ses.state.pqRatchetState.length ≤ pqCap + 8195 :=
    vecCloneLarge_le_cap_add hM pqCap hpq_len
  have harith : 0 + 0 + 0 + 0 + 1080975 + 0 + 0 + 0 + (pqCap + 8195) ≤ 1089170 + pqCap := by
    clear * -
    omega
  refine Nat.le_trans
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add
                  (Nat.add_le_add (Nat.le_of_eq hloc) (Nat.le_of_eq hrem))
                  (Nat.le_of_eq hroot))
                (?_ : _ ≤ 0))
              hrc)
            (Nat.le_of_eq hpend))
          (Nat.le_of_eq hkyb))
        (Nat.le_of_eq halice))
      hpq)
    harith
  rcases hsend_ok with ⟨h1, h2⟩ | ⟨gs, sc, h1, h2, hsrk, hpriv⟩
  · rw [h1, h2]
  · rw [h1, h2]; dsimp only
    exact Nat.le_of_eq (chainCloneLarge_sender_eq_zero (by omega) sc hsrk hpriv)

theorem segCloneMaxReq_le_of_dom {pqCap : Nat} {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    segCloneMaxReq G ses.state ≤ max 208000 pqCap := by
  obtain ⟨hloc_len, hrem_len, _, hch_ok, hsend_ok, hpend_len, hkyb_len, halice_eq, _⟩ :=
    ghostCloneValid_of_sessionGhostValid hgv
  obtain ⟨hrc_len, hseeds, halice_dom, hkyb_cap, hpq_len⟩ := hdom
  unfold segCloneMaxReq
  dsimp only
  have hr1 : max (max G.localIk.bytes.length G.remoteIk.bytes.length) 32 ≤ max 208000 pqCap := by
    omega
  have hfold : (((G.chains.zip ses.state.receiverChains).map chainCloneMaxReq).foldr max 0) ≤
      208000 :=
    map_foldr_max_le chainCloneMaxReq 208000 (G.chains.zip ses.state.receiverChains)
      (fun gc hmem => by
        obtain ⟨hsrk, hpriv, hmk⟩ := hch_ok gc hmem
        exact chainCloneMaxReq_recv_le hsrk hpriv hmk
          (hseeds gc.2 (snd_mem_of_mem_zip hmem)))
  have hr3 : max (104 * ses.state.receiverChains.length)
      (((G.chains.zip ses.state.receiverChains).map chainCloneMaxReq).foldr max 0) ≤
      max 208000 pqCap := by
    omega
  have hkyb_le : optTailCloneLen G.kyber ≤ 1569 := by
    rw [hkyb_len]
    cases hk : ses.pendingKyberPreKey with
    | none => simp
    | some k => exact hkyb_cap k hk
  have halice_le : G.alice.bytes.length ≤ 33 := by
    rw [halice_eq]; exact halice_dom
  have hr4 : max (max (optTailCloneLen G.pending) (optTailCloneLen G.kyber))
      (max G.alice.bytes.length ses.state.pqRatchetState.length) ≤ max 208000 pqCap := by
    omega
  refine Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hr1, ?_⟩, hr3⟩, hr4⟩
  rcases hsend_ok with ⟨h1, h2⟩ | ⟨gs, sc, h1, h2, hsrk, hpriv⟩
  · rw [h1, h2]; dsimp only; omega
  · rw [h1, h2]; dsimp only
    exact Nat.le_trans (chainCloneMaxReq_sender_le sc hsrk hpriv) (by omega)

private theorem lenField1_encSessionMem_eq_encodeRecord
    {G : SessionGhost} {r : SessionRecord (List (BitVec 8))} {ses : Session (List (BitVec 8))}
    (hCur : r.currentSession = some ses) (hgv : SessionGhostValid G ses) :
    lenField 1 (encSessionMem G ses) = encodeRecord r := by
  rw [encSessionMem_eq_of_sessionGhostValid hgv]
  unfold encodeRecord msgField
  rw [hCur]
  rfl

theorem recordSerializeCum_le_of_dom {pqCap encCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    recordSerializeCum g r ≤ 98372903 + 2 * pqCap + 2 * encCap := by
  unfold recordSerializeCum
  split
  · next G ses hg hr =>
    obtain ⟨hgv, hdom⟩ := hValid G ses hg hr
    unfold SessionSerializeCredit.serializeSomeCum
    dsimp only
    rw [lenField1_encSessionMem_eq_encodeRecord hr hgv]
    have hcl := segCloneCum_le_of_dom hgv hdom
    omega
  · omega

theorem recordSerializeOutLarge_le_of_dom {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {pqCap encCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    recordSerializeOutLarge M g r ≤ encCap + 8195 := by
  unfold recordSerializeOutLarge
  split
  · next G ses hg hr =>
    obtain ⟨hgv, _⟩ := hValid G ses hg hr
    unfold SessionSerializeCredit.serializeSomeOutLarge
    rw [lenField1_encSessionMem_eq_encodeRecord hr hgv]
    exact Nat.le_trans (optLargeCost_le_req_add hM (encodeRecord r).length) (by omega)
  · omega

theorem recordSerializePeak_le_of_dom {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    {pqCap encCap : Nat} {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    recordSerializePeak M g r ≤ 1097365 + pqCap + encCap := by
  unfold recordSerializePeak
  split
  · next G ses hg hr =>
    obtain ⟨hgv, hdom⟩ := hValid G ses hg hr
    unfold SessionSerializeCredit.serializeSomePeak
    dsimp only
    rw [lenField1_encSessionMem_eq_encodeRecord hr hgv]
    have hcl := segCloneLarge_le_of_dom hM hsmall hgv hdom
    have hout := optLargeCost_le_req_add hM (encodeRecord r).length
    omega
  · omega

theorem recordSerializeMaxReq_le_of_dom {pqCap encCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    recordSerializeMaxReq g r ≤ max (max 208000 pqCap) encCap := by
  unfold recordSerializeMaxReq
  split
  · next G ses hg hr =>
    obtain ⟨hgv, hdom⟩ := hValid G ses hg hr
    unfold SessionSerializeCredit.serializeSomeMaxReq
    rw [lenField1_encSessionMem_eq_encodeRecord hr hgv]
    have hcl := segCloneMaxReq_le_of_dom hgv hdom
    omega
  · omega

/-! ## 5. Ghost-Free `PhaseCreditSpec M` Bridges -/

theorem sessionClone_dom_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    {pqCap : Nat} {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    PhaseCreditSpec M (SegCloneEnv G ses.state)
      (98363364 + 2 * pqCap)
      (1089170 + pqCap)
      (1089170 + pqCap)
      (max 208000 pqCap) :=
  (sessionClone_phaseCredit hM G ses.state).mono
    (segCloneCum_le_of_dom hgv hdom)
    (segCloneLarge_le_of_dom hM hsmall hgv hdom)
    (segCloneLarge_le_of_dom hM hsmall hgv hdom)
    (segCloneMaxReq_le_of_dom hgv hdom)

/-- Ghost-free `PhaseCreditSpec` for `SegCloneEnv` + `Body` + `dropClonedSessionEvents`. -/
theorem sessionClone_drop_cancel_dom_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    {pqCap : Nat} {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {Body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses)
    (hBody : PhaseCreditSpec M Body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (SegCloneEnv G ses.state) Body)
        (· = dropClonedSessionEvents G ses.state))
      (98363364 + 2 * pqCap + c_b)
      l_b
      (1089170 + pqCap + p_b)
      (max (max 208000 pqCap) r_b) := by
  have hcl_c := segCloneCum_le_of_dom hgv hdom
  have hcl_l := segCloneLarge_le_of_dom hM hsmall hgv hdom
  have hcl_r := segCloneMaxReq_le_of_dom hgv hdom
  exact (sessionClone_drop_cancel_phaseCredit hM G ses.state hBody).mono
    (by omega) (Nat.le_refl l_b) (by omega) (by omega)

theorem serialize_dom_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    {pqCap encCap : Nat} {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    PhaseCreditSpec M (RecordSerializeCancelEnv g r)
      (98372903 + 2 * pqCap + 2 * encCap)
      (encCap + 8195)
      (1097365 + pqCap + encCap)
      (max (max 208000 pqCap) encCap) :=
  (serialize_phaseCredit hM g r).mono
    (recordSerializeCum_le_of_dom hValid hEnc)
    (recordSerializeOutLarge_le_of_dom hM hValid hEnc)
    (recordSerializePeak_le_of_dom hM hsmall hValid hEnc)
    (recordSerializeMaxReq_le_of_dom hValid hEnc)

theorem sessStorePoll_dom_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    {dir : DirGhost} {peer : AddrGhost}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {maxDir maxEntries maxVal pqCap encCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    PhaseCreditSpec M (CliSessStorePollEnv dir peer g r)
      (sessStorePollDeltaCum (98372903 + 2 * pqCap + 2 * encCap) maxEntries)
      (sessStorePollDeltaLive (encCap + 8195) maxEntries)
      (sessStorePollDeltaPeak (1097365 + pqCap + encCap) maxEntries)
      (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries) := by
  have hc := recordSerializeCum_le_of_dom hValid hEnc
  have hl := recordSerializeOutLarge_le_of_dom hM hValid hEnc
  have hp := recordSerializePeak_le_of_dom hM hsmall hValid hEnc
  have hr := recordSerializeMaxReq_le_of_dom hValid hEnc
  refine (sessStorePoll_phaseCredit hM hdc hpeer).mono ?_ ?_ ?_ ?_
  · unfold sessStorePollDeltaCum; omega
  · unfold sessStorePollDeltaLive; omega
  · unfold sessStorePollDeltaPeak; omega
  · unfold sessStorePollMaxReq; omega

/-- Ghost-free `PhaseCreditSpec` for `RecordDecryptEnv tdEnv x` under `SessionGhostValid` and `SessionCloneDom pqCap`.
-/
theorem recordDecrypt_dom_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    {pqCap : Nat} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {ses : Session (List (BitVec 8))}
    {c_td l_td p_td r_td : Nat}
    (hst : x.st = ses.state)
    (hgv : SessionGhostValid x.G ses)
    (hdom : SessionCloneDom pqCap ses)
    (hTd : ∀ G₁ : SessionGhost, CloneRel x.G G₁ →
      PhaseCreditSpec M (tdEnv (recordTryDecryptEnvArgs x G₁)) c_td l_td p_td r_td) :
    PhaseCreditSpec M (RecordDecryptEnv tdEnv x)
      (98382860 + 2 * pqCap + c_td)
      (1089170 + pqCap + l_td)
      (1089170 + pqCap + max p_td l_td)
      (max (max 208000 pqCap) (max r_td 192)) := by
  have hClone : PhaseCreditSpec M (SegCloneEnv x.G x.st)
      (98363364 + 2 * pqCap) (1089170 + pqCap) (1089170 + pqCap) (max 208000 pqCap) := by
    rw [hst]
    exact sessionClone_dom_phaseCredit hM hsmall hgv hdom
  exact (phaseCreditSpec_recordDecryptEnv hM (by omega) hClone hTd).mono
    (by omega) (by omega) (by omega) (by omega)

/-! ## 6. Tight `fineCostModel` and `PhaseGroupSpec` Ghost-Free Bridges -/

section TightFineCloneBounds

open CryptoVerification.SignalSession.Cli (GrowOneDirGhost)
open LibsignalBinary.Heap
  (FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale MmapThresholdReq fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecGrowEvents)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec (CliAddrTextEnv CliDirPutEnv)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec fineSmallAllocGroupS
   smallAllocGroupS_fineCostModel_eq smallAllocGroupS_le_16659_of_le_44)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_freeNonInc fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (fineDirPutCum fineDirPutLive optLargeCost_fine_mono optLargeCost_fine_of_le
   serialize_phaseCredit_tight sessStorePollTightDeltaCum sessStorePollTightDeltaLive
   sessStorePollTightDeltaPeak sessStorePoll_phaseCredit_tight
   sessionClone_drop_cancel_phaseCredit_tight sessionClone_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (chainCloneTightCum_fine_le chainCloneTightCum dropClonedChainEvents dropClonedMessageKeysEvents
   fineSmallAllocCost_192 fineSmallAllocCost_le_9789_of_le_520
   fineSmallAllocCost_le_9789_of_le_2048 rustAllocTightCum
   rustAllocTightCum_fine_32 rustAllocTightCum_fine_le_143484 rustAllocTightCum_fine_le_738
   segCloneTightCum senderChainCloneTightCum_fine_le tryCloneSmallDelta
   tryCloneSmallDelta_fine_le_143484 tryCloneSmallDelta_fine_le_738)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (SerializeSomeCancelEnv recordSerializeTightCum serializeSomeTightCum)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget (GrowOneDirEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (GrowOneSpeEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
  (chainCloneEvents senderChainCloneEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (FromFEnv FromMEnv FromVEnv FromVPostTdEnv SegTailEnv optTailCloneEvents segCloneEvents
   vecCloneEvents)

private theorem list_map_sum_aff_le {α : Type} (f lenF : α → Nat) (a b : Nat) :
    ∀ (xs : List α),
      (∀ x ∈ xs, f x ≤ a + b * lenF x) →
      (xs.map f).sum ≤ xs.length * a + b * (xs.map lenF).sum
  | [], _ => Nat.zero_le _
  | x :: xs, hall => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx := hall x List.mem_cons_self
    have hxs := list_map_sum_aff_le f lenF a b xs (fun y hy => hall y (List.mem_cons_of_mem _ hy))
    have hsum := Nat.add_le_add hx hxs
    have hrhs : (a + b * lenF x) + (xs.length * a + b * (xs.map lenF).sum) =
        (xs.length + 1) * a + b * (lenF x + (xs.map lenF).sum) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
      omega
    rw [← hrhs]
    exact hsum

private theorem add9_mid_aff_le
    {x1 x2 x3 x4 y x6 x7 x8 x9 b1 b2 b3 b4 bm b6 b7 b8 b9 total k : Nat}
    (h1 : x1 ≤ b1) (h2 : x2 ≤ b2) (h3 : x3 ≤ b3) (h4 : x4 ≤ b4)
    (hy : y ≤ bm + k)
    (h6 : x6 ≤ b6) (h7 : x7 ≤ b7) (h8 : x8 ≤ b8) (h9 : x9 ≤ b9)
    (hsum : b1 + b2 + b3 + b4 + bm + b6 + b7 + b8 + b9 ≤ total) :
    x1 + x2 + x3 + x4 + y + x6 + x7 + x8 + x9 ≤ total + k := by
  omega

private theorem tryCloneSmallDelta_fine_le_9789_of_le_2048 {len : Nat} (h : len ≤ 2048) :
    tryCloneSmallDelta fineCostModel len ≤ 9789 := by
  unfold tryCloneSmallDelta rustAllocTightCum
  split
  · exact Nat.zero_le 9789
  · have hsm : len ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]
      exact Nat.le_trans h (by decide)
    simp only [hsm, ↓reduceIte]
    exact fineSmallAllocCost_le_9789_of_le_2048 h

/-- Key-sum-parametric tight `segCloneTightCum` bound on `fineCostModel` (`≤ 897,456 + 738 * maxTotalKeys`).
-/
theorem segCloneTightCum_fine_keys_le_of_dom {pqCap maxTotalKeys : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses)
    (hkeys : ((G.chains.zip ses.state.receiverChains).map
      (fun gc => gc.2.messageKeys.length)).sum ≤ maxTotalKeys) :
    segCloneTightCum fineCostModel G ses.state ≤ 897456 + 738 * maxTotalKeys := by
  obtain ⟨hloc_len, hrem_len, _, hch_ok, hsend_ok, hpend_len, hkyb_len, halice_eq, _⟩ :=
    ghostCloneValid_of_sessionGhostValid hgv
  obtain ⟨hrc_len, hseeds, halice_dom, hkyb_cap, _⟩ := hdom
  unfold segCloneTightCum
  have b1 : tryCloneSmallDelta fineCostModel G.localIk.bytes.length ≤ 738 :=
    tryCloneSmallDelta_fine_le_738 (by omega)
  have b2 : tryCloneSmallDelta fineCostModel G.remoteIk.bytes.length ≤ 738 :=
    tryCloneSmallDelta_fine_le_738 (Nat.le_trans hrem_len (by decide))
  have b3 : rustAllocTightCum fineCostModel 32 ≤ 738 := by
    rw [rustAllocTightCum_fine_32]
  have b4 : (match G.sender, ses.state.senderChain with
      | some gs, some sc => chainCloneTightCum fineCostModel (senderChainAsProtoGhost gs sc)
      | _, _ => 0) ≤ 2214 := by
    rcases hsend_ok with ⟨h1, h2⟩ | ⟨gs, sc, h1, h2, hsrk, hpriv⟩
    · rw [h1, h2]; exact Nat.zero_le 2214
    · rw [h1, h2]
      exact senderChainCloneTightCum_fine_le (by omega) (by omega)
  have b5 : (if ses.state.receiverChains = [] then 0
      else rustAllocTightCum fineCostModel (104 * ses.state.receiverChains.length) +
        ((G.chains.zip ses.state.receiverChains).map (chainCloneTightCum fineCostModel)).sum) ≤
      738279 + 738 * maxTotalKeys := by
    split
    · exact Nat.zero_le _
    · have hout : rustAllocTightCum fineCostModel (104 * ses.state.receiverChains.length) ≤ 9789 := by
        unfold rustAllocTightCum
        have h520 : 104 * ses.state.receiverChains.length ≤ 520 := by omega
        have hsm : 104 * ses.state.receiverChains.length ≤
            HasFineReallocCredit.smallMaxReq fineCostModel := by
          rw [fineCostModel_smallMaxReq_eq]
          exact Nat.le_trans h520 (by decide)
        simp only [hsm, ↓reduceIte]
        exact fineSmallAllocCost_le_9789_of_le_520 h520
      have hzip_len : (G.chains.zip ses.state.receiverChains).length ≤ 5 :=
        Nat.le_trans (zip_length_le_right _ _) hrc_len
      have haff := list_map_sum_aff_le
        (chainCloneTightCum fineCostModel) (fun gc => gc.2.messageKeys.length) 145698 738
        (G.chains.zip ses.state.receiverChains)
        (fun gc hmem => by
          obtain ⟨hsrk, hpriv, _⟩ := hch_ok gc hmem
          have hsd := hseeds gc.2 (snd_mem_of_mem_zip hmem)
          exact chainCloneTightCum_fine_le (by omega) (by omega)
            (fun mkg hm => by rw [hsd mkg hm]; decide))
      have h5mul : (G.chains.zip ses.state.receiverChains).length * 145698 ≤ 728490 :=
        Nat.le_trans (Nat.mul_le_mul_right 145698 hzip_len) (by decide)
      have hk_mul : 738 * ((G.chains.zip ses.state.receiverChains).map
          (fun gc => gc.2.messageKeys.length)).sum ≤ 738 * maxTotalKeys :=
        Nat.mul_le_mul_left 738 hkeys
      have hsum_le : ((G.chains.zip ses.state.receiverChains).map
          (chainCloneTightCum fineCostModel)).sum ≤ 728490 + 738 * maxTotalKeys :=
        Nat.le_trans haff (Nat.add_le_add h5mul hk_mul)
      have htot := Nat.add_le_add hout hsum_le
      rw [← Nat.add_assoc 9789 728490, show 9789 + 728490 = 738279 by decide] at htot
      exact htot
  have b6 : tryCloneSmallDelta fineCostModel (optTailCloneLen G.pending) ≤ 738 :=
    tryCloneSmallDelta_fine_le_738 (Nat.le_trans hpend_len (by decide))
  have hkyb_le : optTailCloneLen G.kyber ≤ 2048 := by
    rw [hkyb_len]
    cases hk : ses.pendingKyberPreKey with
    | none => simp
    | some k => exact Nat.le_trans (hkyb_cap k hk) (by decide)
  have b7 : tryCloneSmallDelta fineCostModel (optTailCloneLen G.kyber) ≤ 9789 :=
    tryCloneSmallDelta_fine_le_9789_of_le_2048 hkyb_le
  have halice_le : G.alice.bytes.length ≤ 44 := by
    rw [halice_eq]; exact Nat.le_trans halice_dom (by decide)
  have b8 : tryCloneSmallDelta fineCostModel G.alice.bytes.length ≤ 738 :=
    tryCloneSmallDelta_fine_le_738 halice_le
  have b9 : tryCloneSmallDelta fineCostModel ses.state.pqRatchetState.length ≤ 143484 :=
    tryCloneSmallDelta_fine_le_143484 ses.state.pqRatchetState.length
  exact add9_mid_aff_le b1 b2 b3 b4 b5 b6 b7 b8 b9 (by decide)

private theorem receiverKeys_sum_le_10000 {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    ((G.chains.zip ses.state.receiverChains).map (fun gc => gc.2.messageKeys.length)).sum ≤ 10000 := by
  obtain ⟨_, _, _, hch_ok, _, _, _, _, _⟩ := ghostCloneValid_of_sessionGhostValid hgv
  have hzip_len : (G.chains.zip ses.state.receiverChains).length ≤ 5 :=
    Nat.le_trans (zip_length_le_right _ _) hdom.rc_len
  have hsum := map_sum_le (fun gc : ChainGhost × ReceiverChain => gc.2.messageKeys.length) 2000
    (G.chains.zip ses.state.receiverChains)
    (fun gc hmem => (hch_ok gc hmem).2.2)
  exact Nat.le_trans hsum (Nat.le_trans (Nat.mul_le_mul_right 2000 hzip_len) (by decide))

/-- Unconditional tight `segCloneTightCum` bound on `fineCostModel` (`≤ 8,277,456`). -/
theorem segCloneTightCum_fine_le_of_dom {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    segCloneTightCum fineCostModel G ses.state ≤ 8277456 := by
  have hk := segCloneTightCum_fine_keys_le_of_dom hgv hdom (receiverKeys_sum_le_10000 hgv hdom)
  exact Nat.le_trans hk (by decide)

theorem segCloneLarge_fine_le_of_dom {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    segCloneLarge fineCostModel G ses.state ≤ 1080975 + optLargeCost fineCostModel pqCap := by
  obtain ⟨hloc_len, hrem_len, _, hch_ok, hsend_ok, hpend_len, hkyb_len, halice_eq, _⟩ :=
    ghostCloneValid_of_sessionGhostValid hgv
  obtain ⟨hrc_len, hseeds, halice_dom, hkyb_cap, hpq_len⟩ := hdom
  have hsmall33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  unfold segCloneLarge
  have hloc : vecCloneLarge fineCostModel G.localIk.bytes.length = 0 :=
    vecCloneLarge_eq_zero_of_le fineCostModel
      (by rw [fineCostModel_smallMaxReq_eq]; omega)
  have hrem : vecCloneLarge fineCostModel G.remoteIk.bytes.length = 0 :=
    vecCloneLarge_eq_zero_of_le fineCostModel
      (by rw [fineCostModel_smallMaxReq_eq]; omega)
  have hroot : optLargeCost fineCostModel 32 = 0 := optLargeCost_fine_of_le (by decide)
  have hrc : (if ses.state.receiverChains = [] then 0
      else optLargeCost fineCostModel (104 * ses.state.receiverChains.length) +
        ((G.chains.zip ses.state.receiverChains).map (chainCloneLarge fineCostModel)).sum) ≤
      1080975 := by
    split_ifs with hnil
    · exact Nat.zero_le 1080975
    · have houter : optLargeCost fineCostModel (104 * ses.state.receiverChains.length) = 0 :=
        optLargeCost_fine_of_le (by omega)
      have hzip_len : (G.chains.zip ses.state.receiverChains).length ≤ 5 :=
        Nat.le_trans (zip_length_le_right _ _) hrc_len
      have hsum : ((G.chains.zip ses.state.receiverChains).map
          (chainCloneLarge fineCostModel)).sum ≤
          (G.chains.zip ses.state.receiverChains).length * 216195 :=
        map_sum_le (chainCloneLarge fineCostModel) 216195 (G.chains.zip ses.state.receiverChains)
          (fun gc hmem => by
            obtain ⟨hsrk, hpriv, hmk⟩ := hch_ok gc hmem
            exact chainCloneLarge_recv_le fineCostModel_modelHyps hsmall33 hsrk hpriv hmk
              (hseeds gc.2 (snd_mem_of_mem_zip hmem)))
      rw [houter, Nat.zero_add]
      exact Nat.le_trans hsum (Nat.le_trans (Nat.mul_le_mul_right 216195 hzip_len) (by decide))
  have hpend : vecCloneLarge fineCostModel (optTailCloneLen G.pending) = 0 :=
    vecCloneLarge_eq_zero_of_le fineCostModel
      (by rw [fineCostModel_smallMaxReq_eq]; omega)
  have hkyb_le : optTailCloneLen G.kyber ≤ 1569 := by
    rw [hkyb_len]
    cases hk : ses.pendingKyberPreKey with
    | none => simp
    | some k => exact hkyb_cap k hk
  have hkyb : vecCloneLarge fineCostModel (optTailCloneLen G.kyber) = 0 :=
    vecCloneLarge_eq_zero_of_le fineCostModel
      (by rw [fineCostModel_smallMaxReq_eq]; omega)
  have halice : vecCloneLarge fineCostModel G.alice.bytes.length = 0 :=
    vecCloneLarge_eq_zero_of_le fineCostModel
      (by rw [fineCostModel_smallMaxReq_eq, halice_eq]; omega)
  have hpq : vecCloneLarge fineCostModel ses.state.pqRatchetState.length ≤
      optLargeCost fineCostModel pqCap := by
    unfold vecCloneLarge
    split
    · exact Nat.zero_le _
    · exact optLargeCost_fine_mono hpq_len
  rw [hloc, hrem, hroot, hpend, hkyb, halice]
  rcases hsend_ok with ⟨h1, h2⟩ | ⟨gs, sc, h1, h2, hsrk, hpriv⟩
  · rw [h1, h2]
    simp only [Nat.zero_add, Nat.add_zero]
    exact Nat.add_le_add hrc hpq
  · rw [h1, h2]
    dsimp only
    rw [chainCloneLarge_sender_eq_zero hsmall33 sc hsrk hpriv]
    simp only [Nat.zero_add, Nat.add_zero]
    exact Nat.add_le_add hrc hpq

theorem sessionClone_keys_dom_phaseCredit_tight {pqCap maxTotalKeys : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses)
    (hkeys : ((G.chains.zip ses.state.receiverChains).map
      (fun gc => gc.2.messageKeys.length)).sum ≤ maxTotalKeys) :
    PhaseCreditSpec fineCostModel (SegCloneEnv G ses.state)
      (897456 + 738 * maxTotalKeys)
      (1080975 + optLargeCost fineCostModel pqCap)
      (1080975 + optLargeCost fineCostModel pqCap)
      (max 208000 pqCap) :=
  (sessionClone_phaseCredit_tight fineCostModel_modelHyps G ses.state).mono
    (segCloneTightCum_fine_keys_le_of_dom hgv hdom hkeys)
    (segCloneLarge_fine_le_of_dom hgv hdom)
    (segCloneLarge_fine_le_of_dom hgv hdom)
    (segCloneMaxReq_le_of_dom hgv hdom)

theorem sessionClone_dom_phaseCredit_tight {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    PhaseCreditSpec fineCostModel (SegCloneEnv G ses.state)
      8277456
      (1080975 + optLargeCost fineCostModel pqCap)
      (1080975 + optLargeCost fineCostModel pqCap)
      (max 208000 pqCap) :=
  (sessionClone_phaseCredit_tight fineCostModel_modelHyps G ses.state).mono
    (segCloneTightCum_fine_le_of_dom hgv hdom)
    (segCloneLarge_fine_le_of_dom hgv hdom)
    (segCloneLarge_fine_le_of_dom hgv hdom)
    (segCloneMaxReq_le_of_dom hgv hdom)

theorem sessionClone_drop_cancel_dom_phaseCredit_tight {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {Body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses)
    (hBody : PhaseCreditSpec fineCostModel Body c_b l_b p_b r_b) :
    PhaseCreditSpec fineCostModel
      (ConcatEnv (ConcatEnv (SegCloneEnv G ses.state) Body)
        (· = dropClonedSessionEvents G ses.state))
      (8277456 + c_b)
      l_b
      (1080975 + optLargeCost fineCostModel pqCap + p_b)
      (max (max 208000 pqCap) r_b) :=
  (sessionClone_drop_cancel_phaseCredit_tight fineCostModel_modelHyps G ses.state hBody).mono
    (Nat.add_le_add_right (segCloneTightCum_fine_le_of_dom hgv hdom) c_b)
    (Nat.le_refl l_b)
    (Nat.add_le_add_right (segCloneLarge_fine_le_of_dom hgv hdom) p_b)
    (Nat.max_le.mpr
      ⟨Nat.le_trans (segCloneMaxReq_le_of_dom hgv hdom) (Nat.le_max_left _ _),
       Nat.le_max_right _ _⟩)

theorem sessionClone_keys_drop_cancel_dom_phaseCredit_tight {pqCap maxTotalKeys : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {Body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses)
    (hkeys : ((G.chains.zip ses.state.receiverChains).map
      (fun gc => gc.2.messageKeys.length)).sum ≤ maxTotalKeys)
    (hBody : PhaseCreditSpec fineCostModel Body c_b l_b p_b r_b) :
    PhaseCreditSpec fineCostModel
      (ConcatEnv (ConcatEnv (SegCloneEnv G ses.state) Body)
        (· = dropClonedSessionEvents G ses.state))
      (897456 + 738 * maxTotalKeys + c_b)
      l_b
      (1080975 + optLargeCost fineCostModel pqCap + p_b)
      (max (max 208000 pqCap) r_b) :=
  (sessionClone_drop_cancel_phaseCredit_tight fineCostModel_modelHyps G ses.state hBody).mono
    (Nat.add_le_add_right (segCloneTightCum_fine_keys_le_of_dom hgv hdom hkeys) c_b)
    (Nat.le_refl l_b)
    (Nat.add_le_add_right (segCloneLarge_fine_le_of_dom hgv hdom) p_b)
    (Nat.max_le.mpr
      ⟨Nat.le_trans (segCloneMaxReq_le_of_dom hgv hdom) (Nat.le_max_left _ _),
       Nat.le_max_right _ _⟩)

theorem recordSerializeTightCum_fine_le_of_dom {pqCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses) :
    recordSerializeTightCum fineCostModel g r ≤ 8420940 := by
  have hcl : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      segCloneTightCum fineCostModel G ses.state ≤ 8277456 := by
    intro G ses hg hr
    obtain ⟨hgv, hdom⟩ := hValid G ses hg hr
    exact segCloneTightCum_fine_le_of_dom hgv hdom
  exact Nat.le_trans (SessionSerializeCredit.recordSerializeTightCum_fine_le_of_clone hcl)
    (by decide)

theorem recordSerializeOutLarge_fine_le_of_dom {pqCap encCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    recordSerializeOutLarge fineCostModel g r ≤ optLargeCost fineCostModel encCap := by
  unfold recordSerializeOutLarge
  split
  · next G ses hg hr =>
    obtain ⟨hgv, _⟩ := hValid G ses hg hr
    unfold SessionSerializeCredit.serializeSomeOutLarge
    rw [lenField1_encSessionMem_eq_encodeRecord hr hgv]
    exact optLargeCost_fine_mono hEnc
  · exact Nat.zero_le _

theorem recordSerializePeak_fine_le_of_dom {pqCap encCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    recordSerializePeak fineCostModel g r ≤
      1080975 + optLargeCost fineCostModel pqCap + optLargeCost fineCostModel encCap := by
  unfold recordSerializePeak
  split
  · next G ses hg hr =>
    obtain ⟨hgv, hdom⟩ := hValid G ses hg hr
    unfold SessionSerializeCredit.serializeSomePeak
    dsimp only
    rw [lenField1_encSessionMem_eq_encodeRecord hr hgv]
    exact Nat.add_le_add (segCloneLarge_fine_le_of_dom hgv hdom) (optLargeCost_fine_mono hEnc)
  · exact Nat.zero_le _

theorem serialize_dom_phaseCredit_tight {pqCap encCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    PhaseCreditSpec fineCostModel (RecordSerializeCancelEnv g r)
      8420940
      (optLargeCost fineCostModel encCap)
      (1080975 + optLargeCost fineCostModel pqCap + optLargeCost fineCostModel encCap)
      (max (max 208000 pqCap) encCap) :=
  (serialize_phaseCredit_tight fineCostModel_modelHyps g r).mono
    (recordSerializeTightCum_fine_le_of_dom hValid)
    (recordSerializeOutLarge_fine_le_of_dom hValid hEnc)
    (recordSerializePeak_fine_le_of_dom hValid hEnc)
    (recordSerializeMaxReq_le_of_dom hValid hEnc)

private theorem max_le_max_nat {a₁ a₂ b₁ b₂ : Nat} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    max a₁ b₁ ≤ max a₂ b₂ := by
  omega

theorem sessStorePoll_dom_phaseCredit_tight
    {dir : DirGhost} {peer : AddrGhost}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {maxDir maxEntries maxVal pqCap encCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    PhaseCreditSpec fineCostModel (CliSessStorePollEnv dir peer g r)
      (sessStorePollTightDeltaCum 8420940 maxEntries)
      (sessStorePollTightDeltaLive (optLargeCost fineCostModel encCap) maxEntries)
      (sessStorePollTightDeltaPeak
        (1080975 + optLargeCost fineCostModel pqCap + optLargeCost fineCostModel encCap) maxEntries)
      (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries) := by
  have hc := recordSerializeTightCum_fine_le_of_dom hValid
  have hl := recordSerializeOutLarge_fine_le_of_dom hValid hEnc
  have hp := recordSerializePeak_fine_le_of_dom hValid hEnc
  have hr := recordSerializeMaxReq_le_of_dom hValid hEnc
  refine (sessStorePoll_phaseCredit_tight hdc hpeer).mono ?_
    (Nat.add_le_add_right hl _) (Nat.add_le_add_right hp _) ?_
  · unfold sessStorePollTightDeltaCum
    exact Nat.add_le_add_right (Nat.add_le_add_left hc 9789) _
  · unfold sessStorePollMaxReq
    exact max_le_max_nat hr (Nat.le_refl _)

private theorem phaseCreditSpec_growOneSpe_zero_fine_tight :
    PhaseCreditSpec fineCostModel (GrowOneSpeEnv 0#64) 8186 0 0 192 := by
  have ha := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight fineCostModel_modelHyps
    (req := 192) (al := 8) (by decide)
  have hc : rustAllocTightCum fineCostModel 192 ≤ 8186 := by
    unfold rustAllocTightCum
    have hsm : 192 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; decide
    simp only [hsm, ↓reduceIte]
    rw [fineSmallAllocCost_192]
  have hl : optLargeCost fineCostModel 192 = 0 := optLargeCost_fine_of_le (by decide)
  rw [hl] at ha
  refine ha.congr_mono ?_ hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  rintro evs (⟨_, h1⟩ | ⟨hne, _⟩)
  · exact h1
  · exact absurd rfl hne

private theorem phaseCreditSpec_segTailEnv_fine_tight :
    PhaseCreditSpec fineCostModel SegTailEnv 738 0 0 17 := by
  have ha := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight fineCostModel_modelHyps
    (req := 17) (al := 1) (by decide)
  have hc : rustAllocTightCum fineCostModel 17 ≤ 738 :=
    rustAllocTightCum_fine_le_738 (by decide)
  have hl : optLargeCost fineCostModel 17 = 0 := optLargeCost_fine_of_le (by decide)
  rw [hl] at ha
  exact ((PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).seq
    (ha.mono hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 17))).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem phaseCreditSpec_fromMEnv_fine_tight :
    PhaseCreditSpec fineCostModel FromMEnv 8924 0 0 192 := by
  have hF : PhaseCreditSpec fineCostModel FromFEnv 738 0 0 17 :=
    (phaseCreditSpec_segTailEnv_fine_tight.seq
      (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc)).mono
      (by decide) (by decide) (by decide) (by decide)
  exact (phaseCreditSpec_growOneSpe_zero_fine_tight.seq hF).mono
    (by decide) (by decide) (by decide) (by decide)

theorem phaseCreditSpec_fromVPostTdEnv_fine_tight :
    PhaseCreditSpec fineCostModel FromVPostTdEnv 8924 0 0 192 :=
  ((PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).or
    phaseCreditSpec_fromMEnv_fine_tight).mono
    (by decide) (by decide) (by decide) (by decide)

theorem phaseCreditSpec_recordDecryptEnv_fine_tight
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {c_cl l_cl p_cl r_cl c_td l_td p_td r_td : Nat}
    (hClone : PhaseCreditSpec fineCostModel (SegCloneEnv x.G x.st) c_cl l_cl p_cl r_cl)
    (hTd : ∀ G₁ : SessionGhost, CloneRel x.G G₁ →
      PhaseCreditSpec fineCostModel (tdEnv (recordTryDecryptEnvArgs x G₁)) c_td l_td p_td r_td) :
    PhaseCreditSpec fineCostModel (RecordDecryptEnv tdEnv x)
      (c_cl + c_td + 8924) (l_cl + l_td) (max p_cl (l_cl + max p_td l_td))
      (max (max r_cl r_td) 192) := by
  unfold RecordDecryptEnv
  split
  · refine W2DecryptRecordStorePeak.phaseCreditSpec_exists_guarded fun G₁ hRel => ?_
    have hFV : PhaseCreditSpec fineCostModel (FromVEnv tdEnv x G₁)
        (c_td + 8924) l_td (max p_td l_td) (max r_td 192) :=
      ((hTd G₁ hRel).seq phaseCreditSpec_fromVPostTdEnv_fine_tight).mono
        (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero l_td))
        (max_le_max_nat (Nat.le_refl p_td) (Nat.le_of_eq (Nat.add_zero l_td)))
        (Nat.le_refl _)
    exact (hClone.seq hFV).mono
      (Nat.le_of_eq (Nat.add_assoc c_cl c_td 8924).symm)
      (Nat.le_refl _)
      (Nat.le_refl _)
      (Nat.le_of_eq (Nat.max_assoc r_cl r_td 192).symm)
  · exact (hClone.seq phaseCreditSpec_fromMEnv_fine_tight).mono
      (by omega)
      (Nat.le_trans (Nat.le_of_eq (Nat.add_zero l_cl)) (Nat.le_add_right l_cl l_td))
      (Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.le_of_eq (Nat.add_zero l_cl))
           (Nat.le_trans (Nat.le_add_right l_cl _) (Nat.le_max_right _ _))⟩)
      (Nat.max_le.mpr
        ⟨Nat.le_trans (Nat.le_max_left r_cl r_td) (Nat.le_max_left _ 192),
         Nat.le_max_right _ 192⟩)

theorem recordDecrypt_dom_phaseCredit_tight
    {pqCap : Nat} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {ses : Session (List (BitVec 8))}
    {c_td l_td p_td r_td : Nat}
    (hst : x.st = ses.state)
    (hgv : SessionGhostValid x.G ses)
    (hdom : SessionCloneDom pqCap ses)
    (hTd : ∀ G₁ : SessionGhost, CloneRel x.G G₁ →
      PhaseCreditSpec fineCostModel (tdEnv (recordTryDecryptEnvArgs x G₁)) c_td l_td p_td r_td) :
    PhaseCreditSpec fineCostModel (RecordDecryptEnv tdEnv x)
      (8286380 + c_td)
      (1080975 + optLargeCost fineCostModel pqCap + l_td)
      (1080975 + optLargeCost fineCostModel pqCap + max p_td l_td)
      (max (max 208000 pqCap) (max r_td 192)) := by
  have hClone : PhaseCreditSpec fineCostModel (SegCloneEnv x.G x.st)
      8277456 (1080975 + optLargeCost fineCostModel pqCap)
      (1080975 + optLargeCost fineCostModel pqCap) (max 208000 pqCap) := by
    rw [hst]
    exact sessionClone_dom_phaseCredit_tight hgv hdom
  refine (phaseCreditSpec_recordDecryptEnv_fine_tight hClone hTd).mono ?_ (Nat.le_refl _) ?_ ?_
  · rw [Nat.add_assoc 8277456 c_td 8924, Nat.add_comm c_td 8924,
        ← Nat.add_assoc 8277456 8924 c_td, show 8277456 + 8924 = 8286380 by decide]
  · exact Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · exact Nat.le_of_eq (Nat.max_assoc (max 208000 pqCap) r_td 192)

theorem recordDecrypt_keys_dom_phaseCredit_tight
    {pqCap maxTotalKeys : Nat} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {ses : Session (List (BitVec 8))}
    {c_td l_td p_td r_td : Nat}
    (hst : x.st = ses.state)
    (hgv : SessionGhostValid x.G ses)
    (hdom : SessionCloneDom pqCap ses)
    (hkeys : ((x.G.chains.zip ses.state.receiverChains).map
      (fun gc => gc.2.messageKeys.length)).sum ≤ maxTotalKeys)
    (hTd : ∀ G₁ : SessionGhost, CloneRel x.G G₁ →
      PhaseCreditSpec fineCostModel (tdEnv (recordTryDecryptEnvArgs x G₁)) c_td l_td p_td r_td) :
    PhaseCreditSpec fineCostModel (RecordDecryptEnv tdEnv x)
      (906380 + 738 * maxTotalKeys + c_td)
      (1080975 + optLargeCost fineCostModel pqCap + l_td)
      (1080975 + optLargeCost fineCostModel pqCap + max p_td l_td)
      (max (max 208000 pqCap) (max r_td 192)) := by
  have hClone : PhaseCreditSpec fineCostModel (SegCloneEnv x.G x.st)
      (897456 + 738 * maxTotalKeys)
      (1080975 + optLargeCost fineCostModel pqCap)
      (1080975 + optLargeCost fineCostModel pqCap) (max 208000 pqCap) := by
    rw [hst]
    exact sessionClone_keys_dom_phaseCredit_tight hgv hdom hkeys
  refine (phaseCreditSpec_recordDecryptEnv_fine_tight hClone hTd).mono ?_ (Nat.le_refl _) ?_ ?_
  · have hcomm : (897456 + 738 * maxTotalKeys) + c_td + 8924 =
        (906380 + 738 * maxTotalKeys) + c_td := by
      rw [Nat.add_assoc (897456 + 738 * maxTotalKeys) c_td 8924,
          Nat.add_comm c_td 8924,
          ← Nat.add_assoc (897456 + 738 * maxTotalKeys) 8924 c_td,
          Nat.add_assoc 897456 (738 * maxTotalKeys) 8924,
          Nat.add_comm (738 * maxTotalKeys) 8924,
          ← Nat.add_assoc 897456 8924 (738 * maxTotalKeys),
          show 897456 + 8924 = 906380 by decide]
    exact Nat.le_of_eq hcomm
  · exact Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · exact Nat.le_of_eq (Nat.max_assoc (max 208000 pqCap) r_td 192)

/-! ### `PhaseGroupSpec fineCostModel` Bridges -/

private theorem phaseGroupSpec_append_eq {M : AllocCostModel} [HasFineGroupCredit M]
    {xs ys : List AllocEvent} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec M (· = xs) g₁) (h₂ : PhaseGroupSpec M (· = ys) g₂) :
    PhaseGroupSpec M (· = xs ++ ys) (g₁ + g₂) :=
  (h₁.concat h₂).of_imp fun _ h => ⟨xs, ys, h, rfl, rfl⟩

private theorem phaseGroupSpec_flatMap_eq {α : Type} {M : AllocCostModel} [HasFineGroupCredit M]
    (f : α → List AllocEvent) (g : α → Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, PhaseGroupSpec M (· = f x) (g x)) →
      PhaseGroupSpec M (· = xs.flatMap f) ((xs.map g).sum)
  | [], _ => PhaseGroupSpec.nil M
  | x :: tl, h => by
    have hx := h x List.mem_cons_self
    have htl := phaseGroupSpec_flatMap_eq f g tl (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simpa only [List.flatMap_cons, List.map_cons, List.sum_cons] using
      phaseGroupSpec_append_eq hx htl

private theorem nonFreeBound_condDealloc (p : Prop) [Decidable p] (sz al : Nat) :
    NonFreeBound (· = if p then [] else rustDeallocEvents sz al) 0 := by
  split
  · exact NonFreeBound.nil
  · exact NonFreeBound.rustDealloc sz al

private theorem nonFreeBound_flatMap_zero {α : Type} (f : α → List AllocEvent) :
    ∀ (xs : List α), (∀ x ∈ xs, NonFreeBound (· = f x) 0) →
      NonFreeBound (· = xs.flatMap f) 0
  | [], _ => NonFreeBound.nil
  | x :: tl, h => by
    have hx := h x List.mem_cons_self
    have htl := nonFreeBound_flatMap_zero f tl (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact (hx.concat htl).of_imp fun _ heq => ⟨f x, tl.flatMap f, heq, rfl, rfl⟩

private theorem nonFreeBound_dropClonedChain (gc : ChainGhost × ReceiverChain) :
    NonFreeBound (· = dropClonedChainEvents gc) 0 := by
  have hsrk := nonFreeBound_condDealloc (gc.1.srk.bytes.length = 0) gc.1.srk.bytes.length 1
  have hpriv := nonFreeBound_condDealloc (gc.1.priv.bytes.length = 0) gc.1.priv.bytes.length 1
  have hck : NonFreeBound (· = match gc.2.chainKey with
      | none => [] | some _ => rustDeallocEvents 32 1) 0 := by
    cases gc.2.chainKey
    · exact NonFreeBound.nil
    · exact NonFreeBound.rustDealloc 32 1
  have hmks : NonFreeBound (· = dropClonedMessageKeysEvents gc.2.messageKeys) 0 := by
    unfold dropClonedMessageKeysEvents
    split
    · exact NonFreeBound.nil
    · have hs := nonFreeBound_flatMap_zero
        (fun mkg : MessageKeyGenerator =>
          if mkg.seed.length = 0 then [] else rustDeallocEvents mkg.seed.length 1)
        gc.2.messageKeys
        (fun mkg _ => nonFreeBound_condDealloc (mkg.seed.length = 0) mkg.seed.length 1)
      exact (hs.concat (NonFreeBound.rustDealloc (104 * gc.2.messageKeys.length) 8)).of_imp
        fun _ h => ⟨_, _, h, rfl, rfl⟩
  unfold dropClonedChainEvents
  exact (((hsrk.concat hpriv).concat hck).concat hmks).of_imp fun _ h => by
    subst h
    exact ⟨_, _, rfl, ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩

/-- `dropClonedSessionEvents G st` emits only `.free` events (`0` `groupsScaled` increment). -/
theorem dropClonedSession_phaseGroup (M : AllocCostModel) [HasFineGroupCredit M]
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    PhaseGroupSpec M (· = dropClonedSessionEvents G st) 0 := by
  have hloc := nonFreeBound_condDealloc (G.localIk.bytes.length = 0) G.localIk.bytes.length 1
  have hrem := nonFreeBound_condDealloc (G.remoteIk.bytes.length = 0) G.remoteIk.bytes.length 1
  have hroot := NonFreeBound.rustDealloc 32 1
  have hrc : NonFreeBound (· = if st.receiverChains = [] then []
      else (G.chains.zip st.receiverChains).flatMap dropClonedChainEvents ++
        rustDeallocEvents (104 * st.receiverChains.length) 8) 0 := by
    split
    · exact NonFreeBound.nil
    · have hcs := nonFreeBound_flatMap_zero dropClonedChainEvents
        (G.chains.zip st.receiverChains) (fun gc _ => nonFreeBound_dropClonedChain gc)
      exact (hcs.concat (NonFreeBound.rustDealloc (104 * st.receiverChains.length) 8)).of_imp
        fun _ h => ⟨_, _, h, rfl, rfl⟩
  have halice := nonFreeBound_condDealloc (G.alice.bytes.length = 0) G.alice.bytes.length 1
  have hpq := nonFreeBound_condDealloc (st.pqRatchetState.length = 0) st.pqRatchetState.length 1
  have hsnd : NonFreeBound (· = match G.sender, st.senderChain with
      | some gs, some sc => dropClonedChainEvents (senderChainAsProtoGhost gs sc)
      | _, _ => []) 0 := by
    cases G.sender <;> cases st.senderChain
    · exact NonFreeBound.nil
    · exact NonFreeBound.nil
    · exact NonFreeBound.nil
    · rename_i gs sc
      exact nonFreeBound_dropClonedChain (senderChainAsProtoGhost gs sc)
  have hpend := nonFreeBound_condDealloc (optTailCloneLen G.pending = 0) (optTailCloneLen G.pending) 1
  have hkyb := nonFreeBound_condDealloc (optTailCloneLen G.kyber = 0) (optTailCloneLen G.kyber) 1
  have hall : NonFreeBound (· = dropClonedSessionEvents G st) 0 := by
    unfold dropClonedSessionEvents
    exact ((((((((hloc.concat hrem).concat hroot).concat hrc).concat halice).concat hpq).concat
      hsnd).concat hpend).concat hkyb).of_imp fun _ h => by
      subst h
      exact ⟨_, _, rfl, ⟨_, _, rfl, ⟨_, _, rfl, ⟨_, _, rfl, ⟨_, _, rfl,
        ⟨_, _, rfl, ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  simpa using PhaseGroupSpec.of_nonFreeBound M hall

private theorem phaseGroupSpec_condAlloc_any (p : Prop) [Decidable p] (sz al : Nat) :
    PhaseGroupSpec fineCostModel (· = if p then [] else rustAllocEvents sz al) 196608 := by
  split
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 196608)
  · exact (PhaseGroupSpec.rustAlloc_any fineCostModel sz al).mono (by decide)

private theorem phaseGroupSpec_vecClone_any (v : CryptoVerification.LibsignalSessionRepr.VecGhost) :
    PhaseGroupSpec fineCostModel (· = vecCloneEvents v) 196608 := by
  unfold vecCloneEvents
  exact phaseGroupSpec_condAlloc_any (v.bytes.length = 0) v.bytes.length 1

private theorem phaseGroupSpec_optTailClone_any (o : Option TailVecGhost) :
    PhaseGroupSpec fineCostModel (· = optTailCloneEvents o) 196608 := by
  cases o with
  | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 196608)
  | some g => exact phaseGroupSpec_vecClone_any g.vec

private theorem phaseGroupSpec_chainClone_recv {gc : ChainGhost × ReceiverChain}
    (hseeds : ∀ mkg ∈ gc.2.messageKeys, mkg.seed.length ≤ 44) :
    PhaseGroupSpec fineCostModel (· = chainCloneEvents gc)
      (786432 + 16659 * gc.2.messageKeys.length) := by
  have hsrk := phaseGroupSpec_vecClone_any gc.1.srk
  have hpriv := phaseGroupSpec_vecClone_any gc.1.priv
  have hck : PhaseGroupSpec fineCostModel
      (· = match gc.2.chainKey with | none => [] | some _ => rustAllocEvents 32 1) 196608 := by
    cases gc.2.chainKey
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 196608)
    · exact (PhaseGroupSpec.rustAlloc_any fineCostModel 32 1).mono (by decide)
  have hmks : PhaseGroupSpec fineCostModel
      (· = if gc.2.messageKeys = [] then []
           else rustAllocEvents (104 * gc.2.messageKeys.length) 8 ++
             gc.2.messageKeys.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1))
      (196608 + 16659 * gc.2.messageKeys.length) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · have hbuf : PhaseGroupSpec fineCostModel
          (· = rustAllocEvents (104 * gc.2.messageKeys.length) 8) 196608 :=
        (PhaseGroupSpec.rustAlloc_any fineCostModel _ 8).mono (by decide)
      have hs := phaseGroupSpec_flatMap_eq
        (fun mkg : MessageKeyGenerator => rustAllocEvents mkg.seed.length 1)
        (fun _ => 16659) gc.2.messageKeys
        (fun mkg hm => by
          have hle44 := hseeds mkg hm
          have hsm := PhaseGroupSpec.rustAlloc_small fineCostModel
            (size := mkg.seed.length) (align := 1) (by decide)
            (Nat.le_trans hle44 (by decide : 44 ≤ MmapThresholdReq))
          rw [smallAllocGroupS_fineCostModel_eq] at hsm
          exact hsm.mono (smallAllocGroupS_le_16659_of_le_44 hle44))
      have hsum : (gc.2.messageKeys.map (fun _ => 16659)).sum =
          16659 * gc.2.messageKeys.length := by
        simp [List.sum_replicate, Nat.mul_comm]
      rw [hsum] at hs
      exact phaseGroupSpec_append_eq hbuf hs
  unfold chainCloneEvents
  exact (phaseGroupSpec_append_eq
    (phaseGroupSpec_append_eq (phaseGroupSpec_append_eq hsrk hpriv) hck) hmks).mono
    (by rw [← Nat.add_assoc (196608 + 196608 + 196608) 196608,
            show 196608 + 196608 + 196608 + 196608 = 786432 by decide])

private theorem phaseGroupSpec_senderChainClone (gs : SenderChainGhost) (sc : SenderChain) :
    PhaseGroupSpec fineCostModel (· = senderChainCloneEvents gs sc) 786432 := by
  have h := phaseGroupSpec_chainClone_recv (gc := senderChainAsProtoGhost gs sc)
    (fun _ hm => nomatch hm)
  simpa [senderChainCloneEvents, senderChainAsProtoGhost] using h

/-- Key-sum-parametric `PhaseGroupSpec fineCostModel` for `SegCloneEnv G ses.state`. -/
theorem sessionClone_keys_dom_phaseGroup {pqCap maxTotalKeys : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (_hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses)
    (hkeys : ((G.chains.zip ses.state.receiverChains).map
      (fun gc => gc.2.messageKeys.length)).sum ≤ maxTotalKeys) :
    PhaseGroupSpec fineCostModel (SegCloneEnv G ses.state)
      (6291456 + 16659 * maxTotalKeys) := by
  have hloc := phaseGroupSpec_vecClone_any G.localIk
  have hrem := phaseGroupSpec_vecClone_any G.remoteIk
  have hroot : PhaseGroupSpec fineCostModel (· = rustAllocEvents 32 1) 196608 :=
    (PhaseGroupSpec.rustAlloc_any fineCostModel 32 1).mono (by decide)
  have hsnd : PhaseGroupSpec fineCostModel
      (· = match G.sender, ses.state.senderChain with
           | some gs, some sc => senderChainCloneEvents gs sc
           | _, _ => []) 786432 := by
    cases G.sender <;> cases ses.state.senderChain
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 786432)
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 786432)
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 786432)
    · rename_i gs sc
      exact phaseGroupSpec_senderChainClone gs sc
  have hrc : PhaseGroupSpec fineCostModel
      (· = if ses.state.receiverChains = [] then []
           else rustAllocEvents (104 * ses.state.receiverChains.length) 8 ++
             (G.chains.zip ses.state.receiverChains).flatMap chainCloneEvents)
      (4128768 + 16659 * maxTotalKeys) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · have hbuf : PhaseGroupSpec fineCostModel
          (· = rustAllocEvents (104 * ses.state.receiverChains.length) 8) 196608 :=
        (PhaseGroupSpec.rustAlloc_any fineCostModel _ 8).mono (by decide)
      have hchains := phaseGroupSpec_flatMap_eq
        chainCloneEvents (fun gc => 786432 + 16659 * gc.2.messageKeys.length)
        (G.chains.zip ses.state.receiverChains)
        (fun gc hmem =>
          phaseGroupSpec_chainClone_recv (fun mkg hm =>
            by rw [hdom.seeds32 gc.2 (snd_mem_of_mem_zip hmem) mkg hm]; decide))
      have hzip_len : (G.chains.zip ses.state.receiverChains).length ≤ 5 :=
        Nat.le_trans (zip_length_le_right _ _) hdom.rc_len
      have haff := list_map_sum_aff_le
        (fun gc : ChainGhost × ReceiverChain => 786432 + 16659 * gc.2.messageKeys.length)
        (fun gc => gc.2.messageKeys.length) 786432 16659
        (G.chains.zip ses.state.receiverChains)
        (fun _ _ => Nat.le_refl _)
      have h5mul : (G.chains.zip ses.state.receiverChains).length * 786432 ≤ 3932160 :=
        Nat.le_trans (Nat.mul_le_mul_right 786432 hzip_len) (by decide)
      have hk_mul : 16659 * ((G.chains.zip ses.state.receiverChains).map
          (fun gc => gc.2.messageKeys.length)).sum ≤ 16659 * maxTotalKeys :=
        Nat.mul_le_mul_left 16659 hkeys
      have hsum_le := Nat.le_trans haff (Nat.add_le_add h5mul hk_mul)
      refine (phaseGroupSpec_append_eq hbuf hchains).mono ?_
      have htot := Nat.add_le_add (Nat.le_refl 196608) hsum_le
      rw [← Nat.add_assoc 196608 3932160, show 196608 + 3932160 = 4128768 by decide] at htot
      exact htot
  have hpend := phaseGroupSpec_optTailClone_any G.pending
  have hkyb := phaseGroupSpec_optTailClone_any G.kyber
  have halice := phaseGroupSpec_vecClone_any G.alice
  have hpq := phaseGroupSpec_condAlloc_any
    (ses.state.pqRatchetState.length = 0) ses.state.pqRatchetState.length 1
  have s1 := phaseGroupSpec_append_eq hloc hrem
  have s2 := phaseGroupSpec_append_eq s1 hroot
  have s3 := phaseGroupSpec_append_eq s2 hsnd
  have s4 := phaseGroupSpec_append_eq s3 hrc
  have s5 := phaseGroupSpec_append_eq s4 hpend
  have s6 := phaseGroupSpec_append_eq s5 hkyb
  have s7 := phaseGroupSpec_append_eq s6 halice
  have s8 := phaseGroupSpec_append_eq s7 hpq
  unfold SegCloneEnv segCloneEvents
  refine s8.mono ?_
  exact add9_mid_aff_le
    (Nat.le_refl 196608) (Nat.le_refl 196608) (Nat.le_refl 196608) (Nat.le_refl 786432)
    (Nat.le_refl (4128768 + 16659 * maxTotalKeys))
    (Nat.le_refl 196608) (Nat.le_refl 196608) (Nat.le_refl 196608) (Nat.le_refl 196608)
    (by decide)

theorem sessionClone_dom_phaseGroup {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (SegCloneEnv G ses.state) 172881456 :=
  (sessionClone_keys_dom_phaseGroup hgv hdom (receiverKeys_sum_le_10000 hgv hdom)).mono
    (by decide)

theorem sessionClone_drop_cancel_dom_phaseGroup {pqCap g_b : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {Body : List AllocEvent → Prop}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses)
    (hBody : PhaseGroupSpec fineCostModel Body g_b) :
    PhaseGroupSpec fineCostModel
      (ConcatEnv (ConcatEnv (SegCloneEnv G ses.state) Body)
        (· = dropClonedSessionEvents G ses.state))
      (172881456 + g_b) :=
  (((sessionClone_dom_phaseGroup hgv hdom).concat hBody).concat
    (dropClonedSession_phaseGroup fineCostModel G ses.state)).mono
    (Nat.le_of_eq (Nat.add_zero _))

theorem serialize_dom_phaseGroup {pqCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g r) 173078064 := by
  unfold RecordSerializeCancelEnv
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 173078064)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 173078064)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 173078064)
  · rename_i G ses
    obtain ⟨hgv, hdom⟩ := hValid G ses hg hr
    unfold SerializeSomeCancelEnv
    have hout : PhaseGroupSpec fineCostModel
        (· = rustAllocEvents (lenField 1 (encSessionMem G ses)).length 1) 196608 :=
      (PhaseGroupSpec.rustAlloc_any fineCostModel _ 1).mono (by decide)
    exact (sessionClone_drop_cancel_dom_phaseGroup hgv hdom hout).mono (by decide)

theorem addrText_phaseGroup (peer : AddrGhost) :
    PhaseGroupSpec fineCostModel (CliAddrTextEnv peer) 196608 := by
  have hnf : NonFreeBound (CliAddrTextEnv peer) 1 := by
    rintro evs ⟨cap, _, hs⟩
    exact ((NonFreeBound.rustAlloc cap 1).seq NonFreeBound.freeOnly) evs hs
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by decide)

theorem dirPut_phaseGroup (dir : DirGhost) (name bytes : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (CliDirPutEnv dir name bytes) 196608 := by
  have hgr : NonFreeBound
      (fun evs => ∃ x : GrowOneDirGhost,
        x.cap.toNat ≤ max 4 (2 * dir.changed.length) ∧ GrowOneDirEnv x evs) 1 := by
    rintro evs ⟨x, _, hg⟩
    unfold GrowOneDirEnv rawVecGrowEvents at hg
    split at hg
    · exact NonFreeBound.rustAlloc _ 8 evs hg
    · exact NonFreeBound.rustRealloc _ _ 8 evs hg
  have hnf : NonFreeBound (CliDirPutEnv dir name bytes) (max 0 1) :=
    NonFreeBound.freeOnly.or hgr
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by decide)

theorem sessStorePoll_dom_phaseGroup {pqCap : Nat}
    {dir : DirGhost} {peer : AddrGhost}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (CliSessStorePollEnv dir peer g r) 173471280 := by
  unfold CliSessStorePollEnv
  have h1 := addrText_phaseGroup peer
  have h2 := serialize_dom_phaseGroup hValid
  have h3 := (dirPut_phaseGroup dir [] []).seq (PhaseGroupSpec.freeOnly fineCostModel)
  exact (h1.seq (h2.seq h3)).mono (by decide)

theorem fromVPostTdEnv_phaseGroup :
    PhaseGroupSpec fineCostModel FromVPostTdEnv 393216 := by
  have hspe : PhaseGroupSpec fineCostModel (GrowOneSpeEnv 0#64) 196608 := by
    refine ((PhaseGroupSpec.rustAlloc_any fineCostModel 192 8).of_imp ?_).mono (by decide)
    rintro evs (⟨_, h1⟩ | ⟨hne, _⟩)
    · exact h1
    · exact absurd rfl hne
  have htail : PhaseGroupSpec fineCostModel SegTailEnv 196608 :=
    ((PhaseGroupSpec.freeOnly fineCostModel).seq
      (PhaseGroupSpec.rustAlloc_any fineCostModel 17 1)).mono (by decide)
  have hF : PhaseGroupSpec fineCostModel FromFEnv 196608 :=
    (htail.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by decide)
  have hM_grp : PhaseGroupSpec fineCostModel FromMEnv 393216 :=
    (hspe.seq hF).mono (by decide)
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hM_grp).mono (by decide)

theorem recordDecrypt_dom_phaseGroup {pqCap g_td : Nat}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {ses : Session (List (BitVec 8))}
    (hst : x.st = ses.state)
    (hgv : SessionGhostValid x.G ses)
    (hdom : SessionCloneDom pqCap ses)
    (hTd : ∀ G₁ : SessionGhost, CloneRel x.G G₁ →
      PhaseGroupSpec fineCostModel (tdEnv (recordTryDecryptEnvArgs x G₁)) g_td) :
    PhaseGroupSpec fineCostModel (RecordDecryptEnv tdEnv x) (173274672 + g_td) := by
  have hClone : PhaseGroupSpec fineCostModel (SegCloneEnv x.G x.st) 172881456 := by
    rw [hst]
    exact sessionClone_dom_phaseGroup hgv hdom
  unfold RecordDecryptEnv
  split
  · refine { groups_le := fun st0 {_} ⟨G₁, hRel, hevs⟩ => ?_ }
    have hFV : PhaseGroupSpec fineCostModel (FromVEnv tdEnv x G₁) (g_td + 393216) :=
      (hTd G₁ hRel).seq fromVPostTdEnv_phaseGroup
    have htot : PhaseGroupSpec fineCostModel (SeqEnv (SegCloneEnv x.G x.st) (FromVEnv tdEnv x G₁))
        (173274672 + g_td) := by
      refine (hClone.seq hFV).mono ?_
      have hcomm : 172881456 + (g_td + 393216) = 173274672 + g_td := by
        rw [← Nat.add_assoc 172881456 g_td 393216,
            Nat.add_comm 172881456 g_td,
            Nat.add_assoc g_td 172881456 393216,
            show 172881456 + 393216 = 173274672 by decide,
            Nat.add_comm g_td 173274672]
      exact Nat.le_of_eq hcomm
    exact htot.groups_le st0 hevs
  · have hspe : PhaseGroupSpec fineCostModel (GrowOneSpeEnv 0#64) 196608 := by
      refine ((PhaseGroupSpec.rustAlloc_any fineCostModel 192 8).of_imp ?_).mono (by decide)
      rintro evs (⟨_, h1⟩ | ⟨hne, _⟩)
      · exact h1
      · exact absurd rfl hne
    have htail : PhaseGroupSpec fineCostModel SegTailEnv 196608 :=
      ((PhaseGroupSpec.freeOnly fineCostModel).seq
        (PhaseGroupSpec.rustAlloc_any fineCostModel 17 1)).mono (by decide)
    have hF : PhaseGroupSpec fineCostModel FromFEnv 196608 :=
      (htail.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by decide)
    have hM_grp : PhaseGroupSpec fineCostModel FromMEnv 393216 :=
      (hspe.seq hF).mono (by decide)
    exact (hClone.seq hM_grp).mono
      (Nat.le_trans (by decide : 172881456 + 393216 ≤ 173274672) (Nat.le_add_right _ g_td))

/-! ### Fresh-Bob `SegCloneEnv` and `FromMEnv` / `FromFEnv` Bounds -/

private def checkFineSmallAllocUnits1024 : Bool :=
  (List.range 33).all fun hi =>
    (List.range 32).all fun lo =>
      let u := 32 * hi + lo
      decide (1024 < u ∨ LibsignalBinary.Heap.Fine.fineSmallAllocCost (16 * u) ≤ 20602)

private theorem checkFineSmallAllocUnits1024_true :
    checkFineSmallAllocUnits1024 = true := by
  decide

theorem fineSmallAllocCost_le_20602_of_le_16384 {req : Nat} (hreq : req ≤ 16384) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 20602 := by
  change LibsignalBinary.Heap.Fine.fineSmallAllocCost req ≤ 20602
  have hm : req ≤ MmapThresholdReq := Nat.le_trans hreq (by decide)
  set u := (req + 3) / 16
  have hu_le : u ≤ 1024 := by omega
  have hhi : u / 32 < 33 := by omega
  have hlo : u % 32 < 32 := by omega
  have hsplit : 32 * (u / 32) + u % 32 = u := Nat.div_add_mod u 32
  have hm16 : 16 * u ≤ MmapThresholdReq := by
    have h16 : 16 * u ≤ 16384 := by omega
    exact Nat.le_trans h16 (by decide)
  have hdiv : (16 * u + 3) / 16 = u := by omega
  have heq : LibsignalBinary.Heap.Fine.fineSmallAllocCost req =
      LibsignalBinary.Heap.Fine.fineSmallAllocCost (16 * u) := by
    unfold LibsignalBinary.Heap.Fine.fineSmallAllocCost
    simp only [hm, hm16, ↓reduceIte]
    rw [hdiv]
  rw [heq]
  have hrow := List.all_eq_true.mp checkFineSmallAllocUnits1024_true
    (u / 32) (List.mem_range.mpr hhi)
  have hcell := List.all_eq_true.mp hrow (u % 32) (List.mem_range.mpr hlo)
  have hor := of_decide_eq_true hcell
  rw [hsplit] at hor
  rcases hor with hgt | hle
  · omega
  · exact hle

private theorem tryCloneSmallDelta_fine_le_20602_of_le_16384 {len : Nat} (h : len ≤ 16384) :
    tryCloneSmallDelta fineCostModel len ≤ 20602 := by
  unfold tryCloneSmallDelta rustAllocTightCum
  split
  · exact Nat.zero_le 20602
  · have hsm : len ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]
      exact Nat.le_trans h (by decide)
    simp only [hsm, ↓reduceIte]
    exact fineSmallAllocCost_le_20602_of_le_16384 h

/-- Fresh-Bob (`receiverChains = []`, `bobPqCap`) session-clone domain bundle. -/
structure FreshBobCloneDom (bobPqCap : Nat) (G : SessionGhost)
    (ses : Session (List (BitVec 8))) : Prop where
  rc_nil : ses.state.receiverChains = []
  gv : SessionGhostValid G ses
  dom : SessionCloneDom bobPqCap ses

def segCloneFreshBob16KTightCum : Nat := 36295

/-- Tight `segCloneTightCum` bound (`≤ 36,295` B) on `fineCostModel` under `FreshBobCloneDom` with `bobPqCap ≤ 16,384`.
-/
theorem segCloneTightCum_fine_freshBob16K_le {bobPqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hbob : FreshBobCloneDom bobPqCap G ses) (hpq : bobPqCap ≤ 16384) :
    segCloneTightCum fineCostModel G ses.state ≤ 36295 := by
  obtain ⟨hrc_nil, hgv, hdom⟩ := hbob
  obtain ⟨hloc_len, hrem_len, _, _, hsend_ok, hpend_len, hkyb_len, halice_eq, _⟩ :=
    ghostCloneValid_of_sessionGhostValid hgv
  obtain ⟨_, _, halice_dom, hkyb_cap, hpq_len⟩ := hdom
  unfold segCloneTightCum
  have b1 : tryCloneSmallDelta fineCostModel G.localIk.bytes.length ≤ 738 :=
    tryCloneSmallDelta_fine_le_738 (by omega)
  have b2 : tryCloneSmallDelta fineCostModel G.remoteIk.bytes.length ≤ 738 :=
    tryCloneSmallDelta_fine_le_738 (Nat.le_trans hrem_len (by decide))
  have b3 : rustAllocTightCum fineCostModel 32 ≤ 738 := by
    rw [rustAllocTightCum_fine_32]
  have b4 : (match G.sender, ses.state.senderChain with
      | some gs, some sc => chainCloneTightCum fineCostModel (senderChainAsProtoGhost gs sc)
      | _, _ => 0) ≤ 2214 := by
    rcases hsend_ok with ⟨h1, h2⟩ | ⟨gs, sc, h1, h2, hsrk, hpriv⟩
    · rw [h1, h2]; exact Nat.zero_le 2214
    · rw [h1, h2]
      exact senderChainCloneTightCum_fine_le (by omega) (by omega)
  have b5 : (if ses.state.receiverChains = [] then 0
      else rustAllocTightCum fineCostModel (104 * ses.state.receiverChains.length) +
        ((G.chains.zip ses.state.receiverChains).map (chainCloneTightCum fineCostModel)).sum) ≤
      0 + 0 := by
    simp only [hrc_nil, ↓reduceIte, Nat.le_refl]
  have b6 : tryCloneSmallDelta fineCostModel (optTailCloneLen G.pending) ≤ 738 :=
    tryCloneSmallDelta_fine_le_738 (Nat.le_trans hpend_len (by decide))
  have hkyb_le : optTailCloneLen G.kyber ≤ 2048 := by
    rw [hkyb_len]
    cases hk : ses.pendingKyberPreKey with
    | none => simp
    | some k => exact Nat.le_trans (hkyb_cap k hk) (by decide)
  have b7 : tryCloneSmallDelta fineCostModel (optTailCloneLen G.kyber) ≤ 9789 :=
    tryCloneSmallDelta_fine_le_9789_of_le_2048 hkyb_le
  have halice_le : G.alice.bytes.length ≤ 44 := by
    rw [halice_eq]; exact Nat.le_trans halice_dom (by decide)
  have b8 : tryCloneSmallDelta fineCostModel G.alice.bytes.length ≤ 738 :=
    tryCloneSmallDelta_fine_le_738 halice_le
  have b9 : tryCloneSmallDelta fineCostModel ses.state.pqRatchetState.length ≤ 20602 :=
    tryCloneSmallDelta_fine_le_20602_of_le_16384 (Nat.le_trans hpq_len hpq)
  have htot := add9_mid_aff_le b1 b2 b3 b4 b5 b6 b7 b8 b9 (by decide :
    738 + 738 + 738 + 2214 + 0 + 738 + 9789 + 738 + 20602 ≤ 36295)
  rw [Nat.add_zero] at htot
  exact htot

/-- Under `FreshBobCloneDom` with `bobPqCap ≤ 135,167`, `segCloneLarge` is `0`. -/
theorem segCloneLarge_fine_freshBob_eq_zero {bobPqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hbob : FreshBobCloneDom bobPqCap G ses) (hpq : bobPqCap ≤ 135167) :
    segCloneLarge fineCostModel G ses.state = 0 := by
  obtain ⟨hrc_nil, hgv, hdom⟩ := hbob
  obtain ⟨hloc_len, hrem_len, _, _, hsend_ok, hpend_len, hkyb_len, halice_eq, _⟩ :=
    ghostCloneValid_of_sessionGhostValid hgv
  obtain ⟨_, _, halice_dom, hkyb_cap, hpq_len⟩ := hdom
  have hsmall33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  unfold segCloneLarge
  have hloc : vecCloneLarge fineCostModel G.localIk.bytes.length = 0 :=
    vecCloneLarge_eq_zero_of_le fineCostModel (by rw [fineCostModel_smallMaxReq_eq]; omega)
  have hrem : vecCloneLarge fineCostModel G.remoteIk.bytes.length = 0 :=
    vecCloneLarge_eq_zero_of_le fineCostModel (by rw [fineCostModel_smallMaxReq_eq]; omega)
  have hroot : optLargeCost fineCostModel 32 = 0 := optLargeCost_fine_of_le (by decide)
  have hpend : vecCloneLarge fineCostModel (optTailCloneLen G.pending) = 0 :=
    vecCloneLarge_eq_zero_of_le fineCostModel (by rw [fineCostModel_smallMaxReq_eq]; omega)
  have hkyb_le : optTailCloneLen G.kyber ≤ 1569 := by
    rw [hkyb_len]
    cases hk : ses.pendingKyberPreKey with
    | none => simp
    | some k => exact hkyb_cap k hk
  have hkyb : vecCloneLarge fineCostModel (optTailCloneLen G.kyber) = 0 :=
    vecCloneLarge_eq_zero_of_le fineCostModel (by rw [fineCostModel_smallMaxReq_eq]; omega)
  have halice : vecCloneLarge fineCostModel G.alice.bytes.length = 0 :=
    vecCloneLarge_eq_zero_of_le fineCostModel
      (by rw [fineCostModel_smallMaxReq_eq, halice_eq]; omega)
  have hpq0 : vecCloneLarge fineCostModel ses.state.pqRatchetState.length = 0 :=
    vecCloneLarge_eq_zero_of_le fineCostModel
      (by rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans hpq_len hpq)
  simp only [hloc, hrem, hroot, hrc_nil, ↓reduceIte, hpend, hkyb, halice, hpq0]
  rcases hsend_ok with ⟨h1, h2⟩ | ⟨gs, sc, h1, h2, hsrk, hpriv⟩
  · rw [h1, h2]; rfl
  · rw [h1, h2]
    dsimp only
    rw [chainCloneLarge_sender_eq_zero hsmall33 sc hsrk hpriv]

theorem sessionClone_freshBob16K_fine_phaseCredit {bobPqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hbob : FreshBobCloneDom bobPqCap G ses) (hpq : bobPqCap ≤ 16384) :
    PhaseCreditSpec fineCostModel (SegCloneEnv G ses.state) 36295 0 0 208000 := by
  have hl0 : segCloneLarge fineCostModel G ses.state = 0 :=
    segCloneLarge_fine_freshBob_eq_zero hbob (Nat.le_trans hpq (by decide))
  have hr : segCloneMaxReq G ses.state ≤ 208000 :=
    Nat.le_trans (segCloneMaxReq_le_of_dom hbob.gv hbob.dom)
      (Nat.max_le.mpr ⟨Nat.le_refl 208000, Nat.le_trans hpq (by decide)⟩)
  exact (sessionClone_phaseCredit_tight fineCostModel_modelHyps G ses.state).mono
    (segCloneTightCum_fine_freshBob16K_le hbob hpq)
    (Nat.le_of_eq hl0)
    (Nat.le_of_eq hl0)
    hr

theorem phaseCreditSpec_segTailEnv_fine_488 :
    PhaseCreditSpec fineCostModel SegTailEnv 488 0 0 17 := by
  have ha := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight fineCostModel_modelHyps
    (req := 17) (al := 1) (by decide)
  have hc : rustAllocTightCum fineCostModel 17 ≤ 488 := by
    unfold rustAllocTightCum
    rw [fineCostModel_smallMaxReq_eq]
    decide
  have hl : optLargeCost fineCostModel 17 = 0 := optLargeCost_fine_of_le (by decide)
  rw [hl] at ha
  exact ((PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).seq
    (ha.mono hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 17))).mono
    (by decide) (by decide) (by decide) (by decide)

theorem phaseCreditSpec_fromFEnv_fine_488 :
    PhaseCreditSpec fineCostModel FromFEnv 488 0 0 17 :=
  (phaseCreditSpec_segTailEnv_fine_488.seq
    (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc)).mono
    (by decide) (by decide) (by decide) (by decide)

theorem phaseCreditSpec_fromMEnv_fine_8674 :
    PhaseCreditSpec fineCostModel FromMEnv 8674 0 0 192 :=
  (phaseCreditSpec_growOneSpe_zero_fine_tight.seq phaseCreditSpec_fromFEnv_fine_488).mono
    (by decide) (by decide) (by decide) (by decide)

theorem phaseCreditSpec_fromVPostTdEnv_fine_8674 :
    PhaseCreditSpec fineCostModel FromVPostTdEnv 8674 0 0 192 :=
  ((PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).or
    phaseCreditSpec_fromMEnv_fine_8674).mono
    (by decide) (by decide) (by decide) (by decide)

end TightFineCloneBounds

end LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds

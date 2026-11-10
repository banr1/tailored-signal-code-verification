/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
public import LibsignalBinary.Specifications.LibsignalPublicApi

/-!
# Session Record Representation and Canonical Ghost Bridges

Relates the `E2E.Record` and `LibsignalPublicApiRepr` session-record predicates and shows
that any heap-resident session or record (`sessionStateReprAt`, `sessionRecordAt` under
`InMemRecOk`) carries a canonical ghost (`CanonSession`, `CanonRecord`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.InMem.SessionStoreImpl

open Arm64 ProofLib
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record (RecordPqEmpty RecordRepr InScope)
open CryptoVerification.E2E.Record.DeserializeGeneral (SessionScope DeserializeScope)
open CryptoVerification.E2E.Record.Serialization (CanonChain CanonSender CanonPending CanonSession CanonCur CanonRecord)

/-! ## `Record` and `LibsignalPublicApiRepr` Equivalence -/

def toRecordGhost (g : CryptoVerification.LibsignalPublicApiRepr.RecordGhost) :
    CryptoVerification.E2E.Record.RecordGhost :=
  ⟨g.prevCap, g.prevPtr, g.cur⟩

def ofRecordGhost (g : CryptoVerification.E2E.Record.RecordGhost) :
    CryptoVerification.LibsignalPublicApiRepr.RecordGhost :=
  ⟨g.prevCap, g.prevPtr, g.cur⟩

@[simp]
theorem toRecordGhost_ofRecordGhost (g : CryptoVerification.E2E.Record.RecordGhost) :
    toRecordGhost (ofRecordGhost g) = g := by
  cases g; rfl

@[simp]
theorem ofRecordGhost_toRecordGhost (g : CryptoVerification.LibsignalPublicApiRepr.RecordGhost) :
    ofRecordGhost (toRecordGhost g) = g := by
  cases g; rfl

theorem optU32Rel_eq :
    CryptoVerification.E2E.Record.OptU32Rel =
      CryptoVerification.LibsignalPublicApiRepr.OptU32Rel :=
  rfl

theorem pendingRel_eq :
    CryptoVerification.E2E.Record.PendingRel =
      CryptoVerification.LibsignalPublicApiRepr.PendingRel :=
  rfl

theorem kyberRel_eq :
    CryptoVerification.E2E.Record.KyberRel =
      CryptoVerification.LibsignalPublicApiRepr.KyberRel :=
  rfl

theorem record_sessionAt_eq (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) :
    CryptoVerification.E2E.Record.sessionStateReprAt A ss G s =
      CryptoVerification.LibsignalPublicApiRepr.sessionStateReprAt A ss G s :=
  rfl

theorem record_sessionRecordAt_eq (A : RustAlloc) (r : BitVec 64)
    (g : CryptoVerification.LibsignalPublicApiRepr.RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) :
    CryptoVerification.E2E.Record.sessionRecordAt A r (toRecordGhost g) rec =
      CryptoVerification.LibsignalPublicApiRepr.sessionRecordAt A r g rec := by
  cases g; rfl

theorem record_recordInScope_eq :
    CryptoVerification.E2E.Record.RecordInScope =
      CryptoVerification.LibsignalPublicApi.RecordInScope :=
  rfl

/-! ## Canonical Ghost Extraction -/

theorem eq_serialize_of_deserialize {v : List (BitVec 8)} {k : PublicKey}
    (hd : PublicKey.deserialize v = .ok k) (hlen : v.length = 33) :
    v = k.serialize := by
  cases v with
  | nil => simp [PublicKey.deserialize] at hd
  | cons t rest =>
    simp only [PublicKey.deserialize] at hd
    split at hd
    · cases hd
    · rename_i ht
      rw [Classical.not_not] at ht
      split at hd
      · obtain rfl := Except.ok.inj hd
        simp only [List.length_cons] at hlen
        simp [PublicKey.serialize, ht, List.take_of_length_le (by omega : rest.length ≤ 32)]
      · cases hd

theorem sepConj_left {P Q : SepProp} {hp : Heap} (h : (P ∗ Q) hp) : ∃ h1, P h1 :=
  SepProp.holds_sepConj_left h

theorem sepConj_right {P Q : SepProp} {hp : Heap} (h : (P ∗ Q) hp) : ∃ h2, Q h2 := by
  rw [sepConj_comm] at h
  exact SepProp.holds_sepConj_left h

theorem canonChain_of_chainAt {A : RustAlloc} {gc : ChainGhost × ReceiverChain} {a : BitVec 64}
    {hp : Heap} (h : chainAt A gc a hp) : CanonChain gc := by
  unfold chainAt at h
  rw [pure_sepConj] at h
  obtain ⟨⟨hd, _, _, hlen, hpriv⟩, _⟩ := h
  exact ⟨eq_serialize_of_deserialize hd hlen, hpriv⟩

theorem canonSender_of_optSenderChainAt {A : RustAlloc} {a : BitVec 64}
    {og : Option SenderChainGhost} {os : Option SenderChain}
    {hp : Heap} (h : optSenderChainAt A a og os hp) : CanonSender og os := by
  match og, os with
  | none, none => trivial
  | some g, some sc =>
    dsimp only [optSenderChainAt] at h
    rw [pure_sepConj] at h
    obtain ⟨⟨hd, hpriv, _, hlen⟩, _⟩ := h
    exact ⟨eq_serialize_of_deserialize hd hlen, hpriv⟩
  | none, some _ =>
    dsimp only [optSenderChainAt] at h
    rw [← sepConj_emp ⌜False⌝] at h
    exact False.elim (SepProp.holds_pure_sepConj h).1
  | some _, none =>
    dsimp only [optSenderChainAt] at h
    rw [← sepConj_emp ⌜False⌝] at h
    exact False.elim (SepProp.holds_pure_sepConj h).1

theorem canonChains_of_arrayAt {A : RustAlloc} {stride : Nat}
    : ∀ (xs : List (ChainGhost × ReceiverChain)) (base : BitVec 64) {hp : Heap},
      arrayAt (chainAt A) stride base xs hp → ∀ gc ∈ xs, CanonChain gc
  | [], _, _, _, _, hmem => nomatch hmem
  | x :: xs, base, _, h, gc, hmem => by
    dsimp only [arrayAt] at h
    rcases List.mem_cons.mp hmem with rfl | htail
    · obtain ⟨_, hp1⟩ := sepConj_left h
      exact canonChain_of_chainAt hp1
    · obtain ⟨_, hp2⟩ := sepConj_right h
      exact canonChains_of_arrayAt xs (base + BitVec.ofNat 64 stride) hp2 gc htail

theorem canonChains_of_vecAt {A : RustAlloc} {stride align : Nat}
    {v cap ptr : BitVec 64} {xs : List (ChainGhost × ReceiverChain)}
    {hp : Heap} (h : vecAt A stride align (chainAt A) v cap ptr xs hp) :
    ∀ gc ∈ xs, CanonChain gc := by
  unfold vecAt at h
  obtain ⟨_, hp2⟩ := sepConj_right h
  unfold vecBuf at hp2
  rw [pure_sepConj] at hp2
  obtain ⟨⟨hlen, _, _⟩, hp2⟩ := hp2
  split at hp2
  · rename_i hcap
    subst hcap
    have hnil : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hnil
    intro _ hmem
    nomatch hmem
  · obtain ⟨_, hp3⟩ := sepConj_right hp2
    obtain ⟨_, hp4⟩ := sepConj_left hp3
    exact canonChains_of_arrayAt xs ptr hp4

/-- Any `SessionStructure` satisfying `sessionStateReprAt` has canonical ghost `CanonSession G s`. -/
theorem canonSession_of_sessionAt (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) :
    ∀ m, sessionStateReprAt A ss G s m → CanonSession G s := by
  intro m hm
  unfold sessionStateReprAt at hm
  rw [pure_sepConj] at hm
  obtain ⟨⟨hPendRel, _, _, _, _⟩, hm⟩ := hm
  unfold sessionStateAt at hm
  rw [pure_sepConj] at hm
  obtain ⟨⟨hLocal, hRemote, hChainsLen, _, _, hLocalLen, hRemoteLen⟩, hm⟩ := hm
  obtain ⟨_, hm⟩ := sepConj_right hm
  obtain ⟨_, hm⟩ := sepConj_right hm
  obtain ⟨_, hm⟩ := sepConj_right hm
  obtain ⟨_, hmChains⟩ := sepConj_left hm
  obtain ⟨_, hm⟩ := sepConj_right hm
  obtain ⟨_, hm⟩ := sepConj_right hm
  obtain ⟨_, hm⟩ := sepConj_right hm
  obtain ⟨_, hmSender⟩ := sepConj_left hm
  refine ⟨eq_serialize_of_deserialize hLocal hLocalLen, ?_,
    canonSender_of_optSenderChainAt hmSender, hChainsLen,
    canonChains_of_vecAt hmChains, ?_⟩
  · cases hrem : s.state.remoteIdentity with
    | none =>
      rw [hrem] at hRemote
      simp [hRemote]
    | some ik =>
      rw [hrem] at hRemote hRemoteLen
      simp [IdentityKey.serialize, eq_serialize_of_deserialize hRemote (hRemoteLen rfl)]
  · cases hgp : G.pending <;> cases hsp : s.pendingPreKey <;>
      simp only [hgp, hsp, PendingRel, CanonPending] at hPendRel ⊢
    exact eq_serialize_of_deserialize hPendRel.1 hPendRel.2.2.2.2

theorem canonSession_of_satisfies_sessionAt (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) :
    ∀ m : Memory, (m ⊨ sessionStateReprAt A ss G s) → CanonSession G s := by
  intro _ hm
  have hsat := Satisfies.mono
    (ProofLib.Entails.extract_heap_fact (canonSession_of_sessionAt A ss G s)) hm
  rw [satisfies_pure_sepConj] at hsat
  exact hsat.1

/-- Store-side record invariant: in-scope `SessionRecord` with empty PQ state and present current session. -/
def InMemRecOk (r : SessionRecord (List (BitVec 8))) : Prop :=
  CryptoVerification.E2E.Record.RecordInScope r ∧
  CryptoVerification.E2E.Record.RecordPqEmpty r ∧ r.currentSession.isSome

theorem InMemRecOk.recordInScope {r : SessionRecord (List (BitVec 8))} (h : InMemRecOk r) :
    RecordInScope r :=
  h.1

theorem InMemRecOk.of_deserializeScope {r : SessionRecord (List (BitVec 8))} (h : DeserializeScope r) :
    InMemRecOk r := by
  obtain ⟨⟨hIn, hPq, _⟩, s, hs, _⟩ := h
  exact ⟨hIn, hPq, by rw [hs]; rfl⟩

theorem canonRecord_of_sessionRecordAt_some (A : RustAlloc) (a : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (hSome : r.currentSession.isSome) :
    ∀ m, sessionRecordAt A a g r m → CanonRecord (toRecordGhost g) r := by
  intro m hm
  unfold sessionRecordAt at hm
  obtain ⟨_, hcur⟩ := sepConj_right hm
  obtain ⟨s, hr⟩ := Option.isSome_iff_exists.mp hSome
  rw [hr] at hcur
  cases hg : g.cur with
  | none =>
    rw [hg] at hcur
    dsimp only at hcur
    rw [← sepConj_emp ⌜False⌝] at hcur
    exact False.elim (SepProp.holds_pure_sepConj hcur).1
  | some G =>
    rw [hg] at hcur
    dsimp only at hcur
    unfold CanonRecord CanonCur toRecordGhost
    dsimp only
    rw [hg, hr]
    exact canonSession_of_sessionAt A (a + 0x18#64) G s _ hcur

/-- Any `SessionRecord` satisfying `sessionRecordAt` and `InMemRecOk` has canonical ghost `CanonRecord`. -/
theorem canonRecord_of_sessionRecordAt (A : RustAlloc) (a : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (hOk : InMemRecOk r) :
    ∀ m, sessionRecordAt A a g r m → CanonRecord (toRecordGhost g) r :=
  canonRecord_of_sessionRecordAt_some A a g r hOk.2.2

abbrev canonRecord_of_inMemRecOk := canonRecord_of_sessionRecordAt

end CryptoVerification.E2E.InMem.SessionStoreImpl

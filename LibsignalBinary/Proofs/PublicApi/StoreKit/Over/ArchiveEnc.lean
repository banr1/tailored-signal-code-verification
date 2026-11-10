/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefs
public import LibsignalBinary.Proofs.E2E.RecordX.Scope
public import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import LibsignalBinary.Specifications.AsmConstants

/-!
# Canonical Encoding and Length Bounds for Archived Sessions

Bridges the memory-level archived encoding `encSessionMem (clearPendingGhost G) (clearPending sess)`
to `Record.encSession` and `encStateUnderExtras`:
* `canonSession_of_satisfies_sessionAt`: `sessionStateReprAt A ss G s` directly entails
  `CanonSession G s` (33-byte serialized `PublicKey`s and empty receiver private-key vectors);
* `encSessionMem_clearPending_sessionOfX_eq`: equates `encSessionMem` on `clearPending` with
  `encStateUnderExtras x { g.session with pendingPreKey := false }`;
* `encStateX_clearPending_length_lt_of_wfPq`: bounds the cleared encoding length below `2 ^ 31`
  under `PqxdhPartyInSpecDomain`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.RecordX
open CryptoVerification.SignalSession

/-! ## 33-Byte `PublicKey.deserialize` Canonicity -/

/-- Any 33-byte list accepted by `PublicKey.deserialize` equals `pk.serialize` (`0x05 ‖ pk.bytes`). -/
theorem publicKey_eq_serialize_of_deserialize_len33 {bs : List (BitVec 8)} {pk : PublicKey}
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

/-- Same for `IdentityKey`: `ik.serialize = ik.publicKey.serialize`. -/
theorem identityKey_eq_serialize_of_deserialize_len33 {bs : List (BitVec 8)} {ik : IdentityKey}
    (hd : PublicKey.deserialize bs = .ok ik.publicKey) (hl : bs.length = 33) :
    bs = ik.serialize :=
  publicKey_eq_serialize_of_deserialize_len33 hd hl

/-! ## Extracting `CanonSession` from `sessionStateReprAt` -/

theorem canonPending_of_pendingRel {og : Option TailVecGhost} {op : Option PendingPreKey}
    (h : PendingRel og op) : CanonPending og op := by
  match og, op with
  | none, none => trivial
  | some g, some p =>
    obtain ⟨hd, _, _, _, hl⟩ := h
    exact publicKey_eq_serialize_of_deserialize_len33 hd hl
  | none, some _ => exact False.elim h
  | some _, none => exact False.elim h

theorem canonChain_of_satisfies_chainAt {A : RustAlloc} {gc : ChainGhost × ReceiverChain}
    {a : BitVec 64} {m : Memory} (hm : m ⊨ chainAt A gc a) : CanonChain gc := by
  unfold chainAt at hm
  have hpure := Satisfies.of_sep_left hm
  rw [satisfies_pure] at hpure
  obtain ⟨hd, _, _, hl, hpriv⟩ := hpure
  exact ⟨publicKey_eq_serialize_of_deserialize_len33 hd hl, hpriv⟩

private theorem canonChains_of_satisfies_arrayAt {A : RustAlloc} :
    ∀ (xs : List (ChainGhost × ReceiverChain)) (ptr : BitVec 64) (m : Memory),
      m ⊨ arrayAt (chainAt A) (asm% chainSize) ptr xs →
      ∀ gc ∈ xs, CanonChain gc
  | [], _, _, _, _, hmem => by simp at hmem
  | gc :: rest, ptr, m, hm, gc', hmem => by
    unfold arrayAt at hm
    rcases List.mem_cons.mp hmem with rfl | hrest
    · exact canonChain_of_satisfies_chainAt (Satisfies.of_sep_left hm)
    · exact canonChains_of_satisfies_arrayAt rest _ _ (Satisfies.of_sep_right hm) gc' hrest

private theorem canonChains_of_satisfies_vecAt {A : RustAlloc}
    {v cap ptr : BitVec 64} {xs : List (ChainGhost × ReceiverChain)} {m : Memory}
    (hm : m ⊨ vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A) v cap ptr xs) :
    ∀ gc ∈ xs, CanonChain gc := by
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
    exact canonChains_of_satisfies_arrayAt xs ptr _ harr

theorem canonSender_of_satisfies_optSenderChainAt {A : RustAlloc} {a : BitVec 64}
    {og : Option SenderChainGhost} {os : Option SenderChain} {m : Memory}
    (hm : m ⊨ optSenderChainAt A a og os) : CanonSender og os := by
  match og, os with
  | none, none => trivial
  | some g, some sc =>
    unfold optSenderChainAt at hm
    have hpure := Satisfies.of_sep_left hm
    rw [satisfies_pure] at hpure
    obtain ⟨hd, hpriv, _, hl⟩ := hpure
    exact ⟨publicKey_eq_serialize_of_deserialize_len33 hd hl, hpriv⟩
  | none, some _ =>
    unfold optSenderChainAt at hm
    rw [satisfies_pure] at hm
    exact False.elim hm
  | some _, none =>
    unfold optSenderChainAt at hm
    rw [satisfies_pure] at hm
    exact False.elim hm

/-- Every in-memory `sessionStateReprAt` satisfies `CanonSession G s` without extra assumptions. -/
theorem canonSession_of_satisfies_sessionAt {A : RustAlloc} {ss : BitVec 64}
    {G : SessionGhost} {s : Session (List (BitVec 8))} {m : Memory} {R : SepProp}
    (hm : m ⊨ sessionStateReprAt A ss G s ∗ R) : CanonSession G s := by
  have hsess := Satisfies.of_sep_left hm
  unfold sessionStateReprAt at hsess
  have hp_sess := Satisfies.of_sep_left hsess
  rw [satisfies_pure] at hp_sess
  have hss := Satisfies.of_sep_right hsess
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
  refine ⟨identityKey_eq_serialize_of_deserialize_len33 hloc_d hloc_l, ?_,
    canonSender_of_satisfies_optSenderChainAt hsender_sat,
    hch_len, canonChains_of_satisfies_vecAt hchains_sat,
    canonPending_of_pendingRel hp_sess.1⟩
  cases hri : s.state.remoteIdentity with
  | none =>
    rw [hri] at hrem_d
    simpa using hrem_d
  | some ik =>
    rw [hri] at hrem_d hrem_l
    simpa using identityKey_eq_serialize_of_deserialize_len33 hrem_d (hrem_l rfl)

/-- Clearing `pending_pre_key` and `pending_kyber_pre_key` preserves `CanonSession`. -/
theorem canonSession_clearPending {G : SessionGhost} {s : Session (List (BitVec 8))}
    (h : CanonSession G s) :
    CanonSession (clearPendingGhost G) (clearPending s) := by
  obtain ⟨hl, hr, hs, hlen, hc, _⟩ := h
  exact ⟨hl, hr, hs, hlen, hc, trivial⟩

/-- Direct equality `encSessionMem (clearPendingGhost G) (clearPending s) = encSession (clearPending s)`
from `m ⊨ sessionStateReprAt A ss G s ∗ R`. -/
theorem encSessionMem_clearPending_eq_of_sessionAt {A : RustAlloc} {ss : BitVec 64}
    {G : SessionGhost} {s : Session (List (BitVec 8))} {m : Memory} {R : SepProp}
    (hm : m ⊨ sessionStateReprAt A ss G s ∗ R) :
    encSessionMem (clearPendingGhost G) (clearPending s) = encSession (clearPending s) :=
  encSessionMem_eq_of_canon (clearPendingGhost G) (clearPending s)
    (canonSession_clearPending (canonSession_of_satisfies_sessionAt hm))

/-! ## `encStateUnderExtras` Bridge and Length Bounds -/

/-- On `sessionOfX (fun _ => x) g`, `encSession ∘ clearPending` equals
`encStateUnderExtras x { g.session with pendingPreKey := false }`. -/
theorem encSession_clearPending_sessionOfX
    (x : RecordExtras) (g : GhostState (List (BitVec 8))) :
    encSession (clearPending (sessionOfX (fun _ => x) g)) =
      encStateUnderExtras x { g.session with pendingPreKey := false } :=
  rfl

/-- Combined memory-to-`encStateUnderExtras` bridge from `sessionStateReprAt` on `sessionOfX (fun _ => x) g`. -/
theorem encSessionMem_clearPending_sessionOfX_eq {A : RustAlloc} {ss : BitVec 64}
    {G : SessionGhost} {x : RecordExtras} {g : GhostState (List (BitVec 8))}
    {m : Memory} {R : SepProp}
    (hm : m ⊨ sessionStateReprAt A ss G (sessionOfX (fun _ => x) g) ∗ R) :
    encSessionMem (clearPendingGhost G) (clearPending (sessionOfX (fun _ => x) g)) =
      encStateUnderExtras x { g.session with pendingPreKey := false } := by
  rw [encSessionMem_clearPending_eq_of_sessionAt hm, encSession_clearPending_sessionOfX]

/-- Clearing `pendingPreKey` does not increase the length of `encStateUnderExtras`. -/
theorem encStateX_clearPending_length_le
    (x : RecordExtras) (st : SessionState (List (BitVec 8))) :
    (encStateUnderExtras x { st with pendingPreKey := false }).length ≤ (encStateUnderExtras x st).length := by
  unfold encStateUnderExtras
  cases st.pendingPreKey
  · simp
  · simp only [Bool.false_eq_true, ↓reduceIte, E2E.msgField,
      List.length_nil, List.length_append]
    omega

/-- The pending-cleared `encStateUnderExtras` is strictly shorter than `encodeRecordUnderExtras (fun _ => x) g`. -/
theorem encStateX_clearPending_length_lt_encodeRecordX
    (x : RecordExtras) (g : GhostState (List (BitVec 8))) :
    (encStateUnderExtras x { g.session with pendingPreKey := false }).length <
      (encodeRecordUnderExtras (fun _ => x) g).length := by
  have hle := encStateX_clearPending_length_le x g.session
  unfold encodeRecordUnderExtras E2E.msgField E2E.lenField encodeKey
  have hk_pos : 0 < (encodeVarint (BitVec.ofNat 64 (1 * 8 + WireType.lengthDelimited.toNat))).length := by
    decide
  dsimp only
  simp only [List.length_append]
  omega

/-- Under `PqxdhPartyInSpecDomain W st` with `st.session = some (x, g)`, the archived session encoding has length
`< 2 ^ 31` (and `< 2 ^ 32`, discharging `archiveOverGenSpec` / `promoteOverGenSpec`). -/
theorem encStateX_clearPending_length_lt_of_wfPq
    {W : PEParams} {st : PqParty} {x : RecordExtras} {g : GhostState (List (BitVec 8))}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g)) :
    (encStateUnderExtras x { g.session with pendingPreKey := false }).length < 2 ^ 31 ∧
    (encStateUnderExtras x { g.session with pendingPreKey := false }).length < 2 ^ 32 := by
  have hrec_lt : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 := (hwf.1 x g hsess).2.2
  have hlt31 : (encStateUnderExtras x { g.session with pendingPreKey := false }).length < 2 ^ 31 :=
    Nat.lt_trans (encStateX_clearPending_length_lt_encodeRecordX x g) hrec_lt
  exact ⟨hlt31, Nat.lt_trans hlt31 (by decide)⟩

theorem encSessionMem_clearPending_length_lt_of_wfPq
    {W : PEParams} {st : PqParty} {x : RecordExtras} {g : GhostState (List (BitVec 8))}
    {A : RustAlloc} {ss : BitVec 64} {G : SessionGhost} {m : Memory} {R : SepProp}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hm : m ⊨ sessionStateReprAt A ss G (sessionOfX (fun _ => x) g) ∗ R) :
    (encSessionMem (clearPendingGhost G) (clearPending (sessionOfX (fun _ => x) g))).length < 2 ^ 32 := by
  rw [encSessionMem_clearPending_sessionOfX_eq hm]
  exact (encStateX_clearPending_length_lt_of_wfPq hwf hsess).2

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

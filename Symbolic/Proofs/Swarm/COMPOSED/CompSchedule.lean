/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.COMPOSED.CompClosed
import all DY.ALaCarte.Basic
import all DY.ALaCarte.Ordering
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Trace.BaseAttackerKnowledge
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
import Symbolic.Proofs.Swarm.COMPOSED.CompLineage

/-!
# Composed Key-Schedule Invariant and Session Uniqueness

Defines the step-1 anchored root-key and chain-root schedule relations (`CompRkSteps`,
`CompChainRootFrom1`), the session-origin predicate `CompSessionAt`, and the composed key-schedule
invariant `CompScheduleInv`, proving its preservation on all reachable composed traces.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse DY.DiffieHellman DY.KdfExtract DY.Concat DY.Literal DY.SymEnc DY.Trunc
open DY.X25519 DY.Spqr DY.TrWire DY.PQKem DY.Signature
open DY.Libsignal.TripleRatchet DY.Libsignal.TripleRatchet DY.Libsignal.TripleRatchet.Cheval
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED.CompTermAlgebra Symbolic.Swarm.COMPOSED.CompTrace

/-! ## Role Parity and Diffie-Hellman Injectivity -/

/-- Parity of `rIdx` for a given role: `1` for initiator (`aliceStart`), `0` for responder (`bobStart`). -/
def roleParity (initiator : Bool) : Nat := if initiator then 1 else 0

theorem dh_right_inj {p₁ p₂ sk : Bytes} (h : dh p₁ sk = dh p₂ sk) : p₁ = p₂ := by
  have hpack₂ := Bytes.pack_view? DiffieHellman.DhPk.SubF p₂
  rcases hp₂ : p₂.view? DiffieHellman.DhPk.SubF with _ | ⟨⟨a⟩⟩
  · have hpack₁ := Bytes.pack_view? DiffieHellman.DhPk.SubF p₁
    rcases hp₁ : p₁.view? DiffieHellman.DhPk.SubF with _ | ⟨⟨b⟩⟩
    · have hview := congrArg (fun x : Bytes => x.view? DiffieHellman.Dh.SubF) h
      dsimp only [dh, CanDH.dh] at hview; rw [hp₁, hp₂] at hview
      simp only [BytesView.view_pack, Option.some.injEq, DiffieHellman.Dh.SubF.mk.injEq] at hview; exact hview.1
    · rw [hp₁] at hpack₁; have hp₁_eq : p₁ = dhPk b := hpack₁.symm; subst hp₁_eq
      rcases dh_eq_dh_dhPk_cases h.symm with ⟨hp₂_eq, _⟩ | ⟨hp₂_eq, _⟩ <;>
        (rw [hp₂_eq] at hp₂; simp only [dhPk, CanDH.dhPk, BytesView.view_pack] at hp₂; cases hp₂)
  · rw [hp₂] at hpack₂; have hp₂_eq : p₂ = dhPk a := hpack₂.symm; subst hp₂_eq
    rcases dh_eq_dh_dhPk_cases h with ⟨rfl, _⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem dh_left_inj {p sk₁ sk₂ : Bytes} (h : dh p sk₁ = dh p sk₂) : sk₁ = sk₂ :=
  Classical.byContradiction fun hne => let ⟨hp₁, hp₂⟩ := dh_eq_of_sk_ne hne h; hne (dhPk_inj (hp₂.symm.trans hp₁))

/-! ## Step-1 Anchored Schedule Relations -/

/-- Step-1 anchored root-key derivation relation. -/
inductive CompRkSteps (dh₁ : Bytes) : Nat → Bytes → Bytes → Prop
  | zero (rk₀ : Bytes) : CompRkSteps dh₁ 0 rk₀ rk₀
  | step_one (rk₀ : Bytes) : CompRkSteps dh₁ 1 rk₀ (kdfRk rk₀ dh₁).1
  | step_succ {k : Nat} {rk₀ rk₁ pk sk : Bytes} :
      CompRkSteps dh₁ (k + 1) rk₀ rk₁ → CompRkSteps dh₁ (k + 2) rk₀ (createChain rk₁ pk sk).1

theorem CompRkSteps.saltDepth_eq {dh₁ : Bytes} {d : Nat} {rk₀ rk : Bytes}
    (h : CompRkSteps dh₁ d rk₀ rk) : saltDepth rk = saltDepth rk₀ + 2 * d := by
  induction h with
  | zero => simp
  | step_one => simp
  | step_succ _ ih => simp only [saltDepth_createChain_fst, ih]; omega

private theorem CompRkSteps.pos_inj_aux {dh₁ dh₂ rk₀₁ rk₀₂ rk : Bytes} {d : Nat}
    (hd : 1 ≤ d) (h₁ : CompRkSteps dh₁ d rk₀₁ rk) (h₂ : CompRkSteps dh₂ d rk₀₂ rk) :
    rk₀₁ = rk₀₂ ∧ dh₁ = dh₂ := by
  induction h₁ generalizing dh₂ rk₀₂ with
  | zero => omega
  | step_one => generalize hrk : (kdfRk _ _).1 = rk' at h₂; cases h₂ with | step_one => exact kdfRk_fst_inj hrk
  | @step_succ k _ rk₁ pk sk h₁_prev ih =>
    generalize hrk : (createChain rk₁ pk sk).1 = rk' at h₂
    cases h₂ with | step_succ h₂_prev => obtain ⟨hrk₁, _⟩ := createChain_fst_inj hrk; exact ih (by omega) (hrk₁ ▸ h₂_prev)

/-- Positive-depth `CompRkSteps` derivations producing the same root key from `pqxdhKdf` root keys
have equal step count, input keying material, and initial DH output. -/
theorem CompRkSteps.pos_inj {dh₁ dh₂ ikm₁ ikm₂ rk : Bytes} {d₁ d₂ : Nat}
    (hd₁ : 1 ≤ d₁) (h₁ : CompRkSteps dh₁ d₁ (pqxdhKdf ikm₁).rk rk)
    (h₂ : CompRkSteps dh₂ d₂ (pqxdhKdf ikm₂).rk rk) : d₁ = d₂ ∧ ikm₁ = ikm₂ ∧ dh₁ = dh₂ := by
  have hd_eq : d₁ = d₂ := by
    have hs₁ := h₁.saltDepth_eq; have hs₂ := h₂.saltDepth_eq; simp only [saltDepth_pqxdhKdf_rk] at hs₁ hs₂; omega
  subst hd_eq; obtain ⟨hrk₀, hdh⟩ := h₁.pos_inj_aux hd₁ h₂; exact ⟨rfl, pqxdhKdf_rk_inj hrk₀, hdh⟩

theorem isChainRoot_kdfRk_snd (rk dhOut : Bytes) : IsChainRoot (kdfRk rk dhOut).2 :=
  fun x h => hkdfBlock2_ne_kdfCk_fst _ _ x h

/-- Step-1 anchored chain-root derivation relation. -/
def CompChainRootFrom1 (dh₁ ikm : Bytes) (m : Nat) (ck₀ : Bytes) : Prop :=
  match m with
  | 0 => ck₀ = (pqxdhKdf ikm).ck
  | 1 => ck₀ = (kdfRk (pqxdhKdf ikm).rk dh₁).2
  | k + 2 => ∃ rk pk sk, CompRkSteps dh₁ (k + 1) (pqxdhKdf ikm).rk rk ∧ ck₀ = (createChain rk pk sk).2

theorem CompChainRootFrom1.isChainRoot {dh₁ ikm : Bytes} {m : Nat} {ck₀ : Bytes}
    (h : CompChainRootFrom1 dh₁ ikm m ck₀) : IsChainRoot ck₀ := by
  rcases m with _ | _ | k
  · subst h; exact isChainRoot_pqxdhKdf_ck ikm
  · subst h; exact isChainRoot_kdfRk_snd _ _
  · obtain ⟨rk, pk, sk, _, rfl⟩ := h; exact isChainRoot_createChain_snd rk pk sk

theorem CompChainRootFrom1.saltDepth_eq {dh₁ ikm : Bytes} {m : Nat} {ck₀ : Bytes}
    (h : CompChainRootFrom1 dh₁ ikm m ck₀) : saltDepth ck₀ = 2 + 2 * m := by
  rcases m with _ | _ | k
  · subst h; simp
  · subst h; simp
  · obtain ⟨rk, pk, sk, hrk, rfl⟩ := h; rw [saltDepth_createChain_snd, hrk.saltDepth_eq, saltDepth_pqxdhKdf_rk]; omega

theorem CompChainRootFrom1.eq_iff {dh₁ dh₂ ikm₁ ikm₂ ck₀ : Bytes} {m₁ m₂ : Nat}
    (h₁ : CompChainRootFrom1 dh₁ ikm₁ m₁ ck₀) (h₂ : CompChainRootFrom1 dh₂ ikm₂ m₂ ck₀) :
    m₁ = m₂ ∧ ikm₁ = ikm₂ ∧ (1 ≤ m₁ → dh₁ = dh₂) := by
  have hm : m₁ = m₂ := by have hd₁ := h₁.saltDepth_eq; have hd₂ := h₂.saltDepth_eq; omega
  subst hm; refine ⟨rfl, ?_⟩; rcases m₁ with _ | _ | k
  · dsimp [CompChainRootFrom1] at h₁ h₂; exact ⟨pqxdhKdf_ck_inj (h₁.symm.trans h₂), fun h => by omega⟩
  · dsimp [CompChainRootFrom1] at h₁ h₂; obtain ⟨hrk, hdh⟩ := kdfRk_snd_inj (h₁.symm.trans h₂)
    exact ⟨pqxdhKdf_rk_inj hrk, fun _ => hdh⟩
  · obtain ⟨rk₁, pk₁, sk₁, hrk₁, hck₁⟩ := h₁; obtain ⟨rk₂, pk₂, sk₂, hrk₂, hck₂⟩ := h₂
    obtain ⟨hrk_eq, _⟩ := createChain_snd_inj (hck₁.symm.trans hck₂)
    obtain ⟨_, hikm, hdh⟩ := hrk₁.pos_inj (Nat.succ_le_succ (Nat.zero_le k)) (hrk_eq ▸ hrk₂)
    exact ⟨hikm, fun _ => hdh⟩

/-! ## Session-Origin Predicate and Session Uniqueness -/

/-- Concrete session-origin invariant `CompSessionAt tr s doneIdx ikm dh1`. -/
def CompSessionAt (tr : ExecTrace) (s : SessionInfo) (doneIdx : Nat) (ikm dh₁ : Bytes) : Prop :=
  tr.EventLogged (ComposedEvent.HandshakeSession s doneIdx) ∧ HandshakeKeysAt tr doneIdx (pqxdhKdf ikm) ∧
  if s.initiator then
    ∃ a b t₀ ikA ikB spk pqpk opk ct dh1 dh2 dh4,
      RandAt tr t₀ 32 ∧ RandAt tr (t₀ + 1) 32 ∧ RandAt tr (t₀ + 2) 32 ∧ doneIdx = t₀ + 5 ∧
      tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk
        (DiffieHellman.dhPk (mkRand t₀ 32)) ct (pqxdhKdf ikm)) doneIdx ∧
      s = { sid := Concat.concat (DiffieHellman.dhPk (mkRand (t₀ + 2) 32)) (pqxdhKdf ikm).rk,
            initiator := true, me := a, peer := b } ∧
      ikm = pqxdhIkm dh1 dh2 (DiffieHellman.dh (DY.X25519.normalizeX25519Key spk) (mkRand t₀ 32)) dh4
        (PQKem.kemEncap pqpk (mkRand (t₀ + 1) 32)).2 ∧
      dh₁ = DiffieHellman.dh (DY.X25519.normalizeX25519Key spk) (mkRand (t₀ + 2) 32)
  else
    ∃ b a t_spk ikB ikA spkSk pqsk opk ek ct dh4 e,
      spkSk = mkRand t_spk 32 ∧ RandAt tr (t_spk + 1) 64 ∧ ikB ≠ spkSk ∧
      tr.EventLoggedAt (PQXDHEvent.BobDone b a (DiffieHellman.dhPk ikB) ikA
        (DiffieHellman.dhPk spkSk) (PQKem.kemPk pqsk) opk ek ct (pqxdhKdf ikm)) doneIdx ∧
      s.me = b ∧ s.peer = a ∧
      ikm = pqxdhIkm (DiffieHellman.dh (DY.X25519.normalizeX25519Key ikA) spkSk)
        (DiffieHellman.dh (DY.X25519.normalizeX25519Key ek) ikB)
        (DiffieHellman.dh (DY.X25519.normalizeX25519Key ek) spkSk) dh4 e ∧
      ∃ pk, s.sid = Concat.concat (DY.X25519.normalizeX25519Key pk) (pqxdhKdf ikm).rk ∧
        dh₁ = DiffieHellman.dh (DY.X25519.normalizeX25519Key pk) spkSk

theorem CompSessionAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {s : SessionInfo} {doneIdx : Nat} {ikm dh₁ : Bytes}
    (h : CompSessionAt tr s doneIdx ikm dh₁) : CompSessionAt tr' s doneIdx ikm dh₁ := by
  obtain ⟨hlog, hhk, hrole⟩ := h; refine ⟨eventLogged_mono hle hlog, handshakeKeysAt_mono hle hhk, ?_⟩
  split at hrole <;> rename_i hinit
  · simp only [hinit, ↓reduceIte]
    obtain ⟨a, b, t₀, ikA, ikB, spk, pqpk, opk, ct, dh1, dh2, dh4, hr0, hr1, hr2, hdone, hevA, hs, hikm, hdh₁⟩ := hrole
    exact ⟨a, b, t₀, ikA, ikB, spk, pqpk, opk, ct, dh1, dh2, dh4,
      randAt_mono hle hr0, randAt_mono hle hr1, randAt_mono hle hr2, hdone, eventLoggedAt_mono hle hevA, hs, hikm, hdh₁⟩
  · simp only [hinit, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨b, a, t_spk, ikB, ikA, spkSk, pqsk, opk, ek, ct, dh4, e, hspk, hr64, hne, hevB, hme, hpeer, hikm, hsid⟩ := hrole
    exact ⟨b, a, t_spk, ikB, ikA, spkSk, pqsk, opk, ek, ct, dh4, e,
      hspk, randAt_mono hle hr64, hne, eventLoggedAt_mono hle hevB, hme, hpeer, hikm, hsid⟩

theorem CompSessionAt.exists_dh {tr : ExecTrace} {s : SessionInfo} {doneIdx : Nat} {ikm dh₁ : Bytes}
    (h : CompSessionAt tr s doneIdx ikm dh₁) : ∃ p sk, dh₁ = DiffieHellman.dh (DY.X25519.normalizeX25519Key p) sk := by
  obtain ⟨_, _, hrole⟩ := h; split at hrole <;> rename_i hinit
  · obtain ⟨_, _, t₀, _, _, spk, _, _, _, _, _, _, _, _, _, _, _, _, _, hdh₁⟩ := hrole; exact ⟨spk, mkRand (t₀ + 2) 32, hdh₁⟩
  · obtain ⟨_, _, _, _, _, spkSk, _, _, _, _, _, _, _, _, _, _, _, _, _, pk, _, hdh₁⟩ := hrole
    exact ⟨pk, spkSk, hdh₁⟩

/-- If two initiator sessions share the same `ikm`, they are the same session at the same `doneIdx`. -/
theorem CompSessionAt.eq_of_initiator_ikm_eq {tr : ExecTrace} {s₁ s₂ : SessionInfo} {d₁ d₂ : Nat} {ikm dh₁ dh₂ : Bytes}
    (hs₁ : CompSessionAt tr s₁ d₁ ikm dh₁) (hs₂ : CompSessionAt tr s₂ d₂ ikm dh₂)
    (hinit₁ : s₁.initiator = true) (hinit₂ : s₂.initiator = true) : s₁ = s₂ ∧ d₁ = d₂ ∧ dh₁ = dh₂ := by
  obtain ⟨_, _, hrole₁⟩ := hs₁; obtain ⟨_, _, hrole₂⟩ := hs₂
  simp only [hinit₁, ↓reduceIte] at hrole₁; simp only [hinit₂, ↓reduceIte] at hrole₂
  obtain ⟨a₁, b₁, t₀₁, ikA₁, ikB₁, spk₁, pqpk₁, opk₁, ct₁, dh1₁, dh2₁, dh4₁, _, _, _, hd₁, hevA₁, hs₁_eq, hikm₁, hdh₁⟩ := hrole₁
  obtain ⟨a₂, b₂, t₀₂, ikA₂, ikB₂, spk₂, pqpk₂, opk₂, ct₂, dh1₂, dh2₂, dh4₂, _, _, _, hd₂, hevA₂, hs₂_eq, hikm₂, hdh₂⟩ := hrole₂
  obtain ⟨_, _, _, _, _, he_eq⟩ := pqxdhIkm_inj_kem (hikm₁.symm.trans hikm₂)
  obtain ⟨ht_eq, _⟩ := mkRand_inj he_eq; have ht₀_eq : t₀₁ = t₀₂ := by omega
  subst ht₀_eq; have hd_eq : d₁ = d₂ := hd₁.trans hd₂.symm; subst hd_eq
  have hsome : (some ⟨PQXDHEvent.AliceDone a₁ b₁ ikA₁ ikB₁ spk₁ pqpk₁ opk₁
      (DiffieHellman.dhPk (mkRand t₀₁ 32)) ct₁ (pqxdhKdf ikm)⟩ : Option PQXDHEntry) =
    some ⟨PQXDHEvent.AliceDone a₂ b₂ ikA₂ ikB₂ spk₂ pqpk₂ opk₂
      (DiffieHellman.dhPk (mkRand t₀₁ 32)) ct₂ (pqxdhKdf ikm)⟩ := hevA₁.symm.trans hevA₂
  injection hsome with h1; injection h1 with hev_eq
  injection hev_eq with ha hb _ _ hspk; subst ha hb hspk
  exact ⟨hs₁_eq.trans hs₂_eq.symm, rfl, hdh₁.trans hdh₂.symm⟩

/-! ## Composed Key-Schedule Invariant and Reachability -/

/-- Per-PQXDH-stored-key invariant distinguishing `.identity` keys (`EventLoggedAt _ (t_id + 1)`)
from `.signedPrekey` keys (`RandAt tr (t_spk + 1) 64`). -/
def CompPQXDHStateOK (tr : ExecTrace) (st : PQXDHState) : Prop :=
  match st.kind with
  | .identity => ∃ t_id, st.sk = mkRand t_id 32 ∧ ∃ ev : PQXDHEvent, tr.EventLoggedAt ev (t_id + 1)
  | .signedPrekey => ∃ t_spk, st.sk = mkRand t_spk 32 ∧ RandAt tr (t_spk + 1) 64
  | _ => True

theorem CompPQXDHStateOK.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {st : PQXDHState}
    (h : CompPQXDHStateOK tr st) : CompPQXDHStateOK tr' st := by
  unfold CompPQXDHStateOK at h ⊢; split at h
  · obtain ⟨t_id, hsk, ev, hev⟩ := h; exact ⟨t_id, hsk, ev, eventLoggedAt_mono hle hev⟩
  · obtain ⟨t_spk, hsk, hr⟩ := h; exact ⟨t_spk, hsk, randAt_mono hle hr⟩
  · trivial

theorem CompPQXDHStateOK.ik_ne_spk {tr : ExecTrace} {ikB spkSk : Bytes}
    (hik : CompPQXDHStateOK tr { kind := .identity, sk := ikB })
    (hspk : CompPQXDHStateOK tr { kind := .signedPrekey, sk := spkSk }) : ikB ≠ spkSk := by
  obtain ⟨t_id, rfl, ev, hev⟩ := hik; obtain ⟨t_spk, rfl, hr64⟩ := hspk
  intro heq; obtain ⟨ht, _⟩ := mkRand_inj heq; subst ht
  exact at?_disjoint rfl hr64 hev

/-- Per-receiver-chain schedule invariant inside a stored `TRState` snapshot. -/
def CompRecvChainScheduleOK (dh₁ ikm : Bytes) (initiator : Bool) (stRIdx : Nat) (c : RecvChain) : Prop :=
  1 ≤ c.rIdx ∧ c.rIdx ≤ stRIdx ∧ c.rIdx % 2 = roleParity initiator ∧
  ∃ ck₀, CompChainRootFrom1 dh₁ ikm (c.rIdx - 1) ck₀ ∧ c.chainKey = chainKeyAt ck₀ c.index.toNat

theorem CompRecvChainScheduleOK.mono_rIdx {dh₁ ikm : Bytes} {initiator : Bool} {r₁ r₂ : Nat}
    {c : RecvChain} (h : CompRecvChainScheduleOK dh₁ ikm initiator r₁ c) (hle : r₁ ≤ r₂) :
    CompRecvChainScheduleOK dh₁ ikm initiator r₂ c :=
  ⟨h.1, Nat.le_trans h.2.1 hle, h.2.2.1, h.2.2.2⟩

/-- Per-snapshot schedule invariant on `TRState` on trace `tr`. -/
def CompStateScheduleOK (tr : ExecTrace) (me : Participant) (st : TRState) : Prop :=
  1 ≤ st.rIdx ∧ st.rIdx % 2 = roleParity st.initiator ∧ (∃ r p sk, st.rk = (createChain r p sk).1) ∧
  (∃ doneIdx ikm dh₁, CompSessionAt tr (st.sessionInfo me) doneIdx ikm dh₁ ∧
    CompRkSteps dh₁ st.rIdx (pqxdhKdf ikm).rk st.rk ∧
    (∃ ck₀, CompChainRootFrom1 dh₁ ikm st.rIdx ck₀ ∧ st.cks = chainKeyAt ck₀ st.ns.toNat) ∧
    (∀ c ∈ st.recv, CompRecvChainScheduleOK dh₁ ikm st.initiator st.rIdx c)) ∧
  (∃ ts, ts < tr.length ∧ RandAt tr ts 32 ∧ st.dhs = mkRand ts 32)

private theorem randAt_lt_length {tr : ExecTrace} {ts sz : Nat} (h : RandAt tr ts sz) : ts < tr.length := by
  have h1 := Trace.at?_eq_some_implies_length_le (EntryT := RndEntry) tr ts
  unfold RandAt at h; rw [h] at h1; exact h1

theorem CompStateScheduleOK.mono {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {me : Participant} {st : TRState} (h : CompStateScheduleOK tr me st) :
    CompStateScheduleOK tr' me st := by
  obtain ⟨hpos, hpar, hrk_shape, ⟨doneIdx, ikm, dh₁, hs, hrk, hcks, hrecv⟩, ⟨ts, _, hr, hdhs⟩⟩ := h
  have hr' := randAt_mono hle hr
  exact ⟨hpos, hpar, hrk_shape, ⟨doneIdx, ikm, dh₁, hs.mono hle, hrk, hcks, hrecv⟩,
    ⟨ts, randAt_lt_length hr', hr', hdhs⟩⟩

/-- Per-event schedule invariant on `TREvent` on trace `tr`. -/
def CompEventScheduleOK (tr : ExecTrace) : TREvent → Prop
  | .SkippedKeyStored s _ n seed rIdx _ =>
    1 ≤ rIdx ∧ rIdx % 2 = roleParity s.initiator ∧
    ∃ doneIdx ikm dh₁ ck₀, CompSessionAt tr s doneIdx ikm dh₁ ∧
      CompChainRootFrom1 dh₁ ikm (rIdx - 1) ck₀ ∧ seed = (kdfCk (chainKeyAt ck₀ n.toNat)).2
  | .MessageKey s .receiver seed _ n rIdx _ =>
    1 ≤ rIdx ∧ rIdx % 2 = roleParity s.initiator ∧
    ∃ doneIdx ikm dh₁ ck₀, CompSessionAt tr s doneIdx ikm dh₁ ∧
      CompChainRootFrom1 dh₁ ikm (rIdx - 1) ck₀ ∧ seed = (kdfCk (chainKeyAt ck₀ n.toNat)).2
  | .MessageKey s .sender seed _ n rIdx _ =>
    1 ≤ rIdx ∧ rIdx % 2 = roleParity s.initiator ∧
    ∃ doneIdx ikm dh₁ ck₀, CompSessionAt tr s doneIdx ikm dh₁ ∧
      CompChainRootFrom1 dh₁ ikm rIdx ck₀ ∧ seed = (kdfCk (chainKeyAt ck₀ n.toNat)).2
  | .Sent _ _ _ _ m => ∃ ts, ts < tr.length ∧ RandAt tr ts 32 ∧ m = mkRand ts 32
  | .ExposedRK s rk rIdx =>
    1 ≤ rIdx ∧ rIdx % 2 = roleParity s.initiator ∧ (∃ r p sk, rk = (createChain r p sk).1) ∧
    ∃ doneIdx ikm dh₁, CompSessionAt tr s doneIdx ikm dh₁ ∧ CompRkSteps dh₁ rIdx (pqxdhKdf ikm).rk rk
  | .ExposedDHs _ dhs _ => ∃ ts, ts < tr.length ∧ RandAt tr ts 32 ∧ dhs = mkRand ts 32
  | .ExposedCKs s ck ns rIdx =>
    1 ≤ rIdx ∧ rIdx % 2 = roleParity s.initiator ∧
    ∃ doneIdx ikm dh₁ ck₀, CompSessionAt tr s doneIdx ikm dh₁ ∧
      CompChainRootFrom1 dh₁ ikm rIdx ck₀ ∧ ck = chainKeyAt ck₀ ns.toNat
  | .ExposedCKr s ck nr rIdx =>
    1 ≤ rIdx ∧ rIdx % 2 = roleParity s.initiator ∧
    ∃ doneIdx ikm dh₁ ck₀, CompSessionAt tr s doneIdx ikm dh₁ ∧
      CompChainRootFrom1 dh₁ ikm (rIdx - 1) ck₀ ∧ ck = chainKeyAt ck₀ nr.toNat
  | .ExposedMK s seed n rIdx =>
    1 ≤ rIdx ∧ rIdx % 2 = roleParity s.initiator ∧
    ∃ doneIdx ikm dh₁ ck₀, CompSessionAt tr s doneIdx ikm dh₁ ∧
      CompChainRootFrom1 dh₁ ikm (rIdx - 1) ck₀ ∧ seed = (kdfCk (chainKeyAt ck₀ n.toNat)).2
  | _ => True

theorem CompEventScheduleOK.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {ev : TREvent}
    (h : CompEventScheduleOK tr ev) : CompEventScheduleOK tr' ev := by
  cases ev with
  | MessageKey s dir seed pqSalt n rIdx par =>
    cases dir <;> { obtain ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs, hroot, hmk⟩ := h
                    exact ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs.mono hle, hroot, hmk⟩ }
  | SkippedKeyStored s pk n seed rIdx src =>
    obtain ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs, hroot, hseed⟩ := h
    exact ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs.mono hle, hroot, hseed⟩
  | Sent me peer pk ns m =>
    obtain ⟨ts, _, hr, hm⟩ := h; have hr' := randAt_mono hle hr
    exact ⟨ts, randAt_lt_length hr', hr', hm⟩
  | ExposedRK s rk rIdx =>
    obtain ⟨hpos, hpar, hshape, doneIdx, ikm, dh₁, hs, hrk⟩ := h
    exact ⟨hpos, hpar, hshape, doneIdx, ikm, dh₁, hs.mono hle, hrk⟩
  | ExposedDHs s dhs rIdx =>
    obtain ⟨ts, _, hr, hdhs⟩ := h; have hr' := randAt_mono hle hr
    exact ⟨ts, randAt_lt_length hr', hr', hdhs⟩
  | ExposedCKs s ck ns rIdx =>
    obtain ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs, hroot, hck⟩ := h
    exact ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs.mono hle, hroot, hck⟩
  | ExposedCKr s ck nr rIdx =>
    obtain ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs, hroot, hck⟩ := h
    exact ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs.mono hle, hroot, hck⟩
  | ExposedMK s seed n rIdx =>
    obtain ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs, hroot, hseed⟩ := h
    exact ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs.mono hle, hroot, hseed⟩
  | _ => trivial

/-- Bundled composed schedule invariant on `tr`. -/
structure CompScheduleInv (tr : ExecTrace) : Prop where
  pqxStOK : ∀ p st j, PQXDHStoredAt tr p st j → CompPQXDHStateOK tr st
  stateOK : ∀ p st j, StateStoredAt p st j tr → CompStateScheduleOK tr p st
  eventOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOK tr ev

theorem CompScheduleInv.nil : CompScheduleInv Trace.nil :=
  ⟨fun _ _ _ hst => (nomatch hst), fun _ _ _ hst => (nomatch hst), fun _ ⟨_, hev⟩ => (nomatch hev)⟩

theorem CompScheduleInv.append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E}
    (hnone_pqSt : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHStEntry) = none)
    (hnone_trSt : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    (hnone_trEv : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (h : CompScheduleInv tr) : CompScheduleInv (tr.append e) := by
  have hle : tr ≤ tr.append e := Trace.append_le tr e
  refine ⟨fun p st j hst => (h.pqxStOK p st j (pqxdhStoredAt_append_other hnone_pqSt hst)).mono hle,
    fun p st j hst => (h.stateOK p st j (trStateStoredAt_append_other hnone_trSt hst)).mono hle,
    fun ev ⟨k, hk⟩ => (h.eventOK ev ⟨k, eventLoggedAt_append_other hnone_trEv hk⟩).mono hle⟩

theorem CompScheduleInv.append_pqxSt {tr : ExecTrace} {p₀ : Participant} {st₀ : PQXDHState}
    (hst₀ : CompPQXDHStateOK (tr.append (PQStE p₀ st₀)) st₀)
    (h : CompScheduleInv tr) : CompScheduleInv (tr.append (PQStE p₀ st₀)) := by
  have hle : tr ≤ tr.append (PQStE p₀ st₀) := Trace.append_le tr _
  refine ⟨fun p st j hst => ?_,
    fun p st j hst => (h.stateOK p st j (trStateStoredAt_append_other rfl hst)).mono hle,
    fun ev ⟨k, hk⟩ => (h.eventOK ev ⟨k, eventLoggedAt_append_other rfl hk⟩).mono hle⟩
  rcases pqxdhStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, rfl, rfl⟩
  · exact (h.pqxStOK p st j hst).mono hle
  · exact hst₀

theorem CompScheduleInv.append_trEv {tr : ExecTrace} {ev : TREvent}
    (hev : CompEventScheduleOK (tr.append (TREvE ev)) ev)
    (h : CompScheduleInv tr) : CompScheduleInv (tr.append (TREvE ev)) := by
  have hle : tr ≤ tr.append (TREvE ev) := Trace.append_le tr _
  refine ⟨fun p st j hst => (h.pqxStOK p st j (pqxdhStoredAt_append_other rfl hst)).mono hle,
    fun p st j hst => (h.stateOK p st j (trStateStoredAt_append_other rfl hst)).mono hle,
    fun ev' ⟨k, hk⟩ => ?_⟩
  rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, rfl⟩
  · exact (h.eventOK ev' ⟨k, hk⟩).mono hle
  · exact hev

theorem CompScheduleInv.append_trSt {tr : ExecTrace} {p₀ : Participant} {st₀ : TRState}
    (hst₀ : CompStateScheduleOK (tr.append (TRStE p₀ st₀)) p₀ st₀)
    (h : CompScheduleInv tr) : CompScheduleInv (tr.append (TRStE p₀ st₀)) := by
  have hle : tr ≤ tr.append (TRStE p₀ st₀) := Trace.append_le tr _
  refine ⟨fun p st j hst => (h.pqxStOK p st j (pqxdhStoredAt_append_other rfl hst)).mono hle,
    fun p st j hst => ?_,
    fun ev ⟨k, hk⟩ => (h.eventOK ev ⟨k, eventLoggedAt_append_other rfl hk⟩).mono hle⟩
  rcases trStateStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, rfl, rfl⟩
  · exact (h.stateOK p st j hst).mono hle
  · exact hst₀

theorem CompRkSteps.step_pos {dh₁ rk₀ rk : Bytes} {d : Nat} (hpos : 1 ≤ d)
    (hrk : CompRkSteps dh₁ d rk₀ rk) (pk sk : Bytes) :
    CompRkSteps dh₁ (d + 1) rk₀ (createChain rk pk sk).1 := by
  rcases d with _ | k
  · omega
  · exact .step_succ hrk

theorem CompChainRootFrom1.of_step_pos {dh₁ ikm rk : Bytes} {d : Nat} (hpos : 1 ≤ d)
    (hrk : CompRkSteps dh₁ d (pqxdhKdf ikm).rk rk) (pk sk : Bytes) :
    CompChainRootFrom1 dh₁ ikm (d + 1) (createChain rk pk sk).2 := by
  rcases d with _ | k
  · omega
  · exact ⟨rk, pk, sk, hrk, rfl⟩

private theorem uint32_toNat_add_one_of_lt {n : UInt32} (h : n.toNat + 1 < UInt32.size) :
    (n + 1).toNat = n.toNat + 1 := by rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

private theorem uint32_toNat_add_one_of_ne_u32Max {n : UInt32} (h : n ≠ u32Max) :
    (n + 1).toNat = n.toNat + 1 := by
  apply uint32_toNat_add_one_of_lt
  have hlt : n.toNat < UInt32.size := n.toBitVec.isLt
  have hne : n.toNat ≠ 4294967295 := fun heq => h (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq heq))
  have hsize : UInt32.size = 4294967296 := rfl; omega

theorem consumeMessageKey_compSchedule {dh₁ ikm : Bytes} {initiator : Bool} {stRIdx : Nat}
    {c c' : RecvChain} {counter : UInt32} {seed : Bytes}
    (hc : CompRecvChainScheduleOK dh₁ ikm initiator stRIdx c)
    (hcons : consumeMessageKey c counter = some (seed, c')) :
    c'.ratchetKey = c.ratchetKey ∧ c'.rIdx = c.rIdx ∧ c.index.toNat ≤ counter.toNat ∧
    counter.toNat + 1 < UInt32.size ∧ CompRecvChainScheduleOK dh₁ ikm initiator stRIdx c' ∧
    ∃ ck₀, CompChainRootFrom1 dh₁ ikm (c.rIdx - 1) ck₀ ∧ c.chainKey = chainKeyAt ck₀ c.index.toNat ∧
      seed = (kdfCk (chainKeyAt ck₀ counter.toNat)).2 ∧ c'.chainKey = chainKeyAt ck₀ c'.index.toNat := by
  obtain ⟨hpos, hle_st, hpar, ck₀, hroot, hck₀⟩ := hc
  unfold consumeMessageKey at hcons; split at hcons
  · cases hcons
  · next hnot_lt =>
    split at hcons
    · cases hcons
    · split at hcons
      · cases hcons
      · next hnot_max =>
        cases hcons
        have hidx_le : c.index.toNat ≤ counter.toNat := Nat.le_of_not_lt hnot_lt
        have hne_max : counter ≠ u32Max := fun h => by subst h; exact hnot_max rfl
        have hcnt_lt : counter.toNat + 1 < UInt32.size := by
          have hlt : counter.toNat < UInt32.size := counter.toBitVec.isLt
          have hne : counter.toNat ≠ 4294967295 := fun heq =>
            hne_max (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq heq))
          have hsize : UInt32.size = 4294967296 := rfl; omega
        have hadv : chainKeyAt c.chainKey (counter.toNat - c.index.toNat) =
            chainKeyAt ck₀ counter.toNat := by rw [hck₀, ← chainKeyAt_add]; congr 1; omega
        have hnext : (kdfCk (chainKeyAt c.chainKey (counter.toNat - c.index.toNat))).1 =
            chainKeyAt ck₀ (counter + 1).toNat := by
          rw [hadv, uint32_toNat_add_one_of_ne_u32Max hne_max, chainKeyAt_succ_eq_kdfCk_fst]
        exact ⟨rfl, rfl, hidx_le, hcnt_lt, ⟨hpos, hle_st, hpar, ck₀, hroot, hnext⟩,
          ck₀, hroot, hck₀, by rw [hadv], hnext⟩

theorem setRecvChain_compSchedule {dh₁ ikm : Bytes} {initiator : Bool} {stRIdx : Nat}
    {recv : List RecvChain} {c' : RecvChain}
    (hrecv : ∀ x ∈ recv, CompRecvChainScheduleOK dh₁ ikm initiator stRIdx x)
    (hc' : CompRecvChainScheduleOK dh₁ ikm initiator stRIdx c') :
    ∀ x ∈ setRecvChain recv c', CompRecvChainScheduleOK dh₁ ikm initiator stRIdx x := by
  intro x hx; unfold setRecvChain at hx; rw [List.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx; split
  · exact hc'
  · exact hrecv c hc

private theorem findRecvChain_some {recv : List RecvChain} {pk : Bytes} {c : RecvChain}
    (h : findRecvChain recv pk = some c) : c ∈ recv ∧ c.ratchetKey = pk :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

private theorem logSkippedKeys_fst (s : SessionInfo) (pk : Bytes) (rIdx sourceStateIdx : Nat) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx sourceStateIdx ck n k).run t).1 = some ()
  | _, _, 0, _ => rfl
  | ck, n, k + 1, _ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [run_bind_fst]
    exact logSkippedKeys_fst s pk rIdx sourceStateIdx (kdfCk ck).1 (n + 1) k _

private theorem schedule_logSkippedKeys (s : SessionInfo) (pk : Bytes)
    (rIdx sourceStateIdx doneIdx : Nat) (ikm dh₁ ck₀ : Bytes)
    (hrpos : 1 ≤ rIdx) (hrpar : rIdx % 2 = roleParity s.initiator)
    (hroot : CompChainRootFrom1 dh₁ ikm (rIdx - 1) ck₀) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat), ck = chainKeyAt ck₀ n.toNat → n.toNat + k < UInt32.size →
      ∀ tr, CompSessionAt tr s doneIdx ikm dh₁ → CompScheduleInv tr →
        CompScheduleInv (((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx sourceStateIdx ck n k).run tr).2.val)
  | _, _, 0, _, _, _, _, hInv => hInv
  | ck, n, k + 1, hck, hlt, tr, hs, hInv => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    let ev := TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx sourceStateIdx
    have hle : tr ≤ tr.append (TREvE ev) := Trace.append_le tr (TREvE ev)
    have hs' : CompSessionAt (tr.append (TREvE ev)) s doneIdx ikm dh₁ := hs.mono hle
    have hInv1 : CompScheduleInv (tr.append (TREvE ev)) :=
      hInv.append_trEv ⟨hrpos, hrpar, doneIdx, ikm, dh₁, ck₀, hs', hroot, by rw [hck]⟩
    have hn1 : (n + 1).toNat = n.toNat + 1 := uint32_toNat_add_one_of_lt (by omega)
    have hck1 : (kdfCk ck).1 = chainKeyAt ck₀ (n + 1).toNat := by
      rw [hck, hn1, chainKeyAt_succ_eq_kdfCk_fst]
    exact schedule_logSkippedKeys s pk rIdx sourceStateIdx doneIdx ikm dh₁ ck₀ hrpos hrpar hroot
      (kdfCk ck).1 (n + 1) k hck1 (by omega) (tr.append (TREvE ev)) hs' hInv1

private theorem schedule_logMessageKeyAndStore (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : Bytes) (n : UInt32) (rIdx parentStateIdx : Nat)
    (st : TRState) (tr : ExecTrace)
    (hev : CompEventScheduleOK tr
      (.MessageKey s dir seed pqSalt n rIdx parentStateIdx))
    (hst : CompStateScheduleOK tr me st) (hInv : CompScheduleInv tr) :
    CompScheduleInv
      (((DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx parentStateIdx st).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  let ev := TREvent.MessageKey s dir seed pqSalt n rIdx parentStateIdx
  have hle1 : tr ≤ tr.append (TREvE ev) := Trace.append_le tr (TREvE ev)
  have hInv1 : CompScheduleInv (tr.append (TREvE ev)) :=
    hInv.append_trEv (hev.mono hle1)
  have hle2 : tr.append (TREvE ev) ≤ (tr.append (TREvE ev)).append (TRStE me st) :=
    Trace.append_le (tr.append (TREvE ev)) (TRStE me st)
  exact hInv1.append_trSt (hst.mono (Trace.le_trans _ _ _ hle1 hle2))

private theorem schedule_decryptTail (me : Participant) (_origIdx parIdx doneIdx : Nat)
    (ikm dh₁ : Bytes) (st : TRState) (msg : TRSignalMsg) (c c' : RecvChain)
    (seed pqSalt m spqr' : Bytes) (tr : ExecTrace) (hInv : CompScheduleInv tr)
    (hpos_st : 1 ≤ st.rIdx) (hpar : st.rIdx % 2 = roleParity st.initiator)
    (hrk_shape : ∃ r p sk, st.rk = (createChain r p sk).1)
    (hs : CompSessionAt tr (st.sessionInfo me) doneIdx ikm dh₁)
    (hrk : CompRkSteps dh₁ st.rIdx (pqxdhKdf ikm).rk st.rk)
    (hcks : ∃ ck₀, CompChainRootFrom1 dh₁ ikm st.rIdx ck₀ ∧ st.cks = chainKeyAt ck₀ st.ns.toNat)
    (hrecv : ∀ x ∈ st.recv, CompRecvChainScheduleOK dh₁ ikm st.initiator st.rIdx x)
    (hdhs : ∃ ts, ts < tr.length ∧ RandAt tr ts 32 ∧ st.dhs = mkRand ts 32)
    (hc : CompRecvChainScheduleOK dh₁ ikm st.initiator st.rIdx c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c')) :
    CompScheduleInv ((do
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx parIdx c.chainKey c.index
        (msg.counter.toNat - c.index.toNat)
      ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) .receiver seed pqSalt msg.counter c.rIdx parIdx { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val := by
  rw [run_bind_snd, logSkippedKeys_fst]; dsimp only
  have hrpos : 1 ≤ c.rIdx := hc.1; have hrpar : c.rIdx % 2 = roleParity st.initiator := hc.2.2.1
  obtain ⟨_, _, hidx_le, hcnt_lt, hc', ck₀, hroot, hck_c, hseed, _⟩ := consumeMessageKey_compSchedule hc hcons
  let tr₁ := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx parIdx c.chainKey c.index
    (msg.counter.toNat - c.index.toNat)).run tr).2.val
  have hle₁ : tr ≤ tr₁ := (DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx parIdx c.chainKey
    c.index (msg.counter.toNat - c.index.toNat)).run tr |>.2.property
  have hInv₁ : CompScheduleInv tr₁ :=
    schedule_logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx parIdx doneIdx ikm dh₁ ck₀
      hrpos hrpar hroot c.chainKey c.index (msg.counter.toNat - c.index.toNat) hck_c (by omega) tr hs hInv
  let tr₂ := tr₁.append (TREvE (.Received me st.peer msg.ratchetKey msg.counter m))
  have hle₀₂ : tr ≤ tr₂ := Trace.le_trans _ _ _ hle₁ (Trace.append_le tr₁ _)
  have hInv₂ : CompScheduleInv tr₂ := hInv₁.append_trEv trivial
  have hs₂ : CompSessionAt tr₂ (st.sessionInfo me) doneIdx ikm dh₁ := hs.mono hle₀₂
  obtain ⟨ts, _, hr, hdhs_eq⟩ := hdhs; have hr₂ := randAt_mono hle₀₂ hr
  have hst' : CompStateScheduleOK tr₂ me { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
    ⟨hpos_st, hpar, hrk_shape, ⟨doneIdx, ikm, dh₁, hs₂, hrk, hcks, setRecvChain_compSchedule hrecv hc'⟩,
      ⟨ts, randAt_lt_length hr₂, hr₂, hdhs_eq⟩⟩
  exact schedule_logMessageKeyAndStore me (st.sessionInfo me) .receiver
    seed pqSalt msg.counter c.rIdx parIdx { st with recv := setRecvChain st.recv c', spqr := spqr' } tr₂
    ⟨hrpos, hrpar, doneIdx, ikm, dh₁, ck₀, hs₂, hroot, hseed⟩ hst' hInv₂

private theorem bind_ensureReceiverChain_schedule {α : Type}
    (me : Participant) (st₀ : TRState) (pk : Bytes) (tr₀ : ExecTrace)
    (hst₀ : CompStateScheduleOK tr₀ me st₀) (hInv₀ : CompScheduleInv tr₀)
    {f : TRState × RecvChain × Bool → Traceful α}
    (hf : ∀ st c ratcheted tr₁ doneIdx ikm dh₁, tr₀ ≤ tr₁ → CompScheduleInv tr₁ →
      1 ≤ st.rIdx → st.rIdx % 2 = roleParity st.initiator → (∃ r p sk, st.rk = (createChain r p sk).1) →
      CompSessionAt tr₁ (st.sessionInfo me) doneIdx ikm dh₁ → CompRkSteps dh₁ st.rIdx (pqxdhKdf ikm).rk st.rk →
      (∃ ck₀, CompChainRootFrom1 dh₁ ikm st.rIdx ck₀ ∧ st.cks = chainKeyAt ck₀ st.ns.toNat) →
      (∀ x ∈ st.recv, CompRecvChainScheduleOK dh₁ ikm st.initiator st.rIdx x) →
      CompRecvChainScheduleOK dh₁ ikm st.initiator st.rIdx c →
      (∃ ts, ts < tr₁.length ∧ RandAt tr₁ ts 32 ∧ st.dhs = mkRand ts 32) →
      CompScheduleInv (((f (st, c, ratcheted)).run tr₁).2.val)) :
    CompScheduleInv (((DY.Libsignal.TripleRatchet.ensureReceiverChain st₀ pk >>= f).run tr₀).2.val) := by
  rw [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  unfold DY.Libsignal.TripleRatchet.recvChainFor
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  dsimp only [TRState.toDRState]
  rw [run_bind_snd]
  cases hfind : findRecvChain st₀.recv pk with
  | some c =>
    dsimp only
    obtain ⟨hpos₀, hpar₀, hrk_shape₀, ⟨doneIdx, ikm, dh₁, hs₀, hrk₀, hcks₀, hrecv₀⟩, hdhs₀⟩ := hst₀
    exact hf st₀ c false tr₀ doneIdx ikm dh₁ (Trace.le_refl tr₀) hInv₀ hpos₀ hpar₀ hrk_shape₀
      hs₀ hrk₀ hcks₀ hrecv₀ (hrecv₀ c (findRecvChain_some hfind).1) hdhs₀
  | none =>
    dsimp only; by_cases hlo : x25519LowOrder pk = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hlo h]; exact hInv₀
    · rw [ite_eq_right_iff.mpr fun h => absurd h hlo]; dsimp only; unfold _root_.guard
      have hlo' : (!x25519LowOrder pk) = true := by cases h : x25519LowOrder pk <;> simp_all
      rw [ite_eq_left_iff.mpr fun h => absurd hlo' h]
      obtain ⟨hpos₀, hpar₀, _, ⟨doneIdx, ikm, dh₁, hs₀, hrk₀, _, hrecv₀⟩, _⟩ := hst₀
      let tr₁ := tr₀.append (RndE 32); have hle₁ : tr₀ ≤ tr₁ := Trace.append_le tr₀ (RndE 32)
      have hInv₁ : CompScheduleInv tr₁ := hInv₀.append_other rfl rfl rfl
      have hs₁ : CompSessionAt tr₁ (st₀.sessionInfo me) doneIdx ikm dh₁ := hs₀.mono hle₁
      let dhs' : Bytes := mkRand tr₀.length 32
      let rk1 := (createChain st₀.rk pk st₀.dhs).1; let ckr := (createChain st₀.rk pk st₀.dhs).2
      let rk2 := (createChain rk1 pk dhs').1; let cks := (createChain rk1 pk dhs').2
      let cNew : RecvChain := { ratchetKey := pk, chainKey := ckr, index := 0, rIdx := st₀.rIdx + 2 }
      have hpos' : 1 ≤ st₀.rIdx + 2 := by omega
      have hpar' : (st₀.rIdx + 2) % 2 = roleParity st₀.initiator := by omega
      have hrk1 : CompRkSteps dh₁ (st₀.rIdx + 1) (pqxdhKdf ikm).rk rk1 := hrk₀.step_pos hpos₀ pk st₀.dhs
      have hroot_ckr : CompChainRootFrom1 dh₁ ikm (st₀.rIdx + 1) ckr :=
        CompChainRootFrom1.of_step_pos hpos₀ hrk₀ pk st₀.dhs
      have hcNew : CompRecvChainScheduleOK dh₁ ikm st₀.initiator (st₀.rIdx + 2) cNew :=
        ⟨by dsimp [cNew]; omega, by dsimp [cNew]; omega, hpar', ckr, hroot_ckr, rfl⟩
      have hpos1 : 1 ≤ st₀.rIdx + 1 := by omega
      have hrk2 : CompRkSteps dh₁ (st₀.rIdx + 2) (pqxdhKdf ikm).rk rk2 := hrk1.step_pos hpos1 pk dhs'
      have hroot_cks : CompChainRootFrom1 dh₁ ikm (st₀.rIdx + 2) cks :=
        CompChainRootFrom1.of_step_pos hpos1 hrk1 pk dhs'
      let st' : TRState :=
        { st₀ with rk := rk2, dhs := dhs', cks := cks, ns := 0,
                   pn := if st₀.ns = 0 then 0 else st₀.ns - 1, rIdx := st₀.rIdx + 2,
                   recv := (st₀.recv ++ [cNew]).drop ((st₀.recv.length + 1) - maxReceiverChains) }
      have hrecv' : ∀ x ∈ st'.recv, CompRecvChainScheduleOK dh₁ ikm st'.initiator st'.rIdx x := by
        intro x hx; dsimp [st'] at hx ⊢
        rcases List.mem_append.mp (List.mem_of_mem_drop hx) with hx' | hx'
        · exact (hrecv₀ x hx').mono_rIdx (by omega)
        · rw [List.mem_singleton] at hx'; subst hx'; exact hcNew
      have hdhs' : ∃ ts, ts < tr₁.length ∧ RandAt tr₁ ts 32 ∧ st'.dhs = mkRand ts 32 :=
        ⟨tr₀.length, by simp [tr₁, Trace.append, Trace.length], Trace.at?_append tr₀ (RndE 32), rfl⟩
      exact hf st' cNew true tr₁ doneIdx ikm dh₁ hle₁ hInv₁ hpos' hpar' ⟨rk1, pk, dhs', rfl⟩
        hs₁ hrk2 ⟨cks, hroot_cks, rfl⟩ hrecv' hcNew hdhs'

private theorem run_sendMessage_bind_snd {α : Type} (msg : Bytes) (f : Nat → Traceful α) (tr : ExecTrace) :
    ((Network.sendMessage msg >>= f).run tr).2.val = ((f tr.length).run (tr.append (NetE msg))).2.val := rfl

private theorem bind_getEntry_tr_at {Inv : ExecTrace → Prop} {α : Type}
    (evH : Nat) {f : TREntry → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ e, tr.EventLogged e.ev → Inv ((f e).run tr).2.val) :
    Inv (((DY.getEntry evH : Traceful TREntry) >>= f).run tr).2.val := by
  unfold DY.getEntry; simp only [Traceful.run_bind, Traceful.run_mk]
  rcases he : (tr.at? evH : Option TREntry) with _ | e
  · exact hInv
  · exact hf e ⟨evH, he⟩

private theorem bind_guardOnTrace_at {Inv : ExecTrace → Prop} {α : Type}
    (p : ExecTrace → Bool) {f : Unit → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : p tr = true → Inv ((f ()).run tr).2.val) :
    Inv (((DY.Libsignal.PQXDH.guardTrace p >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.guardTrace; rw [run_bind_snd, Traceful.run_mk]; dsimp only
  by_cases hp : p tr = true
  · rw [ite_eq_left_iff.mpr fun h => absurd hp h]; exact hf hp
  · rw [ite_eq_right_iff.mpr fun h => absurd h hp]; exact hInv

private theorem bind_guardTrace_at {Inv : ExecTrace → Prop} {α : Type}
    (p : ExecTrace → Bool) {f : Unit → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : p tr = true → Inv ((f ()).run tr).2.val) :
    Inv (((guardTrace p >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.guardTrace; rw [run_bind_snd, Traceful.run_mk]; dsimp only
  by_cases hp : p tr = true
  · rw [ite_eq_left_iff.mpr fun h => absurd hp h]; exact hf hp
  · rw [ite_eq_right_iff.mpr fun h => absurd h hp]; exact hInv

theorem CompScheduleInv.preserves_registerIdentity (p : Participant) :
    Preserves CompScheduleInv (registerIdentity p) := by
  intro tr₀ hInv₀; unfold DY.Libsignal.PQXDH.registerIdentity
  refine bind_guardOnTrace_at _ tr₀ hInv₀ fun _ => ?_
  rw [run_genRand_bind_snd]
  let t_id := tr₀.length; let ik := mkRand t_id 32; let tr₁ := tr₀.append (RndE 32)
  let ev := PQXDHEvent.IdentityRegistered p (DiffieHellman.dhPk ik) (DY.Signature.vk ik) true
  let tr₂ := tr₁.append (PQEvE ev); let tr₃ := tr₂.append (NetE (DiffieHellman.dhPk ik))
  let tr₄ := tr₃.append (NetE (DY.Signature.vk ik)); let tr₅ := tr₄.append (PQStE p { kind := .identity, sk := ik })
  have hInv₄ : CompScheduleInv tr₄ :=
    (((hInv₀.append_other rfl rfl rfl).append_other rfl rfl rfl).append_other rfl rfl rfl).append_other rfl rfl rfl
  have hle₂₅ : tr₂ ≤ tr₅ :=
    Trace.le_trans _ _ _ (Trace.append_le tr₂ _)
      (Trace.le_trans _ _ _ (Trace.append_le tr₃ _) (Trace.append_le tr₄ _))
  exact hInv₄.append_pqxSt ⟨t_id, rfl, ev, eventLoggedAt_mono hle₂₅ (Trace.at?_append tr₁ (PQEvE ev))⟩

theorem CompScheduleInv.preserves_registerCorruptIdentity (p : Participant) (skIdx : Nat) :
    Preserves CompScheduleInv (registerCorruptIdentity p skIdx) := by
  unfold DY.Libsignal.PQXDH.registerCorruptIdentity
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  exact Preserves.bind (fun _ h => h.append_other rfl rfl rfl) fun _ _ h => h.append_other rfl rfl rfl

theorem CompScheduleInv.preserves_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves CompScheduleInv (genSignedPrekey b idStateIdx) := by
  intro tr₀ hInv₀; unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine bind_getKey_at b idStateIdx .identity tr₀ hInv₀ fun ikB _ => ?_
  rw [run_genRand_bind_snd, run_genRand_bind_snd]
  let t_spk := tr₀.length; let spkSk := mkRand t_spk 32
  let tr₁ := tr₀.append (RndE 32); let tr₂ := tr₁.append (RndE 64)
  let tr₃ := tr₂.append (PQEvE (.SignedPrekeyPublished b (DiffieHellman.dhPk spkSk)))
  let tr₄ := tr₃.append (PQStE b { kind := .signedPrekey, sk := spkSk })
  have hInv₃ : CompScheduleInv tr₃ := ((hInv₀.append_other rfl rfl rfl).append_other rfl rfl rfl).append_other rfl rfl rfl
  have hle₂₄ : tr₂ ≤ tr₄ := Trace.le_trans _ _ _ (Trace.append_le tr₂ _) (Trace.append_le tr₃ _)
  have hInv₄ : CompScheduleInv tr₄ := hInv₃.append_pqxSt ⟨t_spk, rfl, randAt_mono hle₂₄ (Trace.at?_append tr₁ (RndE 64))⟩
  exact (hInv₄.append_other rfl rfl rfl).append_other rfl rfl rfl

theorem CompScheduleInv.preserves_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    Preserves CompScheduleInv (genPQPrekey b idStateIdx) := by
  intro tr hInv; unfold DY.Libsignal.PQXDH.genPQPrekey
  refine bind_getKey_at b idStateIdx .identity tr hInv fun _ _ => ?_
  exact (((((hInv.append_other rfl rfl rfl).append_other rfl rfl rfl).append_other rfl rfl rfl).append_pqxSt
    (st₀ := { kind := .pqPrekey, sk := mkRand tr.length 64 }) trivial).append_other rfl rfl rfl).append_other rfl rfl rfl

theorem CompScheduleInv.preserves_genOneTimePrekey (b : Participant) :
    Preserves CompScheduleInv (genOneTimePrekey b) := by
  intro tr hInv; unfold DY.Libsignal.PQXDH.genOneTimePrekey
  exact (((hInv.append_other rfl rfl rfl).append_other rfl rfl rfl).append_pqxSt
    (st₀ := { kind := .oneTimePrekey, sk := mkRand tr.length 32 }) trivial).append_other rfl rfl rfl

theorem CompScheduleInv.preserves_compromiseIK (p : Participant) (stateIdx : Nat) :
    Preserves CompScheduleInv (compromiseIK p stateIdx) := by
  intro tr hInv; unfold DY.Libsignal.PQXDH.compromiseIK
  refine bind_getKey_at p stateIdx .identity tr hInv fun _ _ => (hInv.append_other rfl rfl rfl).append_other rfl rfl rfl

theorem CompScheduleInv.preserves_compromiseSPK (b : Participant) (stateIdx : Nat) :
    Preserves CompScheduleInv (compromiseSPK b stateIdx) := by
  intro tr hInv; unfold DY.Libsignal.PQXDH.compromiseSPK
  refine bind_getKey_at b stateIdx .signedPrekey tr hInv fun _ _ => (hInv.append_other rfl rfl rfl).append_other rfl rfl rfl

theorem CompScheduleInv.preserves_compromisePQSPK (b : Participant) (stateIdx : Nat) :
    Preserves CompScheduleInv (compromisePQSPK b stateIdx) := by
  intro tr hInv; unfold DY.Libsignal.PQXDH.compromisePQSPK
  refine bind_getKey_at b stateIdx .pqPrekey tr hInv fun _ _ => (hInv.append_other rfl rfl rfl).append_other rfl rfl rfl

theorem CompScheduleInv.preserves_compromiseOPK (b : Participant) (stateIdx : Nat) :
    Preserves CompScheduleInv (compromiseOPK b stateIdx) := by
  intro tr hInv; unfold DY.Libsignal.PQXDH.compromiseOPK
  refine bind_getKey_at b stateIdx .oneTimePrekey tr hInv fun _ _ =>
    (Preserves.bind (Preserves.requireTracePredicate _) fun _ _ h =>
      (h.append_other rfl rfl rfl).append_other rfl rfl rfl) tr hInv

theorem CompScheduleInv.preserves_breakDH : Preserves CompScheduleInv breakDH := fun _ h => h.append_other rfl rfl rfl
theorem CompScheduleInv.preserves_breakKEM : Preserves CompScheduleInv breakKEM := fun _ h => h.append_other rfl rfl rfl

theorem CompScheduleInv.preserves_invertDH (pkIdx : Nat) : Preserves CompScheduleInv (invertDH pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertDH
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  split
  · exact fun _ h => h.append_other rfl rfl rfl
  · exact Preserves.failure

theorem CompScheduleInv.preserves_invertKEM (pkIdx : Nat) : Preserves CompScheduleInv (invertKEM pkIdx) := by
  unfold DY.Libsignal.PQXDH.invertKEM
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => Preserves.bind (Preserves.receiveMessage _) fun _ => ?_
  exact Preserves.bind (Preserves.monadLiftErr _) fun _ _ h => h.append_other rfl rfl rfl

theorem CompScheduleInv.preserves_messageEncryptAbort (me : Participant) (stH : Nat) :
    Preserves CompScheduleInv (messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  refine Preserves.bind (Preserves.getLocalState_tr _ _) fun _ => ?_
  exact Preserves.bind (fun _ h => h.append_other rfl rfl rfl) fun _ => Preserves.failure

theorem CompScheduleInv.preserves_aliceStart (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) :
    Preserves CompScheduleInv (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr hInv; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hInv (hInv.append_other rfl rfl rfl)
    fun ikA ikB vkB spk spkSig pqpk pqpkSig opk honest _ _ _ _ _ _ _ _ _ _ _ => ?_
  let t₀ := tr.length; let o := aliceOut tr ikA ikB spk pqpk opk
  let tr1 := tr.append (RndE 32); let tr2 := tr1.append (RndE 32)
  let dhsA := mkRand tr2.length 32; let tr3 := tr2.append (RndE 32)
  let tr4 := tr3.append (NetE o.ek); let tr5 := tr4.append (NetE o.ct); let doneIdx := tr5.length
  let evDone := PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys
  let tr6 := tr5.append (PQEvE evDone); let tr7 := tr6.append (TREvE (.InitSession a b (DiffieHellman.dhPk dhsA) o.spk))
  let stA : TRState := {
    peer := b, myIk := serializedIk o.ikA, peerIk := serializedIk o.ikB,
    rk := (createChain o.keys.rk o.spk dhsA).1, dhs := dhsA,
    cks := (createChain o.keys.rk o.spk dhsA).2, ns := 0, pn := 0,
    sid := Concat.concat (DiffieHellman.dhPk dhsA) o.keys.rk, initiator := true, rIdx := 1,
    recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
    spqr := Spqr.spqrInit o.keys.pqr spqrA2B }
  let tr8 := tr7.append (CEvE (.HandshakeSession (stA.sessionInfo a) doneIdx)); let tr9 := tr8.append (TRStE a stA)
  have hInv6 : CompScheduleInv tr6 :=
    (((((hInv.append_other rfl rfl rfl).append_other rfl rfl rfl).append_other rfl rfl rfl).append_other rfl rfl rfl).append_other rfl rfl rfl).append_other rfl rfl rfl
  have hInv7 : CompScheduleInv tr7 := hInv6.append_trEv trivial; have hInv8 : CompScheduleInv tr8 := hInv7.append_other rfl rfl rfl
  have hle89 : tr8 ≤ tr9 := Trace.append_le tr8 _
  have hle69 : tr6 ≤ tr9 := Trace.le_trans _ _ _ (Trace.append_le tr6 _) (Trace.le_trans _ _ _ (Trace.append_le tr7 _) hle89)
  have hle39 : tr3 ≤ tr9 :=
    Trace.le_trans _ _ _ (Trace.append_le tr3 _)
      (Trace.le_trans _ _ _ (Trace.append_le tr4 _) (Trace.le_trans _ _ _ (Trace.append_le tr5 _) hle69))
  have hle29 : tr2 ≤ tr9 := Trace.le_trans _ _ _ (Trace.append_le tr2 _) hle39
  have hle19 : tr1 ≤ tr9 := Trace.le_trans _ _ _ (Trace.append_le tr1 _) hle29
  have hr0 : RandAt tr9 t₀ 32 := randAt_mono hle19 (Trace.at?_append tr (RndE 32))
  have hr1 : RandAt tr9 (t₀ + 1) 32 := randAt_mono hle29 (Trace.at?_append tr1 (RndE 32))
  have hr2 : RandAt tr9 (t₀ + 2) 32 := randAt_mono hle39 (Trace.at?_append tr2 (RndE 32))
  have hevA9 : tr9.EventLoggedAt evDone doneIdx := eventLoggedAt_mono hle69 (Trace.at?_append tr5 (PQEvE evDone))
  have hhs9 : tr9.EventLogged (ComposedEvent.HandshakeSession (stA.sessionInfo a) doneIdx) :=
    eventLogged_mono hle89 ⟨tr7.length, Trace.at?_append tr7 _⟩
  let ikm := pqxdhIkm (agree o.spk ikA) (agree o.ikB (mkRand t₀ 32)) (agree o.spk (mkRand t₀ 32))
    (o.opk.map (agree · (mkRand t₀ 32))) (PQKem.kemEncap o.pqpk (mkRand (t₀ + 1) 32)).2
  let dh₁ := DiffieHellman.dh (DY.X25519.normalizeX25519Key o.spk) dhsA
  have hhk9 : HandshakeKeysAt tr9 doneIdx (pqxdhKdf ikm) :=
    ⟨a, b, o.ikA, o.ikB, o.spk, o.pqpk, o.opk, .inl ⟨o.ek, o.ct, hevA9⟩⟩
  have hs9 : CompSessionAt tr9 (stA.sessionInfo a) doneIdx ikm dh₁ := by
    refine ⟨hhs9, hhk9, ?_⟩; change if true = true then _ else _; simp only [↓reduceIte]
    exact ⟨a, b, t₀, o.ikA, o.ikB, o.spk, o.pqpk, o.opk, o.ct,
      agree o.spk ikA, agree o.ikB (mkRand t₀ 32), o.opk.map (agree · (mkRand t₀ 32)),
      hr0, hr1, hr2, rfl, hevA9, rfl, rfl, rfl⟩
  refine hInv8.append_trSt ⟨Nat.le_refl 1, rfl, ⟨_, _, _, rfl⟩,
    ⟨doneIdx, ikm, dh₁, hs9, .step_one (pqxdhKdf ikm).rk, ⟨stA.cks, rfl, rfl⟩, ?_⟩,
    ⟨t₀ + 2, randAt_lt_length hr2, hr2, rfl⟩⟩
  intro c hc; rw [List.mem_singleton] at hc; subst hc
  exact ⟨Nat.le_refl 1, Nat.le_refl 1, rfl, (pqxdhKdf ikm).ck, rfl, rfl⟩

theorem CompScheduleInv.preserves_bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves CompScheduleInv (bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  intro tr hInv; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hInv
    fun ikB spkSk pqsk opkSk ikA vkA ek ct honest keys hikB_st hspk_st _ _ _ _ _ _ hagree => ?_
  have hik : CompPQXDHStateOK tr { kind := .identity, sk := ikB } := hInv.pqxStOK b _ kh.ik hikB_st
  have hspk : CompPQXDHStateOK tr { kind := .signedPrekey, sk := spkSk } := hInv.pqxStOK b _ kh.spk hspk_st
  have hne_ik_spk : ikB ≠ spkSk := CompPQXDHStateOK.ik_ne_spk hik hspk
  obtain ⟨t_spk, hspk_eq, hr64_tr⟩ := hspk
  have hkeys := bobAgreement_eq_some_iff.mp hagree; subst hkeys
  let e := (DY.Libsignal.PQXDH.errToOption (PQKem.kemDecap pqsk ct)).getD (PQKem.kemRejKey pqsk ct)
  let ikm := pqxdhIkm (agree ikA spkSk) (agree ek ikB) (agree ek spkSk)
    (opkSk.map (agree ek ·)) e
  rw [run_bind_snd]
  have htr1 : ((receiveSignalMsg mh.msg).run tr).2.val = tr := Preserves.receiveSignalMsg (Inv := fun t => t = tr) mh.msg tr rfl
  rcases ((receiveSignalMsg mh.msg).run tr).1 with _ | msg
  · rw [htr1]; exact hInv
  dsimp only; rw [htr1]
  let st0 : TRState := {
    peer := a, myIk := serializedIk (DiffieHellman.dhPk ikB), peerIk := serializedIk ikA,
    rk := (pqxdhKdf ikm).rk, dhs := spkSk, cks := (pqxdhKdf ikm).ck, ns := 0, pn := 0,
    sid := Concat.concat (DY.X25519.normalizeX25519Key msg.ratchetKey) (pqxdhKdf ikm).rk, initiator := false,
    rIdx := 0, recv := [],
    spqr := Spqr.spqrInit (pqxdhKdf ikm).pqr spqrB2A }
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold DY.Libsignal.TripleRatchet.recvChainFor; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  cases hfind : findRecvChain st0.recv msg.ratchetKey with
  | some c => cases hfind
  | none =>
    dsimp only; by_cases hlo : x25519LowOrder msg.ratchetKey = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hlo h]; exact hInv
    · rw [ite_eq_right_iff.mpr fun h => absurd h hlo]; dsimp only; unfold _root_.guard
      have hlo' : (!x25519LowOrder msg.ratchetKey) = true := by cases h : x25519LowOrder msg.ratchetKey <;> simp_all
      rw [ite_eq_left_iff.mpr fun h => absurd hlo' h,
        run_bind_assoc_snd, run_bind_assoc_snd, run_pure_bind_snd,
        run_bind_assoc_snd, run_genRand_bind_snd, run_pure_bind_snd, run_pure_bind_snd]
      let tr2 := tr.append (RndE 32); have hle02 : tr ≤ tr2 := Trace.append_le tr (RndE 32)
      have hInv2 : CompScheduleInv tr2 := hInv.append_other rfl rfl rfl
      have hr_dhs2 : RandAt tr2 tr.length 32 := Trace.at?_append tr (RndE 32)
      let dhs' := mkRand tr.length 32; let dh₁ := DiffieHellman.dh (DY.X25519.normalizeX25519Key msg.ratchetKey) spkSk
      let rk1 := (createChain (pqxdhKdf ikm).rk msg.ratchetKey spkSk).1
      let ckr := (createChain (pqxdhKdf ikm).rk msg.ratchetKey spkSk).2
      let rk2 := (createChain rk1 msg.ratchetKey dhs').1; let cks := (createChain rk1 msg.ratchetKey dhs').2
      let c : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := ckr, index := 0, rIdx := 2 }
      let st : TRState := { st0 with rk := rk2, dhs := dhs', cks := cks, ns := 0, pn := 0, rIdx := 2, recv := [c] }
      have hrk1 : CompRkSteps dh₁ 1 (pqxdhKdf ikm).rk rk1 := .step_one _
      have hrk2 : CompRkSteps dh₁ 2 (pqxdhKdf ikm).rk rk2 := .step_succ hrk1
      have hc : CompRecvChainScheduleOK dh₁ ikm st.initiator st.rIdx c :=
        ⟨Nat.le_succ 1, Nat.le_refl 2, (rfl : (2 : Nat) % 2 = roleParity false), ckr, rfl, rfl⟩
      have hrecv : ∀ x ∈ st.recv, CompRecvChainScheduleOK dh₁ ikm st.initiator st.rIdx x := by
        intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hc
      have hcks : ∃ ck₀, CompChainRootFrom1 dh₁ ikm st.rIdx ck₀ ∧ st.cks = chainKeyAt ck₀ st.ns.toNat :=
        ⟨cks, ⟨rk1, msg.ratchetKey, dhs', hrk1, rfl⟩, rfl⟩
      rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
      · exact hInv2
      · dsimp only; rcases hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · exact hInv2
        · dsimp only; rw [run_sendMessage_bind_snd]
          let tr3 := tr2.append (NetE key); have hle23 : tr2 ≤ tr3 := Trace.append_le tr2 (NetE key)
          have hInv3 : CompScheduleInv tr3 := hInv2.append_other rfl rfl rfl
          refine bind_receiveMessage_at pqIdx tr3 hInv3 fun pqSalt _ _ => ?_
          rw [run_bind_snd, verifyMacAndDecrypt_trace]
          cases ((verifyMacAndDecrypt _ msg pqSalt seed).run tr3).1 with
          | none => exact hInv3
          | some m =>
            dsimp only
            have h_commit_opk : ∀ (t4 : ExecTrace), tr2 ≤ t4 → CompScheduleInv t4 →
                CompScheduleInv ((do
                  let doneIdx ← traceLength
                  ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk ikB) ikA
                    (DiffieHellman.dhPk spkSk) (PQKem.kemPk pqsk) (opkSk.map DiffieHellman.dhPk)
                    ek ct (pqxdhKdf ikm))
                  if true = true then
                    ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
                    ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
                  ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
                  let skipped := msg.counter.toNat - c.index.toNat
                  let childIdx := (← traceLength) + skipped + 2
                  DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
                  ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
                  DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
                    msg.counter c.rIdx childIdx
                    { st with recv := setRecvChain st.recv c', spqr := spqr' }).run t4).2.val := by
              intro t4 hle24 hInv4; let doneIdx := t4.length
              let evDone := PQXDHEvent.BobDone b a (DiffieHellman.dhPk ikB) ikA
                (DiffieHellman.dhPk spkSk) (PQKem.kemPk pqsk) (opkSk.map DiffieHellman.dhPk)
                ek ct (pqxdhKdf ikm)
              let t5 := t4.append (PQEvE evDone)
              let t6 := t5.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
              let t7 := t6.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
              let t8 := t7.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
              have hInv5 : CompScheduleInv t5 := hInv4.append_other rfl rfl rfl; have hInv6 : CompScheduleInv t6 := hInv5.append_trEv trivial
              have hInv7 : CompScheduleInv t7 := hInv6.append_trEv trivial; have hInv8 : CompScheduleInv t8 := hInv7.append_other rfl rfl rfl
              have hle58 : t5 ≤ t8 :=
                Trace.le_trans _ _ _ (Trace.append_le t5 _)
                  (Trace.le_trans _ _ _ (Trace.append_le t6 _) (Trace.append_le t7 _))
              have hle28 : tr2 ≤ t8 := Trace.le_trans _ _ _ hle24 (Trace.le_trans _ _ _ (Trace.append_le t4 _) hle58)
              have hle08 : tr ≤ t8 := Trace.le_trans _ _ _ hle02 hle28
              have hevB8 : t8.EventLoggedAt evDone doneIdx := eventLoggedAt_mono hle58 (Trace.at?_append t4 (PQEvE evDone))
              have hhs8 : t8.EventLogged (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx) := ⟨t7.length, Trace.at?_append t7 _⟩
              have hhk8 : HandshakeKeysAt t8 doneIdx (pqxdhKdf ikm) :=
                ⟨a, b, ikA, DiffieHellman.dhPk ikB, DiffieHellman.dhPk spkSk,
                  PQKem.kemPk pqsk, opkSk.map DiffieHellman.dhPk, .inr ⟨ek, ct, hevB8⟩⟩
              have hs8 : CompSessionAt t8 (st.sessionInfo b) doneIdx ikm dh₁ := by
                refine ⟨hhs8, hhk8, ?_⟩; change if false = true then _ else _; simp only [Bool.false_eq_true, ↓reduceIte]
                exact ⟨b, a, t_spk, ikB, ikA, spkSk, pqsk, opkSk.map DiffieHellman.dhPk,
                  ek, ct, opkSk.map (agree ek ·), e,
                  hspk_eq, randAt_mono hle08 hr64_tr, hne_ik_spk, hevB8, rfl, rfl, rfl, msg.ratchetKey, rfl, rfl⟩
              have hr_dhs8 : RandAt t8 tr.length 32 := randAt_mono hle28 hr_dhs2
              exact schedule_decryptTail b
                (t8.length + (msg.counter.toNat - c.index.toNat) + 2)
                (t8.length + (msg.counter.toNat - c.index.toNat) + 2)
                doneIdx ikm dh₁ st msg c c' seed pqSalt m spqr' t8 hInv8
                (Nat.le_succ 1) (rfl : (2 : Nat) % 2 = roleParity false) ⟨_, _, _, rfl⟩ hs8 hrk2 hcks hrecv
                ⟨tr.length, randAt_lt_length hr_dhs8, hr_dhs8, rfl⟩ hc hcons
            rcases opkSk with _ | o
            · exact h_commit_opk tr3 hle23 hInv3
            · dsimp only [Option.map]
              refine bind_guardOnTrace_at _ tr3 hInv3 fun _ => ?_
              exact h_commit_opk (tr3.append (PQEvE (.OPKUsed b (DiffieHellman.dhPk o))))
                (Trace.le_trans _ _ _ hle23 (Trace.append_le tr3 _)) (hInv3.append_other rfl rfl rfl)

theorem CompScheduleInv.preserves_messageEncrypt (me : Participant) (stH coinsLen pqIdx : Nat) :
    Preserves CompScheduleInv (messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  unfold _root_.guard; by_cases hns : st.ns ≠ u32Max
  · rw [ite_eq_left_iff.mpr fun h => absurd hns h, run_pure_bind_snd,
      run_genRand_bind_snd, run_genRand_bind_snd, run_sendMessage_bind_snd]
    let ts := tr₀.length; let m := mkRand ts 32
    let coins := mkRand (ts + 1) coinsLen; let key := (Spqr.spqrSend st.spqr coins).2.1
    let tr₁ := tr₀.append (RndE 32); let tr₂ := tr₁.append (RndE coinsLen); let tr₃ := tr₂.append (NetE key)
    have hle₁₃ : tr₁ ≤ tr₃ := Trace.le_trans _ _ _ (Trace.append_le tr₁ _) (Trace.append_le tr₂ _)
    have hle₀₃ : tr₀ ≤ tr₃ := Trace.le_trans _ _ _ (Trace.append_le tr₀ _) hle₁₃
    have hInv₃ : CompScheduleInv tr₃ := ((hInv₀.append_other rfl rfl rfl).append_other rfl rfl rfl).append_other rfl rfl rfl
    refine bind_receiveMessage_at pqIdx tr₃ hInv₃ fun pqSalt _ _ => ?_
    let evSent := TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m
    let tr₄ := tr₃.append (TREvE evSent); have hle₄ : tr₃ ≤ tr₄ := Trace.append_le tr₃ _
    have hle₁₄ : tr₁ ≤ tr₄ := Trace.le_trans _ _ _ hle₁₃ hle₄; have hle₀₄ : tr₀ ≤ tr₄ := Trace.le_trans _ _ _ hle₀₃ hle₄
    have hr_m₄ : RandAt tr₄ ts 32 := randAt_mono hle₁₄ (Trace.at?_append tr₀ (RndE 32))
    have hInv₄ : CompScheduleInv tr₄ := hInv₃.append_trEv (ev := evSent) ⟨ts, randAt_lt_length hr_m₄, hr_m₄, rfl⟩
    obtain ⟨hpos, hpar, hrk_shape, ⟨doneIdx, ikm, dh₁, hs, hrk, ⟨ck₀, hroot, hck₀⟩, hrecv⟩, hdhs⟩ :=
      (hInv₀.stateOK me st stH hst₀).mono hle₀₄
    have hcks' : (kdfCk st.cks).1 = chainKeyAt ck₀ (st.ns + 1).toNat := by
      rw [hck₀, uint32_toNat_add_one_of_ne_u32Max hns, chainKeyAt_succ_eq_kdfCk_fst]
    have hst' : CompStateScheduleOK tr₄ me
        { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 } :=
      ⟨hpos, hpar, hrk_shape, ⟨doneIdx, ikm, dh₁, hs, hrk, ⟨ck₀, hroot, hcks'⟩, hrecv⟩, hdhs⟩
    have hev_mk : CompEventScheduleOK tr₄
        (.MessageKey (st.sessionInfo me) .sender (kdfCk st.cks).2 pqSalt st.ns st.rIdx stH) :=
      ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs, hroot, by rw [hck₀]⟩
    exact (schedule_logMessageKeyAndStore me (st.sessionInfo me)
      .sender (kdfCk st.cks).2 pqSalt st.ns st.rIdx stH
      { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }
      tr₄ hev_mk hst' hInv₄).append_other rfl rfl rfl
  · rw [ite_eq_right_iff.mpr fun h => absurd h hns]; exact hInv₀

theorem CompScheduleInv.preserves_messageDecrypt (me : Participant) (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves CompScheduleInv (messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine Preserves.bind_getLocalState_tr me stH fun st₀ tr₀ hInv₀ hst₀ => ?_
  rw [run_bind_snd]
  have htr1 : ((receiveSignalMsg msgH).run tr₀).2.val = tr₀ := Preserves.receiveSignalMsg (Inv := fun t => t = tr₀) msgH tr₀ rfl
  rcases ((receiveSignalMsg msgH).run tr₀).1 with _ | msg
  · rw [htr1]; exact hInv₀
  dsimp only; rw [htr1]
  refine bind_ensureReceiverChain_schedule me st₀ msg.ratchetKey tr₀ (hInv₀.stateOK me st₀ stH hst₀) hInv₀
    fun st c ratcheted tr₁ doneIdx ikm dh₁ _ hInv₁ hpos hpar hrk_shape hs₁ hrk hcks hrecv hc hdhs => ?_
  dsimp only; rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · exact hInv₁
  · dsimp only; rcases hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact hInv₁
    · dsimp only; rw [run_sendMessage_bind_snd]
      let tr₁' := tr₁.append (NetE key); have hle₁' : tr₁ ≤ tr₁' := Trace.append_le tr₁ _
      have hInv₁' : CompScheduleInv tr₁' := hInv₁.append_other rfl rfl rfl
      have hs₁' : CompSessionAt tr₁' (st.sessionInfo me) doneIdx ikm dh₁ := hs₁.mono hle₁'
      obtain ⟨ts, _, hr_dhs₁, hdhs_eq⟩ := hdhs; have hr_dhs₁' := randAt_mono hle₁' hr_dhs₁
      refine bind_receiveMessage_at pqIdx tr₁' hInv₁' fun pqSalt _ _ => ?_
      rw [run_bind_snd, verifyMacAndDecrypt_trace]
      rcases ((verifyMacAndDecrypt st msg pqSalt seed).run tr₁').1 with _ | m
      · exact hInv₁'
      dsimp only; cases ratcheted with
      | false =>
        exact schedule_decryptTail me stH stH doneIdx ikm dh₁ st msg c c' seed pqSalt m spqr'
          tr₁' hInv₁' hpos hpar hrk_shape hs₁' hrk hcks hrecv
          ⟨ts, randAt_lt_length hr_dhs₁', hr_dhs₁', hdhs_eq⟩ hc hcons
      | true =>
        let tr₂ := tr₁'.append (TREvE (.DHRatchet me st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
        let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo me) st.dhs (st.rIdx - 2)))
        have hle₁'₃ : tr₁' ≤ tr₃ := Trace.le_trans _ _ _ (Trace.append_le tr₁' _) (Trace.append_le tr₂ _)
        have hInv₂ : CompScheduleInv tr₂ := hInv₁'.append_trEv trivial; have hInv₃ : CompScheduleInv tr₃ := hInv₂.append_trEv trivial
        have hr_dhs₃ := randAt_mono hle₁'₃ hr_dhs₁'
        exact schedule_decryptTail me stH stH doneIdx ikm dh₁ st msg c c' seed pqSalt m spqr'
          tr₃ hInv₃ hpos hpar hrk_shape (hs₁'.mono hle₁'₃) hrk hcks hrecv
          ⟨ts, randAt_lt_length hr_dhs₃, hr_dhs₃, hdhs_eq⟩ hc hcons

theorem CompScheduleInv.preserves_messageDecryptSkipped (me : Participant) (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves CompScheduleInv (messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine Preserves.bind_getLocalState_tr me stH fun st tr₀ hInv₀ hst₀ => ?_
  rw [run_bind_snd]
  have htr1 : ((receiveSignalMsg msgH).run tr₀).2.val = tr₀ := Preserves.receiveSignalMsg (Inv := fun t => t = tr₀) msgH tr₀ rfl
  rcases ((receiveSignalMsg msgH).run tr₀).1 with _ | msg
  · rw [htr1]; exact hInv₀
  dsimp only; rw [htr1]
  refine bind_getEntry_tr_at evH tr₀ hInv₀ fun e hev₀ => ?_
  rcases e with ⟨ev⟩; cases ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only; refine bind_guardP_at _ tr₀ hInv₀ fun _ => bind_guardTrace_at _ tr₀ hInv₀ fun _ => ?_
    rcases hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact hInv₀
    · dsimp only; rw [run_sendMessage_bind_snd]
      let tr₁ := tr₀.append (NetE key); have hle₁ : tr₀ ≤ tr₁ := Trace.append_le tr₀ _
      have hInv₁ : CompScheduleInv tr₁ := hInv₀.append_other rfl rfl rfl
      refine bind_receiveMessage_at pqIdx tr₁ hInv₁ fun pqSalt _ _ => ?_
      rw [run_bind_snd, verifyMacAndDecrypt_trace]
      rcases ((verifyMacAndDecrypt st msg pqSalt seed).run tr₁).1 with _ | m
      · exact hInv₁
      dsimp only; obtain ⟨hpos_ev, hpar_ev, doneIdx, ikm, dh₁, ck₀, hs, hroot, hseed⟩ := hInv₀.eventOK _ hev₀
      let tr₂ := tr₁.append (TREvE (.SkippedKeyUsed s evH))
      let tr₃ := tr₂.append (TREvE (.Received me st.peer pk n m))
      have hle₀₃ : tr₀ ≤ tr₃ := Trace.le_trans _ _ _ hle₁ (Trace.le_trans _ _ _ (Trace.append_le tr₁ _) (Trace.append_le tr₂ _))
      have hInv₂ : CompScheduleInv tr₂ := hInv₁.append_trEv trivial; have hInv₃ : CompScheduleInv tr₃ := hInv₂.append_trEv trivial
      obtain ⟨hpos_st, hpar_st, hrk_shape, hsched_st, hdhs_st⟩ := (hInv₀.stateOK me st stH hst₀).mono hle₀₃
      exact schedule_logMessageKeyAndStore me s .receiver seed pqSalt n rIdx stH { st with spqr := spqr' } tr₃
        ⟨hpos_ev, hpar_ev, doneIdx, ikm, dh₁, ck₀, hs.mono hle₀₃, hroot, hseed⟩
        ⟨hpos_st, hpar_st, hrk_shape, hsched_st, hdhs_st⟩ hInv₃
  | _ => exact hInv₀

theorem CompScheduleInv.preserves_exposeKey (me : Participant) (stH : Nat) (kc : KeyComponent) :
    Preserves CompScheduleInv (exposeKey me stH kc) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine Preserves.bind_getLocalState_tr me stH fun st tr hInv hst => ?_
  obtain ⟨hpos, hpar, hrk_shape, ⟨doneIdx, ikm, dh₁, hs, hrk, ⟨ck₀, hroot, hcks⟩, hrecv⟩, ⟨ts, _, hr_dhs, hdhs⟩⟩ :=
    hInv.stateOK me st stH hst
  cases kc with
  | rk =>
    have hle := Trace.append_le tr (TREvE (.ExposedRK (st.sessionInfo me) st.rk st.rIdx))
    exact (hInv.append_trEv (ev := .ExposedRK (st.sessionInfo me) st.rk st.rIdx)
      ⟨hpos, hpar, hrk_shape, doneIdx, ikm, dh₁, hs.mono hle, hrk⟩).append_other rfl rfl rfl
  | dhs =>
    have hle := Trace.append_le tr (TREvE (.ExposedDHs (st.sessionInfo me) st.dhs st.rIdx))
    have hr' := randAt_mono hle hr_dhs
    exact (hInv.append_trEv (ev := .ExposedDHs (st.sessionInfo me) st.dhs st.rIdx)
      ⟨ts, randAt_lt_length hr', hr', hdhs⟩).append_other rfl rfl rfl
  | cks =>
    have hle := Trace.append_le tr (TREvE (.ExposedCKs (st.sessionInfo me) st.cks st.ns st.rIdx))
    exact (hInv.append_trEv (ev := .ExposedCKs (st.sessionInfo me) st.cks st.ns st.rIdx)
      ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs.mono hle, hroot, hcks⟩).append_other rfl rfl rfl
  | ckr pk =>
    dsimp only; cases hfind : findRecvChain st.recv pk with
    | none => exact hInv
    | some c =>
      obtain ⟨hc_pos, _, hc_par, ck_r, hroot_r, hck_r⟩ := hrecv c (findRecvChain_some hfind).1
      have hle := Trace.append_le tr (TREvE (.ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx))
      exact (hInv.append_trEv (ev := .ExposedCKr (st.sessionInfo me) c.chainKey c.index c.rIdx)
        ⟨hc_pos, hc_par, doneIdx, ikm, dh₁, ck_r, hs.mono hle, hroot_r, hck_r⟩).append_other rfl rfl rfl

theorem CompScheduleInv.preserves_exposeSpqr (me : Participant) (stH : Nat) :
    Preserves CompScheduleInv (exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  refine Preserves.bind_getLocalState_tr me stH fun st _ hInv _ => ?_
  exact (hInv.append_trEv (ev := .ExposedSpqr (st.sessionInfo me) st.spqr st.rIdx) trivial).append_other rfl rfl rfl

theorem CompScheduleInv.preserves_exposeSkipped (evH : Nat) : Preserves CompScheduleInv (exposeSkipped evH) := by
  intro tr₀ hInv₀; unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine bind_getEntry_tr_at evH tr₀ hInv₀ fun e hev => ?_
  rcases e with ⟨ev⟩; cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    dsimp only; refine bind_guardTrace_at _ tr₀ hInv₀ fun _ => ?_
    obtain ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs, hroot, hseed⟩ := hInv₀.eventOK _ hev
    have hle := Trace.append_le tr₀ (TREvE (.ExposedMK s seed n rIdx))
    exact (hInv₀.append_trEv (ev := .ExposedMK s seed n rIdx)
      ⟨hpos, hpar, doneIdx, ikm, dh₁, ck₀, hs.mono hle, hroot, hseed⟩).append_other rfl rfl rfl
  | _ => exact hInv₀

/-- Every trace reachable under `Composed.reachability` satisfies `CompScheduleInv`. -/
theorem compScheduleInv_reachable {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability) : CompScheduleInv tr :=
  composed_reachable_induction CompScheduleInv.nil (fun _ _ _ hInv => hInv.append_other rfl rfl rfl)
    CompScheduleInv.preserves_registerIdentity CompScheduleInv.preserves_registerCorruptIdentity
    CompScheduleInv.preserves_genSignedPrekey CompScheduleInv.preserves_genPQPrekey
    CompScheduleInv.preserves_genOneTimePrekey CompScheduleInv.preserves_aliceStart
    CompScheduleInv.preserves_bobStart CompScheduleInv.preserves_messageEncrypt
    CompScheduleInv.preserves_messageEncryptAbort CompScheduleInv.preserves_messageDecrypt
    CompScheduleInv.preserves_messageDecryptSkipped CompScheduleInv.preserves_exposeKey
    CompScheduleInv.preserves_exposeSpqr CompScheduleInv.preserves_exposeSkipped
    CompScheduleInv.preserves_compromiseIK CompScheduleInv.preserves_compromiseSPK
    CompScheduleInv.preserves_compromisePQSPK CompScheduleInv.preserves_compromiseOPK
    CompScheduleInv.preserves_breakDH CompScheduleInv.preserves_breakKEM
    CompScheduleInv.preserves_invertDH CompScheduleInv.preserves_invertKEM hreach

end Symbolic.Swarm.COMPOSED.CompRatchet

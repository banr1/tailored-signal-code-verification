/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSepGood
public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkPeel
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.RatchetDHRkSwapPeelTR

/-!
# Relaxed Seed Separation for `Good` Spine Terms

Proves `seedSepAK_good` and packages `seedSepAKRun_of` for `Q := Good T` from `RecvLinkStored`,
`RkTwinStmt`, `RkTwinStoredStmt`, and `RootTwinStmt` by normalising honest and skipped-seed terms
into `UNF` and discharging the root-key and chain-key twin cases.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.TripleRatchet (RecvChain createChain chainKeyAt kdfCk hkdfBlock1 hkdfBlock2 lit
  litByte findRecvChain)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace Symbolic.Swarm.COMPOSED

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Chains over attacker-known roots -/

theorem ckOut_split_of_ak {T : ExecTrace} {s₀ i₀ : DY.Bytes} (hs : s₀.AttackerKnows T)
    (hi : i₀.AttackerKnows T) (b : Bool) (j : Nat) :
    ∃ s i, ckOut b (chainKeyAt (KdfExtract.kdfExtract s₀ i₀) j) = KdfExtract.kdfExtract s i ∧
      s.AttackerKnows T ∧ i.AttackerKnows T := by
  have hX : (KdfExtract.kdfExtract s₀ i₀).AttackerKnows T := ak_hmac hs hi
  cases b with
  | true =>
    exact ⟨chainKeyAt (KdfExtract.kdfExtract s₀ i₀) j, litByte 1, rfl,
      attackerKnows_chainKeyAt_srk j hX, ak_lit _⟩
  | false =>
    cases j with
    | zero => exact ⟨s₀, i₀, rfl, hs, hi⟩
    | succ j =>
      refine ⟨chainKeyAt (KdfExtract.kdfExtract s₀ i₀) j, litByte 2, ?_,
        attackerKnows_chainKeyAt_srk j hX, ak_lit _⟩
      exact chainKeyAt_succ_eq_kdfCk_fst _ j

theorem ckOut_hkdfBlock2_split_of_ak {T : ExecTrace} {prk : DY.Bytes} (hp : prk.AttackerKnows T)
    (b : Bool) (j : Nat) :
    ∃ s i, ckOut b (chainKeyAt (hkdfBlock2 prk (lit "WhisperRatchet")) j) =
      KdfExtract.kdfExtract s i ∧ s.AttackerKnows T ∧ i.AttackerKnows T :=
  ckOut_split_of_ak (s₀ := prk)
    (i₀ := Concat.concat (hkdfBlock1 prk (lit "WhisperRatchet"))
      (Concat.concat (lit "WhisperRatchet") (litByte 2)))
    hp (ak_concat (ak_hkdfBlock1 hp (ak_lit _)) (ak_concat (ak_lit _) (ak_lit _))) b j

/-! ## Normal form of honest and skipped-seed terms -/

/-- Decomposition of an honest KDF output or logged skipped seed into a stored root key, a chain
output over `RootX`, or a `kdfExtract` on attacker-known inputs. -/
def UNF (T : ExecTrace) (u : DY.Bytes) : Prop :=
  (∃ (p : Participant) (st : TRState) (i₀ : Nat), TRStateStoredAt p st i₀ T ∧ u = st.rk) ∨
  (∃ (X : DY.Bytes) (j : Nat) (b : Bool), RootX T X ∧ u = ckOut b (chainKeyAt X j)) ∨
  (∃ s i, u = KdfExtract.kdfExtract s i ∧ s.AttackerKnows T ∧ i.AttackerKnows T)

theorem unf_of_cks {T : ExecTrace} (hT : ReachableTrace T) {p : Participant} {st : TRState}
    {i₀ : Nat} (hst : TRStateStoredAt p st i₀ T) : UNF T st.cks := by
  obtain ⟨rk1, k, j, hcks, hrk⟩ := stCksIsCreateChain_of_stored hT hst
  exact .inr (.inl ⟨(createChain rk1 k st.dhs).2, j, false,
    .inl ⟨p, st, i₀, j, hst, hcks, rk1, k, rfl, hrk⟩, hcks⟩)

theorem unf_of_recv {T : ExecTrace} (hT : ReachableTrace T) (hLink : RecvLinkStored T)
    {p : Participant} {st : TRState} {i₀ : Nat} (hst : TRStateStoredAt p st i₀ T)
    {c : RecvChain} (hc : c ∈ st.recv) (b : Bool) (j' : Nat) :
    UNF T (ckOut b (chainKeyAt c.chainKey j')) := by
  rcases (stRkSpine_of_stored hT hst).2 c hc with
    ⟨rk', t, j, -, -, hcj, hH | hprk⟩ | ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j, hcj, -⟩
  · rw [hcj, chainKeyAt_add]
    exact .inr (.inl ⟨_, j + j', b, .inl hH, rfl⟩)
  · rw [hcj, createChain_snd_eq, chainKeyAt_add]
    exact .inr (.inr (ckOut_hkdfBlock2_split_of_ak hprk b (j + j')))
  · obtain ⟨R, jR, hcR, hR⟩ := hLink hst c hc
    rcases hR with ⟨p₀, st₀, i₀', hst₀, rfl⟩ | ⟨keys, t, b', idx, hB, hspk, rfl⟩ | ⟨keys, hk, rfl⟩
    · exact absurd (hcR.symm.trans hcj) (createChain_snd_ne_pqxdhKdf_ck _ _ _ _ _ _)
    · exact absurd (hcR.symm.trans hcj) (createChain_snd_ne_pqxdhKdf_ck _ _ _ _ _ _)
    · rw [hcR, chainKeyAt_add]
      exact .inr (.inl ⟨keys.ck, jR + j', b, .inr ⟨keys, hk, rfl⟩, rfl⟩)

theorem unf_of_active {T : ExecTrace} {c : RecvChain} (hc : ActiveRecvChainSpine T c) :
    UNF T (kdfCk c.chainKey).2 := by
  rcases hc with ⟨rk', t, j, -, -, hcj, hH | hprk⟩ |
      ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j, hcj, hak⟩
  · rw [hcj]
    exact .inr (.inl ⟨_, j, true, .inl hH, rfl⟩)
  · rw [hcj, createChain_snd_eq]
    exact .inr (.inr (ckOut_hkdfBlock2_split_of_ak hprk true j))
  · rw [hcj]
    exact .inr (.inr ⟨_, litByte 1, rfl, attackerKnows_chainKeyAt_srk j hak, ak_lit _⟩)

theorem unf_of_honest {T : ExecTrace} (hT : ReachableTrace T) (hLink : RecvLinkStored T)
    {u : DY.Bytes} (hu : HonestKdfOut T u ∨ SkippedSeedLogged T u) : UNF T u := by
  rcases hu with ⟨me, st, idx, hst, rfl | rfl | ⟨c, hc, rfl⟩⟩ | ⟨k, ses, pk, n, rIdx, src, hev⟩
  · exact .inl ⟨me, st, idx, hst, rfl⟩
  · exact unf_of_cks hT hst
  · exact unf_of_recv hT hLink hst hc false 0
  · obtain ⟨c, hc, rfl⟩ := (jRkSpine_reachable hT (Trace.le_refl T)).2 k ses pk n u rIdx src hev
    exact unf_of_active hc

/-! ## Twin comparisons -/

section Twin

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

theorem rootX_form {T : ExecTrace} (hT : ReachableTrace T) {X : DY.Bytes} (h : RootX T X) :
    ∃ prk lbl, X = hkdfBlock2 prk lbl := by
  rcases h with ⟨p', st', i', j', hst', hcks, rk1, k, rfl, hrk⟩ | ⟨keys, hk, rfl⟩
  · exact ⟨_, _, createChain_snd_eq _ _ _⟩
  · obtain ⟨ikm, rfl⟩ := aliceDoneKeys_pqxdh hT hk
    exact ⟨_, _, pqxdhKdf_ck_eq ikm⟩

theorem twin_stored {T : ExecTrace} (hT : ReachableTrace T) (hRkTwin : RkTwinStmt i S g T)
    (hRkTwinStored : RkTwinStoredStmt i S g T) {p : Participant} {st : TRState} {i₀ : Nat}
    (hst : TRStateStoredAt p st i₀ T) {v t₁ t₂ : DY.Bytes} (hv : Good T v)
    (hm₁ : ∀ e ∈ (gamma' i S g st.rk).memo, e ∈ (gamma' i S g t₁).memo)
    (hm₂ : ∀ e ∈ (gamma' i S g v).memo, e ∈ (gamma' i S g t₂).memo)
    (hsh : (gamma' i S g st.rk).shape = (gamma' i S g v).shape) :
    st.rk = v := by
  obtain ⟨prk, hrk⟩ := stored_rk_form hT hst
  rcases hv with ⟨pk, R, j, b, hR, rfl⟩ | ⟨p₂, st₂, i₂, hst₂, rfl⟩ | ⟨pk, hx⟩ | ⟨keys, hk, rfl⟩
  · obtain ⟨prkR, lblR, rfl⟩ := recvRoot_form' hT hR
    rw [hrk, shape_hkdfBlock1, shape_ckOut_chainKeyAt_hkdfBlock2] at hsh
    exact absurd hsh.symm (ckOut_ne_hkdfBlock1 b _ _ _ _ j)
  · exact hRkTwinStored hst hst₂ hm₁ hm₂ hsh
  · exact hRkTwin hst hx hm₁ hm₂ hsh
  · obtain ⟨ikm, rfl⟩ := doneKeys_pqxdh hT hk
    rw [hrk, pqxdhKdf_rk_eq, shape_hkdfBlock1, shape_hkdfBlock1, shape_lit, shape_pqxdhLabel] at hsh
    exact absurd (hkdfBlock1_inj hsh).2.symm pqxdhLabel_ne_whisperRatchet_rk

theorem twin_root {T : ExecTrace} (hT : ReachableTrace T) (hRootTwin : RootTwinStmt i S g T)
    {X : DY.Bytes} (hX : RootX T X) (j : Nat) (b : Bool) {v t₁ t₂ : DY.Bytes} (hv : Good T v)
    (hm₁ : ∀ e ∈ (gamma' i S g (ckOut b (chainKeyAt X j))).memo, e ∈ (gamma' i S g t₁).memo)
    (hm₂ : ∀ e ∈ (gamma' i S g v).memo, e ∈ (gamma' i S g t₂).memo)
    (hsh : (gamma' i S g (ckOut b (chainKeyAt X j))).shape = (gamma' i S g v).shape) :
    ckOut b (chainKeyAt X j) = v := by
  obtain ⟨prkX, lblX, hXf⟩ := rootX_form hT hX
  rcases hv with ⟨pk, R, j', b', hR, rfl⟩ | hv
  · obtain ⟨prkR, lblR, hRf⟩ := recvRoot_form' hT hR
    have hsh' := hsh
    rw [hXf, hRf, shape_ckOut_chainKeyAt_hkdfBlock2, shape_ckOut_chainKeyAt_hkdfBlock2] at hsh'
    obtain ⟨hb, hj, hroot⟩ := ckOut_align hsh'
    rw [← shape_hkdfBlock2, ← shape_hkdfBlock2, ← hXf, ← hRf] at hroot
    have h := hRootTwin hX hR (fun e he => hm₁ _ (memo_ckOut i S g b j he))
        (fun e he => hm₂ _ (memo_ckOut i S g b' j' he)) hroot
    rw [h, hb, hj]
  · obtain ⟨prk, lbl, hvf⟩ := goodRk_form' hT hv
    rw [hXf, hvf, shape_ckOut_chainKeyAt_hkdfBlock2, shape_hkdfBlock1] at hsh
    exact absurd hsh (ckOut_ne_hkdfBlock1 b _ _ _ _ j)

/-- Proves `SeedSepAK` for `Good T` when `t₁` and `t₂` have no `KemSlotAlias`. -/
theorem seedSepAK_good {T : ExecTrace} (hT : ReachableTrace T) (hLink : RecvLinkStored T)
    (hRkTwin : RkTwinStmt i S g T) (hRkTwinStored : RkTwinStoredStmt i S g T)
    (hRootTwin : RootTwinStmt i S g T) (t₁ t₂ : DY.Bytes) :
    SeedSepAK i S g T (Good T) t₁ t₂ := by
  intro u v _ hu hv hm₁ hm₂ hsh
  rcases unf_of_honest hT hLink hu with ⟨p, st, i₀, hst, rfl⟩ | ⟨X, j, b, hX, rfl⟩ | h4
  · exact .inl (twin_stored i S g hT hRkTwin hRkTwinStored hst hv hm₁ hm₂ hsh)
  · exact .inl (twin_root i S g hT hRootTwin hX j b hv hm₁ hm₂ hsh)
  · exact .inr (.inr h4)

end Twin

/-! ## Receive seeds and run-level package -/

theorem good_of_recvSeed {T : ExecTrace} (hLink : RecvLinkStored T) {p : Participant}
    {st : TRState} {i₀ : Nat} (hst : TRStateStoredAt p st i₀ T) {msg : TRSignalMsg}
    {seed : DY.Bytes} (hseed : recvSeed st msg = some seed) : Good T seed := by
  rcases hf : findRecvChain st.recv msg.ratchetKey with _ | c
  · rw [recvSeed_eq_of_findRecvChain_none hf hseed]
    exact .inl ⟨msg.ratchetKey, _, msg.counter.toNat, true,
      .inl ⟨p, st, i₀, hst, rfl⟩, rfl⟩
  · obtain ⟨hc, -, rfl⟩ := recvSeed_eq_of_findRecvChain_some hf hseed
    obtain ⟨R, j, hcR, hR⟩ := hLink hst c hc
    rw [hcR, chainKeyAt_add]
    exact .inl ⟨c.ratchetKey, R, j + (msg.counter.toNat - c.index.toNat), true, hR, rfl⟩

/-- Run-level package of `SeedSepAK` for `Q` over `runTraceMoves r₀ ms`. -/
structure SeedSepAKRun (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (Q : DY.Bytes → Prop) : Prop where
  down : SpineDown Q
  seed : ∀ {st : TRState} {msg : TRSignalMsg} {seed : DY.Bytes},
    st ∈ DY.Libsignal.Composed.Refinement.availableStates r₀ (runTraceMoves r₀ ms) →
    recvSeed st msg = some seed → Q seed
  sep  : ∀ t₁ t₂ : DY.Bytes, SeedSepAK interpretation S g (runTraceMoves r₀ ms) Q t₁ t₂

/-- Assembles `SeedSepAKRun` for `Good (runTraceMoves r₀ ms)` from `RecvLinkStored`, `RkTwinStmt`,
`RkTwinStoredStmt`, and `RootTwinStmt`. -/
theorem seedSepAKRun_of (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (hT : ReachableTrace (runTraceMoves r₀ ms))
    (hLink : RecvLinkStored (runTraceMoves r₀ ms))
    (hRkTwin : RkTwinStmt interpretation S g (runTraceMoves r₀ ms))
    (hRkTwinStored : RkTwinStoredStmt interpretation S g (runTraceMoves r₀ ms))
    (hRootTwin : RootTwinStmt interpretation S g (runTraceMoves r₀ ms)) :
    SeedSepAKRun interpretation r₀ S g ms (Good (runTraceMoves r₀ ms)) where
  down := spineDown_good hT
  seed := fun hst hseed => by
    obtain ⟨p, j, hst'⟩ := trStateStoredAt_of_mem_availableStates hst
    exact good_of_recvSeed hLink hst' hseed
  sep := seedSepAK_good interpretation S g hT hLink hRkTwin hRkTwinStored hRootTwin

end Symbolic.Swarm.CREF.TR.G1.Spine

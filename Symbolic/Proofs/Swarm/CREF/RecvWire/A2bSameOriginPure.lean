/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompSchedule
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecBasePure
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.Swarm.COMPOSED.CompRatchet
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.RatchetDHRkSwapPeelTR
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Same-Session Seed and Ratchet-Index Equality From Equal `gamma'` Shapes

Proves `a2b_sameOrigin_seed_eq_core` on reachable composed traces: when `st₀` and `st` belong to
the same session and `findRecvChain st.recv msg.ratchetKey = some c`, equal `gamma'` shapes of
`seed_c` and `seed_s` force `seed_s = seed_c ∧ rIdx_s = c.rIdx`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding NetE RndE TRStateStoredAt at?_append_of_lt gamma_concat gamma_dhPk getLocalState_fst kemDecap_eq_some_iff mem_availableStates_of_trStateStoredAt newRandoms_append_rnd proj_inj_eq runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry

cref_open
cref_open_tr
attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain consumeMessageKey chainKeyAt
  kdfCk kdfRk createChain hmac zeroSalt hkdfBlock1 hkdfBlock2)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys pqxdhKdf)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompKeyInversion Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Swarm.COMPOSED.CompRatchet

/-! ## Same-`SessionInfo` Uniqueness -/

theorem compSessionAt_same_sinfo_eq {tr : ExecTrace} {s : SessionInfo} {d₁ d₂ : Nat}
    {ikm₁ ikm₂ dh₁ dh₂ : DY.Bytes}
    (hs₁ : CompSessionAt tr s d₁ ikm₁ dh₁)
    (hs₂ : CompSessionAt tr s d₂ ikm₂ dh₂) :
    ikm₁ = ikm₂ ∧ dh₁ = dh₂ := by
  have hrole₁ := hs₁.2.2
  have hrole₂ := hs₂.2.2
  cases hinit : s.initiator with
  | false =>
    simp only [hinit, Bool.false_eq_true, ↓reduceIte] at hrole₁ hrole₂
    obtain ⟨_, _, _, ikB₁, ikA₁, spkSk₁, pqsk₁, _, ek₁, _, dh4₁, e₁, _, _, hne₁, _, _, _, hikm₁, pk₁, hsid₁, hdh₁⟩ := hrole₁
    obtain ⟨_, _, _, ikB₂, ikA₂, spkSk₂, pqsk₂, _, ek₂, _, dh4₂, e₂, _, _, _, _, _, _, hikm₂, pk₂, hsid₂, hdh₂⟩ := hrole₂
    obtain ⟨hpk_eq, hrk_eq⟩ := concat_inj (hsid₁.symm.trans hsid₂)
    have hikm : ikm₁ = ikm₂ := pqxdhKdf_rk_inj hrk_eq
    subst hikm
    obtain ⟨_, hdh2_eq, hdh3_eq, _⟩ := pqxdhIkm_inj_parts (hikm₁.symm.trans hikm₂)
    have hspk_eq : spkSk₁ = spkSk₂ := Classical.byContradiction fun hne_spk => by
      obtain ⟨hek₁, hek₂⟩ := dh_eq_of_sk_ne hne_spk hdh3_eq
      rw [hek₁, hek₂] at hdh2_eq
      rcases dh_eq_dh_dhPk_cases hdh2_eq with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hne_spk (dhPk_inj h1).symm
      · exact hne₁ h2
    refine ⟨rfl, ?_⟩
    rw [hdh₁, hdh₂, hpk_eq, hspk_eq]
  | true =>
    simp only [hinit, ↓reduceIte] at hrole₁ hrole₂
    obtain ⟨_, _, t₀₁, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs₁_eq, _, _⟩ := hrole₁
    obtain ⟨_, _, t₀₂, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs₂_eq, _, _⟩ := hrole₂
    have hsid_eq := (congrArg SessionInfo.sid hs₁_eq).symm.trans (congrArg SessionInfo.sid hs₂_eq)
    obtain ⟨_, hrk_eq⟩ := concat_inj hsid_eq
    have hikm : ikm₁ = ikm₂ := pqxdhKdf_rk_inj hrk_eq
    subst hikm
    exact ⟨rfl, (hs₁.eq_of_initiator_ikm_eq hs₂ hinit hinit).2.2⟩

/-! ## `saltDepth` Under `gamma'` Shape -/

section SaltDepthSchedule

local notation "sd" => Symbolic.Swarm.COMPOSED.CompRatchet.saltDepth

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

private theorem a2b_saltDepth_shape_hmac' (k m : DY.Bytes) :
    sd (gamma' i S g (hmac k m)).shape = sd (gamma' i S g k).shape + 1 := by
  unfold hmac
  rw [shape_kdfExtract_tr]
  exact Symbolic.Swarm.COMPOSED.CompRatchet.saltDepth_kdfExtract _ _

theorem a2b_saltDepth_shape_kdfRk_fst (rk dhOut : DY.Bytes) :
    sd (gamma' i S g (kdfRk rk dhOut).1).shape = sd (gamma' i S g rk).shape + 2 := by
  show sd (gamma' i S g (hkdfBlock1 (hmac rk dhOut) _)).shape = _
  unfold hkdfBlock1
  rw [a2b_saltDepth_shape_hmac', a2b_saltDepth_shape_hmac']

theorem a2b_saltDepth_shape_kdfRk_snd (rk dhOut : DY.Bytes) :
    sd (gamma' i S g (kdfRk rk dhOut).2).shape = sd (gamma' i S g rk).shape + 2 := by
  show sd (gamma' i S g (hkdfBlock2 (hmac rk dhOut) _)).shape = _
  unfold hkdfBlock2
  rw [a2b_saltDepth_shape_hmac', a2b_saltDepth_shape_hmac']

theorem a2b_saltDepth_shape_createChain_fst (rk pk sk : DY.Bytes) :
    sd (gamma' i S g (createChain rk pk sk).1).shape = sd (gamma' i S g rk).shape + 2 :=
  a2b_saltDepth_shape_kdfRk_fst i S g rk _

private theorem a2b_saltDepth_shape_createChain_snd' (rk pk sk : DY.Bytes) :
    sd (gamma' i S g (createChain rk pk sk).2).shape = sd (gamma' i S g rk).shape + 2 :=
  a2b_saltDepth_shape_kdfRk_snd i S g rk _

theorem a2b_saltDepth_shape_pqxdhKdf_ck_eq_rk (ikm : DY.Bytes) :
    sd (gamma' i S g (pqxdhKdf ikm).ck).shape = sd (gamma' i S g (pqxdhKdf ikm).rk).shape := by
  have h1 : sd (gamma' i S g (pqxdhKdf ikm).ck).shape = sd (gamma' i S g (hmac zeroSalt ikm)).shape + 1 :=
    a2b_saltDepth_shape_hmac' i S g (hmac zeroSalt ikm) _
  have h2 : sd (gamma' i S g (pqxdhKdf ikm).rk).shape = sd (gamma' i S g (hmac zeroSalt ikm)).shape + 1 :=
    a2b_saltDepth_shape_hmac' i S g (hmac zeroSalt ikm) _
  exact h1.trans h2.symm

theorem a2b_saltDepth_shape_compRkSteps {dh₁ rk₀ rk : DY.Bytes} {d : Nat}
    (h : CompRkSteps dh₁ d rk₀ rk) :
    sd (gamma' i S g rk).shape = sd (gamma' i S g rk₀).shape + 2 * d := by
  induction h with
  | zero => simp
  | step_one rk₀ =>
    rw [a2b_saltDepth_shape_kdfRk_fst]
  | step_succ _ ih =>
    rw [a2b_saltDepth_shape_createChain_fst, ih]
    omega

theorem a2b_saltDepth_shape_compChainRootFrom1 {dh₁ ikm ck₀ : DY.Bytes} {m : Nat}
    (h : CompChainRootFrom1 dh₁ ikm m ck₀) :
    sd (gamma' i S g ck₀).shape = sd (gamma' i S g (pqxdhKdf ikm).rk).shape + 2 * m := by
  rcases m with _ | _ | k
  · subst h
    rw [a2b_saltDepth_shape_pqxdhKdf_ck_eq_rk]
    omega
  · subst h
    rw [a2b_saltDepth_shape_kdfRk_snd]
  · obtain ⟨rk, pk, sk, hrk, rfl⟩ := h
    rw [a2b_saltDepth_shape_createChain_snd', a2b_saltDepth_shape_compRkSteps i S g hrk]
    omega

theorem compChainRootFrom1_depth_eq_of_shape_eq {dh₁ ikm ck₁ ck₂ : DY.Bytes} {m₁ m₂ : Nat}
    (h₁ : CompChainRootFrom1 dh₁ ikm m₁ ck₁)
    (h₂ : CompChainRootFrom1 dh₁ ikm m₂ ck₂)
    (hsh : (gamma' i S g ck₁).shape = (gamma' i S g ck₂).shape) :
    m₁ = m₂ := by
  have hd := congrArg (fun b => sd b) hsh
  rw [a2b_saltDepth_shape_compChainRootFrom1 i S g h₁,
      a2b_saltDepth_shape_compChainRootFrom1 i S g h₂] at hd
  omega

private theorem shape_hmac_inj' {k₁ m₁ k₂ m₂ : DY.Bytes}
    (h : (gamma' i S g (hmac k₁ m₁)).shape = (gamma' i S g (hmac k₂ m₂)).shape) :
    (gamma' i S g k₁).shape = (gamma' i S g k₂).shape ∧
    (gamma' i S g m₁).shape = (gamma' i S g m₂).shape := by
  unfold hmac at h
  rw [shape_kdfExtract_tr, shape_kdfExtract_tr] at h
  exact kdfExtract_inj h

theorem shape_kdfCk_fst_inj' {ck₁ ck₂ : DY.Bytes}
    (h : (gamma' i S g (kdfCk ck₁).1).shape = (gamma' i S g (kdfCk ck₂).1).shape) :
    (gamma' i S g ck₁).shape = (gamma' i S g ck₂).shape :=
  (shape_hmac_inj' i S g h).1

theorem shape_kdfCk_snd_inj' {ck₁ ck₂ : DY.Bytes}
    (h : (gamma' i S g (kdfCk ck₁).2).shape = (gamma' i S g (kdfCk ck₂).2).shape) :
    (gamma' i S g ck₁).shape = (gamma' i S g ck₂).shape :=
  (shape_hmac_inj' i S g h).1

theorem shape_chainKeyAt_inj' (n : Nat) : ∀ {ck₁ ck₂ : DY.Bytes},
    (gamma' i S g (chainKeyAt ck₁ n)).shape = (gamma' i S g (chainKeyAt ck₂ n)).shape →
    (gamma' i S g ck₁).shape = (gamma' i S g ck₂).shape := by
  induction n with
  | zero => intro ck₁ ck₂ h; exact h
  | succ n ih =>
    intro ck₁ ck₂ h
    exact shape_kdfCk_fst_inj' i S g (ih h)

theorem stored_dhs_eq_of_createChain_snd_shape_eq
    {tr : ExecTrace} (hInv : CompScheduleInv tr)
    {p₁ p₂ : Participant} {st₁ st₂ : TRState} {i₁ i₂ : Nat} {pk : DY.Bytes}
    (hst₁ : CompTrace.TRStateStoredAt p₁ st₁ i₁ tr)
    (hst₂ : CompTrace.TRStateStoredAt p₂ st₂ i₂ tr)
    (hsh : (gamma' i S g (createChain st₁.rk pk st₁.dhs).2).shape =
      (gamma' i S g (createChain st₂.rk pk st₂.dhs).2).shape) :
    st₁.dhs = st₂.dhs := by
  have hprk := (shape_hmac_inj' i S g hsh).1
  have hdh : (gamma' i S g (DiffieHellman.dh (DY.X25519.normalizeX25519Key pk) st₁.dhs)).shape =
      (gamma' i S g (DiffieHellman.dh (DY.X25519.normalizeX25519Key pk) st₂.dhs)).shape :=
    (shape_hmac_inj' i S g hprk).2
  obtain ⟨_, _, _, _, ⟨t₁, _, _, hdhs₁⟩⟩ := hInv.stateOK p₁ st₁ i₁ hst₁
  obtain ⟨_, _, _, _, ⟨t₂, _, _, hdhs₂⟩⟩ := hInv.stateOK p₂ st₂ i₂ hst₂
  have hdhs₁' : st₁.dhs = randTerm t₁ 32 := hdhs₁
  have hdhs₂' : st₂.dhs = randTerm t₂ 32 := hdhs₂
  rw [hdhs₁', hdhs₂'] at hdh ⊢
  rcases notRandDhPkShape_or_eq_dhPk_randTerm32 i S g (DY.X25519.normalizeX25519Key pk) with hnr | ⟨t_m, hpk⟩
  · have ht : t₁ = t₂ := (dh_shape_eq_of_notRandDhPkShape i S g hnr hdh).2
    rw [ht]
  · rw [hpk] at hdh
    have hdh_eq := (dh_eq_of_shape_eq_dh_dhPk_randTerm32 i S g hdh).2
    exact dh_left_inj hdh_eq

end SaltDepthSchedule

/-! ## Receiver-Root Pinning and Seed Equality -/

abbrev LocalRecvRoot (tr : ExecTrace) (pk R : DY.Bytes) : Prop :=
  (∃ (p : Participant) (st₀ : TRState) (i₀ : Nat), CompTrace.TRStateStoredAt p st₀ i₀ tr ∧
    R = (createChain st₀.rk pk st₀.dhs).2) ∨
  (∃ (keys : HandshakeKeys) (t : Nat) (b : Participant) (idx : Nat),
    (∃ b' a ikB ikA spk pqpk opk ek ct j,
      tr.EventLoggedAt (PQXDHEvent.BobDone b' a ikB ikA spk pqpk opk ek ct keys) j) ∧
    CompTrace.PQXDHStoredAt tr b { kind := .signedPrekey, sk := randTerm t 32 } idx ∧
    R = (createChain keys.rk pk (randTerm t 32)).2) ∨
  (∃ keys : HandshakeKeys,
    (∃ a b ikA ikB spk pqpk opk ek ct j,
      tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) j) ∧
    R = keys.ck)

private theorem consume_seed_eq_at' {c c' : RecvChain} {n : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c n = some (seed, c')) :
    seed = (kdfCk (chainKeyAt c.chainKey (n.toNat - c.index.toNat))).2 := by
  unfold consumeMessageKey at h
  split_ifs at h
  injection h with h
  injection h with h
  exact h.symm

private theorem getLocalState_some_iff_trStateStoredAt' {p : Participant} {st : TRState} {idx : Nat}
    {tr : ExecTrace} :
    ((PersistentLocalState.getLocalState p idx : Traceful TRState).run tr).1 = some st ↔
      CompTrace.TRStateStoredAt p st idx tr := by
  rw [CompTrace.getLocalState_tr_fst]
  unfold CompTrace.TRStateStoredAt
  rcases h : (tr.at? idx : Option CompTrace.TRStEntry) with _ | ⟨⟨q, st'⟩⟩
  · simp
  · simp only [Option.some.injEq, PersistentGlobalState.State.ExecEntryT.mk.injEq,
      PersistentLocalState.LocalState.mk.injEq]
    by_cases hq : q = p
    · subst hq; simp
    · simp [hq]

theorem recvRoot_isChainRoot {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability)
    {pk R : DY.Bytes} (hR : LocalRecvRoot tr pk R) :
    IsChainRoot R := by
  rcases hR with ⟨_, st₀, _, _, rfl⟩ | ⟨keys, t, _, _, _, _, rfl⟩ | ⟨keys, halice, rfl⟩
  · exact isChainRoot_createChain_snd st₀.rk pk st₀.dhs
  · exact isChainRoot_createChain_snd keys.rk pk (randTerm t 32)
  · obtain ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, j, hev⟩ := halice
    obtain ⟨ikm, rfl⟩ := (compSessionOriginInv_reachable hreach).handshakeKdf j keys
      ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, hev⟩⟩
    exact isChainRoot_pqxdhKdf_ck ikm

theorem recvRoot_of_compChainRootFrom1_succ_succ {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability)
    {dh₁ ikm pk ck₀ : DY.Bytes} {k : Nat}
    (hroot : CompChainRootFrom1 dh₁ ikm (k + 2) ck₀)
    (hR : LocalRecvRoot tr pk ck₀) :
    ∃ p₁ st₁ i₁, CompTrace.TRStateStoredAt p₁ st₁ i₁ tr ∧ ck₀ = (createChain st₁.rk pk st₁.dhs).2 := by
  have hsd : saltDepth ck₀ = 2 + 2 * (k + 2) := hroot.saltDepth_eq
  rcases hR with hst | ⟨keys, t, _, _, hbob, _, hck⟩ | ⟨keys, halice, hck⟩
  · exact hst
  · exfalso
    obtain ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, j, hev⟩ := hbob
    obtain ⟨ikm', rfl⟩ := (compSessionOriginInv_reachable hreach).handshakeKdf j keys
      ⟨a, b, ikA, ikB, spk, pqpk, opk, .inr ⟨ek, ct, hev⟩⟩
    rw [hck, saltDepth_createChain_snd, saltDepth_pqxdhKdf_rk] at hsd
    omega
  · exfalso
    obtain ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, j, hev⟩ := halice
    obtain ⟨ikm', rfl⟩ := (compSessionOriginInv_reachable hreach).handshakeKdf j keys
      ⟨a, b, ikA, ikB, spk, pqpk, opk, .inl ⟨ek, ct, hev⟩⟩
    rw [hck, saltDepth_pqxdhKdf_ck] at hsd
    omega

theorem a2b_sameOrigin_seed_eq_core
    (interpretation : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability)
    (hlink : ∀ {p : Participant} {st : TRState} {i₀ : Nat}, CompTrace.TRStateStoredAt p st i₀ tr →
      ∀ c ∈ st.recv, ∃ R j, c.chainKey = chainKeyAt R j ∧ LocalRecvRoot tr c.ratchetKey R)
    (hrk_uniq : ∀ {p₁ p₂ : Participant} {st₁ st₂ : TRState} {i₁ i₂ : Nat},
      CompTrace.TRStateStoredAt p₁ st₁ i₁ tr → CompTrace.TRStateStoredAt p₂ st₂ i₂ tr →
      st₁.dhs = st₂.dhs → st₁.rk = st₂.rk)
    {p p₀ : Participant} {stIdx k₀ skIdx rIdx_s srcIdx : Nat}
    {st st₀ : TRState} {msg : TRSignalMsg} {c c' c₀ : RecvChain}
    {seed_c seed_s : DY.Bytes}
    (hst : ((PersistentLocalState.getLocalState p stIdx : Traceful TRState).run tr).1 = some st)
    (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed_c, c'))
    (hsk : (tr.at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx⟩)
    (hshape : (gamma' interpretation S g seed_c).shape = (gamma' interpretation S g seed_s).shape)
    (hst₀ : ((PersistentLocalState.getLocalState p₀ k₀ : Traceful TRState).run tr).1 = some st₀)
    (hc₀_rk : c₀.ratchetKey = msg.ratchetKey)
    (hc₀_seed : (consumeMessageKey c₀ msg.counter).map Prod.fst = some seed_s)
    (hc₀_origin : c₀ ∈ st₀.recv ∨
      c₀ = { ratchetKey := msg.ratchetKey, chainKey := (createChain st₀.rk msg.ratchetKey st₀.dhs).2,
             index := 0, rIdx := st₀.rIdx + 2 } ∨
      (rIdx_s = 2 ∧ c₀.index = 0)) :
    seed_s = seed_c ∧ rIdx_s = c.rIdx := by
  have hInv := compScheduleInv_reachable hreach
  have hst_at : CompTrace.TRStateStoredAt p st stIdx tr :=
    getLocalState_some_iff_trStateStoredAt'.mp hst
  have hfind' : st.recv.find? (·.ratchetKey == msg.ratchetKey) = some c := hfind
  have hc_mem : c ∈ st.recv := List.mem_of_find?_eq_some hfind'
  have hc_rk : c.ratchetKey = msg.ratchetKey := by simpa using List.find?_some hfind'
  obtain ⟨_, _, _, ⟨doneIdx_c, ikm_c, dh₁_c, hs_c, _, _, hrecv_c⟩, _⟩ :=
    hInv.stateOK p st stIdx hst_at
  have hc_sched := hrecv_c c hc_mem
  have hc_pos : 1 ≤ c.rIdx := hc_sched.1
  obtain ⟨_, _, _, _, _, ck₀_c, hroot_c, hck_c, hseed_c, _⟩ :=
    consumeMessageKey_compSchedule hc_sched hcons
  obtain ⟨hs_pos, _, doneIdx_s, ikm_s, dh₁_s, ck₀_s, hs_s, hroot_s, hseed_s⟩ :=
    hInv.eventOK (TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx)
      ⟨skIdx, by rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]⟩
  obtain ⟨rfl, rfl⟩ := compSessionAt_same_sinfo_eq hs_c hs_s
  have hsh_ck₀ :
      (gamma' interpretation S g ck₀_c).shape = (gamma' interpretation S g ck₀_s).shape :=
    shape_chainKeyAt_inj' interpretation S g msg.counter.toNat
      (shape_kdfCk_snd_inj' interpretation S g (by rwa [← hseed_c, ← hseed_s]))
  have hm_eq : c.rIdx - 1 = rIdx_s - 1 :=
    compChainRootFrom1_depth_eq_of_shape_eq interpretation S g hroot_c hroot_s hsh_ck₀
  have hrIdx_eq : rIdx_s = c.rIdx := by omega
  suffices hck₀_eq : ck₀_s = ck₀_c by
    refine ⟨?_, hrIdx_eq⟩
    rw [hseed_s, hseed_c, hck₀_eq]
  rcases hm : c.rIdx - 1 with _ | _ | k
  · rw [hm] at hroot_c hm_eq
    rw [← hm_eq] at hroot_s
    exact hroot_s.trans hroot_c.symm
  · rw [hm] at hroot_c hm_eq
    rw [← hm_eq] at hroot_s
    exact hroot_s.trans hroot_c.symm
  · have hm_s : rIdx_s - 1 = k + 2 := hm_eq.symm.trans hm
    rw [hm] at hroot_c
    rw [hm_s] at hroot_s
    obtain ⟨R_c, j_c, hck_Rc, hR_c⟩ := hlink hst_at c hc_mem
    rw [hc_rk] at hR_c
    have hck₀_c_eq : ck₀_c = R_c :=
      (chainKeyAt_root_inj hroot_c.isChainRoot (recvRoot_isChainRoot hreach hR_c)
        (hck_c.symm.trans hck_Rc)).1
    subst hck₀_c_eq
    obtain ⟨p₁, st₁, i₁, hst₁, hck₀_c⟩ :=
      recvRoot_of_compChainRootFrom1_succ_succ hreach hroot_c hR_c
    have hst₀_at : CompTrace.TRStateStoredAt p₀ st₀ k₀ tr :=
      getLocalState_some_iff_trStateStoredAt'.mp hst₀
    have hR_s_link : ∃ R_s j_s, c₀.chainKey = chainKeyAt R_s j_s ∧ LocalRecvRoot tr msg.ratchetKey R_s := by
      rcases hc₀_origin with hc₀_mem | hc₀_fresh | ⟨hr2, _⟩
      · obtain ⟨R_s, j_s, hck_Rs, hR_s⟩ := hlink hst₀_at c₀ hc₀_mem
        rw [hc₀_rk] at hR_s
        exact ⟨R_s, j_s, hck_Rs, hR_s⟩
      · refine ⟨(createChain st₀.rk msg.ratchetKey st₀.dhs).2, 0, ?_, .inl ⟨p₀, st₀, k₀, hst₀_at, rfl⟩⟩
        rw [hc₀_fresh]
        rfl
      · omega
    obtain ⟨R_s, j_s, hck_Rs, hR_s⟩ := hR_s_link
    rcases hcons₀ : consumeMessageKey c₀ msg.counter with _ | ⟨seed₀, c₀'⟩
    · rw [hcons₀] at hc₀_seed
      cases hc₀_seed
    · rw [hcons₀] at hc₀_seed
      simp only [Option.map_some, Option.some.injEq] at hc₀_seed
      subst hc₀_seed
      have hseed_s_c₀ := consume_seed_eq_at' hcons₀
      have hchain_s :
          chainKeyAt ck₀_s msg.counter.toNat =
          chainKeyAt R_s (j_s + (msg.counter.toNat - c₀.index.toNat)) := by
        apply kdfCk_snd_inj
        rw [← hseed_s, hseed_s_c₀, hck_Rs, ← CompTermAlgebra.chainKeyAt_add]
      have hck₀_s_eq : ck₀_s = R_s :=
        (chainKeyAt_root_inj hroot_s.isChainRoot (recvRoot_isChainRoot hreach hR_s) hchain_s).1
      subst hck₀_s_eq
      obtain ⟨p₂, st₂, i₂, hst₂, hck₀_s⟩ :=
        recvRoot_of_compChainRootFrom1_succ_succ hreach hroot_s hR_s
      rw [hck₀_c, hck₀_s] at hsh_ck₀
      have hdhs_eq : st₁.dhs = st₂.dhs :=
        stored_dhs_eq_of_createChain_snd_shape_eq interpretation S g hInv hst₁ hst₂ hsh_ck₀
      have hrk_eq : st₁.rk = st₂.rk := hrk_uniq hst₁ hst₂ hdhs_eq
      rw [hck₀_s, hck₀_c, hrk_eq, hdhs_eq]

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure

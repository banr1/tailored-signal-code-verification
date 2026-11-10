/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.SpqrRkForgedMac
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.BaseAttackerKnowledge
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
public import Symbolic.Proofs.Swarm.CREF.TR.G1.KdfProvNon01Defs
import ProofLib.Lemmas
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompClosed
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPresPQXDH
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.KdfProvNon01

/-!
# Root and Receiving-Chain Spine Invariant

Proves the state-side root and receiving-chain spine invariant `StRkSpine` for all stored `TRState`s
on any reachable trace (`stRkSpine_of_stored`), together with the receiving-chain step lemmas
`acceptedChain_honest_or_prkAK` and `acceptedBaseChain_ckAK`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.TripleRatchet (RecvChain SessionInfo KeyDir KeyComponent createChain
  consumeMessageKey computeMac findRecvChain setRecvChain recvChainFor chainKeyAt hmac hkdfBlock2
  kdfCk litByte)
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles PreKeyMsgHandles
  pqxdhKdf pqxdhIkm opkUsedB registerIdentity registerCorruptIdentity genSignedPrekey genPQPrekey
  genOneTimePrekey compromiseIK compromiseSPK compromisePQSPK compromiseOPK invertDH invertKEM)
open Symbolic.Swarm.COMPOSED.CompTrace Symbolic.Swarm.COMPOSED.CompRatchet
open Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompPresPQXDH
open Symbolic.Swarm.COMPOSED.CompInv (SpqrInv spqrInv_of_reachable EvE)

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Spine Definitions -/

/-- `root` is the base of the sending chain (`st'.cks = chainKeyAt root j'`) of a stored `TRState`
on `T`, paired with `st'.rk = (createChain rk1 k st'.dhs).1` and `root = (createChain rk1 k st'.dhs).2`. -/
def HonestSendRoot (T : ExecTrace) (root : DY.Bytes) : Prop :=
  ∃ (p' : Participant) (st' : TRState) (i' j' : Nat),
    TRStateStoredAt p' st' i' T ∧ st'.cks = chainKeyAt root j' ∧
    ∃ (rk1 k : DY.Bytes), root = (createChain rk1 k st'.dhs).2 ∧ st'.rk = (createChain rk1 k st'.dhs).1

/-- Pairing invariant between a receiving chain's parent root key `rk'` and DH secret timestamp `t`:
either `rk'` is from `st0` in `dhRatchetStep` (matching `StRkDhsInv`), or `rk'` is Bob's PQXDH
handshake root key and `randTerm t 32` is Bob's signed prekey secret from `bobStart`. -/
def RkDhsPair (T : ExecTrace) (rk' : DY.Bytes) (t : Nat) : Prop :=
  (∃ t_rk, rk' = randTerm t_rk 32) ∨
  (∃ rk_p pk_p, rk' = (createChain rk_p pk_p (randTerm t 32)).1) ∨
  ((∃ (dh1 dh2 dh3 : DY.Bytes) (dh4 : Option DY.Bytes) (ss : DY.Bytes),
      rk' = (DY.Libsignal.PQXDH.pqxdhKdf
        (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 ss)).rk) ∧
   ∃ (b : Participant) (idx : Nat),
     CompTrace.PQXDHStoredAt T b { kind := .signedPrekey, sk := randTerm t 32 } idx)

/-- A ratchet receiving chain (`createChain rk' c.ratchetKey (randTerm t 32)`): its root key `rk'`
lies in `RkTree T` with `RkDhsPair T rk' t`, its `chainKey` is `chainKeyAt root j`, and either
`root` is an `HonestSendRoot` or `prk = hmac rk' (dh (normalizeX25519Key c.ratchetKey) (randTerm t 32))`
is `AttackerKnows T`. -/
def CreateSpine (T : ExecTrace) (c : RecvChain) : Prop :=
  ∃ (rk' : DY.Bytes) (t j : Nat), RkTree T rk' ∧ RkDhsPair T rk' t ∧
    c.chainKey = chainKeyAt (createChain rk' c.ratchetKey (randTerm t 32)).2 j ∧
    (HonestSendRoot T (createChain rk' c.ratchetKey (randTerm t 32)).2 ∨
     (hmac rk' (DiffieHellman.dh (X25519.normalizeX25519Key c.ratchetKey) (randTerm t 32))).AttackerKnows T)

/-- Alice's initial PQXDH receiving chain `(pqxdhKdf ikm).ck` from `aliceStart`: either unconsumed
(`j = 0`) or its root chain key `(pqxdhKdf ikm).ck` is `AttackerKnows T`. -/
def BaseSpine (T : ExecTrace) (c : RecvChain) : Prop :=
  ∃ (dh1 dh2 dh3 : DY.Bytes) (dh4 : Option DY.Bytes) (pk_kem r_kem : DY.Bytes) (j : Nat),
    c.chainKey = chainKeyAt (DY.Libsignal.PQXDH.pqxdhKdf
      (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 (PQKem.kemEncap pk_kem r_kem).2)).ck j ∧
    (j = 0 ∨ (DY.Libsignal.PQXDH.pqxdhKdf
      (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 (PQKem.kemEncap pk_kem r_kem).2)).ck.AttackerKnows T)

/-- Receiving-chain spine invariant on `T`: either a `createChain` ratchet receiving chain
(`CreateSpine T c`) or a PQXDH base receiving chain (`BaseSpine T c`). -/
def RecvChainSpine (T : ExecTrace) (c : RecvChain) : Prop :=
  CreateSpine T c ∨ BaseSpine T c

/-- Full state-side root and receiving-chain spine invariant for a stored `TRState`. -/
def StRkSpine (T : ExecTrace) (st : TRState) : Prop :=
  StRkDhsInv T T.length st ∧ ∀ c ∈ st.recv, RecvChainSpine T c

/-- Every stored state's sending chain `st.cks` is `chainKeyAt (createChain rk1 k st.dhs).2 j`
paired with `st.rk = (createChain rk1 k st.dhs).1`. -/
def StCksIsCreateChain (st : TRState) : Prop :=
  ∃ (rk1 k : DY.Bytes) (j : Nat),
    st.cks = chainKeyAt (createChain rk1 k st.dhs).2 j ∧
    st.rk = (createChain rk1 k st.dhs).1

/-- Skipped-key seed spine invariant on `T`: every logged `SkippedKeyStored` seed comes from a
chain `c` that either satisfies `CreateSpine T c` or is a `BaseSpine` chain whose root `ck` is
already `AttackerKnows T` (since `logSkippedKeys` runs only after `verifyMacAndDecrypt`). -/
def ActiveRecvChainSpine (T : ExecTrace) (c : RecvChain) : Prop :=
  CreateSpine T c ∨
  ∃ (dh1 dh2 dh3 : DY.Bytes) (dh4 : Option DY.Bytes) (pk_kem r_kem : DY.Bytes) (j : Nat),
    c.chainKey = chainKeyAt (DY.Libsignal.PQXDH.pqxdhKdf
      (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 (PQKem.kemEncap pk_kem r_kem).2)).ck j ∧
    (DY.Libsignal.PQXDH.pqxdhKdf
      (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 (PQKem.kemEncap pk_kem r_kem).2)).ck.AttackerKnows T

def SkippedSeedSpine (T : ExecTrace) (seed : DY.Bytes) : Prop :=
  ∃ c : RecvChain, ActiveRecvChainSpine T c ∧ seed = (kdfCk c.chainKey).2

/-! ## `chainKeyAt` Algebraic and Injectivity Helpers -/

theorem chainKeyAt_add (ck : DY.Bytes) : ∀ (m n : Nat),
    chainKeyAt (chainKeyAt ck m) n = chainKeyAt ck (m + n)
  | 0, n => by simp [chainKeyAt]
  | m + 1, n => by
    simp only [chainKeyAt, Nat.succ_add]
    exact chainKeyAt_add (kdfCk ck).1 m n

theorem chainKeyAt_succ_eq_kdfCk_fst (ck : DY.Bytes) : ∀ (n : Nat),
    chainKeyAt ck (n + 1) = (kdfCk (chainKeyAt ck n)).1
  | 0 => rfl
  | n + 1 => chainKeyAt_succ_eq_kdfCk_fst (kdfCk ck).1 n

theorem activeRecvChainSpine_imp_recvChainSpine {T : ExecTrace} {c : RecvChain}
    (hc : ActiveRecvChainSpine T c) : RecvChainSpine T c := by
  rcases hc with hcreate | ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j, hck, hak⟩
  · exact .inl hcreate
  · exact .inr ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j, hck, .inr hak⟩

theorem activeRecvChainSpine_advance {T : ExecTrace} {c : RecvChain}
    (hc : ActiveRecvChainSpine T c) (d : Nat) (idx' : UInt32) :
    ActiveRecvChainSpine T { c with chainKey := chainKeyAt c.chainKey d, index := idx' } := by
  rcases hc with ⟨rk', t, j, hrk, hpair, hck, hdisj⟩ | ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j, hck, hak⟩
  · refine .inl ⟨rk', t, j + d, hrk, hpair, ?_, hdisj⟩
    dsimp only
    rw [hck, chainKeyAt_add]
  · refine .inr ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j + d, ?_, hak⟩
    dsimp only
    rw [hck, chainKeyAt_add]

theorem activeRecvChainSpine_kdfCk_fst {T : ExecTrace} {c : RecvChain}
    (hc : ActiveRecvChainSpine T c) (idx' : UInt32) :
    ActiveRecvChainSpine T { c with chainKey := (kdfCk c.chainKey).1, index := idx' } :=
  activeRecvChainSpine_advance hc 1 idx'

theorem chainKeyAt_concat_base_inj {s₁ a₁ b₁ s₂ a₂ b₂ : DY.Bytes} :
    ∀ (j₁ j₂ : Nat),
      chainKeyAt (KdfExtract.kdfExtract s₁ (Concat.concat a₁ b₁)) j₁ =
      chainKeyAt (KdfExtract.kdfExtract s₂ (Concat.concat a₂ b₂)) j₂ →
      KdfExtract.kdfExtract s₁ (Concat.concat a₁ b₁) =
        KdfExtract.kdfExtract s₂ (Concat.concat a₂ b₂) ∧ j₁ = j₂
  | 0, 0, h => ⟨h, rfl⟩
  | 0, j₂ + 1, h => by
    rw [chainKeyAt, chainKeyAt_succ_eq_kdfCk_fst] at h
    have hi := (kdfExtract_inj_rk h).2
    exact False.elim (concat_ne_literal_rk a₁ b₁ _ hi)
  | j₁ + 1, 0, h => by
    rw [chainKeyAt, chainKeyAt_succ_eq_kdfCk_fst] at h
    have hi := (kdfExtract_inj_rk h).2
    exact False.elim (concat_ne_literal_rk a₂ b₂ _ hi.symm)
  | j₁ + 1, j₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst, chainKeyAt_succ_eq_kdfCk_fst] at h
    have hprev := (kdfExtract_inj_rk h).1
    obtain ⟨hbase, hj⟩ := chainKeyAt_concat_base_inj j₁ j₂ hprev
    exact ⟨hbase, congrArg Nat.succ hj⟩

theorem createChain_snd_ne_pqxdhKdf_ck (rk pk sk ikm : DY.Bytes) (j₁ j₂ : Nat) :
    chainKeyAt (createChain rk pk sk).2 j₁ ≠
      chainKeyAt (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck j₂ := by
  intro h
  have hbase := (chainKeyAt_concat_base_inj j₁ j₂ h).1
  have hi := (kdfExtract_inj_rk hbase).2
  have hlbl := (concat_inj_rk (concat_inj_rk hi).2).1
  exact pqxdhLabel_ne_whisperRatchet_rk hlbl.symm

unseal DY.Bytes in
private theorem kdfExtract_ne_randTerm_spine (s i : DY.Bytes) (t n : Nat) :
    KdfExtract.kdfExtract s i ≠ randTerm t n := by
  intro h
  have h1 : DY.Bytes.view? (KdfExtract.kdfExtract s i) DY.Random.SubF = none := by
    erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _]
  have h2 : DY.Bytes.view? (randTerm t n) DY.Random.SubF = some { timestamp := t, size := n } :=
    DY.BytesView.view_pack _
  rw [h, h2] at h1
  cases h1

theorem createChain_snd_ne_st_rk {T : ExecTrace} {bound : Nat} {st : TRState}
    (hst : StRkDhsInv T bound st) (rk pk sk : DY.Bytes) (m : Nat) :
    chainKeyAt (createChain rk pk sk).2 m ≠ st.rk := by
  intro h
  rcases hst with ⟨_, t_dhs, _, _, ⟨t_rk, hrk_eq⟩ | ⟨rk_p, pk_p, hrk_eq⟩⟩
  · rw [hrk_eq] at h
    cases m with
    | zero => exact kdfExtract_ne_randTerm_spine _ _ _ _ h
    | succ m' =>
      rw [chainKeyAt_succ_eq_kdfCk_fst] at h
      exact kdfExtract_ne_randTerm_spine _ _ _ _ h
  · rw [hrk_eq] at h
    cases m with
    | zero =>
      have hi := (kdfExtract_inj_rk h).2
      have h2 := (concat_inj_rk hi).2
      exact concat_ne_literal_rk _ _ _ h2
    | succ m' =>
      rw [chainKeyAt_succ_eq_kdfCk_fst] at h
      have hi := (kdfExtract_inj_rk h).2
      exact concat_ne_literal_rk _ _ _ hi.symm

theorem pqxdhKdf_ck_ne_st_rk {T : ExecTrace} {bound : Nat} {st : TRState}
    (hst : StRkDhsInv T bound st) (ikm : DY.Bytes) (m : Nat) :
    chainKeyAt (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck m ≠ st.rk := by
  intro h
  rcases hst with ⟨_, t_dhs, _, _, ⟨t_rk, hrk_eq⟩ | ⟨rk_p, pk_p, hrk_eq⟩⟩
  · rw [hrk_eq] at h
    cases m with
    | zero => exact kdfExtract_ne_randTerm_spine _ _ _ _ h
    | succ m' =>
      rw [chainKeyAt_succ_eq_kdfCk_fst] at h
      exact kdfExtract_ne_randTerm_spine _ _ _ _ h
  · rw [hrk_eq] at h
    cases m with
    | zero =>
      have hi := (kdfExtract_inj_rk h).2
      have h2 := (concat_inj_rk hi).2
      exact concat_ne_literal_rk _ _ _ h2
    | succ m' =>
      rw [chainKeyAt_succ_eq_kdfCk_fst] at h
      have hi := (kdfExtract_inj_rk h).2
      exact concat_ne_literal_rk _ _ _ hi.symm

theorem createChain_snd_chainKeyAt_eq_imp_prk_eq {rk₁ pk₁ sk₁ rk₂ pk₂ sk₂ : DY.Bytes}
    {j₁ j₂ : Nat}
    (h : chainKeyAt (createChain rk₁ pk₁ sk₁).2 j₁ = chainKeyAt (createChain rk₂ pk₂ sk₂).2 j₂) :
    (createChain rk₁ pk₁ sk₁).2 = (createChain rk₂ pk₂ sk₂).2 ∧
    hmac rk₁ (DiffieHellman.dh (X25519.normalizeX25519Key pk₁) sk₁) =
      hmac rk₂ (DiffieHellman.dh (X25519.normalizeX25519Key pk₂) sk₂) := by
  have hbase := (chainKeyAt_concat_base_inj j₁ j₂ h).1
  exact ⟨hbase, (kdfExtract_inj_rk hbase).1⟩

/-! ## Trace Invariant `JRkSpine` and Step Lemmas -/

/-- State-side invariant tracked by `JRkSpine`: `st.cks` is a `createChain` sending chain and
every `c ∈ st.recv` satisfies `RecvChainSpine T c`. -/
def StSpineInv (T : ExecTrace) (st : TRState) : Prop :=
  StCksIsCreateChain st ∧ ∀ c ∈ st.recv, RecvChainSpine T c

/-- Trace invariant for `RkSpine`: every stored state satisfies `StSpineInv T st` and every
logged `SkippedKeyStored` event satisfies `SkippedSeedSpine T seed`. -/
def JRkSpine (T tr : ExecTrace) : Prop :=
  (∀ p st i, TRStateStoredAt p st i tr → StSpineInv T st) ∧
  (∀ i s pk n seed rIdx src,
    tr.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i →
    SkippedSeedSpine T seed)

theorem JRkSpine_nil (T : ExecTrace) : JRkSpine T Trace.nil :=
  ⟨fun _ _ _ h => by simp [TRStateStoredAt, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h,
   fun _ _ _ _ _ _ _ h => by simp [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h⟩

theorem JRkSpine_append_other {T tr : ExecTrace} {E : Type} [ExecTraceTypes.Has E] {e : E}
    (h : JRkSpine T tr)
    (hdr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TREntry) = none := by rfl)
    (hst : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option CompTrace.TRStEntry) = none := by rfl) :
    JRkSpine T (tr.append e) :=
  ⟨fun p st i hs => h.1 p st i (CompTrace.trStateStoredAt_append_other hst hs),
   fun i s pk n seed rIdx src hev => h.2 i s pk n seed rIdx src (CompTrace.eventLoggedAt_append_other hdr hev)⟩

theorem JRkSpine_append_ev {T tr : ExecTrace} (ev : TREvent)
    (hev : ∀ s pk n seed rIdx src, ev = .SkippedKeyStored s pk n seed rIdx src → SkippedSeedSpine T seed)
    (h : JRkSpine T tr) : JRkSpine T (tr.append (TREvE ev)) := by
  refine ⟨fun p st i hs => h.1 p st i (CompTrace.trStateStoredAt_append_other rfl hs),
    fun i s pk n seed rIdx src hevl => ?_⟩
  rcases CompTrace.eventLoggedAt_append_same hevl with ⟨_, hevl⟩ | ⟨_, hp⟩
  · exact h.2 i s pk n seed rIdx src hevl
  · exact hev s pk n seed rIdx src hp

theorem JRkSpine_append_st {T tr : ExecTrace} (p : Participant) {st : TRState}
    (hst : StSpineInv T st) (h : JRkSpine T tr) : JRkSpine T (tr.append (TRStE p st)) := by
  refine ⟨fun p' st' i hs => ?_,
    fun i s pk n seed rIdx src hevl => h.2 i s pk n seed rIdx src (CompTrace.eventLoggedAt_append_other rfl hevl)⟩
  rcases CompTrace.trStateStoredAt_append_same hs with ⟨_, hs⟩ | ⟨_, rfl, rfl⟩
  · exact h.1 p' st' i hs
  · exact hst

theorem messageDecrypt_honestCks_or_seed_attackerKnows {tr : ExecTrace} (hreach : ReachableTrace tr)
    {t pqSalt seed ck peerIk myIk : DY.Bytes} {msg : TRSignalMsg}
    (ht_ak : t.AttackerKnows tr) (hparse : parseTrSignalMsg t = some msg)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey peerIk myIk msg.wire)
    (hseed : seed = KdfExtract.kdfExtract ck (litByte 0x01)) :
    (∃ (me : Participant) (st_s : TRState) (stH : Nat),
      TRStateStoredAt me st_s stH tr ∧ st_s.cks = ck) ∨
    seed.AttackerKnows tr := by
  obtain ⟨x, hsplit, _, hpack, _, _, _⟩ := parseTrSignalMsg_unpack hparse
  have hsp_ak := Concat.attacker_knows_split t (t.length - Trunc.trunc8Length) tr ht_ak
  rw [hsplit] at hsp_ak
  have hmac_ak : (computeMac (trMsgKeys pqSalt seed).macKey peerIk myIk msg.wire).AttackerKnows tr :=
    hmac_eq ▸ hsp_ak.2
  let inp₀ := hmac (trMsgKeys pqSalt seed).macKey (Concat.concat peerIk (Concat.concat myIk msg.wire))
  rcases (truncSafeStrong_trunc8_iff inp₀).mp (truncSafeStrong_of_attackerKnows_reachable hreach hmac_ak) with
    hinp_ak | ⟨pqSalt', seed', myIk', peerIk', a, ns, pn, m, pqMsg, t_s, stH, me, st_s,
      hinp_eq, _, _, _, hst_s, _, _, hcks_seed⟩
  · right
    rcases messageDecrypt_dhPk_or_seed_attackerKnows hreach ht_ak hparse hmac_eq hseed with ⟨_, _⟩ | hseed_ak
    · rcases (macKdfSafeTR_kdfExtract_iff _ _).mp (macKdfSafeTR_of_attackerKnows_reachable hreach hinp_ak) with
        ⟨hmackey_ak, _⟩ | ⟨h01, _⟩ | h02 | hwr1 | ⟨b1, hwr2⟩
      · have hmackey_s := macKdfSafeTR_of_attackerKnows_reachable hreach hmackey_ak
        dsimp [trMsgKeys, hkdfBlock2, hmac] at hmackey_s
        rcases (macKdfSafeTR_kdfExtract_iff _ _).mp hmackey_s with
          ⟨hprk_ak, _⟩ | ⟨h01, _⟩ | h02 | hwr1 | ⟨b1, hwr2⟩
        · rcases (macKdfSafeTR_kdfExtract_iff _ _).mp (macKdfSafeTR_of_attackerKnows_reachable hreach hprk_ak) with
            ⟨_, hseed_ak⟩ | ⟨h01, _⟩ | h02 | hwr1 | ⟨b1, hwr2⟩
          · exact hseed_ak
          · rw [hseed] at h01; exact False.elim (kdfExtract_ne_literal_rk _ _ _ h01)
          · rw [hseed] at h02; exact False.elim (kdfExtract_ne_literal_rk _ _ _ h02)
          · rw [hseed] at hwr1; exact False.elim (kdfExtract_ne_concat_rk _ _ _ _ hwr1)
          · rw [hseed] at hwr2; exact False.elim hwr2.ne_kdfExtract
        · exact False.elim (concat_ne_literal_rk _ _ _ h01)
        · exact False.elim (concat_ne_literal_rk _ _ _ h02)
        · exact False.elim (concat_ne_literal_rk _ _ _ (concat_inj_rk hwr1).2)
        · exact False.elim hwr2.ne_whisperMessageKeys
      · exact False.elim (concat_ne_literal_rk _ _ _ h01)
      · exact False.elim (concat_ne_literal_rk _ _ _ h02)
      · exact False.elim (concat_ne_literal_rk _ _ _ (concat_inj_rk hwr1).2)
      · rcases hwr2 with hwr2 | hwr2 | hwr2 <;>
          (have hwire_lit := (concat_inj_rk (concat_inj_rk hwr2).2).2
           rw [hpack] at hwire_lit
           exact False.elim (trWireMsg_pack_ne_literal_rk x _ hwire_lit))
    · exact hseed_ak
  · left
    have hmackey_eq := (kdfExtract_inj_rk hinp_eq).1
    have hprk_eq := (kdfExtract_inj_rk hmackey_eq).1
    have hseed_eq : seed = seed' := (kdfExtract_inj_rk hprk_eq).2
    have hcks_eq : KdfExtract.kdfExtract st_s.cks (litByte 0x01) = KdfExtract.kdfExtract ck (litByte 0x01) :=
      hcks_seed.trans (hseed_eq.symm.trans hseed)
    exact ⟨me, st_s, stH, hst_s, (kdfExtract_inj_rk hcks_eq).1⟩

theorem kdfProv_litByte01_of_reachable {T : ExecTrace} (hT : ReachableTrace T) {s : DY.Bytes}
    (hk : (KdfExtract.kdfExtract s (litByte 0x01)).AttackerKnows T) :
    s.AttackerKnows T ∨
    ∃ j ses pk n rIdx src,
      T.EventLoggedAt (TREvent.SkippedKeyStored ses pk n (KdfExtract.kdfExtract s (litByte 0x01)) rIdx src) j := by
  rcases kdfInputValidProv_of_attackerKnows_reachable hT hk with
    ⟨hs, _⟩ | ⟨_, hskip⟩ | ⟨hi, _⟩ | ⟨hi, _⟩ | ⟨_, hi, _⟩ | ⟨_, hi, _⟩ | ⟨_, hi⟩
  · exact .inl hs
  · exact .inr hskip
  · exact absurd (Symbolic.Swarm.COMPOSED.CompTermAlgebra.litByte_inj hi) (by decide)
  · exact absurd hi (Symbolic.Swarm.COMPOSED.CompRatchet.litByte_ne_concat _ _ _)
  · exact absurd hi (Symbolic.Swarm.COMPOSED.CompRatchet.litByte_ne_concat _ _ _)
  · exact absurd hi (Symbolic.Swarm.COMPOSED.CompRatchet.litByte_ne_concat _ _ _)
  · exact absurd hi (Symbolic.Swarm.COMPOSED.CompRatchet.litByte_ne_concat _ _ _)

theorem honestSendRoot_of_stored_cks_eq {T tr : ExecTrace} (hle : tr ≤ T) (hJ : JRkSpine T tr)
    {me : Participant} {st₁ : TRState} {idx₁ : Nat} (hst₁ : TRStateStoredAt me st₁ idx₁ tr)
    {rk' pk sk : DY.Bytes} {m : Nat}
    (hcks : st₁.cks = chainKeyAt (createChain rk' pk sk).2 m) :
    HonestSendRoot T (createChain rk' pk sk).2 := by
  obtain ⟨rk1, k_pk, j_s, hcks_create, hrk_create⟩ := (hJ.1 me st₁ idx₁ hst₁).1
  have hroot_eq : (createChain rk' pk sk).2 = (createChain rk1 k_pk st₁.dhs).2 :=
    (chainKeyAt_concat_base_inj m j_s (hcks.symm.trans hcks_create)).1
  exact ⟨me, st₁, idx₁, m, trStateStoredAt_mono hle hst₁, hcks, rk1, k_pk, hroot_eq, hrk_create⟩

theorem honestKdfOut_pqxdhKdf_ck_succ_imp_ak {T tr : ExecTrace}
    (hreach : ReachableTrace tr) (hle : tr ≤ T) (hJ : JRkSpine T tr)
    {ikm : DY.Bytes} {m : Nat}
    (hout : HonestKdfOut tr (chainKeyAt (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck (m + 1))) :
    (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck.AttackerKnows T := by
  obtain ⟨me, st₁, idx₁, hst₁, hrk | hcks | ⟨c₁, hc₁, hck₁⟩⟩ := hout
  · have hst₁_dhs : StRkDhsInv T tr.length st₁ := ((JRk_reachable hreach hle).2.1 me st₁ idx₁ hst₁).1
    exact False.elim (pqxdhKdf_ck_ne_st_rk hst₁_dhs ikm (m + 1) hrk)
  · obtain ⟨rk_s, pk_s, j_s, hcks_eq, _⟩ := (hJ.1 me st₁ idx₁ hst₁).1
    exact False.elim (createChain_snd_ne_pqxdhKdf_ck rk_s pk_s st₁.dhs ikm j_s (m + 1) (hcks.trans hcks_eq).symm)
  · rcases (hJ.1 me st₁ idx₁ hst₁).2 c₁ hc₁ with
      ⟨rk₁, t₁, j₁, _, _, hc₁_eq, _⟩ | ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j₁, hc₁_eq, hj₁_or_ak⟩
    · exact False.elim (createChain_snd_ne_pqxdhKdf_ck rk₁ c₁.ratchetKey (randTerm t₁ 32) ikm j₁ (m + 1)
        (hck₁.trans hc₁_eq).symm)
    · obtain ⟨hbase, hj_eq⟩ := chainKeyAt_concat_base_inj (m + 1) j₁ (hck₁.trans hc₁_eq)
      rcases hj₁_or_ak with rfl | hak
      · exact False.elim (Nat.succ_ne_zero m hj_eq)
      · have hbase' : (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck =
            (DY.Libsignal.PQXDH.pqxdhKdf
              (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 (PQKem.kemEncap pk_kem r_kem).2)).ck := hbase
        rw [hbase']; exact hak

theorem chainKeyAt_pqxdhKdf_ck_ak_imp_ak {T tr : ExecTrace}
    (hreach : ReachableTrace tr) (hle : tr ≤ T) (hJ : JRkSpine T tr)
    {ikm : DY.Bytes} :
    ∀ (k : Nat), (chainKeyAt (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck k).AttackerKnows tr →
      (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck.AttackerKnows T
  | 0, hak => DY.Bytes.AttackerKnows_le _ tr T hle hak
  | m + 1, hak => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at hak
    rcases kdfProv_litByte02_of_reachable hreach hak with hprev | hout
    · exact chainKeyAt_pqxdhKdf_ck_ak_imp_ak hreach hle hJ m hprev
    · have hout' : HonestKdfOut tr (chainKeyAt (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck (m + 1)) := by
        rw [chainKeyAt_succ_eq_kdfCk_fst]; exact hout
      exact honestKdfOut_pqxdhKdf_ck_succ_imp_ak hreach hle hJ hout'

/-- Step lemma for a PQXDH base receiving chain: when `verifyMacAndDecrypt` succeeds on a seed
derived from `(pqxdhKdf ikm).ck`, the root chain key `(pqxdhKdf ikm).ck` is `AttackerKnows T`. -/
theorem acceptedBaseChain_ckAK {T tr : ExecTrace}
    (hreach : ReachableTrace tr) (hle : tr ≤ T) (hJ : JRkSpine T tr)
    {t pqSalt seed peerIk myIk ikm : DY.Bytes} {msg : TRSignalMsg} {k : Nat}
    (ht_ak : t.AttackerKnows tr) (hparse : parseTrSignalMsg t = some msg)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey peerIk myIk msg.wire)
    (hseed : seed = KdfExtract.kdfExtract (chainKeyAt (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck k) (litByte 0x01)) :
    (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck.AttackerKnows T := by
  rcases messageDecrypt_honestCks_or_seed_attackerKnows hreach ht_ak hparse hmac_eq hseed with
    ⟨me, st_s, stH, hst_s, hcks_eq⟩ | hseed_ak
  · obtain ⟨rk_s, pk_s, j_s, hcks_create, _⟩ := (hJ.1 me st_s stH hst_s).1
    exact False.elim (createChain_snd_ne_pqxdhKdf_ck rk_s pk_s st_s.dhs ikm j_s k (hcks_create.symm.trans hcks_eq))
  · rw [hseed] at hseed_ak
    rcases kdfProv_litByte01_of_reachable hreach hseed_ak with hck_ak | ⟨j_ev, ses, pk_ev, n_ev, rIdx, src, hev⟩
    · exact chainKeyAt_pqxdhKdf_ck_ak_imp_ak hreach hle hJ k hck_ak
    · obtain ⟨c₁, hc₁_active, hseed_eq⟩ := hJ.2 j_ev ses pk_ev n_ev _ rIdx src hev
      have hck_eq : chainKeyAt (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck k = c₁.chainKey :=
        (kdfExtract_inj_rk hseed_eq).1
      rcases hc₁_active with ⟨rk₁, t₁, j₁, _, _, hc₁_eq, _⟩ | ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j₁, hc₁_eq, hak⟩
      · exact False.elim (createChain_snd_ne_pqxdhKdf_ck rk₁ c₁.ratchetKey (randTerm t₁ 32) ikm j₁ k
          (hck_eq.trans hc₁_eq).symm)
      · have hbase : (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck =
            (DY.Libsignal.PQXDH.pqxdhKdf
              (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 (PQKem.kemEncap pk_kem r_kem).2)).ck :=
          (chainKeyAt_concat_base_inj k j₁ (hck_eq.trans hc₁_eq)).1
        rw [hbase]; exact hak

theorem honestKdfOut_createChain_imp_honest_or_prkAK {T tr : ExecTrace}
    (hreach : ReachableTrace tr) (hle : tr ≤ T) (hJ : JRkSpine T tr)
    {rk' pk : DY.Bytes} {t_dhs m : Nat}
    (hout : HonestKdfOut tr (chainKeyAt (createChain rk' pk (randTerm t_dhs 32)).2 m)) :
    HonestSendRoot T (createChain rk' pk (randTerm t_dhs 32)).2 ∨
    (hmac rk' (DiffieHellman.dh (X25519.normalizeX25519Key pk) (randTerm t_dhs 32))).AttackerKnows T := by
  obtain ⟨me, st₁, idx₁, hst₁, hrk | hcks | ⟨c₁, hc₁, hck₁⟩⟩ := hout
  · have hst₁_dhs : StRkDhsInv T tr.length st₁ := ((JRk_reachable hreach hle).2.1 me st₁ idx₁ hst₁).1
    exact False.elim (createChain_snd_ne_st_rk hst₁_dhs rk' pk (randTerm t_dhs 32) m hrk)
  · exact .inl (honestSendRoot_of_stored_cks_eq hle hJ hst₁ hcks.symm)
  · rcases (hJ.1 me st₁ idx₁ hst₁).2 c₁ hc₁ with
      ⟨rk₁, t₁, j₁, _, _, hc₁_eq, hdisj₁⟩ | ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j₁, hc₁_eq, _⟩
    · obtain ⟨hroot_eq, hprk_eq⟩ := createChain_snd_chainKeyAt_eq_imp_prk_eq (hck₁.trans hc₁_eq)
      rcases hdisj₁ with hhon | hprk_ak
      · exact .inl (hroot_eq.symm ▸ hhon)
      · exact .inr (hprk_eq.symm ▸ hprk_ak)
    · exact False.elim (createChain_snd_ne_pqxdhKdf_ck rk' pk (randTerm t_dhs 32) _ m j₁ (hck₁.trans hc₁_eq))

theorem chainKeyAt_createChain_ak_imp_honest_or_prkAK {T tr : ExecTrace}
    (hreach : ReachableTrace tr) (hle : tr ≤ T) (hJ : JRkSpine T tr)
    {rk' pk : DY.Bytes} {t_dhs : Nat} :
    ∀ (k : Nat), (chainKeyAt (createChain rk' pk (randTerm t_dhs 32)).2 k).AttackerKnows tr →
      HonestSendRoot T (createChain rk' pk (randTerm t_dhs 32)).2 ∨
      (hmac rk' (DiffieHellman.dh (X25519.normalizeX25519Key pk) (randTerm t_dhs 32))).AttackerKnows T
  | 0, hak => by
    rcases kdfProv_wr2_of_reachable hreach hak with hprk_ak | hout
    · exact .inr (DY.Bytes.AttackerKnows_le _ tr T hle hprk_ak)
    · exact honestKdfOut_createChain_imp_honest_or_prkAK hreach hle hJ (m := 0) hout
  | m + 1, hak => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at hak
    rcases kdfProv_litByte02_of_reachable hreach hak with hprev | hout
    · exact chainKeyAt_createChain_ak_imp_honest_or_prkAK hreach hle hJ m hprev
    · have hout' : HonestKdfOut tr (chainKeyAt (createChain rk' pk (randTerm t_dhs 32)).2 (m + 1)) := by
        rw [chainKeyAt_succ_eq_kdfCk_fst]; exact hout
      exact honestKdfOut_createChain_imp_honest_or_prkAK hreach hle hJ (m := m + 1) hout'

/-- Factored step lemma for a `createChain` receiving chain: when `verifyMacAndDecrypt` succeeds on
a seed derived from `(createChain rk' pk (randTerm t_dhs 32)).2`, either its root is an
`HonestSendRoot T` or its ratchet `prk` is `AttackerKnows T`. -/
theorem acceptedChain_honest_or_prkAK {T tr : ExecTrace}
    (hreach : ReachableTrace tr) (hle : tr ≤ T) (hJ : JRkSpine T tr)
    {t pqSalt seed peerIk myIk rk' pk : DY.Bytes} {msg : TRSignalMsg} {t_dhs k : Nat}
    (ht_ak : t.AttackerKnows tr) (hparse : parseTrSignalMsg t = some msg)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey peerIk myIk msg.wire)
    (hseed : seed = KdfExtract.kdfExtract
      (chainKeyAt (createChain rk' pk (randTerm t_dhs 32)).2 k) (litByte 0x01)) :
    HonestSendRoot T (createChain rk' pk (randTerm t_dhs 32)).2 ∨
    (hmac rk' (DiffieHellman.dh (X25519.normalizeX25519Key pk) (randTerm t_dhs 32))).AttackerKnows T := by
  rcases messageDecrypt_honestCks_or_seed_attackerKnows hreach ht_ak hparse hmac_eq hseed with
    ⟨me, st_s, stH, hst_s, hcks_eq⟩ | hseed_ak
  · exact .inl (honestSendRoot_of_stored_cks_eq hle hJ hst_s hcks_eq)
  · rw [hseed] at hseed_ak
    rcases kdfProv_litByte01_of_reachable hreach hseed_ak with hck_ak | ⟨j_ev, ses, pk_ev, n_ev, rIdx, src, hev⟩
    · exact chainKeyAt_createChain_ak_imp_honest_or_prkAK hreach hle hJ k hck_ak
    · obtain ⟨c₁, hc₁_active, hseed_eq⟩ := hJ.2 j_ev ses pk_ev n_ev _ rIdx src hev
      have hck_eq : chainKeyAt (createChain rk' pk (randTerm t_dhs 32)).2 k = c₁.chainKey :=
        (kdfExtract_inj_rk hseed_eq).1
      rcases activeRecvChainSpine_imp_recvChainSpine hc₁_active with
        ⟨rk₁, t₁, j₁, _, _, hc₁_eq, hdisj₁⟩ | ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j₁, hc₁_eq, _⟩
      · obtain ⟨hroot_eq, hprk_eq⟩ := createChain_snd_chainKeyAt_eq_imp_prk_eq (hck_eq.trans hc₁_eq)
        rcases hdisj₁ with hhon | hprk_ak
        · exact .inl (hroot_eq.symm ▸ hhon)
        · exact .inr (hprk_eq.symm ▸ hprk_ak)
      · exact False.elim (createChain_snd_ne_pqxdhKdf_ck rk' pk (randTerm t_dhs 32) _ k j₁ (hck_eq.trans hc₁_eq))

/-! ## Transition Preservation of `JRkSpine` -/

theorem consumeMessageKey_eq_spine {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c counter = some (seed, c')) :
    seed = KdfExtract.kdfExtract (chainKeyAt c.chainKey (counter.toNat - c.index.toNat)) (litByte 0x01) ∧
    c' = { c with chainKey := chainKeyAt c.chainKey ((counter.toNat - c.index.toNat) + 1), index := counter + 1 } := by
  unfold consumeMessageKey at h
  split at h <;> [cases h; (split at h <;> [cases h; (split at h <;> [cases h; skip])])]
  injection h with h; injection h with h1 h2
  subst h1; subst h2
  refine ⟨rfl, ?_⟩
  rw [chainKeyAt_succ_eq_kdfCk_fst]

def PQRkSpineAt (T tr : ExecTrace) {α : Type} (Q : ExecTrace → α → Prop) (x : Traceful α) : Prop :=
  JRkSpine T tr → (x.run tr).2.val ≤ T →
    JRkSpine T (x.run tr).2.val ∧ ∀ a, (x.run tr).1 = some a → Q (x.run tr).2.val a

theorem PQRkSpineAt.bind {T tr : ExecTrace} {α β : Type} {Q : ExecTrace → α → Prop} {R : ExecTrace → β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : PQRkSpineAt T tr Q x) (hf : ∀ tr1 a, tr ≤ tr1 → Q tr1 a → PQRkSpineAt T tr1 R (f a)) :
    PQRkSpineAt T tr R (x >>= f) := by
  intro hJ hle; rw [CompTrace.run_bind_snd] at hle; rw [Traceful.run_bind]; have hx0 := hx hJ
  rcases h : x.run tr with ⟨_ | a, trMid, hmid⟩ <;> rw [h] at hle hx0
  · exact ⟨(hx0 hle).1, fun b hb => by cases hb⟩
  · have hx' := hx0 (Trace.le_trans _ _ _ ((f a).run trMid).2.property hle)
    exact hf trMid a hmid (hx'.2 a rfl) hx'.1 hle

theorem PQRkSpineAt.of_id {T tr : ExecTrace} {α : Type} {x : Traceful α} (hx : (x.run tr).2.val = tr) :
    PQRkSpineAt T tr (fun _ _ => True) x := by
  intro hJ _; rw [hx]; exact ⟨hJ, fun _ _ => trivial⟩

theorem PQRkSpineAt.pure {T tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} (a : α) (ha : Q tr a) :
    PQRkSpineAt T tr Q (Pure.pure a : Traceful α) := by
  intro hJ _; rw [Traceful.run_pure]; refine ⟨hJ, fun b hb => ?_⟩; cases hb; exact ha

theorem PQRkSpineAt.failure {T tr : ExecTrace} {α : Type} {Q : ExecTrace → α → Prop} :
    PQRkSpineAt T tr Q (Alternative.failure : Traceful α) := by
  intro hJ _; rw [Traceful.run_failure]; exact ⟨hJ, fun _ hb => by cases hb⟩

theorem PQRkSpineAt.guardP {T tr : ExecTrace} (p : Prop) [Decidable p] :
    PQRkSpineAt T tr (fun _ _ => p) (_root_.guard p : Traceful Unit) := by
  unfold _root_.guard; split <;> [(rename_i hp; exact PQRkSpineAt.pure () hp); exact PQRkSpineAt.failure]

theorem PQRkSpineAt.guardTrace {T tr : ExecTrace} (p : ExecTrace → Bool) :
    PQRkSpineAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.guardTrace p) :=
  PQRkSpineAt.of_id (by unfold DY.Libsignal.TripleRatchet.guardTrace; rw [Traceful.run_mk])

theorem PQRkSpineAt.traceLength {T tr : ExecTrace} :
    PQRkSpineAt T tr (fun _ _ => True) DY.Libsignal.TripleRatchet.traceLength :=
  PQRkSpineAt.of_id (by unfold DY.Libsignal.TripleRatchet.traceLength; rw [Traceful.run_mk])

theorem PQRkSpineAt.genRand {T tr : ExecTrace} (n : Nat) :
    PQRkSpineAt T tr (fun _ r => r = randTerm tr.length n) (Random.genRand n) := by
  intro hJ _; simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_bind, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
  exact ⟨JRkSpine_append_other hJ, fun b hb => by cases hb; rfl⟩

theorem PQRkSpineAt.sendMessage {T tr : ExecTrace} (m : DY.Bytes) :
    PQRkSpineAt T tr (fun _ _ => True) (Network.sendMessage m) := by
  intro hJ _; rw [CompPresTRExp.run_sendMessage_snd]
  exact ⟨JRkSpine_append_other hJ, fun _ _ => trivial⟩

theorem PQRkSpineAt.logEvent {T tr : ExecTrace} (ev : TREvent)
    (hev : ∀ s pk n seed rIdx src, ev = .SkippedKeyStored s pk n seed rIdx src → SkippedSeedSpine T seed) :
    PQRkSpineAt T tr (fun _ _ => True) (ProtocolEvent.logEvent ev) := by
  intro hJ _; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_bind, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
  exact ⟨JRkSpine_append_ev ev hev hJ, fun _ _ => trivial⟩

theorem PQRkSpineAt.storeLocalState {T tr : ExecTrace} (p : Participant) {st : TRState} (hst : StSpineInv T st) :
    PQRkSpineAt T tr (fun _ _ => True) (PersistentLocalState.storeLocalState p st) := by
  intro hJ _; simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_mk]
  exact ⟨JRkSpine_append_st p hst hJ, fun _ _ => trivial⟩

theorem PQRkSpineAt.getLocalState {T tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQRkSpineAt T tr (fun tr1 st => tr1 = tr ∧ StSpineInv T st ∧ TRStateStoredAt me st stH tr)
      (PersistentLocalState.getLocalState me stH) := by
  intro hJ hle; rw [CompTrace.getLocalState_tr_snd] at hle ⊢; refine ⟨hJ, fun st hst => ?_⟩
  rw [CompTrace.getLocalState_tr_fst] at hst
  rcases he : (tr.at? stH : Option CompTrace.TRStEntry) with _ | ⟨⟨p, st'⟩⟩
  · rw [he] at hst; cases hst
  · rw [he] at hst; dsimp only at hst
    by_cases hp : p = me
    · subst hp; simp only [↓reduceIte] at hst; cases hst
      exact ⟨rfl, hJ.1 _ _ stH he, he⟩
    · simp only [hp, ↓reduceIte] at hst; cases hst

theorem PQRkSpineAt.getEntryTR {T tr : ExecTrace} (evH : Nat) :
    PQRkSpineAt T tr (fun _ _ => True) (DY.getEntry evH : Traceful CompTrace.TREntry) :=
  PQRkSpineAt.of_id (by simp only [Symbolic.DYBridge.DY.getEntry_eq_1]; rw [Traceful.run_mk])

theorem PQRkSpineAt.receiveMessage {T tr : ExecTrace} (msgH : Nat) :
    PQRkSpineAt T tr (fun _ b => b.AttackerKnows tr) (Network.receiveMessage msgH) := by
  intro hJ hle; rw [CompTrace.receiveMessage_snd] at hle ⊢; refine ⟨hJ, fun a ha => ?_⟩
  rw [CompTrace.receiveMessage_fst] at ha
  rcases hat : (tr.at? msgH : Option CompTrace.NetEntry) with _ | ⟨⟨b⟩⟩ <;> rw [hat] at ha
  · cases ha
  · injection ha with ha; subst ha
    exact CompTrace.NetMsgAt.attackerKnows hat

theorem PQRkSpineAt.receiveSignalMsg {T tr : ExecTrace} (msgH : Nat) :
    PQRkSpineAt T tr (fun _ msg => ∃ t : DY.Bytes, t.AttackerKnows tr ∧ parseTrSignalMsg t = some msg)
      (DY.Libsignal.TripleRatchet.receiveSignalMsg msgH) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine PQRkSpineAt.bind (PQRkSpineAt.receiveMessage msgH) fun _ t _ ht_ak => ?_
  rcases hp : parseTrSignalMsg t with _ | msg
  · exact PQRkSpineAt.failure
  · exact PQRkSpineAt.bind (PQRkSpineAt.guardP _) fun _ _ _ _ => PQRkSpineAt.pure msg ⟨t, ht_ak, hp⟩

theorem PQRkSpineAt.verifyMacAndDecrypt {T tr : ExecTrace} (st : TRState) (msg : TRSignalMsg) (pqSalt seed : DY.Bytes) :
    PQRkSpineAt T tr (fun _ _ => msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
      (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  refine PQRkSpineAt.bind (PQRkSpineAt.guardP _) fun _ _ _ hmac hJ _ => by
    erw [Traceful.run_mk]; exact ⟨hJ, fun _ _ => hmac⟩

theorem PQRkSpineAt.logSkippedKeys {T : ExecTrace} (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (c : RecvChain) (n : UInt32) {tr : ExecTrace},
      ActiveRecvChainSpine T c →
      PQRkSpineAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src c.chainKey n k)
  | 0, _, _, _, _ => by simp only [DY.Libsignal.TripleRatchet.logSkippedKeys]; exact PQRkSpineAt.pure () trivial
  | k + 1, c, n, _, hc => by
    simp only [DY.Libsignal.TripleRatchet.logSkippedKeys]
    refine PQRkSpineAt.bind (PQRkSpineAt.logEvent _ ?_) fun _ _ _ _ =>
      PQRkSpineAt.logSkippedKeys s pk rIdx src k { c with chainKey := (kdfCk c.chainKey).1, index := n } (n + 1)
        (activeRecvChainSpine_kdfCk_fst hc n)
    intro s' pk' n' seed' rIdx' src' h; cases h; exact ⟨c, hc, rfl⟩

theorem PQRkSpineAt.logMessageKeyAndStore {T tr : ExecTrace} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx p : Nat) {st : TRState} (hst : StSpineInv T st) :
    PQRkSpineAt T tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx p st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ =>
    PQRkSpineAt.storeLocalState me hst

theorem stSpineInv_setRecvChain {T : ExecTrace} {st : TRState} {c : RecvChain} {spqr' : DY.Bytes}
    (hst : StSpineInv T st) (hc : RecvChainSpine T c) :
    StSpineInv T { st with recv := setRecvChain st.recv c, spqr := spqr' } := by
  refine ⟨hst.1, fun c0 hc0 => ?_⟩
  unfold setRecvChain at hc0; rw [List.mem_map] at hc0; obtain ⟨c1, hc1, rfl⟩ := hc0
  by_cases hk : (c1.ratchetKey == c.ratchetKey) = true
  · simp only [hk, ↓reduceIte]; exact hc
  · simp only [hk, Bool.false_eq_true, ↓reduceIte]; exact hst.2 c1 hc1

def PreVerifySpine (T : ExecTrace) (st0 : TRState) (pk : DY.Bytes) (st : TRState) (c : RecvChain) : Prop :=
  StCksIsCreateChain st ∧
  (∀ c0 ∈ st.recv, RecvChainSpine T c → RecvChainSpine T c0) ∧
  (RecvChainSpine T c ∨ (c.ratchetKey = pk ∧ c.chainKey = (createChain st0.rk pk st0.dhs).2)) ∧
  st.peerIk = st0.peerIk ∧ st.myIk = st0.myIk

theorem PQRkSpineAt.dhRatchetStep {T tr : ExecTrace} {st0 : TRState} {pk : DY.Bytes} (hst0 : StSpineInv T st0) :
    PQRkSpineAt T tr (fun _ (r : TRState × RecvChain) => PreVerifySpine T st0 pk r.1 r.2)
      (DY.Libsignal.TripleRatchet.dhRatchetStep st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  refine PQRkSpineAt.bind (PQRkSpineAt.guardP _) fun _ _ _ _ => ?_
  rcases hc1 : createChain st0.rk pk st0.dhs with ⟨rk1, ckr⟩; dsimp only
  have hckr_eq : ckr = (createChain st0.rk pk st0.dhs).2 := by rw [hc1]
  refine PQRkSpineAt.bind (PQRkSpineAt.genRand 32) fun _ dhs _ _ => ?_
  rcases hc2 : createChain rk1 pk dhs with ⟨rk2, cks⟩; dsimp only
  have hrk2_eq : rk2 = (createChain rk1 pk dhs).1 := by rw [hc2]
  have hcks_eq : cks = (createChain rk1 pk dhs).2 := by rw [hc2]
  refine PQRkSpineAt.pure _ ⟨⟨rk1, pk, 0, hcks_eq, hrk2_eq⟩, ?_, .inr ⟨rfl, hckr_eq⟩, rfl, rfl⟩
  intro c0 hc0 hckr_s
  have hmem := List.mem_of_mem_drop hc0
  rw [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | rfl
  · exact hst0.2 c0 hmem
  · exact hckr_s

theorem PQRkSpineAt.ensureReceiverChain {T tr : ExecTrace} {st0 : TRState} {pk : DY.Bytes} (hst0 : StSpineInv T st0) :
    PQRkSpineAt T tr (fun _ (r : TRState × RecvChain × Bool) => PreVerifySpine T st0 pk r.1 r.2.1)
      (DY.Libsignal.TripleRatchet.ensureReceiverChain st0 pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; split
  · rename_i c hrc
    refine PQRkSpineAt.pure _ ⟨hst0.1, fun c0 hc0 _ => hst0.2 c0 hc0, .inl ?_, rfl, rfl⟩
    unfold recvChainFor at hrc; split at hrc
    · rename_i c0 hfind; injection hrc with hrc; injection hrc with hrc _; subst hrc
      exact hst0.2 c0 (List.mem_of_find?_eq_some hfind)
    · split at hrc <;> [cases hrc; (injection hrc with hrc; injection hrc with _ hb; cases hb)]
  · refine PQRkSpineAt.bind (PQRkSpineAt.dhRatchetStep hst0) fun _ ⟨st', c⟩ _ hr => PQRkSpineAt.pure _ hr
  · exact PQRkSpineAt.failure

theorem PQRkSpineAt.messageEncryptAbort {T tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQRkSpineAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact PQRkSpineAt.bind (PQRkSpineAt.getLocalState me stH) fun _ _ _ _ =>
    PQRkSpineAt.bind (PQRkSpineAt.genRand 32) fun _ _ _ _ => PQRkSpineAt.failure

theorem PQRkSpineAt.messageEncrypt {T tr : ExecTrace} (me : Participant) (stH coinsLen pqIdx : Nat) :
    PQRkSpineAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.messageEncrypt me stH coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine PQRkSpineAt.bind (PQRkSpineAt.getLocalState me stH) fun _ st _ ⟨_, hst, _⟩ =>
    PQRkSpineAt.bind (PQRkSpineAt.guardP _) fun _ _ _ _ =>
    PQRkSpineAt.bind (PQRkSpineAt.genRand 32) fun _ _ _ _ =>
    PQRkSpineAt.bind (PQRkSpineAt.genRand coinsLen) fun _ coins _ _ => ?_
  rcases hspqr : Spqr.spqrSend st.spqr coins with ⟨spqr', key, pqMsg⟩; dsimp only
  refine PQRkSpineAt.bind (PQRkSpineAt.sendMessage key) fun _ _ _ _ => ?_
  rcases hck : kdfCk st.cks with ⟨ck', seed⟩; dsimp only
  obtain ⟨rk1, k_pk, j_s, hcks_eq, hrk_eq⟩ := hst.1
  have hck'_eq : ck' = chainKeyAt (createChain rk1 k_pk st.dhs).2 (j_s + 1) := by
    have h1 : ck' = (kdfCk st.cks).1 := by rw [hck]
    rw [h1, hcks_eq, ← chainKeyAt_succ_eq_kdfCk_fst]
  have hst' : StSpineInv T { st with cks := ck', ns := st.ns + 1, spqr := spqr' } :=
    ⟨⟨rk1, k_pk, j_s + 1, hck'_eq, hrk_eq⟩, hst.2⟩
  refine PQRkSpineAt.bind (PQRkSpineAt.receiveMessage pqIdx) fun _ _ _ _ =>
    PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ =>
    PQRkSpineAt.bind (PQRkSpineAt.logMessageKeyAndStore me _ _ _ _ _ _ _ hst') fun _ _ _ _ =>
      PQRkSpineAt.sendMessage _

theorem PQRkSpineAt.exposeKey {T tr : ExecTrace} (me : Participant) (stH : Nat) (k : KeyComponent) :
    PQRkSpineAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeKey me stH k) := by
  unfold DY.Libsignal.TripleRatchet.exposeKey
  refine PQRkSpineAt.bind (PQRkSpineAt.getLocalState me stH) fun _ st _ _ => ?_
  cases k with
  | rk => exact PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQRkSpineAt.sendMessage _
  | dhs => exact PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQRkSpineAt.sendMessage _
  | cks => exact PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQRkSpineAt.sendMessage _
  | ckr pk =>
    dsimp only
    rcases findRecvChain st.recv pk with _ | c <;>
      [exact PQRkSpineAt.failure;
       exact PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => PQRkSpineAt.sendMessage _]

theorem PQRkSpineAt.exposeSpqr {T tr : ExecTrace} (me : Participant) (stH : Nat) :
    PQRkSpineAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSpqr me stH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSpqr
  exact PQRkSpineAt.bind (PQRkSpineAt.getLocalState me stH) fun _ _ _ _ =>
    PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ =>
      PQRkSpineAt.sendMessage _

theorem PQRkSpineAt.exposeSkipped {T tr : ExecTrace} (evH : Nat) :
    PQRkSpineAt T tr (fun _ _ => True) (DY.Libsignal.TripleRatchet.exposeSkipped evH) := by
  unfold DY.Libsignal.TripleRatchet.exposeSkipped
  refine PQRkSpineAt.bind (PQRkSpineAt.getEntryTR evH) fun _ ⟨ev⟩ _ _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    exact PQRkSpineAt.bind (PQRkSpineAt.guardTrace _) fun _ _ _ _ =>
      PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ =>
        PQRkSpineAt.sendMessage _
  | _ => exact PQRkSpineAt.failure

theorem PQRkSpineAt.messageDecryptSkipped {T tr : ExecTrace} (me : Participant) (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQRkSpineAt T tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH evH pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine PQRkSpineAt.bind (PQRkSpineAt.getLocalState me stH) fun _ st _ ⟨_, hst, _⟩ =>
    PQRkSpineAt.bind (PQRkSpineAt.receiveSignalMsg msgH) fun _ msg _ _ =>
    PQRkSpineAt.bind (PQRkSpineAt.getEntryTR evH) fun _ ⟨ev⟩ _ _ => ?_
  cases ev with
  | SkippedKeyStored s pk n seed rIdx src =>
    refine PQRkSpineAt.bind (PQRkSpineAt.guardP _) fun _ _ _ _ =>
      PQRkSpineAt.bind (PQRkSpineAt.guardTrace _) fun _ _ _ _ => ?_
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · exact PQRkSpineAt.failure
    · refine PQRkSpineAt.bind (PQRkSpineAt.sendMessage key) fun _ _ _ _ =>
        PQRkSpineAt.bind (PQRkSpineAt.receiveMessage pqIdx) fun _ pqSalt _ _ =>
        PQRkSpineAt.bind (PQRkSpineAt.verifyMacAndDecrypt st msg pqSalt seed) fun _ _ _ _ =>
        PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ =>
        PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ =>
          PQRkSpineAt.logMessageKeyAndStore me _ _ _ _ _ _ _ ⟨hst.1, hst.2⟩
  | _ => exact PQRkSpineAt.failure

theorem PQRkSpineAt.messageDecrypt {T tr : ExecTrace}
    (hreach : ReachableTrace tr) (hle_tr_T : tr ≤ T)
    (me : Participant) (stH msgH pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PQRkSpineAt T tr (fun _ _ => True)
      (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx) := by
  intro hJ_init hle_end
  refine (?_ : PQRkSpineAt T tr (fun _ _ => True)
    (DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqIdx spqrMsgIdx)) hJ_init hle_end
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine PQRkSpineAt.bind (PQRkSpineAt.getLocalState me stH) fun tr1 st0 _ ⟨rfl, hst0, hstored0⟩ =>
    PQRkSpineAt.bind (PQRkSpineAt.receiveSignalMsg msgH) fun _ msg _ ⟨t, ht_ak, hparse⟩ =>
    PQRkSpineAt.bind (PQRkSpineAt.ensureReceiverChain hst0) fun _ ⟨st, c, ratcheted⟩ _ hpre => ?_
  dsimp only
  rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · exact PQRkSpineAt.failure
  dsimp only
  rcases hrecv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · exact PQRkSpineAt.failure
  refine PQRkSpineAt.bind (PQRkSpineAt.sendMessage key) fun _ _ _ _ =>
    PQRkSpineAt.bind (PQRkSpineAt.receiveMessage pqIdx) fun _ pqSalt _ _ =>
    PQRkSpineAt.bind (PQRkSpineAt.verifyMacAndDecrypt st msg pqSalt seed) fun tr6 m _ hmac => ?_
  obtain ⟨hseed_eq, hc'_eq⟩ := consumeMessageKey_eq_spine hcons
  let d := msg.counter.toNat - c.index.toNat
  have hc_active : ActiveRecvChainSpine T c := by
    rcases hpre.2.2.1 with (hcreate | ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j, hck_eq, _⟩) | ⟨hc_pk, hc_ck⟩
    · exact .inl hcreate
    · have hseed_base : seed = KdfExtract.kdfExtract
          (chainKeyAt (DY.Libsignal.PQXDH.pqxdhKdf
            (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 dh4 (PQKem.kemEncap pk_kem r_kem).2)).ck (j + d))
          (litByte 0x01) := by
        rw [hseed_eq, hck_eq, chainKeyAt_add]
      have hak := acceptedBaseChain_ckAK hreach hle_tr_T hJ_init ht_ak hparse hmac hseed_base
      exact .inr ⟨dh1, dh2, dh3, dh4, pk_kem, r_kem, j, hck_eq, hak⟩
    · have hdhs0 : StRkDhsInv T tr1.length st0 := ((JRk_reachable hreach hle_tr_T).2.1 me st0 stH hstored0).1
      obtain ⟨hrk0, t_old, _, hdhs0_eq, hpair0⟩ := hdhs0
      have hc_ck0 : c.chainKey = chainKeyAt (createChain st0.rk c.ratchetKey (randTerm t_old 32)).2 0 := by
        rw [hc_ck, hc_pk, hdhs0_eq]; rfl
      have hseed_create : seed = KdfExtract.kdfExtract
          (chainKeyAt (createChain st0.rk c.ratchetKey (randTerm t_old 32)).2 d) (litByte 0x01) := by
        rw [hseed_eq, hc_ck0, chainKeyAt]
      have hdisj := acceptedChain_honest_or_prkAK hreach hle_tr_T hJ_init ht_ak hparse hmac hseed_create
      have hpair : RkDhsPair T st0.rk t_old := by
        rcases hpair0 with h1 | h2
        · exact .inl h1
        · exact .inr (.inl h2)
      exact .inl ⟨st0.rk, t_old, 0, hrk0, hpair, hc_ck0, hdisj⟩
  have hc_spine : RecvChainSpine T c := activeRecvChainSpine_imp_recvChainSpine hc_active
  have hst_spine : StSpineInv T st := ⟨hpre.1, fun c0 hc0 => hpre.2.1 c0 hc0 hc_spine⟩
  have hc'_spine : RecvChainSpine T c' := by
    rw [hc'_eq]
    exact activeRecvChainSpine_imp_recvChainSpine (activeRecvChainSpine_advance hc_active (d + 1) (msg.counter + 1))
  have htail : ∀ {tr_t : ExecTrace}, PQRkSpineAt T tr_t (fun _ _ => True) (do
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey c.index d
      ProtocolEvent.logEvent (TREvent.Received me st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st.sessionInfo me) KeyDir.receiver seed pqSalt msg.counter c.rIdx stH
        { st with recv := setRecvChain st.recv c', spqr := spqr' }) := fun {tr_t} =>
    PQRkSpineAt.bind (PQRkSpineAt.logSkippedKeys _ _ _ _ d c c.index hc_active) fun _ _ _ _ =>
      PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ =>
      PQRkSpineAt.logMessageKeyAndStore me _ _ _ _ _ _ _ (stSpineInv_setRecvChain hst_spine hc'_spine)
  split
  · refine PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ =>
      PQRkSpineAt.bind (PQRkSpineAt.logEvent _ (by intro _ _ _ _ _ _ h; cases h)) fun _ _ _ _ => htail
  · exact htail

theorem JRkSpine_preserves_aliceStart {T tr : ExecTrace}
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) (hJ : JRkSpine T tr) :
    JRkSpine T ((aliceStart a b idStateIdx regIdxB bh).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr hJ (JRkSpine_append_other hJ)
    fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let hs := CompPresPQXDH.aliceOut tr ikA ikBPk spkPk pqPk opk
  let tr1 := tr.append (RndE 32); let tr2 := tr1.append (RndE 32); let dhsA := randTerm tr2.length 32
  let stA : TRState :=
    { peer := b, myIk := DY.Libsignal.PQXDH.serializedIk hs.ikA, peerIk := DY.Libsignal.PQXDH.serializedIk hs.ikB,
      rk := (createChain hs.keys.rk hs.spk dhsA).1, dhs := dhsA, cks := (createChain hs.keys.rk hs.spk dhsA).2,
      ns := 0, pn := 0,
      sid := Concat.concat (DiffieHellman.dhPk dhsA) hs.keys.rk,
      initiator := true, rIdx := 1,
      recv := [{ ratchetKey := hs.spk, chainKey := hs.keys.ck, index := 0, rIdx := 1 }],
      spqr := Spqr.spqrInit hs.keys.pqr spqrA2B }
  let tr3 := tr2.append (RndE 32); let tr4 := tr3.append (NetE hs.ek); let tr5 := tr4.append (NetE hs.ct)
  let tr6 := tr5.append (EvE (PQXDHEvent.AliceDone a b hs.ikA hs.ikB hs.spk hs.pqpk hs.opk hs.ek hs.ct hs.keys))
  let tr7 := tr6.append (TREvE (TREvent.InitSession a b (DiffieHellman.dhPk dhsA) hs.spk))
  let tr8 := tr7.append (CEvE (ComposedEvent.HandshakeSession (stA.sessionInfo a) tr5.length))
  rw [CompTrace.run_genRand_bind_snd]; dsimp only
  rw [CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, htl,
    CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  change JRkSpine T (tr8.append (TRStE a stA))
  have hJ8 : JRkSpine T tr8 :=
    JRkSpine_append_other (JRkSpine_append_ev _ (by intro _ _ _ _ _ _ h; cases h)
      (JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other
        (JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other hJ)))))))
  refine JRkSpine_append_st a ⟨⟨hs.keys.rk, hs.spk, 0, rfl, rfl⟩, fun c hc => ?_⟩ hJ8
  rw [List.mem_singleton] at hc; subst hc
  dsimp [hs, CompPresPQXDH.aliceOut, DY.Libsignal.PQXDH.aliceAgreement]
  exact .inr ⟨_, _, _, _, _, _, 0, rfl, .inl rfl⟩

theorem JRkSpine_logSkippedKeys_preserves {T : ExecTrace} (s : SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) :
    ∀ (k : Nat) (c : RecvChain) (n : UInt32) (tr : ExecTrace),
      ActiveRecvChainSpine T c →
      JRkSpine T tr →
      JRkSpine T ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src c.chainKey n k).run tr).2.val
  | 0, _, _, _, _, hJ => by unfold DY.Libsignal.TripleRatchet.logSkippedKeys; rw [Traceful.run_pure]; exact hJ
  | k + 1, c, n, tr, hc, hJ => by
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [CompPresTRExp.run_logEvent_bind_snd (Ev := TREvent)]
    refine JRkSpine_logSkippedKeys_preserves s pk rIdx src k
      { c with chainKey := (kdfCk c.chainKey).1, index := n } (n + 1) _
      (activeRecvChainSpine_kdfCk_fst hc n) (JRkSpine_append_ev _ ?_ hJ)
    intro _ _ _ _ _ _ h; cases h; exact ⟨c, hc, rfl⟩

theorem bind_verifyMacAndDecrypt_eq_at {Inv : ExecTrace → Prop} {α : Type}
    (st : TRState) (msg : TRSignalMsg) (pqSalt seed : DY.Bytes)
    {f : DY.Bytes → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ m, msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire →
      Inv (((f m).run tr).2.val)) :
    Inv (((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  rw [CompTrace.run_bind_assoc_snd]
  exact CompTrace.bind_guardP_at _ tr hInv fun hmac => by
    rcases SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext with _ | m
    · rw [CompTrace.run_bind_snd]; erw [Traceful.run_mk]; exact hInv
    · rw [CompTrace.run_bind_snd]; erw [Traceful.run_mk]; dsimp [MonadLift.monadLift]; exact hf m hmac

theorem JRkSpine_bobStart_commit {T tr : ExecTrace} (hJ : JRkSpine T tr)
    (b a : Participant) (sB sS sQ : DY.Bytes) (o : Option DY.Bytes) (ikA ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (dhs spqr' seed pqSalt m : DY.Bytes) (c' : RecvChain)
    (hc_active : ActiveRecvChainSpine T (CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS))
    (hst_spine : StSpineInv T { CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs with
      recv := setRecvChain (CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs).recv c', spqr := spqr' }) :
    let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
    let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
    JRkSpine T (((do
      let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
      ProtocolEvent.logEvent (PQXDHEvent.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys)
      if true then
        ProtocolEvent.logEvent (TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
        ProtocolEvent.logEvent (TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
      ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
      let skipped := msg.counter.toNat - c.index.toNat; let childIdx := (← DY.Libsignal.TripleRatchet.traceLength) + skipped + 2
      DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
        { st with recv := setRecvChain st.recv c', spqr := spqr' }).run tr).2.val) := by
  intro st c; let doneIdx := tr.length
  have htl : ∀ {α : Type} (g : Nat → Traceful α) (t : ExecTrace),
      ((DY.Libsignal.TripleRatchet.traceLength >>= g).run t).2.val = ((g t.length).run t).2.val := fun g t => by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [CompTrace.run_bind_snd, Traceful.run_mk]
  let tr₁ := tr.append (EvE (.BobDone b a (DiffieHellman.dhPk sB) ikA (DiffieHellman.dhPk sS) (PQKem.kemPk sQ) (o.map DiffieHellman.dhPk) ek ct keys))
  let tr₂ := tr₁.append (TREvE (.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs)))
  let tr₃ := tr₂.append (TREvE (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
  let tr₄ := tr₃.append (CEvE (.HandshakeSession (st.sessionInfo b) doneIdx))
  have hJ₄ : JRkSpine T tr₄ :=
    JRkSpine_append_other (JRkSpine_append_ev _ (by intro _ _ _ _ _ _ h; cases h)
      (JRkSpine_append_ev _ (by intro _ _ _ _ _ _ h; cases h) (JRkSpine_append_other hJ)))
  let skipped := msg.counter.toNat - c.index.toNat; let childIdx := tr₄.length + skipped + 2
  let skipAct := DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
  let restAct : Unit → Traceful Nat := fun _ => do
    ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx
      { st with recv := setRecvChain st.recv c', spqr := spqr' }
  rw [htl, CompPresTRExp.run_logEvent_bind_snd]; simp only [↓reduceIte]
  rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_logEvent_bind_snd, htl]
  change JRkSpine T (((skipAct >>= restAct).run tr₄).2.val)
  rw [CompInv.CompPresBob.run_logSkippedKeys_bind_snd]
  let tr₅ := (skipAct.run tr₄).2.val
  have hJ₅ : JRkSpine T tr₅ := JRkSpine_logSkippedKeys_preserves (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx skipped c c.index tr₄ hc_active hJ₄
  let tr₆ := tr₅.append (TREvE (.Received b st.peer msg.ratchetKey msg.counter m))
  let tr₇ := tr₆.append (TREvE (.MessageKey (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx childIdx))
  have hJ₇ : JRkSpine T tr₇ :=
    JRkSpine_append_ev _ (by intro _ _ _ _ _ _ h; cases h)
      (JRkSpine_append_ev _ (by intro _ _ _ _ _ _ h; cases h) hJ₅)
  dsimp only [restAct]
  rw [CompPresTRExp.run_logEvent_bind_snd]
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  rw [CompPresTRExp.run_logEvent_bind_snd]
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact JRkSpine_append_st b hst_spine hJ₇

theorem JRkSpine_preserves_bobStart {T tr : ExecTrace} (hreach : ReachableTrace tr) (hle_tr_T : tr ≤ T)
    (hinv : SpqrInv tr) (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat)
    (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (hJ : JRkSpine T tr) :
    JRkSpine T ((bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr hJ fun sB sS sQ o ikA _ ek ct _ keys _ hspk _ _ _ _ _ _ hbob => ?_
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg; rw [CompTrace.run_bind_assoc_snd]
  refine CompTrace.bind_receiveMessage_at mh.msg tr hJ fun raw _ hraw_ak => ?_
  rcases hparse : parseTrSignalMsg raw with _ | msg; · dsimp only; rw [CompTrace.run_bind_snd, Traceful.run_failure]; exact hJ
  dsimp only; rw [CompTrace.run_bind_assoc_snd]; refine CompTrace.bind_guardP_at _ tr hJ fun _ => ?_
  refine CompInv.CompPresBob.bind_ensureReceiverChain_bobInitSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey tr hJ fun _ => ?_
  let dhs := CompKeyInversion.rnd tr.length 32
  let st := CompInv.CompPresBob.bobRatchetedSt a (DiffieHellman.dhPk sB) ikA keys sS msg.ratchetKey dhs
  let c := CompInv.CompPresBob.bobRatchetedChain keys msg.ratchetKey sS
  let tr₁ := tr.append (RndE 32); have hJ₁ : JRkSpine T tr₁ := JRkSpine_append_other hJ
  rcases hConsume : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩; · dsimp only; rw [Traceful.run_failure]; exact hJ₁
  dsimp only; rcases hSpqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩; · dsimp only; rw [Traceful.run_failure]; exact hJ₁
  dsimp only
  have hkeys_eq : keys = DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm
      (DY.Libsignal.PQXDH.agree ikA sS) (DY.Libsignal.PQXDH.agree ek sB)
      (DY.Libsignal.PQXDH.agree ek sS) (o.map (DY.Libsignal.PQXDH.agree ek ·))
      ((DY.Libsignal.PQXDH.errToOption (PQKem.kemDecap sQ ct)).getD (PQKem.kemRejKey sQ ct))) := by
    dsimp only [DY.Libsignal.PQXDH.bobAgreement, Option.pure_def] at hbob
    injection hbob with h; exact h.symm
  let tr₂ := tr₁.append (NetE key); have hJ₂ : JRkSpine T tr₂ := JRkSpine_append_other hJ₁
  rw [CompPresTRExp.run_sendMessage_bind_snd]
  change JRkSpine T (((Network.receiveMessage pqIdx >>= fun pqSalt => DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed >>= fun m => _).run tr₂).2.val)
  refine CompTrace.bind_receiveMessage_at pqIdx tr₂ hJ₂ fun pqSalt _ _ =>
    bind_verifyMacAndDecrypt_eq_at st msg pqSalt seed tr₂ hJ₂ fun m hmac => ?_
  obtain ⟨t_sS, rfl, _, _, _⟩ := hinv.stOK b { kind := .signedPrekey, sk := sS } kh.spk hspk
  obtain ⟨hseed_eq, hc'_eq⟩ := consumeMessageKey_eq_spine hConsume
  let d := msg.counter.toNat - c.index.toNat
  have hrk0 : RkTree T keys.rk := by rw [hkeys_eq]; exact RkTree.pqxdh _ _ _ _ _
  have hspk_T : CompTrace.PQXDHStoredAt T b { kind := .signedPrekey, sk := randTerm t_sS 32 } kh.spk :=
    CompTrace.pqxdhStoredAt_mono hle_tr_T hspk
  have hpair0 : RkDhsPair T keys.rk t_sS :=
    .inr (.inr ⟨⟨_, _, _, _, _, congrArg HandshakeKeys.rk hkeys_eq⟩, b, kh.spk, hspk_T⟩)
  have hseed_create : seed = KdfExtract.kdfExtract
      (chainKeyAt (createChain keys.rk c.ratchetKey (randTerm t_sS 32)).2 d) (litByte 0x01) := hseed_eq
  have hdisj := acceptedChain_honest_or_prkAK hreach hle_tr_T hJ hraw_ak hparse hmac hseed_create
  have hc_active : ActiveRecvChainSpine T c := .inl ⟨keys.rk, t_sS, 0, hrk0, hpair0, rfl, hdisj⟩
  have hc_spine : RecvChainSpine T c := activeRecvChainSpine_imp_recvChainSpine hc_active
  have hc'_spine : RecvChainSpine T c' := by
    rw [hc'_eq]
    exact activeRecvChainSpine_imp_recvChainSpine (activeRecvChainSpine_advance hc_active (d + 1) (msg.counter + 1))
  have hst_base : StSpineInv T st :=
    ⟨⟨(createChain keys.rk msg.ratchetKey (randTerm t_sS 32)).1, msg.ratchetKey, 0, rfl, rfl⟩,
     fun c0 hc0 => by
       dsimp [st, CompInv.CompPresBob.bobRatchetedSt] at hc0
       rw [List.mem_singleton] at hc0; subst hc0; exact hc_spine⟩
  have hst_final : StSpineInv T { st with recv := setRecvChain st.recv c', spqr := spqr' } :=
    stSpineInv_setRecvChain hst_base hc'_spine
  cases o with
  | none =>
    dsimp only [Option.map]
    exact JRkSpine_bobStart_commit hJ₂ b a sB (randTerm t_sS 32) sQ none ikA ek ct keys msg dhs spqr' seed pqSalt m c' hc_active hst_final
  | some oSk =>
    dsimp only [Option.map]; rw [CompTrace.run_bind_snd]; unfold DY.Libsignal.PQXDH.guardTrace; rw [Traceful.run_mk]; dsimp only
    by_cases hused : (!opkUsedB tr₂ b (DiffieHellman.dhPk oSk)) = true
    · rw [ite_eq_left_iff.mpr fun h => absurd hused h]; dsimp only; rw [CompPresTRExp.run_logEvent_bind_snd]
      exact JRkSpine_bobStart_commit (JRkSpine_append_other hJ₂) b a sB (randTerm t_sS 32) sQ (some oSk) ikA ek ct keys msg dhs spqr' seed pqSalt m c' hc_active hst_final
    · rw [ite_eq_right_iff.mpr fun h => absurd h hused]; dsimp only; exact hJ₂

theorem jRkSpine_reachable {T tr : ExecTrace} (hreach : ReachableTrace tr) (hle : tr ≤ T) :
    JRkSpine T tr := by
  induction hreach with
  | Base => exact JRkSpine_nil T
  | @Step tr_prev input hPre hReachPre ih =>
    have hprev_le : tr_prev ≤ T := Trace.le_trans _ _ _ ((reachability.step input).snd.run _).2.property hle
    have hJ : JRkSpine T tr_prev := ih hprev_le
    have hinv : SpqrInv tr_prev := spqrInv_of_reachable _ hReachPre
    have hst_bind : ∀ {S α : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
        (p : Participant) (s : S) (k : Nat → Traceful α) (t : ExecTrace),
        ((PersistentLocalState.storeLocalState p s >>= k).run t).2.val =
          ((k t.length).run (t.append (⟨⟨p, s⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S)))).2.val :=
      fun p s k t => by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
        rw [CompTrace.run_bind_snd, Traceful.run_mk]
    have hst_snd : ∀ {S : Type} [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT S)]
        (p : Participant) (s : S) (t : ExecTrace),
        ((PersistentLocalState.storeLocalState p s).run t).2.val =
          t.append (⟨⟨p, s⟩⟩ : PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState S)) :=
      fun p s t => by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
    have hlog_snd : ∀ {E : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT E)] (ev : E) (t : ExecTrace),
        ((ProtocolEvent.logEvent ev).run t).2.val = t.append (⟨ev⟩ : ProtocolEvent.ExecEntryT E) := fun ev t => by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
      rw [CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
    rcases input with ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k, _⟩, inp⟩
    · change DY.Bytes at inp; change JRkSpine T ((Network.sendMessage inp).run _).2.val
      rw [CompPresTRExp.run_sendMessage_snd]; exact JRkSpine_append_other hJ
    · change Participant at inp; change JRkSpine T ((registerIdentity inp).run _).2.val; unfold registerIdentity
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, hst_snd]
      exact JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other hJ))))
    · rcases inp with ⟨p, skIdx⟩; change JRkSpine T ((registerCorruptIdentity p skIdx).run _).2.val; unfold registerCorruptIdentity
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ =>
        CompTrace.bind_receiveMessage_at skIdx _ hJ fun _ _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, hlog_snd]
      exact JRkSpine_append_other (JRkSpine_append_other hJ)
    · rcases inp with ⟨b, idStateIdx⟩; change JRkSpine T ((genSignedPrekey b idStateIdx).run _).2.val; unfold genSignedPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ hJ fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other hJ)))))
    · rcases inp with ⟨b, idStateIdx⟩; change JRkSpine T ((genPQPrekey b idStateIdx).run _).2.val; unfold genPQPrekey
      refine CompPresPQXDH.bind_getKey_at b idStateIdx .identity _ hJ fun _ _ => ?_
      rw [CompTrace.run_genRand_bind_snd, CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd,
        hst_bind, CompPresTRExp.run_sendMessage_bind_snd, CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other hJ)))))
    · change Participant at inp; change JRkSpine T ((genOneTimePrekey inp).run _).2.val; unfold genOneTimePrekey
      rw [CompTrace.run_genRand_bind_snd, CompPresTRExp.run_logEvent_bind_snd, hst_bind,
        CompPresTRExp.run_sendMessage_bind_snd, Traceful.run_pure]
      exact JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other (JRkSpine_append_other hJ)))
    · rcases inp with ⟨a, b, idStateIdx, regIdxB, bh⟩; exact JRkSpine_preserves_aliceStart a b idStateIdx regIdxB bh hJ
    · rcases inp with ⟨b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx⟩; exact JRkSpine_preserves_bobStart hReachPre hprev_le hinv b a kh regIdxA mh pqIdx spqrMsgIdx hJ
    · rcases inp with ⟨me, stateIdx, coinsLen, pqIdx⟩; exact (PQRkSpineAt.messageEncrypt me stateIdx coinsLen pqIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx⟩; exact (PQRkSpineAt.messageEncryptAbort me stateIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx, msgIdx, pqIdx, spqrMsgIdx⟩; exact (PQRkSpineAt.messageDecrypt hReachPre hprev_le me stateIdx msgIdx pqIdx spqrMsgIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx, msgIdx, skippedKeyEventIdx, pqIdx, spqrMsgIdx⟩; exact (PQRkSpineAt.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx hJ hle).1
    · rcases inp with ⟨me, stateIdx, k⟩; exact (PQRkSpineAt.exposeKey me stateIdx k hJ hle).1
    · rcases inp with ⟨me, stateIdx⟩; exact (PQRkSpineAt.exposeSpqr me stateIdx hJ hle).1
    · exact (PQRkSpineAt.exposeSkipped inp hJ hle).1
    · rcases inp with ⟨p, stateIdx⟩; change JRkSpine T ((compromiseIK p stateIdx).run _).2.val; unfold compromiseIK
      refine CompPresPQXDH.bind_getKey_at p stateIdx .identity _ hJ fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRkSpine_append_other (JRkSpine_append_other hJ)
    · rcases inp with ⟨b, stateIdx⟩; change JRkSpine T ((compromiseSPK b stateIdx).run _).2.val; unfold compromiseSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .signedPrekey _ hJ fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRkSpine_append_other (JRkSpine_append_other hJ)
    · rcases inp with ⟨b, stateIdx⟩; change JRkSpine T ((compromisePQSPK b stateIdx).run _).2.val; unfold compromisePQSPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .pqPrekey _ hJ fun _ _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRkSpine_append_other (JRkSpine_append_other hJ)
    · rcases inp with ⟨b, stateIdx⟩; change JRkSpine T ((compromiseOPK b stateIdx).run _).2.val; unfold compromiseOPK
      refine CompPresPQXDH.bind_getKey_at b stateIdx .oneTimePrekey _ hJ fun _ _ => ?_
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ => ?_
      rw [CompPresTRExp.run_logEvent_bind_snd, CompPresTRExp.run_sendMessage_snd]
      exact JRkSpine_append_other (JRkSpine_append_other hJ)
    · change JRkSpine T ((DY.Libsignal.PQXDH.breakDH).run _).2.val; unfold DY.Libsignal.PQXDH.breakDH
      rw [hlog_snd]; exact JRkSpine_append_other hJ
    · change JRkSpine T ((DY.Libsignal.PQXDH.breakKEM).run _).2.val; unfold DY.Libsignal.PQXDH.breakKEM
      rw [hlog_snd]; exact JRkSpine_append_other hJ
    · change Nat at inp; change JRkSpine T ((invertDH inp).run _).2.val; unfold invertDH
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ =>
        CompTrace.bind_receiveMessage_at inp tr_prev hJ fun pk _ _ => ?_
      rcases DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
      · dsimp only; rw [Traceful.run_failure]; exact hJ
      · dsimp only; rw [CompPresTRExp.run_sendMessage_snd]; exact JRkSpine_append_other hJ
    · change Nat at inp; change JRkSpine T ((invertKEM inp).run _).2.val; unfold invertKEM
      refine CompPresPQXDH.bind_guardOnTrace_at _ _ hJ fun _ =>
        CompTrace.bind_receiveMessage_at inp tr_prev hJ fun pk _ _ => ?_
      rcases PQKem.invertKemPublicKey pk with _ | sk
      · rw [CompTrace.run_bind_snd]; erw [Traceful.run_mk]; exact hJ
      · rw [CompTrace.run_bind_snd]; erw [Traceful.run_mk]; dsimp [MonadLift.monadLift]
        rw [CompPresTRExp.run_sendMessage_snd]; exact JRkSpine_append_other hJ
    · omega

/-- Every `TRState` stored on a reachable trace `T` satisfies `StRkSpine T st`. -/
theorem stRkSpine_of_stored {T : ExecTrace} (hT : ReachableTrace T)
    {p : Participant} {st : TRState} {i : Nat} (hst : TRStateStoredAt p st i T) :
    StRkSpine T st :=
  ⟨((JRk_reachable hT (Trace.le_refl T)).2.1 p st i hst).1,
   ((jRkSpine_reachable hT (Trace.le_refl T)).1 p st i hst).2⟩

theorem stCksIsCreateChain_of_stored {T : ExecTrace} (hT : ReachableTrace T)
    {p : Participant} {st : TRState} {i : Nat} (hst : TRStateStoredAt p st i T) :
    StCksIsCreateChain st :=
  ((jRkSpine_reachable hT (Trace.le_refl T)).1 p st i hst).1

end Symbolic.Swarm.CREF.TR.G1

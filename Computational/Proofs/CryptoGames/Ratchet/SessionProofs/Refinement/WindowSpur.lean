/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.GhostStep
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.SpuriousBounds
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Collision
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins

/-!
# Spurious-step and zero-point rejection lemmas

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Bounds spurious MAC-verification events on new receiver chains and proves that `Params.receive`
rejects evicted honest ratchet keys, zero-point ratchet keys (DEV-LS11), malformed wires, and
mismatched addresses.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

/-- Boolean predicate for whether a candidate eager sending key `x` triggers a spurious MAC match
on wire `w` with salt `salt` and evicted honest ratchet secret `y`. -/
def spurBadSingle (P : Params PQ PQC) (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt)
    (Q : Party) (rk : Ratchet.RootKey) (curCkaMsg : Pt)
    (w : List (BitVec 8)) (salt : Salt) (y : BitVec 256) (x : BitVec 256) : Bool :=
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  if w.length < 2 ^ 32 then
    match (signalWireCodec P.codec).parse ser with
    | none => false
    | some (h, _) =>
      let p₁ := (evictedKeySpuriousStepPrg P.C.F encPt Dh rk curCkaMsg y).gen x
      let ck := (List.range h.counter.toNat).foldl
        (fun k _ => (hmacPRF P.C.F).tag k Ratchet.chainKeySeed) p₁.2
      let mk := deriveMessageKeys P.C.F salt (Ratchet.chainHmac P.C.F ck Ratchet.messageKeySeed)
      (hmacScheme P.C.F).tag mk.2 ((macIds (idOfP P Q.other) (idOfP P Q)).toList ++ ser) == tag
  else false

theorem spurBadSingle_effSalt (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (Q : Party) (rk : Ratchet.RootKey) (curCkaMsg : Pt)
    (w : List (BitVec 8)) (salt : Salt) (y x : BitVec 256) :
    spurBadSingle P encPt Dh Q rk curCkaMsg w (some (effectiveHkdfSalt32 salt)) y x =
      spurBadSingle P encPt Dh Q rk curCkaMsg w salt y x := by
  unfold spurBadSingle
  simp only [← msgKeys_effSalt]

def spurBadList (P : Params PQ PQC) (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt)
    (Q : Party) (rk : Ratchet.RootKey) (curCkaMsg : Pt)
    (L : List (List (BitVec 8) × Salt × BitVec 256)) (x : BitVec 256) : Bool :=
  L.any fun ⟨w, salt, y⟩ => spurBadSingle P encPt Dh Q rk curCkaMsg w salt y x

private theorem measure_setOf_bool_eq_bind (f : BitVec 256 → Bool) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | f x = true} =
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun x => pure (f x)] {true} := by
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply (MeasurableSet.singleton true) Measurable.of_discrete.aemeasurable]
  calc 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | f x = true}
      = ∫⁻ x, Set.indicator {x | f x = true} 1 x ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] :=
        (lintegral_indicator_one MeasurableSet.of_discrete).symm
    _ = ∫⁻ x, 𝒟[pure (f x)] {true} ∂𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
        refine lintegral_congr fun x => ?_
        cases h : f x <;> simp [h]

theorem spurBadSingle_prob_le (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (Q : Party) (rk : Ratchet.RootKey) (curCkaMsg : Pt)
    (w : List (BitVec 8)) (salt : Salt) (y : BitVec 256) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      {x | spurBadSingle P encPt Dh Q rk curCkaMsg w salt y x = true} ≤
      spurUnit P.C.F encPt Dh := by
  by_cases hw : w.length < 2 ^ 32
  swap
  · have hw' : ¬ w.length < 4294967296 := hw
    simp [spurBadSingle, hw, hw']
  have hser : (w.take (w.length - 8)).length < 2 ^ 32 :=
    lt_of_le_of_lt (by rw [List.length_take]; exact Nat.min_le_right _ _) hw
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none =>
    simp [spurBadSingle, hw, hparse]
  | some hb =>
    rcases hb with ⟨h, body⟩
    rw [measure_setOf_bool_eq_bind]
    have hexp :
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
          fun x => pure (spurBadSingle P encPt Dh Q rk curCkaMsg w salt y x)) =
        (evictedKeySpuriousStepPrg P.C.F encPt Dh rk curCkaMsg y).prgRealExperiment
          (wireMacVerifiesTest P.C.F h.counter.toNat salt (macIds (idOfP P Q.other) (idOfP P Q))
            (w.take (w.length - 8)) (bytesToWord64LE (w.drop (w.length - 8)))) := by
      unfold spurBadSingle PRGScheme.prgRealExperiment wireMacVerifiesTest
      simp only [hw, ↓reduceIte, hparse]
    rw [hexp]
    exact spurSingle_le_spurUnit P.C.F encPt Dh rk curCkaMsg y h.counter.toNat h.counter.isLt salt
      (macIds (idOfP P Q.other) (idOfP P Q)) (w.take (w.length - 8)) hser
      (bytesToWord64LE (w.drop (w.length - 8)))

theorem spurBadList_prob_le (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (Q : Party) (rk : Ratchet.RootKey) (curCkaMsg : Pt)
    (L : List (List (BitVec 8) × Salt × BitVec 256)) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      {x | spurBadList P encPt Dh Q rk curCkaMsg L x = true} ≤
      (L.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh := by
  induction L with
  | nil =>
    simp [spurBadList]
  | cons a L ih =>
    rcases a with ⟨w, salt, y⟩
    have hsub :
        {x : BitVec 256 | spurBadList P encPt Dh Q rk curCkaMsg ((w, salt, y) :: L) x = true} ⊆
          {x : BitVec 256 | spurBadSingle P encPt Dh Q rk curCkaMsg w salt y x = true} ∪
            {x : BitVec 256 | spurBadList P encPt Dh Q rk curCkaMsg L x = true} := by
      intro x hx
      simpa [spurBadList, Bool.or_eq_true] using hx
    calc 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
          {x | spurBadList P encPt Dh Q rk curCkaMsg ((w, salt, y) :: L) x = true}
        ≤ 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
            ({x | spurBadSingle P encPt Dh Q rk curCkaMsg w salt y x = true} ∪
              {x | spurBadList P encPt Dh Q rk curCkaMsg L x = true}) :=
          measure_mono hsub
      _ ≤ 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
            {x | spurBadSingle P encPt Dh Q rk curCkaMsg w salt y x = true} +
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
            {x | spurBadList P encPt Dh Q rk curCkaMsg L x = true} :=
          measure_union_le _ _
      _ ≤ spurUnit P.C.F encPt Dh + (L.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh :=
          add_le_add (spurBadSingle_prob_le P encPt Dh Q rk curCkaMsg w salt y) ih
      _ = (((w, salt, y) :: L).length : ℝ≥0∞) * spurUnit P.C.F encPt Dh := by
          simp [List.length_cons, add_mul, one_mul, add_comm]

theorem badCoin_prob_le (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (δ : ℝ≥0∞)
    (hδ : ∀ R : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = R} ≤ δ)
    (Q : Party) (rk : Ratchet.RootKey) (curCkaMsg : Pt)
    (L : List (List (BitVec 8) × Salt × BitVec 256)) (pts : List Pt) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      {x | (spurBadList P encPt Dh Q rk curCkaMsg L x || decide (Dh.dh x Dh.base ∈ pts)) = true} ≤
      (L.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh + (pts.length : ℝ≥0∞) * δ := by
  have hsub :
      {x : BitVec 256 | (spurBadList P encPt Dh Q rk curCkaMsg L x || decide (Dh.dh x Dh.base ∈ pts)) = true} ⊆
        {x : BitVec 256 | spurBadList P encPt Dh Q rk curCkaMsg L x = true} ∪
          {x : BitVec 256 | decide (Dh.dh x Dh.base ∈ pts) = true} := by
    intro x hx
    simpa [Bool.or_eq_true] using hx
  have hpts :
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
        {x | decide (Dh.dh x Dh.base ∈ pts) = true} ≤ (pts.length : ℝ≥0∞) * δ := by
    rw [measure_setOf_bool_eq_bind]
    exact dh_mem_list_prob_le Dh δ hδ pts
  calc 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
        {x | (spurBadList P encPt Dh Q rk curCkaMsg L x || decide (Dh.dh x Dh.base ∈ pts)) = true}
      ≤ 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
          ({x | spurBadList P encPt Dh Q rk curCkaMsg L x = true} ∪
            {x | decide (Dh.dh x Dh.base ∈ pts) = true}) :=
        measure_mono hsub
    _ ≤ 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
          {x | spurBadList P encPt Dh Q rk curCkaMsg L x = true} +
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
          {x | decide (Dh.dh x Dh.base ∈ pts) = true} :=
        measure_union_le _ _
    _ ≤ (L.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh + (pts.length : ℝ≥0∞) * δ :=
        add_le_add (spurBadList_prob_le P encPt Dh Q rk curCkaMsg L) hpts

private theorem exec_advanceChain_foldl (F : ShaCompress) (s : RatchetState) (ci : ℕ)
    (their : PublicKey) (c₀ : Option LibsignalSession.ChainKey) (counter : BitVec 32)
    (hfind : s.findReceiverChainIndex their = some ci) (k : ℕ) :
    ∀ (p : ℕ) (w : BitVec 256) (mks : List MessageKeyGenerator),
      p + k = counter.toNat →
      ∃ mks',
        Mut.exec (RatchetState.advanceChain F their counter k ⟨w, BitVec.ofNat 32 p⟩)
          { s with receiverChains := s.receiverChains.set ci ⟨their, c₀, mks⟩ } =
        (.ok ⟨(List.range k).foldl (fun key _ => (hmacPRF F).tag key Ratchet.chainKeySeed) w, counter⟩,
          { s with receiverChains := s.receiverChains.set ci ⟨their, c₀, mks'⟩ }) := by
  rcases getElem?_of_findIdx_some s.receiverChains their ci hfind with ⟨c_init, hc_init, _⟩
  have hci_lt : ci < s.receiverChains.length := (List.getElem?_eq_some_iff.1 hc_init).1
  induction k with
  | zero =>
    intro p w mks hp
    have hp_eq : p = counter.toNat := by omega
    have hctr : BitVec.ofNat 32 p = counter := by simp [hp_eq]
    exact ⟨mks, by simp [RatchetState.advanceChain, hctr, Mut.exec_pure]⟩
  | succ k ih =>
    intro p w mks hp
    have hctr_lt : counter.toNat < 2 ^ 32 := counter.isLt
    have hp_lt_max : p < 2 ^ 32 - 1 := by omega
    have hbv_lt : (BitVec.ofNat 32 p < counter) = true := by
      simp [BitVec.lt_def, BitVec.toNat_ofNat]; omega
    have hfind_set :
        ({ s with receiverChains := s.receiverChains.set ci ⟨their, c₀, mks⟩ } : RatchetState).findReceiverChainIndex their =
          some ci :=
      findIdx_set_same_key s.receiverChains their ci hfind _ rfl
    have hget_set :
        ({ s with receiverChains := s.receiverChains.set ci ⟨their, c₀, mks⟩ } : RatchetState).receiverChains[ci]? =
          some ⟨their, c₀, mks⟩ := by
      simp [List.getElem?_set_self hci_lt]
    set key_p := ChainKey.messageKeys F ⟨w, BitVec.ofNat 32 p⟩
    set mks₁ := if maxMessageKeys < (key_p :: mks).length then (key_p :: mks).dropLast else key_p :: mks
    have hstore :
        Mut.exec (RatchetState.storeSkippedKey their key_p)
          { s with receiverChains := s.receiverChains.set ci ⟨their, c₀, mks⟩ } =
        (.ok (), { s with receiverChains := s.receiverChains.set ci ⟨their, c₀, mks₁⟩ }) := by
      unfold RatchetState.storeSkippedKey
      simp [Mut.exec_bind, Mut.exec_get, hfind_set, hget_set, Mut.exec_set, List.set_set, mks₁]
    have hnext := nextChainKey_of_lt F w hp_lt_max
    rcases ih (p + 1) ((hmacPRF F).tag w Ratchet.chainKeySeed) mks₁ (by omega) with ⟨mks', hih⟩
    refine ⟨mks', ?_⟩
    unfold RatchetState.advanceChain
    simp only [hbv_lt, ↓reduceIte, Mut.exec_bind, hstore, key_p, hnext, Mut.exec_liftE_ok]
    rw [hih, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]

/-- When `spurBadSingle ... = false`, `P.receive g_in w rc` on a wire `w` whose ratchet key
`h.senderRatchetKey = encT (Dh.dh y Dh.base)` is not in `g_in.session.receiverChains` returns
`none` for all `rc`. -/
theorem receive_evicted_honest_eq_none (P : Params PQ PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (Q : Party) (g_in : GhostState PQ)
    (hparty : g_in.party = Q)
    (hver : g_in.session.sessionVersion = BitVec.ofNat 32 currentVersion.toNat)
    (hloc : g_in.session.localIdentity = idOfP P Q)
    (hrem : g_in.session.remoteIdentity = some (idOfP P Q.other))
    (rk : Ratchet.RootKey) (curCkaMsg : Pt) (x : BitVec 256)
    (ck_prev : BitVec 256) (idx_prev : BitVec 32)
    (hrk : g_in.session.rootKey = (rootKdf P.C.F rk (encPt (Dh.dh x curCkaMsg))).1)
    (hsc : g_in.session.senderChain = some ⟨KeyPair.generate P.C x, ⟨ck_prev, idx_prev⟩⟩)
    (w : List (BitVec 8)) (hw_len : ¬ w.length < 9) (hw32 : w.length < 2 ^ 32)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv g_in.session.pqRatchetState h.pqRatchet = .ok (pq', salt))
    (hfind_none : g_in.session.receiverChains.findIdx?
      (fun c => c.senderRatchetKey == h.senderRatchetKey) = none)
    (y : BitVec 256) (hy_ne0 : Dh.dh y Dh.base ≠ 0)
    (hkey : encT (Dh.dh y Dh.base) = h.senderRatchetKey)
    (hnot_spur : spurBadSingle P encPt Dh Q rk curCkaMsg w salt y x = false)
    (rc : BitVec 256) :
    P.receive g_in w rc = none := by
  classical
  have _ : True := by
    have _ := hver; have _ := haddrs; trivial
  have htry : SignalMessage.tryFrom P.codec w =
      .ok ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩ :=
    tryFrom_of_parse P.codec w h body hw_len hparse
  set msg : SignalMessage :=
    ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
      h.pqRatchet, h.addresses, w⟩
  set p₁ := (evictedKeySpuriousStepPrg P.C.F encPt Dh rk curCkaMsg y).gen x
  set p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc (Dh.dh y Dh.base))
  set pn_new : BitVec 32 := if idx_prev = 0 then 0 else idx_prev - 1
  set r_in : RatchetState :=
    { rootKey := g_in.session.rootKey,
      senderChain := g_in.session.senderChain,
      receiverChains := g_in.session.receiverChains,
      previousCounter := g_in.session.previousCounter,
      maxForwardJumps := 25000 }
  have hfind_r_in : r_in.findReceiverChainIndex h.senderRatchetKey = none := hfind_none
  set L₁ := List.drop (g_in.session.receiverChains.length + 1 - 5) g_in.session.receiverChains
  set r_mid : RatchetState :=
    { rootKey := p₂.1,
      senderChain := some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩,
      receiverChains := RatchetState.evictReceiverChains
        (g_in.session.receiverChains ++ [⟨h.senderRatchetKey, some ⟨p₁.2, 0⟩, []⟩]),
      previousCounter := pn_new,
      maxForwardJumps := 25000 }
  have hens : Mut.exec (RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc) r_in =
      (.ok ⟨p₁.2, 0#32⟩, r_mid) := by
    rw [exec_ensureReceiverChain_new P.C r_in h.senderRatchetKey rc hfind_r_in]
    dsimp only [r_in]
    rw [hrk, hsc]
    exact exec_dhRatchetStep_honest P Dh encPt encT hX
      (rootKdf P.C.F rk (encPt (Dh.dh x curCkaMsg))).1 x ck_prev idx_prev
      g_in.session.receiverChains g_in.session.previousCounter
      h.senderRatchetKey (Dh.dh y Dh.base) hy_ne0 hkey rc
  have hmid_rc : r_mid.receiverChains =
      L₁ ++ [⟨h.senderRatchetKey, some ⟨p₁.2, 0⟩, []⟩] :=
    evictReceiverChains_append_singleton g_in.session.receiverChains _
  set ci_new := L₁.length
  have hfind_mid : r_mid.findReceiverChainIndex h.senderRatchetKey = some ci_new := by
    unfold RatchetState.findReceiverChainIndex
    rw [hmid_rc]
    apply findIdx_append_singleton_of_none L₁ _ (fun c => c.senderRatchetKey == h.senderRatchetKey)
    · exact findIdx_drop_none_of_none _ _ _ hfind_r_in
    · simp
  set g_init : GhostChain := ⟨some h.senderRatchetKey, 0, 0, []⟩
  set v_init : RatchetReceiverState (BitVec 256) (BitVec 256) := ⟨p₁.2, 0, []⟩
  have hget_mid : r_mid.receiverChains[ci_new]? =
      some ⟨h.senderRatchetKey,
        some ⟨v_init.chainKey, BitVec.ofNat 32 v_init.lastIndex⟩,
        mkSkippedList g_init.skipped v_init.skippedKeys⟩ := by
    rw [hmid_rc, List.getElem?_append_right (Nat.le_refl L₁.length), Nat.sub_self]
    rfl
  have hupd_mid :
      updChain r_mid ci_new h.senderRatchetKey
        (some ⟨v_init.chainKey, BitVec.ofNat 32 v_init.lastIndex⟩) g_init.skipped v_init.skippedKeys =
        r_mid :=
    updChain_eq_self r_mid ci_new h.senderRatchetKey
      (some ⟨v_init.chainKey, BitVec.ofNat 32 v_init.lastIndex⟩) g_init.skipped v_init.skippedKeys hget_mid
  have hset_mid :
      { r_mid with receiverChains := r_mid.receiverChains.set ci_new ⟨h.senderRatchetKey, some ⟨p₁.2, 0#32⟩, []⟩ } =
        r_mid :=
    hupd_mid
  have hbv_lt : (h.counter < BitVec.ofNat 32 0) = false := by
    simp [BitVec.lt_def, BitVec.toNat_ofNat]
  have hjump : (h.counter - BitVec.ofNat 32 0).toNat = h.counter.toNat := by simp
  by_cases hj_gt : 25000 < h.counter.toNat
  · have hcons :
        Mut.exec (RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ⟨p₁.2, 0#32⟩ h.counter .whisper)
          r_mid = (.error (.invalidMessage .whisper .tooFarInFuture), r_mid) := by
      unfold RatchetState.consumeMessageKey
      have hmax_mid : r_mid.maxForwardJumps = 25000 := rfl
      simp [hbv_lt, hjump, Mut.exec_bind, Mut.exec_get, hmax_mid, hj_gt, Mut.exec_throw]
    have hstep : Mut.exec
        (do
          let ck' ← RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc
          RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck' h.counter .whisper)
        r_in = (.error (.invalidMessage .whisper .tooFarInFuture), r_mid) := by
      simp [Mut.exec_bind, hens, hcons]
    rcases tryDecryptFromRecord_of_stepChain_error P Q msg rc g_in.session hrem
      (.invalidMessage .whisper .tooFarInFuture) r_mid hstep with ⟨e', hdec_err⟩
    unfold Params.receive
    rw [htry, hparty]
    dsimp only
    rw [hdec_err]
  · rcases exec_advanceChain_foldl P.C.F r_mid ci_new h.senderRatchetKey (some ⟨p₁.2, 0#32⟩)
      h.counter hfind_mid h.counter.toNat 0 p₁.2 [] (Nat.zero_add _) with ⟨mks', hadv⟩
    rw [hset_mid] at hadv
    set ck := (List.range h.counter.toNat).foldl
      (fun key _ => (hmacPRF P.C.F).tag key Ratchet.chainKeySeed) p₁.2
    set r_adv : RatchetState :=
      { r_mid with receiverChains := r_mid.receiverChains.set ci_new ⟨h.senderRatchetKey, some ⟨p₁.2, 0#32⟩, mks'⟩ }
    by_cases hi_ge : 2 ^ 32 ≤ h.counter.toNat + 1
    · rcases nextChainKey_counter_of_ge P.C.F ck h.counter hi_ge with ⟨e, hnext_err⟩
      have hcons :
          Mut.exec (RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ⟨p₁.2, 0#32⟩ h.counter .whisper)
            r_mid = (.error e, r_adv) := by
        unfold RatchetState.consumeMessageKey
        have hmax_mid : r_mid.maxForwardJumps = 25000 := rfl
        simp [hbv_lt, hjump, Mut.exec_bind, Mut.exec_get, hmax_mid, hj_gt, hadv, hnext_err,
          Mut.exec_liftE_error, r_adv]
      have hstep : Mut.exec
          (do
            let ck' ← RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc
            RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck' h.counter .whisper)
          r_in = (.error e, r_adv) := by
        simp [Mut.exec_bind, hens, hcons]
      rcases tryDecryptFromRecord_of_stepChain_error P Q msg rc g_in.session hrem e r_adv hstep with
        ⟨e', hdec_err⟩
      unfold Params.receive
      rw [htry, hparty]
      dsimp only
      rw [hdec_err]
    · have hi_lt : h.counter.toNat + 1 < 2 ^ 32 := by omega
      have hnext := nextChainKey_counter_of_lt P.C.F ck h.counter hi_lt
      set nextCk : LibsignalSession.ChainKey :=
        ⟨((lChainPRG P.C.F h.counter.toNat).gen ck).1, BitVec.ofNat 32 (h.counter.toNat + 1)⟩
      rcases getElem?_of_findIdx_some r_mid.receiverChains h.senderRatchetKey ci_new hfind_mid with
        ⟨c_init, hc_init, _⟩
      have hci_lt : ci_new < r_mid.receiverChains.length := (List.getElem?_eq_some_iff.1 hc_init).1
      have hfind_adv : r_adv.findReceiverChainIndex h.senderRatchetKey = some ci_new :=
        findIdx_set_same_key r_mid.receiverChains h.senderRatchetKey ci_new hfind_mid _ rfl
      have hget_adv : r_adv.receiverChains[ci_new]? =
          some ⟨h.senderRatchetKey, some ⟨p₁.2, 0#32⟩, mks'⟩ := by
        simp [r_adv, List.getElem?_set_self hci_lt]
      set r_out : RatchetState :=
        { r_mid with receiverChains := r_mid.receiverChains.set ci_new ⟨h.senderRatchetKey, some nextCk, mks'⟩ }
      have hset : Mut.exec (RatchetState.setReceiverChainKey h.senderRatchetKey nextCk) r_adv =
          (.ok (), r_out) := by
        unfold RatchetState.setReceiverChainKey
        simp [Mut.exec_bind, Mut.exec_get, hfind_adv, hget_adv, Mut.exec_set, r_adv, r_out, List.set_set]
      have hcons :
          Mut.exec (RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ⟨p₁.2, 0#32⟩ h.counter .whisper)
            r_mid = (.ok (ChainKey.messageKeys P.C.F ⟨ck, h.counter⟩), r_out) := by
        unfold RatchetState.consumeMessageKey
        have hmax_mid : r_mid.maxForwardJumps = 25000 := rfl
        simp only [hbv_lt, Bool.false_eq_true, ↓reduceIte, hjump, Mut.exec_bind,
          Mut.exec_get, hmax_mid, hj_gt, hadv, hnext, Mut.exec_liftE_ok, hset, Mut.exec_pure]
      have hmac_false :
          SignalMessage.verifyMac P.C.F msg (idOfP P Q.other) (idOfP P Q)
            ((ChainKey.messageKeys P.C.F ⟨ck, h.counter⟩).generateKeys P.C.F salt).macKey = false := by
        have hdrop_len : (w.drop (w.length - 8)).length = 8 := by
          simp [List.length_drop]; omega
        unfold SignalMessage.verifyMac
        dsimp only [msg]
        have hmac_len : macLength = 8 := rfl
        rw [hmac_len, computeMac_beq_eq_hmacScheme_beq P.C.F (idOfP P Q.other) (idOfP P Q) _
          (w.take (w.length - 8)) (w.drop (w.length - 8)) hdrop_len]
        unfold spurBadSingle at hnot_spur
        simp only [hw32, ↓reduceIte, hparse] at hnot_spur
        exact hnot_spur
      have hmac_addrs_false :
          SignalMessage.verifyMacWithAddresses P.C.F msg (P.expectedAddrs Q)
            (idOfP P Q.other) g_in.session.localIdentity
            ((ChainKey.messageKeys P.C.F ⟨ck, h.counter⟩).generateKeys P.C.F salt).macKey = false := by
        unfold SignalMessage.verifyMacWithAddresses
        rw [hloc, hmac_false, Bool.false_and]
      unfold Params.receive
      rw [htry, hparty]
      dsimp only
      unfold SessionState.tryDecryptFromRecord
      by_cases hver_chk : g_in.session.version.toNat ≠ msg.messageVersion.toNat
      · rw [ite_eq_left hver_chk]
      · rw [ite_eq_right hver_chk]
        have hmax : maxForwardJumps = 25000 := rfl
        have h_their : msg.senderRatchetKey = h.senderRatchetKey := rfl
        have h_ctr : msg.counter = h.counter := rfl
        have h_pqr : msg.pqRatchet = h.pqRatchet := rfl
        unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
          SessionState.takeRatchetState SessionState.takePqRatchetState
          TripleRatchet.decrypt TripleRatchet.onRatchet zoom
        cases hpan : P.spqr.recvPanics g_in.session.pqRatchetState h.pqRatchet <;>
          simp [h_their, h_ctr, h_pqr, Mut.exec_bind, Mut.exec_modifyGet, Mut.exec_get,
            Mut.exec_set,
          hrem, Mut.exec_pure, hmax, r_in, hens, hcons, Mut.exec_liftE_ok,
          hspqr, hmac_addrs_false, Mut.exec_throw, Mut.exec_liftE_error, hpan]

/-- When `h.senderRatchetKey = encT 0` is not in `g_in.session.receiverChains` and
`∀ x, Dh.dh x 0 = 0`, `dhRatchetStep` fails on the zero DH output and `P.receive g_in w rc = none`
for all `rc`. -/
theorem receive_eq_none_of_encT_zero (P : Params PQ PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (Q : Party) (g_in : GhostState PQ)
    (hparty : g_in.party = Q)
    (hver : g_in.session.sessionVersion = BitVec.ofNat 32 currentVersion.toNat)
    (hloc : g_in.session.localIdentity = idOfP P Q)
    (hrem : g_in.session.remoteIdentity = some (idOfP P Q.other))
    (x : BitVec 256) (ck_prev : BitVec 256) (idx_prev : BitVec 32)
    (hsc : g_in.session.senderChain = some ⟨KeyPair.generate P.C x, ⟨ck_prev, idx_prev⟩⟩)
    (w : List (BitVec 8)) (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv g_in.session.pqRatchetState h.pqRatchet = .ok (pq', salt))
    (hfind_none : g_in.session.receiverChains.findIdx?
      (fun c => c.senderRatchetKey == h.senderRatchetKey) = none)
    (hkey : encT 0 = h.senderRatchetKey)
    (rc : BitVec 256) :
    P.receive g_in w rc = none := by
  classical
  have _ : True := by
    have _ := hver; have _ := hloc; have _ := haddrs; have _ := hspqr; trivial
  have htry : SignalMessage.tryFrom P.codec w =
      .ok ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩ :=
    tryFrom_of_parse P.codec w h body hw_len hparse
  set msg : SignalMessage :=
    ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
      h.pqRatchet, h.addresses, w⟩
  set r_in : RatchetState :=
    { rootKey := g_in.session.rootKey,
      senderChain := g_in.session.senderChain,
      receiverChains := g_in.session.receiverChains,
      previousCounter := g_in.session.previousCounter,
      maxForwardJumps := 25000 }
  have hM := libX25519Rel_model hX
  have hpub : h.senderRatchetKey.bytes.toList = encPt 0 := by
    rw [← hkey]
    exact encT_bytes_toList hX 0
  have hrc_zero := rootCreateChain_generate_zero P.C hM hz g_in.session.rootKey x hpub
  have hens :
      Mut.exec (RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc) r_in =
        (.error .invalidKeyAgreement, { r_in with rootKey := 0 }) := by
    rw [exec_ensureReceiverChain_new P.C r_in h.senderRatchetKey rc hfind_none]
    unfold RatchetState.dhRatchetStep RatchetState.takeRootKey
    simp [r_in, hsc, Mut.exec_bind, Mut.exec_get, Mut.exec_modifyGet, hrc_zero,
      Mut.exec_liftE_error]
  have hstep :
      Mut.exec
        (do
          let ck' ← RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc
          RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck' h.counter .whisper)
        r_in = (.error .invalidKeyAgreement, { r_in with rootKey := 0 }) := by
    rw [Mut.exec_bind, hens]
  rcases tryDecryptFromRecord_of_stepChain_error P Q msg rc g_in.session hrem
    .invalidKeyAgreement { r_in with rootKey := 0 } hstep with ⟨e', hdec_err⟩
  unfold Params.receive
  rw [htry, hparty]
  dsimp only
  rw [hdec_err]

theorem receive_eq_none_of_parse_fail (P : Params PQ PQC)
    (g_in : GhostState PQ) (w : List (BitVec 8))
    (hfail : w.length < 9 ∨ (signalWireCodec P.codec).parse (w.take (w.length - 8)) = none)
    (rc : BitVec 256) :
    P.receive g_in w rc = none := by
  rcases tryFrom_isError_of_parse_none P.codec w hfail with ⟨e, herr⟩
  simp [Params.receive, herr]

theorem receive_eq_none_of_addrsOk_false (P : Params PQ PQC)
    (Q : Party) (g_in : GhostState PQ) (hparty : g_in.party = Q)
    (w : List (BitVec 8)) (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = false)
    (rc : BitVec 256) :
    P.receive g_in w rc = none := by
  have htry : SignalMessage.tryFrom P.codec w =
      .ok ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩ :=
    tryFrom_of_parse P.codec w h body hw_len hparse
  unfold Params.receive
  rw [htry, hparty]
  dsimp only
  unfold SessionState.tryDecryptFromRecord
  by_cases hver : g_in.session.version.toNat ≠ h.messageVersion.toNat
  · rw [ite_eq_left hver]
  · rw [ite_eq_right hver]
    unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
      SessionState.takeRatchetState SessionState.takePqRatchetState
      TripleRatchet.decrypt TripleRatchet.onRatchet zoom
    simp only [Mut.exec_bind, Mut.exec_modifyGet, Mut.exec_get, Mut.exec_set]
    cases g_in.session.remoteIdentity with
    | none => simp [Mut.exec_throw]
    | some remote =>
      dsimp only [Mut.exec_pure]
      rcases h_ens : Mut.exec (RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc)
        { rootKey := g_in.session.rootKey, senderChain := g_in.session.senderChain,
          receiverChains := g_in.session.receiverChains,
          previousCounter := g_in.session.previousCounter,
          maxForwardJumps := maxForwardJumps } with ⟨r_ens, s_ens⟩
      cases r_ens with
      | error e => simp [h_ens, Mut.exec_liftE_error]
      | ok ck =>
        rcases h_con : Mut.exec (RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck h.counter .whisper)
          s_ens with ⟨r_con, s_con⟩
        cases r_con with
        | error e => simp [h_ens, h_con, Mut.exec_liftE_ok, Mut.exec_liftE_error]
        | ok mkGen =>
          cases h_pq : P.spqr.recv g_in.session.pqRatchetState h.pqRatchet with
          | error b =>
            cases b <;> cases hpan : P.spqr.recvPanics g_in.session.pqRatchetState h.pqRatchet <;>
              simp [h_ens, h_con, h_pq, Mut.exec_liftE_ok, Mut.exec_throw, Mut.exec_liftE_error,
                hpan]
          | ok pq_salt =>
            rcases pq_salt with ⟨pq', salt⟩
            cases hpan : P.spqr.recvPanics g_in.session.pqRatchetState h.pqRatchet <;>
              simp [h_ens, h_con, h_pq, SignalMessage.verifyMacWithAddresses, haddrs,
              Mut.exec_liftE_ok, Mut.exec_pure, Mut.exec_throw, Mut.exec_liftE_error, hpan]

theorem receive_eq_none_of_spqr_error (P : Params PQ PQC)
    (Q : Party) (g_in : GhostState PQ) (hparty : g_in.party = Q)
    (w : List (BitVec 8)) (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (e_pq : Bool)
    (hspqr : P.spqr.recv g_in.session.pqRatchetState h.pqRatchet = .error e_pq)
    (rc : BitVec 256) :
    P.receive g_in w rc = none := by
  have htry : SignalMessage.tryFrom P.codec w =
      .ok ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩ :=
    tryFrom_of_parse P.codec w h body hw_len hparse
  unfold Params.receive
  rw [htry, hparty]
  dsimp only
  unfold SessionState.tryDecryptFromRecord
  by_cases hver : g_in.session.version.toNat ≠ h.messageVersion.toNat
  · rw [ite_eq_left hver]
  · rw [ite_eq_right hver]
    unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
      SessionState.takeRatchetState SessionState.takePqRatchetState
      TripleRatchet.decrypt TripleRatchet.onRatchet zoom
    simp only [Mut.exec_bind, Mut.exec_modifyGet, Mut.exec_get, Mut.exec_set]
    cases g_in.session.remoteIdentity with
    | none => simp [Mut.exec_throw]
    | some remote =>
      dsimp only [Mut.exec_pure]
      rcases h_ens : Mut.exec (RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc)
        { rootKey := g_in.session.rootKey, senderChain := g_in.session.senderChain,
          receiverChains := g_in.session.receiverChains,
          previousCounter := g_in.session.previousCounter,
          maxForwardJumps := maxForwardJumps } with ⟨r_ens, s_ens⟩
      cases r_ens with
      | error e => simp [h_ens, Mut.exec_liftE_error]
      | ok ck =>
        rcases h_con : Mut.exec (RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck h.counter .whisper)
          s_ens with ⟨r_con, s_con⟩
        cases r_con with
        | error e => simp [h_ens, h_con, Mut.exec_liftE_ok, Mut.exec_liftE_error]
        | ok mkGen =>
          cases e_pq <;> cases hpan : P.spqr.recvPanics g_in.session.pqRatchetState h.pqRatchet <;>
            simp [h_ens, h_con, hspqr, Mut.exec_liftE_ok, Mut.exec_throw, Mut.exec_liftE_error,
              hpan]

/-! ## Point-generalized spurious-step predicates -/

def spurBadSinglePt (P : Params PQ PQC) (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt)
    (Q : Party) (rk : Ratchet.RootKey) (curCkaMsg : Pt)
    (w : List (BitVec 8)) (salt : Salt) (T : Pt) (x : BitVec 256) : Bool :=
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  if w.length < 2 ^ 32 then
    match (signalWireCodec P.codec).parse ser with
    | none => false
    | some (h, _) =>
      let p₁ := (pointSpuriousStepPrg P.C.F encPt Dh rk curCkaMsg T).gen x
      let ck := (List.range h.counter.toNat).foldl
        (fun k _ => (hmacPRF P.C.F).tag k Ratchet.chainKeySeed) p₁.2
      let mk := deriveMessageKeys P.C.F salt (Ratchet.chainHmac P.C.F ck Ratchet.messageKeySeed)
      (hmacScheme P.C.F).tag mk.2 ((macIds (idOfP P Q.other) (idOfP P Q)).toList ++ ser) == tag
  else false

theorem spurBadSinglePt_prob_le (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (Q : Party) (rk : Ratchet.RootKey) (curCkaMsg : Pt) (hTcur : curCkaMsg ≠ 0)
    (w : List (BitVec 8)) (salt : Salt) (T : Pt) (hT : T ≠ 0) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      {x | spurBadSinglePt P encPt Dh Q rk curCkaMsg w salt T x = true} ≤
      spurUnitPt P.C.F encPt Dh := by
  by_cases hw : w.length < 2 ^ 32
  swap
  · have hw' : ¬ w.length < 4294967296 := hw
    simp [spurBadSinglePt, hw, hw']
  have hser : (w.take (w.length - 8)).length < 2 ^ 32 :=
    lt_of_le_of_lt (by rw [List.length_take]; exact Nat.min_le_right _ _) hw
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none =>
    simp [spurBadSinglePt, hw, hparse]
  | some hb =>
    rcases hb with ⟨h, body⟩
    rw [measure_setOf_bool_eq_bind]
    have hexp :
        (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
          fun x => pure (spurBadSinglePt P encPt Dh Q rk curCkaMsg w salt T x)) =
        (pointSpuriousStepPrg P.C.F encPt Dh rk curCkaMsg T).prgRealExperiment
          (wireMacVerifiesTest P.C.F h.counter.toNat salt (macIds (idOfP P Q.other) (idOfP P Q))
            (w.take (w.length - 8)) (bytesToWord64LE (w.drop (w.length - 8)))) := by
      unfold spurBadSinglePt PRGScheme.prgRealExperiment wireMacVerifiesTest
      simp only [hw, ↓reduceIte, hparse]
    rw [hexp]
    exact spurSinglePt_le_spurUnitPt P.C.F encPt Dh rk curCkaMsg hTcur T hT h.counter.toNat
      h.counter.isLt salt (macIds (idOfP P Q.other) (idOfP P Q)) (w.take (w.length - 8)) hser
      (bytesToWord64LE (w.drop (w.length - 8)))

theorem receive_newChain_eq_none_of_spurBadSinglePt_false (P : Params PQ PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (hX : X25519RealizesDh P.C Dh encPt encT)
    (Q : Party) (g_in : GhostState PQ)
    (hparty : g_in.party = Q)
    (hver : g_in.session.sessionVersion = BitVec.ofNat 32 currentVersion.toNat)
    (hloc : g_in.session.localIdentity = idOfP P Q)
    (hrem : g_in.session.remoteIdentity = some (idOfP P Q.other))
    (rk : Ratchet.RootKey) (curCkaMsg : Pt) (x : BitVec 256)
    (ck_prev : BitVec 256) (idx_prev : BitVec 32)
    (hrk : g_in.session.rootKey = (rootKdf P.C.F rk (encPt (Dh.dh x curCkaMsg))).1)
    (hsc : g_in.session.senderChain = some ⟨KeyPair.generate P.C x, ⟨ck_prev, idx_prev⟩⟩)
    (w : List (BitVec 8)) (hw_len : ¬ w.length < 9) (hw32 : w.length < 2 ^ 32)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv g_in.session.pqRatchetState h.pqRatchet = .ok (pq', salt))
    (hfind_none : g_in.session.receiverChains.findIdx?
      (fun c => c.senderRatchetKey == h.senderRatchetKey) = none)
    (T : Pt) (hT_ne0 : T ≠ 0)
    (hkey : encT T = h.senderRatchetKey)
    (hnot_spur : spurBadSinglePt P encPt Dh Q rk curCkaMsg w salt T x = false)
    (rc : BitVec 256) :
    P.receive g_in w rc = none := by
  classical
  have _ : True := by
    have _ := hver; have _ := haddrs; trivial
  have htry : SignalMessage.tryFrom P.codec w =
      .ok ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩ :=
    tryFrom_of_parse P.codec w h body hw_len hparse
  set msg : SignalMessage :=
    ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
      h.pqRatchet, h.addresses, w⟩
  set p₁ := (pointSpuriousStepPrg P.C.F encPt Dh rk curCkaMsg T).gen x
  set p₂ := (rootPRNG P.C.F encPt).up p₁.1 (Dh.dh rc T)
  set pn_new : BitVec 32 := if idx_prev = 0 then 0 else idx_prev - 1
  set r_in : RatchetState :=
    { rootKey := g_in.session.rootKey,
      senderChain := g_in.session.senderChain,
      receiverChains := g_in.session.receiverChains,
      previousCounter := g_in.session.previousCounter,
      maxForwardJumps := 25000 }
  have hfind_r_in : r_in.findReceiverChainIndex h.senderRatchetKey = none := hfind_none
  set L₁ := List.drop (g_in.session.receiverChains.length + 1 - 5) g_in.session.receiverChains
  set r_mid : RatchetState :=
    { rootKey := p₂.1,
      senderChain := some ⟨KeyPair.generate P.C rc, ⟨p₂.2, 0⟩⟩,
      receiverChains := RatchetState.evictReceiverChains
        (g_in.session.receiverChains ++ [⟨h.senderRatchetKey, some ⟨p₁.2, 0⟩, []⟩]),
      previousCounter := pn_new,
      maxForwardJumps := 25000 }
  have hens : Mut.exec (RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc) r_in =
      (.ok ⟨p₁.2, 0#32⟩, r_mid) := by
    rw [exec_ensureReceiverChain_new P.C r_in h.senderRatchetKey rc hfind_r_in]
    dsimp only [r_in]
    rw [hrk, hsc]
    exact exec_dhRatchetStep_honest P Dh encPt encT hX
      (rootKdf P.C.F rk (encPt (Dh.dh x curCkaMsg))).1 x ck_prev idx_prev
      g_in.session.receiverChains g_in.session.previousCounter
      h.senderRatchetKey T hT_ne0 hkey rc
  have hmid_rc : r_mid.receiverChains =
      L₁ ++ [⟨h.senderRatchetKey, some ⟨p₁.2, 0⟩, []⟩] :=
    evictReceiverChains_append_singleton g_in.session.receiverChains _
  set ci_new := L₁.length
  have hfind_mid : r_mid.findReceiverChainIndex h.senderRatchetKey = some ci_new := by
    unfold RatchetState.findReceiverChainIndex
    rw [hmid_rc]
    apply findIdx_append_singleton_of_none L₁ _ (fun c => c.senderRatchetKey == h.senderRatchetKey)
    · exact findIdx_drop_none_of_none _ _ _ hfind_r_in
    · simp
  set g_init : GhostChain := ⟨some h.senderRatchetKey, 0, 0, []⟩
  set v_init : RatchetReceiverState (BitVec 256) (BitVec 256) := ⟨p₁.2, 0, []⟩
  have hget_mid : r_mid.receiverChains[ci_new]? =
      some ⟨h.senderRatchetKey,
        some ⟨v_init.chainKey, BitVec.ofNat 32 v_init.lastIndex⟩,
        mkSkippedList g_init.skipped v_init.skippedKeys⟩ := by
    rw [hmid_rc, List.getElem?_append_right (Nat.le_refl L₁.length), Nat.sub_self]
    rfl
  have hupd_mid :
      updChain r_mid ci_new h.senderRatchetKey
        (some ⟨v_init.chainKey, BitVec.ofNat 32 v_init.lastIndex⟩) g_init.skipped v_init.skippedKeys =
        r_mid :=
    updChain_eq_self r_mid ci_new h.senderRatchetKey
      (some ⟨v_init.chainKey, BitVec.ofNat 32 v_init.lastIndex⟩) g_init.skipped v_init.skippedKeys hget_mid
  have hset_mid :
      { r_mid with receiverChains := r_mid.receiverChains.set ci_new ⟨h.senderRatchetKey, some ⟨p₁.2, 0#32⟩, []⟩ } =
        r_mid :=
    hupd_mid
  have hbv_lt : (h.counter < BitVec.ofNat 32 0) = false := by
    simp [BitVec.lt_def, BitVec.toNat_ofNat]
  have hjump : (h.counter - BitVec.ofNat 32 0).toNat = h.counter.toNat := by simp
  by_cases hj_gt : 25000 < h.counter.toNat
  · have hcons :
        Mut.exec (RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ⟨p₁.2, 0#32⟩ h.counter .whisper)
          r_mid = (.error (.invalidMessage .whisper .tooFarInFuture), r_mid) := by
      unfold RatchetState.consumeMessageKey
      have hmax_mid : r_mid.maxForwardJumps = 25000 := rfl
      simp [hbv_lt, hjump, Mut.exec_bind, Mut.exec_get, hmax_mid, hj_gt, Mut.exec_throw]
    have hstep : Mut.exec
        (do
          let ck' ← RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc
          RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck' h.counter .whisper)
        r_in = (.error (.invalidMessage .whisper .tooFarInFuture), r_mid) := by
      simp [Mut.exec_bind, hens, hcons]
    rcases tryDecryptFromRecord_of_stepChain_error P Q msg rc g_in.session hrem
      (.invalidMessage .whisper .tooFarInFuture) r_mid hstep with ⟨e', hdec_err⟩
    unfold Params.receive
    rw [htry, hparty]
    dsimp only
    rw [hdec_err]
  · rcases exec_advanceChain_foldl P.C.F r_mid ci_new h.senderRatchetKey (some ⟨p₁.2, 0#32⟩)
      h.counter hfind_mid h.counter.toNat 0 p₁.2 [] (Nat.zero_add _) with ⟨mks', hadv⟩
    rw [hset_mid] at hadv
    set ck := (List.range h.counter.toNat).foldl
      (fun key _ => (hmacPRF P.C.F).tag key Ratchet.chainKeySeed) p₁.2
    set r_adv : RatchetState :=
      { r_mid with receiverChains := r_mid.receiverChains.set ci_new ⟨h.senderRatchetKey, some ⟨p₁.2, 0#32⟩, mks'⟩ }
    by_cases hi_ge : 2 ^ 32 ≤ h.counter.toNat + 1
    · rcases nextChainKey_counter_of_ge P.C.F ck h.counter hi_ge with ⟨e, hnext_err⟩
      have hcons :
          Mut.exec (RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ⟨p₁.2, 0#32⟩ h.counter .whisper)
            r_mid = (.error e, r_adv) := by
        unfold RatchetState.consumeMessageKey
        have hmax_mid : r_mid.maxForwardJumps = 25000 := rfl
        simp [hbv_lt, hjump, Mut.exec_bind, Mut.exec_get, hmax_mid, hj_gt, hadv, hnext_err,
          Mut.exec_liftE_error, r_adv]
      have hstep : Mut.exec
          (do
            let ck' ← RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc
            RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck' h.counter .whisper)
          r_in = (.error e, r_adv) := by
        simp [Mut.exec_bind, hens, hcons]
      rcases tryDecryptFromRecord_of_stepChain_error P Q msg rc g_in.session hrem e r_adv hstep with
        ⟨e', hdec_err⟩
      unfold Params.receive
      rw [htry, hparty]
      dsimp only
      rw [hdec_err]
    · have hi_lt : h.counter.toNat + 1 < 2 ^ 32 := by omega
      have hnext := nextChainKey_counter_of_lt P.C.F ck h.counter hi_lt
      set nextCk : LibsignalSession.ChainKey :=
        ⟨((lChainPRG P.C.F h.counter.toNat).gen ck).1, BitVec.ofNat 32 (h.counter.toNat + 1)⟩
      rcases getElem?_of_findIdx_some r_mid.receiverChains h.senderRatchetKey ci_new hfind_mid with
        ⟨c_init, hc_init, _⟩
      have hci_lt : ci_new < r_mid.receiverChains.length := (List.getElem?_eq_some_iff.1 hc_init).1
      have hfind_adv : r_adv.findReceiverChainIndex h.senderRatchetKey = some ci_new :=
        findIdx_set_same_key r_mid.receiverChains h.senderRatchetKey ci_new hfind_mid _ rfl
      have hget_adv : r_adv.receiverChains[ci_new]? =
          some ⟨h.senderRatchetKey, some ⟨p₁.2, 0#32⟩, mks'⟩ := by
        simp [r_adv, List.getElem?_set_self hci_lt]
      set r_out : RatchetState :=
        { r_mid with receiverChains := r_mid.receiverChains.set ci_new ⟨h.senderRatchetKey, some nextCk, mks'⟩ }
      have hset : Mut.exec (RatchetState.setReceiverChainKey h.senderRatchetKey nextCk) r_adv =
          (.ok (), r_out) := by
        unfold RatchetState.setReceiverChainKey
        simp [Mut.exec_bind, Mut.exec_get, hfind_adv, hget_adv, Mut.exec_set, r_adv, r_out, List.set_set]
      have hcons :
          Mut.exec (RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ⟨p₁.2, 0#32⟩ h.counter .whisper)
            r_mid = (.ok (ChainKey.messageKeys P.C.F ⟨ck, h.counter⟩), r_out) := by
        unfold RatchetState.consumeMessageKey
        have hmax_mid : r_mid.maxForwardJumps = 25000 := rfl
        simp only [hbv_lt, Bool.false_eq_true, ↓reduceIte, hjump, Mut.exec_bind,
          Mut.exec_get, hmax_mid, hj_gt, hadv, hnext, Mut.exec_liftE_ok, hset, Mut.exec_pure]
      have hmac_false :
          SignalMessage.verifyMac P.C.F msg (idOfP P Q.other) (idOfP P Q)
            ((ChainKey.messageKeys P.C.F ⟨ck, h.counter⟩).generateKeys P.C.F salt).macKey = false := by
        have hdrop_len : (w.drop (w.length - 8)).length = 8 := by
          simp [List.length_drop]; omega
        unfold SignalMessage.verifyMac
        dsimp only [msg]
        have hmac_len : macLength = 8 := rfl
        rw [hmac_len, computeMac_beq_eq_hmacScheme_beq P.C.F (idOfP P Q.other) (idOfP P Q) _
          (w.take (w.length - 8)) (w.drop (w.length - 8)) hdrop_len]
        unfold spurBadSinglePt at hnot_spur
        simp only [hw32, ↓reduceIte, hparse] at hnot_spur
        exact hnot_spur
      have hmac_addrs_false :
          SignalMessage.verifyMacWithAddresses P.C.F msg (P.expectedAddrs Q)
            (idOfP P Q.other) g_in.session.localIdentity
            ((ChainKey.messageKeys P.C.F ⟨ck, h.counter⟩).generateKeys P.C.F salt).macKey = false := by
        unfold SignalMessage.verifyMacWithAddresses
        rw [hloc, hmac_false, Bool.false_and]
      unfold Params.receive
      rw [htry, hparty]
      dsimp only
      unfold SessionState.tryDecryptFromRecord
      by_cases hver_chk : g_in.session.version.toNat ≠ msg.messageVersion.toNat
      · rw [ite_eq_left hver_chk]
      · rw [ite_eq_right hver_chk]
        have hmax : maxForwardJumps = 25000 := rfl
        have h_their : msg.senderRatchetKey = h.senderRatchetKey := rfl
        have h_ctr : msg.counter = h.counter := rfl
        have h_pqr : msg.pqRatchet = h.pqRatchet := rfl
        unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
          SessionState.takeRatchetState SessionState.takePqRatchetState
          TripleRatchet.decrypt TripleRatchet.onRatchet zoom
        cases hpan : P.spqr.recvPanics g_in.session.pqRatchetState h.pqRatchet <;>
          simp [h_their, h_ctr, h_pqr, Mut.exec_bind, Mut.exec_modifyGet, Mut.exec_get,
            Mut.exec_set,
          hrem, Mut.exec_pure, hmax, r_in, hens, hcons, Mut.exec_liftE_ok,
          hspqr, hmac_addrs_false, Mut.exec_throw, Mut.exec_liftE_error, hpan]

end CryptoGames.LibsignalSM.Proofs.Refinement


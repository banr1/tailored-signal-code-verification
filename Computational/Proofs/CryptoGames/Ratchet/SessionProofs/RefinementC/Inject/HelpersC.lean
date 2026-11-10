/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Inject

/-!
# Inject step: shared C helpers

Shared `SimInvC` and `SimInvCX` lemmas for the `RefinementC` inject subcases (`KnownChain`, `NewChainUnamb`, `AmbInWinFalse`, `AmbFindSome`), adapting the weak-refinement inject helpers without salt binding.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-- An honest entry's header fields match those of the wire, and the entry equals the wire's raw record at its own salt `c.2.2.2`. -/
theorem honestEntryInvC_eq_raw (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (epExp : ℕ → BitVec 256)
    {w : List (BitVec 8)} {c : Fig8C Pt}
    (hinv : HonestEntryInvC P Inv Dh encT epExp (w, c))
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body)) :
    h.messageVersion = currentVersion ∧
    h.senderRatchetKey = encT (Dh.dh (epExp c.1.1) Dh.base) ∧
    h.counter.toNat + 1 = c.2.1 ∧
    c = ((c.1.1, some (Dh.dh (epExp c.1.1) Dh.base)),
      (h.counter.toNat + 1,
        ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), c.2.2.2))) := by
  rcases hinv with ⟨hw, hw_len, ht_ge1, hraw, hi1, hi32, hT, h₀, body₀, hparse₀, hver, hsrk, hctr, haddrs⟩
  have hhb : (h, body) = (h₀, body₀) := Option.some.inj (hparse.symm.trans hparse₀)
  rcases Prod.mk.inj hhb with ⟨rfl, rfl⟩
  refine ⟨hver, hsrk, hctr, ?_⟩
  rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
  dsimp only at hT hctr hraw ⊢
  rw [hT, ← hctr, hraw]

theorem mkC_eq_raw_of_honest_epochC (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT)
    (epExp : ℕ → BitVec 256) (s : SimState PQ Pt ℓ) (Q : Party)
    (w : List (BitVec 8)) (h : SignalHeader) (body : List (BitVec 8))
    (pq_st pq' : PQ) (salt : Salt) (t : ℕ) {T : Pt}
    (hdecT : decT h.senderRatchetKey = some T)
    (hencT : encT T = h.senderRatchetKey)
    (hhon : ∀ wc ∈ s.honest, HonestEntryInvC P Inv Dh encT epExp wc)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hspqr : P.spqr.recv pq_st h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics pq_st h.pqRatchet = false)
    (ht : ∀ wc ∈ s.honest, wc.1 = w → Party.senderOf wc.2.1.1 = Q.other → wc.2.1.1 = t)
    (hpqInv : Inv pq_st) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let honestC := (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    (match honestC with
      | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else ((t, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
      | none => ((t, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))) =
      ((t, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt))) := by
  intro ser tag i honestC
  dsimp only [honestC]
  cases hfind : s.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none => rfl
  | some wc =>
    dsimp only [Option.map]
    split
    next hsalt₀ =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hpred := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hpred
      rcases wc with ⟨w₀, c₀⟩
      dsimp only at hpred
      rcases hpred with ⟨rfl, hsend⟩
      have hsalt : c₀.2.2.2 = effectiveHkdfSalt32 salt := hsalt₀
      have hinv_wc := hhon (w₀, c₀) hmem
      rcases honestEntryInvC_eq_raw P Inv Dh encT epExp hinv_wc hparse with
        ⟨_, hsrk, _, hc₀⟩
      have ht_eq : c₀.1.1 = t := ht (w₀, c₀) hmem rfl hsend
      have hT_eq : T = Dh.dh (epExp c₀.1.1) Dh.base := hinj (hencT.trans hsrk)
      have hdec_eq : decT h.senderRatchetKey = some (Dh.dh (epExp c₀.1.1) Dh.base) := by
        rw [hdecT, hT_eq]
      rw [hdec_eq, hc₀, ht_eq, hsalt]
    next => rfl

theorem resolveSim_knownChainC (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (k : PublicKey) (ci : ℕ)
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some k) = some ci) :
    let g := (s.chains Q).getD ci ⟨none, 0, 0, []⟩
    let spkKey := encT (Dh.dh x₀ Dh.base)
    let s_res := resolveSim spkKey s
    (s.chains Q)[ci]? = some g ∧
    g.key = some k ∧
    (s_res.chains Q).findIdx? (fun g => g.key == some k) = some ci ∧
    (s_res.chains Q)[ci]? = some g ∧
    (s_res.chains Q).getD ci ⟨none, 0, 0, []⟩ = g ∧
    ∀ i, Function.update s_res.chains Q ((s_res.chains Q).set ci (g.accept i)) =
      resolveSpkChains spkKey (Function.update s.chains Q ((s.chains Q).set ci (g.accept i))) := by
  intro g spkKey s_res
  rcases getElem?_of_findIdx_ghost (s.chains Q) k ci hfind with ⟨g', hg_elem, hg_key⟩
  have hg'_eq : g = g' := by simp [g, List.getD, hg_elem]
  subst hg'_eq
  have hg_mem : g ∈ s.chains Q := List.mem_of_getElem? hg_elem
  have hg_none : g.key.isNone = false := by rw [hg_key]; rfl
  rcases hinv.hchains_sync Q g hg_mem with ⟨hg_ep_le, _, hg_key_sync, _⟩
  simp only [hg_none, Bool.false_eq_true, ↓reduceIte, hg_key] at hg_key_sync
  have hk_eq : k = encT (Dh.dh (epExp g.epoch) Dh.base) := Option.some.inj hg_key_sync
  cases Q with
  | B =>
    have hresB : s_res.chains .B = s.chains .B := rfl
    refine ⟨hg_elem, hg_key, by rw [hresB, hfind], by rw [hresB, hg_elem], ?_, ?_⟩
    · simp [List.getD, hresB, hg_elem]
    · intro i
      funext R
      cases R <;> simp [s_res, resolveSim, resolveSpkChains, Function.update]
  | A =>
    have hnodup : ((s.chains .A).map (·.epoch)).Nodup := by
      rw [hinv.hchainsA_ep]
      exact epListA_nodup (s.mir.epoch .A / 2)
    have hpred_eq : ∀ g₀ ∈ s.chains .A,
        ((if g₀.key.isNone then { g₀ with key := some spkKey } else g₀).key == some k) =
          (g₀.key == some k) := by
      intro g₀ hg₀
      by_cases hnone : g₀.key.isNone = true
      · simp only [hnone, ↓reduceIte]
        have h1 : (g₀.key == some k) = false := by
          cases hk₀ : g₀.key with
          | none => rfl
          | some _ => rw [hk₀] at hnone; cases hnone
        rw [h1, beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
        intro hspk
        have hdh : Dh.dh (epExp 0) Dh.base = Dh.dh (epExp g.epoch) Dh.base := by
          apply hinj
          rw [hinv.hepExp0]
          exact hspk.trans hk_eq
        have hle_max : g.epoch ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) := by
          refine le_trans hg_ep_le (le_trans ?_ (le_max_left _ _))
          unfold maxActiveEp; omega
        have hep0 : g.epoch = 0 := (hinv.hcoll 0 g.epoch (Nat.zero_le _) hle_max hdh).symm
        have hg₀_ep0 : g₀.epoch = 0 := hinv.hchainsA.1 g₀ hg₀ hnone
        rcases List.mem_iff_getElem?.mp hg₀ with ⟨j, hj⟩
        have hj_lt : j < (s.chains .A).length := (List.getElem?_eq_some_iff.mp hj).1
        by_cases hj_ci : j = ci
        · subst hj_ci
          have heq_g : g₀ = g := Option.some.inj (hj.symm.trans hg_elem)
          rw [heq_g, hg_none] at hnone
          cases hnone
        · exact nodup_distinct_epoch hnodup hg_elem j hj_lt hj_ci g₀ hj (hg₀_ep0.trans hep0.symm)
      · simp [hnone]
    have hresA : s_res.chains .A =
        (s.chains .A).map (fun g₀ => if g₀.key.isNone then { g₀ with key := some spkKey } else g₀) := rfl
    have hfind_res : (s_res.chains .A).findIdx? (fun g => g.key == some k) = some ci := by
      rw [hresA, findIdx?_map_eq_of_mem _ _ _ hpred_eq, hfind]
    have helem_res : (s_res.chains .A)[ci]? = some g := by
      rw [hresA, List.getElem?_map, hg_elem]
      simp [Option.map, hg_none]
    refine ⟨hg_elem, hg_key, hfind_res, helem_res, ?_, ?_⟩
    · simp [List.getD, helem_res]
    · intro i
      funext R
      cases R with
      | B => simp [s_res, resolveSim, resolveSpkChains, Function.update]
      | A =>
        simp only [s_res, resolveSim, resolveSpkChains, Function.update_self, ↓reduceIte]
        rw [List.map_set]
        have hacc_none : (g.accept i).key.isNone = false := by
          rw [accept_key, hg_none]
        simp [hacc_none]

theorem receive_knownChain_expectedGhost_eqC (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (w : List (BitVec 8)) (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet = false)
    (ci : ℕ)
    (hfind : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = some ci)
    (T? : Option Pt) (hT : (T?.map encT).getD dummyKey = h.senderRatchetKey)
    (mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8)) )
    (hmir_ep : mir'.epoch = s.mir.epoch)
    (hmir_idx : mir'.idx = s.mir.idx)
    (rc : BitVec 256) :
    let g := (s.chains Q).getD ci ⟨none, 0, 0, []⟩
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let c : Fig8C Pt := ((g.epoch, T?), i, (ser, tag), effectiveHkdfSalt32 salt)
    (g.rejects i = true → P.receive (s_R.st Q) w rc = none) ∧
    (g.rejects i = false →
      match (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c with
      | none => P.receive (s_R.st Q) w rc = none
      | some (st', t', i', (pub, m)) =>
        t' = g.epoch ∧ i' = i ∧
        pub = ⟨h.previousCounter, h.pqRatchet, effectiveHkdfSalt32 salt, h.addresses⟩ ∧
        (∃ v', st' = { (s_fig8.st Q) with vR := Function.update (s_fig8.st Q).vR g.epoch (some v') } ∧
          ChainSync (g.accept i) v') ∧
        ∃ m_raw : List (BitVec 8),
          m = padOrTruncatePlain ℓ m_raw ∧
          let s' : SimState PQ Pt ℓ :=
            { s with
              mir := mir',
              pq := Function.update s.pq Q pq',
              unackA := s.unackA && Q != Party.A,
              chains := Function.update s.chains Q ((s.chains Q).modify ci (·.accept i)) }
          P.receive (s_R.st Q) w rc =
            some (expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q), g.epoch, i, m_raw)) := by
  intro g ser tag i c
  set spkKey := encT (Dh.dh x₀ Dh.base)
  set s_res := resolveSim spkKey s
  set st := s_fig8.st Q
  rcases resolveSim_knownChainC P Inv ℓ Dh encPt encT hinj qep q r x₀ s_R s s_fig8 ec winBefore epExp
    hinv Q h.senderRatchetKey ci hfind with
    ⟨hg_elem, hg_key, hfind_res, helem_res, hgetD_res, hchains_res⟩
  have hg_mem : g ∈ s.chains Q := List.mem_of_getElem? hg_elem
  rcases hinv.hchains_sync Q g hg_mem with ⟨hg_ep_le, hrecv, _, v, hvR, hsync⟩
  have hg_ep_tcur : g.epoch ≤ st.tcur := by
    rw [hinv.htcur Q]
    exact hg_ep_le
  have hdummy : ∀ g₀ ∈ s_res.chains Q, g₀.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro g₀ hg₀ hnone
    exfalso
    cases Q with
    | B =>
      have hb := hinv.hchainsB_none g₀ hg₀
      rw [hnone] at hb
      cases hb
    | A =>
      change g₀ ∈ (s.chains .A).map
        (fun x => if x.key.isNone then { x with key := some spkKey } else x) at hg₀
      rcases List.mem_map.mp hg₀ with ⟨x, _, rfl⟩
      by_cases hx : x.key.isNone = true
      · simp [hx] at hnone
      · simp [hx] at hnone
        rw [hnone] at hx
        exact hx rfl
  have hmap_ep : (s_res.chains Q).map (·.epoch) = (s.chains Q).map (·.epoch) :=
    resolveSpkChains_map_epoch spkKey s.chains Q
  have hnodup_res : ((s_res.chains Q).map (·.epoch)).Nodup := by
    rw [hmap_ep]
    cases Q with
    | A => rw [hinv.hchainsA_ep]; exact epListA_nodup (s.mir.epoch .A / 2)
    | B => rw [hinv.hchainsB_ep]; exact epListB_nodup ((s.mir.epoch .B + 1) / 2)
  have hdistinct : ∀ j < (s_res.chains Q).length, j ≠ ci →
      ∀ g_j, (s_res.chains Q)[j]? = some g_j → g_j.epoch ≠ g.epoch :=
    fun j hj_lt hj_ne g_j hg_j => nodup_distinct_epoch hnodup_res helem_res j hj_lt hj_ne g_j hg_j
  letI : DecidableEq PQ := Classical.decEq PQ
  set g₀ := toGhost P s_res Q st
  set rk := if inReceiveOnlyEpoch s.mir Q then
      match st.γ with
      | .pub T => ((rootPRNG P.C.F encPt).up st.root (Dh.dh (ec Q) T)).1
      | _ => g₀.session.rootKey
    else g₀.session.rootKey
  set sc := if inReceiveOnlyEpoch s.mir Q then
      match st.γ with
      | .pub T => some ⟨KeyPair.generate P.C (ec Q), ⟨((rootPRNG P.C.F encPt).up st.root (Dh.dh (ec Q) T)).2, 0⟩⟩
      | _ => g₀.session.senderChain
    else g₀.session.senderChain
  set pn := if inReceiveOnlyEpoch s.mir Q then
      match st.γ with
      | .pub _ => BitVec.ofNat 32 (s.mir.idx Q - 1)
      | _ => g₀.session.previousCounter
    else g₀.session.previousCounter
  have hst_R_eq : s_R.st Q = withEager g₀ rk sc pn := by
    rw [hinv.hst_R Q]
    exact expectedGhost_eq_withEager P Dh encPt spkKey s Q st (ec Q)
  have hstep := receive_knownChain_withEager_toGhost_eq P Dh encPt encT idOf lam hid s_res Q st
    (hinv.hst_id Q) w hw_len h body hparse haddrs pq' salt hspqr hpan ci hfind_res hdummy
    g helem_res hg_ep_tcur hrecv v hvR hsync T? hT hdistinct mir' (congrFun hmir_ep Q)
    rk sc pn rc
  dsimp only at hstep
  rw [hst_R_eq]
  refine ⟨hstep.1, fun hacc => ?_⟩
  have h2 := hstep.2 hacc
  cases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c with
  | none =>
    rw [hfig] at h2
    exact h2
  | some res =>
    rcases res with ⟨st', t', i', pub, m⟩
    rw [hfig] at h2
    rcases h2 with ⟨ht', hi', hpub, ⟨v', hst', hsync'⟩, m_raw, hm_raw, hrec⟩
    refine ⟨ht', hi', hpub, ⟨v', hst', hsync'⟩, m_raw, hm_raw, ?_⟩
    rw [hrec]
    congr 1
    congr 1
    rw [modify_eq_set_of_getElem? (s.chains Q) ci g (·.accept i) hg_elem]
    set s' : SimState PQ Pt ℓ :=
      { s with
        mir := mir',
        pq := Function.update s.pq Q pq',
        unackA := s.unackA && Q != Party.A,
        chains := Function.update s.chains Q ((s.chains Q).set ci (g.accept i)) }
    have hs_res' :
        ({ s_res with
            mir := mir',
            pq := Function.update s_res.pq Q pq',
            unackA := s_res.unackA && Q != Party.A,
            chains := Function.update s_res.chains Q ((s_res.chains Q).set ci (g.accept i)) } : SimState PQ Pt ℓ) =
        resolveSim spkKey s' := by
      simp only [s_res, s', resolveSim]
      congr 1
      exact hchains_res i
    rw [hs_res', expectedGhost_eq_withEager P Dh encPt spkKey s' Q st' (ec Q)]
    have hinWin_eq : inReceiveOnlyEpoch mir' Q = inReceiveOnlyEpoch s.mir Q := by
      unfold inReceiveOnlyEpoch
      rw [hmir_ep]
    subst hst'
    congr 1 <;> { simp [g₀, rk, sc, pn, s', s_res, st, hinWin_eq, hmir_ep, hmir_idx, toGhost, resolveSim]; try rfl }

theorem simInvC_inject_known_accept (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (ci : ℕ) (g : GhostChain) (i : ℕ) (pq' : PQ)
    (hg_elem : (s.chains Q)[ci]? = some g)
    (v' : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hsync' : ChainSync (g.accept i) v')
    (pos : SM.Pos) (hpos_ep : pos.epoch = g.epoch)
    (hpq' : Inv pq') :
    let st' : Fig8St Pt := { (s_fig8.st Q) with vR := Function.update (s_fig8.st Q).vR g.epoch (some v') }
    let mir' := s.mir.accept Q () pos
    let s' : SimState PQ Pt ℓ :=
      { s with
        mir := mir',
        pq := Function.update s.pq Q pq',
        unackA := s.unackA && Q != Party.A,
        chains := Function.update s.chains Q ((s.chains Q).modify ci (·.accept i)) }
    let s_fig8' := s_fig8.accept Q st' pos
    let s_R' := s_R.accept Q (expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q st' (ec Q)) pos
    SimInvC P Inv ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec winBefore epExp := by
  intro st' mir' s' s_fig8' s_R'
  have hg_mem : g ∈ s.chains Q := List.mem_of_getElem? hg_elem
  rcases hinv.hchains_sync Q g hg_mem with ⟨hg_ep_le, hrecv, hg_key_sync, _⟩
  have hpos_le : pos.epoch ≤ s.mir.epoch Q := by rw [hpos_ep]; exact hg_ep_le
  have hmir_ep : mir'.epoch = s.mir.epoch := WP2A.I3.accept_epoch_eq_of_le s.mir Q () pos hpos_le
  have hmir_idx : mir'.idx = s.mir.idx := rfl
  have hinWin_eq : ∀ R, inReceiveOnlyEpoch mir' R = inReceiveOnlyEpoch s.mir R := by
    intro R; unfold inReceiveOnlyEpoch; rw [hmir_ep]
  have hmax_ep : ∀ R, maxActiveEp mir' R = maxActiveEp s.mir R := by
    intro R; unfold maxActiveEp; rw [hmir_ep, hinWin_eq R]
  have hmod_set : (s.chains Q).modify ci (·.accept i) = (s.chains Q).set ci (g.accept i) :=
    modify_eq_set_of_getElem? (s.chains Q) ci g (·.accept i) hg_elem
  have hchains_ep : ∀ R, (s'.chains R).map (·.epoch) = (s.chains R).map (·.epoch) := by
    intro R
    dsimp only [s']
    by_cases hR : R = Q
    · subst hR
      rw [Function.update_self, hmod_set]
      exact map_epoch_set_accept (s.chains R) ci g i hg_elem
    · rw [Function.update_of_ne hR]
  have hnodup : ((s.chains Q).map (·.epoch)).Nodup := by
    cases Q with
    | A => rw [hinv.hchainsA_ep]; exact epListA_nodup (s.mir.epoch .A / 2)
    | B => rw [hinv.hchainsB_ep]; exact epListB_nodup ((s.mir.epoch .B + 1) / 2)
  have hs'_eq : s' =
      { mir := s.mir.accept Q () pos,
        pq := Function.update s.pq Q pq', pn := s.pn, unackA := s.unackA && Q != Party.A,
        honest := s.honest, chains := Function.update s.chains Q ((s.chains Q).modify ci (·.accept i)),
        amb := s.amb, stopped := false } := by
    have hst : s.stopped = false := hinv.hmeta.hstop
    dsimp only [s', mir']
    rw [hst]
  refine
    { hmeta := by
        rw [hs'_eq]
        exact hinv.hmeta.accept_preserves Q _ st' pos _ _ _ _ _ _
      hcomp := comp_healedBy_false_accept s.mir 3 Q () pos hinv.hcomp
      hec := by
        intro R hR
        rw [hinWin_eq R] at hR
        exact hinv.hec R hR
      hwinBefore := hinv.hwinBefore
      hamb := by dsimp only [s']; have := hinv.hamb; omega
      hamb_strict := by
        intro hpos
        dsimp only [s'] at hpos ⊢
        rw [hmir_ep] at hpos
        have := hinv.hamb_strict hpos; omega
      hidx_le := by intro R; dsimp only [s', mir', SM.GameState.accept, SM.GameState.delete]; have := hinv.hidx_le R; omega
      hhon_len := by dsimp only [s']; have := hinv.hhon_len; omega
      hep_le := by intro R; dsimp only [s']; rw [hmir_ep]; exact hinv.hep_le R
      hep_adj := by
        intro R; dsimp only [s']; rw [hinWin_eq R, hmir_ep]; exact hinv.hep_adj R
      hst_R := by
        intro R
        dsimp only [s_R', s_fig8', SM.GameState.accept, SM.GameState.delete]
        by_cases hR : R = Q
        · subst hR
          simp [Function.update_self]
        · simp only [Function.update_of_ne hR]
          rw [hinv.hst_R R]
          unfold expectedGhost
          have hresolve_R : (resolveSim (encT (Dh.dh x₀ Dh.base)) s').chains R =
              (resolveSim (encT (Dh.dh x₀ Dh.base)) s).chains R := by
            unfold resolveSim resolveSpkChains
            cases R <;> cases Q <;> try contradiction
            · simp [s', Function.update_of_ne (by decide : Party.A ≠ Party.B)]
            · simp [s', Function.update_of_ne (by decide : Party.B ≠ Party.A)]
          have hunack_R : (R == Party.A && s'.unackA) = (R == Party.A && s.unackA) := by
            cases R <;> cases Q <;> try contradiction
            · simp [s']
            · simp [s']
          have hmir_ep_R : mir'.epoch R = s.mir.epoch R := congrFun hmir_ep R
          have htoGhost_R : toGhost P (resolveSim (encT (Dh.dh x₀ Dh.base)) s') R (s_fig8.st R) =
              toGhost P (resolveSim (encT (Dh.dh x₀ Dh.base)) s) R (s_fig8.st R) := by
            unfold toGhost
            simp only [resolveSim_mir, resolveSim_pn, resolveSim_unackA, resolveSim_pq,
               hunack_R, hresolve_R]
            dsimp only [s']
            simp [hmir_ep_R, Function.update_of_ne hR]
          dsimp only [s']
          rw [hinWin_eq R, hmir_idx, htoGhost_R]
      hst_id := by
        intro R
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete]
        by_cases hR : R = Q
        · subst hR; simp [Function.update_self, st', hinv.hst_id R]
        · simp [Function.update_of_ne hR, hinv.hst_id R]
      htcur := by
        intro R
        dsimp only [s_fig8', s', SM.GameState.accept, SM.GameState.delete]
        rw [hmir_ep]
        by_cases hR : R = Q
        · subst hR; simp [Function.update_self, st', hinv.htcur R]
        · simp [Function.update_of_ne hR, hinv.htcur R]
      hepExp0 := hinv.hepExp0
      hspur := by
        intro R
        rcases hinv.hspur R with ⟨rk_base, T_base, h1, h2, h3⟩
        refine ⟨rk_base, T_base, ?_, ?_, ?_⟩
        · intro hinw
          rw [hinWin_eq R] at hinw
          dsimp only [s_fig8', s', SM.GameState.accept, SM.GameState.delete]
          rw [hmir_ep]
          by_cases hR : R = Q
          · subst hR; simpa [Function.update_self, st'] using h1 hinw
          · simpa [Function.update_of_ne hR] using h1 hinw
        · intro hnot_inw
          rw [hinWin_eq R] at hnot_inw
          dsimp only [s_fig8', s', SM.GameState.accept, SM.GameState.delete]
          rw [hmir_ep, hmir_idx]
          by_cases hR : R = Q
          · subst hR; simpa [Function.update_self, st'] using h2 hnot_inw
          · simpa [Function.update_of_ne hR] using h2 hnot_inw
        · intro wc hwc hsend hle hnot_mem
          dsimp only [s'] at hwc hle hnot_mem ⊢
          rw [hmir_ep] at hle ⊢
          rw [hchains_ep R] at hnot_mem
          rw [hmax_ep R]
          exact h3 wc hwc hsend hle hnot_mem
      hchainsA := by
        dsimp only [s']
        rw [hmir_ep]
        cases Q with
        | A =>
          rw [Function.update_self, hmod_set]
          exact chainsEpochInvA_set_accept hinv.hchainsA ci g i hg_elem
        | B =>
          rw [Function.update_of_ne (by decide : Party.A ≠ Party.B)]
          exact hinv.hchainsA
      hchainsA_ep := by
        rw [hchains_ep .A]
        dsimp only [s']
        rw [hmir_ep]
        exact hinv.hchainsA_ep
      hchainsB_ep := by
        rw [hchains_ep .B]
        dsimp only [s']
        rw [hmir_ep]
        exact hinv.hchainsB_ep
      hchainsB_none := by
        intro g₀ hg₀
        dsimp only [s'] at hg₀
        cases Q with
        | A =>
          rw [Function.update_of_ne (by decide : Party.B ≠ Party.A)] at hg₀
          exact hinv.hchainsB_none g₀ hg₀
        | B =>
          rw [Function.update_self, hmod_set] at hg₀
          rcases List.mem_or_eq_of_mem_set hg₀ with hg₀ | rfl
          · exact hinv.hchainsB_none g₀ hg₀
          · rw [accept_key]
            exact hinv.hchainsB_none g hg_mem
      hcorrB0 := by dsimp only [s', mir']; exact hcorrB0_accept_modify hinv.hcorrB0
      hchains_sync := by
        intro R g₀ hg₀
        dsimp only [s', s_fig8', SM.GameState.accept, SM.GameState.delete] at hg₀ ⊢
        rw [hmir_ep]
        by_cases hR : R = Q
        · subst hR
          rw [Function.update_self, hmod_set] at hg₀
          simp only [Function.update_self, st']
          rcases List.mem_iff_getElem?.mp hg₀ with ⟨j, hj⟩
          have hj_lt : j < (s.chains R).length := by
            have := (List.getElem?_eq_some_iff.mp hj).1
            simpa using this
          by_cases hj_ci : j = ci
          · subst hj_ci
            rw [List.getElem?_set_self hj_lt, Option.some.injEq] at hj
            subst hj
            have hacc_ep : (g.accept i).epoch = g.epoch := accept_epoch g i
            have hacc_key : (g.accept i).key = g.key := accept_key g i
            rw [hacc_ep, hacc_key]
            refine ⟨hg_ep_le, hrecv, hg_key_sync, v', ?_, hsync'⟩
            simp [Function.update_self]
          · rw [List.getElem?_set_ne (Ne.symm hj_ci)] at hj
            have hg₀_mem : g₀ ∈ s.chains R := List.mem_of_getElem? hj
            rcases hinv.hchains_sync R g₀ hg₀_mem with ⟨h1, h2, h3, v₀, hv₀, hsync₀⟩
            have hne_ep : g₀.epoch ≠ g.epoch :=
              nodup_distinct_epoch hnodup hg_elem j hj_lt hj_ci g₀ hj
            refine ⟨h1, h2, h3, v₀, ?_, hsync₀⟩
            rw [Function.update_of_ne hne_ep, hv₀]
        · rw [Function.update_of_ne hR] at hg₀
          simp only [Function.update_of_ne hR]
          exact hinv.hchains_sync R g₀ hg₀
      hhon := by
        intro wc hwc
        dsimp only [s'] at hwc ⊢
        rw [hmax_ep .A, hmax_ep .B, hmir_ep]
        exact hinv.hhon wc hwc
      htrans_hon := by
        intro rec_f hrec_f
        dsimp only [s_fig8', SM.GameState.accept, SM.GameState.delete] at hrec_f
        exact hinv.htrans_hon rec_f (List.mem_of_mem_filter hrec_f)
      hcoll := by
        intro t₁ t₂ ht₁ ht₂ hdh
        dsimp only [s'] at ht₁ ht₂
        rw [hmax_ep .A, hmax_ep .B] at ht₁ ht₂
        exact hinv.hcoll t₁ t₂ ht₁ ht₂ hdh
      hpqInv := by
        intro R
        dsimp only [s']
        by_cases hR : R = Q
        · subst hR; simp [Function.update_self, hpq']
        · simp [Function.update_of_ne hR, hinv.hpqInv R] }

theorem expectedGhost_root_senderChain_of_posC (P : Params PQ PQC) (Inv : PQ → Prop) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (hinw : inReceiveOnlyEpoch s.mir Q = true →
      (s_fig8.st Q).root = rk_base ∧
      (s_fig8.st Q).γ = .pub T_base ∧
      T_base ≠ 0 ∧
      epExp (s.mir.epoch Q + 1) = ec Q)
    (hninw : inReceiveOnlyEpoch s.mir Q = false →
      (s_fig8.st Q).γ = .exp (epExp (s.mir.epoch Q)) ∧
      (0 < s.mir.epoch Q →
        (s_fig8.st Q).root = (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s.mir.epoch Q)) T_base))).1 ∧
        (s_fig8.st Q).curCkaMsg = some (Dh.dh (epExp (s.mir.epoch Q)) Dh.base)) ∧
      ∃ vS, (s_fig8.st Q).vS = some vS ∧ vS.lastIndex = s.mir.idx Q)
    (hpos : 0 < s.mir.epoch Q) :
    ∃ ck_prev idx_prev,
      (s_R.st Q).session.rootKey =
        (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (maxActiveEp s.mir Q)) T_base))).1 ∧
      (s_R.st Q).session.senderChain =
        some ⟨KeyPair.generate P.C (epExp (maxActiveEp s.mir Q)), ⟨ck_prev, idx_prev⟩⟩ := by
  rw [hinv.hst_R Q]
  by_cases hw : inReceiveOnlyEpoch s.mir Q = true
  · rcases hinw hw with ⟨hroot, hγ, _, hec_eq⟩
    have hmax : maxActiveEp s.mir Q = s.mir.epoch Q + 1 := by simp [maxActiveEp, hw]
    rw [expectedGhost_of_inWin_true P Dh encPt _ s Q (s_fig8.st Q) (ec Q) T_base hw hγ,
        hmax, hec_eq, hroot]
    exact ⟨_, 0, rfl, rfl⟩
  · have hwf : inReceiveOnlyEpoch s.mir Q = false := Bool.eq_false_iff.mpr hw
    rcases hninw hwf with ⟨hγ, hpos_rk, ⟨vS, hvS, _⟩⟩
    rcases hpos_rk hpos with ⟨hroot, _⟩
    have hmax : maxActiveEp s.mir Q = s.mir.epoch Q := by simp [maxActiveEp, hwf]
    rw [expectedGhost_of_inWin_false P Dh encPt _ s Q (s_fig8.st Q) (ec Q) hwf, hmax]
    unfold toGhost
    dsimp only
    rw [hroot, hγ, hvS]
    exact ⟨vS.chainKey, BitVec.ofNat 32 vS.lastIndex, rfl, rfl⟩

theorem mkC_newChain_eqC (P : Params PQ PQC) (Inv : PQ → Prop) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (huniq : PosUniq s)
    (hrtT : ∀ T, decT (encT T) = some T)
    (Q : Party) (w : List (BitVec 8))
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet = false)
    (hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false)
    (T : Pt) (hdecT : decT h.senderRatchetKey = some T) (hencT : encT T = h.senderRatchetKey) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let honestC := (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    (match honestC with
     | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
     | none => ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))) =
      ((s.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) := by
  intro ser tag i honestC
  have hinj := encT_injective hrtT
  dsimp only [honestC]
  cases hfind_hon : s.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none => rfl
  | some wc =>
    have hmem : wc ∈ s.honest := List.mem_of_find?_eq_some hfind_hon
    have hpred := List.find?_some hfind_hon
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    rcases wc with ⟨w_c, c_h⟩
    rcases hpred with ⟨hw_eq, hsend_h⟩
    dsimp only at hw_eq hsend_h
    rw [hw_eq] at hmem
    simp only [hfind_hon, Option.map_some, beq_eq_false_iff_ne, Ne, Option.some.injEq,
      decide_eq_true_eq] at hevict
    have hc_ep : c_h.1.1 = s.mir.epoch Q + 1 := Decidable.of_not_not hevict
    have hraw := mkC_eq_raw_of_honest_epochC P Inv Dh encT decT hinj epExp s Q w h body
      (s.pq Q) pq' salt (s.mir.epoch Q + 1) hdecT hencT
      (fun wc' hwc' => (hinv.hhon wc' hwc').1) hparse hspqr hpan
      (by
        intro wc' hwc' hw' hsend'
        rcases wc' with ⟨w', c'⟩
        dsimp only at hw' hsend' ⊢
        rw [hw'] at hwc'
        have heq_c : c' = c_h :=
          honestEntryInvC_unique P Inv Dh encT hinj epExp s huniq hwc' hmem
            (hinv.hhon (w, c') hwc').1 (hinv.hhon (w, c_h) hmem).1
            (hinv.hcoll c'.1.1 c_h.1.1 (hinv.hhon (w, c') hwc').2.1 (hinv.hhon (w, c_h) hmem).2.1)
        rw [heq_c, hc_ep])
      (hinv.hpqInv Q)
    dsimp only at hraw
    rw [hfind_hon, Option.map_some, hdecT] at hraw
    exact hraw

theorem hspk_corr_of_simInvC (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    {g₀ : GhostChain} (hg₀ : g₀ ∈ s.chains .A) (hnone : g₀.key.isNone = true) :
    (.B, 0) ∉ s.mir.corrs := by
  intro hcorr
  have hf := hinv.hcorrB0 hcorr g₀ hg₀
  rw [hnone] at hf
  exact Bool.noConfusion hf

/-- Preserves `SimInvCX` at `r - 1` after a trivial accept on a known chain. -/
theorem simInvCX_inject_known_accept (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (Q : Party) (ci : ℕ) (g : GhostChain) (i : ℕ) (pq' : PQ)
    (hg_elem : (sC.base.chains Q)[ci]? = some g)
    (v' : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hsync' : ChainSync (g.accept i) v')
    (pos : SM.Pos) (hpos_ep : pos.epoch = g.epoch)
    (hpq' : InvB Inv q r pq')
    (s' : SimState PQ Pt ℓ)
    (hs' : s' = { sC.base with
        mir := sC.base.mir.accept Q () pos,
        pq := Function.update sC.base.pq Q pq',
        unackA := sC.base.unackA && Q != Party.A,
        chains := Function.update sC.base.chains Q ((sC.base.chains Q).modify ci (·.accept i)) })
    (s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hs_fig8' : s_fig8' = s_fig8.accept Q
        { (s_fig8.st Q) with vR := Function.update (s_fig8.st Q).vR g.epoch (some v') } pos)
    (s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (hs_R' : s_R' = s_R.accept Q (expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' Q
        { (s_fig8.st Q) with vR := Function.update (s_fig8.st Q).vR g.epoch (some v') } (ec Q)) pos)
    (kept' : Party → Kept Pt)
    (hkept' : KeptInv P Dh encPt encT idOf lam { sC with base := s', kept := kept' } s_fig8')
    (hsync8' : EpochSync P Dh encPt encT idOf s'.honest sC.sent sC.snaps s_fig8' epExp) :
    SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' { sC with base := s', kept := kept' }
      s_fig8' ec winBefore epExp := by
  subst hs' hs_fig8' hs_R'
  have hsimr := simInvC_inject_known_accept P (InvB Inv q r) ℓ Dh encPt encT qep q r x₀ s_R sC.base
    s_fig8 ec winBefore epExp hinv.hsim Q ci g i pq' hg_elem v' hsync' pos hpos_ep hpq'
  dsimp only at hsimr
  have hg_mem : g ∈ sC.base.chains Q := List.mem_of_getElem? hg_elem
  have hpos_le : pos.epoch ≤ sC.base.mir.epoch Q := by
    rw [hpos_ep]; exact (hinv.hsim.hchains_sync Q g hg_mem).1
  have hmir_ep : (sC.base.mir.accept Q () pos).epoch = sC.base.mir.epoch :=
    WP2A.I3.accept_epoch_eq_of_le sC.base.mir Q () pos hpos_le
  refine
    { hsim := SimInvC.mono hsimr (fun R => InvB.mono (Nat.sub_le r 1) (hsimr.hpqInv R))
      huniq := hinv.huniq
      hkept := hkept'
      hidx := ?_
      hsync := hsync8' }
  intro wc hwc hep
  dsimp only at hwc hep ⊢
  rw [hmir_ep] at hep
  exact hinv.hidx wc hwc hep

end CryptoGames.LibsignalSM.Proofs.Refinement

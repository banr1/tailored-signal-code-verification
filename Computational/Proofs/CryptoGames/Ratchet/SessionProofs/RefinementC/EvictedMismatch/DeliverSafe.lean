/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.FigWin
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base

/-!
# Evicted salt mismatch, deliver: forward under `safeInj 3`

Proves `closeByStateC_deliver_evictedMismatch_safe`, closing an evicted-epoch `deliver` step with a
salt mismatch outside `inReceiveOnlyEpoch` when `safeInj 3` holds.
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

private theorem dems_srk_ne_spkKey {ℓ : ℕ} (P : Params PQ PQC) (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    {t : ℕ} (ht1 : 1 ≤ t)
    (ht_le : t ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B)) :
    encT (Dh.dh (epExp t) Dh.base) ≠ encT (Dh.dh x₀ Dh.base) := by
  intro heq
  have hdh : Dh.dh (epExp t) Dh.base = Dh.dh (epExp 0) Dh.base := by
    rw [hinv.hepExp0]
    exact hinj heq
  have ht0 : t = 0 := hinv.hcoll t 0 ht_le (Nat.zero_le _) hdh
  omega

private theorem dems_simRecvStepC_deliver_inTransit_mismatch_eq (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : sC.base.stopped = false) (hwin : sC.base.mir.win = false)
    (r_mir : SM.Record (Plain ℓ) (List (BitVec 8)))
    (htr : sC.base.mir.inTransit Q.other w = some r_mir)
    (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (c : Fig8C Pt) (pq' : PQ) (salt : Salt)
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1) :
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let i := h.counter.toNat + 1
    let T? := decT h.senderRatchetKey
    let spkAmb := Q == Party.A && (sC.base.chains Q).any (·.key.isNone)
    simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
      if T? == some 0 then (some .rejected, (sC, s_fig8, false))
      else
        let amb := inReceiveOnlyEpoch sC.base.mir Q || spkAmb
        let x₁ : JointC PQ Pt ℓ :=
          if amb then ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, (s_fig8, false))
          else (sC, (s_fig8, false))
        if inReceiveOnlyEpoch sC.base.mir Q || 25000 < i - 1 || 2 ^ 32 ≤ i then (some .rejected, x₁)
        else match T? with
        | none => (some .rejected, x₁)
        | some T =>
          let c' : Fig8C Pt := ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
          fwdEvictCPure P ℓ Dh encPt encT idOf lam qep true Q w true h.senderRatchetKey pq'
            c' x₁ := by
  intro ser tag i T? spkAmb
  unfold simRecvStepC simRecvStepCGen
  dsimp only
  have hstop' : ¬ (sC.base.stopped = true) := by rw [hstop]; decide
  have hwin' : ¬ (sC.base.mir.win = true) := by rw [hwin]; decide
  rw [ite_eq_right hstop', ite_eq_right hwin']
  have hbeq_true : ∀ b : Bool, (some b == some true) = b := by decide
  have hsalt_f : ¬ (c.2.2.2 = effectiveHkdfSalt32 salt) := hsalt
  have hdec_t : decide (c.1.1 ≠ sC.base.mir.epoch Q + 1) = true := decide_eq_true hepoch
  simp only [htr, Option.isNone_some, Bool.and_false, Bool.not_true, Bool.false_and,
    hw_len, Bool.false_eq_true, ↓reduceIte, hparse, haddrs, hspqr, hpan, hhonC, Option.map_some,
    hbeq_true, hsalt_f, hfind, hdec_t, Bool.true_and]
  rfl

/-- Closes the `deliver` step for an evicted salt mismatch outside `inReceiveOnlyEpoch` with in-range
counter under `safeInj 3`, either coupling rejection or winning Fig. 8 on acceptance. -/
theorem closeByStateC_deliver_evictedMismatch_safe {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hS : SpqrCLocal P.spqr q Inv) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r)
    (post : α → Bool)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (RecvResult (Plain ℓ)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest) (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC : (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) =
      some c)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1)
    (hsalt : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hbound : ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1))
    (hsafe : sC.base.mir.safeInj 3 = true)
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inr (Q, w)))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  have hsim := hinv.hsim
  have hmeta := hsim.hmeta
  have hM := libX25519Rel_model hX
  set M := max (maxActiveEp sC.base.mir .A) (maxActiveEp sC.base.mir .B)
  have hfind_hon : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) =
      some (w, c) := by
    cases hf : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
    | none => rw [hf] at hhonC; cases hhonC
    | some wc =>
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      rw [hf, Option.map_some] at hhonC
      have hc2 : wc.2 = c := Option.some.inj hhonC
      rcases wc with ⟨w', c'⟩
      dsimp only at hp hc2
      rw [hp.1, hc2]
  rcases hsim.hhon (w, c) hc_mem with ⟨hhon_c, hc_le_M, hsends_c, hc_le_sender⟩
  rcases hhon_c with ⟨hw_eq, _, ht1, hraw_c, hi1, hi32, hT_c,
    h_c, body_c, hparse_c, hver, hsrk, hctr, _⟩
  have hh_eq : h_c = h := congrArg Prod.fst (Option.some.inj (hparse_c.symm.trans hparse))
  rw [hh_eq] at hver hsrk hctr
  have huse_all : ∀ k, simRecvUsesCoin P encT decT k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvUsesCoin_of_honestC_some P encT decT k Q w true (sC.base, s_fig8) c hhonC hc_sender
  have hres_k : ∀ k,
      simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w true 0 (sC.base, s_fig8) =
        (some .rejected, (sC.base, s_fig8)) := by
    intro k
    unfold simRecvStep
    simp [hmeta.hstop, hmeta.hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon,
      hepoch]
  have hstops_all : ∀ k, simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8) = false :=
    fun k => simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w true (sC.base, s_fig8)
      (by rw [hres_k k]; exact hmeta.hstop)
  have hstepC_inTransit :=
    dems_simRecvStepC_deliver_inTransit_mismatch_eq P ℓ Dh encPt encT decT idOf lam qep
      Q w sC s_fig8 hmeta.hstop hmeta.hwin_mir r_mir htr_mir hlen h body hparse haddrs c pq' salt
      hspqr hpan hsalt hhonC hfind hepoch
  let spkKey := encT (Dh.dh x₀ Dh.base)
  set i := h.counter.toNat + 1
  set sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    rw [hsrk]
    exact dems_srk_ne_spkKey P (InvB Inv q r) Dh encPt encT hinj qep q r x₀ hsim ht1 hc_le_M
  let T := Dh.dh (epExp c.1.1) Dh.base
  have hT_dec : decT h.senderRatchetKey = some T := by
    dsimp only [T]; rw [hsrk, hdec]
  have hT_ne0 : T ≠ 0 :=
    hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hsrk' : h.senderRatchetKey = encT T := by
    dsimp only [T]; exact hsrk
  have hzero_f : (decT h.senderRatchetKey == some 0) = false := by
    rw [hT_dec]; simp [beq_eq_false_iff_ne, hT_ne0]
  have hzero_T : (some T == some (0 : Pt)) = false := by
    simp [beq_eq_false_iff_ne, hT_ne0]
  have hst_R_Q : s_R.st Q = toGhost P (resolveSim spkKey sC.base) Q (s_fig8.st Q) := by
    rw [hsim.hst_R Q]; simp [expectedGhost, hinw, spkKey]
  rcases hsim.hspur Q with ⟨rk_base, T_base, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw with ⟨hγ_Q, _, v_prev, hvS_Q, hv_last⟩
  have hmir_ep_tcur : (resolveSim spkKey sC.base).mir.epoch Q = (s_fig8.st Q).tcur :=
    (hsim.htcur Q).symm
  have hrecv_tcur : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hsim.htcur Q]; exact sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
  have hfind_res : ((resolveSim spkKey sC.base).chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none := by
    rw [resolveSim_findIdx_eq_of_ne spkKey sC.base Q h.senderRatchetKey hsrk_ne_spk]
    exact hfind
  have hdummy_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro _ _ _; rw [hsrk]; exact hdum _
  have hchains_ep_res : ∀ g' ∈ (resolveSim spkKey sC.base).chains Q, g'.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g' hg'
    have hmem_ep : g'.epoch ∈ (sC.base.chains Q).map (·.epoch) := by
      rw [← resolveSim_chains_map_epoch spkKey sC.base Q]
      exact List.mem_map_of_mem hg'
    rw [List.mem_map] at hmem_ep
    rcases hmem_ep with ⟨g₀, hg₀, hgep⟩
    have hg₀_le := (hsim.hchains_sync Q g₀ hg₀).1
    rw [hsim.htcur Q, ← hgep]
    omega
  let t := sC.base.mir.epoch Q + 1
  let pos_new : SM.Pos := ⟨Q.other, t, i⟩
  have hmir'_ep_tcur : (sC.base.mir.accept Q () pos_new).epoch Q = (s_fig8.st Q).tcur + 1 := by
    dsimp only [SM.GameState.accept, SM.GameState.delete, pos_new, t]
    simp [Function.update_self, hsim.htcur Q, Nat.max_eq_right (Nat.le_succ _)]
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  let c' : Fig8C Pt := ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
  have hc'_eq_tcur : (((s_fig8.st Q).tcur + 1, some T), i, (ser, tag), effectiveHkdfSalt32 salt) = c' := by
    dsimp only [c']
    rw [hsim.htcur Q]
  have hnew := receive_newChain_toGhost_eq (ℓ := ℓ) P Dh encPt encT idOf lam hX hid
    (resolveSim spkKey sC.base) Q (s_fig8.st Q) (hsim.hst_id Q) hmir_ep_tcur hrecv_tcur
    (epExp (sC.base.mir.epoch Q)) hγ_Q v_prev hvS_Q w hlen h body hparse haddrs
    pq' salt hspqr hpan hfind_res hdummy_res hchains_ep_res T hT_ne0 hsrk'.symm
    (sC.base.mir.accept Q () pos_new) hmir'_ep_tcur
  dsimp only at hnew
  rw [hc'_eq_tcur, hsim.htcur Q] at hnew
  have hsm_rcv_eq : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' =
      sm.receive (s_fig8.st Q) c' := rfl
  have hjump : ¬ 25000 < i - 1 := fun hj => hbound (Or.inl hj)
  have hi32' : ¬ 2 ^ 32 ≤ i := fun hi => hbound (Or.inr hi)
  set g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have hg_rej_eq : g_init.rejects i = decide (25000 < i - 1) :=
    g_init_rejects_eq (some h.senderRatchetKey) t i (by dsimp only [i]; omega) (by dsimp only [i]; omega)
  have hi32_f : decide (2 ^ 32 ≤ i) = false := decide_eq_false hi32'
  have hjump_f : decide (25000 < i - 1) = false := decide_eq_false hjump
  have hrej_false : g_init.rejects i = false := by
    rw [hg_rej_eq]; exact hjump_f
  have hc'_not_hon : ∀ wc ∈ sC.base.honest, wc.2 ≠ c' := by
    intro wc hwc heq_c'
    rcases hsim.hhon wc hwc with ⟨hhon_wc, hwc_le_M, _, _⟩
    have hT_wc : wc.2.1.2 = some (Dh.dh (epExp wc.2.1.1) Dh.base) := hhon_wc.2.2.2.2.2.2.1
    have hep_wc : wc.2.1.1 = sC.base.mir.epoch Q + 1 := congrArg (fun x : Fig8C Pt => x.1.1) heq_c'
    have hT_eq : wc.2.1.2 = some T := congrArg (fun x : Fig8C Pt => x.1.2) heq_c'
    have hdh : Dh.dh (epExp wc.2.1.1) Dh.base = Dh.dh (epExp c.1.1) Dh.base :=
      Option.some.inj (hT_wc.symm.trans hT_eq)
    have hcoll_eq : wc.2.1.1 = c.1.1 := hsim.hcoll wc.2.1.1 c.1.1 hwc_le_M hc_le_M hdh
    exact hepoch (hcoll_eq.symm.trans hep_wc)
  have hfwd_c' : ∀ s₁ : SimState PQ Pt ℓ, s₁.honest = sC.base.honest →
      fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c' s_fig8 =
        injectPure sm 3 (qep + 1) SM.Config.h1 Q c' s_fig8 := by
    intro s₁ hs₁
    unfold fwdPure
    have hany : s₁.honest.any (fun wc => decide (wc.2 = c') && (s₁.mir.inTransit Q.other wc.1).isSome) = false := by
      rw [hs₁, List.any_eq_false]
      intro wc hwc
      simp [hc'_not_hon wc hwc]
    rw [hany]
    rfl
  have htr_fig8_c' : (s_fig8.inTransit Q.other c').isSome = false := by
    rw [Bool.eq_false_iff]
    intro hsome
    rcases Option.isSome_iff_exists.mp hsome with ⟨r_f, hr_f⟩
    have hmem_f : r_f ∈ s_fig8.trans := List.mem_of_find?_eq_some hr_f
    have hpred_f := List.find?_some hr_f
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred_f
    have hhon_f := (hsim.htrans_hon r_f hmem_f).1
    exact hc'_not_hon (LibsignalSim.toWire r_f.ct, r_f.ct) hhon_f hpred_f.2
  have hguard_fig8 : (s_fig8.win || (s_fig8.inTransit Q.other c').isSome || !s_fig8.safeInj 3) = false := by
    rw [hmeta.hwin_fig8, htr_fig8_c', hmeta.safeInj_fig8 3, hsafe]
    rfl
  set spkAmb := (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
  cases hfig8_rcv : sm.receive (s_fig8.st Q) c' with
  | none =>
    have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c' s_fig8 = (some .rejected, s_fig8) := by
      unfold injectPure
      simp [hguard_fig8, hfig8_rcv]
    have hnone_R : ∀ rc, P.receive (s_R.st Q) w rc = none := by
      intro rc
      rw [hst_R_Q]
      have h2 := (hnew rc).2 hrej_false
      rw [hsm_rcv_eq, hfig8_rcv] at h2
      exact h2
    cases hspk : spkAmb with
    | false =>
      have hresC :
          simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
            (some .rejected, (sC, s_fig8, false)) := by
        rw [hstepC_inTransit]
        simp only [hzero_f, hzero_T, Bool.false_eq_true, ↓reduceIte,
          hinw, hspk, Bool.or_self, hjump_f, hi32_f, hT_dec]
        unfold fwdEvictCPure fwdCPure
        simp only [hsafe, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 sC.base Q c' s_fig8
                let kept' := match z.1 with
                  | some (.accepted _ _ _) => Function.update sC.kept Q (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q))
                  | _ => sC.kept
                let a := onAnswerPure qep Q w true none h.senderRatchetKey pq' z.1 sC.base
                (a.1, ({ sC with base := a.2, kept := kept' }, z.2, false))) = _
        rw [hfwd_c' sC.base rfl, hinj_fig8]
        rfl
      exact closeByStateC_deliver_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
        Q w cont s_R sC s_fig8 ec winBefore epExp hinv htr_mir hnone_R huse_all hres_k hresC ih
    | true =>
      let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := { sC.base with amb := sC.base.amb + 1 } }
      have hresC :
          simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
            (some .rejected, (sC', s_fig8, false)) := by
        rw [hstepC_inTransit]
        simp only [hzero_f, hzero_T, Bool.false_eq_true, ↓reduceIte,
          hinw, hspk, Bool.false_or, Bool.or_self, hjump_f, hi32_f, hT_dec]
        unfold fwdEvictCPure fwdCPure
        simp only [hsafe, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 { sC.base with amb := sC.base.amb + 1 } Q c' s_fig8
                let kept' := match z.1 with
                  | some (.accepted _ _ _) => Function.update sC.kept Q (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q))
                  | _ => sC.kept
                let a := onAnswerPure qep Q w true none h.senderRatchetKey pq' z.1 { sC.base with amb := sC.base.amb + 1 }
                (a.1, ({ sC with base := a.2, kept := kept' }, z.2, false))) = _
        rw [hfwd_c' { sC.base with amb := sC.base.amb + 1 } rfl, hinj_fig8]
        rfl
      have hstepSim : ∀ k,
          stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w))))
            (sC, s_fig8, false) ec =
            pure (some .rejected, ((sC', s_fig8, false), ec)) := fun k =>
        stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep k Q w
          (sC, s_fig8, false) ec hsim.hec (huse_all k) (hstops_all k)
          _ hresC rfl
      have hR_map := hmeta.inTransit_R_map Q.other w
      rw [htr_mir, Option.map_some] at hR_map
      rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, _⟩
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          (.inl (.inl (.inr (Q, w)))) s_R =
          (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
        rw [stepR_deliver_R1Inj_some P ℓ encPt decT encT lam qep Q w s_R r_R hmeta.hwin_R hr_R]
        congr 1; funext rc
        rw [hnone_R rc]
      exact closeByStateC_inr_amb_noStop P ℓ Dh encPt encT decT idOf lam qep q δ post
        (.inl (.inl (.inr (Q, w)))) cont s_R sC sC' s_fig8 s_fig8 false false ec ec winBefore
        (some .rejected) ($ᵗ BitVec 256 : ProbComp (BitVec 256)) (fun _ => s_R)
        (stepR_deliver_D0_eq_R1Inj P ℓ encPt decT encT lam qep Q w s_R)
        hstepR (hstepSim none) (hstepSim (some sC.base.amb)) rfl hmeta.hstop le_rfl
        (fun _ => ih (some .rejected) s_R sC' s_fig8 false ec
          (fun j => if j = sC.base.amb then false else winBefore j) epExp
          (simInvCX_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r hr x₀
            s_R sC s_fig8 ec winBefore epExp hinv rfl))
  | some val =>
    rcases val with ⟨st', t', i', pub, m⟩
    have hnew0 := (hnew 0).2 hrej_false
    rw [hsm_rcv_eq, hfig8_rcv] at hnew0
    rcases hnew0 with ⟨ht', hi', _, _, _⟩
    subst ht' hi'
    have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < sC.base.mir.epoch Q + 1) := by
      have hep_le := hsim.hep_le Q
      omega
    have htriv_f : sC.base.mir.trivial 3 ⟨Q.other, sC.base.mir.epoch Q + 1, h.counter.toNat + 1⟩ = false :=
      trivial_false_of_newChain_inject hsafe hsim.hcomp Q ⟨Q.other, sC.base.mir.epoch Q + 1, h.counter.toNat + 1⟩
        (Nat.le_succ _)
    have htriv_fig8 : s_fig8.trivial 3 ⟨Q.other, sC.base.mir.epoch Q + 1, h.counter.toNat + 1⟩ = false := by
      rw [hmeta.trivial_fig8, htriv_f]
    let s_fig8' := { s_fig8 with win := true }
    have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c' s_fig8 =
        (some .rejected, s_fig8') := by
      unfold injectPure
      simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig8_rcv,
        hnot_gt_fig8, htriv_fig8, SM.Config.h1]
      rfl
    let s₁ : SimState PQ Pt ℓ := if spkAmb then { sC.base with amb := sC.base.amb + 1 } else sC.base
    have hs₁_hon : s₁.honest = sC.base.honest := by dsimp only [s₁]; split <;> rfl
    have hs₁_mir : s₁.mir = sC.base.mir := by dsimp only [s₁]; split <;> rfl
    have hresC :
        simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, false) =
          (some .rejected, ({ sC with base := s₁ }, s_fig8', false)) := by
      rw [hstepC_inTransit]
      simp only [hzero_f, hzero_T, Bool.false_eq_true, ↓reduceIte,
        hinw, Bool.false_or, hjump_f, hi32_f, hT_dec]
      have hx₁ : (if spkAmb then ({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, (s_fig8, false))
          else (sC, (s_fig8, false)) : JointC PQ Pt ℓ) = ({ sC with base := s₁ }, (s_fig8, false)) := by
        dsimp only [s₁]; split <;> rfl
      rw [hx₁]
      unfold fwdEvictCPure fwdCPure
      simp only [hs₁_mir, hsafe, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c' s_fig8
              let kept' := match z.1 with
                | some (.accepted _ _ _) => Function.update sC.kept Q (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q))
                | _ => sC.kept
              let a := onAnswerPure qep Q w true none h.senderRatchetKey pq' z.1 s₁
              (a.1, ({ sC with base := a.2, kept := kept' }, z.2, false))) = _
      rw [hfwd_c' s₁ hs₁_hon, hinj_fig8]
      rfl
    have hstepSim_none :
        stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w))))
          (sC, s_fig8, false) ec =
          pure (some .rejected, (({ sC with base := s₁ }, s_fig8', false), ec)) :=
      stepSimCEager_deliver_of_not_stops_same_epoch P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec hsim.hec (huse_all none) (hstops_all none)
        _ hresC (by dsimp only; rw [hs₁_mir])
    exact closeByStateC_inr_fig8_win P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inl (.inr (Q, w)))) cont s_R sC { sC with base := s₁ } s_fig8 s_fig8' false false
      ec ec winBefore (some .rejected) hstepSim_none rfl

end CryptoGames.LibsignalSM.Proofs.Refinement

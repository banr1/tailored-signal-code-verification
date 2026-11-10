/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedStepInjectAmbBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Tracker-halted ambiguous new-chain `inject` cases

Proves `closeByStateCTrack_inject_newChain_amb_inWin_false_find_none` and
`closeByStateCTrack_inject_newChain_amb_find_some`.
-/

set_option autoImplicit false

@[expose] public section

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open Computational.Proofs.SpecLemmas.Session
open CryptoGames
open CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.CKA CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.SpqrV1Sync.InSync (Seed)
open CryptoVerification.SpqrV1Sync.Braid (EncRand)
open CryptoVerification.E2E (liftStateT)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {Pt PQ : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

/-! ## Outside receive-only window, chain not found -/

private theorem iaf_mkC_newChain_eq (P : Params PQ (BitVec 512)) (Inv : PQ → Prop) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256} {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hrtT : ∀ T, decT (encT T) = some T)
    (Q : Party) (w : List (BitVec 8))
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (salt : Salt)
    (hevict : ((((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true) = false)
    (T : Pt) (hencT : encT T = h.senderRatchetKey) :
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
    rcases hpred with ⟨hw_eq, _⟩
    dsimp only at hw_eq
    rw [hw_eq] at hmem
    simp only [hfind_hon, Option.map_some, beq_eq_false_iff_ne, Ne, Option.some.injEq,
      decide_eq_true_eq] at hevict
    have hc_ep : c_h.1.1 = s.mir.epoch Q + 1 := Decidable.of_not_not hevict
    dsimp only [Option.map]
    split
    · rename_i hsalt
      rcases (hinv.hhon (w, c_h) hmem).1 with
        ⟨_, _, _, hraw, _, _, hT_c, h₀, body₀, hparse₀, _, hsrk, hctr, _⟩
      have hhb : (h, body) = (h₀, body₀) := Option.some.inj (hparse.symm.trans hparse₀)
      rcases Prod.mk.inj hhb with ⟨rfl, rfl⟩
      have hT_eq : T = Dh.dh (epExp c_h.1.1) Dh.base := hinj (hencT.trans hsrk)
      rcases c_h with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
      dsimp only at hc_ep hT_c hT_eq hctr hraw hsalt ⊢
      rw [hc_ep, hT_c, ← hT_eq, ← hctr, hraw, hsalt]
    · rfl

private theorem iaf_fwdCPure_false_rejected (P : Params PQ (BitVec 512)) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g g' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (hfwd : fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
      sC'.base Q c' g = (some .rejected, g')) :
    fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' honestC c' (sC', g, fl) =
      (some .rejected, (sC', g', fl)) := by
  have hplain : fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' honestC c' (sC', g, fl) =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' none c' (sC', g, fl) := by
    unfold fwdCPure
    cases honestC <;> simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hplain]
  unfold fwdCPure
  dsimp only
  rw [hfwd]
  rfl

theorem closeByStateCTrack_inject_newChain_amb_inWin_false_find_none {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    (hcC : trC.cand = none)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = false)
    (hamb_b : (inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))) = true)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hfind_res : ((resolveSim (encT (Dh.dh x₀ Dh.base)) sC.base).chains Q).findIdx?
      (fun g => g.key == some h.senderRatchetKey) = none)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC' trC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  let spkKey := encT (Dh.dh x₀ Dh.base)
  let s_res := resolveSim spkKey sC.base
  have hstop0 := (simRecvStepEager_inject_ambC P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep q r x₀
    Q w s_R sC.base s_fig8 ec winBefore epExp hinv.hcx.hsim hguard hlen hparse haddrs hspqr hpan hfind hevict hzero hamb_b).1
  have hspk_amb : (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = true := by
    rw [hinw, Bool.false_or] at hamb_b
    exact hamb_b
  have hst_R_eq : s_R.st Q = toGhost P s_res Q (s_fig8.st Q) := by
    rw [hinv.hcx.hsim.hst_R Q, expectedGhost_of_inWin_false P Dh encPt spkKey sC.base Q (s_fig8.st Q) (ec Q) hinw]
  have hon_img : ratchetKeyAdmissible P.codec decT encT w = true := by
    revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;>
      cases ratchetKeyAdmissible P.codec decT encT w <;> simp
  rcases lOnImage_some_of_parse P decT encT w h body hon_img hlen hparse with ⟨T, hdecT, hencT⟩
  have hT_ne0 : T ≠ 0 := by
    intro h0
    subst h0
    have h0' : (decT h.senderRatchetKey == some 0) = true := by simp [hdecT]
    rw [h0'] at hzero
    exact Bool.noConfusion hzero
  rcases hinv.hcx.hsim.hspur Q with ⟨rk_base, T_base, _, hninw, _⟩
  rcases hninw hinw with ⟨hγ, _, ⟨vS, hvS, _⟩⟩
  have hrecv : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hinv.hcx.hsim.htcur Q]
    exact sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
  have hno_none_res : ∀ g ∈ s_res.chains Q, g.key.isNone = false :=
    resolveSim_chains_no_none' spkKey sC.base Q hinv.hcx.hsim.hchainsB_none
  have hdummy : ∀ g ∈ s_res.chains Q, g.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro g hg hgn
    have hgn' := hno_none_res g hg
    simp [hgn] at hgn'
  have hchains_ep : ∀ g ∈ s_res.chains Q, g.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g hg
    have hmem_ep : g.epoch ∈ (resolveSpkChains spkKey sC.base.chains Q).map (·.epoch) := List.mem_map_of_mem hg
    rw [resolveSpkChains_map_epoch spkKey sC.base.chains Q, List.mem_map] at hmem_ep
    rcases hmem_ep with ⟨g₀, hg₀, hgep⟩
    have hle := (hinv.hcx.hsim.hchains_sync Q g₀ hg₀).1
    have htcur := hinv.hcx.hsim.htcur Q
    omega
  let i := h.counter.toNat + 1
  let t := (s_fig8.st Q).tcur + 1
  let pos : SM.Pos := ⟨Q.other, t, i⟩
  let mir' := sC.base.mir.accept Q () pos
  have hmir'_ep : mir'.epoch Q = (s_fig8.st Q).tcur + 1 := by
    have htcur := (hinv.hcx.hsim.htcur Q).symm
    unfold mir' SM.GameState.accept SM.GameState.delete
    dsimp only [pos, t]
    rw [Function.update_self, htcur]
    exact Nat.max_eq_right (Nat.le_succ _)
  have hstep_all := fun rc =>
    receive_newChain_toGhost_eq P Dh encPt encT idOf lam hX hid
      s_res Q (s_fig8.st Q) (hinv.hcx.hsim.hst_id Q) (hinv.hcx.hsim.htcur Q).symm hrecv
      (epExp (sC.base.mir.epoch Q)) hγ vS hvS w hlen h body hparse haddrs
      pq' salt hspqr hpan hfind_res hdummy hchains_ep T hT_ne0 hencT mir' hmir'_ep rc
  let g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have huse_none : simRecvUsesCoin P encT decT none Q w false (sC.base, s_fig8) = false :=
    simRecvUsesCoin_none P encT decT Q w false (sC.base, s_fig8)
  have hnone_div : ((none : Option ℕ) == some sC.base.amb) = false := rfl
  let s₁ : SimState PQ Pt ℓ := { sC.base with amb := sC.base.amb + 1 }
  have hs₁_stop : ({ sC.base with amb := sC.base.amb + 1, stopped := false } : SimState PQ Pt ℓ) = s₁ := by
    dsimp only [s₁]
    generalize hs : sC.base = sb
    have hst : sb.stopped = false := hs ▸ hinv.hcx.hsim.hmeta.hstop
    cases sb
    dsimp only at hst
    subst hst
    rfl
  by_cases hjump : (25000 < i - 1 || 2 ^ 32 ≤ i) = true
  · have hrej_init : g_init.rejects i = true := by
      unfold GhostChain.rejects
      dsimp only [g_init]
      have hi_pos : ¬ i ≤ 0 := by dsimp only [i]; omega
      simp only [hi_pos, ↓reduceIte, Nat.sub_zero]
      exact hjump
    have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (sC.base, s_fig8) =
        (some .rejected, (s₁, s_fig8)) := by
      unfold simRecvStep
      simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hevict, hzero, hamb_b, hnone_div, hinw, hspk_amb, Bool.false_or,
        show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hjump,
        hs₁_stop]
    have hstepC_none : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
        (some .rejected, ({ sC with base := s₁ }, s_fig8, false)) := by
      unfold simRecvStepCGen
      simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hevict, hzero, hamb_b, hinw, hspk_amb, Bool.false_or,
        show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hjump,
        hs₁_stop]
    have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8) = false :=
      simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8)
        (by rw [hstep_none]; exact hinv.hcx.hsim.hmeta.hstop)
    have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
        (sC, s_fig8, false) ec =
        pure (some .rejected, (({ sC with base := s₁ }, s_fig8, false), ec)) :=
      stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec hinv.hcx.hsim.hec huse_none hstops_none _ hstepC_none rfl
    have hrcv_R : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
      intro rc
      unfold libsignalSessionScheme
      dsimp only
      rw [hst_R_eq, (hstep_all rc).1 hrej_init]
      rfl
    exact closeByStateCTrack_inject_amb_reject (hnpW := recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan)
      P K Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
      Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0 hnone_eager
      (ih (some .rejected))
  · have hjump_f : (25000 < i - 1 || 2 ^ 32 ≤ i) = false := Bool.eq_false_iff.mpr hjump
    have hrej_init_f : g_init.rejects i = false := by
      unfold GhostChain.rejects
      dsimp only [g_init]
      have hi_pos : ¬ i ≤ 0 := by dsimp only [i]; omega
      simp only [hi_pos, ↓reduceIte, Nat.sub_zero]
      exact hjump_f
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let c : Fig8C Pt := ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    let honestC := (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
    let c_mk : Fig8C Pt :=
      match honestC with
      | some c₀ => if c₀.2.2.2 = effectiveHkdfSalt32 salt then c₀ else ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
      | none => ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    have hc_eq : ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = c := by
      dsimp only [t, c]; rw [hinv.hcx.hsim.htcur Q]
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    have hhon_wire : ∀ wc ∈ sC.base.honest, wc.1 = LibsignalSim.toWire wc.2 :=
      fun wc hwc => (hinv.hcx.hsim.hhon wc hwc).1.1
    have htr_mir : (sC.base.mir.inTransit Q.other w).isSome = false := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> simp
    have hsafe_mir : sC.base.mir.safeInj 3 = true := by
      revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;> simp
    have hmkC : c_mk = c := iaf_mkC_newChain_eq P (InvB Inv q r) Dh encPt encT decT qep q r x₀
      hinv.hcx.hsim hdec Q w hparse salt hevict T hencT
    have htoWire : LibsignalSim.toWire c = w :=
      toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T) i (effectiveHkdfSalt32 salt)
    have hfwd : fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c s_fig8 =
        injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 :=
      fwdPure_of_inTransit_false sm 3 (qep + 1) SM.Config.h1 s₁ Q w c s_fig8 hhon_wire htoWire htr_mir
    have htr_fig8 : (s_fig8.inTransit Q.other c).isSome = false :=
      inTransit_fig8_isSome_of_toWire hinv.hcx.hsim.hmeta Q w c htoWire htr_mir
    have hguard_fig8 : (s_fig8.win || (s_fig8.inTransit Q.other c).isSome || !s_fig8.safeInj 3) = false := by
      rw [hinv.hcx.hsim.hmeta.hwin_fig8, htr_fig8, hinv.hcx.hsim.hmeta.safeInj_fig8 3, hsafe_mir]
      rfl
    have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !s_R.safeInj 3 ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hinv.hcx.hsim.hmeta.hwin_R, hinv.hcx.hsim.hmeta.inTransit_R_isSome, hinv.hcx.hsim.hmeta.safeInj_R]
      simpa [configR1OnCurve] using hguard
    cases hfig : sm.receive (s_fig8.st Q) c with
    | none =>
      have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 = (some .rejected, s_fig8) := by
        unfold injectPure
        simp [hguard_fig8, hfig]
      have hfig_t : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
          (((s_fig8.st Q).tcur + 1, some T), h.counter.toNat + 1,
            (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) = none := by
        change sm.receive (s_fig8.st Q) ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = none
        rw [hc_eq, hfig]
      have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (sC.base, s_fig8) =
          (some .rejected, (s₁, s_fig8)) := by
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStep
        simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hamb_b, hnone_div, hinw, hspk_amb, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT, hs₁_stop]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c_mk s_fig8
                let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 s₁
                (a.1, (a.2, z.2))) = (some .rejected, (s₁, s_fig8))
        rw [hmkC, hfwd, hinj_fig8]
        rfl
      have hstepC_none : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
          (some .rejected, ({ sC with base := s₁ }, s_fig8, false)) := by
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStepCGen
        simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hamb_b, hinw, hspk_amb, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT, hs₁_stop]
        exact iaf_fwdCPure_false_rejected P ℓ Dh encPt encT idOf lam qep Q w false none
          h.senderRatchetKey pq' honestC c_mk { sC with base := s₁ } s_fig8 s_fig8 false
          (by dsimp only; rw [hmkC, hfwd, hinj_fig8])
      have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8) = false :=
        simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8)
          (by rw [hstep_none]; exact hinv.hcx.hsim.hmeta.hstop)
      have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
          (sC, s_fig8, false) ec =
          pure (some .rejected, (({ sC with base := s₁ }, s_fig8, false), ec)) :=
        stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
          (sC, s_fig8, false) ec hinv.hcx.hsim.hec huse_none hstops_none _ hstepC_none rfl
      have hrcv_R : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
        intro rc
        have h2_rc := (hstep_all rc).2 hrej_init_f
        dsimp only at h2_rc
        rw [hfig_t] at h2_rc
        unfold libsignalSessionScheme
        dsimp only
        rw [hst_R_eq, h2_rc]
        rfl
      exact closeByStateCTrack_inject_amb_reject (hnpW := recvPanicsW_eq_false_of P Q w sC.base hlen hparse hpan)
        P K Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
        Q w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0 hnone_eager
        (ih (some .rejected))
    | some val =>
      rcases val with ⟨st', t', i', ⟨pub, m⟩⟩
      have hfig_t : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
          (((s_fig8.st Q).tcur + 1, some T), h.counter.toNat + 1,
            (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) =
          some (st', t', i', (pub, m)) := by
        change sm.receive (s_fig8.st Q) ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = some (st', t', i', (pub, m))
        rw [hc_eq, hfig]
      have h2_0 := (hstep_all 0).2 hrej_init_f
      dsimp only at h2_0
      rw [hfig_t] at h2_0
      rcases h2_0 with ⟨ht', hi', _, _, _⟩
      have ht_eq : t = sC.base.mir.epoch Q + 1 := by dsimp only [t]; rw [hinv.hcx.hsim.htcur Q]
      subst ht' hi'
      have hnot_gt : ¬ (qep + 1 < t) := by
        have hep_le := hinv.hcx.hsim.hep_le Q
        omega
      have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < t) := by omega
      have htriv_f : sC.base.mir.trivial 3 ⟨Q.other, t, i⟩ = false :=
        trivial_false_of_newChain_inject hsafe_mir hinv.hcx.hsim.hcomp Q ⟨Q.other, t, i⟩
          (by dsimp only; omega)
      have htriv_R : s_R.trivial 3 ⟨Q.other, t, i⟩ = false := by
        rw [hinv.hcx.hsim.hmeta.trivial_R, htriv_f]
      have htriv_fig8 : s_fig8.trivial 3 ⟨Q.other, t, i⟩ = false := by
        rw [hinv.hcx.hsim.hmeta.trivial_fig8, htriv_f]
      let s_fig8' := { s_fig8 with win := true }
      have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c s_fig8 =
          (some .rejected, s_fig8') := by
        unfold injectPure
        simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig,
          show ¬ (qep + 1 + 1 < (s_fig8.st Q).tcur + 1) from hnot_gt_fig8,
          show s_fig8.trivial 3 ⟨Q.other, (s_fig8.st Q).tcur + 1, h.counter.toNat + 1⟩ = false from htriv_fig8]
        rfl
      have hstep_sim_none :
          simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w false 0 (sC.base, s_fig8) =
            (some .rejected, (s₁, s_fig8')) := by
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStep
        simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hamb_b, hnone_div, hinw, hspk_amb, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT, hs₁_stop]
        change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c_mk s_fig8
                let a := onAnswerPure qep Q w false none h.senderRatchetKey pq' z.1 s₁
                (a.1, (a.2, z.2))) = _
        rw [hmkC, hfwd, hinj_fig8]
        rfl
      have hstepC_none :
          simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
            (some .rejected, ({ sC with base := s₁ }, s_fig8', false)) := by
        have hT0_b : (some T == some 0) = false := by rw [← hdecT]; exact hzero
        unfold simRecvStepCGen
        simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
          hevict, hzero, hT0_b, hamb_b, hinw, hspk_amb, Bool.false_or,
          show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
          hdecT, hs₁_stop]
        exact iaf_fwdCPure_false_rejected P ℓ Dh encPt encT idOf lam qep Q w false none
          h.senderRatchetKey pq' honestC c_mk { sC with base := s₁ } s_fig8 s_fig8' false
          (by dsimp only; rw [hmkC, hfwd, hinj_fig8])
      have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8) = false :=
        simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none Q w false (sC.base, s_fig8)
          (by rw [hstep_sim_none]; exact hinv.hcx.hsim.hmeta.hstop)
      have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
          (sC, s_fig8, false) ec =
          pure (some .rejected, (({ sC with base := s₁ }, s_fig8', false), ec)) :=
        stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
          (sC, s_fig8, false) ec hinv.hcx.hsim.hec huse_none hstops_none _ hstepC_none rfl
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          (.inl (.inr (Q, w))) s_R =
          (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
            pure (some .rejected, { s_R with win := true })) := by
        rw [stepR_inject_eq]
        simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
        congr 1; funext rc
        have h2_rc := (hstep_all rc).2 hrej_init_f
        dsimp only at h2_rc
        rw [hfig_t] at h2_rc
        rcases h2_rc with ⟨_, _, _, _, m_raw, hm_raw, hrec_rc, _⟩
        unfold injectRPure
        simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
        unfold libsignalSessionScheme
        dsimp only
        rw [hst_R_eq, hrec_rc, Option.map_some]
        simp only [show ¬ (qep + 1 < (s_fig8.st Q).tcur + 1) from hnot_gt,
          show s_R.trivial 3 ⟨Q.other, (s_fig8.st Q).tcur + 1, h.counter.toNat + 1⟩ = false from htriv_R,
          Bool.false_eq_true, ↓reduceIte]
        rfl
      exact closeByStateCTrack_inr_both_win_const_rc P K ℓ Dh encPt encT decT idOf lam qep q δ post
        Q w cont s_R { s_R with win := true } stTrR
        sC { sC with base := s₁ } trC s_fig8 s_fig8' false false ec ec winBefore
        (some .rejected) hstepR hnone_eager rfl rfl

/-! ## Resolved SPK chain found -/

private theorem iafs_chainSync_with_key {g : GhostChain} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (k : Option PublicKey) (h : ChainSync g v) :
    ChainSync { g with key := k } v := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem closeByStateCTrack_inject_newChain_amb_find_some {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
    (cont : Option (RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R stTrR sC trC s_fig8 ec winBefore epExp)
    (hcC : trC.cand = none)
    (hguard : ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
      !(ratchetKeyAdmissible P.codec decT encT w)) = false)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hevict : ((((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = false)
    (hzero : (decT h.senderRatchetKey == some 0) = false)
    (hamb_b : (inReceiveOnlyEpoch sC.base.mir Q || (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))) = true)
    {ci : ℕ}
    (hfind_res : ((resolveSim (encT (Dh.dh x₀ Dh.base)) sC.base).chains Q).findIdx?
      (fun g => g.key == some h.senderRatchetKey) = some ci)
    (ih : ∀ ans s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCXTrack P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' stTrR' sC' trC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' stTrR' sC' trC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R stTrR sC trC s_fig8 false ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  let spkKey := encT (Dh.dh x₀ Dh.base)
  let s_res := resolveSim spkKey sC.base
  cases Q with
  | B =>
    have hchainsB : s_res.chains .B = sC.base.chains .B := rfl
    rw [hchainsB, hfind] at hfind_res
    cases hfind_res
  | A =>
    have hstop0 := (simRecvStepEager_inject_ambC P (InvB Inv q r) ℓ Dh encPt encT decT idOf lam qep q r x₀
      .A w s_R sC.base s_fig8 ec winBefore epExp hinv.hcx.hsim hguard hlen hparse haddrs hspqr hpan hfind hevict hzero hamb_b).1
    rcases getElem?_of_findIdx_ghost (s_res.chains .A) h.senderRatchetKey ci hfind_res with
      ⟨g_res, helem_res, hg_res_key⟩
    have hresA : s_res.chains .A =
        (sC.base.chains .A).map (fun g₀ => if g₀.key.isNone then { g₀ with key := some spkKey } else g₀) := rfl
    have helem_map : ((sC.base.chains .A).map
        (fun g₀ => if g₀.key.isNone then { g₀ with key := some spkKey } else g₀))[ci]? = some g_res :=
      helem_res
    rw [List.getElem?_map] at helem_map
    rcases Option.map_eq_some_iff.mp helem_map with ⟨g₀, hg₀_elem, hg_res_def⟩
    have hg₀_mem : g₀ ∈ sC.base.chains .A := List.mem_of_getElem? hg₀_elem
    have hg₀_none : g₀.key.isNone = true := by
      cases hnone : g₀.key.isNone with
      | true => rfl
      | false =>
        exfalso
        rw [hnone, ite_eq_right Bool.false_ne_true] at hg_res_def
        subst hg_res_def
        have hfind_none := List.findIdx?_eq_none_iff.mp hfind g₀ hg₀_mem
        rw [hg_res_key, beq_self_eq_true] at hfind_none
        exact Bool.noConfusion hfind_none
    rw [hg₀_none, ite_eq_left rfl] at hg_res_def
    have hsrk_eq : h.senderRatchetKey = spkKey := by
      have hk : g_res.key = some spkKey := by rw [← hg_res_def]
      exact Option.some.inj (hg_res_key.symm.trans hk)
    have hdecT : decT h.senderRatchetKey = some (Dh.dh x₀ Dh.base) := by
      rw [hsrk_eq]; exact hdec (Dh.dh x₀ Dh.base)
    have hT_map : ((decT h.senderRatchetKey).map encT).getD dummyKey = h.senderRatchetKey := by
      rw [hdecT, Option.map_some, Option.getD_some, hsrk_eq]
    have hg₀_ep0 : g₀.epoch = 0 := hinv.hcx.hsim.hchainsA.1 g₀ hg₀_mem hg₀_none
    have hg_res_ep0 : g_res.epoch = 0 := by rw [← hg_res_def, hg₀_ep0]
    rcases hinv.hcx.hsim.hchains_sync .A g₀ hg₀_mem with ⟨hg₀_ep_le, hrecv₀, _, v, hvR₀, hsync₀⟩
    have hg_res_ep_tcur : g_res.epoch ≤ (s_fig8.st .A).tcur := by
      rw [hinv.hcx.hsim.htcur .A, hg_res_ep0]
      exact Nat.zero_le _
    have hrecv_res : Party.A.sendsIn g_res.epoch = false := by
      rw [hg_res_ep0]; rfl
    have hvR_res : (s_fig8.st .A).vR g_res.epoch = some v := by
      rw [hg_res_ep0, ← hg₀_ep0]; exact hvR₀
    have hsync_res : ChainSync g_res v := by
      rw [← hg_res_def]
      exact iafs_chainSync_with_key (some spkKey) hsync₀
    have hno_none_res : ∀ g ∈ s_res.chains .A, g.key.isNone = false :=
      resolveSim_chains_no_none' spkKey sC.base .A hinv.hcx.hsim.hchainsB_none
    have hdummy_res : ∀ g ∈ s_res.chains .A, g.key = none → h.senderRatchetKey ≠ dummyKey := by
      intro g hg hgn
      have hgn' := hno_none_res g hg
      simp [hgn] at hgn'
    have hmap_ep : (s_res.chains .A).map (·.epoch) = (sC.base.chains .A).map (·.epoch) :=
      resolveSpkChains_map_epoch spkKey sC.base.chains .A
    have hnodup_res : ((s_res.chains .A).map (·.epoch)).Nodup := by
      rw [hmap_ep, hinv.hcx.hsim.hchainsA_ep]
      exact epListA_nodup (sC.base.mir.epoch .A / 2)
    have hdistinct : ∀ j < (s_res.chains .A).length, j ≠ ci →
        ∀ g_j, (s_res.chains .A)[j]? = some g_j → g_j.epoch ≠ g_res.epoch :=
      fun j hj_lt hj_ne g_j hg_j => nodup_distinct_epoch hnodup_res helem_res j hj_lt hj_ne g_j hg_j
    let st := s_fig8.st .A
    let g_ghost := toGhost P s_res .A st
    let rk := if inReceiveOnlyEpoch sC.base.mir .A then
        match st.γ with
        | .pub T => ((rootPRNG P.C.F encPt).up st.root (Dh.dh (ec .A) T)).1
        | _ => g_ghost.session.rootKey
      else g_ghost.session.rootKey
    let sc := if inReceiveOnlyEpoch sC.base.mir .A then
        match st.γ with
        | .pub T => some ⟨KeyPair.generate P.C (ec .A), ⟨((rootPRNG P.C.F encPt).up st.root (Dh.dh (ec .A) T)).2, 0⟩⟩
        | _ => g_ghost.session.senderChain
      else g_ghost.session.senderChain
    let pn := if inReceiveOnlyEpoch sC.base.mir .A then
        match st.γ with
        | .pub _ => BitVec.ofNat 32 (sC.base.mir.idx .A - 1)
        | _ => g_ghost.session.previousCounter
      else g_ghost.session.previousCounter
    have hst_R_eq : s_R.st .A = withEager g_ghost rk sc pn := by
      rw [hinv.hcx.hsim.hst_R .A]
      exact expectedGhost_eq_withEager P Dh encPt spkKey sC.base .A st (ec .A)
    let i := h.counter.toNat + 1
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let c₀ : Fig8C Pt := ((g_res.epoch, decT h.senderRatchetKey), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
    let pos₀ : SM.Pos := ⟨.B, g_res.epoch, i⟩
    let mir'₀ := sC.base.mir.accept .A () pos₀
    have hmir'₀_ep : mir'₀.epoch .A = sC.base.mir.epoch .A := by
      have hep := accept_epoch_eq_of_le sC.base.mir .A () pos₀ (by dsimp only [pos₀]; rw [hg_res_ep0]; exact Nat.zero_le _)
      exact congrFun hep .A
    have hstep_res := fun rc =>
      receive_knownChain_withEager_toGhost_eq P Dh encPt encT idOf lam hid s_res .A st
        (hinv.hcx.hsim.hst_id .A) w hlen h body hparse haddrs pq' salt hspqr hpan ci hfind_res hdummy_res
        g_res helem_res hg_res_ep_tcur hrecv_res v hvR_res hsync_res (decT h.senderRatchetKey) hT_map
        hdistinct mir'₀ hmir'₀_ep rk sc pn rc
    have hguard_B : ((sC.base.mir.inTransit Party.B w).isSome || !sC.base.mir.safeInj 3 || !ratchetKeyAdmissible P.codec decT encT w) = false := hguard
    have htr_mir : (sC.base.mir.inTransit Party.B w).isSome = false := by
      revert hguard_B; cases (sC.base.mir.inTransit Party.B w).isSome <;> simp
    have hsafe_mir : sC.base.mir.safeInj 3 = true := by
      revert hguard_B; cases (sC.base.mir.inTransit Party.B w).isSome <;> cases sC.base.mir.safeInj 3 <;> simp
    have hguard_R : (s_R.win || (s_R.inTransit Party.B w).isSome || !s_R.safeInj 3 ||
        !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
      rw [hinv.hcx.hsim.hmeta.hwin_R, hinv.hcx.hsim.hmeta.inTransit_R_isSome, hinv.hcx.hsim.hmeta.safeInj_R]
      simpa [configR1OnCurve] using hguard_B
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    have hfig0_eq : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st
        ((g_res.epoch, decT h.senderRatchetKey), h.counter.toNat + 1,
          (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) =
            sm.receive st c₀ := rfl
    have hrcv_none_or_some :
        (∀ rc, P.receive (s_R.st .A) w rc = none) ∨
        (g_res.rejects i = false ∧ ∃ st' t' i' pub m, sm.receive st c₀ = some (st', t', i', (pub, m))) := by
      by_cases hrej : g_res.rejects i = true
      · refine Or.inl fun rc => ?_
        rw [hst_R_eq]
        exact (hstep_res rc).1 hrej
      · have hrej_f : g_res.rejects i = false := Bool.eq_false_iff.mpr hrej
        cases hfig0 : sm.receive st c₀ with
        | none =>
          refine Or.inl fun rc => ?_
          have h2 := (hstep_res rc).2 hrej_f
          dsimp only at h2
          rw [hfig0_eq, hfig0] at h2
          dsimp only at h2
          rw [hst_R_eq]
          exact h2
        | some val =>
          rcases val with ⟨st', t', i', ⟨pub, m⟩⟩
          exact Or.inr ⟨hrej_f, st', t', i', pub, m, rfl⟩
    have hfind_hon : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Party.A.other) = none := by
      cases hf : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Party.A.other) with
      | none => rfl
      | some wc =>
        exfalso
        have hmem_wc := List.mem_of_find?_eq_some hf
        have hpred_wc := List.find?_some hf
        simp only [Bool.and_eq_true, beq_iff_eq] at hpred_wc
        rcases wc with ⟨w_wc, c_wc⟩
        dsimp only at hpred_wc
        rcases hpred_wc with ⟨rfl, hsend_wc⟩
        have hinv_wc := hinv.hcx.hsim.hhon (w_wc, c_wc) hmem_wc
        rcases hinv_wc.1 with ⟨_, _, hge1, _, _, _, _, h_wc, body_wc, hparse_wc, _, hsrk_wc, _, _⟩
        have hhb : (h_wc, body_wc) = (h, body) := Option.some.inj (hparse_wc.symm.trans hparse)
        rcases Prod.mk.inj hhb with ⟨rfl, rfl⟩
        have hdh_eq : Dh.dh (epExp c_wc.1.1) Dh.base = Dh.dh (epExp 0) Dh.base := by
          rw [hinv.hcx.hsim.hepExp0]
          exact hinj (hsrk_wc.symm.trans hsrk_eq)
        have ht_eq0 : c_wc.1.1 = 0 :=
          hinv.hcx.hsim.hcoll c_wc.1.1 0 hinv_wc.2.1 (Nat.zero_le _) hdh_eq
        dsimp only at hge1
        omega
    let s₁ : SimState PQ Pt ℓ := { sC.base with amb := sC.base.amb + 1 }
    let sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := s₁ }
    have hs₁_stop : ({ sC.base with amb := sC.base.amb + 1, stopped := false } : SimState PQ Pt ℓ) = s₁ := by
      dsimp only [s₁]; exact congrArg (SimState.mk _ _ _ _ _ _ _) hinv.hcx.hsim.hmeta.hstop.symm
    have hhon_wire : ∀ wc ∈ s₁.honest, wc.1 = LibsignalSim.toWire wc.2 :=
      fun wc hwc => (hinv.hcx.hsim.hhon wc hwc).1.1
    rcases hrcv_none_or_some with hrcv_none | ⟨hrej_f, st', t', i', pub, m, hfig0⟩
    · have huse_none : simRecvUsesCoin P encT decT none .A w false (sC.base, s_fig8) = false :=
        simRecvUsesCoin_none P encT decT .A w false (sC.base, s_fig8)
      have hnone_div : ((none : Option ℕ) == some sC.base.amb) = false := rfl
      have hrcv_R : ∀ rc, (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st .A) w rc = none := by
        intro rc
        unfold libsignalSessionScheme
        dsimp only
        rw [hrcv_none rc]
        rfl
      by_cases hinw_j : (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
      · have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none .A w false 0 (sC.base, s_fig8) =
            (some .rejected, (s₁, s_fig8)) := by
          unfold simRecvStep
          simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
            hevict, hzero, hamb_b, hnone_div,
            show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hinw_j,
            hs₁_stop]
        have hstepC_none : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false .A w false (sC, s_fig8, false) =
            (some .rejected, (sC₁, s_fig8, false)) := by
          unfold simRecvStepCGen
          simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
            Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
            hevict, hzero, hamb_b,
            show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true from hinw_j,
            hs₁_stop]
          rfl
        have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8) = false :=
          simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8)
            (by rw [hstep_none]; exact hinv.hcx.hsim.hmeta.hstop)
        have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (.A, w)))
            (sC, s_fig8, false) ec =
            pure (some .rejected, ((sC₁, s_fig8, false), ec)) :=
          stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none .A w
            (sC, s_fig8, false) ec hinv.hcx.hsim.hec huse_none hstops_none _ hstepC_none rfl
        exact closeByStateCTrack_inject_amb_reject (hnpW := recvPanicsW_eq_false_of P .A w sC.base hlen hparse hpan)
          P K Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
          .A w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0 hnone_eager
          (ih (some .rejected))
      · have hinw_j_f : (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = false :=
          Bool.eq_false_iff.mpr hinw_j
        have hinw : inReceiveOnlyEpoch sC.base.mir .A = false := by
          revert hinw_j_f; cases inReceiveOnlyEpoch sC.base.mir .A <;> simp
        have hjump_f : (decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = false := by
          revert hinw_j_f; cases inReceiveOnlyEpoch sC.base.mir .A <;> simp
        let c_new : Fig8C Pt :=
          ((sC.base.mir.epoch .A + 1, some (Dh.dh x₀ Dh.base)), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
        have htoWire_new : LibsignalSim.toWire c_new = w :=
          toWire_raw_eq w hlen (sC.base.mir.epoch .A + 1) (some (Dh.dh x₀ Dh.base)) i (effectiveHkdfSalt32 salt)
        have hfwd_new : fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8 =
            injectPure sm 3 (qep + 1) SM.Config.h1 .A c_new s_fig8 :=
          fwdPure_of_inTransit_false sm 3 (qep + 1) SM.Config.h1 s₁ .A w c_new s_fig8 hhon_wire htoWire_new htr_mir
        have htr_fig8_new : (s_fig8.inTransit Party.B c_new).isSome = false :=
          inTransit_fig8_isSome_of_toWire hinv.hcx.hsim.hmeta .A w c_new htoWire_new htr_mir
        have hguard_fig8_new : (s_fig8.win || (s_fig8.inTransit Party.B c_new).isSome || !s_fig8.safeInj 3) = false := by
          rw [hinv.hcx.hsim.hmeta.hwin_fig8, htr_fig8_new, hinv.hcx.hsim.hmeta.safeInj_fig8 3, hsafe_mir]
          rfl
        cases hfig_new : sm.receive (s_fig8.st .A) c_new with
        | none =>
          have hinj_new : injectPure sm 3 (qep + 1) SM.Config.h1 .A c_new s_fig8 = (some .rejected, s_fig8) := by
            unfold injectPure
            dsimp only [Party.other]
            simp [hguard_fig8_new, hfig_new]
          have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none .A w false 0 (sC.base, s_fig8) =
              (some .rejected, (s₁, s_fig8)) := by
            have hT0_b : (some (Dh.dh x₀ Dh.base) == some 0) = false := by rw [← hdecT]; exact hzero
            unfold simRecvStep
            simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
              Bool.false_and, Bool.true_and, Bool.and_false, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
              hevict, hzero, hT0_b, hamb_b, hnone_div,
              hfind_hon, Option.map_none, hdecT,
              show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hinw_j_f,
              hs₁_stop]
            change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8
                    let a := onAnswerPure qep .A w false none h.senderRatchetKey pq' z.1 s₁
                    (a.1, (a.2, z.2))) = (some .rejected, (s₁, s_fig8))
            rw [hfwd_new, hinj_new]
            rfl
          have hstepC_none : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false .A w false (sC, s_fig8, false) =
              (some .rejected, (sC₁, s_fig8, false)) := by
            have hT0_b : (some (Dh.dh x₀ Dh.base) == some 0) = false := by rw [← hdecT]; exact hzero
            unfold simRecvStepCGen
            simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
              Bool.false_and, Bool.true_and, Bool.and_false, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
              hevict, hzero, hT0_b, hamb_b, hdecT,
              show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hinw_j_f,
              hs₁_stop]
            simp only [hfind_hon, Option.map_none]
            change fwdCPure P ℓ Dh encPt encT idOf lam qep false .A w false none h.senderRatchetKey pq' none c_new
              (sC₁, s_fig8, false) = (some .rejected, (sC₁, s_fig8, false))
            unfold fwdCPure
            dsimp only
            change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8
                    let kept' := match z.1 with
                      | some (.accepted _ _ _) => Function.update sC.kept .A (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c_new (sC.kept .A))
                      | _ => sC.kept
                    let a := onAnswerPure qep .A w false none h.senderRatchetKey pq' z.1 s₁
                    (a.1, ({ sC₁ with base := a.2, kept := kept' }, z.2, false))) =
              (some .rejected, (sC₁, s_fig8, false))
            rw [hfwd_new, hinj_new]
            rfl
          have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8) = false :=
            simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8)
              (by rw [hstep_none]; exact hinv.hcx.hsim.hmeta.hstop)
          have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (.A, w)))
              (sC, s_fig8, false) ec =
              pure (some .rejected, ((sC₁, s_fig8, false), ec)) :=
            stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none .A w
              (sC, s_fig8, false) ec hinv.hcx.hsim.hec huse_none hstops_none _ hstepC_none rfl
          exact closeByStateCTrack_inject_amb_reject (hnpW := recvPanicsW_eq_false_of P .A w sC.base hlen hparse hpan)
            P K Inv ℓ Dh encPt encT decT idOf lam qep q r hr δ post x₀
            .A w cont s_R stTrR sC trC s_fig8 ec winBefore epExp hinv hguard hrcv_R hstop0 hnone_eager
            (ih (some .rejected))
        | some val_new =>
          rcases val_new with ⟨st_new, t_new, i_new, ⟨pub_new, m_new⟩⟩
          rcases lFig8_receive_epoch_idx_eq Dh encPt P.C P.codec ℓ encT idOf lam (s_fig8.st .A) c_new hfig_new with
            ⟨ht_new, hi_new⟩
          dsimp only [c_new] at ht_new hi_new
          subst ht_new hi_new
          have htriv_new_mir : sC.base.mir.trivial 3 ⟨.B, sC.base.mir.epoch .A + 1, i⟩ = false :=
            trivial_false_of_newChain_inject hsafe_mir hinv.hcx.hsim.hcomp .A ⟨.B, sC.base.mir.epoch .A + 1, i⟩
              (by dsimp only; omega)
          have htriv_new_fig8 : s_fig8.trivial 3 ⟨.B, sC.base.mir.epoch .A + 1, i⟩ = false := by
            rw [hinv.hcx.hsim.hmeta.trivial_fig8, htriv_new_mir]
          have hnot_gt_new : ¬ ((qep + 1) + 1 < sC.base.mir.epoch .A + 1) := by
            have := hinv.hcx.hsim.hep_le .A
            omega
          have hinj_new : injectPure sm 3 (qep + 1) SM.Config.h1 .A c_new s_fig8 =
              (some .rejected, { s_fig8 with win := true }) := by
            unfold injectPure SM.Config.h1
            dsimp only [Party.other]
            simp only [hguard_fig8_new, Bool.false_eq_true, ↓reduceIte, hfig_new, hnot_gt_new, htriv_new_fig8]
          have hstep_none : simRecvStep P ℓ Dh encPt encT decT idOf lam qep none .A w false 0 (sC.base, s_fig8) =
              (some .rejected, (s₁, { s_fig8 with win := true })) := by
            have hT0_b : (some (Dh.dh x₀ Dh.base) == some 0) = false := by rw [← hdecT]; exact hzero
            unfold simRecvStep
            simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
              Bool.false_and, Bool.true_and, Bool.and_false, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
              hevict, hzero, hT0_b, hamb_b, hnone_div,
              hfind_hon, Option.map_none, hdecT,
              show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hinw_j_f,
              hs₁_stop]
            change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8
                    let a := onAnswerPure qep .A w false none h.senderRatchetKey pq' z.1 s₁
                    (a.1, (a.2, z.2))) = (some .rejected, (s₁, { s_fig8 with win := true }))
            rw [hfwd_new, hinj_new]
            rfl
          have hstepC_none : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false .A w false (sC, s_fig8, false) =
              (some .rejected, (sC₁, { s_fig8 with win := true }, false)) := by
            have hT0_b : (some (Dh.dh x₀ Dh.base) == some 0) = false := by rw [← hdecT]; exact hzero
            unfold simRecvStepCGen
            simp only [hinv.hcx.hsim.hmeta.hstop, hinv.hcx.hsim.hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
              Bool.false_and, Bool.true_and, Bool.and_false, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
              hevict, hzero, hT0_b, hamb_b, hdecT,
              show (inReceiveOnlyEpoch sC.base.mir .A || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hinw_j_f,
              hs₁_stop]
            simp only [hfind_hon, Option.map_none]
            change fwdCPure P ℓ Dh encPt encT idOf lam qep false .A w false none h.senderRatchetKey pq' none c_new
              (sC₁, s_fig8, false) = (some .rejected, (sC₁, { s_fig8 with win := true }, false))
            unfold fwdCPure
            dsimp only
            change (let z := fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ .A c_new s_fig8
                    let kept' := match z.1 with
                      | some (.accepted _ _ _) => Function.update sC.kept .A (Kept.recv (fig := sm) (fs := lFS P.C P.codec ℓ encT idOf 25000) c_new (sC.kept .A))
                      | _ => sC.kept
                    let a := onAnswerPure qep .A w false none h.senderRatchetKey pq' z.1 s₁
                    (a.1, ({ sC₁ with base := a.2, kept := kept' }, z.2, false))) =
              (some .rejected, (sC₁, { s_fig8 with win := true }, false))
            rw [hfwd_new, hinj_new]
            rfl
          have hstops_none : simRecvStops P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8) = false :=
            simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep none .A w false (sC.base, s_fig8)
              (by rw [hstep_none]; exact hinv.hcx.hsim.hmeta.hstop)
          have hstepSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (.A, w))) (sC, s_fig8, false) ec =
              pure (some .rejected, ((sC₁, { s_fig8 with win := true }, false), ec)) :=
            stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none .A w
              (sC, s_fig8, false) ec hinv.hcx.hsim.hec huse_none hstops_none _ hstepC_none rfl
          have hstepSimT : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none
              (.inl (.inr (.A, w))) (sC, s_fig8, false) trC ec =
              pure (some .rejected, (((sC₁, { s_fig8 with win := true }, false), trC), ec)) := by
            change stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (.A, w)))
              (sC, s_fig8, false) ec >>= _ = _
            rw [hstepSim, pure_bind]
          unfold CloseByStateCTrack
          refine closeByRefinesH_of_win_eq_one (k₀ := 0) (by simp) ?_
          unfold runWinAtCTrack
          rw [runSimCEagerTrack_inr_bind, hstepSimT, pure_bind]
          exact evalDist_runSimCEagerTrack_win_true P K ℓ Dh encPt encT decT idOf lam qep
            (cont (some .rejected)) (sC₁, { s_fig8 with win := true }, false) trC ec rfl _
            (fun z hz => by simp [hz])
    · have h2_0 := (hstep_res 0).2 hrej_f
      dsimp only at h2_0
      rw [hfig0_eq, hfig0] at h2_0
      dsimp only at h2_0
      rcases h2_0 with ⟨ht', hi', _, _, m_raw, hm_raw, _⟩
      let st_R' :=
        withEager
          (toGhost P
            { s_res with
              mir := mir'₀,
              pq := Function.update s_res.pq .A pq',
              unackA := s_res.unackA && Party.A != Party.A,
              chains := Function.update s_res.chains .A ((s_res.chains .A).set ci (g_res.accept i)) }
            .A st')
          rk sc pn
      have hguard_D0 : (s_R.win || (s_R.inTransit Party.B w).isSome || !s_R.safeInj 3 ||
          !((configEpoch0Distinguisher (PQ := PQ) (ℓ := ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false :=
        hguard_R
      have hnot_gt0' : ¬ (qep + 1 < 0) := by omega
      have hcorr_R : (.B, 0) ∉ s_R.corrs := by
        rw [hinv.hcx.hsim.hmeta.hcorrs_R]
        exact hspk_corr_of_simInvC P (InvB Inv q r) ℓ Dh encPt encT qep q r x₀ s_R sC.base s_fig8 ec winBefore epExp hinv.hcx.hsim hg₀_mem hg₀_none
      by_cases htriv0 : sC.base.mir.trivial 3 ⟨.B, 0, i⟩ = true
      · have htriv_R0 : s_R.trivial 3 ⟨.B, 0, i⟩ = true := by
          rw [hinv.hcx.hsim.hmeta.trivial_R, htriv0]
        let s_R' := s_R.accept .A st_R' ⟨.B, 0, i⟩
        have hstepD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (.A, w))) s_R =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
              pure (some (.accepted 0 i (some m)), s_R')) := by
          rw [stepR_inject_eq]
          dsimp only [Party.other]
          simp only [hguard_D0, Bool.false_eq_true, ↓reduceIte]
          congr 1; funext rc
          have h2_rc := (hstep_res rc).2 hrej_f
          dsimp only at h2_rc
          rw [hfig0_eq, hfig0] at h2_rc
          dsimp only at h2_rc
          rcases h2_rc with ⟨_, _, _, _, m_raw_rc, hm_raw_rc, hrec_rc⟩
          have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st .A) w rc =
              some (st_R', 0, i, m) := by
            unfold libsignalSessionScheme
            dsimp only
            rw [hst_R_eq, hrec_rc]
            dsimp only [Option.map]
            rw [← hm_raw_rc, hg_res_ep0]
          unfold injectRPure configEpoch0Distinguisher
          dsimp only [Party.other]
          simp only [hguard_D0, hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R, hnot_gt0', htriv_R0]
          rfl
        have hsafe_R : s_R.safeInj 3 = true := by
          rw [hinv.hcx.hsim.hmeta.safeInj_R, hsafe_mir]
        have hcomp_R : ∀ p ∈ s_R.comp, SM.healedBy s_R.tL 3 p.epoch = false := by
          rw [hinv.hcx.hsim.hmeta.hcomp_R, hinv.hcx.hsim.hmeta.htL_R]
          exact hinv.hcx.hsim.hcomp
        have heps0 : eps0Cond s_R' :=
          eps0Cond_of_inject_epoch0' hsafe_R htriv_R0 hcomp_R hcorr_R (by dsimp only [i]; omega)
        exact closeByStateCTrack_inr_eps0_const_rc P K ℓ Dh encPt encT decT idOf lam qep q δ post
          .A w cont s_R s_R' stTrR sC trC s_fig8 false ec winBefore (some (.accepted 0 i (some m))) hstepD0 heps0
      · have htriv0_f : sC.base.mir.trivial 3 ⟨.B, 0, i⟩ = false := Bool.eq_false_iff.mpr htriv0
        have htriv_R0 : s_R.trivial 3 ⟨.B, 0, i⟩ = false := by
          rw [hinv.hcx.hsim.hmeta.trivial_R, htriv0_f]
        let s_R' := { s_R with win := true }
        have hstepD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
            (.inl (.inr (.A, w))) s_R =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ =>
              pure (some .rejected, s_R')) := by
          rw [stepR_inject_eq]
          dsimp only [Party.other]
          simp only [hguard_D0, Bool.false_eq_true, ↓reduceIte]
          congr 1; funext rc
          have h2_rc := (hstep_res rc).2 hrej_f
          dsimp only at h2_rc
          rw [hfig0_eq, hfig0] at h2_rc
          dsimp only at h2_rc
          rcases h2_rc with ⟨_, _, _, _, m_raw_rc, hm_raw_rc, hrec_rc⟩
          have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st .A) w rc =
              some (st_R', 0, i, m) := by
            unfold libsignalSessionScheme
            dsimp only
            rw [hst_R_eq, hrec_rc]
            dsimp only [Option.map]
            rw [← hm_raw_rc, hg_res_ep0]
          unfold injectRPure configEpoch0Distinguisher
          dsimp only [Party.other]
          simp only [hguard_D0, hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R, hnot_gt0', htriv_R0]
          rfl
        have heps0 : eps0Cond s_R' := Or.inr ⟨rfl, hcorr_R⟩
        exact closeByStateCTrack_inr_eps0_const_rc P K ℓ Dh encPt encT decT idOf lam qep q δ post
          .A w cont s_R s_R' stTrR sC trC s_fig8 false ec winBefore (some .rejected) hstepD0 heps0

end CryptoGames.LibsignalSM.Proofs.Refinement

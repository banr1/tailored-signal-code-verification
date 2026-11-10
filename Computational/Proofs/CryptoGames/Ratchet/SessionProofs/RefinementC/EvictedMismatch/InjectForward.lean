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
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.EvictedMismatch.FigWin
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Reject

/-!
# Evicted salt mismatch on inject: forward branch

Proves `closeByStateC_inject_evictedMismatch_forward`, handling an injected wire with an evicted salt mismatch outside the receive-only window when the counter is in range.
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
set_option autoImplicit false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

private theorem o2i4mf_fwdEvictCPure_inject_rejected
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (T_key : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g g' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (hfwd : fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1
      sC'.base Q c' g = (some .rejected, g')) :
    fwdEvictCPure P ℓ Dh encPt encT idOf lam qep false Q w false T_key pq' c' (sC', g, fl) =
      (some .rejected, (sC', g', fl)) := by
  unfold fwdEvictCPure fwdCPure
  dsimp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hfwd]
  rfl

/-- On an injected wire with an evicted salt mismatch outside `inReceiveOnlyEpoch` and counter in range, `libsignalToModularSchemeSim` forwards `c'` to Fig. 8, which either rejects on both sides or wins by non-trivial injection. -/
theorem closeByStateC_inject_evictedMismatch_forward {α : Type} (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
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
      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true)
    (c : Fig8C Pt)
    (hfind_hon : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) =
      some (w, c))
    (hmis : c.2.2.2 ≠ effectiveHkdfSalt32 salt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hbound : ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1))
    (ih : ∀ ans s_R' sC' s_fig8' fl' ec' winBefore' epExp',
      SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q (r - 1) x₀ s_R' sC' s_fig8' ec' winBefore'
        epExp' →
      CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' sC' s_fig8' fl'
        ec' winBefore') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inr (Q, w))))) >>= cont)
      s_R sC s_fig8 false ec winBefore := by
  letI : DecidableEq PQ := Classical.decEq PQ
  have hsim := hinv.hsim
  have hmeta := hsim.hmeta
  have hM := libX25519Rel_model hX
  let spkKey := encT (Dh.dh x₀ Dh.base)
  let s_res := resolveSim spkKey sC.base
  have hmem_hon : (w, c) ∈ sC.base.honest := List.mem_of_find?_eq_some hfind_hon
  rcases hsim.hhon (w, c) hmem_hon with ⟨hc_inv, hc_max, _, _⟩
  rcases honestEntryInvC_eq_raw P (InvB Inv q r) Dh encT epExp hc_inv hparse with
    ⟨_, hsrk, _, _⟩
  have hc_ge1 : 1 ≤ c.1.1 := hc_inv.2.2.1
  let T := Dh.dh (epExp c.1.1) Dh.base
  have hdecT : decT h.senderRatchetKey = some T := by
    rw [hsrk, hdec]
  have hencT : encT T = h.senderRatchetKey := hsrk.symm
  have hT_ne0 : T ≠ 0 := hM.dh_ne_zero (epExp c.1.1) Dh.base hM.base_ne_zero
  have hzero : (decT h.senderRatchetKey == some 0) = false := by
    rw [hdecT]
    exact beq_eq_false_iff_ne.mpr (fun h0 => hT_ne0 (Option.some.inj h0))
  have hT0_b : (some T == (some 0 : Option Pt)) = false := by
    rw [← hdecT]; exact hzero
  have hsrk_ne_spk : h.senderRatchetKey ≠ spkKey := by
    dsimp only [spkKey]
    rw [hsrk, ← hsim.hepExp0]
    intro heq
    have hcoll := hsim.hcoll c.1.1 0 hc_max (Nat.zero_le _) (hinj heq)
    omega
  have hfind_res : (s_res.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none := by
    dsimp only [s_res]
    rw [resolveSim_findIdx_eq_of_ne spkKey sC.base Q h.senderRatchetKey hsrk_ne_spk]
    exact hfind
  have hst_R_eq : s_R.st Q = toGhost P s_res Q (s_fig8.st Q) := by
    rw [hsim.hst_R Q, expectedGhost_of_inWin_false P Dh encPt spkKey sC.base Q (s_fig8.st Q) (ec Q) hinw]
  rcases hsim.hspur Q with ⟨rk_base, T_base, _, hninw, _⟩
  rcases hninw hinw with ⟨hγ, _, ⟨vS, hvS, _⟩⟩
  have hrecv : Q.sendsIn ((s_fig8.st Q).tcur + 1) = false := by
    rw [hsim.htcur Q]
    exact sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
  have hno_none_res : ∀ g ∈ s_res.chains Q, g.key.isNone = false :=
    resolveSim_chains_no_none' spkKey sC.base Q hsim.hchainsB_none
  have hdummy : ∀ g ∈ s_res.chains Q, g.key = none → h.senderRatchetKey ≠ dummyKey := by
    intro g hg hgn
    have hgn' := hno_none_res g hg
    simp [hgn] at hgn'
  have hchains_ep : ∀ g ∈ s_res.chains Q, g.epoch ≠ (s_fig8.st Q).tcur + 1 := by
    intro g hg
    have hmem_ep : g.epoch ∈ (resolveSpkChains spkKey sC.base.chains Q).map (·.epoch) := List.mem_map_of_mem hg
    rw [resolveSpkChains_map_epoch spkKey sC.base.chains Q, List.mem_map] at hmem_ep
    rcases hmem_ep with ⟨g₀, hg₀, hgep⟩
    have hle := (hsim.hchains_sync Q g₀ hg₀).1
    have htcur := hsim.htcur Q
    omega
  let i := h.counter.toNat + 1
  let t := (s_fig8.st Q).tcur + 1
  let pos : SM.Pos := ⟨Q.other, t, i⟩
  let mir' := sC.base.mir.accept Q () pos
  have hmir'_ep : mir'.epoch Q = (s_fig8.st Q).tcur + 1 := by
    have htcur := (hsim.htcur Q).symm
    unfold mir' SM.GameState.accept SM.GameState.delete
    dsimp only [pos, t]
    rw [Function.update_self, htcur]
    exact Nat.max_eq_right (Nat.le_succ _)
  have hstep_all := fun rc =>
    receive_newChain_toGhost_eq P Dh encPt encT idOf lam hX hid
      s_res Q (s_fig8.st Q) (hsim.hst_id Q) (hsim.htcur Q).symm hrecv
      (epExp (sC.base.mir.epoch Q)) hγ vS hvS w hlen h body hparse haddrs
      pq' salt hspqr hpan hfind_res hdummy hchains_ep T hT_ne0 hencT mir' hmir'_ep rc
  let g_init : GhostChain := ⟨some h.senderRatchetKey, t, 0, []⟩
  have hjump_f : (decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = false := by
    dsimp only [i]
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    exact ⟨fun h1 => hbound (Or.inl h1), fun h2 => hbound (Or.inr h2)⟩
  have hrej_init_f : g_init.rejects i = false := by
    unfold GhostChain.rejects
    dsimp only [g_init]
    have hi_pos : ¬ i ≤ 0 := by dsimp only [i]; omega
    simp only [hi_pos, ↓reduceIte, Nat.sub_zero]
    exact hjump_f
  have hevict' : c.1.1 ≠ sC.base.mir.epoch Q + 1 := by
    simpa [hfind_hon] using hevict
  have huse : ∀ k, simRecvUsesCoin P encT decT k Q w false (sC.base, s_fig8) = false := by
    intro k
    unfold simRecvUsesCoin
    simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon, hevict']
  have hres : ∀ k, simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w false 0
      (sC.base, s_fig8) = (some .rejected, (sC.base, s_fig8)) := by
    intro k
    unfold simRecvStep
    simp [hmeta.hstop, hmeta.hwin_mir, hguard, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon, hevict']
  have hstops : ∀ k, simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w false
      (sC.base, s_fig8) = false := fun k =>
    simRecvStops_eq_false_of P ℓ Dh encPt encT decT idOf lam qep k Q w false (sC.base, s_fig8)
      (by rw [hres k]; exact hmeta.hstop)
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  let c' : Fig8C Pt := ((sC.base.mir.epoch Q + 1, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt)))
  have hc_eq : ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = c' := by
    dsimp only [t, c']; rw [hsim.htcur Q]
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hhon_wire : ∀ wc ∈ sC.base.honest, wc.1 = LibsignalSim.toWire wc.2 :=
    fun wc hwc => (hsim.hhon wc hwc).1.1
  have htr_mir : (sC.base.mir.inTransit Q.other w).isSome = false := by
    revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> simp
  have hsafe_mir : sC.base.mir.safeInj 3 = true := by
    revert hguard; cases (sC.base.mir.inTransit Q.other w).isSome <;> cases sC.base.mir.safeInj 3 <;> simp
  have htoWire : LibsignalSim.toWire c' = w :=
    toWire_raw_eq w hlen (sC.base.mir.epoch Q + 1) (some T) i (effectiveHkdfSalt32 salt)
  have htr_fig8 : (s_fig8.inTransit Q.other c').isSome = false :=
    inTransit_fig8_isSome_of_toWire hmeta Q w c' htoWire htr_mir
  have hguard_fig8 : (s_fig8.win || (s_fig8.inTransit Q.other c').isSome || !s_fig8.safeInj 3) = false := by
    rw [hmeta.hwin_fig8, htr_fig8, hmeta.safeInj_fig8 3, hsafe_mir]
    rfl
  have hguard_R : (s_R.win || (s_R.inTransit Q.other w).isSome || !s_R.safeInj 3 ||
      !((configR1OnCurve (St := GhostState PQ) (Msg := Plain ℓ) (ratchetKeyAdmissible P.codec decT encT)).injOK w)) = false := by
    rw [hmeta.hwin_R, hmeta.inTransit_R_isSome, hmeta.safeInj_R]
    simpa [configR1OnCurve] using hguard
  let spkAmb := (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))
  let s₁ : SimState PQ Pt ℓ :=
    if spkAmb then { sC.base with amb := sC.base.amb + 1 } else sC.base
  have hs₁_stop : ({ sC.base with amb := sC.base.amb + 1, stopped := false } : SimState PQ Pt ℓ) =
      { sC.base with amb := sC.base.amb + 1 } := by
    generalize hs : sC.base = sb
    have hst : sb.stopped = false := hs ▸ hmeta.hstop
    cases sb; dsimp only at hst; subst hst; rfl
  have hx₁_eq :
      (if (Q == Party.A && (sC.base.chains Q).any fun x => x.key.isNone) = true then
        ({ sC with base := { sC.base with amb := sC.base.amb + 1, stopped := false } }, s_fig8, false)
      else (sC, s_fig8, false)) =
      ({ sC with base := s₁ }, s_fig8, false) := by
    rw [hs₁_stop]
    dsimp only [s₁, spkAmb]
    split_ifs <;> rfl
  have hs₁_hon : s₁.honest = sC.base.honest := by
    dsimp only [s₁]; split_ifs <;> rfl
  have hs₁_mir : s₁.mir = sC.base.mir := by
    dsimp only [s₁]; split_ifs <;> rfl
  have hfwd : fwdPure sm 3 (qep + 1) SM.Config.h1 s₁ Q c' s_fig8 =
      injectPure sm 3 (qep + 1) SM.Config.h1 Q c' s_fig8 := by
    refine fwdPure_of_inTransit_false sm 3 (qep + 1) SM.Config.h1 s₁ Q w c' s_fig8 ?_ htoWire ?_
    · rw [hs₁_hon]; exact hhon_wire
    · rw [hs₁_mir]; exact htr_mir
  have hmis_b : ((((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
      fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true) = false := by
    rw [hfind_hon]
    simp [hmis]
  cases hfig : sm.receive (s_fig8.st Q) c' with
  | none =>
    have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c' s_fig8 = (some .rejected, s_fig8) := by
      unfold injectPure
      simp [hguard_fig8, hfig]
    have hfig_t : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
        (((s_fig8.st Q).tcur + 1, some T), h.counter.toNat + 1,
          (w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) = none := by
      change sm.receive (s_fig8.st Q) ((t, some T), (i, ((ser, tag), effectiveHkdfSalt32 salt))) = none
      rw [hc_eq, hfig]
    have hrcv_P : ∀ rc, P.receive (s_R.st Q) w rc = none := by
      intro rc
      have h2_rc := (hstep_all rc).2 hrej_init_f
      dsimp only at h2_rc
      rw [hfig_t] at h2_rc
      rw [hst_R_eq, h2_rc]
    have hstepC : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
        (some .rejected, ({ sC with base := s₁ }, s_fig8, false)) := by
      unfold simRecvStepCGen
      simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hevict, hmis_b, hzero, hT0_b, hinw, Bool.false_or,
        show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
        hdecT, hx₁_eq]
      exact o2i4mf_fwdEvictCPure_inject_rejected P ℓ Dh encPt encT idOf lam qep Q w
        h.senderRatchetKey pq' c' { sC with base := s₁ } s_fig8 s_fig8 false
        (by dsimp only; rw [hfwd, hinj_fig8])
    by_cases hspk : spkAmb = true
    · have hs₁_eq : s₁ = { sC.base with amb := sC.base.amb + 1 } := by
        dsimp only [s₁]; simp [hspk]
      rw [hs₁_eq] at hstepC
      have hstep_eager : ∀ k, stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w)))
          (sC, s_fig8, false) ec =
          pure (some .rejected, (({ sC with base := { sC.base with amb := sC.base.amb + 1 } }, s_fig8, false), ec)) :=
        fun k => stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep k Q w
          (sC, s_fig8, false) ec hsim.hec (huse k) (hstops k) _ hstepC rfl
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          (.inl (.inr (Q, w))) s_R =
          (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (some .rejected, s_R)) := by
        rw [stepR_inject_eq]
        simp only [hguard_R, Bool.false_eq_true, ↓reduceIte]
        congr 1; funext rc
        have hrcv_R : (libsignalSessionScheme P ℓ encPt lam).receive (s_R.st Q) w rc = none := by
          unfold libsignalSessionScheme; dsimp only; rw [hrcv_P rc]; rfl
        unfold injectRPure
        simp only [hguard_R, Bool.false_eq_true, ↓reduceIte, hrcv_R]
      have hD0 := stepR_inject_configD0_eq_configR1OnCurve P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep Q w s_R
        (Or.inr fun rc _ _ _ _ h => by unfold libsignalSessionScheme at h; dsimp only at h; rw [hrcv_P rc] at h; cases h)
      have hinv' := simInvCX_inject_amb_reject P Inv ℓ Dh encPt encT idOf lam qep q r hr x₀
        s_R sC s_fig8 ec winBefore epExp hinv rfl
      exact closeByStateC_inr_amb_noStop P ℓ Dh encPt encT decT idOf lam qep q δ post
        (.inl (.inr (Q, w))) cont s_R sC { sC with base := { sC.base with amb := sC.base.amb + 1 } }
        s_fig8 s_fig8 false false ec ec winBefore (some .rejected)
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) (fun _ => s_R)
        hD0 hstepR (hstep_eager none) (hstep_eager (some sC.base.amb))
        rfl hmeta.hstop le_rfl
        (fun _ => ih (some .rejected) s_R { sC with base := { sC.base with amb := sC.base.amb + 1 } }
          s_fig8 false ec _ epExp hinv')
    · have hspk_f : spkAmb = false := Bool.eq_false_iff.mpr hspk
      have hs₁_eq : s₁ = sC.base := by
        dsimp only [s₁]; simp [hspk_f]
      rw [hs₁_eq] at hstepC
      exact closeByStateC_inject_reject_same P Inv ℓ Dh encPt encT decT idOf lam qep q r δ post x₀
        Q w cont s_R sC s_fig8 ec winBefore epExp hinv hguard hrcv_P huse hres hstepC ih
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
    have ht_eq : t = sC.base.mir.epoch Q + 1 := by dsimp only [t]; rw [hsim.htcur Q]
    subst ht' hi'
    have hnot_gt : ¬ (qep + 1 < t) := by
      have hep_le := hsim.hep_le Q
      omega
    have hnot_gt_fig8 : ¬ ((qep + 1) + 1 < t) := by omega
    have htriv_f : sC.base.mir.trivial 3 ⟨Q.other, t, i⟩ = false :=
      trivial_false_of_newChain_inject hsafe_mir hsim.hcomp Q ⟨Q.other, t, i⟩
        (by dsimp only; omega)
    have htriv_fig8 : s_fig8.trivial 3 ⟨Q.other, t, i⟩ = false := by
      rw [hmeta.trivial_fig8, htriv_f]
    let s_fig8' := { s_fig8 with win := true }
    have hinj_fig8 : injectPure sm 3 (qep + 1) SM.Config.h1 Q c' s_fig8 =
        (some .rejected, s_fig8') := by
      unfold injectPure
      simp only [hguard_fig8, Bool.false_eq_true, ↓reduceIte, hfig,
        show ¬ (qep + 1 + 1 < (s_fig8.st Q).tcur + 1) from hnot_gt_fig8,
        show s_fig8.trivial 3 ⟨Q.other, (s_fig8.st Q).tcur + 1, h.counter.toNat + 1⟩ = false from htriv_fig8]
      rfl
    have hstepC : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false (sC, s_fig8, false) =
        (some .rejected, ({ sC with base := s₁ }, s_fig8', false)) := by
      unfold simRecvStepCGen
      simp only [hmeta.hstop, hmeta.hwin_mir, hguard, Bool.false_eq_true, ↓reduceIte,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, hlen, hparse, haddrs, hspqr, hpan, hfind,
        hevict, hmis_b, hzero, hT0_b, hinw, Bool.false_or,
        show (decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = false from hjump_f,
        hdecT, hx₁_eq]
      exact o2i4mf_fwdEvictCPure_inject_rejected P ℓ Dh encPt encT idOf lam qep Q w
        h.senderRatchetKey pq' c' { sC with base := s₁ } s_fig8 s_fig8' false
        (by dsimp only; rw [hfwd, hinj_fig8])
    have hnone_eager : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w)))
        (sC, s_fig8, false) ec =
        pure (some .rejected, (({ sC with base := s₁ }, s_fig8', false), ec)) :=
      stepSimCEager_inject_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w
        (sC, s_fig8, false) ec hsim.hec (huse none) (hstops none) _ hstepC
        (by dsimp only; rw [hs₁_mir])
    exact closeByStateC_inr_fig8_win P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inl (.inr (Q, w))) cont s_R sC { sC with base := s₁ } s_fig8 s_fig8' false false ec ec winBefore
      (some .rejected) hnone_eager rfl

end CryptoGames.LibsignalSM.Proofs.Refinement


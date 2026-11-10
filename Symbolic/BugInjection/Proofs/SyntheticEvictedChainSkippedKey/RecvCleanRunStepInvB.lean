/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvA
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSt
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGamma
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.Initiate.PostTrace
import Symbolic.Proofs.Swarm.CREF.SendWire.ModelSteps
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Clean-Run Prefix Step Agreement: Call 0 (`aliceStart`)

Proves Call 0 (`aliceStart`) step agreement for the clean-run prefix. `ev0_draws_pin` pins the three
fresh draws (`ek`, Kyber entropy, and `dhsA`) from `DrawsMatch` against the 192-byte `(ev 0).coins`
slice, and `alice_call0_agree` steps `aliceStart` across an arbitrary network prefix `c0.pre` to
establish `ActivePartySt "alice"`, `OnlyAliceDone`, `PkiUnchanged`, and `NoPartyState "bob"`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvB

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace Traceful ExecTraceTypes)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH (BundleHandles AliceHandshakeOut PQXDHEvent)
open DY.Libsignal.TripleRatchet (TRState TREvent isCurrentSnapshot u32Max)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   gamma clamp slice ecKey kyberKey pubBytes secretBytes preKeyWire setupTrace setupPublic
   runSteps stepView aliceVis encDraws encSendEntry pendingPreKey lastSent
   newIndices newRandoms exposures pqExposureAt trExposureAt received rngEntry kyberCoinEntries
   randTerm GhostAndSemMatchSetup GhostWF BytesMatchEntry DrawsMatch OutputsMatch RunMatches
   runWrapped inputKind nextBundleIds)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry TRStE PQEvE at?_append_cases)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs rnd encSt encMsg encSig parse_encMsg aliceOut aliceSt RndE NetE EvT StT)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB dhsA o1 stA0 t4 t4_length)
open Symbolic.Swarm.CREF.TR (gamma_rand gamma_dhPk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned evictedPubOfIdx evictedSecretIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse (ev)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeTrace (r_names_of_fit)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (w0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse
  (ev0KyberEnt ev0_cmd_and_exit ev0_bundle_slices ev0_coins_facts sendCallOf)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunTraceBase
  (setupTrace_eq_t4 encTrGen encTrGen_length encTrGen_le append_len
   at?_append_of_lt at?_append_self_proj at?_append_at le_append_of_le at?_mono)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGhost
  (pqAddrBytes gClean gClean_sigma_lt22 gClean_sigma_22 gClean_sigma_23 gClean_sigma_24
   gamma_KemPk setupRandomsAt_of_fit ghostAndSemMatchSetup_gClean gamma_dhPk_ratchetTs)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunGamma
  (StateBytesAgree stateBytesAgree_aliceStart stateBytesAgree_encrypt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvA
  (PeeledCall stepCoinLen PkiUnchanged pkiUnchanged_t4 pkiUnchanged_runSteps_network
   pkiUnchanged_step_party pki_pin_st pki_pin_reg
   OnlyAliceDone onlyAliceDone_t4 onlyAliceDone_runSteps_network
   onlyAliceDone_iniAliceStartTr onlyAliceDone_messageEncrypt pendingPreKey_eq_of_onlyAliceDone)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvSt
  (NoPartyState noPartyState_setupTrace NoNewPartyState noNewPartyState_trans
   noPartyState_of_noNew noNewPartyState_runSteps_network noNewPartyState_step_other
   ActivePartySt noNewPartyState_preserves_active activePartySt_pin_state
   activePartySt_init activePartySt_of_unique_new)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse.ev

private theorem forall₂_append_inv {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys₁ ys₂ : List β}
    (h : List.Forall₂ R xs (ys₁ ++ ys₂)) :
    xs.take ys₁.length ++ xs.drop ys₁.length = xs ∧
    List.Forall₂ R (xs.take ys₁.length) ys₁ ∧
    List.Forall₂ R (xs.drop ys₁.length) ys₂ := by
  induction ys₁ generalizing xs with
  | nil => simpa using h
  | cons y ys₁ ih =>
    cases xs with
    | nil => cases h
    | cons x xs =>
      cases h with
      | cons hxy hrest =>
        obtain ⟨_, h1, h2⟩ := ih hrest
        exact ⟨List.take_append_drop _ _, .cons hxy h1, h2⟩

private theorem flatten_len_of_all_4 {xs : List HwBytes}
    (h : ∀ x ∈ xs, x.length = 4) :
    xs.flatten.length = 4 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatten_cons, List.length_append, List.length_cons, hx, hxs]
    omega

private theorem flatten_drop_4mul_head? {xs : List HwBytes}
    (h4 : ∀ x ∈ xs, x.length = 4) :
    ∀ {j : Nat} (hj : j < xs.length),
      (xs.flatten.drop (4 * j)).head? = xs[j].head? := by
  induction xs with
  | nil => intro j hj; simp at hj
  | cons x xs ih =>
    intro j hj
    have hx4 : x.length = 4 := h4 x List.mem_cons_self
    have hxs4 : ∀ y ∈ xs, y.length = 4 := fun y hy => h4 y (List.mem_cons_of_mem _ hy)
    cases j with
    | zero =>
      simp only [Nat.mul_zero, List.drop_zero, List.flatten_cons, List.getElem_cons_zero]
      cases x with
      | nil => simp at hx4
      | cons _ _ => rfl
    | succ j' =>
      have hj' : j' < xs.length := Nat.lt_of_succ_lt_succ hj
      simp only [List.flatten_cons, List.getElem_cons_succ]
      rw [show 4 * (j' + 1) = x.length + 4 * j' by omega,
          List.drop_append, List.drop_of_length_le (Nat.le_add_right _ _),
          List.nil_append, Nat.add_sub_cancel_left]
      exact ih hxs4 hj'

/-- Pins the three `aliceStart` fresh draws (`ek`, Kyber entropy, and `dhsA`) from `DrawsMatch`
against `(ev 0).coins`. -/
theorem ev0_draws_pin {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} {ts0 : Nat} {anc : Option Nat}
    (hgwf : GhostWF g visAll)
    (hsub : ∀ w ∈ (rngEntry (randTerm ts0 32) ::
        kyberCoinEntries (randTerm (ts0 + 1) 32) ++
        [{ rngEntry (randTerm (ts0 + 2) 32) with anchor := anc }]), w ∈ visAll)
    (hdr : DrawsMatch evictedI0 r S g
      (rngEntry (randTerm ts0 32) ::
        kyberCoinEntries (randTerm (ts0 + 1) 32) ++
        [{ rngEntry (randTerm (ts0 + 2) 32) with anchor := anc }])
      (ev 0).coins) :
    gamma evictedI0 S g (randTerm ts0 32) = slice (ev 0).coins 0 32 ∧
    gamma evictedI0 S g (randTerm (ts0 + 1) 32) = ev0KyberEnt ∧
    gamma evictedI0 S g (randTerm (ts0 + 2) 32) = slice (ev 0).coins 160 32 := by
  obtain ⟨pieces, _, hpref, hrel⟩ := hdr
  simp only [List.cons_append] at hrel hsub
  cases pieces with
  | nil => cases hrel
  | cons p0 ps1 =>
    cases hrel with
    | cons h0 hrel1 =>
      have hp0_eq : gamma evictedI0 S g (randTerm ts0 32) = p0 := by
        simpa [rngEntry] using h0.2
      have hp0_len : p0.length = 32 := by
        have hmem0 : rngEntry (randTerm ts0 32) ∈ visAll := hsub _ List.mem_cons_self
        have hsig := hgwf.1 _ hmem0 rfl ts0 32 (by decide) (by simp [rngEntry])
        rw [← hp0_eq]; unfold randTerm; rw [gamma_rand]; simpa using hsig
      obtain ⟨hps1_split, hrel_kem, hrel_last⟩ := forall₂_append_inv hrel1
      have hkem_len : (kyberCoinEntries (randTerm (ts0 + 1) 32)).length = 32 := by
        simp [kyberCoinEntries]
      set ps_kem := ps1.take 32
      have hps_kem_eq : ps1.take (kyberCoinEntries (randTerm (ts0 + 1) 32)).length = ps_kem := by
        rw [hkem_len]
      rw [hps_kem_eq] at hrel_kem hps1_split
      rw [hkem_len] at hrel_last hps1_split
      cases hdrop : ps1.drop 32 with
      | nil => rw [hdrop] at hrel_last; cases hrel_last
      | cons p33 ps_rem =>
        rw [hdrop] at hrel_last hps1_split
        cases hrel_last with
        | cons hlast hrem =>
          cases ps_rem with
          | cons _ _ => cases hrem
          | nil =>
            have hp33_eq : gamma evictedI0 S g (randTerm (ts0 + 2) 32) = p33 := by
              simpa [rngEntry] using hlast.2
            have hp33_len : p33.length = 32 := by
              have hmem33 : { rngEntry (randTerm (ts0 + 2) 32) with anchor := anc } ∈ visAll :=
                hsub _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
              have hsig := hgwf.1 _ hmem33 rfl (ts0 + 2) 32 (by decide) (by simp [rngEntry])
              rw [← hp33_eq]; unfold randTerm; rw [gamma_rand]; simpa using hsig
            have hps_kem_len : ps_kem.length = 32 := hrel_kem.length_eq.trans hkem_len
            have hkem_item : ∀ (j : Nat) (hj : j < 32),
                (ps_kem[j]'(by omega)).length = 4 ∧
                (gamma evictedI0 S g (randTerm (ts0 + 1) 32)).length = 32 ∧
                (ps_kem[j]'(by omega)).head? =
                  (gamma evictedI0 S g (randTerm (ts0 + 1) 32))[j]? := by
              intro j hj
              have hget := (List.forall₂_iff_get.mp hrel_kem).2 j
                (by omega) (by rw [hkem_len]; exact hj)
              simp only [List.get_eq_getElem, kyberCoinEntries, List.getElem_map,
                List.getElem_range] at hget
              obtain ⟨_, hlen4, t, ht_eq, hlen32, hhead⟩ := hget
              simp only [List.cons.injEq, and_true] at ht_eq
              subst ht_eq
              exact ⟨hlen4, hlen32, hhead⟩
            have hall4 : ∀ q ∈ ps_kem, q.length = 4 := by
              intro q hq
              obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
              exact (hkem_item j (by omega)).1
            have hflat_kem_len : ps_kem.flatten.length = 128 := by
              rw [flatten_len_of_all_4 hall4, hps_kem_len]
            have hflat_eq : (p0 :: ps1).flatten = p0 ++ (ps_kem.flatten ++ p33) := by
              rw [← hps1_split]; simp [List.flatten_cons, List.flatten_append]
            obtain ⟨coins_Fact_len, _, _, hent_len, _, hent_idx⟩ := ev0_coins_facts
            obtain ⟨tail_rem, hcoins_eq⟩ := hpref
            rw [hflat_eq] at hcoins_eq
            have htail_nil : tail_rem = [] := by
              have hlen := congrArg List.length hcoins_eq
              simp only [List.length_append, hp0_len, hflat_kem_len, hp33_len,
                coins_Fact_len] at hlen
              exact List.eq_nil_of_length_eq_zero (by omega)
            rw [htail_nil, List.append_nil] at hcoins_eq
            have hs0 : slice (ev 0).coins 0 32 = p0 := by
              rw [← hcoins_eq]; unfold slice; simp only [List.drop_zero]
              exact List.take_left' hp0_len
            have hs160 : slice (ev 0).coins 160 32 = p33 := by
              rw [← hcoins_eq, ← List.append_assoc]; unfold slice
              have h160 : (p0 ++ ps_kem.flatten).length = 160 := by simp [hp0_len, hflat_kem_len]
              rw [List.drop_left' h160, List.take_of_length_le (by omega)]
            have he1_eq : gamma evictedI0 S g (randTerm (ts0 + 1) 32) = ev0KyberEnt := by
              have hlen_e1 : (gamma evictedI0 S g (randTerm (ts0 + 1) 32)).length = 32 :=
                (hkem_item 0 (by decide)).2.1
              apply List.ext_getElem?
              intro j
              by_cases hj : j < 32
              · have hhead_j := (hkem_item j hj).2.2
                have hdrop_kem := flatten_drop_4mul_head? hall4 (j := j) (by omega)
                have hcoins_drop : ((ev 0).coins.drop (32 + 4 * j)).head? =
                    (ps_kem.flatten.drop (4 * j)).head? := by
                  rw [← hcoins_eq]
                  rw [show 32 + 4 * j = p0.length + 4 * j by omega,
                      List.drop_append, List.drop_of_length_le (Nat.le_add_right _ _),
                      List.nil_append, Nat.add_sub_cancel_left, List.drop_append]
                  cases hdk : ps_kem.flatten.drop (4 * j) with
                  | nil =>
                    have hlen_dk := congrArg List.length hdk
                    simp only [List.length_drop, List.length_nil, hflat_kem_len] at hlen_dk; omega
                  | cons _ _ => rfl
                rw [← hhead_j, ← hdrop_kem, ← hcoins_drop, hent_idx j hj]
              · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
            exact ⟨hp0_eq.trans hs0.symm, he1_eq, hp33_eq.trans hs160.symm⟩

theorem gamma_setup_rnd_eq {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (cls : Nat → Nat) {ts n : Nat}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hCompat : GhostAndSemMatchSetup evictedI0 r S g)
    (hmem : (ts, n) ∈ [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)])
    (hn : n ≠ 0) :
    gamma evictedI0 S g (rnd ts n) = gamma evictedI0 S (gClean r cls) (rnd ts n) := by
  have hmem' : (ts, n) ∈ DY.Libsignal.Composed.Refinement.setupRandomsAt r :=
    (setupRandomsAt_of_fit hfit) ▸ hmem
  have hlt : ts < 22 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  unfold rnd
  rw [gamma_rand, gamma_rand]
  simp only [hn, ↓reduceIte]
  exact (hCompat.1 (ts, n) hmem').trans (gClean_sigma_lt22 r cls hlt).symm

theorem gamma_kemPk_pqskB_gClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (cls : Nat → Nat)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hCompat : GhostAndSemMatchSetup evictedI0 r S g) :
    gamma evictedI0 S (gClean r cls) (DY.PQKem.kemPk pqskB) = w0.kyberPk := by
  have hnames := r_names_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hnames.1, hnames.2]; decide
  have hCompat' := ghostAndSemMatchSetup_gClean cls hfit hCompat
  have h6 : r.opaqueBytes (setupPublic r 6) = gamma evictedI0 S (gClean r cls) (setupPublic r 6) :=
    (hCompat'.2.1 r.pqpkPubTerm (by simp)).symm
  rw [hfit.1.1.2.2.2.2.2.2.2.2.2.2.1] at h6
  rw [Symbolic.Swarm.CREF.b1_setupPublic_6 r hNe] at h6
  exact h6.symm

/-- Steps Call 0 (`aliceStart`) across a network prefix `c0.pre` to initialize `"alice"`'s
`ActivePartySt` and match handshake concretizations against `gClean r cls`. -/
theorem alice_call0_agree {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat) {c0 : PeeledCall}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hCompat : GhostAndSemMatchSetup evictedI0 r S g)
    (hgwf : GhostWF g visAll)
    (hnet : ∀ x ∈ c0.pre, ∃ msg, x = .network msg)
    (hrm : RunMatches evictedI0 r S g (runSteps c0.pre (setupTrace r)) c0.s (ev 0) c0.v none)
    (hsub : ∀ w ∈ c0.v, w ∈ visAll) :
    let tr₁ := c0.s.next (runSteps c0.pre (setupTrace r))
    ∃ ek0 ct0 : Bytes,
      gamma evictedI0 S g ek0 = gamma evictedI0 S (gClean r cls) o1.ek ∧
      gamma evictedI0 S g ct0 = gamma evictedI0 S (gClean r cls) o1.ct ∧
      PkiUnchanged tr₁ ∧
      OnlyAliceDone ek0 ct0 tr₁ ∧
      ActivePartySt "alice" true S g (gClean r cls) [⟨2, by decide⟩] ⟨4, by decide⟩ stA0 tr₁ ∧
      NoPartyState "bob" tr₁ ∧
      nextBundleIds none (ev 0) = some (none, 7#32, 9#32) := by
  set tr₀ := runSteps c0.pre (setupTrace r)
  have hnames := r_names_of_fit hfit
  have hpki₀ : PkiUnchanged tr₀ :=
    pkiUnchanged_runSteps_network c0.pre hnet (setupTrace_eq_t4 hfit ▸ pkiUnchanged_t4)
  have hnoA₀ : NoPartyState "alice" tr₀ :=
    noPartyState_of_noNew (noNewPartyState_runSteps_network c0.pre _ hnet)
      (noPartyState_setupTrace "alice" r)
  have hnoB₀ : NoPartyState "bob" tr₀ :=
    noPartyState_of_noNew (noNewPartyState_runSteps_network c0.pre _ hnet)
      (noPartyState_setupTrace "bob" r)
  obtain ⟨hparty_ev0, hcmd_ev0, hexit_ev0, _⟩ := ev0_cmd_and_exit
  obtain ⟨_, hparty, hfits, hpeer, hok, _, hvis_eq,
    inp, drs, outs, hv_split, hbm_in, hdr, hout, _, _⟩ := hrm
  rw [hparty_ev0] at hparty
  rw [hcmd_ev0] at hfits
  cases hs : c0.s with
  | aliceStart a b idS regB bh =>
    rw [hs] at hparty hpeer hok hvis_eq
    rcases Option.some.inj hparty with rfl
    have hb_eq : b = "bob" := by simpa [Step.MatchesSetupPeer, hnames.2] using hpeer
    subst hb_eq
    have hnext_mv : (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ =
        (DY.Libsignal.Composed.Refinement.Move.aliceStart "alice" "bob" idS regB bh 35).next tr₀ := by
      rw [Symbolic.Swarm.CREF.b5_aliceStart_next]
      dsimp only [Step.next, Step.toInput]
      erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]
    obtain ⟨o0_ok, ho0_ok⟩ := Symbolic.Proofs.Swarm.UA.XlateSteps.aliceStart_ok_trOfOut hok
    have hlen_o0 : (Symbolic.Swarm.CREF.aliceStartTrOfOut tr₀ "alice" "bob" o0_ok).length =
        tr₀.length + 9 :=
      Symbolic.Swarm.CREF.length_iniAliceStartTr tr₀ "alice" "bob" o0_ok
    rcases Symbolic.Swarm.CREF.aliceStart_next_cases "alice" "bob" idS regB bh 35 tr₀ with
      h0 | h1 | ⟨ik_a, ik_b, vk_b, spk, spkSig, pqpk, pqpkSig, opk, honest,
        hstA, hregB, hspk, hspkSig, hpq, hpqSig, hopk, h3⟩
    · have := (congrArg DY.Trace.length (h0.symm.trans ho0_ok)).trans hlen_o0; omega
    · have := (append_len tr₀ (RndE 32)).symm.trans
        ((congrArg DY.Trace.length (h1.symm.trans ho0_ok)).trans hlen_o0); omega
    · have hikA_pin : ik_a = ikA := by
        rcases pki_pin_st hpki₀ hstA with ⟨_, hst_eq⟩ | ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨hf, _⟩
        · cases hst_eq; rfl
        · exact absurd hf (by decide)
        · exact absurd hf (by decide)
        · exact absurd hf (by decide)
      subst hikA_pin
      have hregB_at : (tr₀.at? regB : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
          some ⟨.IdentityRegistered "bob" ik_b vk_b honest⟩ := by
        rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hregB
      have hikB_pin : ik_b = dhPk ikB := by
        rcases pki_pin_reg hpki₀ hregB_at with ⟨hf, _⟩ | ⟨_, hpk, _⟩
        · exact absurd hf (by decide)
        · exact hpk
      subst hikB_pin
      have hout_nil : outs = [] := by
        unfold OutputsMatch at hout
        rw [hexit_ev0, hcmd_ev0] at hout
        exact hout
      rw [hout_nil, List.append_nil] at hv_split
      let o_gen := Symbolic.Swarm.COMPOSED.CompTrace.aliceOut tr₀ ikA (dhPk ikB) spk pqpk opk
      have htr'_ofOut : (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ =
          Symbolic.Swarm.CREF.aliceStartTrOfOut tr₀ "alice" "bob" o_gen :=
        hnext_mv.trans h3
      have hvis_full : c0.v =
          { kind := .recv, terms := received tr₀ ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList),
            layout := .bundle, anchor := none } ::
          rngEntry (randTerm tr₀.length 32) ::
          (kyberCoinEntries (randTerm (tr₀.length + 1) 32) ++
            [{ rngEntry (randTerm (tr₀.length + 2) 32) with anchor := some (tr₀.length + 5) }]) := by
        rw [hvis_eq]; unfold stepView
        simp only [hok, ↓reduceIte, htr'_ofOut]
        rw [Symbolic.Swarm.CREF.exposures_aliceStartTrOfOut, List.append_nil]
        exact Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.aliceVis_iniAliceStartTr
          tr₀ "alice" "bob" o_gen bh
      have hinp_drs := hv_split.symm.trans hvis_full
      injection hinp_drs with hinp_eq hdrs_eq
      obtain ⟨_, hbun_b4, hnext_ids, hbun_spk, _, hbun_pq, _, _⟩ := ev0_bundle_slices
      have hopk_none : bh.opk = none ∧ opk = none := by
        rcases hopk with ⟨h1, h2⟩ | ⟨idx, u, h1, _, hu⟩
        · exact ⟨h1, h2⟩
        · exfalso
          have hrec : received tr₀ ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList) =
              [spk, spkSig, pqpk, pqpkSig, u] := by
            rw [h1]
            change received tr₀ [bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig, idx] = _
            simp only [received, List.filterMap_cons, List.filterMap_nil,
              Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hspk,
              Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hspkSig,
              Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hpq,
              Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hpqSig,
              Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hu]
          rw [hinp_eq] at hbm_in
          have hplm := hbm_in.2
          dsimp only at hplm
          rw [hrec] at hplm
          dsimp only [DY.Libsignal.Composed.Refinement.PreKeyBundleLayoutMatches,
            DY.Libsignal.PQXDH.Refinement.BundleBlob.hasOpkByte] at hplm
          rw [hbun_b4] at hplm
          cases hplm.2.1
      rcases hopk_none with ⟨hbh_opk, hopk_eq⟩
      subst hopk_eq
      have hrec4 : received tr₀ ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList) =
          [spk, spkSig, pqpk, pqpkSig] := by
        rw [hbh_opk]
        change received tr₀ [bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] = _
        simp only [received, List.filterMap_cons, List.filterMap_nil,
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hspk,
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hspkSig,
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hpq,
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hpqSig]
      rw [hinp_eq] at hbm_in
      have hplm := hbm_in.2
      dsimp only at hplm
      rw [hrec4] at hplm
      obtain ⟨⟨_, hspk_sl, _, hpq_sl, _⟩, _⟩ := hplm
      have hspk_gam : gamma evictedI0 S g spk =
          gamma evictedI0 S (gClean r cls) (dhPk spkB) := by
        have h1 : ecKey (gamma evictedI0 S g spk) = ecKey (evictedPubOfIdx ⟨2, by decide⟩) :=
          hspk_sl.symm.trans hbun_spk
        have h2 : gamma evictedI0 S g spk = evictedPubOfIdx ⟨2, by decide⟩ :=
          (List.cons.inj h1).2
        have h3_clean := gamma_dhPk_ratchetTs (S := S) (cls := cls) (ts := 10) hfit (by decide)
        exact h2.trans h3_clean.symm
      have hpq_gam : gamma evictedI0 S g pqpk =
          gamma evictedI0 S (gClean r cls) (DY.PQKem.kemPk pqskB) := by
        have h1 : kyberKey (gamma evictedI0 S g pqpk) = kyberKey w0.kyberPk :=
          hpq_sl.symm.trans hbun_pq
        have h2 : gamma evictedI0 S g pqpk = w0.kyberPk := (List.cons.inj h1).2
        exact h2.trans (gamma_kemPk_pqskB_gClean cls hfit hCompat).symm
      have hsub_drs : ∀ w ∈ drs, w ∈ visAll :=
        fun w hw => hsub w (hv_split ▸ List.mem_cons_of_mem _ hw)
      rw [hdrs_eq] at hdr hsub_drs
      obtain ⟨hek_coins, he_coins, hdhs_coins⟩ := ev0_draws_pin hgwf hsub_drs hdr
      have hek_gam : gamma evictedI0 S g (rnd tr₀.length 32) =
          gamma evictedI0 S (gClean r cls) (rnd 22 32) := by
        change gamma evictedI0 S g (randTerm tr₀.length 32) =
          gamma evictedI0 S (gClean r cls) (randTerm 22 32)
        rw [hek_coins]; unfold randTerm; rw [gamma_rand]; simp [gClean_sigma_22]
      have he_gam : gamma evictedI0 S g (rnd (tr₀.length + 1) 32) =
          gamma evictedI0 S (gClean r cls) (rnd 23 32) := by
        change gamma evictedI0 S g (randTerm (tr₀.length + 1) 32) =
          gamma evictedI0 S (gClean r cls) (randTerm 23 32)
        rw [he_coins]; unfold randTerm; rw [gamma_rand]; simp [gClean_sigma_23]
      have hdhs_gam : gamma evictedI0 S g (randTerm (tr₀.length + 2) 32) =
          gamma evictedI0 S (gClean r cls) dhsA := by
        change gamma evictedI0 S g (randTerm (tr₀.length + 2) 32) =
          gamma evictedI0 S (gClean r cls) (randTerm 24 32)
        rw [hdhs_coins]; unfold randTerm; rw [gamma_rand]; simp [gClean_sigma_24]
      have hikA_gam : gamma evictedI0 S g ikA = gamma evictedI0 S (gClean r cls) ikA :=
        gamma_setup_rnd_eq cls hfit hCompat (by decide) (by decide)
      have hikB_gam : gamma evictedI0 S g (dhPk ikB) =
          gamma evictedI0 S (gClean r cls) (dhPk ikB) := by
        rw [gamma_dhPk, gamma_dhPk,
            gamma_setup_rnd_eq cls hfit hCompat (ts := 5) (n := 32) (by decide) (by decide)]
      obtain ⟨hek_pk, hct_eq, hst_agree⟩ := stateBytesAgree_aliceStart (tr := tr₀)
        hikA_gam hikB_gam hspk_gam hpq_gam hek_gam he_gam hdhs_gam
      let o_ss := aliceOut tr₀ ikA (dhPk ikB) spk pqpk
      have htr₁_eq : (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ =
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.iniAliceStartTr
            tr₀ "alice" "bob" o_ss :=
        htr'_ofOut
      refine ⟨o_ss.ek, o_ss.ct, hek_pk, hct_eq, ?_, ?_, ?_, ?_, hnext_ids⟩
      · exact pkiUnchanged_step_party rfl hpki₀
      · rw [htr₁_eq]
        exact onlyAliceDone_iniAliceStartTr
          (onlyAliceDone_runSteps_network c0.pre hnet
            (setupTrace_eq_t4 hfit ▸ onlyAliceDone_t4 o_ss.ek o_ss.ct))
      · have hle_tr₁ : tr₀ ≤ (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ := by
          rw [htr₁_eq]
          unfold Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.iniAliceStartTr
          dsimp only
          iterate 8 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
          exact DY.Trace.append_le _ _
        let stA_ss := Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.iniAliceStartState
          tr₀ "bob" o_ss
        have hat_stA : (((Step.aliceStart "alice" "bob" idS regB bh).next tr₀).at? (tr₀.length + 8) :
            Option TRStEntry) = some ⟨⟨"alice", stA_ss⟩⟩ := by
          rw [htr₁_eq,
              Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.at?_trSt_iniAliceStartTr]
          simp only [↓reduceIte]; rfl
        refine activePartySt_init hnoA₀ hle_tr₁ hat_stA ?_ rfl hst_agree ?_ ?_
        · intro j st hj hat_j
          rw [htr₁_eq,
              Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.at?_trSt_iniAliceStartTr] at hat_j
          by_cases hjeq : j = tr₀.length + 8
          · subst hjeq
            simp only [↓reduceIte, TRStE, Option.some.injEq] at hat_j
            injection hat_j with h1
            injection h1 with _ h2
            exact ⟨rfl, h2.symm⟩
          · simp only [hjeq, ↓reduceIte] at hat_j
            exact False.elim (hnoA₀ j st hat_j)
        · show [gamma evictedI0 S g spk] = [evictedPubOfIdx ⟨2, by decide⟩]
          have h1 : ecKey (gamma evictedI0 S g spk) = ecKey (evictedPubOfIdx ⟨2, by decide⟩) :=
            hspk_sl.symm.trans hbun_spk
          exact congrArg (· :: []) ((List.cons.inj h1).2)
        · show evictedSecretIdx (clamp (gamma evictedI0 S g (randTerm (tr₀.length + 2) 32))) =
              some ⟨4, by decide⟩
          rw [hdhs_coins]
          exact ev0_coins_facts.2.2.1
      · exact noPartyState_of_noNew (noNewPartyState_step_other tr₀ rfl (by simp [Step.party?])) hnoB₀
  | _ => rw [hs] at hfits; cases hfits

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunStepInvB

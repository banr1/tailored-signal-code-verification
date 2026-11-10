/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Synthetic.Witnesses.PromotedPrekeyHeadersCli
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridge
public import Symbolic.BugInjection.Proofs.Common.CoinsFresh
public import Symbolic.Proofs.SpecLemmas.SecurityBinaryFixed
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

/-!
# Spec-Half Disproof for `PromotedPrekeyHeadersCli`

Proves `cliCompFitsPinned_satisfiable`, `spec_half_pinned`, and
`not_signalSessionSecure_of_implHalf` for the `PromotedPrekeyHeadersCli` witness, reusing the
four-event prefix invariants of `Cheval26WeakStateIdx1Cli` and refuting the mutated fifth receive
event by identity-key mismatch and known base key.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticPromotedPrekeyHeaders.Top

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.Defs Symbolic.Proofs.Swarm.UA.ClassicalBridge
open Symbolic.Swarm.CREF
open Symbolic.BugInjection
open Symbolic.BugInjection.Synthetic.Witnesses
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliCompFitsPinned cliCompFitsPinned_satisfiable_of_plausible)
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_kyberCorrectOn)
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose (coinSplit_nonRng_cons coinSplit_rng_cons)
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.MacGuardGen
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridge
  (ev0 ev1 ev2 ev3 ev4 ev5 ev6 cliEvents cliEvents_eq cliTrace cliCoins0 cliCoins2 rngAt acceptAt
   schedFits_prefix_cliEvents not_readCollisionCliClassical_sub_take3
   not_readCollisionCliClassical_of_not_knownBaseKeyOn not_knownBaseKeyOn_take3
   matchesEventsClassical_run_exit0_inv_local not_nextEventCollidesClassical_recv_preKey_sub
   not_pt_cli_2_self not_pt_cli_5_self not_kyberMismatch_cli_8 wireAt_40_head_ne_whisper
   noBscCliAt_8_sub map_rng_kind_local map_rng_snoc_send_kind_local rpk_blk_cut_eq)

theorem cliCompFitsPinned_satisfiable :
    ∃ iw r, cliCompFitsPinned PromotedPrekeyHeadersCli.setup iw r :=
  cliCompFitsPinned_satisfiable_of_plausible
    PromotedPrekeyHeadersCli.setup
    (by decide +kernel)
    (fun _ h => nomatch h)

private theorem compFitsPinned_ws1_of {r : ProtocolSetup}
    (h : compFitsPinned PromotedPrekeyHeadersCli.setup SpecTop.compI0 r) :
    compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r := by
  obtain ⟨⟨hwf, hopk, hra, hrb, hspk, hkpk, hs0, hs1, hs2, ho5, ho6, ho7, hsec, hcryp, hcan, _⟩,
    hi, hsec35, hpart, htorRej, _⟩ := h
  exact ⟨⟨hwf, hopk, hra, hrb, hspk, hkpk, hs0, hs1, hs2, ho5, ho6, ho7, hsec, hcryp, hcan,
    compI0_kyberCorrectOn r _⟩, hi, hsec35, hpart, htorRej, fun _ hm => nomatch hm⟩

attribute [local irreducible] Symbolic.BugInjection.hexBytes

private def wireMut : HwBytes :=
  match PromotedPrekeyHeadersCli.trace with
  | [_, _, _, _, .run ev] => ev.input
  | _ => []

private def coinsMut : HwBytes :=
  match PromotedPrekeyHeadersCli.trace with
  | [_, _, _, _, .run ev] => ev.coins
  | _ => []

private def outMut : HwBytes :=
  match PromotedPrekeyHeadersCli.trace with
  | [_, _, _, _, .run ev] =>
    match ev.exit with
    | some (_, out) => out
    | none => []
  | _ => []

private def ev4Mut : RunEvent :=
  { party := "bob"
    cmd := .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩
    input := wireMut
    coins := coinsMut
    exit := some (0, outMut) }

private def promoEvents : List CliEvent :=
  [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4Mut]

private theorem promoEvents_take4_eq :
    [.run ev0, .run ev1, .run ev2, .run ev3] = PromotedPrekeyHeadersCli.trace.take 4 := by
  have h1 : [.run ev0, .run ev1, .run ev2, .run ev3] = cliEvents.take 4 := rfl
  have h2 : Witnesses.Cheval26WeakStateIdx1Cli.trace.take 4 =
      PromotedPrekeyHeadersCli.trace.take 4 := rfl
  rw [h1, congrArg (List.take 4) cliEvents_eq, h2]

private theorem promoEvents_eq : promoEvents = PromotedPrekeyHeadersCli.trace := by
  have h3 : PromotedPrekeyHeadersCli.trace =
      PromotedPrekeyHeadersCli.trace.take 4 ++ [.run ev4Mut] := rfl
  unfold promoEvents
  rw [h3, ← promoEvents_take4_eq]
  rfl

private theorem promoEvents_breakFree : BreakFree promoEvents :=
  breakFree_map_run [ev0, ev1, ev2, ev3, ev4Mut]

private theorem list_eq_five_splits {α : Type} {x0 x1 x2 x3 x4 y : α} {l1 l2 : List α}
    (h : [x0, x1, x2, x3, x4] = l1 ++ y :: l2) :
    (l1 = [] ∧ y = x0 ∧ l2 = [x1, x2, x3, x4]) ∨
    (l1 = [x0] ∧ y = x1 ∧ l2 = [x2, x3, x4]) ∨
    (l1 = [x0, x1] ∧ y = x2 ∧ l2 = [x3, x4]) ∨
    (l1 = [x0, x1, x2] ∧ y = x3 ∧ l2 = [x4]) ∨
    (l1 = [x0, x1, x2, x3] ∧ y = x4 ∧ l2 = []) := by
  rcases l1 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, l1⟩⟩⟩⟩⟩ <;> simp at h
  · obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))

local elab "chars_of_hex_mut" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

local elab "str_of_hex_mut" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  return sLit

private def wireMutChars : List Char := chars_of_hex_mut wireMut
private theorem wireMut_eq_hex : wireMut = hexBytes (str_of_hex_mut wireMut) := rfl
private theorem wireMutStr_eq : (str_of_hex_mut wireMut) = String.ofList wireMutChars := rfl
private def wireMutFast : HwBytes := hexBytes.go SpecTop.hexDigit wireMutChars

private theorem wireMut_eq_fast : wireMut = wireMutFast := by
  change wireMut = hexBytes.go SpecTop.hexDigit wireMutChars
  rw [wireMut_eq_hex, wireMutStr_eq, SpecTop.hexBytes_ofList]

private def badIdentityKey : HwBytes :=
  0x05#8 :: (List.replicate 31 0x42#8 ++ [0x02#8])

private theorem wireMut_head? : wireMut.head? = some 0x03#8 := by
  rw [wireMut_eq_fast]; decide +kernel

private theorem wireMut_head_ne_whisper :
    wireMut.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by
  rw [wireMut_head?]; decide

private theorem wireMut_baseKey :
    (parsePreKeyWire wireMut).map (fun p => p.baseKey.take 33) = some (ecKey ek1PubKey) := by
  rw [wireMut_eq_fast]; decide +kernel

private theorem wireMut_parses : ∃ p, parsePreKeyWire wireMut = some p :=
  parses_of_map wireMut_baseKey

private theorem wireMut_identityKey :
    (parsePreKeyWire wireMut).map (fun p => p.identityKey.take 33) = some badIdentityKey := by
  rw [wireMut_eq_fast]; decide +kernel

private theorem badIdentityKey_ne_alice :
    badIdentityKey ≠ ecKey (pubBytes SpecTop.compI0 PromotedPrekeyHeadersCli.setup.aliceId) := by
  decide +kernel

private theorem wireMut_identityKey_ne_alice {p : PreKeyFields}
    (hp : parsePreKeyWire wireMut = some p) :
    p.identityKey.take 33 ≠ ecKey (pubBytes SpecTop.compI0 PromotedPrekeyHeadersCli.setup.aliceId) := by
  have h := wireMut_identityKey
  rw [hp, Option.map_some, Option.some.injEq] at h
  rw [h]
  exact badIdentityKey_ne_alice

private theorem exposures_kind_eq_leak {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') : v.kind = .leak := by
  unfold exposures at hv
  rcases List.mem_append.mp hv with hpq | htr
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hpq
    unfold pqExposureAt at hj
    split at hj <;> simp at hj <;> (subst hj; rfl)
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp htr
    unfold trExposureAt at hj
    split at hj <;> simp at hj <;> (subst hj; rfl)

private theorem recv_stepView_head_layout {tr : ExecTrace} {s : Step} {wrapped : Bool}
    {peer : CryptoVerification.SignalSession.Address} {inp : VisEntry} {rest : List VisEntry}
    (hfits : s.FitsCmd (.recv peer)) (hok : s.ok tr = true) (hk : inp.kind = .recv)
    (hview : stepView s tr wrapped = inp :: rest) :
    inp.layout = .preKeyRecv ∨ inp.layout = .whisper ∨ ∃ eks, inp.layout = .preKeyInner eks := by
  have hmem : inp ∈ stepView s tr wrapped := by rw [hview]; exact List.mem_cons_self ..
  simp only [stepView, hok, ↓reduceIte] at hmem
  rcases List.mem_append.mp hmem with hown | hexp
  · cases s <;> try exact False.elim hfits
    case bobStart b _ kh _ mh _ _ =>
      dsimp only [bobVis] at hown
      rcases List.mem_cons.mp hown with rfl | htail
      · exact Or.inl rfl
      · rcases List.mem_append.mp htail with hrng | hacc
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng; simp [rngEntry] at hk
        · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp (Option.mem_toList.mp hacc); simp at hk
    all_goals
      dsimp only [decVis] at hown
      rcases List.mem_append.mp hown with h12 | hacc
      · rcases List.mem_append.mp h12 with hrecv | hrng
        · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp (Option.mem_toList.mp hrecv)
          cases wrapped
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr ⟨_, rfl⟩)
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng; simp [rngEntry] at hk
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp (Option.mem_toList.mp hacc); simp at hk
  · have hlk := exposures_kind_eq_leak hexp; rw [hk] at hlk; cases hlk

private theorem not_runMatches_ev4Mut {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {s : Step} {v : List VisEntry} {initIds : Option BundlePreKeyIds}
    (hs0 : secretBytes r 0 = PromotedPrekeyHeadersCli.setup.aliceId)
    (hrm : RunMatches SpecTop.compI0 r S g tr s ev4Mut v initIds) : False := by
  obtain ⟨_, _, hfits, _, hok, _, hv, inp, drs, outs, hv_cons, hbme, _⟩ := hrm
  have hlay := recv_stepView_head_layout hfits hok hbme.1.symm (hv.symm.trans hv_cons)
  have hbme' : BytesMatchEntry SpecTop.compI0 r S g .recv wireMut inp := hbme
  rcases hlay with hlay | hlay | ⟨eks, hlay⟩
  · unfold BytesMatchEntry at hbme'
    rw [hlay] at hbme'
    rcases hinp_t : inp.terms with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _ | ⟨opk, _ | _⟩⟩⟩⟩ <;>
      rw [hinp_t] at hbme'
    · exact hbme'.2
    · exact hbme'.2
    · exact hbme'.2
    · obtain ⟨⟨p, hp, _, _, _, _, _, _, hid, _⟩, _⟩ := hbme'.2
      rw [show r.ikASecBytes = secretBytes r 0 from rfl, hs0] at hid
      exact wireMut_identityKey_ne_alice hp hid
    · obtain ⟨⟨p, hp, _, _, _, _, _, _, hid, _⟩, _⟩ := hbme'.2
      rw [show r.ikASecBytes = secretBytes r 0 from rfl, hs0] at hid
      exact wireMut_identityKey_ne_alice hp hid
    · exact hbme'.2
  · unfold BytesMatchEntry at hbme'
    rw [hlay] at hbme'
    obtain ⟨t, _, hw⟩ := hbme'.2
    apply wireMut_head_ne_whisper
    rw [hw]; rfl
  · unfold BytesMatchEntry at hbme'
    rw [hlay] at hbme'
    obtain ⟨_, p, _, hp, _, hid, _⟩ := hbme'.2
    rw [hs0] at hid
    exact wireMut_identityKey_ne_alice hp hid

private theorem not_explains_promoEvents {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hs0 : secretBytes r 0 = PromotedPrekeyHeadersCli.setup.aliceId)
    (hex : Explains SpecTop.compI0 r S g ss vis promoEvents) : False := by
  have hex_cl := explainsClassical_of hex promoEvents_breakFree
  obtain ⟨_, _, _, _, _, _, _, _, hme1⟩ := matchesEventsClassical_run_exit0_inv_local rfl hex_cl.2.2.2
  obtain ⟨_, _, _, _, _, _, _, _, hme2⟩ := matchesEventsClassical_run_exit0_inv_local rfl hme1
  obtain ⟨_, _, _, _, _, _, _, _, hme3⟩ := matchesEventsClassical_run_exit0_inv_local rfl hme2
  obtain ⟨_, _, _, _, _, _, _, _, hme4⟩ := matchesEventsClassical_run_exit0_inv_local rfl hme3
  obtain ⟨_, _, _, _, _, _, _, hrm4, _⟩ := matchesEventsClassical_run_exit0_inv_local rfl hme4
  exact not_runMatches_ev4Mut hs0 hrm4

private theorem not_readCollisionCliClassical_take4 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} (hwf : ProtocolSetupWF r)
    (hex : ExplainsClassical SpecTop.compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3]) :
    ¬ ReadCollisionCliClassical SpecTop.compI0 r S g ss [.run ev0, .run ev1, .run ev2, .run ev3] := by
  refine not_readCollisionCliClassical_of_not_knownBaseKeyOn hex fun evs₁ ev evs₂ _ hevs ⟨_, hcmd⟩ _ => ?_
  rcases evs₁ with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, evs₁⟩⟩⟩⟩ <;> simp at hevs
  · obtain ⟨rfl, _⟩ := hevs; cases hcmd
  · obtain ⟨rfl, rfl, _⟩ := hevs; cases hcmd
  · obtain ⟨rfl, rfl, rfl, _⟩ := hevs; cases hcmd
  · obtain ⟨rfl, rfl, rfl, rfl, _⟩ := hevs; obtain ⟨p40, hp40⟩ := wireAt40_parses
    exact ⟨p40, hp40, fun _ _ hex₁ => not_knownBaseKeyOn_take3 hwf hex₁⟩

open PtPrefixInv78a
  (bobStartTr bobStartSkipTr bobStartPreSkipTr bobOutOf bobStart_next_eq
   at?_append_other_eq' at?_append_same_eq' at?_other_logSkippedKeys) in
private theorem mem_bobDoneBaseKeys_bobStartTr {tr : ExecTrace} {b a : Participant}
    {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat}
    {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : CompSetupSecrecy.BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) :
    w.ek ∈ bobDoneBaseKeys (bobStartTr tr b a w) := by
  let o := bobOutOf w.ikB w.spk w.pqsk w.opk w.ikAPk w.ek w.ct w.keys
  let tr_send := (tr.append (Symbolic.Swarm.CREF.TR.RndE 32)).append (Symbolic.Swarm.CREF.TR.NetE w.key)
  let tr_opk := match o.opk with
    | some opkPk => tr_send.append (Symbolic.Swarm.CREF.TR.EvE (.OPKUsed b opkPk))
    | none => tr_send
  let doneIdx := tr_opk.length
  have hat : ((bobStartTr tr b a w).at? doneIdx :
      Option (ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
      some ⟨.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys⟩ := by
    unfold bobStartTr bobStartSkipTr bobStartPreSkipTr
    dsimp only
    rw [at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.TRStE _ _) rfl,
        at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.TREvE _) rfl,
        at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.TREvE _) rfl,
        at?_other_logSkippedKeys (fun _ => rfl),
        at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.CEvE _) rfl,
        at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.TREvE _) rfl,
        at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.TREvE _) rfl]
    change (((tr_opk.append (Symbolic.Swarm.CREF.TR.EvE
      (.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys))).at? tr_opk.length) :
      Option (ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = _
    rw [at?_append_same_eq']
    simp only [↓reduceIte]
  have hget : (bobStartTr tr b a w).getEventAt DY.Libsignal.PQXDH.PQXDHEvent doneIdx =
      some (.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys) := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getEventAt_eq_at?, hat]
  unfold bobDoneBaseKeys
  exact List.mem_filterMap.2
    ⟨doneIdx, List.mem_range.2 (bks_lt_length_of_getEventAt DY.Libsignal.PQXDH.PQXDHEvent hget), by
      rw [hget]; rfl⟩

open CompPrefixInvStruct in
private theorem knownBaseKey_cli_11 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {τ₁ : List MachineEvent} {g : Ghost} {ms : List Move} {p : PreKeyFields}
    (hp : parsePreKeyWire wireMut = some p)
    (hex : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 11) τ₁ g ms) :
    KnownBaseKey SpecTop.compI0 r S g ms p := by
  have ⟨hcs, hmp, _, hrng⟩ := hex
  have htr_eq : cliTrace.take 11 =
      [.recv (wireAt 0), .rng cliCoins0, .pt (ptAt 35),
       .rng (rngAt 36), .send (sendAt 37), .pt (ptAt 38),
       .rng cliCoins2, .send (wireAt 40), .recv (wireAt 40),
       .rng (rngAt 41), .accept (acceptAt 42)] := rfl
  rw [htr_eq] at hcs
  obtain ⟨τ1, rfl, hcs1⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs
  obtain ⟨p0, τ2, _, _, rfl, hcs2⟩ := coinSplit_rng_cons hcs1
  obtain ⟨τ3, rfl, hcs3⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs2
  obtain ⟨p1, τ4, _, _, rfl, hcs4⟩ := coinSplit_rng_cons hcs3
  obtain ⟨τ5, rfl, hcs5⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs4
  obtain ⟨τ6, rfl, hcs6⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs5
  obtain ⟨p2, τ7, _, _, rfl, hcs7⟩ := coinSplit_rng_cons hcs6
  obtain ⟨τ8, rfl, hcs8⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs7
  obtain ⟨τ9, rfl, hcs9⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs8
  obtain ⟨p3, τ10, hp3_ne, hp3_pref, rfl, hcs10⟩ := coinSplit_rng_cons hcs9
  obtain ⟨τ11, rfl, hcs11⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs10
  cases hcs11
  let b0 : List MachineEvent := .recv (wireAt 0) :: p0.map .rng
  let b1 : List MachineEvent := .pt (ptAt 35) :: (p1.map .rng ++ [.send (sendAt 37)])
  let b2 : List MachineEvent := .pt (ptAt 38) :: (p2.map .rng ++ [.send (wireAt 40)])
  let b3 : List MachineEvent := .recv (wireAt 40) :: p3.map .rng ++ [.accept (acceptAt 42)]
  have hmp_cref : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms
      (((b0 ++ b1) ++ b2) ++ b3) := by
    have h0 := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp
    simpa [b0, b1, b2, b3, List.append_assoc] using h0
  obtain ⟨p40, hp40⟩ := wireAt40_parses
  have hp40_bk : p40.baseKey.take 33 = ecKey ek1PubKey := baseKey_of_map wireAt40_baseKey hp40
  have hp_bk : p.baseKey.take 33 = ecKey ek1PubKey := baseKey_of_map wireMut_baseKey hp
  have hb0 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ b0 →
      AllBobDone (fun _ => False) (runTraceMoves r ms₀) := by
    intro ms₀ h
    have h' : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ ([] ++ b0) := h
    obtain ⟨ms_nil, δ₀, rfl, hmp_nil, hfor₀⟩ := matchedPrefix6_split h'
      (by intro e he; simp [b0] at he; subst he; exact Or.inl rfl) (matchedPrefix6_prefix_reachable h')
    exact allBobDone_xplBlock_ini ⟨hmp_nil, h.2.1, hfor₀⟩ map_rng_kind_local (allBobDone_matchedPrefix_nil hmp_nil)
  have hb1 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ (b0 ++ b1) →
      AllBobDone (fun _ => False) (runTraceMoves r ms₀) := by
    intro ms₀ h
    obtain ⟨ms_0, δ₁, rfl, hmp_0, hfor₁⟩ := matchedPrefix6_split h
      (by intro e he; simp [b1] at he; subst he; exact Or.inr rfl) (matchedPrefix6_prefix_reachable h)
    exact allBobDone_xplBlock_send ⟨hmp_0, h.2.1, hfor₁⟩ map_rng_snoc_send_kind_local (hb0 ms_0 hmp_0)
  have hb2 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ ((b0 ++ b1) ++ b2) →
      AllBobDone (fun _ => False) (runTraceMoves r ms₀) := by
    intro ms₀ h
    obtain ⟨ms_1, δ₂, rfl, hmp_1, hfor₂⟩ := matchedPrefix6_split h
      (by intro e he; simp [b2] at he; subst he; exact Or.inr rfl) (matchedPrefix6_prefix_reachable h)
    exact allBobDone_xplBlock_send ⟨hmp_1, h.2.1, hfor₂⟩ map_rng_snoc_send_kind_local (hb1 ms_1 hmp_1)
  have hnk40 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ ((b0 ++ b1) ++ b2) →
      ¬ KnownBaseKey SpecTop.compI0 r S g ms₀ p40 := fun ms₀ h => not_knownBaseKey_of_allBobDone_false (hb2 ms₀ h)
  obtain ⟨ms_2, δ_3, hms_eq, hmp_2, hfor_3⟩ := matchedPrefix6_split hmp_cref
    (by intro e he; simp [b3] at he; subst he; exact Or.inl rfl) (matchedPrefix6_prefix_reachable hmp_cref)
  have hcs_b3 : CoinSplit [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)] b3 :=
    .keep (fun _ h => by cases h) (.split hp3_ne hp3_pref (.keep (fun _ h => by cases h) .nil))
  have hb3_eq : b3 = [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)] :=
    rpk_blk_cut_eq PtPrefixInv78b.rngAt41_length hcs_b3 wireAt40_head? hp40 (hnk40 ms_2 hmp_2)
      ⟨hmp_2, hms_eq ▸ hmp_cref.2.1, hfor_3⟩
      (by simpa [hms_eq] using hrng : RngLengthsFaithfulCli SpecTop.compI0 r S g (ms_2 ++ δ_3 ++ []))
  have hmp_3' : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms
      (((b0 ++ b1) ++ b2) ++ [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)]) := by
    rwa [← hb3_eq]
  obtain ⟨ms₀, pre, post, b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx, shown, rfl,
      _, _, _, hpost_inv, _, hm⟩ :=
    matchedPrefix_rpk_bobStart_only SpecTop.compI0 r S g ((b0 ++ b1) ++ b2)
      (wireAt 40) (rngAt 41) (acceptAt 42) ms p40 wireAt40_head? hp40 hnk40 hmp_3'
  obtain ⟨w, hw_ek, _⟩ := bobStartOk_of_rpk_forall2 hp40 hm
  refine ⟨w.ek, ?_, by rw [hw_ek, hp40_bk, hp_bk]⟩
  rw [Symbolic.Swarm.CREF.runTrace_append, runMoves_append_fst]
  change w.ek ∈ bobDoneBaseKeys
    (runMoves post ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown).next
      (runMoves pre (runTraceMoves r ms₀)).1)).1
  rw [bobDoneBaseKeys_runMoves_of_movesFrom _ post hpost_inv, PtPrefixInv78a.bobStart_next_eq w]
  exact mem_bobDoneBaseKeys_bobStartTr w

private theorem knownBaseKeyOn_take4 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {p : PreKeyFields}
    (hwf : ProtocolSetupWF r) (hp : parsePreKeyWire wireMut = some p)
    (hex : ExplainsClassical SpecTop.compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3]) :
    KnownBaseKeyOn SpecTop.compI0 S g (runTrace r ss) p := by
  obtain ⟨τ, ms, hex_cli, _, _, htr, _⟩ :=
    xlate_inv_with_noBrk hwf
      (schedFits_prefix_cliEvents (evs₂ := [.run ev4, .run ev5, .run ev6]) rfl)
      hex (not_readCollisionCliClassical_take4 hwf hex)
  have hkb := knownBaseKey_cli_11 hp hex_cli
  unfold KnownBaseKey at hkb
  rwa [htr] at hkb

private theorem not_nextEventCollidesClassical_ev4Mut {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hwf : ProtocolSetupWF r)
    (hs0 : secretBytes r 0 = PromotedPrekeyHeadersCli.setup.aliceId)
    (hex : ExplainsClassical SpecTop.compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3]) :
    ¬ NextEventCollidesClassical SpecTop.compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3] ev4Mut := by
  obtain ⟨p4, hp4⟩ := wireMut_parses
  rcases hmsg : wireMut with _ | ⟨tag, body⟩
  · rw [hmsg] at hp4; cases hp4
  · intro hcol
    have hcmd : ev4Mut.cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
    have hinp : ev4Mut.input = tag :: body := hmsg
    simp only [NextEventCollidesClassical, hcmd, hinp] at hcol
    rcases hcol.2 with ⟨htag_eq, _⟩ | ⟨p', hp', ⟨_, _, hid, _⟩ | ⟨hnkb, _⟩⟩
    · apply wireMut_head_ne_whisper
      rw [hmsg, htag_eq]; rfl
    · rw [← hmsg] at hp'
      rw [hs0] at hid
      exact wireMut_identityKey_ne_alice hp' hid
    · rw [← hmsg, hp4] at hp'
      cases Option.some.inj hp'
      exact hnkb (knownBaseKeyOn_take4 hwf hp4 hex)

theorem spec_half_pinned :
    cliCompShape.SpecHalf (cliCompFitsPinned PromotedPrekeyHeadersCli.setup)
      PromotedPrekeyHeadersCli.trace := by
  intro (iw : cliCompShape.Interp) (r : ProtocolSetup) hfits
  have hwf : ProtocolSetupWF r := hfits.1.1.1
  have hiw : iw.1 = SpecTop.compI0 := hfits.1.2.1
  have hs0 : secretBytes r 0 = PromotedPrekeyHeadersCli.setup.aliceId := hfits.1.1.2.2.2.2.2.2.1
  have hfits0 : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r :=
    compFitsPinned_ws1_of (hiw ▸ hfits.1)
  refine ⟨hwf, fun (S : OpaqueSymbolSemantics) _ hdisj => ?_⟩
  change (∃ g ss vis, Explains iw.1 r S g ss vis PromotedPrekeyHeadersCli.trace) ∨
    CollisionAfterExplainedPrefix iw.1 r S PromotedPrekeyHeadersCli.trace at hdisj
  rw [← promoEvents_eq, hiw] at hdisj
  rcases hdisj with ⟨g, ss, vis, hex⟩ | hcol
  · exact not_explains_promoEvents hs0 hex
  · refine not_collisionAfterExplainedPrefix_of_splits promoEvents_breakFree ?_ hcol
    intro evs₁ ev evs₂ g ss vis hevs hex
    rcases list_eq_five_splits hevs with
      ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ <;>
      injection hev with hev' <;> subst hev'
    · exact not_nextEventCollidesClassical_init rfl
    · refine not_nextEventCollidesClassical_send hwf
        (schedFits_prefix_cliEvents (evs₂ := [.run ev1, .run ev2, .run ev3, .run ev4, .run ev5, .run ev6]) rfl)
        hex (not_readCollisionCliClassical_sub_take3 fun _ h => by simp at h ⊢; tauto) rfl
        fun τ ms hex_cli _ hnb hbme hmcol => not_pt_cli_2_self hfits0 hnb hex_cli
          ⟨rfl, by simpa [BytesMatchEntry, ptEntryAt, ptEntryOfNextEncrypt, ev1, eventBytes] using hbme⟩ hmcol
    · refine not_nextEventCollidesClassical_send hwf
        (schedFits_prefix_cliEvents (evs₂ := [.run ev2, .run ev3, .run ev4, .run ev5, .run ev6]) rfl)
        hex (not_readCollisionCliClassical_sub_take3 fun _ h => by simp at h ⊢; tauto) rfl
        fun τ ms hex_cli _ hnb hbme hmcol => not_pt_cli_5_self hfits0 hnb hex_cli
          ⟨rfl, by simpa [BytesMatchEntry, ptEntryAt, ptEntryOfNextEncrypt, ev2, eventBytes] using hbme⟩ hmcol
    · obtain ⟨p40, hp40⟩ := wireAt40_parses; rcases hmsg : wireAt 40 with _ | ⟨tag, body⟩
      · rw [hmsg] at hp40; cases hp40
      · have htag : tag ≠ DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag :=
          fun h => wireAt_40_head_ne_whisper (by rw [hmsg, h]; rfl)
        refine not_nextEventCollidesClassical_recv_preKey_sub hwf
          (schedFits_prefix_cliEvents (evs₂ := [.run ev3, .run ev4, .run ev5, .run ev6]) rfl)
          hex (not_readCollisionCliClassical_sub_take3 fun _ h => h) rfl hmsg htag (hmsg ▸ hp40)
          (not_knownBaseKeyOn_take3 hwf hex) (not_kyberMismatch_cli_8 hfits0.1 p40 hp40)
          fun τ ms hex_cli _ hnb htr hsalts hpre hpt => ?_
        simpa [hmsg] using noBscCliAt_8_sub hfits0 hex hp40 hex_cli hnb htr hsalts hpre hpt
    · exact not_nextEventCollidesClassical_ev4Mut hwf hs0 hex

theorem not_signalSessionSecure_of_implHalf {bytes : List (BitVec 8)}
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      cliCompShape.ImplHalf (cliCompFitsPinned PromotedPrekeyHeadersCli.setup) elf
        PromotedPrekeyHeadersCli.trace) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecure bytes :=
  not_signalSessionSecure_of_witness spec_half_pinned hi
    Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_promotedPrekeyHeadersCli

end Symbolic.BugInjection.Proofs.SyntheticPromotedPrekeyHeaders.Top

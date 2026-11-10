/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.SpecHalf
public import Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose
public import Symbolic.BugInjection.Proofs.Common443.CliEventBridge
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable

/-!
# CLI Bridge for `Cheval26SmallSubgroupHighBitComp443`

Establishes `no_coinSplit_matchedPrefix`, the generic 3-call specification bridge
`spec_half_pinned_443_of_gen`, and `spec_half_pinned` for
`Witnesses.Cheval26SmallSubgroupHighBitCli`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent EnvEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.Defs (runOk flatEntry flatExit failedSend flatEvent flatEvents callsOf SchedFits)
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (BreakFree breakFree_nil breakFree_of_cons
    breakFree_append breakFree_run_cons explainsClassical_of explains_of_classical
    readCollisionCli_of_classical readCollisionCliClassical_of acceptsViaCli_eq)
open Symbolic.BugInjection
open Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace

attribute [local irreducible] Symbolic.BugInjection.hexBytes

def rngMsg39 : HwBytes :=
  match (Witnesses.Cheval26SmallSubgroupHighBitComp.trace[39]? : Option MachineEvent) with
  | some (.rng b) => b
  | _ => []

def acceptMsg40 : HwBytes :=
  match (Witnesses.Cheval26SmallSubgroupHighBitComp.trace[40]? : Option MachineEvent) with
  | some (.accept b) => b
  | _ => []

def cliTrace : List MachineEvent :=
  [ .recv CompRX0SS38.bunBytes, .rng cliCoins0,
    .pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes,
    .recv recvMsg38, .rng rngMsg39, .accept acceptMsg40 ]

def evInit : RunEvent :=
  { party := "alice"
    cmd := .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle"
    input := CompRX0SS38.bunBytes
    coins := cliCoins0
    exit := some (0, []) }

def evSend : RunEvent :=
  { party := "alice"
    cmd := .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩
    input := CompRX0SS38.ptB
    coins := CompRX0SS38.cB
    exit := some (0, CompRPlantWire.sentWireBytes) }

def evRecv (msg38 : HwBytes) : RunEvent :=
  { party := "bob"
    cmd := .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩
    input := msg38
    coins := rngMsg39
    exit := some (0, acceptMsg40) }

def cliEvents (msg38 : HwBytes) : List CliEvent :=
  [.run evInit, .run evSend, .run (evRecv msg38)]

theorem rngMsg39_eq_hex :
    rngMsg39 = hexBytes "277e2a7f356d98732990e6c96848114813f782d86b9349fbf714af9e97857fdc" := rfl

theorem acceptMsg40_eq_hex :
    acceptMsg40 = hexBytes "68656c6c6f20626f62" := rfl

theorem cliSetup_eq : setup = Witnesses.Cheval26SmallSubgroupHighBitCli.setup := rfl

theorem nil_eq_hexBytes : ([] : HwBytes) = hexBytes "" := by
  unfold hexBytes hexBytes.go; rfl

theorem cliEvents_eq :
    cliEvents recvMsg38 = Witnesses.Cheval26SmallSubgroupHighBitCli.trace := by
  unfold cliEvents evInit evSend evRecv cliCoins0 Witnesses.Cheval26SmallSubgroupHighBitCli.trace
  rw [CompRX0SS38.bunBytes_eq_hex, CompRX0SS38.ptB_eq_hex, CompRX0SS38.cB_eq_hex,
    CompRX0SS38.sentWireBytes_eq_hex, recvMsg38_eq_hex, rngMsg39_eq_hex, acceptMsg40_eq_hex,
    nil_eq_hexBytes]

theorem breakFree_cliEvents (msg38 : HwBytes) : BreakFree (cliEvents msg38) :=
  breakFree_cons_run _ (breakFree_cons_run _ (breakFree_cons_run _ breakFree_nil))

theorem callsOf_cliEvents (msg38 : HwBytes) :
    callsOf (cliEvents msg38) = [("alice", true), ("alice", true), ("bob", true)] := rfl

theorem callsOf_evInit :
    callsOf [.run evInit] = [("alice", true)] := rfl

theorem callsOf_evInit_evSend :
    callsOf [.run evInit, .run evSend] = [("alice", true), ("alice", true)] := rfl

set_option linter.unnecessarySeqFocus false in
theorem schedFits_cliEvents (msg38 : HwBytes) :
    SchedFits (callsOf (cliEvents msg38)) who ok := by
  rw [callsOf_cliEvents]
  refine ⟨by decide, fun k p b hget => ?_⟩
  rcases k with _ | _ | _ | k <;> simp at hget <;> obtain ⟨rfl, rfl⟩ := hget <;> rfl

set_option linter.unnecessarySeqFocus false in
theorem schedFits_evInit : SchedFits (callsOf [.run evInit]) who ok := by
  rw [callsOf_evInit]
  refine ⟨by decide, fun k p b hget => ?_⟩
  rcases k with _ | k <;> simp at hget <;> obtain ⟨rfl, rfl⟩ := hget <;> rfl

set_option linter.unnecessarySeqFocus false in
theorem schedFits_evInit_evSend :
    SchedFits (callsOf [.run evInit, .run evSend]) who ok := by
  rw [callsOf_evInit_evSend]
  refine ⟨by decide, fun k p b hget => ?_⟩
  rcases k with _ | _ | k <;> simp at hget <;> obtain ⟨rfl, rfl⟩ := hget <;> rfl

theorem recvMsg38_eq_ss_highBitWireBytes :
    recvMsg38 = CompSmallSubgroupTrace.highBitWireBytes := by
  rw [recvMsg38_eq_highBitWireBytes, census_highBitWireBytes_eq_trace]

theorem no_coinSplit_matchedPrefix
    {r : Records} {S : Sem} {who₀ : List Participant} {g : Ghost} {ms : List Move}
    {τhw : List MachineEvent}
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hcs : CoinSplit cliTrace τhw) :
    ¬ MatchedPrefix compI0 r S who₀ g ms τhw := by
  have hcs' : CoinSplit
      ([.recv CompRX0SS38.bunBytes, .rng cliCoins0,
        .pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] ++
       [.recv CompSmallSubgroupTrace.highBitWireBytes, .rng rngMsg39, .accept acceptMsg40]) τhw := by
    rw [← recvMsg38_eq_ss_highBitWireBytes]; exact hcs
  exact no_coinSplit_matchedPrefix_of_gen
    [.recv CompRX0SS38.bunBytes, .rng cliCoins0,
     .pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes]
    CompSmallSubgroupTrace.highBitWireBytes rngMsg39 acceptMsg40
    (by decide)
    highBitWireBytes_props.1 highBitWireBytes_props.2
    highBitWireBytes_baseKey_ne_compPubOfOpt
    hnb hcs'

theorem ptB_eq_ptMsg35 : CompRX0SS38.ptB = ptMsg35 := by
  rw [CompRX0SS38.ptB_eq_hex]
  rfl

private theorem runWrapped_evSend : runWrapped evSend = true := by
  unfold runWrapped evSend
  dsimp only [Option.bind]
  rw [CompRPlantWire.sentWireBytes_eq]
  decide

private theorem list_eq_three_splits {α : Type} {a b c x : α} {xs ys : List α}
    (h : [a, b, c] = xs ++ x :: ys) :
    (xs = [] ∧ x = a ∧ ys = [b, c]) ∨
    (xs = [a] ∧ x = b ∧ ys = [c]) ∨
    (xs = [a, b] ∧ x = c ∧ ys = []) := by
  rcases xs with _ | ⟨x₀, _ | ⟨x₁, _ | ⟨x₂, xs⟩⟩⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · simp at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
  · simp at h

private theorem not_knownBaseKeyOn_of_bobDone_nil {i : ExternInterpretation} {S : Sem}
    {g : Ghost} {tr : ExecTrace} {p : PreKeyFields}
    (h : bobDoneBaseKeys tr = []) : ¬ KnownBaseKeyOn i S g tr p := by
  rintro ⟨ek, hek, _⟩; rw [h] at hek; cases hek

/-- Generic `SpecHalf` reduction for a 3-call (`init`, `send`, pre-key `recv`) small-subgroup CLI
trace under `compI0`. -/
theorem spec_half_pinned_443_of_gen
    (setup₀ : PQXDHSpqrSetup) (msg38 : HwBytes)
    (hhead38 : msg38.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag)
    (hq38 : (parsePreKeyWire msg38).isSome = true)
    (hno_mp : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (τhw : List MachineEvent),
      CompSetupSecrecy.NoBrk r ms →
      CoinSplit (flatEvents (cliEvents msg38)) τhw →
      ¬ MatchedPrefix compI0 r S who g ms τhw)
    (hBsc : ∀ (blk₁ : List MachineEvent),
      CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁ →
      ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields),
        compFitsPinned setup₀ compI0 r →
        CompSetupSecrecy.NoBrk r ms →
        ExplainsCli compI0 r S who ok (flatEvents [.run evInit, .run evSend])
          ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) g ms →
        parsePreKeyWire msg38 = some p →
        ∃ (pre mid post : List Move) (hb_eq : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
          let tr₁ := (runMoves pre (setupTrace r)).1
          let o := aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
          let m₀ := Move.aliceStart r.alice r.bob 4 6 hb_eq shown
          let tr₂ := (runMoves mid (m₀.next tr₁)).1
          let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post
          ms = pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post ∧
          Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (setupTrace r) pre ∧
          Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (m₀.next tr₁) mid ∧
          Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect
            ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post ∧
          m₀.next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o ∧
          ∃ x ∈ preKeyRepresentations compI0 r S g ms' msg38,
            ¬ BobStartCollision compI0 r S g ms' p x) :
    cliCompShape.SpecHalf (cliCompFitsPinned setup₀) (cliEvents msg38) := by
  intro (iw : cliCompShape.Interp) (r : Records) hfits
  have hwf : ProtocolSetupWF r := hfits.1.1.1
  have hiw : iw.1 = compI0 := hfits.1.2.1
  have hfits0 : compFitsPinned setup₀ compI0 r := hiw ▸ hfits.1
  refine ⟨hwf, fun (S : Sem) _ hdisj => ?_⟩
  change (∃ g ss vis, Explains iw.1 r S g ss vis (cliEvents msg38)) ∨
    CollisionAfterExplainedPrefix iw.1 r S (cliEvents msg38) at hdisj
  rw [hiw] at hdisj
  rcases hdisj with ⟨g, ss, vis, hex⟩ | hcol
  · have hex_cl := explainsClassical_of hex (breakFree_cliEvents msg38)
    have hnrc : ¬ ReadCollisionCliClassical compI0 r S g ss (cliEvents msg38) := by
      refine not_readCollisionCliClassical_of_preKey_recv hwf.1 hex_cl.2.2.2 ?_
      intro evs₁ ev evs₂ out hevs ⟨peer, hcmd⟩ _
      rcases list_eq_three_splits hevs with ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩
      · injection hev with hev'; subst hev'; cases hcmd
      · injection hev with hev'; subst hev'; cases hcmd
      · injection hev with hev'; subst hev'
        refine ⟨hq38, ?_⟩
        intro ev' out' hev' ⟨p', hcmd'⟩ _
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hev'
        rcases hev' with h1 | h2
        · injection h1 with h1'; subst h1'; cases hcmd'
        · injection h2 with h2'; subst h2'; cases hcmd'
    obtain ⟨τ, ms, hex_cli, _, hnb, _⟩ :=
      xlate_inv_with_noBrk hwf (schedFits_cliEvents msg38) hex_cl hnrc
    exact hno_mp r S g ms τ hnb hex_cli.1 hex_cli.2.1
  · refine not_collisionAfterExplainedPrefix_of_splits (breakFree_cliEvents msg38) ?_ hcol
    intro evs₁ ev evs₂ g ss vis hevs hex
    rcases list_eq_three_splits hevs with ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩
    · injection hev with hev'; subst hev'
      exact not_nextEventCollidesClassical_init rfl
    · injection hev with hev'; subst hev'
      have hnrc₁ : ¬ ReadCollisionCliClassical compI0 r S g ss [.run evInit] := by
        refine not_readCollisionCliClassical_of_no_recv ?_
        intro ev' out' hev' ⟨p', hcmd'⟩ _
        simp only [List.mem_singleton] at hev'
        injection hev' with hev''; subst hev''; cases hcmd'
      refine not_nextEventCollidesClassical_send hwf schedFits_evInit hex hnrc₁ rfl ?_
      intro τ ms hex_cli _ hnb hbme hmcol
      obtain ⟨hτ, hex_hw⟩ := CliCoinSplit.init_exit0_cut_eq (by decide) cliCoins0_length hex_cli
      subst hτ
      dsimp only [evInit, evSend] at hex_hw hbme
      rw [init_draws_cliCoins0_eq_hb, trace_take_35_eq] at hex_hw
      have hem : EventMatchesEntry compI0 r S g (.pt ptMsg35) (ptEntryOfNextEncrypt r ms) :=
        ⟨rfl, by simpa [EventMatchesEntry, BytesMatchEntry, ptEntryAt, ptEntryOfNextEncrypt, ptB_eq_ptMsg35, eventBytes] using hbme⟩
      have hmcol' : MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
          (runTraceMoves r ms) (runVis r ms)
          (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms := by
        simpa [MemoCollisionOn, ptEntryAt, ptEntryOfNextEncrypt] using hmcol
      exact ptDead35_self hwf hnb hex_hw hem hmcol'
    · injection hev with hev'; subst hev'
      have hnrc₂ : ¬ ReadCollisionCliClassical compI0 r S g ss [.run evInit, .run evSend] := by
        refine not_readCollisionCliClassical_of_no_recv ?_
        intro ev' out' hev' ⟨p', hcmd'⟩ _
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hev'
        rcases hev' with h1 | h2
        · injection h1 with h1'; subst h1'; cases hcmd'
        · injection h2 with h2'; subst h2'; cases hcmd'
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hq38
      rcases hmsg : msg38 with _ | ⟨tag, body⟩
      · rw [hmsg] at hp; cases hp
      · have htag : tag ≠ DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by
          intro h; apply hhead38; rw [hmsg, h]; rfl
        have hbob_nil : bobDoneBaseKeys (runTrace r ss) = [] := by
          refine bobDoneBaseKeys_nil_of_matchesEventsClassical_no_recv hwf.1 hex.2.2.2 ?_
          intro ev' out' hev' ⟨p', hcmd'⟩ _
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hev'
          rcases hev' with h1 | h2
          · injection h1 with h1'; subst h1'; cases hcmd'
          · injection h2 with h2'; subst h2'; cases hcmd'
        have hnkb : ¬ KnownBaseKeyOn compI0 S g (runTrace r ss) p :=
          not_knownBaseKeyOn_of_bobDone_nil hbob_nil
        have hnkm : ¬ KyberMismatch compI0 r p := not_kyberMismatch_compI0 r p
        refine not_nextEventCollidesClassical_recv_preKey hwf schedFits_evInit_evSend hex hnrc₂
          rfl rfl htag (hmsg ▸ hp) hnkb hnkm ?_
        intro τ ms hex_cli _ hnb htr hsalts hpre_vis hpt_vis
        obtain ⟨blk₁, hτ, hcs₁, _⟩ :=
          CliCoinSplit.explainsCli_init_send_decomp (by decide) cliCoins0_length hex_cli
        rw [initiateDrawsOfCoins_cliCoins0_eq] at hτ
        subst hτ
        obtain ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hpre, hmid, hpost, hm₀, x, hx, hnbsc⟩ :=
          hBsc blk₁ hcs₁ r S g ms p hfits0 hnb hex_cli hp
        subst hms_eq
        let tr₁ := (runMoves pre (setupTrace r)).1
        let o := aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
        let m₀ := Move.aliceStart r.alice r.bob 4 6 hb_eq shown
        let tr₂ := (runMoves mid (m₀.next tr₁)).1
        let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post
        have htr' : runTraceMoves r ms' = runTrace r ss :=
          (CompRVariantFree38.runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl (tr₂.length + 2)
            (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))).symm.trans htr
        have hsalts' : honestSalts r ms' = honestSaltsOf r ss :=
          (honestSalts_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl (tr₂.length + 2)
            (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))).symm.trans hsalts
        have hpre' : prefixTerms r (runTrace r ss) (runVis r ms') = prefixTerms r (runTrace r ss) vis :=
          prefixTerms_split38_swap_eq_of_init_send hwf.1 rfl rfl rfl rfl runWrapped_evSend hex.2.2.2
            rfl hpre hmid hpost hm₀ htr hpre_vis hpt_vis
        have hpt' : plaintextTerms (runVis r ms') = plaintextTerms vis :=
          (plaintextTerms_split38_swap_eq hwf.1 (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
            hpre hmid hpost).trans hpt_vis
        have hx' : x ∈ preKeyRepresentations compI0 r S g ms' (tag :: body) := by
          rwa [← hmsg]
        exact ⟨ms', x, htr', hsalts', hpre', hpt', hx', hnbsc⟩

theorem spec_half_pinned :
    cliCompShape.SpecHalf
      (cliCompFitsPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
      Witnesses.Cheval26SmallSubgroupHighBitCli.trace := by
  rw [← cliSetup_eq, ← cliEvents_eq]
  refine spec_half_pinned_443_of_gen setup recvMsg38
    (by rw [recvMsg38_eq_ss_highBitWireBytes]; exact highBitWireBytes_props.1)
    (by rw [recvMsg38_eq_ss_highBitWireBytes]; exact highBitWireBytes_props.2)
    (fun _ _ _ _ _ hnb hcs => no_coinSplit_matchedPrefix hnb hcs)
    (fun blk₁ hcs₁ r' S' g' ms' p hfits' hnb' hex' hp => ?_)
  rw [recvMsg38_eq_highBitWireBytes] at hp ⊢
  obtain ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hpre, hmid, hpost, hm₀, _, x, hx, hnbsc⟩ :=
    noBsc38HB_cli_swap hcs₁ r' S' g' ms' p hfits' hnb' hex' hp
  exact ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hpre, hmid, hpost, hm₀, x, hx, hnbsc⟩

theorem cliCompFitsPinned_satisfiable :
    ∃ iw r, cliCompFitsPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup iw r :=
  Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.cliCompFitsPinned_satisfiable_hb

end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge

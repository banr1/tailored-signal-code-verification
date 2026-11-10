/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.World.TopPure
public import Symbolic.Proofs.Swarm.CREF.Sanitize
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
public import Symbolic.Proofs.Swarm.CREF.Cli.World.CallCountPure
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Cli.World.XplTransferPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.Leaves.IC12_Stage1MatchedPrefixPure

/-!
# Promote Pre-Key Receive Reject, Stop, and Turn-Update Lemmas

Proves `CoinSplit`, `MatchedPrefix`, `Clean`, `PureCRel`, and `COpkRelC` preservation for rejected
or stopped promote pre-key `recv` calls (`rpkProm_reject_live`), dispatching parseable pre-key
wires through `Sanitize.sanitizeMoves` and unparseable wires through bare `Move.reject []`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SignalSession (oneTimePreKeyFile coinsFile bundleDir)
open DY.Libsignal.Composed.Refinement.Cli (DirectorySnapshot CliCall CliTurn PreKeyNoMatch CoinSplit
  cliEntryEvents cliExitEvents sessionPathOf scrub SamePath peerOf)

/-! ## `CoinSplit` Helpers -/

theorem cliExitEvents_of_ne_zero (c : CliCall) {code : Nat} (hne : code ≠ 0) (out : HwBytes) :
    cliExitEvents c code out = [] := by
  rcases code with _ | n
  · exact absurd rfl hne
  · cases c.cmd <;> rfl

theorem cliExitEvents_of_recv_ok {c : CliCall} {peer : CryptoVerification.SignalSession.Address}
    (hcmd : c.cmd = .recv peer) (out : HwBytes) :
    cliExitEvents c 0 out = [.accept out] := by
  simp [cliExitEvents, hcmd]

theorem coinSplit_rpkProm_stop {c : CliCall} {peer : CryptoVerification.SignalSession.Address}
    (hcmd : c.cmd = .recv peer) :
    CoinSplit (cliEntryEvents c) [.recv c.stdin] := by
  simpa [cliInputEvent, hcmd] using coinSplit_cliEntry_drop_rng c

theorem coinSplit_rpkProm_reject {c : CliCall} {peer : CryptoVerification.SignalSession.Address}
    (hcmd : c.cmd = .recv peer) {code : Nat} (hne : code ≠ 0) (out : HwBytes) :
    CoinSplit (cliEntryEvents c ++ cliExitEvents c code out) [.recv c.stdin] := by
  rw [cliExitEvents_of_ne_zero c hne out, List.append_nil]
  exact coinSplit_rpkProm_stop hcmd

theorem coinSplit_rpkProm_accept_nil {c : CliCall}
    {peer : CryptoVerification.SignalSession.Address}
    (hcmd : c.cmd = .recv peer) (out : HwBytes) :
    CoinSplit (cliEntryEvents c ++ cliExitEvents c 0 out) (promAccBlk c.stdin [] out) := by
  have hent := coinSplit_rpkProm_stop hcmd
  have hexit : CoinSplit (cliExitEvents c 0 out) [.accept out] := by
    rw [cliExitEvents_of_recv_ok hcmd]
    exact coinSplit_refl_of_no_rng (by simp)
  simpa [promAccBlk] using coinSplit_append hent hexit

theorem coinSplit_rpkProm_accept_rng {c : CliCall}
    {peer : CryptoVerification.SignalSession.Address}
    (hcmd : c.cmd = .recv peer) (hlen : c.coins.length = 32) (out : HwBytes) :
    CoinSplit (cliEntryEvents c ++ cliExitEvents c 0 out)
      (promAccBlk c.stdin [.rng c.coins] out) := by
  have hne : c.coins ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    cases hlen
  have hent : CoinSplit (cliEntryEvents c) [.recv c.stdin, .rng c.coins] := by
    simpa [cliInputEvent, hcmd] using
      coinSplit_cliEntry_one_piece c hne (List.prefix_refl c.coins)
  have hexit : CoinSplit (cliExitEvents c 0 out) [.accept out] := by
    rw [cliExitEvents_of_recv_ok hcmd]
    exact coinSplit_refl_of_no_rng (by simp)
  simpa [promAccBlk] using coinSplit_append hent hexit

/-! ## Pre-Key Reject Preservation -/

theorem rpkProm_callStarts_fail_blk (b : HwBytes) (ds : List HwBytes) :
    (MachineEvent.recv b :: ds.map MachineEvent.rng).filter
      (fun e => eventKind e == .recv || eventKind e == .pt) = [.recv b] := by
  have hnil : (ds.map MachineEvent.rng).filter
      (fun e => eventKind e == .recv || eventKind e == .pt) = [] := by
    induction ds with
    | nil => rfl
    | cons _ _ ih => exact ih
  rw [List.filter_cons_of_pos (by simp [eventKind]), hnil]

private theorem movesFrom_noEff_of_invisible :
    ∀ (tr : ExecTrace) (ms : List Move),
      MovesFrom InvisibleNoEffect tr ms →
      MovesFrom (fun tr m => NoSessionEffect tr m) tr ms
  | _, [], _ => trivial
  | _, _ :: ms, ⟨⟨_, hne⟩, hms⟩ => ⟨hne, movesFrom_noEff_of_invisible _ ms hms⟩

private theorem movesFrom_noEff_append :
    ∀ (tr : ExecTrace) (ms₁ ms₂ : List Move),
      MovesFrom (fun tr m => NoSessionEffect tr m) tr ms₁ →
      MovesFrom (fun tr m => NoSessionEffect tr m) (runMoves ms₁ tr).1 ms₂ →
      MovesFrom (fun tr m => NoSessionEffect tr m) tr (ms₁ ++ ms₂)
  | _, [], _, _, h₂ => by simpa [runMoves] using h₂
  | tr, m :: ms₁, ms₂, ⟨h₁, hms₁⟩, h₂ =>
    ⟨h₁, movesFrom_noEff_append (m.next tr) ms₁ ms₂ hms₁ (by simpa [runMoves_cons_fst] using h₂)⟩

/-- Pure block-quietness of `.recv b :: ds.map .rng` (`ds.length < 34`): no move in an `XplBlock`
for a non-accepting `recv` block can mutate session state or emit sends/accepts. -/
theorem rpkProm_fail_quiet {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ δ : List Move}
    {acc : List MachineEvent} {b : HwBytes} {ds : List HwBytes}
    (hlen : ds.length < 34)
    (hB : XplBlock interp r S who g ms₀ δ acc (.recv b :: ds.map MachineEvent.rng)) :
    MovesFrom (fun tr m => NoSessionEffect tr m) (runTraceMoves r ms₀) δ := by
  let blk : List MachineEvent := .recv b :: ds.map MachineEvent.rng
  have hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    simp only [blk, List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  have htail : ∀ e ∈ blk.tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    simp only [blk, List.tail_cons] at he
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp he
    simp [eventKind]
  obtain ⟨pre, m, post, rfl, hpre, ⟨_, ha, hm⟩, hpost⟩ :=
    xpl_oneMove hB hhead (by simp) htail
  have hm_noEff : NoSessionEffect (runMoves pre (runTraceMoves r ms₀)).1 m := by
    obtain ⟨v, hv, hvk, _⟩ := xpl_head_entry hm (rfl : blk.head? = some (.recv b))
    have hrk : RecvHeadKind m := xpl_recvHeadKind m _ hv (by simpa [eventKind] using hvk)
    have hlen_vis : (m.vis (runMoves pre (runTraceMoves r ms₀)).1).length < 35 := by
      rw [← xpl_forall₂_length hm]
      simp only [List.length_cons, List.length_map]
      omega
    have hnoacc_vis : ∀ w ∈ m.vis (runMoves pre (runTraceMoves r ms₀)).1, w.kind ≠ .accept := by
      intro w hw
      obtain ⟨e, he, hew⟩ := xpl_forall₂_mem_right hm w hw
      rw [xpl_kind_of_matches hew]
      rcases List.mem_cons.mp he with rfl | he'
      · simp [eventKind]
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp he'
        simp [eventKind]
    cases m
    case aliceStart => exact noSessionEffect_aliceStart_short ha hlen_vis
    case bobStart => exact noSessionEffect_of_no_accept trivial ha hnoacc_vis
    case decrypt => exact noSessionEffect_of_no_accept trivial ha hnoacc_vis
    case decryptSkipped => exact noSessionEffect_of_no_accept trivial ha hnoacc_vis
    case reject => exact noSessionEffect_of_no_accept trivial ha hnoacc_vis
    all_goals exact False.elim hrk
  exact movesFrom_noEff_append (runTraceMoves r ms₀) pre (m :: post)
    (movesFrom_noEff_of_invisible _ pre hpre)
    ⟨hm_noEff, movesFrom_noEff_of_invisible _ post hpost⟩

private theorem clearStuckWrap_prekeyPath?_imp {tr : ExecTrace} {m : Move} {promote : Bool}
    (hp : (Sanitize.clearStuckWrap tr m).prekeyPath? = some promote) :
    m.prekeyPath? = some promote := by
  cases m <;> simp only [Sanitize.clearStuckWrap, Move.prekeyPath?] at hp ⊢
  case bobStart => exact hp
  case decrypt me si mi pq sp w => revert hp; cases (tr.getMessageSentAt mi).isSome <;> simp
  case decryptSkipped me si mi k pq sp w => revert hp; cases (tr.getMessageSentAt mi).isSome <;> simp
  all_goals cases hp

theorem rpkProm_sanitize_clean {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent} (hc : Clean interp r S who ok g ms acc) :
    Clean interp r S who ok g (Sanitize.sanitizeMoves (setupTrace r) ms) acc := by
  let ms_s := Sanitize.sanitizeMoves (setupTrace r) ms
  have hpath_s : PathFaithful interp r S g ms_s acc := by
    intro i m' promote b' p hi hpath hcall hparse
    rw [Sanitize.getElem?_sanitizeMoves] at hi
    rcases hmi : ms[i]? with _ | m
    · simp [hmi] at hi
    · simp only [hmi, Option.map_some, Option.some.injEq] at hi
      subst hi
      simp only [ms_s, Sanitize.sanitizeMoves_take, Sanitize.runVis_sanitizeMoves,
        Sanitize.runTrace_sanitizeMoves] at hcall ⊢
      exact hc.matched.2.2.2.1 i m promote b' p hmi
        (clearStuckWrap_prekeyPath?_imp hpath) hcall hparse
  exact ⟨⟨⟨hc.matched.1, Sanitize.modelRun_sanitizeMoves hc.matched.2.1,
    Sanitize.roleFaithful_sanitizeMoves hc.matched.2.2.1, hpath_s,
    Sanitize.readFaithful_sanitizeMoves hc.matched.2.2.2.2.1,
    by simpa [ms_s] using hc.matched.2.2.2.2.2⟩,
    Sanitize.outcomeFaithful_sanitizeMoves hc.1.2⟩,
    mt Sanitize.readCollision_sanitizeMoves_iff.mp hc.2⟩

theorem rpkProm_sanitize_path_fail {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent} (b : HwBytes) (ds : List HwBytes)
    (hc : Clean interp r S who ok g ms acc) :
    PathFaithful interp r S g (Sanitize.sanitizeMoves (setupTrace r) ms)
      (acc ++ (.recv b :: ds.map MachineEvent.rng)) := by
  have hc_s := rpkProm_sanitize_clean hc
  intro i m' promote b' p hi hpath hcall hparse
  have hk := Sanitize.callCount_take_lt_of_sanitizeMoves_prekeyPath? hc.matched hi hpath
  have hcs_app : callStarts (acc ++ (.recv b :: ds.map MachineEvent.rng)) =
      callStarts acc ++ [.recv b] := by
    unfold callStarts
    rw [List.filter_append]
    exact congrArg (callStarts acc ++ ·) (rpkProm_callStarts_fail_blk b ds)
  rw [hcs_app, List.getElem?_append_left hk] at hcall
  exact hc_s.matched.2.2.2.1 i m' promote b' p hi hpath hcall hparse

theorem rpkProm_unparseable_path_fail {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent} {b : HwBytes} (hnone : parsePreKeyWire b = none)
    (ds : List HwBytes) (hc : Clean interp r S who ok g ms acc) :
    PathFaithful interp r S g ms (acc ++ (.recv b :: ds.map MachineEvent.rng)) := by
  intro i m' promote b' p hi hpath hcall hparse
  have hcs_app : callStarts (acc ++ (.recv b :: ds.map MachineEvent.rng)) =
      callStarts acc ++ [.recv b] := by
    unfold callStarts
    rw [List.filter_append]
    exact congrArg (callStarts acc ++ ·) (rpkProm_callStarts_fail_blk b ds)
  rw [hcs_app] at hcall
  let k := callCount (runVis r (ms.take i))
  by_cases hk : k < (callStarts acc).length
  · rw [List.getElem?_append_left hk] at hcall
    exact hc.matched.2.2.2.1 i m' promote b' p hi hpath hcall hparse
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hk)] at hcall
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hk) with hk_eq | hk_gt
    · rw [← hk_eq, Nat.sub_self] at hcall
      simp only [List.getElem?_cons_zero, Option.some.injEq, MachineEvent.recv.injEq] at hcall
      subst hcall
      rw [hnone] at hparse
      cases hparse
    · have hsub : k - (callStarts acc).length ≥ 1 := by omega
      have hnone_idx : ([MachineEvent.recv b] : List MachineEvent)[k - (callStarts acc).length]? = none :=
        List.getElem?_eq_none (by simp; omega)
      rw [hnone_idx] at hcall
      cases hcall

theorem rpkProm_parseable_reject_live {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {t : CliTurn} {accepted : List HwBytes} {acc : List MachineEvent}
    {b : HwBytes} {pw : PreKeyFields}
    (_hparse : parsePreKeyWire b = some pw)
    (hlive : CliLiveAt interp r S who ok t accepted acc) :
    (∃ g' ms', MatchedPrefix interp r S who g' ms' (acc ++ [.recv b])) ∧
    (ok (callStarts acc).length = false →
      (∃ g' ms', Clean interp r S who ok g' ms' (acc ++ [.recv b])) ∧
      PureCRel interp r S who ok (t.leakRecords r) t.sent accepted (acc ++ [.recv b]) ∧
      COpkRelC interp r S who ok (t.opkUsed r) (acc ++ [.recv b])) := by
  obtain ⟨⟨g, ms, hc⟩, hrel, hopk⟩ := hlive
  refine ⟨⟨g, Sanitize.sanitizeMoves (setupTrace r) ms ++ [.reject []],
      Symbolic.Swarm.Leaves.IC12Stage1MP.matchedPrefix_snoc_reject b []
        (rpkProm_sanitize_clean hc).matched (rpkProm_sanitize_path_fail b [] hc)⟩,
    fun hok => ?_⟩
  have hhead : ∀ e ∈ ([MachineEvent.recv b]).head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  have hnosend : ∀ s, MachineEvent.send s ∉ ([MachineEvent.recv b] : List MachineEvent) := by simp
  have hnoacc : ∀ e ∈ ([MachineEvent.recv b] : List MachineEvent), eventKind e ≠ .accept := by
    intro e he; simp only [List.mem_singleton] at he; subst he; simp [eventKind]
  have hc_s := rpkProm_sanitize_clean hc
  have hc' := Symbolic.Swarm.Leaves.IC12Stage1MP.clean_snoc_reject b [] ⟨hc_s.1, hc_s.2⟩
    (rpkProm_sanitize_path_fail b [] hc) hok
  refine ⟨⟨g, Sanitize.sanitizeMoves (setupTrace r) ms ++ [.reject []], ⟨hc'.1, hc'.2⟩⟩,
    pureCRel_transfer_quiet hhead hnosend
      (fun _ _ _ hB => rpkProm_fail_quiet (ds := []) (by decide) hB) hrel,
    cOpkRelC_of_no_accept' hopk id hhead hnoacc⟩

theorem rpkProm_unparseable_reject_live {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {t : CliTurn} {accepted : List HwBytes} {acc : List MachineEvent}
    {b : HwBytes}
    (hnone : parsePreKeyWire b = none)
    (hlive : CliLiveAt interp r S who ok t accepted acc) :
    (∃ g' ms', MatchedPrefix interp r S who g' ms' (acc ++ [.recv b])) ∧
    (ok (callStarts acc).length = false →
      (∃ g' ms', Clean interp r S who ok g' ms' (acc ++ [.recv b])) ∧
      PureCRel interp r S who ok (t.leakRecords r) t.sent accepted (acc ++ [.recv b]) ∧
      COpkRelC interp r S who ok (t.opkUsed r) (acc ++ [.recv b])) := by
  obtain ⟨⟨g, ms, hc⟩, hrel, hopk⟩ := hlive
  refine ⟨⟨g, ms ++ [.reject []],
      Symbolic.Swarm.Leaves.IC12Stage1MP.matchedPrefix_snoc_reject b [] hc.matched
        (rpkProm_unparseable_path_fail hnone [] hc)⟩,
    fun hok => ?_⟩
  have hhead : ∀ e ∈ ([MachineEvent.recv b]).head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  have hnosend : ∀ s, MachineEvent.send s ∉ ([MachineEvent.recv b] : List MachineEvent) := by simp
  have hnoacc : ∀ e ∈ ([MachineEvent.recv b] : List MachineEvent), eventKind e ≠ .accept := by
    intro e he; simp only [List.mem_singleton] at he; subst he; simp [eventKind]
  have hc' := Symbolic.Swarm.Leaves.IC12Stage1MP.clean_snoc_reject b [] ⟨hc.1, hc.2⟩
    (rpkProm_unparseable_path_fail hnone [] hc) hok
  refine ⟨⟨g, ms ++ [.reject []], ⟨hc'.1, hc'.2⟩⟩,
    pureCRel_transfer_quiet hhead hnosend
      (fun _ _ _ hB => rpkProm_fail_quiet (ds := []) (by decide) hB) hrel,
    cOpkRelC_of_no_accept' hopk id hhead hnoacc⟩

/-- Preserves `MatchedPrefix`, `Clean`, `PureCRel`, and `COpkRelC` across a rejected or stopped
`recv` input `b`, dispatching on `parsePreKeyWire b`. -/
theorem rpkProm_reject_live {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {t : CliTurn} {accepted : List HwBytes} {acc : List MachineEvent} (b : HwBytes)
    (hlive : CliLiveAt interp r S who ok t accepted acc) :
    (∃ g' ms', MatchedPrefix interp r S who g' ms' (acc ++ [.recv b])) ∧
    (ok (callStarts acc).length = false →
      (∃ g' ms', Clean interp r S who ok g' ms' (acc ++ [.recv b])) ∧
      PureCRel interp r S who ok (t.leakRecords r) t.sent accepted (acc ++ [.recv b]) ∧
      COpkRelC interp r S who ok (t.opkUsed r) (acc ++ [.recv b])) := by
  cases hparse : parsePreKeyWire b with
  | none => exact rpkProm_unparseable_reject_live hparse hlive
  | some pw => exact rpkProm_parseable_reject_live hparse hlive

/-! ## `CliTurn.after` Transitions on Rejected `recv` -/

@[simp] theorem after_sent_of_recv {r : ProtocolSetup} {t : CliTurn} {c : CliCall}
    {peer : CryptoVerification.SignalSession.Address}
    (hcmd : c.cmd = .recv peer) (code : Nat) (out : HwBytes) (files : DirectorySnapshot) :
    (t.after r c code out files).sent = t.sent := by
  simp [CliTurn.after, hcmd]

@[simp] theorem after_bobOff_of_ne_zero {r : ProtocolSetup} {t : CliTurn} {c : CliCall}
    {code : Nat} (hne : code ≠ 0) (out : HwBytes) (files : DirectorySnapshot) :
    (t.after r c code out files).bobOff = t.bobOff := by
  simp [CliTurn.after, hne]

set_option linter.auxLemma false in
private theorem prom_splitSlash_go_cons_ne (cur : List Char) {c : Char} (hc : c ≠ '/') (cs : List Char) :
    Arm64.splitSlash.go cur (c :: cs) = Arm64.splitSlash.go (c :: cur) cs := by
  delta Arm64.splitSlash.go
  dsimp only [List.brecOn, List.brecOn.go, PProd.fst, PProd.snd]
  delta Arm64.splitSlash.go._f Arm64.splitSlash.go.match_1
  dsimp only
  split
  · next h => exact absurd h hc
  · rfl

private theorem prom_splitSlash_go_append_slash :
    ∀ (cs1 cur cs2 : List Char), '/' ∉ cs1 →
      Arm64.splitSlash.go cur (cs1 ++ '/' :: cs2) =
        String.ofList (cur.reverse ++ cs1) :: Arm64.splitSlash.go [] cs2
  | [], cur, cs2, _ => by rw [List.nil_append, List.append_nil]; rfl
  | c :: cs1, cur, cs2, h => by
    have hc : c ≠ '/' := fun he => h (he ▸ List.mem_cons_self ..)
    have ih := prom_splitSlash_go_append_slash cs1 (c :: cur) cs2
      (fun hm => h (List.mem_cons_of_mem _ hm))
    rw [List.cons_append, prom_splitSlash_go_cons_ne cur hc (cs1 ++ '/' :: cs2), ih]
    simp [List.append_assoc]

private theorem prom_normalizePath_head_slash (dir rest : String)
    (hno : '/' ∉ dir.toList) (hne : (!dir.isEmpty && dir != ".") = true) :
    (Arm64.normalizePath ((dir ++ "/") ++ rest)).head? = some dir := by
  have hsplit : Arm64.splitSlash ((dir ++ "/") ++ rest) =
      dir :: Arm64.splitSlash.go [] rest.toList := by
    unfold Arm64.splitSlash
    simpa [String.toList_append] using
      prom_splitSlash_go_append_slash dir.toList [] rest.toList hno
  simp [Arm64.normalizePath, hsplit, hne]

theorem prom_normalizePath_sessionPathOf_head (r : ProtocolSetup) (p : Participant) :
    (Arm64.normalizePath (sessionPathOf r p)).head? = some "sessions" :=
  prom_normalizePath_head_slash "sessions" (peerOf r p).text (by decide) (by decide)

theorem prom_normalizePath_oneTimePreKeyFile_head (id : BitVec 32) :
    (Arm64.normalizePath (oneTimePreKeyFile id)).head? = some "one-time-pre-keys" :=
  prom_normalizePath_head_slash "one-time-pre-keys" (toString id.toNat) (by decide) (by decide)

theorem prom_scrub_sessionPathOf (d : String → Option HwBytes) (r : ProtocolSetup) (p : Participant) :
    scrub d (sessionPathOf r p) = d (sessionPathOf r p) := by
  unfold scrub
  have h1 : SamePath (sessionPathOf r p) coinsFile = false := by
    unfold SamePath
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have hs := prom_normalizePath_sessionPathOf_head r p
    have hc : (Arm64.normalizePath coinsFile).head? = some "coins" := by decide
    rw [heq, hc] at hs; exact absurd hs (by decide)
  have h2 : ((Arm64.normalizePath (sessionPathOf r p)).head? == some bundleDir) = false := by
    rw [prom_normalizePath_sessionPathOf_head]
    decide
  simp [h1, h2]

theorem prom_scrub_oneTimePreKeyFile (d : String → Option HwBytes) (id : BitVec 32) :
    scrub d (oneTimePreKeyFile id) = d (oneTimePreKeyFile id) := by
  unfold scrub
  have h1 : SamePath (oneTimePreKeyFile id) coinsFile = false := by
    unfold SamePath
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have hs := prom_normalizePath_oneTimePreKeyFile_head id
    have hc : (Arm64.normalizePath coinsFile).head? = some "coins" := by decide
    rw [heq, hc] at hs; exact absurd hs (by decide)
  have h2 : ((Arm64.normalizePath (oneTimePreKeyFile id)).head? == some bundleDir) = false := by
    rw [prom_normalizePath_oneTimePreKeyFile_head]
    decide
  simp [h1, h2]

theorem after_unchanged_of_recv_reject {r : ProtocolSetup} {t : CliTurn} {c : CliCall}
    {peer : CryptoVerification.SignalSession.Address}
    (hcmd : c.cmd = .recv peer) {code : Nat} (hne : code ≠ 0) (out : HwBytes) (files : DirectorySnapshot)
    (hsess : files (sessionPathOf r c.party) = t.dirs c.party (sessionPathOf r c.party))
    (hopk : c.party = r.bob →
      files (oneTimePreKeyFile r.opkId) = t.dirs r.bob (oneTimePreKeyFile r.opkId)) :
    (t.after r c code out files).records r = t.records r ∧
    (t.after r c code out files).leakRecords r = t.leakRecords r ∧
    (t.after r c code out files).sent = t.sent ∧
    (t.after r c code out files).opkUsed r = t.opkUsed r := by
  have hrec : (t.after r c code out files).records r = t.records r := by
    funext q
    by_cases hqc : q = c.party
    · subst hqc
      simp only [CliTurn.records, CliTurn.after, ↓reduceIte]
      rw [prom_scrub_sessionPathOf, hsess]
    · simp [CliTurn.records, CliTurn.after, hqc]
  have hleak : (t.after r c code out files).leakRecords r = t.leakRecords r := by
    funext q
    simp [CliTurn.leakRecords, hrec, after_bobOff_of_ne_zero hne]
  have hopk' : (t.after r c code out files).opkUsed r = t.opkUsed r := by
    by_cases hbc : r.bob = c.party
    · simp only [CliTurn.opkUsed, CliTurn.after, hbc, ↓reduceIte, prom_scrub_oneTimePreKeyFile]
      rw [hopk hbc.symm, hbc]
    · simp [CliTurn.opkUsed, CliTurn.after, hbc]
  exact ⟨hrec, hleak, after_sent_of_recv hcmd code out files, hopk'⟩

end Symbolic.Swarm.CREF.Cli

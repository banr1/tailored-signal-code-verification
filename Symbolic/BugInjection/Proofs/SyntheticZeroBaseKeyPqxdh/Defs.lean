/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Synthetic.Witnesses.ZeroBaseKeyPqxdhCli
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.NoFullMatch
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone
public import Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj
public import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
public import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepPtAtomsTR

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticZeroBaseKeyPqxdh.Defs

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.Defs
open Symbolic.BugInjection
open Symbolic.BugInjection.Synthetic
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
  (evInit evSend rngMsg39 rngMsg39_eq_hex)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
  (AllBobDone bobDoneBaseKeys_of_allBobDone mem_bobDoneBaseKeys_of_mem_sessionBaseKeys)

def macZbk8 : HwBytes :=
  [0xfe#8, 0x52#8, 0x0a#8, 0x62#8, 0x82#8, 0x58#8, 0xd2#8, 0x5a#8]

def ctZbk16 : HwBytes :=
  [0x95#8, 0x0e#8, 0x0a#8, 0x35#8, 0x2b#8, 0x10#8, 0x2b#8, 0xba#8,
   0xbf#8, 0xd4#8, 0x95#8, 0x96#8, 0xe8#8, 0x25#8, 0x84#8, 0x58#8]

def addrZbk36 : HwBytes :=
  [0x00#8, 0x8a#8, 0x6f#8, 0x1c#8, 0x2e#8, 0x3b#8, 0x4d#8, 0x4e#8,
   0x5f#8, 0x9a#8, 0x0b#8, 0x1c#8, 0x2d#8, 0x3e#8, 0x4f#8, 0x5a#8,
   0x6b#8, 0x01#8, 0x00#8, 0x5d#8, 0x3e#8, 0x2f#8, 0x10#8, 0x7a#8,
   0x8b#8, 0x4c#8, 0x9d#8, 0x8e#8, 0x0f#8, 0xa1#8, 0xb2#8, 0xc3#8,
   0xd4#8, 0xe5#8, 0xf6#8, 0x01#8]

def forgedPt9 : HwBytes := hexBytes "666f72676564212121"

def msg38_zbk : HwBytes :=
  match (Witnesses.ZeroBaseKeyPqxdhCli.trace[2]? : Option CliEvent) with
  | some (.run ev) => ev.input
  | _ => []

section FastZbkWire

attribute [local irreducible] Symbolic.BugInjection.hexBytes

local elab "chars_of_hex_zbk" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

local elab "str_of_hex_zbk" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  return sLit

def msg38ZbkChars : List Char := chars_of_hex_zbk msg38_zbk

theorem msg38_zbk_head_eq : msg38_zbk = hexBytes (str_of_hex_zbk msg38_zbk) := rfl

theorem msg38_zbk_str_eq : (str_of_hex_zbk msg38_zbk) = String.ofList msg38ZbkChars := rfl

def msg38ZbkFast : HwBytes := hexBytes.go CompRPlantWire.hexDigit msg38ZbkChars

end FastZbkWire

theorem msg38_zbk_eq_fast : msg38_zbk = msg38ZbkFast := by
  change msg38_zbk = hexBytes.go CompRPlantWire.hexDigit msg38ZbkChars
  rw [msg38_zbk_head_eq, msg38_zbk_str_eq, CompRPlantWire.hexBytes_ofList]

attribute [local irreducible] Symbolic.BugInjection.hexBytes

def evRecvZbk : RunEvent :=
  { party := "bob"
    cmd := .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩
    input := msg38_zbk
    coins := rngMsg39
    exit := some (0, forgedPt9) }

def cliEventsZbk : List CliEvent := [.run evInit, .run evSend, .run evRecvZbk]

theorem cliEventsZbk_eq : cliEventsZbk = Witnesses.ZeroBaseKeyPqxdhCli.trace := by
  unfold cliEventsZbk evInit evSend evRecvZbk msg38_zbk forgedPt9
    Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose.cliCoins0
    Witnesses.ZeroBaseKeyPqxdhCli.trace
  dsimp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
  rw [CompRX0SS38.bunBytes_eq_hex, CompRX0SS38.ptB_eq_hex, CompRX0SS38.cB_eq_hex,
    CompRX0SS38.sentWireBytes_eq_hex, rngMsg39_eq_hex,
    Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge.nil_eq_hexBytes]

theorem compFits_hb_of_zbk {i : ExternInterpretation} {r : Records}
    (h : compFits Witnesses.ZeroBaseKeyPqxdhCli.setup i r) :
    compFits Witnesses.Cheval26SmallSubgroupHighBitComp.setup i r := by
  simpa [compFits, Witnesses.ZeroBaseKeyPqxdhCli.setup,
    Witnesses.Cheval26SmallSubgroupHighBitComp.setup,
    Witnesses.Cheval26SmallSubgroupHighBitCli.setup] using h

theorem compFitsPinned_hb_of_zbk {i : ExternInterpretation} {r : Records}
    (h : compFitsPinned Witnesses.ZeroBaseKeyPqxdhCli.setup i r) :
    compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup i r :=
  ⟨compFits_hb_of_zbk h.1, h.2⟩

theorem rowDigests_take8_ne_macZbk8 :
    ∀ d ∈ CompRI0TermInj.rowDigests, d.take 8 ≠ macZbk8 := by
  decide +kernel

theorem compTag4_ne_macZbk4 : compTag4 ≠ macZbk8.take 4 := by decide

theorem gamma_computeMac_length (S : Sem) (g : Ghost) (mk peerIk myIk wire : DY.Bytes) :
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk peerIk myIk wire)).length = 8 := by
  unfold DY.Libsignal.TripleRatchet.computeMac
  rw [CompFreshDistinct.gamma_trunc8_eq, List.length_take, CompFreshDistinct.gamma_hmac_length]
  decide

theorem gamma_computeMac_ne_macZbk8 (S : Sem) (g : Ghost) (mk peerIk myIk wire : DY.Bytes) :
    gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk peerIk myIk wire) ≠ macZbk8 := by
  unfold DY.Libsignal.TripleRatchet.computeMac
  rw [CompFreshDistinct.gamma_trunc8_eq]
  intro heq
  rcases CompRI0TermInj.gamma_kdfExtract_tag_or_row (S := S) (g := g)
      mk (DY.Concat.concat peerIk (DY.Concat.concat myIk wire)) with htag | hrow
  · have h4 : ((gamma compI0 S g
        (DY.Libsignal.TripleRatchet.hmac mk
          (DY.Concat.concat peerIk (DY.Concat.concat myIk wire)))).take 8).take 4 =
        macZbk8.take 4 := congrArg (List.take 4) heq
    rw [List.take_take, show min 4 8 = 4 by decide] at h4
    exact compTag4_ne_macZbk4 (htag.symm.trans h4)
  · exact rowDigests_take8_ne_macZbk8 _ hrow heq

theorem drop_sub_eight_append {a b : HwBytes} (hb : b.length = 8) :
    (a ++ b).drop ((a ++ b).length - 8) = b := by
  rw [List.length_append, hb, Nat.add_sub_cancel, List.drop_left' rfl]

theorem parseTrSignalMsg_gamma_drop8 {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {raw : DY.Bytes} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    (hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg)
    (hlen : (gamma i S g msg.mac).length = 8) :
    (gamma i S g raw).drop ((gamma i S g raw).length - 8) = gamma i S g msg.mac := by
  obtain ⟨_, hsp, _⟩ := Symbolic.Swarm.CREF.TR.G1.parseTrSignalMsg_unpack_c hparse
  have hraw : raw = DY.Concat.concat msg.wire msg.mac :=
    (Symbolic.Swarm.CREF.TR.G1.split_eq_some_concat_and_length_tr32 hsp).1
  rw [hraw, CompFreshDistinct.gamma_concat_eq]
  exact drop_sub_eight_append hlen

private theorem msg38ZbkFast_props :
    msg38ZbkFast.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag ∧
    (parsePreKeyWire msg38ZbkFast).isSome = true ∧
    (parsePreKeyWire msg38ZbkFast).map (fun p => p.message.drop (p.message.length - 8)) =
      some macZbk8 ∧
    (parsePreKeyWire msg38ZbkFast).map (fun p => p.preKeyId) = some none := by
  decide +kernel

theorem msg38_zbk_props :
    msg38_zbk.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag ∧
    (parsePreKeyWire msg38_zbk).isSome = true ∧
    (parsePreKeyWire msg38_zbk).map (fun p => p.message.drop (p.message.length - 8)) =
      some macZbk8 ∧
    (parsePreKeyWire msg38_zbk).map (fun p => p.preKeyId) = some none := by
  rw [msg38_zbk_eq_fast]
  exact msg38ZbkFast_props

open Symbolic.Swarm.CREF in
private theorem not_matchedPrefix_zbk_tail_gen {r : Records} {S : Sem} {g : Ghost}
    {ms : List Move} {b0 b1 rest : List MachineEvent}
    {bun pt wire : HwBytes} {rs0 : List MachineEvent} {tail1 : List MachineEvent}
    (hb0 : b0 = .recv bun :: rs0) (hrs0 : ∀ e ∈ rs0, eventKind e = .rng)
    (hb1 : b1 = .pt pt :: tail1) (htail1 : ∀ e ∈ tail1, eventKind e = .rng ∨ eventKind e = .send)
    (hhead_ne : wire.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag)
    (hq_some : (parsePreKeyWire wire).isSome = true)
    (hmac_z : (parsePreKeyWire wire).map (fun p => p.message.drop (p.message.length - 8)) =
      some macZbk8)
    (hrest_ne : ∀ e ∈ rest, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak)
    (hacc : ∃ e ∈ rest, eventKind e = .accept)
    (hnoleak : ∀ e ∈ (b0 ++ b1) ++ (.recv wire :: rest), eventKind e ≠ .leak)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms
      ((b0 ++ b1) ++ (.recv wire :: rest))) : False := by
  let blk : List MachineEvent := .recv wire :: rest
  have hhead : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; simp [blk] at he; subst he; exact Or.inl rfl
  obtain ⟨ms₁, δ, hms, hmp₁, hfor⟩ :=
    matchedPrefix6_split hmp hhead (CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp)
  have hbd₁ : AllBobDone (fun _ => False) (runTraceMoves r ms₁) := by
    rw [hb1] at hmp₁
    refine Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.allBobDone_matchedPrefix_send_tail
      htail1 (fun ms₀ hmp₀ => ?_) hmp₁
    rw [hb0] at hmp₀
    exact Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.allBobDone_matchedPrefix_ini_rs
      hrs0 (fun _ hnil =>
        Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.allBobDone_matchedPrefix_nil hnil)
      (by simpa using hmp₀)
  have hB : XplBlock6 compI0 r S g ms₁ δ (b0 ++ b1) blk := ⟨hmp₁, hms ▸ hmp.2.1, hfor⟩
  obtain ⟨pre, m, post, rfl, hpre_inv, ⟨_, _, hm⟩, _⟩ :=
    xpl6_oneMove hB hhead (by simp [blk]) hrest_ne
  let ms_pre := ms₁ ++ pre
  have hms_eq : ms = ms_pre ++ (m :: post) := by simp [hms, ms_pre, List.append_assoc]
  have htr_eq : (runMoves pre (runTraceMoves r ms₁)).1 = runTraceMoves r ms_pre :=
    (CompPrefixInvStruct.runTrace_append r ms₁ pre).symm
  have hbd_pre : AllBobDone (fun _ => False)
      (runTraceMoves r ms_pre) :=
    htr_eq ▸ Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.allBobDone_runMoves_of_movesFrom
      hpre_inv hbd₁
  rw [htr_eq] at hm
  have hnoleak_all : ∀ v ∈ runVis r ms, v.kind ≠ .leak :=
    CompSetupSecrecy.crit_noleak_of_forall2 hnoleak hmp.2.2
  have hvis_split : runVis r ms = runVis r ms_pre ++ (m.vis (runTraceMoves r ms_pre) ++
        (runMoves post (m.next (runTraceMoves r ms_pre))).2) := by
    rw [hms_eq,
      Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.runVis_append,
      runMoves_cons_snd]
  have hnoleak_m : ∀ v ∈ m.vis (runTraceMoves r ms_pre), v.kind ≠ .leak := fun v hv =>
    hnoleak_all v (by rw [hvis_split]; exact List.mem_append_right _ (List.mem_append_left _ hv))
  let tr := runTraceMoves r ms_pre
  obtain ⟨v₀, vs, hv₀, hrest_m, hvis⟩ := xpl_forall₂_cons_left hm
  obtain ⟨e_acc, he_acc, he_kind⟩ := hacc
  obtain ⟨v_acc, hv_acc_vs, hev_acc⟩ := xpl_forall₂_mem_left hrest_m e_acc he_acc
  have hv_acc : v_acc ∈ m.vis tr := by rw [hvis]; exact List.mem_cons_of_mem _ hv_acc_vs
  have hv_acc_kind : v_acc.kind = .accept := (xpl_kind_of_matches hev_acc).trans he_kind
  have hexp : exposures tr (m.next tr) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    exact hnoleak_m v (by rw [xpl_vis_eq]; exact List.mem_append_right _ hv) (xpl_exposures_kind hv)
  have hown_acc : v_acc ∈ xpl_ownVis m tr := by
    have h := hv_acc; rw [xpl_vis_eq, hexp, List.append_nil] at h; exact h
  have hown_vis : xpl_ownVis m tr = v₀ :: vs := by
    rw [← List.append_nil (xpl_ownVis m tr), ← hexp, ← xpl_vis_eq, hvis]
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hq_some
  cases m with
  | bobStart b a kh regA mh pqIdx spqrMsgIdx shown =>
    obtain ⟨w⟩ := CompSetupSecrecy.bobStart_accept_ok hv_acc hv_acc_kind
    have hpm := w.preKeyRecvMatches_of_vis hvis (hvis ▸ hnoleak_m) hv₀
    obtain ⟨p, hp, _, _, hmsg_eq, _⟩ := hpm
    rw [hq] at hp; injection hp with hp_eq; subst hp_eq
    have hdrop : q.message.drop (q.message.length - 8) = macZbk8 := by
      rw [hq, Option.map_some, Option.some.injEq] at hmac_z; exact hmac_z
    have hlen8 : (gamma compI0 S g w.msg.mac).length = 8 := by
      rw [w.hmac]; exact gamma_computeMac_length S g _ _ _ _
    have hdrop_raw := parseTrSignalMsg_gamma_drop8 (i := compI0) (S := S) (g := g) w.hparse hlen8
    rw [← hmsg_eq, hdrop, w.hmac] at hdrop_raw
    exact gamma_computeMac_ne_macZbk8 S g _ _ _ _ hdrop_raw.symm
  | decrypt me si mi pq sp wrapped =>
    let tr' := (Move.decrypt me si mi pq sp wrapped).next tr
    dsimp only [xpl_ownVis] at hown_vis
    have hvk₀ : v₀.kind = .recv := hv₀.1.symm
    have hv₀_in : v₀ ∈ decVis tr tr' si mi wrapped := by rw [hown_vis]; exact List.mem_cons_self ..
    rcases hmsg : tr.getMessageSentAt mi with _ | raw
    · simp only [decVis, hmsg, Option.map_none, Option.toList_none, List.nil_append,
        List.mem_append, List.mem_map] at hv₀_in
      rcases hv₀_in with ⟨_, _, rfl⟩ | hacc_mem
      · cases hvk₀
      · rcases hp : receivedPlaintext tr tr' with _ | m_pt <;> simp [hp] at hacc_mem
        subst hacc_mem; cases hvk₀
    · unfold decVis at hown_vis; rw [hmsg] at hown_vis
      simp only [Option.map_some, Option.toList_some, List.cons_append, List.cons.injEq] at hown_vis
      obtain ⟨rfl, _⟩ := hown_vis
      cases wrapped with
      | false =>
        obtain ⟨_, _, hw_eq⟩ := hv₀.2; change wire = _ at hw_eq
        rw [hw_eq] at hhead_ne; exact absurd rfl hhead_ne
      | true =>
        obtain ⟨_, _, _, _, ⟨ek, hek_mem, _⟩, _⟩ := hv₀.2
        exact bobDoneBaseKeys_of_allBobDone hbd_pre ek
          (mem_bobDoneBaseKeys_of_mem_sessionBaseKeys hek_mem)
  | decryptSkipped me si mi k pq sp wrapped =>
    let tr' := (Move.decryptSkipped me si mi k pq sp wrapped).next tr
    dsimp only [xpl_ownVis] at hown_vis
    have hvk₀ : v₀.kind = .recv := hv₀.1.symm
    have hv₀_in : v₀ ∈ decVis tr tr' si mi wrapped := by rw [hown_vis]; exact List.mem_cons_self ..
    rcases hmsg : tr.getMessageSentAt mi with _ | raw
    · simp only [decVis, hmsg, Option.map_none, Option.toList_none, List.nil_append,
        List.mem_append, List.mem_map] at hv₀_in
      rcases hv₀_in with ⟨_, _, rfl⟩ | hacc_mem
      · cases hvk₀
      · rcases hp : receivedPlaintext tr tr' with _ | m_pt <;> simp [hp] at hacc_mem
        subst hacc_mem; cases hvk₀
    · unfold decVis at hown_vis; rw [hmsg] at hown_vis
      simp only [Option.map_some, Option.toList_some, List.cons_append, List.cons.injEq] at hown_vis
      obtain ⟨rfl, _⟩ := hown_vis
      cases wrapped with
      | false =>
        obtain ⟨_, _, hw_eq⟩ := hv₀.2; change wire = _ at hw_eq
        rw [hw_eq] at hhead_ne; exact absurd rfl hhead_ne
      | true =>
        obtain ⟨_, _, _, _, ⟨ek, hek_mem, _⟩, _⟩ := hv₀.2
        exact bobDoneBaseKeys_of_allBobDone hbd_pre ek
          (mem_bobDoneBaseKeys_of_mem_sessionBaseKeys hek_mem)
  | aliceStart =>
    rcases xpl_aliceVis_kind (List.mem_of_mem_take hown_acc) with h | h <;> (rw [hv_acc_kind] at h; cases h)
  | reject =>
    simp only [xpl_ownVis, List.mem_cons, List.mem_map] at hown_acc
    rcases hown_acc with rfl | ⟨_, _, rfl⟩ <;> cases hv_acc_kind
  | encrypt =>
    rcases xpl_encVis_kind hown_acc with h | h | ⟨_, h⟩ <;> (rw [hv_acc_kind] at h; cases h)
  | encryptAbort =>
    rcases xpl_encVis_kind hown_acc with h | h | ⟨_, h⟩ <;> (rw [hv_acc_kind] at h; cases h)
  | encryptFail =>
    rcases xpl_encVis_kind hown_acc with h | h | ⟨_, h⟩ <;> (rw [hv_acc_kind] at h; cases h)
  | _ => simp [xpl_ownVis] at hown_acc

theorem not_matchedPrefix_zbk_tail {r : Records} {S : Sem} {g : Ghost}
    {ms : List Move} {b0 b1 rest : List MachineEvent}
    {bun pt sw : HwBytes} {rs0 : List MachineEvent} {tail1 : List MachineEvent}
    (hb0 : b0 = .recv bun :: rs0) (hrs0 : ∀ e ∈ rs0, eventKind e = .rng)
    (hb1 : b1 = .pt pt :: tail1) (htail1 : ∀ e ∈ tail1, eventKind e = .rng ∨ eventKind e = .send)
    (hrest_ne : ∀ e ∈ rest, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak)
    (hacc : ∃ e ∈ rest, eventKind e = .accept)
    (hnoleak : ∀ e ∈ (b0 ++ b1) ++ (.recv msg38_zbk :: rest), eventKind e ≠ .leak)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms
      ((b0 ++ b1) ++ (.recv msg38_zbk :: rest))) : False :=
  let _ := sw
  let ⟨hhead_ne, hq_some, hmac_z, _⟩ := msg38_zbk_props
  not_matchedPrefix_zbk_tail_gen hb0 hrs0 hb1 htail1 hhead_ne hq_some hmac_z hrest_ne hacc hnoleak hmp

end Symbolic.BugInjection.Proofs.SyntheticZeroBaseKeyPqxdh.Defs

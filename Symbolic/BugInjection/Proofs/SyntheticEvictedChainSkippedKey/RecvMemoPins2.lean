/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins1

/-!
# Single-Step `RunMatches` Peeling for Encrypt and Decrypt Calls

Peels `RunMatches` on clean `messageEncrypt` (`preKeySend` and `whisper`), `bobStart`, and
`messageDecrypt` steps to pin `g.σ`, `g.addr`, sent message bytes, and `vis` send and plaintext
entries.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins2

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open DY (Bytes Participant ExecTrace)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent)
open DY.Libsignal.TripleRatchet (TRState parseTrSignalMsg)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry Step BundlePreKeyIds
   pendingPreKey encDraws encSendEntry bobVis decVis stepView rngEntry
   eventIdx receivedPlaintext ecKey pubBytes secretBytes randTerm
   bundlePreKeyIds runWrapped inputKind preKeyWire plaintextTerms
   GhostWF BytesMatchEntry OutputsMatch SendMatches RunMatches gamma)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (kh1 o1)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (w0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse (ev)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData (dagBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace0 (encTrGen decTr0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace
  (pqKeyOf sendMsgOf trClean2 trClean3 step3_bobStart_next)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins0
  (preKeyWire_msg_inj gamma_randTerm_ne_zero drawsMatch_singleton_single)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins1
  (SetupAndCall0Pinned newRandoms_encTrGen newRandoms_trClean3 newRandoms_decTr0
   lastSent_encTrGen exposures_encTrGen exposures_trClean3 exposures_decTr0
   aliceDonePairs pendingPreKey_mem_aliceDonePairs)

private theorem split_append_singleton {α : Type} {drs rngs : List α} {v_out v_send : α}
    (heq : drs ++ [v_out] = rngs ++ [v_send]) :
    drs = rngs ∧ v_out = v_send := by
  have hlen : drs.length = rngs.length := by
    have hl := congrArg List.length heq
    simp only [List.length_append, List.length_singleton] at hl
    omega
  obtain ⟨hd, hv⟩ := List.append_inj heq hlen
  exact ⟨hd, List.singleton_inj.mp hv⟩

/-- Peels `RunMatches` for a pre-key-wrapped `messageEncrypt` step: pins plaintext coins, optional
SPQR coins, inner `TRSignalMsg` bytes via `preKeyWire` injectivity, and Alice/Bob address bytes. -/
theorem peel_encrypt_preKey {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {me : Participant} {stateIdx cl pqIdx : Nat} {st : TRState}
    {e : RunEvent} {v visAll : List VisEntry} {out₀ msg₀ : HwBytes}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hpinned : SetupAndCall0Pinned S g)
    (hgwf : GhostWF g visAll)
    (hv : ∀ w ∈ v, w ∈ visAll)
    (hnext : (Step.messageEncrypt me stateIdx cl pqIdx).next tr =
      encTrGen tr me stateIdx st cl (pqKeyOf st cl tr.length))
    (halice : aliceDonePairs tr = [(o1.ek, o1.ct)])
    (hcmd : ∃ p, e.cmd = .send p)
    (hexit : e.exit = some (0, out₀))
    (hwrap : runWrapped e = true)
    (hout_wire :
      let (pkId, spkId, kpkId) := bundlePreKeyIds (ev 0).input
      out₀ = preKeyWire pkId spkId kpkId w0.regIdA
        (ecKey (pubBytes evictedI0 w0.aliceId)) (dagBytes 68) (dagBytes 73) msg₀ ∧
      out₀.length < 2048)
    (hrm : RunMatches evictedI0 r S g tr (Step.messageEncrypt me stateIdx cl pqIdx) e v
      (some (bundlePreKeyIds (ev 0).input))) :
    let msg := sendMsgOf st cl tr.length
    g.σ tr.length 32 = e.input ∧
    (cl ≠ 0 → g.σ (tr.length + 1) cl = e.coins.take cl) ∧
    gamma evictedI0 S g msg = msg₀ ∧
    (∀ pm, parseTrSignalMsg msg = some pm →
      g.addr pm.wire =
        DY.Libsignal.Composed.Refinement.Cli.serializeAddresses
          ⟨DY.Libsignal.Composed.Refinement.Cli.aliceUuid, 1⟩
          ⟨DY.Libsignal.Composed.Refinement.Cli.bobUuid, 1⟩) ∧
    (v.filter (·.kind == .send)).flatMap (·.terms) = [o1.ek, o1.ct, msg] ∧
    plaintextTerms v = [randTerm tr.length 32] := by
  obtain ⟨_, _, _, _, hok, _, hv_eq, inp, drs, outs, hv_split, hinp, hdrs, houts, _, _⟩ := hrm
  obtain ⟨p_cmd, hp_cmd⟩ := hcmd
  unfold OutputsMatch at houts
  rw [hexit, hp_cmd] at houts
  obtain ⟨v_out, rfl, hb_out⟩ := houts
  unfold stepView at hv_eq
  simp only [hok, ↓reduceIte] at hv_eq
  rw [hnext, exposures_encTrGen, List.append_nil,
      newRandoms_encTrGen, hwrap] at hv_eq
  dsimp only [encDraws, List.filter, List.map] at hv_eq
  unfold encSendEntry at hv_eq
  rw [lastSent_encTrGen] at hv_eq
  let rngs : List VisEntry :=
    List.map (fun r => rngEntry r.1)
      (match cl != 0 with | true => [(randTerm (tr.length + 1) cl, cl)] | false => [])
  have hrngs_kind : ∀ w ∈ rngs, w.kind = .rng := by
    intro w hw; dsimp only [rngs] at hw
    rcases h : (cl != 0) with _ | _ <;>
      simp only [h, List.map_nil, List.not_mem_nil, List.map_cons, List.mem_singleton] at hw
    rw [hw]; rfl
  cases hppk : pendingPreKey tr stateIdx with
  | none =>
    rw [hppk] at hv_eq
    dsimp only [List.append] at hv_eq
    simp only [List.append_nil] at hv_eq
    have htail : drs ++ [v_out] = rngs := (List.cons.inj (hv_split.symm.trans hv_eq)).2
    have hmem : v_out ∈ rngs := by
      rw [← htail]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hk1 := hrngs_kind v_out hmem
    have hk2 := hb_out.1.symm
    rw [hk1] at hk2; cases hk2
  | some pair =>
    rcases pair with ⟨ek, ct⟩
    have hmem_ad := pendingPreKey_mem_aliceDonePairs hppk
    rw [halice, List.mem_singleton, Prod.mk.injEq] at hmem_ad
    obtain ⟨rfl, rfl⟩ := hmem_ad
    rw [hppk] at hv_eq
    dsimp only [List.append] at hv_eq
    change v = ⟨.pt, [randTerm tr.length 32], .single, none⟩ ::
      (rngs ++ [⟨.send, [o1.ek, o1.ct, sendMsgOf st cl tr.length], .preKeySend, none⟩]) at hv_eq
    obtain ⟨hinp_eq, htail_eq⟩ := List.cons.inj (hv_split.symm.trans hv_eq)
    obtain ⟨hdrs_eq, hvout_eq⟩ := split_append_singleton htail_eq
    have hpt_pin : g.σ tr.length 32 = e.input := by
      unfold BytesMatchEntry inputKind at hinp
      rw [hp_cmd, hinp_eq] at hinp
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hinp
      rw [← hinp.2, ← gamma_randTerm_ne_zero S g (by decide)]
    have hcl_pin : cl ≠ 0 → g.σ (tr.length + 1) cl = e.coins.take cl := by
      intro hcl
      have hcl_b : (cl != 0) = true := bne_iff_ne.mpr hcl
      have hdrs_single : drs = [rngEntry (randTerm (tr.length + 1) cl)] := by
        rw [hdrs_eq]; dsimp only [rngs]; rw [hcl_b]; rfl
      rw [hdrs_single] at hdrs
      have hmem_rng : rngEntry (randTerm (tr.length + 1) cl) ∈ visAll := by
        apply hv; rw [hv_split, hdrs_single]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self)
      exact drawsMatch_singleton_single hcl hgwf hmem_rng rfl rfl rfl hdrs
    have hmsg_pin : gamma evictedI0 S g (sendMsgOf st cl tr.length) = msg₀ := by
      unfold BytesMatchEntry at hb_out
      rw [hvout_eq] at hb_out
      dsimp only [SendMatches] at hb_out
      obtain ⟨_, ⟨pkId, spkId, kpkId, hids, hwire⟩⟩ := hb_out
      injection hids with hids_eq
      have hreg : r.regIdA = w0.regIdA := hfit.1.1.2.2.1
      have hs0 : secretBytes r 0 = w0.aliceId := hfit.1.1.2.2.2.2.2.2.1
      rw [hreg, show r.ikASecBytes = secretBytes r 0 from rfl, hs0, hpinned.ek0, hpinned.ct0] at hwire
      have hout_w := hout_wire
      rw [hids_eq] at hout_w
      dsimp only at hout_w
      exact preKeyWire_msg_inj (hout_w.1 ▸ hout_w.2) (hwire.symm.trans hout_w.1)
    have haddr_pin : ∀ pm, parseTrSignalMsg (sendMsgOf st cl tr.length) = some pm →
        g.addr pm.wire =
          DY.Libsignal.Composed.Refinement.Cli.serializeAddresses
            ⟨DY.Libsignal.Composed.Refinement.Cli.aliceUuid, 1⟩
            ⟨DY.Libsignal.Composed.Refinement.Cli.bobUuid, 1⟩ := by
      intro pm hpm
      have hv_mem : v_out ∈ visAll := by
        apply hv; rw [hv_split]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      rw [hvout_eq] at hv_mem
      exact (hgwf.2.2 _ hv_mem rfl).1 rfl o1.ek o1.ct _ pm rfl hpm
    have hsend_v : (v.filter (·.kind == .send)).flatMap (·.terms) =
        [o1.ek, o1.ct, sendMsgOf st cl tr.length] := by
      rw [hv_eq]
      have hrng_f : rngs.filter (·.kind == .send) = [] := by
        rw [List.filter_eq_nil_iff]
        intro w hw; rw [hrngs_kind w hw]; decide
      simp only [List.filter_cons, List.filter_append, hrng_f]
      rfl
    have hpt_v : plaintextTerms v = [randTerm tr.length 32] := by
      unfold plaintextTerms; rw [hv_eq]
      have hrng_f : rngs.filter (·.kind == .pt) = [] := by
        rw [List.filter_eq_nil_iff]
        intro w hw; rw [hrngs_kind w hw]; decide
      simp only [List.filter_cons, List.filter_append, hrng_f]
      rfl
    exact ⟨hpt_pin, hcl_pin, hmsg_pin, haddr_pin, hsend_v, hpt_v⟩

/-- Peels `RunMatches` for an unwrapped whisper `messageEncrypt` step: pins plaintext coins,
optional SPQR coins, `TRSignalMsg` bytes from `out₀.tail`, and empty `g.addr`. -/
theorem peel_encrypt_whisper {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {me : Participant} {stateIdx cl pqIdx : Nat} {st : TRState}
    {e : RunEvent} {v visAll : List VisEntry} {initIds : Option BundlePreKeyIds} {out₀ : HwBytes}
    (hgwf : GhostWF g visAll)
    (hv : ∀ w ∈ v, w ∈ visAll)
    (hnext : (Step.messageEncrypt me stateIdx cl pqIdx).next tr =
      encTrGen tr me stateIdx st cl (pqKeyOf st cl tr.length))
    (hcmd : ∃ p, e.cmd = .send p)
    (hexit : e.exit = some (0, out₀))
    (hwrap : runWrapped e = false)
    (hrm : RunMatches evictedI0 r S g tr (Step.messageEncrypt me stateIdx cl pqIdx) e v initIds) :
    let msg := sendMsgOf st cl tr.length
    g.σ tr.length 32 = e.input ∧
    (cl ≠ 0 → g.σ (tr.length + 1) cl = e.coins.take cl) ∧
    gamma evictedI0 S g msg = out₀.tail ∧
    (∀ pm, parseTrSignalMsg msg = some pm → g.addr pm.wire = []) ∧
    (v.filter (·.kind == .send)).flatMap (·.terms) = [msg] ∧
    plaintextTerms v = [randTerm tr.length 32] := by
  obtain ⟨_, _, _, _, hok, _, hv_eq, inp, drs, outs, hv_split, hinp, hdrs, houts, _, _⟩ := hrm
  obtain ⟨p_cmd, hp_cmd⟩ := hcmd
  unfold OutputsMatch at houts
  rw [hexit, hp_cmd] at houts
  obtain ⟨v_out, rfl, hb_out⟩ := houts
  unfold stepView at hv_eq
  simp only [hok, ↓reduceIte] at hv_eq
  rw [hnext, exposures_encTrGen, List.append_nil,
      newRandoms_encTrGen, hwrap] at hv_eq
  dsimp only [encDraws, List.filter, List.map] at hv_eq
  unfold encSendEntry at hv_eq
  rw [lastSent_encTrGen] at hv_eq
  let rngs : List VisEntry :=
    List.map (fun r => rngEntry r.1)
      (match cl != 0 with | true => [(randTerm (tr.length + 1) cl, cl)] | false => [])
  have hrngs_kind : ∀ w ∈ rngs, w.kind = .rng := by
    intro w hw; dsimp only [rngs] at hw
    rcases h : (cl != 0) with _ | _ <;>
      simp only [h, List.map_nil, List.not_mem_nil, List.map_cons, List.mem_singleton] at hw
    rw [hw]; rfl
  cases hppk : pendingPreKey tr stateIdx with
  | some pair =>
    rw [hppk] at hv_eq
    dsimp only [List.append] at hv_eq
    simp only [List.append_nil] at hv_eq
    have htail : drs ++ [v_out] = rngs := (List.cons.inj (hv_split.symm.trans hv_eq)).2
    have hmem : v_out ∈ rngs := by
      rw [← htail]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hk1 := hrngs_kind v_out hmem
    have hk2 := hb_out.1.symm
    rw [hk1] at hk2; cases hk2
  | none =>
    rw [hppk] at hv_eq
    dsimp only [List.append] at hv_eq
    change v = ⟨.pt, [randTerm tr.length 32], .single, none⟩ ::
      (rngs ++ [⟨.send, [sendMsgOf st cl tr.length], .whisper, none⟩]) at hv_eq
    obtain ⟨hinp_eq, htail_eq⟩ := List.cons.inj (hv_split.symm.trans hv_eq)
    obtain ⟨hdrs_eq, hvout_eq⟩ := split_append_singleton htail_eq
    have hpt_pin : g.σ tr.length 32 = e.input := by
      unfold BytesMatchEntry inputKind at hinp
      rw [hp_cmd, hinp_eq] at hinp
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hinp
      rw [← hinp.2, ← gamma_randTerm_ne_zero S g (by decide)]
    have hcl_pin : cl ≠ 0 → g.σ (tr.length + 1) cl = e.coins.take cl := by
      intro hcl
      have hcl_b : (cl != 0) = true := bne_iff_ne.mpr hcl
      have hdrs_single : drs = [rngEntry (randTerm (tr.length + 1) cl)] := by
        rw [hdrs_eq]; dsimp only [rngs]; rw [hcl_b]; rfl
      rw [hdrs_single] at hdrs
      have hmem_rng : rngEntry (randTerm (tr.length + 1) cl) ∈ visAll := by
        apply hv; rw [hv_split, hdrs_single]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self)
      exact drawsMatch_singleton_single hcl hgwf hmem_rng rfl rfl rfl hdrs
    have hmsg_pin : gamma evictedI0 S g (sendMsgOf st cl tr.length) = out₀.tail := by
      unfold BytesMatchEntry at hb_out
      rw [hvout_eq] at hb_out
      obtain ⟨_, t, ht_eq, hw_eq⟩ := hb_out
      rw [← List.singleton_inj.mp ht_eq] at hw_eq
      rw [hw_eq]; rfl
    have haddr_pin : ∀ pm, parseTrSignalMsg (sendMsgOf st cl tr.length) = some pm →
        g.addr pm.wire = [] := by
      intro pm hpm
      have hv_mem : v_out ∈ visAll := by
        apply hv; rw [hv_split]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      rw [hvout_eq] at hv_mem
      exact (hgwf.2.2 _ hv_mem rfl).2 rfl _ pm rfl hpm
    have hsend_v : (v.filter (·.kind == .send)).flatMap (·.terms) =
        [sendMsgOf st cl tr.length] := by
      rw [hv_eq]
      have hrng_f : rngs.filter (·.kind == .send) = [] := by
        rw [List.filter_eq_nil_iff]
        intro w hw; rw [hrngs_kind w hw]; decide
      simp only [List.filter_cons, List.filter_append, hrng_f]
      rfl
    have hpt_v : plaintextTerms v = [randTerm tr.length 32] := by
      unfold plaintextTerms; rw [hv_eq]
      have hrng_f : rngs.filter (·.kind == .pt) = [] := by
        rw [List.filter_eq_nil_iff]
        intro w hw; rw [hrngs_kind w hw]; decide
      simp only [List.filter_cons, List.filter_append, hrng_f]
      rfl
    exact ⟨hpt_pin, hcl_pin, hmsg_pin, haddr_pin, hsend_v, hpt_v⟩

/-- Peels `RunMatches` at Call 3 (`bobStart`): pins `g.σ 45 32` and shows that `v` contains no
`.send` or `.pt` entries. -/
theorem peel_bobStart {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {cls : Nat → Nat} {idx : UInt32} {v visAll : List VisEntry} {initIds : Option BundlePreKeyIds}
    (hgwf : GhostWF g visAll)
    (hv : ∀ w ∈ v, w ∈ visAll)
    (hrm : RunMatches evictedI0 r S g (trClean2 cls)
      (Step.bobStart "bob" "alice" kh1 1 ⟨25, 26, 44⟩ 40 idx) (ev 3) v initIds) :
    g.σ 45 32 = ((ev 3).coins).take 32 ∧
    (v.filter (·.kind == .send)).flatMap (·.terms) = [] ∧
    plaintextTerms v = [] := by
  obtain ⟨_, _, _, _, hok, ⟨out3, hexit3⟩, hv_eq, inp, drs, outs, hv_split, _, hdrs, houts, _, _⟩ := hrm
  have ⟨p_cmd3, hcmd3⟩ : ∃ p_cmd3, (ev 3).cmd = .recv p_cmd3 := ⟨_, rfl⟩
  unfold OutputsMatch at houts
  rw [hexit3, hcmd3] at houts
  obtain ⟨v_out, rfl, hb_out⟩ := houts
  unfold stepView at hv_eq
  simp only [hok, ↓reduceIte] at hv_eq
  rw [step3_bobStart_next cls idx, exposures_trClean3, List.append_nil] at hv_eq
  unfold bobVis at hv_eq
  rw [newRandoms_trClean3] at hv_eq
  dsimp only [List.append] at hv_eq
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil] at hv_eq
  have htail := (List.cons.inj (hv_split.symm.trans hv_eq)).2
  cases hacc : receivedPlaintext (trClean2 cls) (trClean3 cls idx) with
  | none =>
    rw [hacc] at htail
    dsimp only [Option.map, Option.toList, List.append] at htail
    have hk : v_out.kind = .rng := by
      have hv_in : v_out ∈ [rngEntry (randTerm 45 32)] := by
        rw [← htail]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      rw [List.mem_singleton.mp hv_in]; rfl
    have hk2 := hb_out.1.symm
    rw [hk] at hk2; cases hk2
  | some m_pt =>
    rw [hacc] at htail
    dsimp only [Option.map, Option.toList, List.append] at htail
    change drs ++ [v_out] = [rngEntry (randTerm 45 32)] ++ [_] at htail
    obtain ⟨hdrs_eq, _⟩ := split_append_singleton htail
    rw [hdrs_eq] at hdrs
    have hmem_rng : rngEntry (randTerm 45 32) ∈ visAll := by
      apply hv; rw [hv_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have h45 := drawsMatch_singleton_single (by decide) hgwf hmem_rng rfl rfl rfl hdrs
    have hsend_v : (v.filter (·.kind == .send)).flatMap (·.terms) = [] := by
      rw [hv_eq, hacc]; rfl
    have hpt_v : plaintextTerms v = [] := by
      unfold plaintextTerms; rw [hv_eq, hacc]; rfl
    exact ⟨h45, hsend_v, hpt_v⟩

/-- Peels `RunMatches` at a clean `messageDecrypt` step: pins `g.σ tr.length 32` and shows that `v`
contains no `.send` or `.pt` entries. -/
theorem peel_decrypt {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {me : Participant} {stateIdx msgIdx pqIdx : Nat} {idx : UInt32}
    {st : TRState} {peerDhs pq pqm m : Bytes}
    {e : RunEvent} {v visAll : List VisEntry} {initIds : Option BundlePreKeyIds}
    (hgwf : GhostWF g visAll)
    (hv : ∀ w ∈ v, w ∈ visAll)
    (hnext : (Step.messageDecrypt me stateIdx msgIdx pqIdx idx).next tr =
      decTr0 tr me stateIdx st peerDhs pq pqm m)
    (hmsg_at : ∃ b, tr.getMessageSentAt msgIdx = some b)
    (hcmd : ∃ p, e.cmd = .recv p)
    (hrm : RunMatches evictedI0 r S g tr
      (Step.messageDecrypt me stateIdx msgIdx pqIdx idx) e v initIds) :
    g.σ tr.length 32 = e.coins.take 32 ∧
    (v.filter (·.kind == .send)).flatMap (·.terms) = [] ∧
    plaintextTerms v = [] := by
  obtain ⟨_, _, _, _, hok, ⟨out_d, hexit_d⟩, hv_eq, inp, drs, outs, hv_split, _, hdrs, houts, _, _⟩ := hrm
  obtain ⟨p_cmd, hp_cmd⟩ := hcmd
  obtain ⟨b_msg, hb_msg⟩ := hmsg_at
  unfold OutputsMatch at houts
  rw [hexit_d, hp_cmd] at houts
  obtain ⟨v_out, rfl, hb_out⟩ := houts
  unfold stepView at hv_eq
  simp only [hok, ↓reduceIte] at hv_eq
  rw [hnext, exposures_decTr0, List.append_nil] at hv_eq
  unfold decVis at hv_eq
  rw [hb_msg, newRandoms_decTr0] at hv_eq
  dsimp only [Option.map, Option.toList, List.append] at hv_eq
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil] at hv_eq
  have htail := (List.cons.inj (hv_split.symm.trans hv_eq)).2
  cases hacc : receivedPlaintext tr (decTr0 tr me stateIdx st peerDhs pq pqm m) with
  | none =>
    rw [hacc] at htail
    dsimp only [Option.map, Option.toList, List.append] at htail
    have hk : v_out.kind = .rng := by
      have hv_in : v_out ∈ [rngEntry (randTerm tr.length 32)] := by
        rw [← htail]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      rw [List.mem_singleton.mp hv_in]; rfl
    have hk2 := hb_out.1.symm
    rw [hk] at hk2; cases hk2
  | some m_pt =>
    rw [hacc] at htail
    dsimp only [Option.map, Option.toList, List.append] at htail
    change drs ++ [v_out] = [rngEntry (randTerm tr.length 32)] ++ [_] at htail
    obtain ⟨hdrs_eq, _⟩ := split_append_singleton htail
    rw [hdrs_eq] at hdrs
    have hmem_rng : rngEntry (randTerm tr.length 32) ∈ visAll := by
      apply hv; rw [hv_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have hpin := drawsMatch_singleton_single (by decide) hgwf hmem_rng rfl rfl rfl hdrs
    have hsend_v : (v.filter (·.kind == .send)).flatMap (·.terms) = [] := by
      rw [hv_eq, hacc]; rfl
    have hpt_v : plaintextTerms v = [] := by
      unfold plaintextTerms; rw [hv_eq, hacc]; rfl
    exact ⟨hpin, hsend_v, hpt_v⟩

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPins2

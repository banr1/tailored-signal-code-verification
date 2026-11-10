/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
public import Symbolic.Proofs.Swarm.CREF.SendWire.Ghosts
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaHead
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
import VCVio.Prelude.Core

/-!
# Ghost Stamp and Prefix Invariance for `SendWire`

Proves that `setSendAddr g ts addr` (along with its specializations `clearSendAddr`, `sendGhost`,
and `sendPendingGhost`) leaves `gamma` unchanged on every term stamped below `ts`, preserving
`GhostAndSemMatchSetup`, `PathFaithful`, `ReadFaithful`, `EventMatchesEntry`, `MatchedPrefix`, and
`TRRecordStateInv`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.SendWire

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.CREF.TR.FreshSigma

section SetSendAddrPP2

unseal DY.Bytes

private theorem isFreshSendWire_eq_false_of_stampsLt
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat)
    (x : DY.TrWire.TrWireMsg.SubF DY.Bytes)
    (h : MemoStampsLt ts (concretizeTrWire g x (fun y _ => DY.Bytes.rec (concretizeAll i S g) y))) :
    isFreshSendWire ts x.pack = false := by
  cases htrue' : isFreshSendWire ts x.pack with
  | false => rfl
  | true =>
    unfold isFreshSendWire at htrue'
    rw [BytesView.view_pack] at htrue'
    dsimp only at htrue'
    split at htrue'
    · next e he =>
      split at htrue'
      · next r hr =>
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at htrue'
        obtain ⟨hts_eq, hsz_eq⟩ := htrue'
        rcases x with ⟨v, rk, c, pc, ct, pq, ev⟩
        dsimp only [concretizeTrWire] at he h
        have hct : MemoStampsLt ts (DY.Bytes.rec (concretizeAll i S g) ct) :=
          memoStampsLt_of_mem h (by simp)
        have hpv_e := DY.Bytes.pack_view? DY.SymEnc.Enc.SubF ct
        rw [he] at hpv_e
        rw [← hpv_e, DY.Bytes.rec_eq (concretizeSym i) (concretizeAll i S g)] at hct
        rcases e with ⟨k, iv, msg⟩
        dsimp only [concretizeSym] at hr hct
        have hmsg : MemoStampsLt ts (DY.Bytes.rec (concretizeAll i S g) msg) :=
          memoStampsLt_of_mem hct (by simp)
        have hpv_r := DY.Bytes.pack_view? DY.Random.Random msg
        rw [hr] at hpv_r
        rw [← hpv_r, DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g)] at hmsg
        dsimp only [concretizeRandom] at hmsg
        have hsz0 : r.size ≠ 0 := by omega
        simp only [hsz0, ↓reduceIte] at hmsg
        have hlt : r.timestamp < ts :=
          hmsg r.pack r.pack (g.σ r.timestamp r.size) r (List.mem_cons_self ..) (BytesView.view_pack r)
        omega
      · cases htrue'
    · cases htrue'

private theorem gTrWire0_setSendAddr_pp2
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr : HwBytes)
    (rec2 : DY.Bytes → ConcretizedTerm) :
    DY.Bytes.PartialProof2 (concretizeTrWire g) (concretizeTrWire (setSendAddr g ts addr))
      (DY.Bytes.rec (concretizeAll i S g)) rec2 (MemoRel ts) := by
  intro x ih h
  have hfalse : isFreshSendWire ts x.pack = false :=
    isFreshSendWire_eq_false_of_stampsLt i S g ts x h
  rcases x with ⟨v, rk, c, pc, ct, pq, ev⟩
  dsimp only [concretizeTrWire, MemoRel, setSendAddr] at h hfalse ⊢
  have hrk : rec2 rk = DY.Bytes.rec (concretizeAll i S g) rk :=
    ih rk (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  have hct : rec2 ct = DY.Bytes.rec (concretizeAll i S g) ct :=
    ih ct (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  have hpq : rec2 pq = DY.Bytes.rec (concretizeAll i S g) pq :=
    ih pq (by simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf]) (memoStampsLt_of_mem h (by simp))
  rw [hrk, hct, hpq]
  simp only [hfalse, Bool.false_eq_true, ↓reduceIte]

private theorem allFuns_setSendAddr_pp2
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr : HwBytes)
    (rec2 : DY.Bytes → ConcretizedTerm) (id : Fin 12) :
    DY.Bytes.PartialProof2 (allFuns i S g id) (allFuns i S (setSendAddr g ts addr) id)
      (DY.Bytes.rec (concretizeAll i S g)) rec2 (MemoRel ts) := by
  let rec1 := DY.Bytes.rec (concretizeAll i S g)
  match id with
  | ⟨0, _⟩ =>
    dsimp only [allFuns, DY.Libsignal.Composed.SubF.internal]
    intro _ _ _; rfl
  | ⟨1, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩ _ _ _; rfl
  | ⟨2, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gConcat0_pp2 ts rec1 rec2
  | ⟨3, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with | ⟨0, _⟩ => exact gDhPk_pp2 i ts rec1 rec2 | ⟨1, _⟩ => exact gDh_pp2 i ts rec1 rec2
  | ⟨4, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gKdf0_pp2 i ts rec1 rec2
  | ⟨5, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gSym0_pp2 i ts rec1 rec2
  | ⟨6, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gTrunc0_pp2 ts rec1 rec2
  | ⟨7, _⟩ => dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩; exact gVariant0_pp2 ts rec1 rec2
  | ⟨8, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact gKemPk_pp2 S ts rec1 rec2
    | ⟨1, _⟩ => exact gKemEncap_pp2 i ts rec1 rec2
    | ⟨2, _⟩ => exact gKemSS_pp2 i S ts rec1 rec2
    | ⟨3, _⟩ => exact gKemRej_pp2 S ts rec1 rec2
  | ⟨9, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with | ⟨0, _⟩ => exact gVk_pp2 S ts rec1 rec2 | ⟨1, _⟩ => exact gSign_pp2 S ts rec1 rec2
  | ⟨10, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact gSpqrInit_pp2 S ts rec1 rec2
    | ⟨1, _⟩ => exact gSpqrSendState_pp2 S ts rec1 rec2
    | ⟨2, _⟩ => exact gSpqrSendKey_pp2 S ts rec1 rec2
    | ⟨3, _⟩ => exact gSpqrSendMsg_pp2 S ts rec1 rec2
    | ⟨4, _⟩ => exact gSpqrRecvState_pp2 S ts rec1 rec2
    | ⟨5, _⟩ => exact gSpqrRecvKey_pp2 S ts rec1 rec2
    | ⟨6, _⟩ => exact gSpqrChainKey_pp2 S ts rec1 rec2
  | ⟨11, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof2.combine; intro ⟨0, _⟩
    exact gTrWire0_setSendAddr_pp2 i S g ts addr rec2

theorem gamma'_setSendAddr_of_stampsLt
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr : HwBytes)
    (b : DY.Bytes) :
    StampsLt i S g ts b →
      gamma' i S (setSendAddr g ts addr) b = gamma' i S g b := by
  have hpf : DY.Bytes.Proof2 (concretizeAll i S g) (concretizeAll i S (setSendAddr g ts addr)) (MemoRel ts) :=
    DY.Bytes.PartialProof2.combine (allFuns_setSendAddr_pp2 i S g ts addr _)
  exact hpf.prove b

end SetSendAddrPP2

theorem gamma_setSendAddr_of_stampsLt
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr : HwBytes)
    (b : DY.Bytes) (h : StampsLt i S g ts b) :
    gamma i S (setSendAddr g ts addr) b = gamma i S g b :=
  congrArg ConcretizedTerm.bytes (gamma'_setSendAddr_of_stampsLt i S g ts addr b h)

private theorem bundleMatches_setSendAddr_of_visStampsLt
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr b : HwBytes)
    (terms : List DY.Bytes) (hv : ∀ t ∈ terms, StampsLt i S g ts t) :
    PreKeyBundleLayoutMatches i S (setSendAddr g ts addr) b terms ↔ PreKeyBundleLayoutMatches i S g b terms := by
  match terms with
  | [spk, spkSig, pqpk, pqpkSig] =>
    simp only [PreKeyBundleLayoutMatches, BundleSignedKeysMatch,
      gamma_setSendAddr_of_stampsLt i S g ts addr spk (hv spk (by simp)),
      gamma_setSendAddr_of_stampsLt i S g ts addr spkSig (hv spkSig (by simp)),
      gamma_setSendAddr_of_stampsLt i S g ts addr pqpk (hv pqpk (by simp)),
      gamma_setSendAddr_of_stampsLt i S g ts addr pqpkSig (hv pqpkSig (by simp))]
  | [spk, spkSig, pqpk, pqpkSig, opk] =>
    simp only [PreKeyBundleLayoutMatches, BundleSignedKeysMatch,
      gamma_setSendAddr_of_stampsLt i S g ts addr spk (hv spk (by simp)),
      gamma_setSendAddr_of_stampsLt i S g ts addr spkSig (hv spkSig (by simp)),
      gamma_setSendAddr_of_stampsLt i S g ts addr pqpk (hv pqpk (by simp)),
      gamma_setSendAddr_of_stampsLt i S g ts addr pqpkSig (hv pqpkSig (by simp)),
      gamma_setSendAddr_of_stampsLt i S g ts addr opk (hv opk (by simp))]
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

private theorem sendMatches_setSendAddr_of_visStampsLt
    (i : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (initIds : Option BundlePreKeyIds) (ts : Nat) (addr b : HwBytes)
    (terms : List DY.Bytes) (hv : ∀ t ∈ terms, StampsLt i S g ts t) :
    SendMatches i r S (setSendAddr g ts addr) initIds b terms ↔ SendMatches i r S g initIds b terms := by
  match terms with
  | [ek, ct, msg] =>
    simp only [SendMatches,
      gamma_setSendAddr_of_stampsLt i S g ts addr ek (hv ek (by simp)),
      gamma_setSendAddr_of_stampsLt i S g ts addr ct (hv ct (by simp)),
      gamma_setSendAddr_of_stampsLt i S g ts addr msg (hv msg (by simp))]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => rfl

private theorem preKeyRecvMatches_setSendAddr_of_visStampsLt
    (i : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr b : HwBytes)
    (terms : List DY.Bytes) (hv : ∀ t ∈ terms, StampsLt i S g ts t) :
    PreKeyRecvMatches i r S (setSendAddr g ts addr) b terms ↔ PreKeyRecvMatches i r S g b terms := by
  match terms with
  | [ek, ct, msg] =>
    simp only [PreKeyRecvMatches,
      gamma_setSendAddr_of_stampsLt i S g ts addr ek (hv ek (by simp)),
      gamma_setSendAddr_of_stampsLt i S g ts addr ct (hv ct (by simp)),
      gamma_setSendAddr_of_stampsLt i S g ts addr msg (hv msg (by simp))]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => rfl

private theorem preKeyRecvOpkMatches_setSendAddr_of_visStampsLt
    (i : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr b : HwBytes)
    (terms : List DY.Bytes) (hv : ∀ t ∈ terms, StampsLt i S g ts t) :
    PreKeyRecvOpkMatches i r S (setSendAddr g ts addr) b terms ↔ PreKeyRecvOpkMatches i r S g b terms := by
  match terms with
  | [ek, ct, msg] =>
    exact and_congr_left fun _ =>
      preKeyRecvMatches_setSendAddr_of_visStampsLt i r S g ts addr b [ek, ct, msg] hv
  | [ek, ct, msg, _opk] =>
    exact and_congr_left fun _ =>
      preKeyRecvMatches_setSendAddr_of_visStampsLt i r S g ts addr b [ek, ct, msg]
        (fun t ht => hv t (by simp at ht; rcases ht with rfl | rfl | rfl <;> simp))
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem eventMatchesEntry_setSendAddr_of_visStampsLt
    (i : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ts : Nat) (addr : HwBytes)
    (e : MachineEvent) (v : VisEntry) (hv : VisStampsLt i S g ts v) :
    EventMatchesEntry i r S (setSendAddr g ts addr) e v ↔ EventMatchesEntry i r S g e v := by
  have hmap : v.terms.map (gamma i S (setSendAddr g ts addr)) = v.terms.map (gamma i S g) :=
    List.map_congr_left fun t ht => gamma_setSendAddr_of_stampsLt i S g ts addr t (hv.1 t ht)
  have hkeys := hv.2
  have hv := hv.1
  unfold EventMatchesEntry; apply and_congr_right; intro _; dsimp only
  cases hl : v.layout with
  | single => rw [hmap]
  | whisper =>
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [gamma_setSendAddr_of_stampsLt i S g ts addr t (hv t (by simp [ht]))]
  | bundle => exact bundleMatches_setSendAddr_of_visStampsLt i S g ts addr (eventBytes e) v.terms hv
  | preKeySend =>
    exact exists_congr fun ids =>
      sendMatches_setSendAddr_of_visStampsLt i r S g (some ids) ts addr (eventBytes e) v.terms hv
  | preKeyRecv => exact preKeyRecvOpkMatches_setSendAddr_of_visStampsLt i r S g ts addr (eventBytes e) v.terms hv
  | preKeyInner eks =>
    rw [hl] at hkeys
    refine exists_congr fun t => exists_congr fun p => and_congr_right fun ht => and_congr_right fun _ => ?_
    rw [gamma_setSendAddr_of_stampsLt i S g ts addr t (hv t (by simp [ht]))]
    refine and_congr_left fun _ => exists_congr fun ek => and_congr_right fun hek => ?_
    rw [gamma_setSendAddr_of_stampsLt i S g ts addr ek (hkeys ek hek)]
  | fresh _ => rfl
  | kyberCoin j =>
    apply and_congr_right; intro _
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [gamma_setSendAddr_of_stampsLt i S g ts addr t (hv t (by simp [ht]))]
  | unconstrained => rfl
  | leakPq pq => cases pq <;> simp [hmap]
  | leakRecord =>
    refine exists_congr fun t => and_congr_right fun ht => ?_
    rw [gamma_setSendAddr_of_stampsLt i S g ts addr t (hv t (by simp [ht]))]

private theorem runMoves_append_fst_loc :
    ∀ (L₁ L₂ : List Move) (tr : ExecTrace),
      (runMoves (L₁ ++ L₂) tr).1 = (runMoves L₂ (runMoves L₁ tr).1).1
  | [], _, _ => rfl
  | m :: L₁, L₂, tr => by
    simp only [List.cons_append, runMoves]
    exact runMoves_append_fst_loc L₁ L₂ (m.next tr)

private theorem runTrace_take_le_loc (r₀ : ProtocolSetup) (ms : List Move) (idx : Nat) :
    runTraceMoves r₀ (ms.take idx) ≤ runTraceMoves r₀ ms := by
  have hsplit : ms = ms.take idx ++ ms.drop idx := (List.take_append_drop idx ms).symm
  conv => rhs; rw [hsplit]
  unfold runTraceMoves; simp only [runMoves]
  rw [runMoves_append_fst_loc]
  exact runMoves_le (ms.drop idx) _

theorem pathFaithful_setSendAddr_of_traceEntriesLt {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (hpf : PathFaithful interpretation r₀ S g ms τ) {ts : Nat}
    (htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms)) (addr : HwBytes) :
    PathFaithful interpretation r₀ S (setSendAddr g ts addr) ms τ := by
  intro idx mv promote b p hmi hpp hcs hpw
  rw [hpf idx mv promote b p hmi hpp hcs hpw]
  refine exists_congr fun ek => and_congr_right fun hek => ?_
  have hek_lt : StampsLt interpretation S g ts ek :=
    stampsLt_of_mem_bobDoneBaseKeys (runTrace_take_le_loc r₀ ms idx) htr hek
  rw [gamma_setSendAddr_of_stampsLt interpretation S g ts addr ek hek_lt]

theorem recvRepresentations_setSendAddr_of_traceEntriesLt {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {b : HwBytes} {t : DY.Bytes}
    (ht : t ∈ recvRepresentations interpretation r₀ S g ms b) {ts : Nat}
    (htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms)) (addr : HwBytes) :
    t ∈ recvRepresentations interpretation r₀ S (setSendAddr g ts addr) ms b := by
  have ht_lt : StampsLt interpretation S g ts t := traceEntriesLt_knows htr ht.1
  refine ⟨ht.1, ?_, ht.2.2.1, fun msg hparse => ?_⟩
  · rw [gamma_setSendAddr_of_stampsLt interpretation S g ts addr t ht_lt]; exact ht.2.1
  · obtain ⟨hw_lt, hm_lt, hrk_lt, hct_lt, hpq_lt⟩ := stampsLt_parseTrSignalMsg ht_lt hparse
    have hmsg := ht.2.2.2 msg hparse
    refine ⟨?_, ?_, hmsg.2.2.1, fun sm hsm => ?_⟩
    · rw [gamma_setSendAddr_of_stampsLt interpretation S g ts addr msg.wire hw_lt]; exact hmsg.1
    · rw [gamma_setSendAddr_of_stampsLt interpretation S g ts addr msg.mac hm_lt]; exact hmsg.2.1
    · have hsm' := hmsg.2.2.2 sm hsm
      refine ⟨?_, ?_, ?_, hsm'.2.2.2⟩
      · rw [gamma_setSendAddr_of_stampsLt interpretation S g ts addr msg.ciphertext hct_lt]; exact hsm'.1
      · rw [gamma_setSendAddr_of_stampsLt interpretation S g ts addr msg.ratchetKey hrk_lt]; exact hsm'.2.1
      · rw [gamma_setSendAddr_of_stampsLt interpretation S g ts addr msg.pqRatchet hpq_lt]; exact hsm'.2.2.1

theorem preKeyRepresentations_setSendAddr_of_traceEntriesLt {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {b : HwBytes} {x : PreKeyRep}
    (hx : x ∈ preKeyRepresentations interpretation r₀ S g ms b) {ts : Nat}
    (htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms)) (addr : HwBytes) :
    x ∈ preKeyRepresentations interpretation r₀ S (setSendAddr g ts addr) ms b := by
  have hek_lt : StampsLt interpretation S g ts x.ek := traceEntriesLt_knows htr hx.1
  have hct_lt : StampsLt interpretation S g ts x.ct := traceEntriesLt_knows htr hx.2.1
  have hmsg_lt : StampsLt interpretation S g ts x.msg := traceEntriesLt_knows htr hx.2.2.1
  have hv_list : ∀ u ∈ [x.ek, x.ct, x.msg], StampsLt interpretation S g ts u := by
    intro u hu; simp at hu; rcases hu with rfl | rfl | rfl <;> assumption
  refine ⟨hx.1, hx.2.1, hx.2.2.1,
    (preKeyRecvMatches_setSendAddr_of_visStampsLt interpretation r₀ S g ts addr b
      [x.ek, x.ct, x.msg] hv_list).mpr hx.2.2.2.1, ?_⟩
  obtain ⟨p, hpw, msg, hparse, hw, hmac, hspqr, hct, hrk, hpq, hcnt, hver⟩ := hx.2.2.2.2
  obtain ⟨hw_lt, hm_lt, hrk_lt, hct_lt', hpq_lt⟩ := stampsLt_parseTrSignalMsg hmsg_lt hparse
  refine ⟨p, hpw, msg, hparse, ?_, ?_, hspqr, ?_, ?_, ?_, hcnt, hver⟩
  · rwa [gamma_setSendAddr_of_stampsLt interpretation S g ts addr msg.wire hw_lt]
  · rwa [gamma_setSendAddr_of_stampsLt interpretation S g ts addr msg.mac hm_lt]
  · rwa [gamma_setSendAddr_of_stampsLt interpretation S g ts addr msg.ciphertext hct_lt']
  · rwa [gamma_setSendAddr_of_stampsLt interpretation S g ts addr msg.ratchetKey hrk_lt]
  · rwa [gamma_setSendAddr_of_stampsLt interpretation S g ts addr msg.pqRatchet hpq_lt]

theorem readFaithful_setSendAddr_of_traceEntriesLt {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (hrf : ReadFaithful interpretation r₀ S g ms τ) {ts : Nat}
    (htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms)) (addr : HwBytes) :
    ReadFaithful interpretation r₀ S (setSendAddr g ts addr) ms τ := by
  intro ev hev hkind
  have h := hrf ev hev hkind
  revert h
  split <;> intro h
  · exact recvRepresentations_setSendAddr_of_traceEntriesLt h htr addr
  · intro p hp; exact recvRepresentations_setSendAddr_of_traceEntriesLt (h p hp) htr addr
  · exact preKeyRepresentations_setSendAddr_of_traceEntriesLt h htr addr
  · trivial

theorem compat_setSendAddr {interpretation : ExternInterpretation}
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) {ts : Nat}
    (hts : (runTraceMoves r₀ ms).length ≤ ts)
    (htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms))
    (addr : HwBytes) (hc : GhostAndSemMatchSetup interpretation r₀ S g) :
    GhostAndSemMatchSetup interpretation r₀ S (setSendAddr g ts addr) := by
  refine ⟨hc.1, fun t ht => ?_, hc.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · unfold ProtocolSetup.spkSigTerm
    rw [gamma_setSendAddr_of_stampsLt interpretation S g ts addr (setupPublic r₀ 5)
        (stampsLt_setupPublic hts htr 5)]
    exact hc.2.1 r₀.spkSigTerm (by simp)
  · unfold ProtocolSetup.pqpkPubTerm
    rw [gamma_setSendAddr_of_stampsLt interpretation S g ts addr (setupPublic r₀ 6)
        (stampsLt_setupPublic hts htr 6)]
    exact hc.2.1 r₀.pqpkPubTerm (by simp)
  · unfold ProtocolSetup.pqpkSigTerm
    rw [gamma_setSendAddr_of_stampsLt interpretation S g ts addr (setupPublic r₀ 7)
        (stampsLt_setupPublic hts htr 7)]
    exact hc.2.1 r₀.pqpkSigTerm (by simp)

theorem matchedPrefix_setSendAddr {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move}
    {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r₀ S who g ms τ) (addr : HwBytes) :
    MatchedPrefix interpretation r₀ S who (setSendAddr g (runTraceMoves r₀ ms).length addr) ms τ := by
  let ts := (runTraceMoves r₀ ms).length
  have hts : (runTraceMoves r₀ ms).length ≤ ts := Nat.le_refl _
  have htr : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms) :=
    traceEntriesLt_of_reachable interpretation S g ts hmp.2.1.2.2.1.1 hts
  refine ⟨compat_setSendAddr r₀ S g ms hts htr addr hmp.1,
    hmp.2.1, hmp.2.2.1,
    pathFaithful_setSendAddr_of_traceEntriesLt hmp.2.2.2.1 htr addr,
    readFaithful_setSendAddr_of_traceEntriesLt hmp.2.2.2.2.1 htr addr, ?_⟩
  have hfor := hmp.2.2.2.2.2
  rw [List.forall₂_iff_zip] at hfor ⊢
  refine ⟨hfor.1, fun {e v} hx => ?_⟩
  have hvs : VisStampsLt interpretation S g ts v :=
    runMoves_visStampsLt (r₀.setupMove :: ms) DY.Trace.nil opkNetOK_nil hts htr v
      (List.of_mem_zip hx |>.2)
  exact (eventMatchesEntry_setSendAddr_of_visStampsLt interpretation r₀ S g ts addr e v hvs).mpr
    (hfor.2 hx)

theorem matchedPrefix_sendGhost {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r₀ S who g ms τ) (pt coins : HwBytes) :
    MatchedPrefix interpretation r₀ S who (sendGhost g (runTraceMoves r₀ ms).length pt coins) ms τ :=
  matchedPrefix_setSendAddr
    (matchedPrefix_updateFreshAt
      (matchedPrefix_updateFreshAt hmp (Nat.le_refl _) 32 pt)
      (Nat.le_succ _) coins.length coins)
    []

theorem matchedPrefix_sendPendingGhost {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (hmp : MatchedPrefix interpretation r₀ S who g ms τ) (pt coins : HwBytes) :
    MatchedPrefix interpretation r₀ S who (sendPendingGhost g (runTraceMoves r₀ ms).length pt coins) ms τ :=
  matchedPrefix_setSendAddr
    (matchedPrefix_updateFreshAt
      (matchedPrefix_updateFreshAt hmp (Nat.le_refl _) 32 pt)
      (Nat.le_succ _) coins.length coins)
    pqHarnessAddrBytes

end Symbolic.Swarm.CREF.SendWire

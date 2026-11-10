/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupHighBitComp

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.PQXDH.Refinement
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp
def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
theorem hexBytes_ofList (cs : List Char) : hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by unfold hexBytes hexDigit; rw [String.toList_ofList]
attribute [local irreducible] Symbolic.BugInjection.hexBytes
abbrev compI0 : ExternInterpretation := Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compI0
def ptMsg35 : HwBytes :=
  match (Witnesses.Cheval26SmallSubgroupHighBitComp.trace[35]? : Option MachineEvent) with
  | some (.pt b) => b
  | _ => []
def recvMsg38 : HwBytes :=
  match (Witnesses.Cheval26SmallSubgroupHighBitComp.trace[38]? : Option MachineEvent) with
  | some (.recv b) => b
  | _ => []
theorem trace_getElem?_35 : Witnesses.Cheval26SmallSubgroupHighBitComp.trace[35]? = some (.pt ptMsg35) := rfl
theorem trace_getElem?_38 : Witnesses.Cheval26SmallSubgroupHighBitComp.trace[38]? = some (.recv recvMsg38) := rfl
def NoFullMatchHB : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → Common443.CompSetupSecrecy.NoBrk r ms → ¬ MatchedPrefix compI0 r S who g ms trace
def PtDeadHB : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → Common443.CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who ok g ms (trace.take 35) → EventMatchesEntry compI0 r S g (.pt ptMsg35) (ptEntryOfNextEncrypt r ms) → ¬ (∀ g' ∈ PrefixGhosts compI0 r S who g ms (trace.take 35),
        MemoCollisionOn compI0 r S g' (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms) (runVis r ms) (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms)
def NoBobDone38HB : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → ExplainsMoves compI0 r S who ok g ms (trace.take 38) → bobDoneBaseKeys (runTraceMoves r ms) = []
def NoBsc38HB : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup compI0 r → Common443.CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who ok g ms (trace.take 38) → parsePreKeyWire recvMsg38 = some p → ∃ g' ms', ExplainsMoves compI0 r S who ok g' ms' (trace.take 38) ∧ ∃ x ∈ preKeyRepresentations compI0 r S g' ms' recvMsg38, ¬ BobStartCollision compI0 r S g' ms' p x
elab "chars_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id); let eWhnf ← Lean.Meta.whnf e; let args := eWhnf.getAppArgs; let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"
elab "str_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id); let eWhnf ← Lean.Meta.whnf e; let args := eWhnf.getAppArgs; let sLit ← Lean.Meta.whnf args[0]!
  return sLit
def recvMsg38Chars : List Char := chars_of_hex_def recvMsg38
theorem recvMsg38_eq_hex : recvMsg38 = hexBytes (str_of_hex_def recvMsg38) := rfl
theorem recvMsg38Str_eq : (str_of_hex_def recvMsg38) = String.ofList recvMsg38Chars := rfl
def recvMsg38Fast : HwBytes := hexBytes.go hexDigit recvMsg38Chars
theorem recvMsg38_eq_fast : recvMsg38 = recvMsg38Fast := by change recvMsg38 = hexBytes.go hexDigit recvMsg38Chars; rw [recvMsg38_eq_hex, recvMsg38Str_eq, hexBytes_ofList]
theorem recvMsg38Fast_head_ne_whisper : recvMsg38Fast.head? ≠ some wireWhisperTag := by decide +kernel
theorem recvMsg38_head_ne_whisper : recvMsg38.head? ≠ some wireWhisperTag := by rw [recvMsg38_eq_fast]; exact recvMsg38Fast_head_ne_whisper
section KyberMismatchCompI0
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
private theorem leBytes_length : ∀ (k v : Nat), (leBytes k v).length = k
  | 0, _ => rfl
  | k + 1, v => by simp [leBytes, leBytes_length k]
private theorem compKyberCt0_length : compKyberCt0.length = 1568 := leBytes_length 1568 _
private theorem compKyberCt1_length : compKyberCt1.length = 1568 := leBytes_length 1568 _
private theorem compKyberCt2_length : compKyberCt2.length = 1568 := leBytes_length 1568 _
private theorem compDefaultKyberCt_length : compDefaultKyberCt.length = 1568 := List.length_replicate
private theorem compKyberCt1_beq_ct0 : (compKyberCt1 == compKyberCt0) = false :=
  Bool.eq_false_iff.mpr fun h => by
    have := congrArg List.head? (eq_of_beq h); revert this; decide
private theorem compKyberCt2_beq_ct0 : (compKyberCt2 == compKyberCt0) = false :=
  Bool.eq_false_iff.mpr fun h => by
    have := congrArg List.head? (eq_of_beq h); revert this; decide
private theorem compKyberCt2_beq_ct1 : (compKyberCt2 == compKyberCt1) = false :=
  Bool.eq_false_iff.mpr fun h => by
    have := congrArg List.head? (eq_of_beq h); revert this; decide
private theorem compDefaultKyberCt_beq_ct0 : (compDefaultKyberCt == compKyberCt0) = false :=
  Bool.eq_false_iff.mpr fun h => by
    have := congrArg List.head? (eq_of_beq h); revert this; decide
private theorem compDefaultKyberCt_beq_ct1 : (compDefaultKyberCt == compKyberCt1) = false :=
  Bool.eq_false_iff.mpr fun h => by
    have := congrArg List.head? (eq_of_beq h); revert this; decide
private theorem compDefaultKyberCt_beq_ct2 : (compDefaultKyberCt == compKyberCt2) = false :=
  Bool.eq_false_iff.mpr fun h => by
    have := congrArg List.head? (eq_of_beq h); revert this; decide
private theorem take_append_of_eq_length {α : Type} {l1 l2 : List α} {n : Nat} (h : l1.length = n) : (l1 ++ l2).take n = l1 := by subst h; exact List.take_left
private theorem drop_append_of_eq_length {α : Type} {l1 l2 : List α} {n : Nat} (h : l1.length = n) : (l1 ++ l2).drop n = l2 := by subst h; exact List.drop_left
private theorem compKyberDecaps_encaps (e : HwBytes) : compKyberDecaps ((compKyberEncaps e).take 1568) = (compKyberEncaps e).drop 1568 := by
  unfold compKyberEncaps
  split
  · rw [take_append_of_eq_length compKyberCt0_length, drop_append_of_eq_length compKyberCt0_length]; simp [compKyberDecaps]
  · split
    · rw [take_append_of_eq_length compKyberCt1_length, drop_append_of_eq_length compKyberCt1_length]; simp [compKyberDecaps, compKyberCt1_beq_ct0]
    · split
      · rw [take_append_of_eq_length compKyberCt2_length, drop_append_of_eq_length compKyberCt2_length]; simp [compKyberDecaps, compKyberCt2_beq_ct0, compKyberCt2_beq_ct1]
      · rw [take_append_of_eq_length compDefaultKyberCt_length, drop_append_of_eq_length compDefaultKyberCt_length]; simp [compKyberDecaps, compDefaultKyberCt_beq_ct0, compDefaultKyberCt_beq_ct1, compDefaultKyberCt_beq_ct2]
theorem not_kyberMismatch_compI0 (r : Records) (p : PreKeyFields) : ¬ KyberMismatch compI0 r p := by rintro ⟨e, ct, ss, _, _, henc, hdec⟩; change Option.map (fun out => (out.take 1568, out.drop 1568)) (some (compKyberEncaps e)) = some (ct, ss) at henc; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at henc; obtain ⟨hct, hss⟩ := henc; change some (compKyberDecaps ct) ≠ some ss at hdec; apply hdec; rw [← hct, ← hss, compKyberDecaps_encaps]
end KyberMismatchCompI0
def NoAccept (τ : List MachineEvent) : Prop := ∀ e ∈ τ, eventKind e ≠ .accept
theorem not_readCollision_of_noAccept {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ₁ : List MachineEvent} (hna : NoAccept τ₁) : ¬ ReadCollision i r S g ms τ₁ := by
  rintro ⟨_, σ₁, e, σ₂, _, hτ, _, _, ⟨pt, hacc⟩, _⟩
  have hmem : MachineEvent.accept pt ∈ σ₂.filter fun e => eventKind e != .rng := List.mem_of_mem_head? hacc
  have hmem₂ : MachineEvent.accept pt ∈ τ₁ := (by rw [hτ]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_of_mem_filter hmem))); exact hna _ hmem₂ rfl
theorem noAccept_trace_take38 : NoAccept (trace.take 38) := by
  unfold NoAccept
  decide
def isAcceptedRecvKindAt (τ : List MachineEvent) (n : Nat) : Bool :=
  match τ[n]? with
  | some e =>
    (eventKind e == .recv) &&
      match ((τ.drop (n + 1)).filter fun e' => eventKind e' != .rng).head? with
      | some e' => eventKind e' == .accept
      | none => false
  | none => false
def isPtKindAt (τ : List MachineEvent) (n : Nat) : Bool :=
  match τ[n]? with
  | some e => eventKind e == .pt
  | none => false
theorem isAcceptedRecvKindAt_of_recv_accepted {τ : List MachineEvent} {n : Nat} {b : HwBytes} {pt : HwBytes} (hget : τ[n]? = some (.recv b)) (hacc : ((τ.drop (n + 1)).filter fun e => eventKind e != .rng).head? = some (.accept pt)) : isAcceptedRecvKindAt τ n = true := by unfold isAcceptedRecvKindAt; rw [hget, hacc]; rfl
theorem isPtKindAt_of_pt {τ : List MachineEvent} {n : Nat} {b : HwBytes} (hget : τ[n]? = some (.pt b)) : isPtKindAt τ n = true := by unfold isPtKindAt; rw [hget]; rfl
theorem split_at_length {α : Type} {τ τ₁ τ₂ : List α} {e : α} (h : τ = τ₁ ++ e :: τ₂) : τ₁.length < τ.length ∧ τ₁ = τ.take τ₁.length ∧ τ[τ₁.length]? = some e ∧ τ₂ = τ.drop (τ₁.length + 1) := by
  subst h; refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · rw [List.drop_append]; simp
private theorem highBitComp_acceptedRecv_fin : ∀ k : Fin trace.length, isAcceptedRecvKindAt trace k.1 = true → k.1 = 38 := by decide
private theorem highBitComp_pt_fin : ∀ k : Fin trace.length, isPtKindAt trace k.1 = true → k.1 = 35 := by decide
theorem highBitComp_acceptedRecv_index {n : Nat} (hn : n < trace.length) (h : isAcceptedRecvKindAt trace n = true) : n = 38 := highBitComp_acceptedRecv_fin ⟨n, hn⟩ h
theorem highBitComp_pt_index {n : Nat} (hn : n < trace.length) (h : isPtKindAt trace n = true) : n = 35 := highBitComp_pt_fin ⟨n, hn⟩ h
theorem not_knownBaseKey_of_bobDone_nil {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields} (hnil : bobDoneBaseKeys (runTraceMoves r ms) = []) : ¬ KnownBaseKey i r S g ms p := by rintro ⟨ek, hek, _⟩; rw [hnil] at hek; exact List.not_mem_nil hek
theorem not_collisionAt_of_gen (setup₀ : PQXDHSpqrSetup) (who₀ : List Participant) (ok₀ : Nat → Bool) (τ : List MachineEvent) (pt35 msg38 : HwBytes) (hget35 : τ[35]? = some (.pt pt35)) (hget38 : τ[38]? = some (.recv msg38)) (hhead38 : msg38.head? ≠ some wireWhisperTag) (hna38 : NoAccept (τ.take 38)) (hacc_idx : ∀ {n : Nat}, n < τ.length → isAcceptedRecvKindAt τ n = true → n = 38) (hpt_idx : ∀ {n : Nat}, n < τ.length → isPtKindAt τ n = true → n = 35) (hPt : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup₀ compI0 r → Common443.CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who₀ ok₀ g ms (τ.take 35) → EventMatchesEntry compI0 r S g (.pt pt35) (ptEntryOfNextEncrypt r ms) → ¬ (∀ g' ∈ PrefixGhosts compI0 r S who₀ g ms (τ.take 35), MemoCollisionOn compI0 r S g' (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms) (runVis r ms) (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms)) (hBob : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup₀ compI0 r → ExplainsMoves compI0 r S who₀ ok₀ g ms (τ.take 38) → bobDoneBaseKeys (runTraceMoves r ms) = []) (hBsc : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup₀ compI0 r → Common443.CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who₀ ok₀ g ms (τ.take 38) → parsePreKeyWire msg38 = some p → ∃ g' ms', ExplainsMoves compI0 r S who₀ ok₀ g' ms' (τ.take 38) ∧ ∃ x ∈ preKeyRepresentations compI0 r S g' ms' msg38, ¬ BobStartCollision compI0 r S g' ms' p x) {r : Records} {S : Sem} (hfits : compFitsPinned setup₀ compI0 r) (hnb : ∀ ms, Common443.CompSetupSecrecy.NoBrk r ms) : ¬ CollisionAt compI0 r S who₀ ok₀ τ := by
  rintro ⟨τ₁, e, τ₂, g, ms, hτ, hex, hbody⟩; obtain ⟨hlen, htake, hget, hdrop⟩ := split_at_length hτ
  cases e with
  | recv msg =>
    cases msg with
    | nil => exact hbody
    | cons tag body =>
      dsimp only at hbody; obtain ⟨⟨pt, hacc⟩, hdisj⟩ := hbody; rw [hdrop] at hacc; have hn38 : τ₁.length = 38 := hacc_idx hlen (isAcceptedRecvKindAt_of_recv_accepted hget hacc); rw [hn38] at htake hget hdrop; rw [htake] at hex
      have hmsg : tag :: body = msg38 := by
        rw [hget38] at hget
        injection hget with h1
        injection h1 with h2
        exact h2.symm
      rcases hdisj with ⟨htag, _⟩ | ⟨p, hp, ⟨hkb, _⟩ | ⟨_, hpk⟩⟩
      · apply hhead38; rw [← hmsg, htag]; rfl
      · exact not_knownBaseKey_of_bobDone_nil (hBob r S g ms hfits hex) hkb
      · rw [hmsg] at hp; rw [htake, hmsg] at hpk
        rcases hpk.2 with hkm | hall
        · exact not_kyberMismatch_compI0 r p hkm
        · obtain ⟨g', ms', hex', x, hx, hnbsc⟩ := hBsc r S g ms p hfits (hnb ms) hex hp; exact hnbsc (hall g' ms' hex' (not_readCollision_of_noAccept hna38) x hx)
  | pt b =>
    dsimp only at hbody; have hn35 : τ₁.length = 35 := hpt_idx hlen (isPtKindAt_of_pt hget); rw [hn35] at htake hget; rw [htake] at hex hbody
    have hb : b = pt35 := by
      rw [hget35] at hget
      injection hget with h1
      injection h1 with h2
      exact h2.symm
    rw [hb] at hbody; exact hPt r S g ms hfits (hnb ms) hex hbody.1 hbody.2
  | send _ => exact hbody
  | rng _ => exact hbody
  | accept _ => exact hbody
  | leak _ => exact hbody
theorem not_collisionAt_of (hPt : PtDeadHB) (hBob : NoBobDone38HB) (hBsc : NoBsc38HB) {r : Records} {S : Sem} (hfits : compFitsPinned setup compI0 r) (hnb : ∀ ms, Common443.CompSetupSecrecy.NoBrk r ms) : ¬ CollisionAt compI0 r S who ok trace := not_collisionAt_of_gen setup who ok trace ptMsg35 recvMsg38 trace_getElem?_35 trace_getElem?_38 recvMsg38_head_ne_whisper noAccept_trace_take38 highBitComp_acceptedRecv_index highBitComp_pt_index hPt hBob hBsc hfits hnb
end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.Top
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26WeakStateIdx1

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop
open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.PQXDH.Refinement
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg computeMac trMsgKeys)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443 (hexDigit hexBytes_ofList isAcceptedRecvKindAt isPtKindAt isAcceptedRecvKindAt_of_recv_accepted isPtKindAt_of_pt)
export Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443 ( hexDigit hexBytes_ofList isAcceptedRecvKindAt isPtKindAt isAcceptedRecvKindAt_of_recv_accepted isPtKindAt_of_pt)
attribute [local irreducible] Symbolic.BugInjection.hexBytes
elab "chars_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let sLit ← Lean.Meta.whnf (← Lean.Meta.whnf e).getAppArgs[0]!
  match sLit with | .lit (.strVal s) => return Lean.toExpr s.toList | _ => throwError "not strVal: {sLit}"
elab "str_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  Lean.Meta.whnf (← Lean.Meta.whnf e).getAppArgs[0]!
abbrev compI0 : ExternInterpretation := Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compI0
def ptAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with | some (.pt b) => b | _ => []
def recvAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with | some (.recv b) => b | _ => []
theorem ptAt_of_getElem? {n : Nat} {b : HwBytes} (h : (Witnesses.Cheval26WeakStateIdx1.trace)[n]? = some (.pt b)) : ptAt n = b := by unfold ptAt; rw [h]
theorem recvAt_of_getElem? {n : Nat} {b : HwBytes} (h : (Witnesses.Cheval26WeakStateIdx1.trace)[n]? = some (.recv b)) : recvAt n = b := by unfold recvAt; rw [h]
def NoFullMatchWS : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy.NoBrk r ms → ¬ MatchedPrefix compI0 r S who g ms trace
def PtDeadAt (n : Nat) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who ok g ms (trace.take n) → EventMatchesEntry compI0 r S g (.pt (ptAt n)) (ptEntryOfNextEncrypt r ms) → ¬ (∀ g' ∈ PrefixGhosts compI0 r S who g ms (trace.take n), MemoCollisionOn compI0 r S g' (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms) (runVis r ms) (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms)
def NotKnownBaseKeyAt (n : Nat) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup compI0 r → ExplainsMoves compI0 r S who ok g ms (trace.take n) → parsePreKeyWire (recvAt n) = some p → ¬ KnownBaseKey compI0 r S g ms p
def NoBscAt (n : Nat) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup compI0 r → Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who ok g ms (trace.take n) → parsePreKeyWire (recvAt n) = some p → ∃ g' ms', ExplainsMoves compI0 r S who ok g' ms' (trace.take n) ∧ ¬ ReadCollision compI0 r S g' ms' (trace.take n) ∧ ∃ x ∈ preKeyRepresentations compI0 r S g' ms' (recvAt n), ¬ BobStartCollision compI0 r S g' ms' p x
structure SpecObls : Prop where
  noFull : NoFullMatchWS
  ptDead : ∀ n, n = 35 ∨ n = 38 ∨ n = 78 → PtDeadAt n
  notKnown : ∀ n, n = 40 ∨ n = 81 → NotKnownBaseKeyAt n
  noBsc : ∀ n, n = 40 ∨ n = 81 → NoBscAt n
def recvCtOf (b : HwBytes) : HwBytes :=
  match (parsePreKeyWire b).bind (·.kyberCiphertext) with | some (_ :: ct) => ct | _ => []
def recvCt (n : Nat) : HwBytes := recvCtOf (recvAt n)
def recv40Chars : List Char := chars_of_hex (recvAt 40)
def recv81Chars : List Char := chars_of_hex (recvAt 81)
theorem recvAt40_eq_hex : recvAt 40 = hexBytes (str_of_hex (recvAt 40)) := rfl
theorem recvAt81_eq_hex : recvAt 81 = hexBytes (str_of_hex (recvAt 81)) := rfl
theorem recv40Str_eq : (str_of_hex (recvAt 40)) = String.ofList recv40Chars := rfl
theorem recv81Str_eq : (str_of_hex (recvAt 81)) = String.ofList recv81Chars := rfl
def recv40Fast : HwBytes := hexBytes.go hexDigit recv40Chars
def recv81Fast : HwBytes := hexBytes.go hexDigit recv81Chars
theorem recvAt40_eq_fast : recvAt 40 = recv40Fast := by change recvAt 40 = hexBytes.go hexDigit recv40Chars; rw [recvAt40_eq_hex, recv40Str_eq, hexBytes_ofList]
theorem recvAt81_eq_fast : recvAt 81 = recv81Fast := by change recvAt 81 = hexBytes.go hexDigit recv81Chars; rw [recvAt81_eq_hex, recv81Str_eq, hexBytes_ofList]
theorem recvAt_head_ne_whisper {n : Nat} (hn : n = 40 ∨ n = 81) : (recvAt n).head? ≠ some wireWhisperTag := by rcases hn with rfl | rfl <;> [rw [recvAt40_eq_fast]; rw [recvAt81_eq_fast]] <;> decide +kernel
theorem recvAt_kyberCt_eq {n : Nat} (hn : n = 40 ∨ n = 81) : ∀ p, parsePreKeyWire (recvAt n) = some p → p.kyberCiphertext = some (kyberKey (recvCt n)) := by
  have h : ((parsePreKeyWire (recvAt n)).bind (·.kyberCiphertext) == some (kyberKey (recvCt n))) = true := by
    unfold recvCt; rcases hn with rfl | rfl <;> [rw [recvAt40_eq_fast]; rw [recvAt81_eq_fast]] <;> decide +kernel
  intro p hp; simpa [hp] using eq_of_beq h
theorem recvCt_mem_kyberCts {n : Nat} (hn : n = 40 ∨ n = 81) : recvCt n ∈ setup.kyberCts := by unfold recvCt; rcases hn with rfl | rfl <;> [rw [recvAt40_eq_fast]; rw [recvAt81_eq_fast]] <;> decide +kernel
theorem not_kyberMismatch_at {n : Nat} (hn : n = 40 ∨ n = 81) {i : ExternInterpretation} {r : Records} (hfits : compFits setup i r) : ∀ p, parsePreKeyWire (recvAt n) = some p → ¬ KyberMismatch i r p := by
  rintro p hp ⟨e, ct, ss, helen, hpct, henc, hdec⟩
  rw [recvAt_kyberCt_eq hn p hp] at hpct; injection hpct with hkk; unfold kyberKey at hkk; injection hkk with _ hct_eq; subst hct_eq
  exact hdec (hfits.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (recvCt_mem_kyberCts hn) e ss helen henc)
private theorem acceptedRecv_fin : ∀ k : Fin trace.length, isAcceptedRecvKindAt trace k.1 = true → k.1 = 40 ∨ k.1 = 81 := by decide
private theorem pt_fin : ∀ k : Fin trace.length, isPtKindAt trace k.1 = true → k.1 = 35 ∨ k.1 = 38 ∨ k.1 = 78 := by decide
private theorem split_at_length {α : Type} {τ τ₁ τ₂ : List α} {e : α} (h : τ = τ₁ ++ e :: τ₂) : τ₁.length < τ.length ∧ τ₁ = τ.take τ₁.length ∧ τ[τ₁.length]? = some e ∧ τ₂ = τ.drop (τ₁.length + 1) := by
  subst h; refine ⟨by simp, by simp, by simp, by rw [List.drop_append]; simp⟩
theorem not_collisionAt_of (O : SpecObls) {r : Records} {S : Sem} (hfits : compFitsPinned setup compI0 r)
    (hnb : ∀ (g : Ghost) (ms : List Move) (τ₁ : List MachineEvent), ExplainsMoves compI0 r S who ok g ms τ₁ → Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy.NoBrk r ms) :
    ¬ CollisionAt compI0 r S who ok trace := by
  rintro ⟨τ₁, e, τ₂, g, ms, hτ, hex, hbody⟩
  obtain ⟨hlen, htake, hget, hdrop⟩ := split_at_length hτ
  generalize τ₁.length = n at hlen htake hget hdrop; subst htake
  cases e with
  | recv msg =>
    cases msg with
    | nil => exact hbody
    | cons tag body =>
      obtain ⟨⟨pt, hacc⟩, hdisj⟩ := hbody; rw [hdrop] at hacc; have hn := acceptedRecv_fin ⟨n, hlen⟩ (isAcceptedRecvKindAt_of_recv_accepted hget hacc); have hb : recvAt n = tag :: body := recvAt_of_getElem? hget
      rcases hdisj with ⟨htag, _⟩ | ⟨p, hp, ⟨hkb, _⟩ | ⟨_, hpk⟩⟩
      · exact recvAt_head_ne_whisper hn (by rw [hb, htag]; rfl)
      · rw [← hb] at hp; exact O.notKnown n hn r S g ms p hfits hex hp hkb
      · rw [← hb] at hp hpk; rcases hpk.2 with hkm | hall
        · exact not_kyberMismatch_at hn hfits.1 p hp hkm
        · obtain ⟨g', ms', hex', hnrc, x, hx, hnbsc⟩ := O.noBsc n hn r S g ms p hfits (hnb g ms _ hex) hex hp
          exact hnbsc (hall g' ms' hex' hnrc x hx)
  | pt b =>
    have hn := pt_fin ⟨n, hlen⟩ (isPtKindAt_of_pt hget); have hb : ptAt n = b := ptAt_of_getElem? hget; subst hb; exact O.ptDead n hn r S g ms hfits (hnb g ms _ hex) hex hbody.1 hbody.2
  | send _ | rng _ | accept _ | leak _ => exact hbody
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop

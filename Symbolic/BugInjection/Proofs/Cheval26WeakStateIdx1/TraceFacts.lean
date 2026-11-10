/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26WeakStateIdx1

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TRState)
open Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1
def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
theorem hexBytes_ofList (cs : List Char) : hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by unfold hexBytes hexDigit; rw [String.toList_ofList]
attribute [local irreducible] Symbolic.BugInjection.hexBytes
elab "tf_chars_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let sLit ← Lean.Meta.whnf (← Lean.Meta.whnf e).getAppArgs[0]!
  match sLit with | .lit (.strVal s) => return Lean.toExpr s.toList | _ => throwError "not strVal: {sLit}"
elab "tf_str_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  Lean.Meta.whnf (← Lean.Meta.whnf e).getAppArgs[0]!
def seg (a k : Nat) : List MachineEvent := (trace.drop a).take k
theorem take_add_seg (a k : Nat) : trace.take (a + k) = trace.take a ++ seg a k := List.take_add ..
theorem seg0_kinds : (seg 0 35).map eventKind = .recv :: List.replicate 34 .rng := rfl
theorem seg35_kinds : (seg 35 3).map eventKind = [.pt, .rng, .send] := rfl
theorem seg38_kinds : (seg 38 2).map eventKind = [.pt, .send] := rfl
theorem seg40_kinds : (seg 40 3).map eventKind = [.recv, .rng, .accept] := rfl
theorem seg43_kinds : (seg 43 35).map eventKind = .recv :: List.replicate 34 .rng := rfl
theorem seg78_kinds : (seg 78 3).map eventKind = [.pt, .rng, .send] := rfl
theorem trace_length : trace.length = 84 := rfl
theorem take35_eq : trace.take 35 = [] ++ seg 0 35 := rfl
theorem take38_eq : trace.take 38 = trace.take 35 ++ seg 35 3 := take_add_seg 35 3
theorem take40_eq : trace.take 40 = trace.take 38 ++ seg 38 2 := take_add_seg 38 2
theorem take43_eq : trace.take 43 = trace.take 40 ++ seg 40 3 := take_add_seg 40 3
theorem take78_eq : trace.take 78 = trace.take 43 ++ seg 43 35 := take_add_seg 43 35
theorem take81_eq : trace.take 81 = trace.take 78 ++ seg 78 3 := take_add_seg 78 3
theorem trace_eq : trace = trace.take 81 ++ seg 81 3 := by
  rw [← take_add_seg]; rfl
theorem iniShape_of_map_eventKind {blk : List MachineEvent} {ks : List Kind} (hmap : blk.map eventKind = .recv :: ks) (hks : ∀ k ∈ ks, k = .rng) : ∃ bun rs, blk = .recv bun :: rs ∧ ∀ e ∈ rs, eventKind e = .rng := by
  cases blk with
  | nil => cases hmap
  | cons hd tl =>
    simp only [List.map_cons, List.cons.injEq] at hmap; rcases hmap with ⟨hhd, htl⟩
    cases hd <;> try cases hhd
    exact ⟨_, tl, rfl, fun e he => hks (eventKind e) (htl ▸ List.mem_map_of_mem he)⟩
theorem sendShape_of_map_eventKind {blk : List MachineEvent} {ks : List Kind} (hmap : blk.map eventKind = .pt :: ks) (hks : ∀ k ∈ ks, k = .rng ∨ k = .send) : ∃ b_pt tail, blk = .pt b_pt :: tail ∧ ∀ e ∈ tail, eventKind e = .rng ∨ eventKind e = .send := by
  cases blk with
  | nil => cases hmap
  | cons hd tl =>
    simp only [List.map_cons, List.cons.injEq] at hmap; rcases hmap with ⟨hhd, htl⟩
    cases hd <;> try cases hhd
    exact ⟨_, tl, rfl, fun e he => hks (eventKind e) (htl ▸ List.mem_map_of_mem he)⟩
theorem replicate_rng (n : Nat) : ∀ k ∈ List.replicate n Kind.rng, k = .rng := fun _ hk => List.eq_of_mem_replicate hk
theorem rng_send_of_mem_rng_send {k : Kind} (hk : k ∈ [Kind.rng, Kind.send]) : k = .rng ∨ k = .send := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; exact hk
theorem rng_send_of_mem_send {k : Kind} (hk : k ∈ [Kind.send]) : k = .rng ∨ k = .send := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; exact Or.inr hk
def wireAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with | some (.recv b) => b | _ => []
theorem seg40_eq : ∃ b_rng b_pt, seg 40 3 = [.recv (wireAt 40), .rng b_rng, .accept b_pt] := ⟨_, _, rfl⟩
theorem seg81_eq : ∃ b_rng b_pt, seg 81 3 = [.recv (wireAt 81), .rng b_rng, .accept b_pt] := ⟨_, _, rfl⟩
def wire40Chars : List Char := tf_chars_of_hex (wireAt 40)
def wire81Chars : List Char := tf_chars_of_hex (wireAt 81)
theorem wireAt40_eq_hex : wireAt 40 = hexBytes (tf_str_of_hex (wireAt 40)) := rfl
theorem wireAt81_eq_hex : wireAt 81 = hexBytes (tf_str_of_hex (wireAt 81)) := rfl
theorem wire40Str_eq : (tf_str_of_hex (wireAt 40)) = String.ofList wire40Chars := rfl
theorem wire81Str_eq : (tf_str_of_hex (wireAt 81)) = String.ofList wire81Chars := rfl
def wire40Fast : HwBytes := hexBytes.go hexDigit wire40Chars
def wire81Fast : HwBytes := hexBytes.go hexDigit wire81Chars
theorem wireAt40_eq_fast : wireAt 40 = wire40Fast := by change wireAt 40 = hexBytes.go hexDigit wire40Chars; rw [wireAt40_eq_hex, wire40Str_eq, hexBytes_ofList]
theorem wireAt81_eq_fast : wireAt 81 = wire81Fast := by change wireAt 81 = hexBytes.go hexDigit wire81Chars; rw [wireAt81_eq_hex, wire81Str_eq, hexBytes_ofList]
def ek1PubKey : HwBytes := hexBytes.go hexDigit ['8','f','0','7','7','b','9','9','c','f','1','8','8','2','1','e','e','2','a','e','9','6','5','c','8','1','e','4','8','9','c','1', '7','b','e','9','2','f','1','e','e','6','9','8','2','4','6','8','8','5','2','d','a','a','2','5','f','2','d','0','7','6','3','8']
def ek2PubKey : HwBytes := hexBytes.go hexDigit ['9','7','a','8','5','f','f','b','6','d','6','2','c','c','5','f','2','1','b','0','a','4','8','1','8','0','1','2','2','4','9','f', 'c','4','6','f','c','b','2','5','e','e','2','d','1','8','9','6','e','c','c','c','2','e','3','5','f','5','3','3','1','9','1','9']
theorem ek1_ne_ek2 : ecKey ek1PubKey ≠ ecKey ek2PubKey := by decide +kernel
theorem wireAt40_head? : (wireAt 40).head? = some 0x03#8 := by rw [wireAt40_eq_fast]; decide +kernel
theorem wireAt81_head? : (wireAt 81).head? = some 0x03#8 := by rw [wireAt81_eq_fast]; decide +kernel
theorem wireAt40_baseKey : (parsePreKeyWire (wireAt 40)).map (fun p => p.baseKey.take 33) = some (ecKey ek1PubKey) := by rw [wireAt40_eq_fast]; decide +kernel
theorem wireAt81_baseKey : (parsePreKeyWire (wireAt 81)).map (fun p => p.baseKey.take 33) = some (ecKey ek2PubKey) := by rw [wireAt81_eq_fast]; decide +kernel
theorem baseKey_of_map {b : HwBytes} {k : HwBytes} {p : PreKeyFields} (hmap : (parsePreKeyWire b).map (fun p => p.baseKey.take 33) = some k) (hp : parsePreKeyWire b = some p) : p.baseKey.take 33 = k := by rw [hp, Option.map_some, Option.some.injEq] at hmap; exact hmap
theorem parses_of_map {b : HwBytes} {k : HwBytes} (hmap : (parsePreKeyWire b).map (fun p => p.baseKey.take 33) = some k) : ∃ p, parsePreKeyWire b = some p := by cases hp : parsePreKeyWire b with | none => rw [hp] at hmap; cases hmap | some p => exact ⟨p, rfl⟩
theorem wireAt40_parses : ∃ p, parsePreKeyWire (wireAt 40) = some p := parses_of_map wireAt40_baseKey
theorem wireAt81_parses : ∃ p, parsePreKeyWire (wireAt 81) = some p := parses_of_map wireAt81_baseKey
def bobDoneEk? : PQXDHEvent → Option DY.Bytes | .BobDone _ _ _ _ _ _ _ ek _ _ => some ek | _ => none
def AllBobDone (P : DY.Bytes → Prop) (tr : ExecTrace) : Prop := ∀ i ev ek, tr.getEventAt PQXDHEvent i = some ev → bobDoneEk? ev = some ek → P ek
theorem bobDoneBaseKeys_of_allBobDone {P : DY.Bytes → Prop} {tr : ExecTrace} (h : AllBobDone P tr) : ∀ ek ∈ bobDoneBaseKeys tr, P ek := by
  intro ek hek; unfold bobDoneBaseKeys at hek
  rcases List.mem_filterMap.1 hek with ⟨i, _, hi⟩
  rcases hev : tr.getEventAt PQXDHEvent i with _ | ev <;> rw [hev] at hi
  · cases hi
  · cases ev <;> try cases hi
    exact h i _ _ hev rfl
theorem mem_bobDoneBaseKeys_of_mem_sessionBaseKeys {tr : ExecTrace} {stateIdx : Nat} {ek : DY.Bytes} (h : ek ∈ sessionBaseKeys tr stateIdx) : ek ∈ bobDoneBaseKeys tr := by
  unfold sessionBaseKeys DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at h
  cases hst : (tr.at? stateIdx : Option (PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState))) with
  | none => simp [hst] at h
  | some e =>
    simp only [hst, Option.map_some, List.mem_filterMap] at h
    rcases h with ⟨pev, ⟨i, _, hi⟩, hpev⟩
    cases hce : tr.getEventAt CEvent i with
    | none => rw [hce] at hi; cases hi
    | some ev =>
      rw [hce] at hi; cases ev with
      | HandshakeSession s d =>
        dsimp only at hi; split at hi
        · cases hbd : tr.getEventAt PQXDHEvent d with
          | none => rw [hbd] at hi; cases hi
          | some pev' =>
            rw [hbd] at hi; injection hi with hpev_eq; subst hpev_eq
            cases pev' <;> simp at hpev
            subst hpev
            unfold bobDoneBaseKeys; refine List.mem_filterMap.2 ⟨d, ?_, by rw [hbd]⟩
            exact List.mem_range.2 (Symbolic.Swarm.CREF.bks_lt_length_of_getEventAt PQXDHEvent hbd)
        · cases hi
theorem not_knownBaseKey_of_allBobDone_false {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields} (h : AllBobDone (fun _ => False) (runTraceMoves r ms)) : ¬ KnownBaseKey i r S g ms p := fun ⟨ek, hek, _⟩ => bobDoneBaseKeys_of_allBobDone h ek hek
theorem wireAt81_not_knownBaseKey_of_allBobDone_ek1 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields} (hp : parsePreKeyWire (wireAt 81) = some p) (h : AllBobDone (fun ek => ecKey (gamma i S g ek) = ecKey ek1PubKey) (runTraceMoves r ms)) : ¬ KnownBaseKey i r S g ms p := by
  rintro ⟨ek, hek, hbk⟩
  rw [baseKey_of_map wireAt81_baseKey hp, bobDoneBaseKeys_of_allBobDone h ek hek] at hbk; exact ek1_ne_ek2 hbk.symm
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts

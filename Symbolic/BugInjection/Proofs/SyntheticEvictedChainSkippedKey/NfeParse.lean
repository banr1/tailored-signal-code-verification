/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Lean
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws

/-!
# Trace and Wire Parsing Facts for `EvictedChainSkippedKeyCli`

Extracts the 25 `RunEvent`s `ev 0 .. ev 24` of `EvictedChainSkippedKeyCli.trace` with `hexBytes`
kept irreducible, and proves kernel-checked parsing facts for Bob's PreKey inputs (`ev 3`,
`ev 24`), Whisper inputs (`ev 7, 11, 15, 19, 23`), and 32-byte DH ratchet draws.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse

open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (PreKeyFields parsePreKey parsePreKeyWire decodePreKey ecKey clamp
   RunRejected runWrapped)
open Symbolic.BugInjection (hexBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedPubOfIdx evictedPubOfOpt evictedSecretIdx evictedPointIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
  (evictedPointIdx_evictedPubOfOpt)

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

theorem hexBytes_ofList (cs : List Char) :
    hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by
  unfold hexBytes hexDigit
  rw [String.toList_ofList]

attribute [local irreducible] Symbolic.BugInjection.hexBytes

elab "nfe_chars_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let sLit ← Lean.Meta.whnf (← Lean.Meta.whnf e).getAppArgs[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

elab "nfe_str_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  Lean.Meta.whnf (← Lean.Meta.whnf e).getAppArgs[0]!

abbrev cliTrace : List CliEvent :=
  Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli.trace

def dummyRunEvent : RunEvent :=
  { party := "", cmd := .init ⟨"", 0⟩ "", input := [], coins := [], exit := none }

def ev (k : Nat) : RunEvent :=
  match cliTrace[k]? with
  | some (.run e) => e
  | _ => dummyRunEvent

theorem trace_eq_evs :
    cliTrace = [
      .run (ev 0), .run (ev 1), .run (ev 2), .run (ev 3), .run (ev 4),
      .run (ev 5), .run (ev 6), .run (ev 7), .run (ev 8), .run (ev 9),
      .run (ev 10), .run (ev 11), .run (ev 12), .run (ev 13), .run (ev 14),
      .run (ev 15), .run (ev 16), .run (ev 17), .run (ev 18), .run (ev 19),
      .run (ev 20), .run (ev 21), .run (ev 22), .run (ev 23), .run (ev 24)
    ] := rfl

theorem ev_exit_ok (k : Nat) (hk : k < 25) : ∃ out, (ev k).exit = some (0, out) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12
  | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 => exact ⟨_, rfl⟩
  | n + 25 => omega

theorem ev_not_rejected (k : Nat) (hk : k < 25) : ¬ RunRejected (ev k) := by
  obtain ⟨out, hout⟩ := ev_exit_ok k hk
  intro hrej
  exact hrej out hout

theorem ev_alice (k : Nat)
    (hk : k ∈ ([0, 1, 2, 5, 6, 9, 10, 13, 14, 17, 18, 21, 22] : List Nat)) :
    (ev k).party = "alice" := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem ev_bob_send (k : Nat) (hk : k ∈ ([4, 8, 12, 16, 20] : List Nat)) :
    (ev k).party = "bob" ∧ ∃ peer, (ev k).cmd = .send peer := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, _, rfl⟩

theorem ev_bob_recv (k : Nat) (hk : k ∈ ([3, 7, 11, 15, 19, 23, 24] : List Nat)) :
    (ev k).party = "bob" ∧ ∃ peer, (ev k).cmd = .recv peer := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, _, rfl⟩

theorem evictedPubOfIdx_inj {i j : Fin 16} (h : evictedPubOfIdx i = evictedPubOfIdx j) :
    i = j := by
  have hpt := congrArg evictedPointIdx h
  change evictedPointIdx (evictedPubOfOpt (some i)) =
    evictedPointIdx (evictedPubOfOpt (some j)) at hpt
  rw [evictedPointIdx_evictedPubOfOpt, evictedPointIdx_evictedPubOfOpt] at hpt
  exact Option.some.inj hpt

theorem tryFrom_of_parsePreKeyWire {b : HwBytes} {p : PreKeyFields}
    (hp : parsePreKeyWire b = some p) :
    CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec p.message = .ok p.inner := by
  unfold parsePreKeyWire at hp
  cases b with
  | nil => cases hp
  | cons t body =>
    dsimp only at hp
    split at hp <;> try cases hp
    unfold parsePreKey at hp
    cases body with
    | nil => cases hp
    | cons vb bbody =>
      dsimp only at hp
      split at hp <;> try cases hp
      cases hd : decodePreKey bbody with
      | none => rw [hd] at hp; cases hp
      | some m =>
        rw [hd] at hp
        dsimp only at hp
        rcases hm1 : m.baseKey with _ | bk <;>
        rcases hm2 : m.identityKey with _ | ik <;>
        rcases hm3 : m.message with _ | msg <;>
        rcases hm4 : m.signedPreKeyId with _ | sid <;>
          rw [hm1, hm2, hm3, hm4] at hp <;> try cases hp
        dsimp only at hp
        split at hp <;> try cases hp
        cases htr : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg with
        | error _ => rw [htr] at hp; cases hp
        | ok inner =>
          rw [htr] at hp
          injection hp with hp'
          subst hp'
          exact htr

private def ev3InChars : List Char := nfe_chars_of_hex (ev 3).input
private def ev3InFast : HwBytes := hexBytes.go hexDigit ev3InChars
private theorem ev3In_eq : (ev 3).input = ev3InFast := by
  have h1 : (ev 3).input = hexBytes (nfe_str_of_hex (ev 3).input) := rfl
  have h2 : (nfe_str_of_hex (ev 3).input) = String.ofList ev3InChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private def ev24InChars : List Char := nfe_chars_of_hex (ev 24).input
private def ev24InFast : HwBytes := hexBytes.go hexDigit ev24InChars
private theorem ev24In_eq : (ev 24).input = ev24InFast := by
  have h1 : (ev 24).input = hexBytes (nfe_str_of_hex (ev 24).input) := rfl
  have h2 : (nfe_str_of_hex (ev 24).input) = String.ofList ev24InChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private def ev7InChars : List Char := nfe_chars_of_hex (ev 7).input
private def ev7InFast : HwBytes := hexBytes.go hexDigit ev7InChars
private theorem ev7In_eq : (ev 7).input = ev7InFast := by
  have h1 : (ev 7).input = hexBytes (nfe_str_of_hex (ev 7).input) := rfl
  have h2 : (nfe_str_of_hex (ev 7).input) = String.ofList ev7InChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private def ev11InChars : List Char := nfe_chars_of_hex (ev 11).input
private def ev11InFast : HwBytes := hexBytes.go hexDigit ev11InChars
private theorem ev11In_eq : (ev 11).input = ev11InFast := by
  have h1 : (ev 11).input = hexBytes (nfe_str_of_hex (ev 11).input) := rfl
  have h2 : (nfe_str_of_hex (ev 11).input) = String.ofList ev11InChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private def ev15InChars : List Char := nfe_chars_of_hex (ev 15).input
private def ev15InFast : HwBytes := hexBytes.go hexDigit ev15InChars
private theorem ev15In_eq : (ev 15).input = ev15InFast := by
  have h1 : (ev 15).input = hexBytes (nfe_str_of_hex (ev 15).input) := rfl
  have h2 : (nfe_str_of_hex (ev 15).input) = String.ofList ev15InChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private def ev19InChars : List Char := nfe_chars_of_hex (ev 19).input
private def ev19InFast : HwBytes := hexBytes.go hexDigit ev19InChars
private theorem ev19In_eq : (ev 19).input = ev19InFast := by
  have h1 : (ev 19).input = hexBytes (nfe_str_of_hex (ev 19).input) := rfl
  have h2 : (nfe_str_of_hex (ev 19).input) = String.ofList ev19InChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private def ev23InChars : List Char := nfe_chars_of_hex (ev 23).input
private def ev23InFast : HwBytes := hexBytes.go hexDigit ev23InChars
private theorem ev23In_eq : (ev 23).input = ev23InFast := by
  have h1 : (ev 23).input = hexBytes (nfe_str_of_hex (ev 23).input) := rfl
  have h2 : (nfe_str_of_hex (ev 23).input) = String.ofList ev23InChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private theorem ev3_parse_check :
    ((parsePreKeyWire ev3InFast).map fun p =>
      (p.baseKey.take 33 == ecKey (evictedPubOfIdx ⟨3, by decide⟩) &&
       p.inner.senderRatchetKey.bytes.toList == evictedPubOfIdx ⟨4, by decide⟩ &&
       p.inner.counter.toNat == 1)) = some true := by
  decide +kernel

theorem ev3_preKey_fields :
    runWrapped (ev 3) = true ∧
    ∃ p, parsePreKeyWire (ev 3).input = some p ∧
      p.baseKey.take 33 = ecKey (evictedPubOfIdx ⟨3, by decide⟩) ∧
      p.inner.senderRatchetKey.bytes.toList = evictedPubOfIdx ⟨4, by decide⟩ ∧
      p.inner.counter.toNat = 1 := by
  refine ⟨?_, ?_⟩
  · unfold runWrapped
    have hcmd : (ev 3).cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
    rw [hcmd, ev3In_eq]
    decide +kernel
  · have hc := ev3_parse_check
    rw [← ev3In_eq] at hc
    cases hp : parsePreKeyWire (ev 3).input with
    | none => rw [hp] at hc; cases hc
    | some p =>
      rw [hp, Option.map_some, Option.some.injEq] at hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨p, rfl, hc.1.1, hc.1.2, hc.2⟩

private theorem ev24_parse_check :
    ((parsePreKeyWire ev24InFast).map fun p =>
      (p.baseKey.take 33 == ecKey (evictedPubOfIdx ⟨3, by decide⟩) &&
       p.inner.senderRatchetKey.bytes.toList == evictedPubOfIdx ⟨4, by decide⟩ &&
       p.inner.counter.toNat == 0 &&
       (p.message.drop (p.message.length - 8)).take 4 != compTag4)) = some true := by
  decide +kernel

theorem ev24_preKey_fields :
    runWrapped (ev 24) = true ∧
    ∃ p, parsePreKeyWire (ev 24).input = some p ∧
      p.baseKey.take 33 = ecKey (evictedPubOfIdx ⟨3, by decide⟩) ∧
      p.inner.senderRatchetKey.bytes.toList = evictedPubOfIdx ⟨4, by decide⟩ ∧
      p.inner.counter.toNat = 0 ∧
      (p.message.drop (p.message.length - 8)).take 4 ≠ compTag4 := by
  refine ⟨?_, ?_⟩
  · unfold runWrapped
    have hcmd : (ev 24).cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
    rw [hcmd, ev24In_eq]
    decide +kernel
  · have hc := ev24_parse_check
    rw [← ev24In_eq] at hc
    cases hp : parsePreKeyWire (ev 24).input with
    | none => rw [hp] at hc; cases hc
    | some p =>
      rw [hp, Option.map_some, Option.some.injEq] at hc
      simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hc
      exact ⟨p, rfl, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

def WhisperInputSpec (e : RunEvent) (pkIdx : Fin 16) : Prop :=
  runWrapped e = false ∧
  parsePreKeyWire e.input = none ∧
  ∃ body m, e.input = wireWhisperTag :: body ∧
    CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body = .ok m ∧
    m.senderRatchetKey.bytes.toList = evictedPubOfIdx pkIdx ∧
    m.counter.toNat = 0

private def checkWhisperFast (b : HwBytes) (pkIdx : Fin 16) : Bool :=
  match b with
  | tag :: body =>
    tag == wireWhisperTag &&
    match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body with
    | .ok m => m.senderRatchetKey.bytes.toList == evictedPubOfIdx pkIdx && m.counter.toNat == 0
    | .error _ => false
  | [] => false

private theorem whisperInputSpec_of_check {e : RunEvent} {fast : HwBytes} {pkIdx : Fin 16}
    (hcmd : ∃ peer, e.cmd = .recv peer)
    (heq : e.input = fast)
    (hc : checkWhisperFast fast pkIdx = true) :
    WhisperInputSpec e pkIdx := by
  unfold checkWhisperFast at hc
  cases fast with
  | nil => cases hc
  | cons tag body =>
    dsimp only at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with ⟨htag, hrest⟩
    subst htag
    cases htr : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body with
    | error _ => rw [htr] at hrest; cases hrest
    | ok m =>
      rw [htr] at hrest
      simp only [Bool.and_eq_true, beq_iff_eq] at hrest
      obtain ⟨peer, hp⟩ := hcmd
      refine ⟨?_, ?_, body, m, heq, htr, hrest.1, hrest.2⟩
      · unfold runWrapped; rw [hp, heq]; simp
      · rw [heq]; unfold parsePreKeyWire; simp [wireWhisperTag, wirePrekeyTag]

theorem ev7_whisper : WhisperInputSpec (ev 7) ⟨6, by decide⟩ :=
  whisperInputSpec_of_check ⟨_, rfl⟩ ev7In_eq (by decide +kernel)

theorem ev11_whisper : WhisperInputSpec (ev 11) ⟨8, by decide⟩ :=
  whisperInputSpec_of_check ⟨_, rfl⟩ ev11In_eq (by decide +kernel)

theorem ev15_whisper : WhisperInputSpec (ev 15) ⟨10, by decide⟩ :=
  whisperInputSpec_of_check ⟨_, rfl⟩ ev15In_eq (by decide +kernel)

theorem ev19_whisper : WhisperInputSpec (ev 19) ⟨12, by decide⟩ :=
  whisperInputSpec_of_check ⟨_, rfl⟩ ev19In_eq (by decide +kernel)

theorem ev23_whisper : WhisperInputSpec (ev 23) ⟨14, by decide⟩ :=
  whisperInputSpec_of_check ⟨_, rfl⟩ ev23In_eq (by decide +kernel)

private def ev3CoinsChars : List Char := nfe_chars_of_hex (ev 3).coins
private def ev7CoinsChars : List Char := nfe_chars_of_hex (ev 7).coins
private def ev11CoinsChars : List Char := nfe_chars_of_hex (ev 11).coins
private def ev15CoinsChars : List Char := nfe_chars_of_hex (ev 15).coins
private def ev19CoinsChars : List Char := nfe_chars_of_hex (ev 19).coins
private def ev23CoinsChars : List Char := nfe_chars_of_hex (ev 23).coins

theorem ev3_coins_idx :
    evictedSecretIdx (clamp (((ev 3).coins).take 32)) = some ⟨5, by decide⟩ := by
  have h1 : (ev 3).coins = hexBytes (nfe_str_of_hex (ev 3).coins) := rfl
  have h2 : (nfe_str_of_hex (ev 3).coins) = String.ofList ev3CoinsChars := rfl
  rw [h1, h2, hexBytes_ofList]
  decide +kernel

theorem ev7_coins_idx :
    evictedSecretIdx (clamp (((ev 7).coins).take 32)) = some ⟨7, by decide⟩ := by
  have h1 : (ev 7).coins = hexBytes (nfe_str_of_hex (ev 7).coins) := rfl
  have h2 : (nfe_str_of_hex (ev 7).coins) = String.ofList ev7CoinsChars := rfl
  rw [h1, h2, hexBytes_ofList]
  decide +kernel

theorem ev11_coins_idx :
    evictedSecretIdx (clamp (((ev 11).coins).take 32)) = some ⟨9, by decide⟩ := by
  have h1 : (ev 11).coins = hexBytes (nfe_str_of_hex (ev 11).coins) := rfl
  have h2 : (nfe_str_of_hex (ev 11).coins) = String.ofList ev11CoinsChars := rfl
  rw [h1, h2, hexBytes_ofList]
  decide +kernel

theorem ev15_coins_idx :
    evictedSecretIdx (clamp (((ev 15).coins).take 32)) = some ⟨11, by decide⟩ := by
  have h1 : (ev 15).coins = hexBytes (nfe_str_of_hex (ev 15).coins) := rfl
  have h2 : (nfe_str_of_hex (ev 15).coins) = String.ofList ev15CoinsChars := rfl
  rw [h1, h2, hexBytes_ofList]
  decide +kernel

theorem ev19_coins_idx :
    evictedSecretIdx (clamp (((ev 19).coins).take 32)) = some ⟨13, by decide⟩ := by
  have h1 : (ev 19).coins = hexBytes (nfe_str_of_hex (ev 19).coins) := rfl
  have h2 : (nfe_str_of_hex (ev 19).coins) = String.ofList ev19CoinsChars := rfl
  rw [h1, h2, hexBytes_ofList]
  decide +kernel

theorem ev23_coins_idx :
    evictedSecretIdx (clamp (((ev 23).coins).take 32)) = some ⟨15, by decide⟩ := by
  have h1 : (ev 23).coins = hexBytes (nfe_str_of_hex (ev 23).coins) := rfl
  have h2 : (nfe_str_of_hex (ev 23).coins) = String.ofList ev23CoinsChars := rfl
  rw [h1, h2, hexBytes_ofList]
  decide +kernel

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse

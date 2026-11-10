/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Lean
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse

/-!
# Concrete Trace Splitting and Wire/Coin Facts

Concrete index-classification, wire-handoff, and byte-slice lemmas on `trace0`:
locates `.recv` events (`split_recv_trace0`), checks Call 0 bundle slices and 192-byte handshake
coins, bounds send/receive coin lengths, verifies Alice's whisper inputs and DH ratchet coin
indices, and extracts Call 3 `PreKeyFields` with `¬ KyberMismatch`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse

open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag preKeyBundleByteLength)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup PreKeyFields BundlePreKeyIds KyberMismatch parsePreKeyWire ecKey kyberKey clamp
   slice runWrapped nextBundleIds)
open Symbolic.BugInjection (hexBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4 compKyberEncaps)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned evictedPubOfIdx evictedSecretIdx)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (w0 trace0 trace0_length)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (recvCallIndices whisperOrReplayIndices)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev trace_eq_evs hexDigit hexBytes_ofList WhisperInputSpec)

attribute [local irreducible] Symbolic.BugInjection.hexBytes

theorem trace0_eq_cliTrace : trace0 = NfeParse.cliTrace := rfl

theorem trace0_getElem?_eq_ev {k : Nat} (hk : k < 25) :
    trace0[k]? = some (.run (ev k)) := by
  change NfeParse.cliTrace[k]? = some (.run (ev k))
  rw [trace_eq_evs]
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12
  | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 => rfl
  | n + 25 => omega

theorem trace0_take_25 : trace0.take 25 = trace0 := by
  rw [List.take_of_length_le (by rw [trace0_length])]

theorem trace0_take_succ {k : Nat} (hk : k < 25) :
    trace0.take (k + 1) = trace0.take k ++ [.run (ev k)] := by
  have hlen : k < trace0.length := by rw [trace0_length]; exact hk
  rw [List.take_add_one, trace0_getElem?_eq_ev hk]
  rfl

theorem ev_is_recv_iff {k : Nat} (hk : k < 25) :
    (∃ peer, (ev k).cmd = .recv peer) ↔ k ∈ recvCallIndices := by
  constructor
  · rintro ⟨peer, hp⟩
    match k with
    | 0 | 1 | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 22 => cases hp
    | 3 | 5 | 7 | 9 | 11 | 13 | 15 | 17 | 19 | 21 | 23 | 24 => decide
    | n + 25 => omega
  · intro hmem
    simp only [recvCallIndices, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, rfl⟩

theorem split_recv_trace0 {evs₁ : List CliEvent} {evCur : RunEvent} {evs₂ : List CliEvent}
    (hsplit : trace0 = evs₁ ++ .run evCur :: evs₂)
    (hrecv : ∃ peer, evCur.cmd = .recv peer) :
    let k := evs₁.length
    k ∈ recvCallIndices ∧ evs₁ = trace0.take k ∧ evCur = ev k := by
  intro k
  have hk25 : k < 25 := by
    have hlen := congrArg List.length hsplit
    rw [trace0_length, List.length_append, List.length_cons] at hlen
    omega
  have hget : trace0[k]? = some (.run evCur) := by
    rw [hsplit, List.getElem?_append_right (Nat.le_refl k), Nat.sub_self]
    rfl
  rw [trace0_getElem?_eq_ev hk25] at hget
  injection hget with hev
  injection hev with hev'
  subst hev'
  have htake : trace0.take k = evs₁ := by
    rw [hsplit, List.take_left]
  exact ⟨(ev_is_recv_iff hk25).mp hrecv, htake.symm, rfl⟩

theorem mem_whisperOrReplayIndices_of_recv {k : Nat}
    (hk : k ∈ recvCallIndices) (hne3 : k ≠ 3) :
    k ∈ whisperOrReplayIndices := by
  revert k
  decide +kernel

theorem lt_25_of_mem_recvCallIndices {k : Nat} (hk : k ∈ recvCallIndices) : k < 25 := by
  revert k
  decide +kernel

theorem lt_25_of_mem_whisperOrReplayIndices {k : Nat} (hk : k ∈ whisperOrReplayIndices) :
    k < 25 := by
  revert k
  decide +kernel

theorem ev1_to_ev24 : (ev 1).exit = some (0, (ev 24).input) := rfl
theorem ev2_to_ev3 : (ev 2).exit = some (0, (ev 3).input) := rfl
theorem ev3_pt_eq_ev2 : (ev 3).exit = some (0, (ev 2).input) := rfl

theorem whisper_wire_eq {k : Nat} (hk : k ∈ whisperOrReplayIndices) (hne24 : k ≠ 24) :
    (ev (k - 1)).exit = some (0, (ev k).input) ∧
    (ev k).exit = some (0, (ev (k - 1)).input) := by
  simp only [whisperOrReplayIndices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd rfl hne24

private def ev0InChars : List Char := nfe_chars_of_hex (ev 0).input
private def ev0InFast : HwBytes := hexBytes.go hexDigit ev0InChars
private theorem ev0In_eq : (ev 0).input = ev0InFast := by
  have h1 : (ev 0).input = hexBytes (nfe_str_of_hex (ev 0).input) := rfl
  have h2 : (nfe_str_of_hex (ev 0).input) = String.ofList ev0InChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private def ev0CoinsChars : List Char := nfe_chars_of_hex (ev 0).coins
private def ev0CoinsFast : HwBytes := hexBytes.go hexDigit ev0CoinsChars
private theorem ev0Coins_eq : (ev 0).coins = ev0CoinsFast := by
  have h1 : (ev 0).coins = hexBytes (nfe_str_of_hex (ev 0).coins) := rfl
  have h2 : (nfe_str_of_hex (ev 0).coins) = String.ofList ev0CoinsChars := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

/-- The 32 Kyber randomness bytes drawn in 4-byte chunks at offsets `32 + 4 * j` of `(ev 0).coins`. -/
def ev0KyberEnt : HwBytes :=
  (List.range 32).map fun j => ((ev 0).coins.drop (32 + 4 * j)).headD 0#8

private def ev0KyberEntFast : HwBytes :=
  (List.range 32).map fun j => (ev0CoinsFast.drop (32 + 4 * j)).headD 0#8

private theorem ev0KyberEnt_eq : ev0KyberEnt = ev0KyberEntFast := by
  unfold ev0KyberEnt ev0KyberEntFast
  rw [ev0Coins_eq]

theorem ev0_cmd_and_exit :
    (ev 0).party = "alice" ∧
    (ev 0).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" ∧
    (ev 0).exit = some (0, []) ∧
    runWrapped (ev 0) = true := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change some (0, hexBytes "") = some (0, [])
    rw [show ("" : String) = String.ofList [] from rfl, hexBytes_ofList]
    rfl
  · unfold runWrapped
    have hcmd : (ev 0).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" := rfl
    rw [hcmd, ev0In_eq]
    decide +kernel

theorem ev0_bundle_slices :
    (ev 0).input.length = preKeyBundleByteLength ∧
    ((ev 0).input)[4]? = some 0#8 ∧
    nextBundleIds none (ev 0) = some (none, 7#32, 9#32) ∧
    slice (ev 0).input 46 33 = ecKey (evictedPubOfIdx ⟨2, by decide⟩) ∧
    slice (ev 0).input 79 64 = w0.spkSig ∧
    slice (ev 0).input 147 1569 = kyberKey w0.kyberPk ∧
    slice (ev 0).input 1716 64 = w0.kyberPkSig ∧
    slice (ev 0).input 1780 33 = ecKey (evictedPubOfIdx ⟨1, by decide⟩) := by
  have hcmd : (ev 0).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · unfold nextBundleIds; rw [hcmd, ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel

theorem ev0_coins_facts :
    (ev 0).coins.length = 192 ∧
    evictedSecretIdx (clamp (slice (ev 0).coins 0 32)) = some ⟨3, by decide⟩ ∧
    evictedSecretIdx (clamp (slice (ev 0).coins 160 32)) = some ⟨4, by decide⟩ ∧
    ev0KyberEnt.length = 32 ∧
    (compKyberEncaps ev0KyberEnt).take 1568 = w0.kyberCts.headD [] ∧
    (∀ j < 32, ev0KyberEnt[j]? = ((ev 0).coins.drop (32 + 4 * j)).head?) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ev0Coins_eq]; decide +kernel
  · rw [ev0Coins_eq]; decide +kernel
  · rw [ev0Coins_eq]; decide +kernel
  · rw [ev0KyberEnt_eq]; decide +kernel
  · rw [ev0KyberEnt_eq]; decide +kernel
  · intro j hj
    rw [ev0KyberEnt_eq, ev0Coins_eq]
    revert hj
    match j with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 =>
      intro _; decide +kernel
    | n + 32 => intro h; omega

/-- Maps send index `s ∈ 0..11` to its call index in `trace0` (`1, 2, 4, 6, ..., 22`). -/
def sendCallOf (s : Nat) : Nat :=
  if s = 0 then 1 else if s = 1 then 2 else 2 * s

private theorem hexBytes_go_length :
    ∀ cs : List Char, (hexBytes.go hexDigit cs).length = cs.length / 2
  | [] => by simp [hexBytes.go]
  | [_] => by simp [hexBytes.go]
  | a :: b :: rest => by
    simp only [hexBytes.go, List.length_cons, hexBytes_go_length rest]
    omega

theorem send_coins_ge_64 {s : Nat} (hs : s < 12) :
    64 ≤ (ev (sendCallOf s)).coins.length := by
  have h1 : ∀ k ∈ ([1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22] : List Nat),
      64 ≤ (ev k).coins.length := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show (ev 1).coins = hexBytes (nfe_str_of_hex (ev 1).coins) from rfl,
          show (nfe_str_of_hex (ev 1).coins) = String.ofList (nfe_chars_of_hex (ev 1).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 2).coins = hexBytes (nfe_str_of_hex (ev 2).coins) from rfl,
          show (nfe_str_of_hex (ev 2).coins) = String.ofList (nfe_chars_of_hex (ev 2).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 4).coins = hexBytes (nfe_str_of_hex (ev 4).coins) from rfl,
          show (nfe_str_of_hex (ev 4).coins) = String.ofList (nfe_chars_of_hex (ev 4).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 6).coins = hexBytes (nfe_str_of_hex (ev 6).coins) from rfl,
          show (nfe_str_of_hex (ev 6).coins) = String.ofList (nfe_chars_of_hex (ev 6).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 8).coins = hexBytes (nfe_str_of_hex (ev 8).coins) from rfl,
          show (nfe_str_of_hex (ev 8).coins) = String.ofList (nfe_chars_of_hex (ev 8).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 10).coins = hexBytes (nfe_str_of_hex (ev 10).coins) from rfl,
          show (nfe_str_of_hex (ev 10).coins) = String.ofList (nfe_chars_of_hex (ev 10).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 12).coins = hexBytes (nfe_str_of_hex (ev 12).coins) from rfl,
          show (nfe_str_of_hex (ev 12).coins) = String.ofList (nfe_chars_of_hex (ev 12).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 14).coins = hexBytes (nfe_str_of_hex (ev 14).coins) from rfl,
          show (nfe_str_of_hex (ev 14).coins) = String.ofList (nfe_chars_of_hex (ev 14).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 16).coins = hexBytes (nfe_str_of_hex (ev 16).coins) from rfl,
          show (nfe_str_of_hex (ev 16).coins) = String.ofList (nfe_chars_of_hex (ev 16).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 18).coins = hexBytes (nfe_str_of_hex (ev 18).coins) from rfl,
          show (nfe_str_of_hex (ev 18).coins) = String.ofList (nfe_chars_of_hex (ev 18).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 20).coins = hexBytes (nfe_str_of_hex (ev 20).coins) from rfl,
          show (nfe_str_of_hex (ev 20).coins) = String.ofList (nfe_chars_of_hex (ev 20).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 22).coins = hexBytes (nfe_str_of_hex (ev 22).coins) from rfl,
          show (nfe_str_of_hex (ev 22).coins) = String.ofList (nfe_chars_of_hex (ev 22).coins) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
  apply h1
  revert hs
  match s with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => intro _; decide
  | n + 12 => intro h; omega

theorem send_input_len_lt_16 {s : Nat} (hs : s < 12) :
    (ev (sendCallOf s)).input.length < 16 := by
  have h1 : ∀ k ∈ ([1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22] : List Nat),
      (ev k).input.length < 16 := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show (ev 1).input = hexBytes (nfe_str_of_hex (ev 1).input) from rfl,
          show (nfe_str_of_hex (ev 1).input) = String.ofList (nfe_chars_of_hex (ev 1).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 2).input = hexBytes (nfe_str_of_hex (ev 2).input) from rfl,
          show (nfe_str_of_hex (ev 2).input) = String.ofList (nfe_chars_of_hex (ev 2).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 4).input = hexBytes (nfe_str_of_hex (ev 4).input) from rfl,
          show (nfe_str_of_hex (ev 4).input) = String.ofList (nfe_chars_of_hex (ev 4).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 6).input = hexBytes (nfe_str_of_hex (ev 6).input) from rfl,
          show (nfe_str_of_hex (ev 6).input) = String.ofList (nfe_chars_of_hex (ev 6).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 8).input = hexBytes (nfe_str_of_hex (ev 8).input) from rfl,
          show (nfe_str_of_hex (ev 8).input) = String.ofList (nfe_chars_of_hex (ev 8).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 10).input = hexBytes (nfe_str_of_hex (ev 10).input) from rfl,
          show (nfe_str_of_hex (ev 10).input) = String.ofList (nfe_chars_of_hex (ev 10).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 12).input = hexBytes (nfe_str_of_hex (ev 12).input) from rfl,
          show (nfe_str_of_hex (ev 12).input) = String.ofList (nfe_chars_of_hex (ev 12).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 14).input = hexBytes (nfe_str_of_hex (ev 14).input) from rfl,
          show (nfe_str_of_hex (ev 14).input) = String.ofList (nfe_chars_of_hex (ev 14).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 16).input = hexBytes (nfe_str_of_hex (ev 16).input) from rfl,
          show (nfe_str_of_hex (ev 16).input) = String.ofList (nfe_chars_of_hex (ev 16).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 18).input = hexBytes (nfe_str_of_hex (ev 18).input) from rfl,
          show (nfe_str_of_hex (ev 18).input) = String.ofList (nfe_chars_of_hex (ev 18).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 20).input = hexBytes (nfe_str_of_hex (ev 20).input) from rfl,
          show (nfe_str_of_hex (ev 20).input) = String.ofList (nfe_chars_of_hex (ev 20).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
    · rw [show (ev 22).input = hexBytes (nfe_str_of_hex (ev 22).input) from rfl,
          show (nfe_str_of_hex (ev 22).input) = String.ofList (nfe_chars_of_hex (ev 22).input) from rfl,
          hexBytes_ofList, hexBytes_go_length]; decide
  apply h1
  revert hs
  match s with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => intro _; decide
  | n + 12 => intro h; omega

theorem send_runWrapped_prekey :
    runWrapped (ev 1) = true ∧ runWrapped (ev 2) = true := by
  constructor
  · unfold runWrapped
    have hcmd : (ev 1).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
    have hex : (ev 1).exit = some (0, hexBytes (nfe_str_of_hex (ev 24).input)) := rfl
    rw [hcmd, hex,
        show (nfe_str_of_hex (ev 24).input) = String.ofList (nfe_chars_of_hex (ev 24).input) from rfl,
        hexBytes_ofList]
    decide +kernel
  · unfold runWrapped
    have hcmd : (ev 2).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
    have hex : (ev 2).exit = some (0, hexBytes (nfe_str_of_hex (ev 3).input)) := rfl
    rw [hcmd, hex,
        show (nfe_str_of_hex (ev 3).input) = String.ofList (nfe_chars_of_hex (ev 3).input) from rfl,
        hexBytes_ofList]
    decide +kernel

theorem send_runWrapped_whisper {s : Nat} (hs2 : 2 ≤ s) (hs12 : s < 12) :
    runWrapped (ev (sendCallOf s)) = false := by
  have h1 : ∀ k ∈ ([4, 6, 8, 10, 12, 14, 16, 18, 20, 22] : List Nat),
      runWrapped (ev k) = false := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · unfold runWrapped
      have hcmd : (ev 4).cmd = .send ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
      have hex : (ev 4).exit = some (0, hexBytes (nfe_str_of_hex (ev 5).input)) := rfl
      rw [hcmd, hex, show (nfe_str_of_hex (ev 5).input) = String.ofList (nfe_chars_of_hex (ev 5).input) from rfl, hexBytes_ofList]
      decide +kernel
    · unfold runWrapped
      have hcmd : (ev 6).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
      have hex : (ev 6).exit = some (0, hexBytes (nfe_str_of_hex (ev 7).input)) := rfl
      rw [hcmd, hex, show (nfe_str_of_hex (ev 7).input) = String.ofList (nfe_chars_of_hex (ev 7).input) from rfl, hexBytes_ofList]
      decide +kernel
    · unfold runWrapped
      have hcmd : (ev 8).cmd = .send ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
      have hex : (ev 8).exit = some (0, hexBytes (nfe_str_of_hex (ev 9).input)) := rfl
      rw [hcmd, hex, show (nfe_str_of_hex (ev 9).input) = String.ofList (nfe_chars_of_hex (ev 9).input) from rfl, hexBytes_ofList]
      decide +kernel
    · unfold runWrapped
      have hcmd : (ev 10).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
      have hex : (ev 10).exit = some (0, hexBytes (nfe_str_of_hex (ev 11).input)) := rfl
      rw [hcmd, hex, show (nfe_str_of_hex (ev 11).input) = String.ofList (nfe_chars_of_hex (ev 11).input) from rfl, hexBytes_ofList]
      decide +kernel
    · unfold runWrapped
      have hcmd : (ev 12).cmd = .send ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
      have hex : (ev 12).exit = some (0, hexBytes (nfe_str_of_hex (ev 13).input)) := rfl
      rw [hcmd, hex, show (nfe_str_of_hex (ev 13).input) = String.ofList (nfe_chars_of_hex (ev 13).input) from rfl, hexBytes_ofList]
      decide +kernel
    · unfold runWrapped
      have hcmd : (ev 14).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
      have hex : (ev 14).exit = some (0, hexBytes (nfe_str_of_hex (ev 15).input)) := rfl
      rw [hcmd, hex, show (nfe_str_of_hex (ev 15).input) = String.ofList (nfe_chars_of_hex (ev 15).input) from rfl, hexBytes_ofList]
      decide +kernel
    · unfold runWrapped
      have hcmd : (ev 16).cmd = .send ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
      have hex : (ev 16).exit = some (0, hexBytes (nfe_str_of_hex (ev 17).input)) := rfl
      rw [hcmd, hex, show (nfe_str_of_hex (ev 17).input) = String.ofList (nfe_chars_of_hex (ev 17).input) from rfl, hexBytes_ofList]
      decide +kernel
    · unfold runWrapped
      have hcmd : (ev 18).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
      have hex : (ev 18).exit = some (0, hexBytes (nfe_str_of_hex (ev 19).input)) := rfl
      rw [hcmd, hex, show (nfe_str_of_hex (ev 19).input) = String.ofList (nfe_chars_of_hex (ev 19).input) from rfl, hexBytes_ofList]
      decide +kernel
    · unfold runWrapped
      have hcmd : (ev 20).cmd = .send ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
      have hex : (ev 20).exit = some (0, hexBytes (nfe_str_of_hex (ev 21).input)) := rfl
      rw [hcmd, hex, show (nfe_str_of_hex (ev 21).input) = String.ofList (nfe_chars_of_hex (ev 21).input) from rfl, hexBytes_ofList]
      decide +kernel
    · unfold runWrapped
      have hcmd : (ev 22).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
      have hex : (ev 22).exit = some (0, hexBytes (nfe_str_of_hex (ev 23).input)) := rfl
      rw [hcmd, hex, show (nfe_str_of_hex (ev 23).input) = String.ofList (nfe_chars_of_hex (ev 23).input) from rfl, hexBytes_ofList]
      decide +kernel
  apply h1
  revert hs2 hs12
  match s with
  | 0 | 1 => intro h _; omega
  | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => intro _ _; decide
  | n + 12 => intro _ h; omega

theorem nextBundleIds_non_init {k : Nat} (hk0 : k ≠ 0) (hk25 : k < 25)
    (cur : Option BundlePreKeyIds) :
    nextBundleIds cur (ev k) = cur := by
  unfold nextBundleIds
  match k with
  | 0 => exact absurd rfl hk0
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12
  | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 => rfl
  | n + 25 => omega

private def ev5InFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (ev 5).input)
private theorem ev5In_eq : (ev 5).input = ev5InFast := by
  rw [show (ev 5).input = hexBytes (nfe_str_of_hex (ev 5).input) from rfl,
      show (nfe_str_of_hex (ev 5).input) = String.ofList (nfe_chars_of_hex (ev 5).input) from rfl,
      hexBytes_ofList]
  rfl

private def ev9InFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (ev 9).input)
private theorem ev9In_eq : (ev 9).input = ev9InFast := by
  rw [show (ev 9).input = hexBytes (nfe_str_of_hex (ev 9).input) from rfl,
      show (nfe_str_of_hex (ev 9).input) = String.ofList (nfe_chars_of_hex (ev 9).input) from rfl,
      hexBytes_ofList]
  rfl

private def ev13InFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (ev 13).input)
private theorem ev13In_eq : (ev 13).input = ev13InFast := by
  rw [show (ev 13).input = hexBytes (nfe_str_of_hex (ev 13).input) from rfl,
      show (nfe_str_of_hex (ev 13).input) = String.ofList (nfe_chars_of_hex (ev 13).input) from rfl,
      hexBytes_ofList]
  rfl

private def ev17InFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (ev 17).input)
private theorem ev17In_eq : (ev 17).input = ev17InFast := by
  rw [show (ev 17).input = hexBytes (nfe_str_of_hex (ev 17).input) from rfl,
      show (nfe_str_of_hex (ev 17).input) = String.ofList (nfe_chars_of_hex (ev 17).input) from rfl,
      hexBytes_ofList]
  rfl

private def ev21InFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (ev 21).input)
private theorem ev21In_eq : (ev 21).input = ev21InFast := by
  rw [show (ev 21).input = hexBytes (nfe_str_of_hex (ev 21).input) from rfl,
      show (nfe_str_of_hex (ev 21).input) = String.ofList (nfe_chars_of_hex (ev 21).input) from rfl,
      hexBytes_ofList]
  rfl

private def checkWhisperFast' (b : HwBytes) (pkIdx : Fin 16) : Bool :=
  match b with
  | tag :: body =>
    tag == wireWhisperTag &&
    match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body with
    | .ok m => m.senderRatchetKey.bytes.toList == evictedPubOfIdx pkIdx && m.counter.toNat == 0
    | .error _ => false
  | [] => false

private theorem whisperInputSpec_of_check' {e : RunEvent} {fast : HwBytes} {pkIdx : Fin 16}
    (hcmd : ∃ peer, e.cmd = .recv peer)
    (heq : e.input = fast)
    (hc : checkWhisperFast' fast pkIdx = true) :
    WhisperInputSpec e pkIdx := by
  unfold checkWhisperFast' at hc
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

theorem ev5_whisper : WhisperInputSpec (ev 5) ⟨5, by decide⟩ :=
  whisperInputSpec_of_check' ⟨_, rfl⟩ ev5In_eq (by decide +kernel)

theorem ev9_whisper : WhisperInputSpec (ev 9) ⟨7, by decide⟩ :=
  whisperInputSpec_of_check' ⟨_, rfl⟩ ev9In_eq (by decide +kernel)

theorem ev13_whisper : WhisperInputSpec (ev 13) ⟨9, by decide⟩ :=
  whisperInputSpec_of_check' ⟨_, rfl⟩ ev13In_eq (by decide +kernel)

theorem ev17_whisper : WhisperInputSpec (ev 17) ⟨11, by decide⟩ :=
  whisperInputSpec_of_check' ⟨_, rfl⟩ ev17In_eq (by decide +kernel)

theorem ev21_whisper : WhisperInputSpec (ev 21) ⟨13, by decide⟩ :=
  whisperInputSpec_of_check' ⟨_, rfl⟩ ev21In_eq (by decide +kernel)

theorem ev5_coins_idx :
    evictedSecretIdx (clamp (((ev 5).coins).take 32)) = some ⟨6, by decide⟩ := by
  rw [show (ev 5).coins = hexBytes (nfe_str_of_hex (ev 5).coins) from rfl,
      show (nfe_str_of_hex (ev 5).coins) = String.ofList (nfe_chars_of_hex (ev 5).coins) from rfl,
      hexBytes_ofList]
  decide +kernel

theorem ev9_coins_idx :
    evictedSecretIdx (clamp (((ev 9).coins).take 32)) = some ⟨8, by decide⟩ := by
  rw [show (ev 9).coins = hexBytes (nfe_str_of_hex (ev 9).coins) from rfl,
      show (nfe_str_of_hex (ev 9).coins) = String.ofList (nfe_chars_of_hex (ev 9).coins) from rfl,
      hexBytes_ofList]
  decide +kernel

theorem ev13_coins_idx :
    evictedSecretIdx (clamp (((ev 13).coins).take 32)) = some ⟨10, by decide⟩ := by
  rw [show (ev 13).coins = hexBytes (nfe_str_of_hex (ev 13).coins) from rfl,
      show (nfe_str_of_hex (ev 13).coins) = String.ofList (nfe_chars_of_hex (ev 13).coins) from rfl,
      hexBytes_ofList]
  decide +kernel

theorem ev17_coins_idx :
    evictedSecretIdx (clamp (((ev 17).coins).take 32)) = some ⟨12, by decide⟩ := by
  rw [show (ev 17).coins = hexBytes (nfe_str_of_hex (ev 17).coins) from rfl,
      show (nfe_str_of_hex (ev 17).coins) = String.ofList (nfe_chars_of_hex (ev 17).coins) from rfl,
      hexBytes_ofList]
  decide +kernel

theorem ev21_coins_idx :
    evictedSecretIdx (clamp (((ev 21).coins).take 32)) = some ⟨14, by decide⟩ := by
  rw [show (ev 21).coins = hexBytes (nfe_str_of_hex (ev 21).coins) from rfl,
      show (nfe_str_of_hex (ev 21).coins) = String.ofList (nfe_chars_of_hex (ev 21).coins) from rfl,
      hexBytes_ofList]
  decide +kernel

theorem active_recv_coins_ge_32 {k : Nat}
    (hk : k ∈ recvCallIndices) (hne24 : k ≠ 24) :
    32 ≤ (ev k).coins.length := by
  simp only [recvCallIndices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show (ev 3).coins = hexBytes (nfe_str_of_hex (ev 3).coins) from rfl,
        show (nfe_str_of_hex (ev 3).coins) = String.ofList (nfe_chars_of_hex (ev 3).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  · rw [show (ev 5).coins = hexBytes (nfe_str_of_hex (ev 5).coins) from rfl,
        show (nfe_str_of_hex (ev 5).coins) = String.ofList (nfe_chars_of_hex (ev 5).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  · rw [show (ev 7).coins = hexBytes (nfe_str_of_hex (ev 7).coins) from rfl,
        show (nfe_str_of_hex (ev 7).coins) = String.ofList (nfe_chars_of_hex (ev 7).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  · rw [show (ev 9).coins = hexBytes (nfe_str_of_hex (ev 9).coins) from rfl,
        show (nfe_str_of_hex (ev 9).coins) = String.ofList (nfe_chars_of_hex (ev 9).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  · rw [show (ev 11).coins = hexBytes (nfe_str_of_hex (ev 11).coins) from rfl,
        show (nfe_str_of_hex (ev 11).coins) = String.ofList (nfe_chars_of_hex (ev 11).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  · rw [show (ev 13).coins = hexBytes (nfe_str_of_hex (ev 13).coins) from rfl,
        show (nfe_str_of_hex (ev 13).coins) = String.ofList (nfe_chars_of_hex (ev 13).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  · rw [show (ev 15).coins = hexBytes (nfe_str_of_hex (ev 15).coins) from rfl,
        show (nfe_str_of_hex (ev 15).coins) = String.ofList (nfe_chars_of_hex (ev 15).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  · rw [show (ev 17).coins = hexBytes (nfe_str_of_hex (ev 17).coins) from rfl,
        show (nfe_str_of_hex (ev 17).coins) = String.ofList (nfe_chars_of_hex (ev 17).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  · rw [show (ev 19).coins = hexBytes (nfe_str_of_hex (ev 19).coins) from rfl,
        show (nfe_str_of_hex (ev 19).coins) = String.ofList (nfe_chars_of_hex (ev 19).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  · rw [show (ev 21).coins = hexBytes (nfe_str_of_hex (ev 21).coins) from rfl,
        show (nfe_str_of_hex (ev 21).coins) = String.ofList (nfe_chars_of_hex (ev 21).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  · rw [show (ev 23).coins = hexBytes (nfe_str_of_hex (ev 23).coins) from rfl,
        show (nfe_str_of_hex (ev 23).coins) = String.ofList (nfe_chars_of_hex (ev 23).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  · exact absurd rfl hne24

private def ev3InFast' : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (ev 3).input)
private theorem ev3In_eq' : (ev 3).input = ev3InFast' := by
  rw [show (ev 3).input = hexBytes (nfe_str_of_hex (ev 3).input) from rfl,
      show (nfe_str_of_hex (ev 3).input) = String.ofList (nfe_chars_of_hex (ev 3).input) from rfl,
      hexBytes_ofList]
  rfl

private theorem ev3_full_check :
    ((parsePreKeyWire ev3InFast').map fun p =>
      (p.version == 4#8 &&
       p.signedPreKeyId == 7 &&
       p.preKeyId == none &&
       p.kyberPreKeyId == some 9 &&
       p.kyberCiphertext == some (kyberKey (w0.kyberCts.headD [])) &&
       p.baseKey == ecKey (evictedPubOfIdx ⟨3, by decide⟩) &&
       p.identityKey == ecKey (evictedPubOfIdx ⟨0, by decide⟩) &&
       p.inner.senderRatchetKey.bytes.toList == evictedPubOfIdx ⟨4, by decide⟩ &&
       p.inner.counter.toNat == 1 &&
       p.inner.previousCounter.toNat == 0 &&
       (p.message.drop (p.message.length - 8)).take 4 != compTag4)) = some true := by
  decide +kernel

theorem ev3_full_fields {p : PreKeyFields} (hp : parsePreKeyWire (ev 3).input = some p) :
    p.version = 4#8 ∧
    p.signedPreKeyId = 7 ∧
    p.preKeyId = none ∧
    p.kyberPreKeyId = some 9 ∧
    p.kyberCiphertext = some (kyberKey (w0.kyberCts.headD [])) ∧
    p.baseKey = ecKey (evictedPubOfIdx ⟨3, by decide⟩) ∧
    p.identityKey = ecKey (evictedPubOfIdx ⟨0, by decide⟩) ∧
    p.inner.senderRatchetKey.bytes.toList = evictedPubOfIdx ⟨4, by decide⟩ ∧
    p.inner.counter.toNat = 1 ∧
    p.inner.previousCounter.toNat = 0 ∧
    (p.message.drop (p.message.length - 8)).take 4 ≠ compTag4 := by
  have hc := ev3_full_check
  rw [← ev3In_eq', hp, Option.map_some, Option.some.injEq] at hc
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hc
  exact ⟨hc.1.1.1.1.1.1.1.1.1.1, hc.1.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.1.2,
    hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2, hc.1.1.1.1.1.2, hc.1.1.1.1.2,
    hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

theorem not_kyberMismatch_ev3 {r : ProtocolSetup} {p : PreKeyFields}
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hp : parsePreKeyWire (ev 3).input = some p) :
    ¬ KyberMismatch evictedI0 r p := by
  have hct := (ev3_full_fields hp).2.2.2.2.1
  have hkyber := hfit.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rintro ⟨e, ct, ss, helen, hpct, henc, hndec⟩
  rw [hct] at hpct
  injection hpct with hkk
  have hct_eq : ct = w0.kyberCts.headD [] := by
    unfold kyberKey at hkk
    exact (List.cons.inj hkk).2.symm
  subst hct_eq
  have hmem : w0.kyberCts.headD [] ∈ w0.kyberCts := List.mem_of_getElem? (rfl : w0.kyberCts[0]? = _)
  exact hndec (hkyber _ hmem e ss helen henc)

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvCleanRunParse

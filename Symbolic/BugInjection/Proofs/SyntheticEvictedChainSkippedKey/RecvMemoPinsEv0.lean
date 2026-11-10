/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Lean
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse

/-!
# Concrete `RunEvent` Byte Facts for Calls `0` and `1`

Defines shared plaintext and DAG node index tables for the clean schedule and proves kernel-checked
input, coin-draw, and stdout byte facts for `ev 0` and `ev 1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
  (bundlePreKeyIds nextBundleIds preKeyWire ecKey pubBytes runWrapped)
open Symbolic.BugInjection (hexBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0 (evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (w0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev hexDigit hexBytes_ofList)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData (dagBytes)

theorem w0_aliceId_eq : w0.aliceId = dagBytes 21 := by decide +kernel

def aliceBobAddrBytes : HwBytes := [0x00#8, 0x8a#8, 0x6f#8, 0x1c#8, 0x2e#8, 0x3b#8, 0x4d#8, 0x4e#8, 0x5f#8, 0x9a#8, 0x0b#8, 0x1c#8, 0x2d#8, 0x3e#8, 0x4f#8, 0x5a#8, 0x6b#8, 0x01#8, 0x00#8, 0x5d#8, 0x3e#8, 0x2f#8, 0x10#8, 0x7a#8, 0x8b#8, 0x4c#8, 0x9d#8, 0x8e#8, 0x0f#8, 0xa1#8, 0xb2#8, 0xc3#8, 0xd4#8, 0xe5#8, 0xf6#8, 0x01#8]

theorem serializeAddresses_alice_bob_eq :
    DY.Libsignal.Composed.Refinement.Cli.serializeAddresses
      ⟨DY.Libsignal.Composed.Refinement.Cli.aliceUuid, 1⟩
      ⟨DY.Libsignal.Composed.Refinement.Cli.bobUuid, 1⟩ = aliceBobAddrBytes := by
  decide +kernel

def sendPtTs (j : Nat) : Nat :=
  if j = 0 then 31 else if j = 1 then 38 else 55 + 14 * (j - 2)

def sendPtBytesList : List HwBytes := [
  [0x73#8, 0x6b#8, 0x69#8, 0x70#8, 0x2d#8, 0x30#8],
  [0x69#8, 0x6e#8, 0x69#8, 0x74#8, 0x2d#8, 0x31#8],
  [0x62#8, 0x30#8],
  [0x61#8, 0x31#8],
  [0x62#8, 0x31#8],
  [0x61#8, 0x32#8],
  [0x62#8, 0x32#8],
  [0x61#8, 0x33#8],
  [0x62#8, 0x33#8],
  [0x61#8, 0x34#8],
  [0x62#8, 0x34#8],
  [0x61#8, 0x35#8]
]

def sendPtBytes (j : Nat) : HwBytes := sendPtBytesList[j]?.getD []
def sendC32IdList : List Nat := [102, 122, 167, 260, 416, 651, 981, 1422, 1990, 2701, 3571, 4616]
def sendC64IdList : List Nat := [103, 123, 168, 261, 417, 652, 982, 1423, 1991, 2702, 3572, 4617]
def sendWmacIdList : List Nat := [118, 138, 183, 276, 432, 667, 997, 1438, 2006, 2717, 3587, 4632]
def sendC32Id (j : Nat) : Nat := sendC32IdList[j]?.getD 0
def sendC64Id (j : Nat) : Nat := sendC64IdList[j]?.getD 0
def sendWmacId (j : Nat) : Nat := sendWmacIdList[j]?.getD 0

def recvDhsTs (m : Nat) : Nat := if m = 0 then 45 else 62 + 14 * (m - 1)
def recvSkIdList : List Nat := [156, 249, 405, 640, 970, 1411, 1979, 2690, 3560, 4605, 5841]
def recvSkId (m : Nat) : Nat := recvSkIdList[m]?.getD 0

theorem sendPtBytes_len_lt8 {j : Nat} (hj : j < 12) : (sendPtBytes j).length < 8 := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
      j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

open DY.Libsignal.HwEvents (RunEvent)

attribute [local irreducible] Symbolic.BugInjection.hexBytes

local elab "nfe_exit_str" k:term : term => do
  let e ← Lean.Elab.Term.elabTerm (← `(RunEvent.exit (ev $k))) none
  let someVal ← Lean.Meta.whnf e
  let prodVal ← Lean.Meta.whnf someVal.getAppArgs[1]!
  let sndVal ← Lean.Meta.whnf prodVal.getAppArgs[3]!
  Lean.Meta.whnf sndVal.getAppArgs[0]!

local elab "nfe_exit_chars" k:term : term => do
  let e ← Lean.Elab.Term.elabTerm (← `(RunEvent.exit (ev $k))) none
  let someVal ← Lean.Meta.whnf e
  let prodVal ← Lean.Meta.whnf someVal.getAppArgs[1]!
  let sndVal ← Lean.Meta.whnf prodVal.getAppArgs[3]!
  let sLit ← Lean.Meta.whnf sndVal.getAppArgs[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

def ev0InC : List Char := nfe_chars_of_hex ((ev 0).input)
def ev0InF : HwBytes := hexBytes.go hexDigit ev0InC
theorem ev0In_eq : ((ev 0).input) = ev0InF := by
  have h1 : ((ev 0).input) = hexBytes (nfe_str_of_hex ((ev 0).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 0).input)) = String.ofList ev0InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev1InC : List Char := nfe_chars_of_hex ((ev 1).input)
private def ev1InF : HwBytes := hexBytes.go hexDigit ev1InC
private theorem ev1In_eq : ((ev 1).input) = ev1InF := by
  have h1 : ((ev 1).input) = hexBytes (nfe_str_of_hex ((ev 1).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 1).input)) = String.ofList ev1InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev1CoinsC : List Char := nfe_chars_of_hex ((ev 1).coins)
private def ev1CoinsF : HwBytes := hexBytes.go hexDigit ev1CoinsC
private theorem ev1Coins_eq : ((ev 1).coins) = ev1CoinsF := by
  have h1 : ((ev 1).coins) = hexBytes (nfe_str_of_hex ((ev 1).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 1).coins)) = String.ofList ev1CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev1OutC : List Char := nfe_exit_chars 1
def ev1OutF : HwBytes := hexBytes.go hexDigit ev1OutC
theorem ev1Out_exit_eq : (ev 1).exit = some (0, ev1OutF) := by
  have h1 : (ev 1).exit = some (0, hexBytes (nfe_exit_str 1)) := rfl
  have h2 : (nfe_exit_str 1) = String.ofList ev1OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private theorem ev1_fast_ok :
    (ev1OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = true ∧
    (let (pkId, spkId, kpkId) := bundlePreKeyIds ev0InF
     ev1OutF = preKeyWire pkId spkId kpkId w0.regIdA
       (ecKey (pubBytes evictedI0 (dagBytes 21))) (dagBytes 68) (dagBytes 73) (dagBytes 118) ∧
     ev1OutF.length < 2048) ∧
    ev1InF = sendPtBytes 0 ∧
    ev1CoinsF.take 32 = dagBytes 102 ∧
    ev1CoinsF.take 64 = dagBytes 103 := by
  decide +kernel

theorem ev1_preKeySend_facts :
    (∃ p, (ev 1).cmd = .send p) ∧
    (ev 1).exit = some (0, ev1OutF) ∧
    runWrapped (ev 1) = true ∧
    (let (pkId, spkId, kpkId) := bundlePreKeyIds (ev 0).input
     ev1OutF = preKeyWire pkId spkId kpkId w0.regIdA
       (ecKey (pubBytes evictedI0 w0.aliceId)) (dagBytes 68) (dagBytes 73) (dagBytes 118) ∧
     ev1OutF.length < 2048) ∧
    (ev 1).input = sendPtBytes 0 ∧
    (ev 1).coins.take 32 = dagBytes 102 ∧
    (ev 1).coins.take 64 = dagBytes 103 ∧
    nextBundleIds (some (bundlePreKeyIds (ev 0).input)) (ev 1) =
      some (bundlePreKeyIds (ev 0).input) := by
  obtain ⟨hw, hwire, hin, hc32, hc64⟩ := ev1_fast_ok
  have hp : ∃ p, (ev 1).cmd = .send p := ⟨_, rfl⟩
  refine ⟨hp, ev1Out_exit_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hpc⟩ := hp; unfold runWrapped; rw [hpc, ev1Out_exit_eq]; exact hw
  · rw [ev0In_eq, w0_aliceId_eq]; exact hwire
  · rw [ev1In_eq]; exact hin
  · rw [ev1Coins_eq]; exact hc32
  · rw [ev1Coins_eq]; exact hc64
  · obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0

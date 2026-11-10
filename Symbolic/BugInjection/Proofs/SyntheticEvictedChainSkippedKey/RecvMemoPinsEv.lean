/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Lean
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0

/-!
# Concrete `RunEvent` Byte Facts for Calls `2..23`

Kernel-checked input, coin-draw, and stdout byte facts for the clean prefix calls `ev 2 .. ev 23`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv

open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent)
open DY.Libsignal.Composed.Refinement
  (bundlePreKeyIds nextBundleIds preKeyWire ecKey pubBytes runWrapped)
open Symbolic.BugInjection (hexBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0 (evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (w0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.NfeParse
  (ev hexDigit hexBytes_ofList)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData (dagBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0
  (w0_aliceId_eq ev0InF ev0In_eq)

export Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0
  (w0_aliceId_eq aliceBobAddrBytes serializeAddresses_alice_bob_eq sendPtTs sendPtBytes
   sendC32Id sendC64Id sendWmacId recvDhsTs recvSkId sendPtBytes_len_lt8 ev1_preKeySend_facts)

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

private def ev2InC : List Char := nfe_chars_of_hex ((ev 2).input)
private def ev2InF : HwBytes := hexBytes.go hexDigit ev2InC
private theorem ev2In_eq : ((ev 2).input) = ev2InF := by
  have h1 : ((ev 2).input) = hexBytes (nfe_str_of_hex ((ev 2).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 2).input)) = String.ofList ev2InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev2CoinsC : List Char := nfe_chars_of_hex ((ev 2).coins)
private def ev2CoinsF : HwBytes := hexBytes.go hexDigit ev2CoinsC
private theorem ev2Coins_eq : ((ev 2).coins) = ev2CoinsF := by
  have h1 : ((ev 2).coins) = hexBytes (nfe_str_of_hex ((ev 2).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 2).coins)) = String.ofList ev2CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev2OutC : List Char := nfe_exit_chars 2
def ev2OutF : HwBytes := hexBytes.go hexDigit ev2OutC
theorem ev2Out_exit_eq : (ev 2).exit = some (0, ev2OutF) := by
  have h1 : (ev 2).exit = some (0, hexBytes (nfe_exit_str 2)) := rfl
  have h2 : (nfe_exit_str 2) = String.ofList ev2OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev4InC : List Char := nfe_chars_of_hex ((ev 4).input)
private def ev4InF : HwBytes := hexBytes.go hexDigit ev4InC
private theorem ev4In_eq : ((ev 4).input) = ev4InF := by
  have h1 : ((ev 4).input) = hexBytes (nfe_str_of_hex ((ev 4).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 4).input)) = String.ofList ev4InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev4CoinsC : List Char := nfe_chars_of_hex ((ev 4).coins)
private def ev4CoinsF : HwBytes := hexBytes.go hexDigit ev4CoinsC
private theorem ev4Coins_eq : ((ev 4).coins) = ev4CoinsF := by
  have h1 : ((ev 4).coins) = hexBytes (nfe_str_of_hex ((ev 4).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 4).coins)) = String.ofList ev4CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev4OutC : List Char := nfe_exit_chars 4
def ev4OutF : HwBytes := hexBytes.go hexDigit ev4OutC
theorem ev4Out_exit_eq : (ev 4).exit = some (0, ev4OutF) := by
  have h1 : (ev 4).exit = some (0, hexBytes (nfe_exit_str 4)) := rfl
  have h2 : (nfe_exit_str 4) = String.ofList ev4OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev6InC : List Char := nfe_chars_of_hex ((ev 6).input)
private def ev6InF : HwBytes := hexBytes.go hexDigit ev6InC
private theorem ev6In_eq : ((ev 6).input) = ev6InF := by
  have h1 : ((ev 6).input) = hexBytes (nfe_str_of_hex ((ev 6).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 6).input)) = String.ofList ev6InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev6CoinsC : List Char := nfe_chars_of_hex ((ev 6).coins)
private def ev6CoinsF : HwBytes := hexBytes.go hexDigit ev6CoinsC
private theorem ev6Coins_eq : ((ev 6).coins) = ev6CoinsF := by
  have h1 : ((ev 6).coins) = hexBytes (nfe_str_of_hex ((ev 6).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 6).coins)) = String.ofList ev6CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev6OutC : List Char := nfe_exit_chars 6
def ev6OutF : HwBytes := hexBytes.go hexDigit ev6OutC
theorem ev6Out_exit_eq : (ev 6).exit = some (0, ev6OutF) := by
  have h1 : (ev 6).exit = some (0, hexBytes (nfe_exit_str 6)) := rfl
  have h2 : (nfe_exit_str 6) = String.ofList ev6OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev8InC : List Char := nfe_chars_of_hex ((ev 8).input)
private def ev8InF : HwBytes := hexBytes.go hexDigit ev8InC
private theorem ev8In_eq : ((ev 8).input) = ev8InF := by
  have h1 : ((ev 8).input) = hexBytes (nfe_str_of_hex ((ev 8).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 8).input)) = String.ofList ev8InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev8CoinsC : List Char := nfe_chars_of_hex ((ev 8).coins)
private def ev8CoinsF : HwBytes := hexBytes.go hexDigit ev8CoinsC
private theorem ev8Coins_eq : ((ev 8).coins) = ev8CoinsF := by
  have h1 : ((ev 8).coins) = hexBytes (nfe_str_of_hex ((ev 8).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 8).coins)) = String.ofList ev8CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev8OutC : List Char := nfe_exit_chars 8
def ev8OutF : HwBytes := hexBytes.go hexDigit ev8OutC
theorem ev8Out_exit_eq : (ev 8).exit = some (0, ev8OutF) := by
  have h1 : (ev 8).exit = some (0, hexBytes (nfe_exit_str 8)) := rfl
  have h2 : (nfe_exit_str 8) = String.ofList ev8OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev10InC : List Char := nfe_chars_of_hex ((ev 10).input)
private def ev10InF : HwBytes := hexBytes.go hexDigit ev10InC
private theorem ev10In_eq : ((ev 10).input) = ev10InF := by
  have h1 : ((ev 10).input) = hexBytes (nfe_str_of_hex ((ev 10).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 10).input)) = String.ofList ev10InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev10CoinsC : List Char := nfe_chars_of_hex ((ev 10).coins)
private def ev10CoinsF : HwBytes := hexBytes.go hexDigit ev10CoinsC
private theorem ev10Coins_eq : ((ev 10).coins) = ev10CoinsF := by
  have h1 : ((ev 10).coins) = hexBytes (nfe_str_of_hex ((ev 10).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 10).coins)) = String.ofList ev10CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev10OutC : List Char := nfe_exit_chars 10
def ev10OutF : HwBytes := hexBytes.go hexDigit ev10OutC
theorem ev10Out_exit_eq : (ev 10).exit = some (0, ev10OutF) := by
  have h1 : (ev 10).exit = some (0, hexBytes (nfe_exit_str 10)) := rfl
  have h2 : (nfe_exit_str 10) = String.ofList ev10OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev12InC : List Char := nfe_chars_of_hex ((ev 12).input)
private def ev12InF : HwBytes := hexBytes.go hexDigit ev12InC
private theorem ev12In_eq : ((ev 12).input) = ev12InF := by
  have h1 : ((ev 12).input) = hexBytes (nfe_str_of_hex ((ev 12).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 12).input)) = String.ofList ev12InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev12CoinsC : List Char := nfe_chars_of_hex ((ev 12).coins)
private def ev12CoinsF : HwBytes := hexBytes.go hexDigit ev12CoinsC
private theorem ev12Coins_eq : ((ev 12).coins) = ev12CoinsF := by
  have h1 : ((ev 12).coins) = hexBytes (nfe_str_of_hex ((ev 12).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 12).coins)) = String.ofList ev12CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev12OutC : List Char := nfe_exit_chars 12
def ev12OutF : HwBytes := hexBytes.go hexDigit ev12OutC
theorem ev12Out_exit_eq : (ev 12).exit = some (0, ev12OutF) := by
  have h1 : (ev 12).exit = some (0, hexBytes (nfe_exit_str 12)) := rfl
  have h2 : (nfe_exit_str 12) = String.ofList ev12OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev14InC : List Char := nfe_chars_of_hex ((ev 14).input)
private def ev14InF : HwBytes := hexBytes.go hexDigit ev14InC
private theorem ev14In_eq : ((ev 14).input) = ev14InF := by
  have h1 : ((ev 14).input) = hexBytes (nfe_str_of_hex ((ev 14).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 14).input)) = String.ofList ev14InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev14CoinsC : List Char := nfe_chars_of_hex ((ev 14).coins)
private def ev14CoinsF : HwBytes := hexBytes.go hexDigit ev14CoinsC
private theorem ev14Coins_eq : ((ev 14).coins) = ev14CoinsF := by
  have h1 : ((ev 14).coins) = hexBytes (nfe_str_of_hex ((ev 14).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 14).coins)) = String.ofList ev14CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev14OutC : List Char := nfe_exit_chars 14
def ev14OutF : HwBytes := hexBytes.go hexDigit ev14OutC
theorem ev14Out_exit_eq : (ev 14).exit = some (0, ev14OutF) := by
  have h1 : (ev 14).exit = some (0, hexBytes (nfe_exit_str 14)) := rfl
  have h2 : (nfe_exit_str 14) = String.ofList ev14OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev16InC : List Char := nfe_chars_of_hex ((ev 16).input)
private def ev16InF : HwBytes := hexBytes.go hexDigit ev16InC
private theorem ev16In_eq : ((ev 16).input) = ev16InF := by
  have h1 : ((ev 16).input) = hexBytes (nfe_str_of_hex ((ev 16).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 16).input)) = String.ofList ev16InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev16CoinsC : List Char := nfe_chars_of_hex ((ev 16).coins)
private def ev16CoinsF : HwBytes := hexBytes.go hexDigit ev16CoinsC
private theorem ev16Coins_eq : ((ev 16).coins) = ev16CoinsF := by
  have h1 : ((ev 16).coins) = hexBytes (nfe_str_of_hex ((ev 16).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 16).coins)) = String.ofList ev16CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev16OutC : List Char := nfe_exit_chars 16
def ev16OutF : HwBytes := hexBytes.go hexDigit ev16OutC
theorem ev16Out_exit_eq : (ev 16).exit = some (0, ev16OutF) := by
  have h1 : (ev 16).exit = some (0, hexBytes (nfe_exit_str 16)) := rfl
  have h2 : (nfe_exit_str 16) = String.ofList ev16OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev18InC : List Char := nfe_chars_of_hex ((ev 18).input)
private def ev18InF : HwBytes := hexBytes.go hexDigit ev18InC
private theorem ev18In_eq : ((ev 18).input) = ev18InF := by
  have h1 : ((ev 18).input) = hexBytes (nfe_str_of_hex ((ev 18).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 18).input)) = String.ofList ev18InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev18CoinsC : List Char := nfe_chars_of_hex ((ev 18).coins)
private def ev18CoinsF : HwBytes := hexBytes.go hexDigit ev18CoinsC
private theorem ev18Coins_eq : ((ev 18).coins) = ev18CoinsF := by
  have h1 : ((ev 18).coins) = hexBytes (nfe_str_of_hex ((ev 18).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 18).coins)) = String.ofList ev18CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev18OutC : List Char := nfe_exit_chars 18
def ev18OutF : HwBytes := hexBytes.go hexDigit ev18OutC
theorem ev18Out_exit_eq : (ev 18).exit = some (0, ev18OutF) := by
  have h1 : (ev 18).exit = some (0, hexBytes (nfe_exit_str 18)) := rfl
  have h2 : (nfe_exit_str 18) = String.ofList ev18OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev20InC : List Char := nfe_chars_of_hex ((ev 20).input)
private def ev20InF : HwBytes := hexBytes.go hexDigit ev20InC
private theorem ev20In_eq : ((ev 20).input) = ev20InF := by
  have h1 : ((ev 20).input) = hexBytes (nfe_str_of_hex ((ev 20).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 20).input)) = String.ofList ev20InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev20CoinsC : List Char := nfe_chars_of_hex ((ev 20).coins)
private def ev20CoinsF : HwBytes := hexBytes.go hexDigit ev20CoinsC
private theorem ev20Coins_eq : ((ev 20).coins) = ev20CoinsF := by
  have h1 : ((ev 20).coins) = hexBytes (nfe_str_of_hex ((ev 20).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 20).coins)) = String.ofList ev20CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev20OutC : List Char := nfe_exit_chars 20
def ev20OutF : HwBytes := hexBytes.go hexDigit ev20OutC
theorem ev20Out_exit_eq : (ev 20).exit = some (0, ev20OutF) := by
  have h1 : (ev 20).exit = some (0, hexBytes (nfe_exit_str 20)) := rfl
  have h2 : (nfe_exit_str 20) = String.ofList ev20OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev22InC : List Char := nfe_chars_of_hex ((ev 22).input)
private def ev22InF : HwBytes := hexBytes.go hexDigit ev22InC
private theorem ev22In_eq : ((ev 22).input) = ev22InF := by
  have h1 : ((ev 22).input) = hexBytes (nfe_str_of_hex ((ev 22).input)) := rfl
  have h2 : (nfe_str_of_hex ((ev 22).input)) = String.ofList ev22InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev22CoinsC : List Char := nfe_chars_of_hex ((ev 22).coins)
private def ev22CoinsF : HwBytes := hexBytes.go hexDigit ev22CoinsC
private theorem ev22Coins_eq : ((ev 22).coins) = ev22CoinsF := by
  have h1 : ((ev 22).coins) = hexBytes (nfe_str_of_hex ((ev 22).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 22).coins)) = String.ofList ev22CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
def ev22OutC : List Char := nfe_exit_chars 22
def ev22OutF : HwBytes := hexBytes.go hexDigit ev22OutC
theorem ev22Out_exit_eq : (ev 22).exit = some (0, ev22OutF) := by
  have h1 : (ev 22).exit = some (0, hexBytes (nfe_exit_str 22)) := rfl
  have h2 : (nfe_exit_str 22) = String.ofList ev22OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev3CoinsC : List Char := nfe_chars_of_hex ((ev 3).coins)
private def ev3CoinsF : HwBytes := hexBytes.go hexDigit ev3CoinsC
private theorem ev3Coins_eq : ((ev 3).coins) = ev3CoinsF := by
  have h1 : ((ev 3).coins) = hexBytes (nfe_str_of_hex ((ev 3).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 3).coins)) = String.ofList ev3CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev5CoinsC : List Char := nfe_chars_of_hex ((ev 5).coins)
private def ev5CoinsF : HwBytes := hexBytes.go hexDigit ev5CoinsC
private theorem ev5Coins_eq : ((ev 5).coins) = ev5CoinsF := by
  have h1 : ((ev 5).coins) = hexBytes (nfe_str_of_hex ((ev 5).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 5).coins)) = String.ofList ev5CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev7CoinsC : List Char := nfe_chars_of_hex ((ev 7).coins)
private def ev7CoinsF : HwBytes := hexBytes.go hexDigit ev7CoinsC
private theorem ev7Coins_eq : ((ev 7).coins) = ev7CoinsF := by
  have h1 : ((ev 7).coins) = hexBytes (nfe_str_of_hex ((ev 7).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 7).coins)) = String.ofList ev7CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev9CoinsC : List Char := nfe_chars_of_hex ((ev 9).coins)
private def ev9CoinsF : HwBytes := hexBytes.go hexDigit ev9CoinsC
private theorem ev9Coins_eq : ((ev 9).coins) = ev9CoinsF := by
  have h1 : ((ev 9).coins) = hexBytes (nfe_str_of_hex ((ev 9).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 9).coins)) = String.ofList ev9CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev11CoinsC : List Char := nfe_chars_of_hex ((ev 11).coins)
private def ev11CoinsF : HwBytes := hexBytes.go hexDigit ev11CoinsC
private theorem ev11Coins_eq : ((ev 11).coins) = ev11CoinsF := by
  have h1 : ((ev 11).coins) = hexBytes (nfe_str_of_hex ((ev 11).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 11).coins)) = String.ofList ev11CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev13CoinsC : List Char := nfe_chars_of_hex ((ev 13).coins)
private def ev13CoinsF : HwBytes := hexBytes.go hexDigit ev13CoinsC
private theorem ev13Coins_eq : ((ev 13).coins) = ev13CoinsF := by
  have h1 : ((ev 13).coins) = hexBytes (nfe_str_of_hex ((ev 13).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 13).coins)) = String.ofList ev13CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev15CoinsC : List Char := nfe_chars_of_hex ((ev 15).coins)
private def ev15CoinsF : HwBytes := hexBytes.go hexDigit ev15CoinsC
private theorem ev15Coins_eq : ((ev 15).coins) = ev15CoinsF := by
  have h1 : ((ev 15).coins) = hexBytes (nfe_str_of_hex ((ev 15).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 15).coins)) = String.ofList ev15CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev17CoinsC : List Char := nfe_chars_of_hex ((ev 17).coins)
private def ev17CoinsF : HwBytes := hexBytes.go hexDigit ev17CoinsC
private theorem ev17Coins_eq : ((ev 17).coins) = ev17CoinsF := by
  have h1 : ((ev 17).coins) = hexBytes (nfe_str_of_hex ((ev 17).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 17).coins)) = String.ofList ev17CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev19CoinsC : List Char := nfe_chars_of_hex ((ev 19).coins)
private def ev19CoinsF : HwBytes := hexBytes.go hexDigit ev19CoinsC
private theorem ev19Coins_eq : ((ev 19).coins) = ev19CoinsF := by
  have h1 : ((ev 19).coins) = hexBytes (nfe_str_of_hex ((ev 19).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 19).coins)) = String.ofList ev19CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev21CoinsC : List Char := nfe_chars_of_hex ((ev 21).coins)
private def ev21CoinsF : HwBytes := hexBytes.go hexDigit ev21CoinsC
private theorem ev21Coins_eq : ((ev 21).coins) = ev21CoinsF := by
  have h1 : ((ev 21).coins) = hexBytes (nfe_str_of_hex ((ev 21).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 21).coins)) = String.ofList ev21CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl
private def ev23CoinsC : List Char := nfe_chars_of_hex ((ev 23).coins)
private def ev23CoinsF : HwBytes := hexBytes.go hexDigit ev23CoinsC
private theorem ev23Coins_eq : ((ev 23).coins) = ev23CoinsF := by
  have h1 : ((ev 23).coins) = hexBytes (nfe_str_of_hex ((ev 23).coins)) := rfl
  have h2 : (nfe_str_of_hex ((ev 23).coins)) = String.ofList ev23CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

private theorem ev2_fast_ok :
    (ev2OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = true ∧
    (let (pkId, spkId, kpkId) := bundlePreKeyIds ev0InF
     ev2OutF = preKeyWire pkId spkId kpkId w0.regIdA
       (ecKey (pubBytes evictedI0 (dagBytes 21))) (dagBytes 68) (dagBytes 73) (dagBytes 138) ∧
     ev2OutF.length < 2048) ∧
    ev2InF = sendPtBytes 1 ∧
    ev2CoinsF.take 32 = dagBytes 122 ∧
    ev2CoinsF.take 64 = dagBytes 123 := by
  decide +kernel

theorem ev2_preKeySend_facts :
    (∃ p, (ev 2).cmd = .send p) ∧
    (ev 2).exit = some (0, ev2OutF) ∧
    runWrapped (ev 2) = true ∧
    (let (pkId, spkId, kpkId) := bundlePreKeyIds (ev 0).input
     ev2OutF = preKeyWire pkId spkId kpkId w0.regIdA
       (ecKey (pubBytes evictedI0 w0.aliceId)) (dagBytes 68) (dagBytes 73) (dagBytes 138) ∧
     ev2OutF.length < 2048) ∧
    (ev 2).input = sendPtBytes 1 ∧
    (ev 2).coins.take 32 = dagBytes 122 ∧
    (ev 2).coins.take 64 = dagBytes 123 ∧
    nextBundleIds (some (bundlePreKeyIds (ev 0).input)) (ev 2) =
      some (bundlePreKeyIds (ev 0).input) := by
  obtain ⟨hw, hwire, hin, hc32, hc64⟩ := ev2_fast_ok
  have hp : ∃ p, (ev 2).cmd = .send p := ⟨_, rfl⟩
  refine ⟨hp, ev2Out_exit_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hpc⟩ := hp; unfold runWrapped; rw [hpc, ev2Out_exit_eq]; exact hw
  · rw [ev0In_eq, w0_aliceId_eq]; exact hwire
  · rw [ev2In_eq]; exact hin
  · rw [ev2Coins_eq]; exact hc32
  · rw [ev2Coins_eq]; exact hc64
  · obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]

def evWhisperOutF (h : Nat) : HwBytes :=
  match h with
  | 0 => ev4OutF
  | 1 => ev6OutF
  | 2 => ev8OutF
  | 3 => ev10OutF
  | 4 => ev12OutF
  | 5 => ev14OutF
  | 6 => ev16OutF
  | 7 => ev18OutF
  | 8 => ev20OutF
  | 9 => ev22OutF
  | _ => []

private theorem ev4_whisper_fast_ok :
    (ev4OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = false ∧
    ev4OutF.tail = dagBytes (sendWmacId 2) ∧
    ev4InF = sendPtBytes 2 ∧
    ev4CoinsF.take 32 = dagBytes (sendC32Id 2) ∧
    ev4CoinsF.take 64 = dagBytes (sendC64Id 2) := by
  decide +kernel
private theorem ev6_whisper_fast_ok :
    (ev6OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = false ∧
    ev6OutF.tail = dagBytes (sendWmacId 3) ∧
    ev6InF = sendPtBytes 3 ∧
    ev6CoinsF.take 32 = dagBytes (sendC32Id 3) ∧
    ev6CoinsF.take 64 = dagBytes (sendC64Id 3) := by
  decide +kernel
private theorem ev8_whisper_fast_ok :
    (ev8OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = false ∧
    ev8OutF.tail = dagBytes (sendWmacId 4) ∧
    ev8InF = sendPtBytes 4 ∧
    ev8CoinsF.take 32 = dagBytes (sendC32Id 4) ∧
    ev8CoinsF.take 64 = dagBytes (sendC64Id 4) := by
  decide +kernel
private theorem ev10_whisper_fast_ok :
    (ev10OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = false ∧
    ev10OutF.tail = dagBytes (sendWmacId 5) ∧
    ev10InF = sendPtBytes 5 ∧
    ev10CoinsF.take 32 = dagBytes (sendC32Id 5) ∧
    ev10CoinsF.take 64 = dagBytes (sendC64Id 5) := by
  decide +kernel
private theorem ev12_whisper_fast_ok :
    (ev12OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = false ∧
    ev12OutF.tail = dagBytes (sendWmacId 6) ∧
    ev12InF = sendPtBytes 6 ∧
    ev12CoinsF.take 32 = dagBytes (sendC32Id 6) ∧
    ev12CoinsF.take 64 = dagBytes (sendC64Id 6) := by
  decide +kernel
private theorem ev14_whisper_fast_ok :
    (ev14OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = false ∧
    ev14OutF.tail = dagBytes (sendWmacId 7) ∧
    ev14InF = sendPtBytes 7 ∧
    ev14CoinsF.take 32 = dagBytes (sendC32Id 7) ∧
    ev14CoinsF.take 64 = dagBytes (sendC64Id 7) := by
  decide +kernel
private theorem ev16_whisper_fast_ok :
    (ev16OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = false ∧
    ev16OutF.tail = dagBytes (sendWmacId 8) ∧
    ev16InF = sendPtBytes 8 ∧
    ev16CoinsF.take 32 = dagBytes (sendC32Id 8) ∧
    ev16CoinsF.take 64 = dagBytes (sendC64Id 8) := by
  decide +kernel
private theorem ev18_whisper_fast_ok :
    (ev18OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = false ∧
    ev18OutF.tail = dagBytes (sendWmacId 9) ∧
    ev18InF = sendPtBytes 9 ∧
    ev18CoinsF.take 32 = dagBytes (sendC32Id 9) ∧
    ev18CoinsF.take 64 = dagBytes (sendC64Id 9) := by
  decide +kernel
private theorem ev20_whisper_fast_ok :
    (ev20OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = false ∧
    ev20OutF.tail = dagBytes (sendWmacId 10) ∧
    ev20InF = sendPtBytes 10 ∧
    ev20CoinsF.take 32 = dagBytes (sendC32Id 10) ∧
    ev20CoinsF.take 64 = dagBytes (sendC64Id 10) := by
  decide +kernel
private theorem ev22_whisper_fast_ok :
    (ev22OutF.head? == some DY.Libsignal.PQXDH.Refinement.wirePrekeyTag) = false ∧
    ev22OutF.tail = dagBytes (sendWmacId 11) ∧
    ev22InF = sendPtBytes 11 ∧
    ev22CoinsF.take 32 = dagBytes (sendC32Id 11) ∧
    ev22CoinsF.take 64 = dagBytes (sendC64Id 11) := by
  decide +kernel

theorem ev_whisperSend_facts {h : Nat} (hh : h < 10) :
    let k := 4 + 2 * h
    let j := 2 + h
    (∃ p, (ev k).cmd = .send p) ∧
    (ev k).exit = some (0, evWhisperOutF h) ∧
    runWrapped (ev k) = false ∧
    (evWhisperOutF h).tail = dagBytes (sendWmacId j) ∧
    (ev k).input = sendPtBytes j ∧
    (ev k).coins.take 32 = dagBytes (sendC32Id j) ∧
    (ev k).coins.take 64 = dagBytes (sendC64Id j) ∧
    ∀ ids, nextBundleIds ids (ev k) = ids := by
  rcases (show h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hw, htl, hin, hc32, hc64⟩ := ev4_whisper_fast_ok
    have hp : ∃ p, (ev 4).cmd = .send p := ⟨_, rfl⟩
    refine ⟨hp, ev4Out_exit_eq, ?_, htl, by rw [ev4In_eq]; exact hin,
      by rw [ev4Coins_eq]; exact hc32, by rw [ev4Coins_eq]; exact hc64, ?_⟩
    · obtain ⟨p, hpc⟩ := hp; unfold runWrapped
      rw [hpc, ev4Out_exit_eq]; exact hw
    · intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · obtain ⟨hw, htl, hin, hc32, hc64⟩ := ev6_whisper_fast_ok
    have hp : ∃ p, (ev 6).cmd = .send p := ⟨_, rfl⟩
    refine ⟨hp, ev6Out_exit_eq, ?_, htl, by rw [ev6In_eq]; exact hin,
      by rw [ev6Coins_eq]; exact hc32, by rw [ev6Coins_eq]; exact hc64, ?_⟩
    · obtain ⟨p, hpc⟩ := hp; unfold runWrapped
      rw [hpc, ev6Out_exit_eq]; exact hw
    · intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · obtain ⟨hw, htl, hin, hc32, hc64⟩ := ev8_whisper_fast_ok
    have hp : ∃ p, (ev 8).cmd = .send p := ⟨_, rfl⟩
    refine ⟨hp, ev8Out_exit_eq, ?_, htl, by rw [ev8In_eq]; exact hin,
      by rw [ev8Coins_eq]; exact hc32, by rw [ev8Coins_eq]; exact hc64, ?_⟩
    · obtain ⟨p, hpc⟩ := hp; unfold runWrapped
      rw [hpc, ev8Out_exit_eq]; exact hw
    · intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · obtain ⟨hw, htl, hin, hc32, hc64⟩ := ev10_whisper_fast_ok
    have hp : ∃ p, (ev 10).cmd = .send p := ⟨_, rfl⟩
    refine ⟨hp, ev10Out_exit_eq, ?_, htl, by rw [ev10In_eq]; exact hin,
      by rw [ev10Coins_eq]; exact hc32, by rw [ev10Coins_eq]; exact hc64, ?_⟩
    · obtain ⟨p, hpc⟩ := hp; unfold runWrapped
      rw [hpc, ev10Out_exit_eq]; exact hw
    · intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · obtain ⟨hw, htl, hin, hc32, hc64⟩ := ev12_whisper_fast_ok
    have hp : ∃ p, (ev 12).cmd = .send p := ⟨_, rfl⟩
    refine ⟨hp, ev12Out_exit_eq, ?_, htl, by rw [ev12In_eq]; exact hin,
      by rw [ev12Coins_eq]; exact hc32, by rw [ev12Coins_eq]; exact hc64, ?_⟩
    · obtain ⟨p, hpc⟩ := hp; unfold runWrapped
      rw [hpc, ev12Out_exit_eq]; exact hw
    · intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · obtain ⟨hw, htl, hin, hc32, hc64⟩ := ev14_whisper_fast_ok
    have hp : ∃ p, (ev 14).cmd = .send p := ⟨_, rfl⟩
    refine ⟨hp, ev14Out_exit_eq, ?_, htl, by rw [ev14In_eq]; exact hin,
      by rw [ev14Coins_eq]; exact hc32, by rw [ev14Coins_eq]; exact hc64, ?_⟩
    · obtain ⟨p, hpc⟩ := hp; unfold runWrapped
      rw [hpc, ev14Out_exit_eq]; exact hw
    · intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · obtain ⟨hw, htl, hin, hc32, hc64⟩ := ev16_whisper_fast_ok
    have hp : ∃ p, (ev 16).cmd = .send p := ⟨_, rfl⟩
    refine ⟨hp, ev16Out_exit_eq, ?_, htl, by rw [ev16In_eq]; exact hin,
      by rw [ev16Coins_eq]; exact hc32, by rw [ev16Coins_eq]; exact hc64, ?_⟩
    · obtain ⟨p, hpc⟩ := hp; unfold runWrapped
      rw [hpc, ev16Out_exit_eq]; exact hw
    · intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · obtain ⟨hw, htl, hin, hc32, hc64⟩ := ev18_whisper_fast_ok
    have hp : ∃ p, (ev 18).cmd = .send p := ⟨_, rfl⟩
    refine ⟨hp, ev18Out_exit_eq, ?_, htl, by rw [ev18In_eq]; exact hin,
      by rw [ev18Coins_eq]; exact hc32, by rw [ev18Coins_eq]; exact hc64, ?_⟩
    · obtain ⟨p, hpc⟩ := hp; unfold runWrapped
      rw [hpc, ev18Out_exit_eq]; exact hw
    · intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · obtain ⟨hw, htl, hin, hc32, hc64⟩ := ev20_whisper_fast_ok
    have hp : ∃ p, (ev 20).cmd = .send p := ⟨_, rfl⟩
    refine ⟨hp, ev20Out_exit_eq, ?_, htl, by rw [ev20In_eq]; exact hin,
      by rw [ev20Coins_eq]; exact hc32, by rw [ev20Coins_eq]; exact hc64, ?_⟩
    · obtain ⟨p, hpc⟩ := hp; unfold runWrapped
      rw [hpc, ev20Out_exit_eq]; exact hw
    · intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · obtain ⟨hw, htl, hin, hc32, hc64⟩ := ev22_whisper_fast_ok
    have hp : ∃ p, (ev 22).cmd = .send p := ⟨_, rfl⟩
    refine ⟨hp, ev22Out_exit_eq, ?_, htl, by rw [ev22In_eq]; exact hin,
      by rw [ev22Coins_eq]; exact hc32, by rw [ev22Coins_eq]; exact hc64, ?_⟩
    · obtain ⟨p, hpc⟩ := hp; unfold runWrapped
      rw [hpc, ev22Out_exit_eq]; exact hw
    · intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]

private theorem ev3_recv_fast_ok : ev3CoinsF.take 32 = dagBytes (recvSkId 0) := by
  decide +kernel
private theorem ev5_recv_fast_ok : ev5CoinsF.take 32 = dagBytes (recvSkId 1) := by
  decide +kernel
private theorem ev7_recv_fast_ok : ev7CoinsF.take 32 = dagBytes (recvSkId 2) := by
  decide +kernel
private theorem ev9_recv_fast_ok : ev9CoinsF.take 32 = dagBytes (recvSkId 3) := by
  decide +kernel
private theorem ev11_recv_fast_ok : ev11CoinsF.take 32 = dagBytes (recvSkId 4) := by
  decide +kernel
private theorem ev13_recv_fast_ok : ev13CoinsF.take 32 = dagBytes (recvSkId 5) := by
  decide +kernel
private theorem ev15_recv_fast_ok : ev15CoinsF.take 32 = dagBytes (recvSkId 6) := by
  decide +kernel
private theorem ev17_recv_fast_ok : ev17CoinsF.take 32 = dagBytes (recvSkId 7) := by
  decide +kernel
private theorem ev19_recv_fast_ok : ev19CoinsF.take 32 = dagBytes (recvSkId 8) := by
  decide +kernel
private theorem ev21_recv_fast_ok : ev21CoinsF.take 32 = dagBytes (recvSkId 9) := by
  decide +kernel
private theorem ev23_recv_fast_ok : ev23CoinsF.take 32 = dagBytes (recvSkId 10) := by
  decide +kernel

theorem ev_recv_facts {m : Nat} (hm : m < 11) :
    let k := 3 + 2 * m
    (∃ p, (ev k).cmd = .recv p) ∧
    (ev k).coins.take 32 = dagBytes (recvSkId m) ∧
    ∀ ids, nextBundleIds ids (ev k) = ids := by
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hp : ∃ p, (ev 3).cmd = .recv p := ⟨_, rfl⟩
    refine ⟨hp, by rw [ev3Coins_eq]; exact ev3_recv_fast_ok, ?_⟩
    intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · have hp : ∃ p, (ev 5).cmd = .recv p := ⟨_, rfl⟩
    refine ⟨hp, by rw [ev5Coins_eq]; exact ev5_recv_fast_ok, ?_⟩
    intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · have hp : ∃ p, (ev 7).cmd = .recv p := ⟨_, rfl⟩
    refine ⟨hp, by rw [ev7Coins_eq]; exact ev7_recv_fast_ok, ?_⟩
    intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · have hp : ∃ p, (ev 9).cmd = .recv p := ⟨_, rfl⟩
    refine ⟨hp, by rw [ev9Coins_eq]; exact ev9_recv_fast_ok, ?_⟩
    intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · have hp : ∃ p, (ev 11).cmd = .recv p := ⟨_, rfl⟩
    refine ⟨hp, by rw [ev11Coins_eq]; exact ev11_recv_fast_ok, ?_⟩
    intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · have hp : ∃ p, (ev 13).cmd = .recv p := ⟨_, rfl⟩
    refine ⟨hp, by rw [ev13Coins_eq]; exact ev13_recv_fast_ok, ?_⟩
    intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · have hp : ∃ p, (ev 15).cmd = .recv p := ⟨_, rfl⟩
    refine ⟨hp, by rw [ev15Coins_eq]; exact ev15_recv_fast_ok, ?_⟩
    intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · have hp : ∃ p, (ev 17).cmd = .recv p := ⟨_, rfl⟩
    refine ⟨hp, by rw [ev17Coins_eq]; exact ev17_recv_fast_ok, ?_⟩
    intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · have hp : ∃ p, (ev 19).cmd = .recv p := ⟨_, rfl⟩
    refine ⟨hp, by rw [ev19Coins_eq]; exact ev19_recv_fast_ok, ?_⟩
    intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · have hp : ∃ p, (ev 21).cmd = .recv p := ⟨_, rfl⟩
    refine ⟨hp, by rw [ev21Coins_eq]; exact ev21_recv_fast_ok, ?_⟩
    intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]
  · have hp : ∃ p, (ev 23).cmd = .recv p := ⟨_, rfl⟩
    refine ⟨hp, by rw [ev23Coins_eq]; exact ev23_recv_fast_ok, ?_⟩
    intro ids; obtain ⟨p, hpc⟩ := hp; unfold nextBundleIds; rw [hpc]

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv

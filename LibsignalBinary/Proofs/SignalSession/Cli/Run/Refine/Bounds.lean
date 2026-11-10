/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.List.SplitOn.Basic
import all Init.Data.Array.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.FilesOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing -- shake: keep

/-!
# `RunBounds` on `CliSpecPqxdh` and `CliSpecE` Domain Inputs

Proves that every domain input of `CliSpecPqxdh` and `CliSpecE` satisfies `RunCompose.RunBounds`:
stdin fits within `u32` bounds, the local `address` file is ASCII, bundle paths satisfy
`read_file`'s path invariant, and the `coins` file fits within `slotFrame`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunRefine

open Arm64 (NAME_MAX)
open Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose

private theorem keyToBytes32_length (rc : BitVec 256) : (HMAC.keyToBytes32 rc).length = 32 := by
  simp [HMAC.keyToBytes32]

private def pathOkBytes (p : List (BitVec 8)) : Bool :=
  ((p.map fun b => Char.ofNat b.toNat).splitOn '/').all fun c =>
    !isUnmodelledPathComponent c && !c.contains '\x00' &&
      !(["<stdin>".toList, "<stdout>".toList, "<stderr>".toList].contains c)

private theorem mem_stdio_ofList (c : List Char) :
    stdioPaths.contains (String.ofList c) =
      ["<stdin>".toList, "<stdout>".toList, "<stderr>".toList].contains c := by
  unfold stdioPaths
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, List.contains_iff_mem]
  have inj : ∀ s : String, String.ofList c = s ↔ c = s.toList := fun s =>
    ⟨fun h => by rw [← h, String.toList_ofList], fun h => by rw [h, String.ofList_toList]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, inj]

private theorem pathOk_pathStr_eq (p : List (BitVec 8)) :
    PathOk (pathStr p) = pathOkBytes p := by
  unfold PathOk pathComps pathStr pathOkBytes
  rw [String.toList_ofList]
  simp only [mem_stdio_ofList]

private theorem byteArray_toList_loop (bs : ByteArray) :
    ∀ i r, ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  intro i r
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r hi ih =>
    have h1 : bs.size = bs.data.toList.length := rfl
    have hget : bs.get! i = bs.data.toList[i]'(h1 ▸ hi) := by
      cases bs
      simp [ByteArray.get!]
      exact getElem!_pos _ i hi
    rw [ih, List.reverse_cons, List.append_assoc, List.singleton_append, hget,
      ← List.drop_eq_getElem_cons (h1 ▸ hi)]
  | case2 i r hi =>
    have h1 : bs.size = bs.data.toList.length := rfl
    rw [List.drop_of_length_le (Nat.not_lt.mp (h1 ▸ hi)), List.append_nil]

private theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, byteArray_toList_loop, List.reverse_nil, List.nil_append, List.drop_zero]

private theorem bundleNames_cliWrOk :
    ∀ name ∈ bundleNames, cliWrOk (bundlePath (bytesOfString bundleDir) name) := by
  have h : (bundleNames.all fun name =>
      let p := bundlePath (bytesOfString bundleDir) name
      ((pathOkBytes p && (p.all fun b => decide (b.toNat < 128))) &&
        (((p.map fun b => Char.ofNat b.toNat).splitOn '/').all fun c => decide (c.length ≤ NAME_MAX))) &&
        decide (p.length < cliPathMaxBytes)) =
      true := by
    simp [bundleNames, bundlePath, bundleDir, bytesOfString, utf8, pathOkBytes, cliPathMaxBytes,
      NAME_MAX, byteArray_toList_eq, ← String.utf8Encode_toList,
      List.utf8Encode, String.utf8EncodeChar, List.splitOn, List.splitOnP_eq_splitOnPTR]
    decide
  intro name hname
  have hn := List.all_eq_true.mp h name hname
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
  have hascii : ∀ b ∈ bundlePath (bytesOfString bundleDir) name, b.toNat < 128 := fun b hb =>
    of_decide_eq_true (List.all_eq_true.mp hn.1.1.2 b hb)
  have hmax : ((pathComps (pathStr (bundlePath (bytesOfString bundleDir) name))).all fun c =>
      decide (c.length ≤ NAME_MAX)) = true := by
    unfold pathComps pathStr
    rw [String.toList_ofList]
    exact hn.1.2
  exact ⟨⟨by rw [pathOk_pathStr_eq]; exact hn.1.1.1, ⟨hascii, hmax⟩, hn.2⟩,
    Nat.lt_trans hn.2 (by decide)⟩

theorem runBounds_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : RunBounds (pqInitInputs W st b t) := by
  have ht : t.toList.length = initiateTapeLen := t.2
  have ha : (pqInitInputs W st b t).argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [coinsOf_pqInit, ht]
    decide
  · intro peer h
    rw [ha, parseArgs_init] at h
    cases h
  · intro peer h
    rw [ha, parseArgs_init] at h
    cases h
  · intro bs h
    rw [ownAddr_pqInit] at h
    cases h
    exact textBytes_addrE_ascii st.party
  · intro peer dir h
    rw [ha, parseArgs_init] at h
    cases h
    exact bundleNames_cliWrOk

theorem runBounds_pqSend (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (hm : m.length < 2 ^ 32) :
    RunBounds (pqSendInputs W st m r) := by
  have hr : r.toList.length = 64 := r.2
  have ha : (pqSendInputs W st m r).argv = (Cmd.send (partyAddress st.party.other)).argv := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [coinsOf_pqSend, hr]
    decide
  · intro _ _
    exact hm
  · intro peer h
    rw [ha, parseArgs_send] at h
    cases h
  · intro bs h
    rw [ownAddr_pqSend] at h
    cases h
    exact textBytes_addrE_ascii st.party
  · intro peer dir h
    rw [ha, parseArgs_send] at h
    cases h

/-- `RunBounds` for PQXDH `recv` when full stdin `c` (including the wire type byte) has length `≤ 2^32`. -/
theorem runBounds_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (hc : c.length ≤ 2 ^ 32) : RunBounds (pqRecvInputs W st c rc) := by
  have ha : (pqRecvInputs W st c rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [coinsOf_pqRecv, keyToBytes32_length]
    decide
  · intro peer h
    rw [ha, parseArgs_recv] at h
    cases h
  · intro _ _
    change c.tail.length < 2 ^ 32
    cases c with
    | nil => decide
    | cons _ _ => exact Nat.lt_of_succ_le hc
  · intro bs h
    rw [ownAddr_pqRecv] at h
    cases h
    exact textBytes_addrE_ascii st.party
  · intro peer dir h
    rw [ha, parseArgs_recv] at h
    cases h

theorem runBounds_smSend (g : GhostState (List (BitVec 8))) (m : List (BitVec 8))
    (hm : m.length < 2 ^ 32) : RunBounds (smSendInputs g m) := by
  have ha : (smSendInputs g m).argv = (Cmd.send (partyAddress g.party.other)).argv := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [coinsOf_smSend]
    decide
  · intro _ _
    exact hm
  · intro peer h
    rw [ha, parseArgs_send] at h
    cases h
  · intro bs h
    rw [ownAddr_smSend] at h
    cases h
    exact textBytes_addrE_ascii g.party
  · intro peer dir h
    rw [ha, parseArgs_send] at h
    cases h

/-- `RunBounds` for Signal-Message `recv` when payload `c` (after `msgTypeWhisper`) has length `< 2^32`. -/
theorem runBounds_smRecv (g : GhostState (List (BitVec 8))) (c : List (BitVec 8)) (rc : BitVec 256)
    (hc : c.length < 2 ^ 32) : RunBounds (smRecvInputs g c rc) := by
  have ha : (smRecvInputs g c rc).argv = (Cmd.recv (partyAddress g.party.other)).argv := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [coinsOf_smRecv, keyToBytes32_length]
    decide
  · intro peer h
    rw [ha, parseArgs_recv] at h
    cases h
  · intro _ _
    exact hc
  · intro bs h
    rw [ownAddr_smRecv] at h
    cases h
    exact textBytes_addrE_ascii g.party
  · intro peer dir h
    rw [ha, parseArgs_recv] at h
    cases h

end CryptoVerification.SignalSession.Cli.RunRefine

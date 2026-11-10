/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.FilesOk
import all Init.Data.String.Defs
import all Init.Data.Repr
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon

/-!
# Encrypt Slot Input Condition (`encOk₀` and `RunEncOk`)

Defines `encOk₀ Scope F peer coins := 64 ≤ coins.length ∨ PeerPqEmpty Scope F peer` for the
`encrypt` slot (`encSlotSpec`, `RunEncOk`) and discharges it on PQXDH and Signal-Message domain
inputs.

Encrypting with a non-empty post-quantum ratchet state follows the V1 route (`otrEncryptSpecT`),
which requires `64 ≤ coins.length` (DEV-SPQR5: on a shorter tape the binary zero-pads and returns
`Ok` while the model returns `rngExhausted`); when the post-quantum state is empty (`PeerPqEmpty`),
any tape length suffices.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## `encOk₀` and `PeerPqEmpty` -/

/-- Injectivity of `E2E.Record.encodeRecord` (`SessionRecord::serialize`) on `Scope`. -/
def EncodeInjOn (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ r₁ r₂, Scope r₁ → Scope r₂ → E2E.Record.encodeRecord r₁ = E2E.Record.encodeRecord r₂ → r₁ = r₂

/-- Every record in `Scope` encoded by `peer`'s session file on `F` has an empty post-quantum
ratchet state (`pqRatchetState = []`). -/
def PeerPqEmpty (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles) (peer : AddrVal) :
    Prop :=
  ∀ bs r, StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) = .ok bs →
    E2E.Record.encodeRecord r = bs → Scope r → E2E.Record.RecordPqEmpty r

/-- Encrypt slot input condition: either `64 ≤ coins.length` or `PeerPqEmpty Scope F peer`. -/
def encOk₀ (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles) (peer : AddrVal)
    (coins : List (BitVec 8)) : Prop :=
  64 ≤ coins.length ∨ PeerPqEmpty Scope F peer

/-- Eliminates `encOk₀` at a decoded session record `r` in `Scope` into `64 ≤ coins.length` or
`RecordPqEmpty r`. -/
theorem encOk₀_split {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrVal} {coins : List (BitVec 8)} (h : encOk₀ Scope F peer coins)
    {bs : List (BitVec 8)} {r : SessionRecord (List (BitVec 8))}
    (hget : StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) = .ok bs)
    (henc : E2E.Record.encodeRecord r = bs) (hS : Scope r) :
    64 ≤ coins.length ∨ E2E.Record.RecordPqEmpty r := by
  exact h.imp id fun hpq => hpq bs r hget henc hS

/-! ## Domain input lemmas -/

private theorem cons_drop_succ {α : Type} :
    ∀ (l : List α) (i : Nat) (_ : i < l.length), l[i] :: l.drop (i + 1) = l.drop i
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, hi => cons_drop_succ xs i (Nat.lt_of_succ_lt_succ hi)

private theorem byteArray_mk_toList (l : List UInt8) :
    (⟨l.toArray⟩ : ByteArray).toList = l := by
  suffices ∀ (i : Nat) (r : List UInt8),
      ByteArray.toList.loop ⟨l.toArray⟩ i r = r.reverse ++ l.drop i by
    simpa [ByteArray.toList] using this 0 []
  intro i r
  fun_induction ByteArray.toList.loop ⟨l.toArray⟩ i r with
  | case1 i r hi ih =>
    have hi' : i < l.length := by simpa [ByteArray.size] using hi
    have hget : (⟨l.toArray⟩ : ByteArray).get! i = l[i] := by
      show l.toArray[i]! = l[i]
      rw [getElem!_pos l.toArray i (by simpa using hi')]
      simp
    rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
      cons_drop_succ l i hi']
  | case2 i r hi =>
    have hi' : l.length ≤ i := by simpa [ByteArray.size] using hi
    simp [List.drop_of_length_le hi']

private theorem utf8_ofList_eq (s : String) (cs : List Char) (h : s = String.ofList cs) :
    Cli.utf8 s =
      ((cs.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat) := by
  subst h
  change (String.ofList cs).toByteArray.toList.map _ = _
  rw [String.toByteArray_ofList, List.utf8Encode, ByteArray.ext List.data_toByteArray,
    byteArray_mk_toList]

private abbrev nameAChars : List Char :=
  ['8', 'a', '6', 'f', '1', 'c', '2', 'e', '-', '3', 'b', '4', 'd', '-', '4', 'e', '5', 'f'] ++
  ['-', '9', 'a', '0', 'b', '-', '1', 'c', '2', 'd', '3', 'e', '4', 'f', '5', 'a', '6', 'b']

private abbrev nameABytes : List (BitVec 8) :=
  [56#8, 97#8, 54#8, 102#8, 49#8, 99#8, 50#8, 101#8, 45#8,
   51#8, 98#8, 52#8, 100#8, 45#8, 52#8, 101#8, 53#8, 102#8] ++
  [45#8, 57#8, 97#8, 48#8, 98#8, 45#8, 49#8, 99#8, 50#8,
   100#8, 51#8, 101#8, 52#8, 102#8, 53#8, 97#8, 54#8, 98#8]

private abbrev nameBChars : List Char :=
  ['5', 'd', '3', 'e', '2', 'f', '1', '0', '-', '7', 'a', '8', 'b', '-', '4', 'c', '9', 'd'] ++
  ['-', '8', 'e', '0', 'f', '-', 'a', '1', 'b', '2', 'c', '3', 'd', '4', 'e', '5', 'f', '6']

private abbrev nameBBytes : List (BitVec 8) :=
  [53#8, 100#8, 51#8, 101#8, 50#8, 102#8, 49#8, 48#8, 45#8,
   55#8, 97#8, 56#8, 98#8, 45#8, 52#8, 99#8, 57#8, 100#8] ++
  [45#8, 56#8, 101#8, 48#8, 102#8, 45#8, 97#8, 49#8, 98#8,
   50#8, 99#8, 51#8, 100#8, 52#8, 101#8, 53#8, 102#8, 54#8]

private theorem utf8_nameA_eq : Cli.utf8 (partyAddressName .A) = nameABytes :=
  (utf8_ofList_eq (partyAddressName .A) nameAChars (by decide)).trans rfl

private theorem utf8_nameB_eq : Cli.utf8 (partyAddressName .B) = nameBBytes :=
  (utf8_ofList_eq (partyAddressName .B) nameBChars (by decide)).trans rfl

private theorem coinsOf_trailing {l : List (String × List (BitVec 8))} {cs : List (BitVec 8)}
    {i : Inputs} (hf : i.files = l ++ [(coinsFile, cs)]) : MainHops.coinsOf i = cs := by
  have hns : normalizePath "coins" ∉ stdioPaths.map normalizePath := of_decide_eq_true rfl
  have hemp : (normalizePath "coins").isEmpty = false := of_decide_eq_true rfl
  have h4 : (normalizePath "coins" == normalizePath coinsFile) = true := of_decide_eq_true rfl
  have hanc : (normalizePath coinsFile).nonEmptyPrefixes.dropLast = [] := of_decide_eq_true rfl
  unfold MainHops.coinsOf filesOf fsView initFsState
  simp only [hf, hns, ↓reduceIte, List.foldl_append, List.foldl_cons, List.foldl_nil, hanc,
    FsState.files, FsState.getEntry, FsState.setFd, FsState.setFile, FsState.setEntry,
    hemp, Bool.false_eq_true, h4, Option.getD_some]

theorem coinsOf_pqSend (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) : MainHops.coinsOf (pqSendInputs W st m r) = r.toList := by
  exact coinsOf_trailing rfl

theorem coinsOf_smSend (g : GhostState Bytes) (m : List (BitVec 8)) :
    MainHops.coinsOf (smSendInputs g m) = [] := by
  exact coinsOf_trailing rfl

/-- On `smSendInputs g m`, `PeerPqEmpty` holds whenever `encodeRecord` is injective on `Scope`,
`g`'s record lies in `Scope`, and `g` has an empty post-quantum state. -/
theorem peerPqEmpty_smSend {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinj : EncodeInjOn Scope) (g : GhostState Bytes) (m : List (BitVec 8))
    (hS : Scope (E2E.Record.toRecord E2E.Record.extrasM g))
    (hpq : g.session.pqRatchetState = [])
    (hcap : (E2E.encodeRecord g).length ≤ fileCapBytes) :
    PeerPqEmpty Scope (runFiles (smSendInputs g m)) (partyAddr g.party.other) := by
  intro bs r hget henc hSr
  rw [show smSendInputs g m = smInputs g (.send (partyAddress g.party.other)) [] m from rfl,
    smSessGet g (.send (partyAddress g.party.other)) [] m hcap, Except.ok.injEq] at hget
  have hr : r = E2E.Record.toRecord E2E.Record.extrasM g :=
    hinj r _ hSr hS (by rw [henc, ← hget, Reach.encodeRecord_eq_toRecord])
  subst hr
  intro s hs
  simp only [E2E.Record.toRecord, Option.some.injEq] at hs
  subst hs
  exact hpq

theorem encOk₀_pqSend (Scope : SessionRecord (List (BitVec 8)) → Prop) (W : PEParams)
    (st : PqParty) (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64) :
    encOk₀ Scope (runFiles (pqSendInputs W st m r)) (partyAddr st.party.other)
      (MainHops.coinsOf (pqSendInputs W st m r)) := by
  left
  rw [coinsOf_pqSend, List.Vector.toList_length]

theorem encOk₀_smSend {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinj : EncodeInjOn Scope) (g : GhostState Bytes) (m : List (BitVec 8))
    (hS : Scope (E2E.Record.toRecord E2E.Record.extrasM g))
    (hpq : g.session.pqRatchetState = [])
    (hcap : (E2E.encodeRecord g).length ≤ fileCapBytes) :
    encOk₀ Scope (runFiles (smSendInputs g m)) (partyAddr g.party.other)
      (MainHops.coinsOf (smSendInputs g m)) := by
  exact Or.inr (peerPqEmpty_smSend hinj g m hS hpq hcap)

/-! ## Bridges to `RunEncOk` -/

private theorem utf8_init_eq : Cli.utf8 "init" = [105#8, 110#8, 105#8, 116#8] :=
  (utf8_ofList_eq "init" ['i', 'n', 'i', 't'] (by decide)).trans rfl

private theorem utf8_send_eq : Cli.utf8 "send" = [115#8, 101#8, 110#8, 100#8] :=
  (utf8_ofList_eq "send" ['s', 'e', 'n', 'd'] (by decide)).trans rfl

private theorem utf8_recv_eq : Cli.utf8 "recv" = [114#8, 101#8, 99#8, 118#8] :=
  (utf8_ofList_eq "recv" ['r', 'e', 'c', 'v'] (by decide)).trans rfl

private theorem utf8_keygen_eq : Cli.utf8 "keygen" = [107#8, 101#8, 121#8, 103#8, 101#8, 110#8] :=
  (utf8_ofList_eq "keygen" ['k', 'e', 'y', 'g', 'e', 'n'] (by decide)).trans rfl

private theorem pniPrefix_eq_bytes : pniPrefix = [80#8, 78#8, 73#8, 58#8] :=
  (utf8_ofList_eq "PNI:" ['P', 'N', 'I', ':'] (by decide)).trans rfl

private theorem addrParse_addrE_local (P : Party) :
    addrParse uuidTryParse (bytesOfString (partyAddress P).text) = some ⟨Cli.utf8 (partyAddressName P), 1#8⟩ := by
  cases P with
  | A =>
    have ht : bytesOfString (partyAddress .A).text = nameABytes ++ [46#8, 49#8] := by
      rw [show (partyAddress .A).text = String.ofList (nameAChars ++ ['.', '1']) by decide]
      simp only [bytesOfString, String.toList_ofList, List.map_append, List.map_cons, List.map_nil]
      rfl
    have hshape :
        (addrParse uuidTryParse (nameABytes ++ [46#8, 49#8])).map (fun v => (v.name, v.device)) =
          some (nameABytes, 1#8) := by
      unfold addrParse serviceIdParse
      rw [pniPrefix_eq_bytes]
      decide
    rw [ht, utf8_nameA_eq]
    cases hv : addrParse uuidTryParse (nameABytes ++ [46#8, 49#8]) with
    | none => rw [hv] at hshape; cases hshape
    | some v =>
      rw [hv] at hshape
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hshape
      cases v
      simp only at hshape
      rw [hshape.1, hshape.2]
  | B =>
    have ht : bytesOfString (partyAddress .B).text = nameBBytes ++ [46#8, 49#8] := by
      rw [show (partyAddress .B).text = String.ofList (nameBChars ++ ['.', '1']) by decide]
      simp only [bytesOfString, String.toList_ofList, List.map_append, List.map_cons, List.map_nil]
      rfl
    have hshape :
        (addrParse uuidTryParse (nameBBytes ++ [46#8, 49#8])).map (fun v => (v.name, v.device)) =
          some (nameBBytes, 1#8) := by
      unfold addrParse serviceIdParse
      rw [pniPrefix_eq_bytes]
      decide
    rw [ht, utf8_nameB_eq]
    cases hv : addrParse uuidTryParse (nameBBytes ++ [46#8, 49#8]) with
    | none => rw [hv] at hshape; cases hshape
    | some v =>
      rw [hv] at hshape
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hshape
      cases v
      simp only at hshape
      rw [hshape.1, hshape.2]

private theorem parseArgs_cmd_local (cmd : Cmd) {P : Party} (hP : cmdPeer cmd = partyAddress P) :
    ∃ c, parseArgs uuidTryParse (cmd.argv.map bytesOfString) = some c ∧ c.tag = cmdTag cmd := by
  have hi : bytesOfString "init" = utf8 "init" := by rw [utf8_init_eq]; simp [bytesOfString]
  have hs : bytesOfString "send" = utf8 "send" := by rw [utf8_send_eq]; simp [bytesOfString]
  have hr : bytesOfString "recv" = utf8 "recv" := by rw [utf8_recv_eq]; simp [bytesOfString]
  have hk : utf8 "init" ≠ utf8 "keygen" := by rw [utf8_init_eq, utf8_keygen_eq]; decide
  have hrs : utf8 "recv" ≠ utf8 "send" := by rw [utf8_recv_eq, utf8_send_eq]; decide
  have ha := addrParse_addrE_local P
  cases cmd with
  | init peer b =>
    simp only [cmdPeer] at hP
    subst hP
    exact ⟨.init ⟨utf8 (partyAddressName P), 1#8⟩ (bytesOfString b), by
      simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hi, hk, ha, Option.map_some,
        ↓reduceIte], rfl⟩
  | send peer =>
    simp only [cmdPeer] at hP
    subst hP
    exact ⟨.send ⟨utf8 (partyAddressName P), 1#8⟩, by
      simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hs, ha, Option.map_some,
        ↓reduceIte], rfl⟩
  | recv peer =>
    simp only [cmdPeer] at hP
    subst hP
    exact ⟨.recv ⟨utf8 (partyAddressName P), 1#8⟩, by
      simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hr, hrs, ha, Option.map_some,
        ↓reduceIte], rfl⟩

/-- On a `send` command line to `partyAddress P`, `RunEncOk S i` reduces to `S.encOk` on `runFiles i`,
`partyAddr P`, and `coinsOf i`. -/
theorem runEncOk_of_send {S : RunSem} {i : Inputs} {P : Party}
    (hargv : i.argv = (Cmd.send (partyAddress P)).argv)
    (hok : S.encOk (runFiles i) (partyAddr P) (MainHops.coinsOf i)) : RunEncOk S i := by
  intro peer _ _ hparse _ _
  have hs : bytesOfString "send" = utf8 "send" := by rw [utf8_send_eq]; simp [bytesOfString]
  rw [hargv] at hparse
  simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hs, addrParse_addrE_local P,
    Option.map_some, ↓reduceIte, Option.some.injEq, CallV.send.injEq] at hparse
  subst hparse
  exact hok

/-- On an `init` or `recv` command line, `RunEncOk S i` holds unconditionally. -/
theorem runEncOk_of_not_send {S : RunSem} {i : Inputs} (cmd : Cmd) {P : Party}
    (hP : cmdPeer cmd = partyAddress P) (hargv : i.argv = cmd.argv) (hns : ∀ a, cmd ≠ .send a) :
    RunEncOk S i := by
  intro peer _ _ hparse _ _
  obtain ⟨c, hc, htag⟩ := parseArgs_cmd_local cmd hP
  rw [hargv, hc, Option.some.injEq] at hparse
  subst hparse
  cases cmd with
  | init _ _ => cases htag
  | send a => exact absurd rfl (hns a)
  | recv _ => cases htag

theorem runEncOk_pqSend {S : RunSem} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hS : S.encOk = encOk₀ Scope) (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) : RunEncOk S (pqSendInputs W st m r) := by
  exact runEncOk_of_send rfl (hS ▸ encOk₀_pqSend Scope W st m r)

theorem runEncOk_smSend {S : RunSem} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hS : S.encOk = encOk₀ Scope) (hinj : EncodeInjOn Scope) (g : GhostState Bytes)
    (m : List (BitVec 8)) (hsc : Scope (E2E.Record.toRecord E2E.Record.extrasM g))
    (hpq : g.session.pqRatchetState = [])
    (hcap : (E2E.encodeRecord g).length ≤ fileCapBytes) : RunEncOk S (smSendInputs g m) := by
  exact runEncOk_of_send rfl (hS ▸ encOk₀_smSend hinj g m hsc hpq hcap)

theorem runEncOk_smRecv (S : RunSem) (g : GhostState Bytes) (c : List (BitVec 8))
    (rc : BitVec 256) : RunEncOk S (smRecvInputs g c rc) := by
  exact runEncOk_of_not_send (.recv (partyAddress g.party.other)) rfl rfl fun _ h => nomatch h

theorem runEncOk_pqInit (S : RunSem) (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : RunEncOk S (pqInitInputs W st b t) := by
  exact runEncOk_of_not_send (.init (partyAddress st.party.other) bundleDir) rfl rfl fun _ h => nomatch h

theorem runEncOk_pqRecv (S : RunSem) (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) : RunEncOk S (pqRecvInputs W st c rc) := by
  exact runEncOk_of_not_send (.recv (partyAddress st.party.other)) rfl rfl fun _ h => nomatch h

end CryptoVerification.SignalSession.Cli.Slots

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.EncOk
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon

/-!
# Functional Session-Record Loader (`loadRec`)

Defines `loadRec Scope F peer` as a functional witness for the CLI session kit's `SessLoadAns Scope`
relation on `StoresGhost.opened.sessions`, proves uniqueness under `EncodeInjOn Scope`, and computes
`loadRec` on Signal-Message and PQXDH domain inputs.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

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

open Classical in
/-- Functional witness for `SessLoadAns Scope` on `StoresGhost.opened.sessions`: returns `none` on
an empty file and selects the decoded record in `Scope` via `Classical.choose` on non-empty bytes. -/
noncomputable def loadRec (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer : AddrVal) : Except Unit (Option (SessionRecord (List (BitVec 8)))) :=
  match StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) with
  | .error _ => .error ()
  | .ok [] => .ok none
  | .ok (b :: bs) =>
    if h : ∃ r, E2E.Record.encodeRecord r = b :: bs ∧ Scope r then .ok (some (Classical.choose h))
    else .error ()

/-- On well-formed peer files (`FilesOkPeer Scope F peer`), `loadRec` satisfies `SessLoadAns Scope`. -/
theorem sessLoadAns_loadRec {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrVal} (h : FilesOkPeer Scope F peer) :
    SessLoadAns Scope (StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer))
      (loadRec Scope F peer) := by
  obtain ⟨bs, hget, hwf⟩ := h.sessGet
  unfold loadRec
  rw [hget]
  rcases bs with _ | ⟨b, bs⟩
  · rfl
  · rcases hwf with hnil | hex
    · cases hnil
    · dsimp only
      simp only [hex, ↓reduceDIte]
      exact ⟨Classical.choose hex, rfl, (Classical.choose_spec hex).1,
        (Classical.choose_spec hex).2⟩

/-- Under `EncodeInjOn Scope`, any `SessLoadAns Scope` witness equals `loadRec Scope F peer`. -/
theorem loadRec_unique {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinj : EncodeInjOn Scope) {F : FsFiles} {peer : AddrVal}
    {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (h : SessLoadAns Scope (StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer))
      ans) :
    ans = loadRec Scope F peer := by
  unfold loadRec
  rcases hget : StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) with
    _ | (_ | ⟨b, bs⟩) <;> rw [hget] at h
  · exact h
  · exact h
  · obtain ⟨r, hans, henc, hsc⟩ := h
    have hex : ∃ r', E2E.Record.encodeRecord r' = b :: bs ∧ Scope r' := ⟨r, henc, hsc⟩
    dsimp only
    simp only [hex, ↓reduceDIte]
    rw [hans,
      hinj r (Classical.choose hex) hsc (Classical.choose_spec hex).2
        (henc.trans (Classical.choose_spec hex).1.symm)]

/-- Specializes `encOk₀_split` to a record loaded via `loadRec Scope F peer = .ok (some r)`. -/
theorem loadRec_encOk₀ {Scope : SessionRecord (List (BitVec 8)) → Prop} {F : FsFiles}
    {peer : AddrVal} {coins : List (BitVec 8)} (h : encOk₀ Scope F peer coins)
    {r : SessionRecord (List (BitVec 8))} (hr : loadRec Scope F peer = .ok (some r)) :
    64 ≤ coins.length ∨ E2E.Record.RecordPqEmpty r := by
  unfold loadRec at hr
  rcases hget : StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) with
    _ | (_ | ⟨b, bs⟩) <;> rw [hget] at hr <;> dsimp only at hr
  · cases hr
  · cases hr
  · split at hr
    · rename_i hex
      simp only [Except.ok.injEq, Option.some.injEq] at hr
      subst hr
      exact encOk₀_split h hget (Classical.choose_spec hex).1 (Classical.choose_spec hex).2
    · cases hr

private theorem encodeRecord_some_ne_nil (s : Session (List (BitVec 8))) :
    E2E.Record.encodeRecord ⟨some s⟩ ≠ [] := by
  intro h
  have hge : 1 ≤ (E2E.Record.encodeRecord ⟨some s⟩).length := by
    unfold E2E.Record.encodeRecord E2E.Record.msgField E2E.Record.lenField
    dsimp only [Option.map]
    simp only [List.length_append]
    have hk : (encodeKey 1 WireType.lengthDelimited).length = 1 := by decide
    omega
  rw [h] at hge
  cases hge

private theorem loadRec_of_get_some {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinj : EncodeInjOn Scope) {F : FsFiles} {peer : AddrVal}
    {s : Session (List (BitVec 8))}
    (hget : StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) =
      .ok (E2E.Record.encodeRecord ⟨some s⟩))
    (hS : Scope ⟨some s⟩) :
    loadRec Scope F peer = .ok (some ⟨some s⟩) := by
  rcases henc : E2E.Record.encodeRecord ⟨some s⟩ with _ | ⟨b, bs⟩
  · exact absurd henc (encodeRecord_some_ne_nil s)
  · refine (loadRec_unique hinj ?_).symm
    rw [hget, henc]
    exact ⟨⟨some s⟩, rfl, henc, hS⟩

private theorem loadRec_of_pqSessBytes {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinj : EncodeInjOn Scope) {F : FsFiles} {peer : AddrVal} {st : PqParty}
    (hget : StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) =
      .ok (pqSessBytes st))
    (hS : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g)) :
    loadRec Scope F peer =
      .ok (st.session.map fun (x, g) => E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g) := by
  rcases hsess : st.session with _ | ⟨x, g⟩
  · refine (loadRec_unique hinj ?_).symm
    rw [hget]
    simp only [pqSessBytes, hsess]
    rfl
  · simp only [Option.map_some]
    refine loadRec_of_get_some hinj ?_ (hS x g hsess)
    rw [hget]
    simp only [pqSessBytes, hsess, E2E.RecordX.encodeRecordX_eq_toRecord]
    rfl

theorem loadRec_sm {Scope : SessionRecord (List (BitVec 8)) → Prop} (hinj : EncodeInjOn Scope)
    (g : GhostState Bytes) (cmd : Cmd) (coins stdin : List (BitVec 8))
    (hS : Scope (E2E.Record.toRecord E2E.Record.extrasM g))
    (hcap : (E2E.encodeRecord g).length ≤ fileCapBytes) :
    loadRec Scope (runFiles (smInputs g cmd coins stdin)) (partyAddr g.party.other) =
      .ok (some (E2E.Record.toRecord E2E.Record.extrasM g)) := by
  refine loadRec_of_get_some hinj ?_ hS
  rw [smSessGet g cmd coins stdin hcap, Reach.encodeRecord_eq_toRecord]
  rfl

theorem loadRec_pqInit {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinj : EncodeInjOn Scope) (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen)
    (hS : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g))
    (hcap : (pqSessBytes st).length ≤ fileCapBytes) :
    loadRec Scope (runFiles (pqInitInputs W st b t)) (partyAddr st.party.other) =
      .ok (st.session.map fun (x, g) => E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g) :=
  loadRec_of_pqSessBytes hinj (pqSessGet_init W st b t hcap) hS

theorem loadRec_pqSend {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinj : EncodeInjOn Scope) (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64)
    (hS : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g))
    (hcap : (pqSessBytes st).length ≤ fileCapBytes) :
    loadRec Scope (runFiles (pqSendInputs W st m r)) (partyAddr st.party.other) =
      .ok (st.session.map fun (x, g) => E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g) :=
  loadRec_of_pqSessBytes hinj (pqSessGet_send W st m r hcap) hS

theorem loadRec_pqRecv {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hinj : EncodeInjOn Scope) (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256)
    (hS : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g))
    (hcap : (pqSessBytes st).length ≤ fileCapBytes) :
    loadRec Scope (runFiles (pqRecvInputs W st c rc)) (partyAddr st.party.other) =
      .ok (st.session.map fun (x, g) => E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g) :=
  loadRec_of_pqSessBytes hinj (pqSessGet_recv W st c rc hcap) hS

end CryptoVerification.SignalSession.Cli.Slots

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced

/-!
# CLI `SessionFiles` Store Specification

Defines the pure store invariant `CliSessInv`, the separation-logic store predicate
`cliSessStoreAt`, and the concrete `SessionStoreSpec` instance `cliSessionStoreSpec` for
`SessionFiles(Dir)`, together with its vtable, quietness, and invariant-preservation lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)

/-! ## Store invariant -/

/-- Pure invariant of `SessionFiles` at peer `peer` and initial file table `F0`: `u32` bounds for
`address_text` and `Dir::get`/`Dir::put`, path guard `pathOk` on `sessions/<address_text(peer)>`,
a well-formed (`SessFileWf Scope`) session file for `peer`, and capacity in `changed` for one
`put`. -/
structure CliSessInv (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost) (d : DirGhost) : Prop where
  nameLt : peer.name.bytes.length < 2 ^ 32
  textLt : (addressText peer.val).length < 2 ^ 32
  pathLt : d.path.length < 2 ^ 32
  pathOk : pathOk (pathOf d.path (addressText peer.val))
  getOk : ∃ bs, d.get rd F0 (addressText peer.val) = .ok bs ∧ SessFileWf Scope bs
  changedLt : d.changed.length < 2 ^ 32 ∧
    (d.changed.length + 1 < 2 ^ 32 ∨ addressText peer.val ∈ d.changed.map Prod.fst)

/-- `SessionFiles` layout at `self`: its `Dir` at `+0x00` and `CliSessInv`. -/
def cliSessStoreAt (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (self : BitVec 64) (d : DirGhost) : SepProp :=
  ⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗ dirAt A self d

/-! ## Trace projection -/

/-- Trace events of a single `StoreCall`: empty for `load_session`/`store_session`, and
`trustEvent`/`saveEvent` for identity calls. -/
def cliSessCallEvs (ans : StoreAnswers (List (BitVec 8)) Unit) :
    StoreCall AddrVal (List (BitVec 8)) → List TraceEvent
  | .loadSession _ => []
  | .isTrustedIdentity rem k dir => [trustEvent rem k dir ans.isTrustedIdentity]
  | .saveIdentity rem k => [saveEvent rem k ans.saveIdentity]
  | .storeSession _ _ => []

def cliSessTraceOf (_encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (calls : List (StoreCall AddrVal (List (BitVec 8)))) : List TraceEvent :=
  (calls.map (cliSessCallEvs ans)).flatten

/-! ## Store kit specification -/

/-- Concrete `SessionStoreSpec` for CLI `SessionFiles` at peer `peer`, scope `Scope`, and initial
files `F0`. -/
def cliSessionStoreSpec (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (loadShimStk loadPollStk storeShimStk storePollStk : Nat) :
    SessionStoreSpec A b where
  ss_vt := b + cliSessVtOff
  id_vt := b + cliIdVtOff
  StoreState := DirGhost
  storeAt := cliSessStoreAt A rd F0 pathOk Scope peer
  addrOk := fun rem => rem = peer.val
  envOk := fun f => f = F0
  fdsOk := fun fs => FdsGe3Closed fs
  RecOk := fun r => Scope r ∧ (E2E.Record.encodeRecord r).length < 2 ^ 32
  storeUpdate := fun d rem r _ => d.put (addressText rem) (E2E.Record.encodeRecord r)
  loadRel := fun d rem ans =>
    ∃ bs, d.get rd F0 (addressText rem) = .ok bs ∧ SessLoadAns Scope (.ok bs) ans
  storeRel := fun _ _ _ ans => ans = .ok ()
  loadEvs := fun _ _ _ => []
  storeEvs := fun _ _ _ _ => []
  traceOf := cliSessTraceOf
  traceOf_load := fun _ _ _ => rfl
  traceOf_load_trust := fun _ _ _ _ _ => rfl
  traceOf_load_trust_save := fun _ _ _ _ _ => rfl
  traceOf_all4 := fun _ _ _ _ _ _ => rfl
  traceOf_load_store := fun _ _ _ _ => rfl
  loadShimOff := cliSessLoadShimOff
  loadFutVtOff := cliSessLoadFutVtOff
  loadPollOff := cliSessLoadPollOff
  loadFutDropOff := cliIdFutDropOff
  loadBoxSize := 24
  storeShimOff := cliSessStoreShimOff
  storeFutVtOff := cliSessStoreFutVtOff
  storePollOff := cliSessStorePollOff
  storeFutDropOff := cliIdFutDropOff
  storeBoxSize := 32
  loadShimStack := loadShimStk
  loadPollStack := loadPollStk
  storeShimStack := storeShimStk
  storePollStack := storePollStk
  loadBoxAt := sessLoadBoxAt
  storeBoxAt := sessStoreBoxAt
  loadBoxAt_memRegion := (hookSessionStoreSpec A b).loadBoxAt_memRegion
  storeBoxAt_memRegion := (hookSessionStoreSpec A b).storeBoxAt_memRegion
  loadBoxSize_ne_zero := by decide
  storeBoxSize_ne_zero := by decide
  loadBoxSize_lt := by decide
  storeBoxSize_lt := by decide
  loadFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)
  storeFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)

section
variable {A : RustAlloc} {img : Obj.Image} {rd : ReadRule} {F0 : FsFiles}
  {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
  {peer : AddrGhost} {s1 s2 s3 s4 : Nat}

theorem cliSessKitOffsets :
    CliSessKitOffsets img (cliSessionStoreSpec A img.base rd F0 pathOk Scope peer s1 s2 s3 s4) where
  ssVt := rfl
  loadShim := rfl
  storeShim := rfl
  loadFutVt := rfl
  storeFutVt := rfl
  loadPoll := rfl
  storePoll := rfl
  loadFutDrop := rfl
  storeFutDrop := rfl
  loadBoxSize := rfl
  storeBoxSize := rfl

/-- Vtable validity (`SessionOnlyVtablesOk`) for `cliSessionStoreSpec`. -/
theorem cliSessionStoreSpec_vtablesOk (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyVtablesOk img
      (cliSessionStoreSpec A img.base rd F0 pathOk Scope peer s1 s2 s3 s4) :=
  cliSessionOnlyVtablesOk himg cliSessKitOffsets

/-- `cliSessionStoreSpec` emits no filesystem trace events (`Quiet`). -/
theorem cliSessionStoreSpec_quiet :
    (cliSessionStoreSpec A img.base rd F0 pathOk Scope peer s1 s2 s3 s4).Quiet :=
  ⟨fun _ _ _ => by simp [cliSessionStoreSpec, NoFsEv],
    fun _ _ _ _ => by simp [cliSessionStoreSpec, NoFsEv]⟩

end

/-! ## Invariant preservation -/

theorem setOrPush_length_of_mem {n bs : List (BitVec 8)} :
    ∀ {l : List (List (BitVec 8) × List (BitVec 8))}, n ∈ l.map Prod.fst →
      (DirGhost.setOrPush n bs l).length = l.length
  | [], h => by simp at h
  | e :: es, h => by
    by_cases he : e.1 = n
    · simp [DirGhost.setOrPush, he]
    · have h' : n ∈ es.map Prod.fst := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm he
        · exact h
      simp [DirGhost.setOrPush, he, setOrPush_length_of_mem h']

theorem setOrPush_length_le (n bs : List (BitVec 8)) :
    ∀ l : List (List (BitVec 8) × List (BitVec 8)),
      (DirGhost.setOrPush n bs l).length ≤ l.length + 1
  | [] => by simp [DirGhost.setOrPush]
  | e :: es => by
    by_cases he : e.1 = n
    · simp [DirGhost.setOrPush, he]
    · simp [DirGhost.setOrPush, he, setOrPush_length_le n bs es]

theorem mem_setOrPush_self (n bs : List (BitVec 8))
    (l : List (List (BitVec 8) × List (BitVec 8))) :
    n ∈ (DirGhost.setOrPush n bs l).map Prod.fst :=
  List.mem_map.2 ⟨(n, bs), List.mem_of_find?_eq_some (DirGhost.find_setOrPush_self n bs l), rfl⟩

/-- `DirGhost.put` of a record in `Scope` for `peer` preserves `CliSessInv`. -/
theorem CliSessInv.put {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost} {d : DirGhost}
    {r : SessionRecord (List (BitVec 8))} (h : CliSessInv rd F0 pathOk Scope peer d)
    (hr : Scope r) :
    CliSessInv rd F0 pathOk Scope peer
      (d.put (addressText peer.val) (E2E.Record.encodeRecord r)) where
  nameLt := h.nameLt
  textLt := h.textLt
  pathLt := h.pathLt
  pathOk := h.pathOk
  getOk := ⟨_, DirGhost.get_put_self rd F0 d _ _, Or.inr ⟨r, rfl, hr⟩⟩
  changedLt := by
    obtain ⟨hlt, hroom⟩ := h.changedLt
    refine ⟨?_, Or.inr (mem_setOrPush_self _ _ _)⟩
    show (DirGhost.setOrPush _ _ d.changed).length < 2 ^ 32
    rcases hroom with hroom | hmem
    · exact Nat.lt_of_le_of_lt (setOrPush_length_le _ _ _) hroom
    · rw [setOrPush_length_of_mem hmem]; exact hlt

theorem cliSessionStoreSpec_storeUpdate_inv {A : RustAlloc} {b : BitVec 64} {rd : ReadRule}
    {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {d : DirGhost} {rem : AddrVal} {r : SessionRecord (List (BitVec 8))} {ans : Except Unit Unit}
    (h : CliSessInv rd F0 pathOk Scope peer d)
    (hrem : (cliSessionStoreSpec A b rd F0 pathOk Scope peer s1 s2 s3 s4).addrOk rem)
    (hr : (cliSessionStoreSpec A b rd F0 pathOk Scope peer s1 s2 s3 s4).RecOk r) :
    CliSessInv rd F0 pathOk Scope peer
      ((cliSessionStoreSpec A b rd F0 pathOk Scope peer s1 s2 s3 s4).storeUpdate d rem r ans) := by
  have hrem' : rem = peer.val := hrem
  subst hrem'
  exact h.put hr.1

/-! ## Entry-address rewrites -/

section
variable {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}

theorem cliKitProg_eq :
    tripleRatchetProgAtExt b (tripleRatchetExterns C ctl abs) = tripleRatchetProgAt b C ctl abs :=
  rfl

theorem cliSessLoadShim_fnAddr {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr sessLoadShimName = b + cliSessLoadShimOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, sessLoadShim_fnOff, cliSessLoadShimOff]

theorem cliSessStoreShim_fnAddr {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr sessStoreShimName = b + cliSessStoreShimOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, sessStoreShim_fnOff,
    cliSessStoreShimOff]

theorem cliSessLoadPoll_fnAddr {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr sessLoadPollName = b + cliSessLoadPollOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, sessLoadPoll_fnOff, cliSessLoadPollOff]

theorem cliSessStorePoll_fnAddr {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr sessStorePollName = b + cliSessStorePollOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, sessStorePoll_fnOff,
    cliSessStorePollOff]

theorem cliSess_kitProg {α : Type} {spec : Spec α} {name : String} {off : BitVec 64}
    (haddr : ∀ ext : String → Option (State → State),
      (tripleRatchetProgAtExt b ext).fnAddr name = b + off)
    (h : subroutine_ok (tripleRatchetProgAtExt b (tripleRatchetExterns C ctl abs))
      ((tripleRatchetProgAtExt b (tripleRatchetExterns C ctl abs)).fnAddr name) spec) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) (b + off) spec := by
  rw [haddr] at h
  exact h

end

end CryptoVerification.SignalSession.Cli.KitInst

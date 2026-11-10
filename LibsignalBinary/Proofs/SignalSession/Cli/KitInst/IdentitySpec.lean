/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec

/-!
# CLI `IdentityFiles` Store Specification

Defines the pure store invariant `CliIdInv`, the separation-logic store predicate `cliIdStoreAt`,
and the concrete `IdentityStoreSpec` instance `cliIdentityStoreSpec` for
`IdentityFiles { own: Dir, peers: Dir }`, together with its vtable, quietness, `futDrop`, and
invariant-preservation lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)

/-! ## Store invariant -/

/-- Pure invariant of `IdentityFiles` at peer `peer` and initial file table `F0`: `u32` name and
path bounds for `Dir::get`/`Dir::put`, path guard `pathOk` on `identities/<name>`, a well-formed
(`IdFileWf`) read result for `peer`, and capacity in `peers.changed` for one `put`. -/
structure CliIdInv (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (peer : AddrGhost) (g : IdGhost) : Prop where
  nameLt : peer.name.bytes.length < 2 ^ 32
  pathLt : g.peers.path.length < 2 ^ 32
  pathOk : pathOk (pathOf g.peers.path peer.val.name)
  getOk : ∃ bs, g.peers.get rd F0 peer.val.name = .ok bs ∧ IdFileWf bs
  changedLt : g.peers.changed.length < 2 ^ 32 ∧
    (g.peers.changed.length + 1 < 2 ^ 32 ∨ peer.val.name ∈ g.peers.changed.map Prod.fst)

/-- `IdentityFiles` layout at `self`: `own` at `+0x00`, `peers` at `+0x28`, and `CliIdInv`. -/
def cliIdStoreAt (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost) (self : BitVec 64) (g : IdGhost) :
    SepProp :=
  ⌜CliIdInv rd F0 pathOk peer g⌝ ∗ dirAt A self g.own ∗ dirAt A (self + 0x28#64) g.peers

/-! ## Store kit specification -/

/-- Concrete `IdentityStoreSpec` for CLI `IdentityFiles` at peer `peer` and initial files `F0`.

`identityAt` owns the full `0x50`-byte `IdentityFiles` struct (`own` at `+0x00`, `peers` at
`+0x28`) while leaving `own` unchanged across trust and save updates. `trustRel` is
direction-independent (trust-on-first-use), and `saveRel` excludes `.error` (`IdFileWf` rules out
key-decode errors). -/
def cliIdentityStoreSpec (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (trustShimStk trustPollStk saveShimStk savePollStk : Nat) : IdentityStoreSpec A b where
  id_vt := b + cliIdVtOff
  IdState := IdGhost
  identityAt := cliIdStoreAt A rd F0 pathOk peer
  addrOk := fun rem => rem = peer.val
  envOk := fun f => f = F0
  fdsOk := fun fs => FdsGe3Closed fs
  trustUpdate := fun g _ _ _ _ => g
  saveUpdate := fun g rem k _ => g.saveUpd rd F0 rem k
  trustRel := fun g rem k _ ans => ∃ t, g.trusted rd F0 rem k = .ok t ∧ ans = .ok t
  saveRel := fun g rem k ans => ∃ c, g.saveAns rd F0 rem k = .ok c ∧ ans = .ok c
  trustEvs := fun _ _ _ _ => []
  saveEvs := fun _ _ _ => []
  trustShimOff := cliIdTrustShimOff
  trustFutVtOff := cliIdTrustFutVtOff
  trustPollOff := cliIdTrustPollOff
  trustFutDropOff := cliIdFutDropOff
  trustBoxSize := 32
  saveShimOff := cliIdSaveShimOff
  saveFutVtOff := cliIdSaveFutVtOff
  savePollOff := cliIdSavePollOff
  saveFutDropOff := cliIdFutDropOff
  saveBoxSize := 32
  trustShimStack := trustShimStk
  trustPollStack := trustPollStk
  saveShimStack := saveShimStk
  savePollStack := savePollStk
  trustBoxAt := idTrustBoxAt
  saveBoxAt := idSaveBoxAt
  trustBoxAt_memRegion := (hookIdentityStoreSpecAt A b (b + cliIdVtOff)).trustBoxAt_memRegion
  saveBoxAt_memRegion := (hookIdentityStoreSpecAt A b (b + cliIdVtOff)).saveBoxAt_memRegion
  trustBoxSize_ne_zero := by decide
  saveBoxSize_ne_zero := by decide
  trustBoxSize_lt := by decide
  saveBoxSize_lt := by decide
  trustFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)
  saveFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)

section
variable {A : RustAlloc} {img : Obj.Image} {rd : ReadRule} {F0 : FsFiles}
  {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}

theorem cliIdKitOffsets :
    CliIdKitOffsets img (cliIdentityStoreSpec A img.base rd F0 pathOk peer s1 s2 s3 s4) where
  idVt := rfl
  saveShim := rfl
  trustShim := rfl
  saveFutVt := rfl
  trustFutVt := rfl
  savePoll := rfl
  trustPoll := rfl
  saveFutDrop := rfl
  trustFutDrop := rfl
  saveBoxSize := rfl
  trustBoxSize := rfl

/-- Vtable validity (`IdentityVtablesOk`) for `cliIdentityStoreSpec`. -/
theorem cliIdentityStoreSpec_vtablesOk (himg : Obj.Loads libsignalSessionImage img) :
    IdentityVtablesOk img (cliIdentityStoreSpec A img.base rd F0 pathOk peer s1 s2 s3 s4) :=
  cliIdentityVtablesOk himg cliIdKitOffsets

/-- `cliIdentityStoreSpec` emits no filesystem trace events (`Quiet`). -/
theorem cliIdentityStoreSpec_quiet :
    (cliIdentityStoreSpec A img.base rd F0 pathOk peer s1 s2 s3 s4).Quiet :=
  ⟨fun _ _ _ _ => by simp [cliIdentityStoreSpec, NoFsEv],
    fun _ _ _ => by simp [cliIdentityStoreSpec, NoFsEv]⟩

end

section
variable {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F0 : FsFiles}
  {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
  {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}

theorem cliIdentityStoreSpec_trustFutDrop :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).trustFutDropOff)
      futDropSpec :=
  cliIdFutDrop_ok

theorem cliIdentityStoreSpec_saveFutDrop :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (b + (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).saveFutDropOff)
      futDropSpec :=
  cliIdFutDrop_ok

end

/-! ## Invariant preservation and answer totality -/

section
variable {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
  {g : IdGhost}

theorem CliIdInv.peer_ok (h : CliIdInv rd F0 pathOk peer g) :
    ∃ o, g.peer rd F0 peer.val = .ok o := by
  obtain ⟨bs, hget, hwf⟩ := h.getOk
  rcases hwf with rfl | ⟨k, rfl⟩
  · refine ⟨none, ?_⟩
    unfold IdGhost.peer
    rw [hget]
    exact (idPeerAns_bind (gr := .ok []) (p := .ok none) rfl).symm
  · refine ⟨some k, ?_⟩
    have hk : IdPeerAns (.ok k.serialize) (.ok (some k)) := ⟨k, rfl, rfl⟩
    unfold IdGhost.peer
    rw [hget]
    exact (idPeerAns_bind hk).symm

theorem CliIdInv.trusted_ok (h : CliIdInv rd F0 pathOk peer g) (k : IdentityKey) :
    ∃ t, g.trusted rd F0 peer.val k = .ok t := by
  obtain ⟨o, ho⟩ := h.peer_ok
  unfold IdGhost.trusted
  rw [ho]
  exact ⟨_, rfl⟩

theorem CliIdInv.saveAns_ok (h : CliIdInv rd F0 pathOk peer g) (k : IdentityKey) :
    ∃ c, g.saveAns rd F0 peer.val k = .ok c := by
  obtain ⟨o, ho⟩ := h.peer_ok
  unfold IdGhost.saveAns
  rw [ho]
  exact ⟨_, rfl⟩

theorem CliIdInv.saveUpd_eq (h : CliIdInv rd F0 pathOk peer g) (k : IdentityKey) :
    g.saveUpd rd F0 peer.val k = { g with peers := g.peers.put peer.val.name k.serialize } := by
  obtain ⟨o, ho⟩ := h.peer_ok
  unfold IdGhost.saveUpd
  rw [ho]

theorem CliIdInv.fileWf (h : CliIdInv rd F0 pathOk peer g) :
    ∀ bs, g.peers.get rd F0 peer.val.name = .ok bs → IdFileWf bs := by
  obtain ⟨bs', hget, hwf⟩ := h.getOk
  intro bs hbs
  rw [hget] at hbs
  exact Except.ok.inj hbs ▸ hwf

/-- `IdGhost.saveUpd` preserves `CliIdInv`. -/
theorem CliIdInv.saveUpd (h : CliIdInv rd F0 pathOk peer g) (k : IdentityKey) :
    CliIdInv rd F0 pathOk peer (g.saveUpd rd F0 peer.val k) := by
  rw [h.saveUpd_eq k]
  refine ⟨h.nameLt, h.pathLt, h.pathOk,
    ⟨_, DirGhost.get_put_self rd F0 g.peers _ _, Or.inr ⟨k, rfl⟩⟩, ?_⟩
  obtain ⟨hlt, hroom⟩ := h.changedLt
  refine ⟨?_, Or.inr (mem_setOrPush_self _ _ _)⟩
  show (DirGhost.setOrPush _ _ g.peers.changed).length < 2 ^ 32
  rcases hroom with hroom | hmem
  · exact Nat.lt_of_le_of_lt (setOrPush_length_le _ _ _) hroom
  · rw [setOrPush_length_of_mem hmem]; exact hlt

end

section
variable {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F0 : FsFiles}
  {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {g : IdGhost}
  {rem : AddrVal} {k : IdentityKey}

theorem cliIdentityStoreSpec_saveUpdate_inv {ans : Except Unit IdentityChange}
    (h : CliIdInv rd F0 pathOk peer g)
    (hrem : (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).addrOk rem) :
    CliIdInv rd F0 pathOk peer
      ((cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).saveUpdate g rem k ans) := by
  have hrem' : rem = peer.val := hrem
  subst hrem'
  exact h.saveUpd k

theorem cliIdentityStoreSpec_saveUpdate_own {ans : Except Unit IdentityChange} :
    ((cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).saveUpdate g rem k ans).own =
      g.own := by
  show (g.saveUpd rd F0 rem k).own = g.own
  unfold IdGhost.saveUpd
  split <;> rfl

theorem cliIdentityStoreSpec_trustUpdate_eq {d : Direction} {ans : Except Unit Bool} :
    (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).trustUpdate g rem k d ans = g :=
  rfl

theorem cliIdentityStoreSpec_trustRel {d : Direction} (h : CliIdInv rd F0 pathOk peer g)
    (hrem : (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).addrOk rem) :
    (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).trustRel g rem k d
      (g.trusted rd F0 rem k) := by
  have hrem' : rem = peer.val := hrem
  subst hrem'
  obtain ⟨t, ht⟩ := h.trusted_ok k
  exact ⟨t, ht, ht⟩

theorem cliIdentityStoreSpec_saveRel (h : CliIdInv rd F0 pathOk peer g)
    (hrem : (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).addrOk rem) :
    (cliIdentityStoreSpec A b rd F0 pathOk peer s1 s2 s3 s4).saveRel g rem k
      (g.saveAns rd F0 rem k) := by
  have hrem' : rem = peer.val := hrem
  subst hrem'
  obtain ⟨c, hc⟩ := h.saveAns_ok k
  exact ⟨c, hc, hc⟩

end

/-! ## Entry-address rewrites -/

section
variable {b : BitVec 64}

theorem cliIdSaveShim_fnAddr {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr idSaveShimName = b + cliIdSaveShimOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idSaveShim_fnOff, cliIdSaveShimOff]

theorem cliIdTrustShim_fnAddr {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr idTrustShimName = b + cliIdTrustShimOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idTrustShim_fnOff, cliIdTrustShimOff]

theorem cliIdSavePoll_fnAddr {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr idSavePollName = b + cliIdSavePollOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idSavePoll_fnOff, cliIdSavePollOff]

theorem cliIdTrustPoll_fnAddr {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr idTrustPollName = b + cliIdTrustPollOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idTrustPoll_fnOff, cliIdTrustPollOff]

end

end CryptoVerification.SignalSession.Cli.KitInst

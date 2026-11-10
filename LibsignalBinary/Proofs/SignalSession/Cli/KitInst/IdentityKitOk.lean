/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitE
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOneX
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShim
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustShim

/-!
# CLI `IdentityStoreKitOkIE` Assembly

Assembles `StoreKit.Identity.IdentityStoreKitOkIE` for `cliIdentityStoreSpec` from the
`IdentityFiles` shim, poll, and `futDrop` contracts over an arbitrary allocator, `ReadRule`,
initial file table, and external-hook map.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst.IdKit

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.Store
open CryptoVerification.SignalSession.Cli.MainHops

/-! ## Stack bounds -/

abbrev trustShimNeed : Nat := 0x30 + extHookStack

abbrev saveShimNeed : Nat := 0x30 + extHookStack

abbrev growOneDirNeed : Nat := 0x40 + CryptoVerification.LibsignalTripleRatchet.finishGrowStackX

abbrev dirPutStrNeed : Nat := 0x50 + max growOneDirNeed extHookStack

abbrev trustPollNeed (readStk : Nat) : Nat :=
  0xc0 + max (max (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩) 0x60) (max 64 extHookStack)

abbrev savePollNeed (readStk : Nat) : Nat :=
  0xd0 + max (max (max (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩) dirPutStrNeed) (max 0x60 64))
    (max publicKeySerializeStackX extHookStack)

private theorem panic_absorb_own {φ : Prop} {own R : SepProp} {m : Memory}
    (h : m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ (own ∗ R)) :
    m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ R := by
  have h1 : m ⊨ ⌜φ⌝ ∗ ((anyHeap ∗ own) ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) h
  rw [satisfies_pure_sepConj] at h1
  have h2 : m ⊨ ⌜φ⌝ ∗ (anyHeap ∗ R) := by
    rw [satisfies_pure_sepConj]
    exact ⟨h1.1, Satisfies.mono (sepConj_mono_left (entails_anyHeap (anyHeap ∗ own))) h1.2⟩
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) h2

/-! ## Kit assembly -/

private theorem cliIdKitOkIE_of_polls {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : AllocContractsX img A ext)
    (hTrust : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName)
      (idTrustPollSpec rd cliWrOk A img s2))
    (hSave : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName)
      (idSavePollSpec rd cliWrOk A img s4))
    (hs1 : trustShimNeed ≤ s1) (hs3 : saveShimNeed ≤ s3) :
    StoreKit.Identity.IdentityStoreKitOkIE img
      (cliIdentityStoreSpec A img.base rd F0 cliWrOk peer s1 s2 s3 s4) ext := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := RunSkeleton.base_aligned himg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- trustShim
    have h := IdTrustShim.idTrustShim_ok_of_deps hC hs1 hb
    rw [cliIdTrustShim_fnAddr] at h
    exact h
  · -- trustPoll
    have h := hTrust
    rw [cliIdTrustPoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨x, d, self, g⟩ R s0 hpre
    dsimp only [kitTrustPollSpecI, Spec.inImage, withLogOff, kitTrustPollSpecE,
      kitTrustPollSpec, withEnvPre, cliIdentityStoreSpec, cliIdStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ x.call.addr.val = peer.val⌝ ∗
        (⌜CliIdInv rd F0 cliWrOk peer g⌝ ∗
        (idTrustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
          dirAt A (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
          protocolAddressAt A x.call.addr x.call.addrA ∗
          (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ logOff img ∗
          A.pool ∗ stackAt s0.sp s2 ∗ (dirAt A self g.own ∗ R))))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, haddr⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : x.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hhop_pure :
        s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
          x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
          cliWrOk (pathOf g.peers.path x.call.addr.val.name) ∧
          ∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs :=
      ⟨hx0, hx8, hname ▸ hinv.nameLt, hinv.pathLt, haddr ▸ hinv.pathOk, fun bs hbs => by
        rw [hfiles, haddr] at hbs
        exact hinv.fileWf bs hbs⟩
    have hm_hop :
        s0.mem ⊨ (idTrustPollSpec rd cliWrOk A img s2).pre (⟨x, self, g.peers⟩, directionByte d) s0 ∗
          (dirAt A self g.own ∗ R) := by
      dsimp only [idTrustPollSpec, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
            x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
            cliWrOk (pathOf g.peers.path x.call.addr.val.name) ∧
            ∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs⌝ ∗
          (idTrustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
            dirAt A (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ logOff img ∗
            A.pool ∗ stackAt s0.sp s2 ∗ (dirAt A self g.own ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hhop_pure, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨(⟨x, self, g.peers⟩, directionByte d), dirAt A self g.own ∗ R, hm_hop, ?_,
      fun _ hpan => panic_absorb_own hpan⟩
    intro sf hpost
    dsimp only [idTrustPollSpec, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨gr, p, ⟨⟨hgr, htr⟩, hpeer⟩, hm⟩ := hpost
    rw [hfiles] at hgr
    have ht1 : g.trusted rd F0 x.call.addr.val x.call.key = idTrustOf p x.call.key :=
      IdGhost.trusted_of_peerAns (hgr ▸ hpeer)
    obtain ⟨t, ht0⟩ := hinv.trusted_ok x.call.key
    have ht : g.trusted rd F0 x.call.addr.val x.call.key = .ok t := haddr.symm ▸ ht0
    have hans : idTrustOf p x.call.key = .ok t := ht1.symm.trans ht
    have hout_eq : idTrustOutAt A x.out (idTrustOf p x.call.key) =
        trustPollOutAt img.base x.out (.ok t) :=
      hans.symm ▸ idTrustOutAt_ok A img.base x.out t
    rw [hout_eq] at hm
    dsimp only [kitTrustPollSpecI, Spec.inImage, withLogOff, kitTrustPollSpecE,
      kitTrustPollSpec, withEnvPre, cliIdentityStoreSpec, cliIdStoreAt]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨.ok t, ?_⟩
    have hgoal : sf.mem ⊨
        ⌜(∃ t', g.trusted rd F0 x.call.addr.val x.call.key = .ok t' ∧
            (Except.ok t : Except Unit Bool) = .ok t') ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliIdInv rd F0 cliWrOk peer g⌝ ∗
          (trustPollOutAt img.base x.out (.ok t) ∗
            idTrustBoxAt x.fut self x.call.addrA x.call.keyA 1#8 (directionByte d) ∗
            dirAt A self g.own ∗ dirAt A (self + 0x28#64) g.peers ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
            logOff img ∗ A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨⟨t, ht, rfl⟩, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  · -- trustFutDrop
    exact cliIdentityStoreSpec_trustFutDrop_ext
  · -- saveShim
    have h := IdSaveShim.idSaveShim_ok_of_deps hC hs3 hb
    rw [cliIdSaveShim_fnAddr] at h
    exact h
  · -- savePoll
    have h := hSave
    rw [cliIdSavePoll_fnAddr] at h
    refine subroutine_ok_map_panic h ?_
    rintro ⟨x, self, g⟩ R s0 hpre
    dsimp only [kitSavePollSpecI, Spec.inImage, withLogOff, kitSavePollSpecE,
      kitSavePollSpec, withEnvPre, cliIdentityStoreSpec, cliIdStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ x.call.addr.val = peer.val⌝ ∗
        (⌜CliIdInv rd F0 cliWrOk peer g⌝ ∗
        (idSaveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
          dirAt A (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
          protocolAddressAt A x.call.addr x.call.addrA ∗
          (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ logOff img ∗
          A.pool ∗ stackAt s0.sp s4 ∗ (dirAt A self g.own ∗ R))))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, haddr⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : x.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hhop_pure :
        s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
          x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
          g.peers.changed.length < 2 ^ 32 ∧
          cliWrOk (pathOf g.peers.path x.call.addr.val.name) ∧
          ∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs :=
      ⟨hx0, hx8, hname ▸ hinv.nameLt, hinv.pathLt, hinv.changedLt.1, haddr ▸ hinv.pathOk,
        fun bs hbs => by
          rw [hfiles, haddr] at hbs
          exact hinv.fileWf bs hbs⟩
    have hm_hop :
        s0.mem ⊨ (idSavePollSpec rd cliWrOk A img s4).pre ⟨x, self, g.peers⟩ s0 ∗
          (dirAt A self g.own ∗ R) := by
      dsimp only [idSavePollSpec, Spec.inImage]
      have h1 : s0.mem ⊨
          ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
            x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
            g.peers.changed.length < 2 ^ 32 ∧
            cliWrOk (pathOf g.peers.path x.call.addr.val.name) ∧
            ∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs⌝ ∗
          (idSaveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
            dirAt A (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ logOff img ∗
            A.pool ∗ stackAt s0.sp s4 ∗ (dirAt A self g.own ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hhop_pure, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨x, self, g.peers⟩, dirAt A self g.own ∗ R, hm_hop, ?_,
      fun _ hpan => panic_absorb_own hpan⟩
    intro sf hpost
    dsimp only [idSavePollSpec, Spec.inImage] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨gr, p, ⟨⟨hgr, htr⟩, hpeer⟩, hm⟩ := hpost
    rw [hfiles] at hgr
    obtain ⟨hs1_eq, hs2_eq⟩ := IdGhost.saveAns_of_peerAns (k := x.call.key) (hgr ▸ hpeer)
    obtain ⟨c, hc0⟩ := hinv.saveAns_ok x.call.key
    have hc : g.saveAns rd F0 x.call.addr.val x.call.key = .ok c := haddr.symm ▸ hc0
    have hans : idSaveOf p x.call.key = .ok c := hs1_eq.symm.trans hc
    have hout_eq : idSaveOutAt A x.out (idSaveOf p x.call.key) =
        savePollOutAt img.base x.out (.ok c) :=
      hans.symm ▸ idSaveOutAt_ok A img.base x.out c
    have hown_eq : dirAt A self g.own =
        dirAt A self (g.saveUpd rd F0 x.call.addr.val x.call.key).own :=
      (congrArg (dirAt A self)
        (cliIdentityStoreSpec_saveUpdate_own (A := A) (b := img.base) (rd := rd) (F0 := F0)
          (pathOk := cliWrOk) (peer := peer) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
          (g := g) (rem := x.call.addr.val) (k := x.call.key) (ans := .ok c))).symm
    have hpeers_eq :
        dirAt A (self + 0x28#64) (idSavePeers g.peers x.call.addr.val.name x.call.key p) =
          dirAt A (self + 0x28#64) (g.saveUpd rd F0 x.call.addr.val x.call.key).peers :=
      congrArg (dirAt A (self + 0x28#64)) (congrArg IdGhost.peers hs2_eq).symm
    have hinv_upd : CliIdInv rd F0 cliWrOk peer (g.saveUpd rd F0 x.call.addr.val x.call.key) :=
      cliIdentityStoreSpec_saveUpdate_inv (A := A) (b := img.base)
        (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (k := x.call.key) (ans := .ok c) hinv haddr
    rw [hout_eq, hpeers_eq, hown_eq] at hm
    dsimp only [kitSavePollSpecI, Spec.inImage, withLogOff, kitSavePollSpecE,
      kitSavePollSpec, withEnvPre, cliIdentityStoreSpec, cliIdStoreAt]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨.ok c, ?_⟩
    have hgoal : sf.mem ⊨
        ⌜(∃ c', g.saveAns rd F0 x.call.addr.val x.call.key = .ok c' ∧
            (Except.ok c : Except Unit IdentityChange) = .ok c') ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliIdInv rd F0 cliWrOk peer (g.saveUpd rd F0 x.call.addr.val x.call.key)⌝ ∗
          (savePollOutAt img.base x.out (.ok c) ∗
            idSaveBoxAt x.fut self x.call.addrA x.call.keyA 1#8 ∗
            dirAt A self (g.saveUpd rd F0 x.call.addr.val x.call.key).own ∗
            dirAt A (self + 0x28#64) (g.saveUpd rd F0 x.call.addr.val x.call.key).peers ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
            logOff img ∗ A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨⟨c, hc, rfl⟩, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hinv_upd, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  · -- saveFutDrop
    exact cliIdentityStoreSpec_saveFutDrop_ext

/-- Assemble `IdentityStoreKitOkIE` for `cliIdentityStoreSpec` from `Dir::get`,
`Dir::put::<&str>`, and `PublicKey::eq` contracts. -/
theorem cliIdKitOkIE {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooks img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hEq : Getters.PublicKeyEqOkExt img.base ext)
    (hs1 : trustShimNeed ≤ s1) (hs2 : trustPollNeed readStk ≤ s2)
    (hs3 : saveShimNeed ≤ s3) (hs4 : savePollNeed readStk ≤ s4) :
    StoreKit.Identity.IdentityStoreKitOkIE img
      (cliIdentityStoreSpec A img.base rd F0 cliWrOk peer s1 s2 s3 s4) ext := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := RunSkeleton.base_aligned himg
  have hC : AllocContractsX img A ext := hh.alloc
  have hDec := RunSkeleton.identityKeyDecode_ok (A := A) (ext := ext) himg
  have hGet := Get.dirGet_ok_of_deps (pathOk := cliWrOk) himg (fun _ hp => hp.2) hC
    hh.memcpyRO hh.bcmp (RunSkeleton.path_ok himg hh (Nat.le_refl RunSkeleton.pathNeed))
    hRead hh.fs (Nat.le_refl (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩)) hb
  have hGrow := GrowOne.growOneDir_ok_x hC (Nat.le_refl growOneDirNeed) hb
  have hPut := PutStr.dirPutStr_ok_of_deps hC hh.memcpyRO hh.bcmp hGrow
    (Nat.le_refl dirPutStrNeed) hb
  exact cliIdKitOkIE_of_polls himg hC
    (IdTrustPoll.idTrustPoll_ok_of_deps hC hGet hDec hEq hs2 hb)
    (IdSavePoll.idSavePoll_ok_of_deps hC hGet hPut hDec hEq hs4 hb)
    hs1 hs3

private theorem path_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img RunSkeleton.pathNeed) :=
  Path.path_ok_of_deps_withStack hh.alloc hh.memcpyRO
    (RunSkeleton.reserve_ok_ext hh (Nat.le_refl doReserveStackX))
    (Nat.le_refl RunSkeleton.pathNeed) (RunSkeleton.base_aligned himg)

private theorem trustPoll_hstk_ext32 {readStk s2 : Nat} (hs2 : trustPollNeed readStk ≤ s2) :
    0xc0 + max (max (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩) 0x60)
      Getters.publicKeyEqStackExt ≤ s2 := by
  dsimp only [trustPollNeed, extHookStack, Getters.publicKeyEqStackExt,
    RunSkeleton.RunBudgets.dirGetNeed] at hs2 ⊢
  omega

private theorem savePoll_hstk_ext32 {readStk s4 : Nat} (hs4 : savePollNeed readStk ≤ s4) :
    0xd0 + max (max (max (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩) dirPutStrNeed) 0x60)
      (max publicKeySerializeStackX Getters.publicKeyEqStackExt) ≤ s4 := by
  dsimp only [savePollNeed, extHookStack, Getters.publicKeyEqStackExt,
    RunSkeleton.RunBudgets.dirGetNeed] at hs4 ⊢
  omega

/-- Variant of `cliIdKitOkIE` taking `RunHooksExt` and `PublicKeyEqOkExt32`. -/
theorem cliIdKitOkIE_ext32 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {rd : ReadRule} {F0 : FsFiles} {peer : AddrGhost} {readStk s1 s2 s3 s4 : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec rd cliWrOk A img readStk))
    (hEq : Getters.PublicKeyEqOkExt32 img.base ext)
    (hs1 : trustShimNeed ≤ s1) (hs2 : trustPollNeed readStk ≤ s2)
    (hs3 : saveShimNeed ≤ s3) (hs4 : savePollNeed readStk ≤ s4) :
    StoreKit.Identity.IdentityStoreKitOkIE img
      (cliIdentityStoreSpec A img.base rd F0 cliWrOk peer s1 s2 s3 s4) ext := by
  have hb : (img.base &&& 0xfff#64) = 0#64 := RunSkeleton.base_aligned himg
  have hC : AllocContractsX img A ext := hh.alloc
  have hDec := RunSkeleton.identityKeyDecode_ok (A := A) (ext := ext) himg
  have hGet := Get.dirGet_ok_of_deps_withStack (pathOk := cliWrOk) himg (fun _ hp => hp.2) hC
    hh.memcpyRO hh.bcmp (path_ok_ext himg hh)
    hRead hh.fs (Nat.le_refl (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩)) hb
  have hGrow := GrowOne.growOneDir_ok_x hC (Nat.le_refl growOneDirNeed) hb
  have hPut := PutStr.dirPutStr_ok_of_deps_withStack hC hh.memcpyRO hh.bcmp hGrow
    (Nat.le_refl dirPutStrNeed) hb
  exact cliIdKitOkIE_of_polls himg hC
    (IdTrustPoll.idTrustPoll_ok_of_deps_ext32 hC hGet hDec hEq (trustPoll_hstk_ext32 hs2) hb)
    (IdSavePoll.idSavePoll_ok_of_deps_ext32 hC hGet hPut hDec hEq (savePoll_hstk_ext32 hs4) hb)
    hs1 hs3

end CryptoVerification.SignalSession.Cli.KitInst.IdKit

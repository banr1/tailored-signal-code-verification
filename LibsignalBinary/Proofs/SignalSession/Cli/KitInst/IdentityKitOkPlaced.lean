/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrowPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustShimPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShimPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed CLI `IdentityStoreKitPlacedOkI` Assembly

Relocatable `[LibsignalPlacement]` `IdentityStoreSpec` and `IdentityStoreKitPlacedOkI`
assembly for CLI `IdentityFiles`, composing the `Dir` helpers with the `IdentityFiles`
shims, polls, and `futDrop`.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst.IdKit

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding withLsCodeRoLoaded LibsignalCodeRoLoaded
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

/-- Relocatable `IdentityStoreSpec` for CLI `IdentityFiles` with placed block bases and
`.rodata` symbol addresses. -/
def cliIdentityKitSpecPlaced [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (trustShimStk trustPollStk saveShimStk savePollStk : Nat)
    (vtSym : String := cliIdentityVtRoSym) :
    IdentityStoreSpec A 0#64 :=
  { cliIdentityStoreSpec A 0#64 rd F0 pathOk peer
      trustShimStk trustPollStk saveShimStk savePollStk with
    id_vt := lsρ vtSym
    trustShimOff := lsmpl.base 601
    trustFutVtOff := lsρ idTrustFutVtSym
    trustPollOff := lsmpl.base 566
    trustFutDropOff := lsDropOffPlaced
    saveShimOff := lsmpl.base 600
    saveFutVtOff := lsρ idSaveFutVtSym
    savePollOff := lsmpl.base 565
    saveFutDropOff := lsDropOffPlaced
    trustFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    saveFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

theorem cliIdentityKitSpecPlaced_offsets [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} (hDropNz : lsmpl.base 547 ≠ 0#64) :
    CliIdKitOffsetsPlaced
      (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 cliIdentityVtRoSym) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, lsDropOffPlaced_eq hDropNz, lsDropOffPlaced_eq hDropNz,
    rfl, rfl⟩

theorem cliIdentityKitSpecPlaced_vtables [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} (hDropNz : lsmpl.base 547 ≠ 0#64) :
    IdentityVtablesPlacedOk
      (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 cliIdentityVtRoSym) :=
  cliIdentityVtablesPlacedOk (cliIdentityKitSpecPlaced_offsets hDropNz)

theorem cliIdentityKitSpecPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String} :
    (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym).Quiet :=
  ⟨fun _ _ _ _ => NoFsEv.nil, fun _ _ _ => NoFsEv.nil⟩

theorem cliIdentityKitSpecPlaced_saveUpdate_inv [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {g : IdGhost} {rem : AddrVal} {k : IdentityKey} {ans : Except Unit IdentityChange}
    (hinv : CliIdInv rd F0 pathOk peer g) (hrem : rem = peer.val) :
    CliIdInv rd F0 pathOk peer
      ((cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym).saveUpdate
        g rem k ans) :=
  cliIdentityStoreSpec_saveUpdate_inv (A := A) (b := 0#64)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (k := k) (ans := ans) hinv hrem

theorem cliIdentityKitSpecPlaced_saveUpdate_own [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {g : IdGhost} {rem : AddrVal} {k : IdentityKey} {ans : Except Unit IdentityChange} :
    ((cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym).saveUpdate
      g rem k ans).own = g.own :=
  cliIdentityStoreSpec_saveUpdate_own (A := A) (b := 0#64) (rd := rd) (F0 := F0)
    (pathOk := pathOk) (peer := peer) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
    (g := g) (rem := rem) (k := k) (ans := ans)

/-! ## Stack bounds -/

abbrev trustShimNeedPlaced : Nat := 0x30 + extHookStack

abbrev saveShimNeedPlaced : Nat := 0x30 + extHookStack

abbrev growOneDirNeedPlaced : Nat :=
  0x40 + CryptoVerification.LibsignalTripleRatchet.finishGrowStackX

abbrev dirPutStrNeedPlaced : Nat := 0x50 + max growOneDirNeedPlaced extHookStack

abbrev trustPollNeedPlaced (readStk : Nat) : Nat :=
  0xc0 + max (max (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩) 0x60) (max 64 extHookStack)

abbrev savePollNeedPlaced (readStk : Nat) : Nat :=
  0xd0 + max (max (max (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩) dirPutStrNeedPlaced)
      (max 0x60 64))
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

/-! ## Shims and `futDrop` -/

theorem cliIdTrustShim_rocl_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : AllocContractsXCliPlaced A H) (hpan : Store.PlacedCommon.CliPanicHooksPlaced H)
    (hs1 : trustShimNeedPlaced ≤ s1) (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym).trustShimOff)
      (withLsRoCl lsmpl
        (kitTrustShimSpec (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym))) := by
  have h601 := Store.IdTrustShim.idTrustShim_placed_ok_of_deps hC hpan hs1
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 601)
    h601 hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 601) _
  rw [BitVec.zero_add]
  refine subroutine_ok_mono hrocl (fun _ _ _ hp => hp) (fun ⟨_, _⟩ _ _ _ hq => ?_)
  dsimp only [withLsRoCl, kitTrustShimSpec, cliIdentityKitSpecPlaced, cliIdentityStoreSpec] at hq ⊢
  simpa only [BitVec.zero_add] using hq

theorem cliIdSaveShim_rocl_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : AllocContractsXCliPlaced A H) (hpan : Store.PlacedCommon.CliPanicHooksPlaced H)
    (hs3 : saveShimNeedPlaced ≤ s3) (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym).saveShimOff)
      (withLsRoCl lsmpl
        (kitSaveShimSpec (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym))) := by
  have h600 := Store.IdSaveShim.idSaveShim_placed_ok_of_deps hC hpan hs3
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 600)
    h600 hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 600) _
  rw [BitVec.zero_add]
  refine subroutine_ok_mono hrocl (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsRoCl, kitSaveShimSpec, cliIdentityKitSpecPlaced, cliIdentityStoreSpec] at hq ⊢
  simpa only [BitVec.zero_add] using hq

theorem cliIdFutDrop_rocl_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (0#64 + lsmpl.base 547) (withLsRoCl lsmpl futDropSpec) := by
  rw [BitVec.zero_add]
  exact ls_futDrop_ok_of_block (callerProg := callerProg)
    (StoreCalleesProofs.futDrop_block_placed_ok H) hblk (by decide) (by decide)

/-! ## `Dir` helpers and `idTrustPoll` -/

theorem cliDirGet_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunSkeleton.RunHooksPlaced A H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A readStk)))
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩)) :=
  Get.dirGet_placed_ok_of_deps hpathLen hh.alloc hh.panics hh.memcpyRO hh.bcmp
    (jPath := 589) (by decide) (by decide)
    (RunSkeleton.path_placed_ok (callerProg := lsProg_589 H) (i := 589) hh
      (Nat.le_refl RunSkeleton.pathNeed) (by decide))
    hjRead hjRead_unmut hRead (hh.fs (lsProg_589 H) 589)
    (Nat.le_refl (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩))

theorem cliIdTrustPoll_rocl_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {callerProg getProg eqProg : Program} {callerBlk getBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    (hC : AllocContractsXCliPlaced A H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212) (withLsCodeLoaded lsmpl Getters.publicKeyEqSpec))
    (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym).trustPollOff)
      (withLsRoCl lsmpl
        (kitTrustPollPlacedSpecI
          (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym))) := by
  have h566 := Store.IdTrustPoll.idTrustPoll_placed_ok_of_deps hC hGet
    (RecordCodecsBinary.IdentityKeyDecode.identityKey_decode_placed_ok H)
    hEq hs2 hGetBlk hGetUnmut (by decide) (by decide) hEqBlk hEqUnmut
  have h566_kit : subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withLsCodeRoLoaded lsmpl
        (kitTrustPollPlacedSpecI
          (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym))) := by
    refine subroutine_ok_map_panic h566 ?_
    rintro ⟨x, d, self, g⟩ R s0 hpre
    dsimp only [withLsCodeRoLoaded, kitTrustPollPlacedSpecI, withLsLogOff,
      kitTrustPollPlacedSpecE, kitTrustPollPlacedSpec, withEnvPre,
      cliIdentityKitSpecPlaced, cliIdentityStoreSpec, cliIdStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ x.call.addr.val = peer.val⌝ ∗
        (⌜CliIdInv rd F0 pathOk peer g⌝ ∗
        (idTrustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
          dirAt A (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
          protocolAddressAt A x.call.addr x.call.addrA ∗
          (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
          A.pool ∗ stackAt s0.sp s2 ∗ (dirAt A self g.own ∗ R))))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, haddr⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : x.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hhop_pure :
        s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
          x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
          pathOk (pathOf g.peers.path x.call.addr.val.name) ∧
          ∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs :=
      ⟨hx0, hx8, hname ▸ hinv.nameLt, hinv.pathLt, haddr ▸ hinv.pathOk, fun bs hbs => by
        rw [hfiles, haddr] at hbs
        exact hinv.fileWf bs hbs⟩
    have hm_hop :
        s0.mem ⊨ (idTrustPollSpecPlaced rd pathOk A s2).pre (⟨x, self, g.peers⟩, directionByte d) s0 ∗
          (dirAt A self g.own ∗ R) := by
      dsimp only [idTrustPollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
            x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
            pathOk (pathOf g.peers.path x.call.addr.val.name) ∧
            ∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs⌝ ∗
          (idTrustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
            dirAt A (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
            A.pool ∗ stackAt s0.sp s2 ∗ (dirAt A self g.own ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hhop_pure, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨(⟨x, self, g.peers⟩, directionByte d), dirAt A self g.own ∗ R, hm_hop, ?_,
      fun _ hpan => panic_absorb_own hpan⟩
    intro sf hpost
    dsimp only [idTrustPollSpecPlaced, withLsCodeRoLoaded] at hpost
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
        trustPollPlacedOutAt x.out (.ok t) :=
      hans.symm ▸ idTrustOutAt_ok A 0#64 x.out t
    rw [hout_eq] at hm
    dsimp only [withLsCodeRoLoaded, kitTrustPollPlacedSpecI, withLsLogOff,
      kitTrustPollPlacedSpecE, kitTrustPollPlacedSpec, withEnvPre,
      cliIdentityKitSpecPlaced, cliIdentityStoreSpec, cliIdStoreAt]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨.ok t, ?_⟩
    have hgoal : sf.mem ⊨
        ⌜(∃ t', g.trusted rd F0 x.call.addr.val x.call.key = .ok t' ∧
            (Except.ok t : Except Unit Bool) = .ok t') ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliIdInv rd F0 pathOk peer g⌝ ∗
          (trustPollPlacedOutAt x.out (.ok t) ∗
            idTrustBoxAt x.fut self x.call.addrA x.call.keyA 1#8 (directionByte d) ∗
            dirAt A self g.own ∗ dirAt A (self + 0x28#64) g.peers ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
            FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨⟨t, ht, rfl⟩, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  change subroutine_ok callerProg (0#64 + lsmpl.base 566) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 566)
    h566_kit hCallerBlk (by decide) (by decide)

/-! ## `idSavePoll` and kit bundles -/

theorem cliGrowOneDir_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : Store.PlacedCommon.CliPanicHooksPlaced H) :
    subroutine_ok (lsProg_586 H) (lsmpl.base 586)
      (growOneDirSpecPlaced A growOneDirNeedPlaced) :=
  GrowOne.Helpers.growOneDir_placed_of_bytes
    (GrowOne.Helpers.growOneDirBytes_placed_ok hpan
      (FinishGrow.cliFinishGrow_placed_caller_ok_x (callerProg := lsProg_586 H) (i := 586)
        hC (by decide)))
    (Nat.le_refl growOneDirNeedPlaced)

theorem cliDirPutStr_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunSkeleton.RunHooksPlaced A H) :
    subroutine_ok (lsProg_543 H) (lsmpl.base 543)
      (dirPutStrSpecPlaced A dirPutStrNeedPlaced) :=
  PutStr.dirPutStr_placed_ok_of_deps hh.alloc hh.panics hh.memcpyRO hh.bcmp
    (jGrow := 586) (by decide) (by decide)
    (cliGrowOneDir_placed_ok hh.alloc hh.panics)
    (Nat.le_refl dirPutStrNeedPlaced)

theorem cliIdSavePoll_rocl_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {callerProg getProg putProg eqProg : Program} {callerBlk getBlk putBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    (hC : AllocContractsXCliPlaced A H)
    (hpan : Store.PlacedCommon.CliPanicHooksPlaced H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩)))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (dirPutStrSpecPlaced A dirPutStrNeedPlaced))
    (hEq : subroutine_ok eqProg (lsmpl.base 212) (withLsCodeLoaded lsmpl Getters.publicKeyEqSpec))
    (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym).savePollOff)
      (withLsRoCl lsmpl
        (kitSavePollPlacedSpecI
          (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym))) := by
  have h565 := Store.IdSavePoll.idSavePoll_placed_ok_of_deps hC hpan hGet hPut
    (RecordCodecsBinary.IdentityKeyDecode.identityKey_decode_placed_ok H)
    hEq hs4 hGetBlk hGetUnmut hPutBlk hPutUnmut (by decide) (by decide) hEqBlk hEqUnmut
  have h565_kit : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (withLsCodeRoLoaded lsmpl
        (kitSavePollPlacedSpecI
          (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym))) := by
    refine subroutine_ok_map_panic h565 ?_
    rintro ⟨x, self, g⟩ R s0 hpre
    dsimp only [withLsCodeRoLoaded, kitSavePollPlacedSpecI, withLsLogOff,
      kitSavePollPlacedSpecE, kitSavePollPlacedSpec, withEnvPre,
      cliIdentityKitSpecPlaced, cliIdentityStoreSpec, cliIdStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ x.call.addr.val = peer.val⌝ ∗
        (⌜CliIdInv rd F0 pathOk peer g⌝ ∗
        (idSaveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
          dirAt A (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
          protocolAddressAt A x.call.addr x.call.addrA ∗
          (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
          A.pool ∗ stackAt s0.sp s4 ∗ (dirAt A self g.own ∗ R))))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, haddr⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : x.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hhop_pure :
        s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
          x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
          g.peers.changed.length < 2 ^ 32 ∧
          pathOk (pathOf g.peers.path x.call.addr.val.name) ∧
          ∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs :=
      ⟨hx0, hx8, hname ▸ hinv.nameLt, hinv.pathLt, hinv.changedLt.1, haddr ▸ hinv.pathOk,
        fun bs hbs => by
          rw [hfiles, haddr] at hbs
          exact hinv.fileWf bs hbs⟩
    have hm_hop :
        s0.mem ⊨ (idSavePollSpecPlaced rd pathOk A s4).pre ⟨x, self, g.peers⟩ s0 ∗
          (dirAt A self g.own ∗ R) := by
      dsimp only [idSavePollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
            x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
            g.peers.changed.length < 2 ^ 32 ∧
            pathOk (pathOf g.peers.path x.call.addr.val.name) ∧
            ∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs⌝ ∗
          (idSaveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
            dirAt A (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
            A.pool ∗ stackAt s0.sp s4 ∗ (dirAt A self g.own ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hhop_pure, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨x, self, g.peers⟩, dirAt A self g.own ∗ R, hm_hop, ?_,
      fun _ hpan => panic_absorb_own hpan⟩
    intro sf hpost
    dsimp only [idSavePollSpecPlaced, withLsCodeRoLoaded] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨gr, p, ⟨⟨hgr, htr⟩, hpeer⟩, hm⟩ := hpost
    rw [hfiles] at hgr
    obtain ⟨hs1_eq, hs2_eq⟩ := IdGhost.saveAns_of_peerAns (k := x.call.key) (hgr ▸ hpeer)
    obtain ⟨c, hc0⟩ := hinv.saveAns_ok x.call.key
    have hc : g.saveAns rd F0 x.call.addr.val x.call.key = .ok c := haddr.symm ▸ hc0
    have hans : idSaveOf p x.call.key = .ok c := hs1_eq.symm.trans hc
    have hout_eq : idSaveOutAt A x.out (idSaveOf p x.call.key) =
        savePollPlacedOutAt x.out (.ok c) :=
      hans.symm ▸ idSaveOutAt_ok A 0#64 x.out c
    have hown_eq : dirAt A self g.own =
        dirAt A self (g.saveUpd rd F0 x.call.addr.val x.call.key).own :=
      (congrArg (dirAt A self)
        (cliIdentityKitSpecPlaced_saveUpdate_own (A := A) (rd := rd) (F0 := F0)
          (pathOk := pathOk) (peer := peer) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
          (vtSym := vtSym)
          (g := g) (rem := x.call.addr.val) (k := x.call.key) (ans := .ok c))).symm
    have hpeers_eq :
        dirAt A (self + 0x28#64) (idSavePeers g.peers x.call.addr.val.name x.call.key p) =
          dirAt A (self + 0x28#64) (g.saveUpd rd F0 x.call.addr.val x.call.key).peers :=
      congrArg (dirAt A (self + 0x28#64)) (congrArg IdGhost.peers hs2_eq).symm
    have hinv_upd : CliIdInv rd F0 pathOk peer (g.saveUpd rd F0 x.call.addr.val x.call.key) :=
      cliIdentityKitSpecPlaced_saveUpdate_inv (A := A)
        (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (vtSym := vtSym)
        (k := x.call.key) (ans := .ok c) hinv haddr
    rw [hout_eq, hpeers_eq, hown_eq] at hm
    dsimp only [withLsCodeRoLoaded, kitSavePollPlacedSpecI, withLsLogOff,
      kitSavePollPlacedSpecE, kitSavePollPlacedSpec, withEnvPre,
      cliIdentityKitSpecPlaced, cliIdentityStoreSpec, cliIdStoreAt]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨.ok c, ?_⟩
    have hgoal : sf.mem ⊨
        ⌜(∃ c', g.saveAns rd F0 x.call.addr.val x.call.key = .ok c' ∧
            (Except.ok c : Except Unit IdentityChange) = .ok c') ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliIdInv rd F0 pathOk peer (g.saveUpd rd F0 x.call.addr.val x.call.key)⌝ ∗
          (savePollPlacedOutAt x.out (.ok c) ∗
            idSaveBoxAt x.fut self x.call.addrA x.call.keyA 1#8 ∗
            dirAt A self (g.saveUpd rd F0 x.call.addr.val x.call.key).own ∗
            dirAt A (self + 0x28#64) (g.saveUpd rd F0 x.call.addr.val x.call.key).peers ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
            FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨⟨c, hc, rfl⟩, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hinv_upd, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  change subroutine_ok callerProg (0#64 + lsmpl.base 565) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 565)
    h565_kit hCallerBlk (by decide) (by decide)

/-- Relocatable `IdentityStoreKitOkI` bundle carrying `withLsRoCl lsmpl` across all six
callbacks. -/
structure IdentityStoreKitPlacedRoClOkI [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64) (H : LibsignalHooks) : Prop where
  trustShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustShimOff) (withLsRoCl lsmpl (kitTrustShimSpec ikit))
  trustPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustPollOff)
      (withLsRoCl lsmpl (kitTrustPollPlacedSpecI ikit))
  trustFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustFutDropOff) (withLsRoCl lsmpl futDropSpec)
  saveShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.saveShimOff) (withLsRoCl lsmpl (kitSaveShimSpec ikit))
  savePoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.savePollOff)
      (withLsRoCl lsmpl (kitSavePollPlacedSpecI ikit))
  saveFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.saveFutDropOff) (withLsRoCl lsmpl futDropSpec)

/-- Assemble `IdentityStoreKitPlacedRoClOkI` for `cliIdentityKitSpecPlaced`. -/
theorem cliIdKitRoClOkIE_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunSkeleton.RunHooksPlaced A H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A readStk)))
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    IdentityStoreKitPlacedRoClOkI
      (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym) H := by
  have hGet := cliDirGet_placed_ok hpathLen hh hRead hjRead hjRead_unmut
  have hPut := cliDirPutStr_placed_ok hh
  have hEq := Store.IdTrustPoll.publicKeyEq_placed_ok_of_bb h_bb
  exact
    { trustShim := fun hblk => cliIdTrustShim_rocl_placed_ok hh.alloc hh.panics hs1 hblk
      trustPoll := fun hblk => cliIdTrustPoll_rocl_placed_ok hh.alloc hGet hEq hs2 hblk
      trustFutDrop := fun hblk => by
        dsimp only [cliIdentityKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliIdFutDrop_rocl_placed_ok hblk
      saveShim := fun hblk => cliIdSaveShim_rocl_placed_ok hh.alloc hh.panics hs3 hblk
      savePoll := fun hblk => cliIdSavePoll_rocl_placed_ok hh.alloc hh.panics hGet hPut hEq hs4 hblk
      saveFutDrop := fun hblk => by
        dsimp only [cliIdentityKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliIdFutDrop_rocl_placed_ok hblk }

/-- Assemble `StoreKit.IdentityStoreKitPlacedOkI` for `cliIdentityKitSpecPlaced`. -/
theorem cliIdKitOkIE_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunSkeleton.RunHooksPlaced A H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A readStk)))
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    IdentityStoreKitPlacedOkI
      (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym) H := by
  have hrocl := cliIdKitRoClOkIE_placed
    (A := A) (H := H) (rd := rd) (F0 := F0) (pathOk := pathOk) (peer := peer)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (vtSym := vtSym)
    hDropNz hpathLen hh hRead h_bb hs1 hs2 hs3 hs4 hjRead hjRead_unmut
  exact
    { trustShim := hrocl.trustShim
      trustPoll := hrocl.trustPoll
      trustFutDrop := hrocl.trustFutDrop
      saveShim := hrocl.saveShim
      savePoll := hrocl.savePoll
      saveFutDrop := hrocl.saveFutDrop }

end CryptoVerification.SignalSession.Cli.KitInst.IdKit

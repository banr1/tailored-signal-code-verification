/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrowPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShimPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShimPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed CLI `SessionOnlyKitPlacedOkSE` Assembly and Instantiation

Defines `cliSessionKitSpecPlaced`, proves `SessionOnlyVtablesPlacedOk`, assembles
`SessionOnlyKitPlacedRoClOkSE` and `SessionOnlyKitPlacedOkSE`, and specializes them to
`cliExternsPlaced mmpl W`, `E2E.HooksE.A0`, `cliIo.rd`, and `cliWrOk`.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst.SessKit

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding withLsCodeRoLoaded LibsignalCodeRoLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Store
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

/-! ## Stack bounds -/

abbrev decNeedPlaced : Nat := 10 * 0x50 + doReserveStackX
abbrev addrTextNeedPlaced : Nat :=
  0x70 + max (max doReserveStackX extHookStack) decNeedPlaced
abbrev growOneDirNeedPlaced : Nat := 0x40 + finishGrowStackX
abbrev dirPutNeedPlaced : Nat := 0x60 + max growOneDirNeedPlaced extHookStack
abbrev loadShimNeedPlaced : Nat := 0x20 + extHookStack
abbrev storeShimNeedPlaced : Nat := 0x30 + extHookStack
abbrev loadPollNeedPlaced (readStk : Nat) : Nat :=
  0x350 + max (max addrTextNeedPlaced (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩))
    (max E2E.Record.recDeserializeStack extHookStack)
abbrev storePollNeedXPlaced : Nat :=
  0xd0 + max (max addrTextNeedPlaced Proofs.libsignal.Hooks2.serializeStackX)
    (max dirPutNeedPlaced extHookStack)

/-! ## Relocatable `SessionStoreSpec` and vtables -/

/-- Relocatable `SessionStoreSpec` for CLI `SessionFiles` with placed block bases and `.rodata`
symbol addresses. -/
def cliSessionKitSpecPlaced [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost)
    (loadShimStk loadPollStk storeShimStk storePollStk : Nat)
    (vtSym : String := cliSessionVtRoSym)
    (idVtSym : String := cliIdentityVtRoSym) :
    SessionStoreSpec A 0#64 :=
  { cliSessionStoreSpec A 0#64 rd F0 pathOk Scope peer
      loadShimStk loadPollStk storeShimStk storePollStk with
    ss_vt := lsρ vtSym
    id_vt := lsρ idVtSym
    loadShimOff := lsmpl.base 604
    storeShimOff := lsmpl.base 605
    loadFutVtOff := lsρ sessLoadFutVtSym
    storeFutVtOff := lsρ sessStoreFutVtSym
    loadPollOff := lsmpl.base 569
    storePollOff := lsmpl.base 570
    loadFutDropOff := lsDropOffPlaced
    storeFutDropOff := lsDropOffPlaced
    loadFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    storeFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

theorem cliSessionKitSpecPlaced_offsets [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat}
    {idVtSym : String} (hDropNz : lsmpl.base 547 ≠ 0#64) :
    CliSessKitOffsetsPlaced
      (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4
        cliSessionVtRoSym idVtSym) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, lsDropOffPlaced_eq hDropNz, lsDropOffPlaced_eq hDropNz,
    rfl, rfl⟩

theorem cliSessionKitSpecPlaced_vtables [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat}
    {idVtSym : String} (hDropNz : lsmpl.base 547 ≠ 0#64) :
    SessionOnlyVtablesPlacedOk
      (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4
        cliSessionVtRoSym idVtSym) :=
  cliSessionOnlyVtablesPlacedOk (cliSessionKitSpecPlaced_offsets hDropNz)

theorem cliSessionKitSpecPlaced_quiet [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String} :
    (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym).Quiet :=
  ⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩

theorem cliSessionKitSpecPlaced_storeUpdate_inv [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {g : DirGhost} {rem : AddrVal} {rec : SessionRecord (List (BitVec 8))} {ans : Except Unit Unit}
    (hinv : CliSessInv rd F0 pathOk Scope peer g) (hrem : rem = peer.val)
    (hrec : (cliSessionStoreSpec A 0#64 rd F0 pathOk Scope peer s1 s2 s3 s4).RecOk rec) :
    CliSessInv rd F0 pathOk Scope peer
      ((cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).storeUpdate g rem rec ans) :=
  cliSessionStoreSpec_storeUpdate_inv (A := A) (b := 0#64)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (ans := ans) hinv hrem hrec

/-! ## Shims and `futDrop` -/

theorem cliSessLoadShim_rocl_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hs1 : loadShimNeedPlaced ≤ s1)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).loadShimOff)
      (withLsRoCl lsmpl
        (kitLoadShimSpec
          (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym))) := by
  have hcall := subroutine_ok_rocl_of_withLsCodeRoLoaded
    (LoadShim.sessLoadShim_placed_caller_ok_of_deps (callerProg := callerProg) hC hpan hs1 hblk)
  change subroutine_ok callerProg (0#64 + lsmpl.base 604) _
  rw [BitVec.zero_add]
  refine subroutine_ok_mono hcall (fun _ _ _ hpre => hpre) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  simpa only [withLsRoCl, kitLoadShimSpec, cliSessionKitSpecPlaced, cliSessionStoreSpec,
    BitVec.zero_add] using hpost

theorem cliSessStoreShim_rocl_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hs3 : storeShimNeedPlaced ≤ s3)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).storeShimOff)
      (withLsRoCl lsmpl
        (kitStoreShimSpec
          (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym))) := by
  have hcall := subroutine_ok_rocl_of_withLsCodeRoLoaded
    (StoreShim.sessStoreShim_placed_caller_ok_of_deps (callerProg := callerProg) hC hpan hs3 hblk)
  change subroutine_ok callerProg (0#64 + lsmpl.base 605) _
  rw [BitVec.zero_add]
  refine subroutine_ok_mono hcall (fun _ _ _ hpre => hpre) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  simpa only [withLsRoCl, kitStoreShimSpec, cliSessionKitSpecPlaced, cliSessionStoreSpec,
    BitVec.zero_add] using hpost

theorem cliSessFutDrop_rocl_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (0#64 + lsmpl.base 547) (withLsRoCl lsmpl futDropSpec) := by
  rw [BitVec.zero_add]
  exact ls_futDrop_ok_of_block (callerProg := callerProg) (j := 547)
    (cliSessionStoreSpecPlaced_futDrop H) hblk (by decide) (by decide)

/-! ## `Dir` helpers and `sessLoadPoll` -/

theorem cliDecimal_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunSkeleton.RunHooksPlaced A H) :
    subroutine_ok (lsProg_597 H) (lsmpl.base 597) (decimalSpecPlaced A decNeedPlaced) :=
  Decimal.Helpers.decimal_placed_ok_main
    (RunSkeleton.reserve_placed_ok (callerProg := lsProg_597 H) (i := 597) hh
      (Nat.le_refl doReserveStackX) (by decide))
    (Nat.le_refl decNeedPlaced)

theorem cliAddrText_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunSkeleton.RunHooksPlaced A H) :
    subroutine_ok (lsProg_594 H) (lsmpl.base 594) (addrTextSpecPlaced A addrTextNeedPlaced) :=
  AddressText.Helpers.addrText_placed_ok_of_deps
    (resProg := lsProg_594 H) (decProg := lsProg_597 H) (resBlk := 594) (decBlk := 597)
    hh.alloc hh.panics
    (RunSkeleton.reserve_placed_ok (callerProg := lsProg_594 H) (i := 594) hh
      (Nat.le_refl doReserveStackX) (by decide))
    (cliDecimal_placed_ok hh)
    (Nat.le_refl addrTextNeedPlaced)
    (by decide) (by decide) (by decide) (by decide)

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

theorem cliGrowOneDir_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H) :
    subroutine_ok (lsProg_586 H) (lsmpl.base 586)
      (growOneDirSpecPlaced A growOneDirNeedPlaced) :=
  GrowOne.Helpers.growOneDir_placed_of_bytes
    (GrowOne.Helpers.growOneDirBytes_placed_ok hpan
      (FinishGrow.cliFinishGrow_placed_caller_ok_x (callerProg := lsProg_586 H) (i := 586)
        hC (by decide)))
    (Nat.le_refl growOneDirNeedPlaced)

theorem cliDirPut_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunSkeleton.RunHooksPlaced A H) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 542) (dirPutSpecPlaced A dirPutNeedPlaced) :=
  Put.dirPut_placed_caller_ok_of_deps (callerProg := lsProg_570 H) (i := 570)
    hh.alloc hh.bcmp (growProg := lsProg_586 H) (jGrow := 586) (by decide) (by decide)
    (cliGrowOneDir_placed_ok hh.alloc hh.panics) (Nat.le_refl dirPutNeedPlaced) (by decide)

theorem cliSessLoadPoll_rocl_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {callerProg addrProg getProg deserProg : Program}
    {callerBlk addrBlk getBlk deserBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg deserProg deserBlk H]
    (hC : AllocContractsXCliPlaced A H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A addrTextNeedPlaced))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46) (sessDeserializeSpecPlaced Scope A))
    (hFs : TraceFsSound (lsProg_569 H))
    (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).loadPollOff)
      (withLsRoCl lsmpl
        (kitLoadPollPlacedSpecSE
          (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          Scope E2E.Record.encodeRecord)) := by
  have h569 := LoadPoll.sessLoadPoll_placed_ok_of_deps hC hAddr hGet hDeser hFs hs2
    hAddrBlk hAddrUnmut hGetBlk hGetUnmut hDeserBlk hDeserUnmut
  have h569_kit : subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (withLsCodeRoLoaded lsmpl
        (kitLoadPollPlacedSpecSE
          (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          Scope E2E.Record.encodeRecord)) := by
    refine subroutine_ok_map_panic h569 ?_
    rintro ⟨call, self, d⟩ R s0 hpre
    dsimp only [withLsCodeRoLoaded, kitLoadPollPlacedSpecSE, withEnvPre, kitLoadPollPlacedSpecS,
      cliSessionKitSpecPlaced, cliSessionStoreSpec, cliSessStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          call.addr.val = peer.val⌝ ∗
        (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
        (sessLoadBoxAt call.fut self call.addrA 0#8 ∗ dirAt A self d ∗ memRegion call.out 368 ∗
          protocolAddressAt A call.addr call.addrA ∗ A.pool ∗ stackAt s0.sp s2 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, haddr⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hhop_pure :
        s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          call.addr.name.bytes.length < 2 ^ 32 ∧
          (addressText call.addr.val).length < 2 ^ 32 ∧ d.path.length < 2 ^ 32 ∧
          pathOk (pathOf d.path (addressText call.addr.val)) ∧
          ∀ bs, d.get rd s0.fs.files (addressText call.addr.val) = .ok bs → SessFileWf Scope bs :=
      ⟨hx0, hx8, hname ▸ hinv.nameLt, haddr ▸ hinv.textLt, hinv.pathLt, haddr ▸ hinv.pathOk,
        fun bs hbs => by
          rw [hfiles, haddr] at hbs
          obtain ⟨bs₀, hget₀, hwf₀⟩ := hinv.getOk
          rw [hget₀] at hbs
          cases hbs
          exact hwf₀⟩
    have hm_hop : s0.mem ⊨ (sessLoadPollSpecPlaced rd pathOk Scope A s2).pre ⟨call, self, d⟩ s0 ∗ R := by
      dsimp only [sessLoadPollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.addr.name.bytes.length < 2 ^ 32 ∧
            (addressText call.addr.val).length < 2 ^ 32 ∧ d.path.length < 2 ^ 32 ∧
            pathOk (pathOf d.path (addressText call.addr.val)) ∧
            ∀ bs, d.get rd s0.fs.files (addressText call.addr.val) = .ok bs → SessFileWf Scope bs⌝ ∗
          (sessLoadBoxAt call.fut self call.addrA 0#8 ∗ dirAt A self d ∗ memRegion call.out 368 ∗
            protocolAddressAt A call.addr call.addrA ∗ A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hhop_pure, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨call, self, d⟩, R, hm_hop, ?_, fun _ hpan => hpan⟩
    intro sf hpost
    dsimp only [sessLoadPollSpecPlaced, withLsCodeRoLoaded] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨gr, ans, ⟨⟨hgr, htr⟩, hans⟩, hm⟩ := hpost
    rw [hfiles, haddr] at hgr
    obtain ⟨bs₀, hget₀, _⟩ := hinv.getOk
    rw [hget₀] at hgr
    subst hgr
    have hout_ent : sessLoadOutAt A call.out ans ⊢ loadPollPlacedOutAtS Scope A call.out ans := by
      cases bs₀ with
      | nil =>
        have hans' : ans = .ok none := hans
        subst hans'
        exact Entails.refl _
      | cons b bs =>
        obtain ⟨r, hans', _, hsc⟩ := hans
        subst hans'
        exact Entails.pure_right hsc (Entails.refl _)
    have hm_out : sf.mem ⊨
        loadPollPlacedOutAtS Scope A call.out ans ∗
          (sessLoadBoxAt call.fut self call.addrA 1#8 ∗ dirAt A self d ∗
            protocolAddressAt A call.addr call.addrA ∗ A.pool ∗ stackAt s0.sp s2 ∗ R) :=
      Satisfies.mono (sepConj_mono_left hout_ent) hm
    dsimp only [withLsCodeRoLoaded, kitLoadPollPlacedSpecSE, withEnvPre, kitLoadPollPlacedSpecS,
      cliSessionKitSpecPlaced, cliSessionStoreSpec, cliSessStoreAt]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ans, ?_⟩
    have hgoal : sf.mem ⊨
        ⌜(∃ bs, d.get rd F0 (addressText call.addr.val) = .ok bs ∧ SessLoadAns Scope (.ok bs) ans) ∧
          sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
          (loadPollPlacedOutAtS Scope A call.out ans ∗
            sessLoadBoxAt call.fut self call.addrA 1#8 ∗ dirAt A self d ∗
            protocolAddressAt A call.addr call.addrA ∗ A.pool ∗ stackAt s0.sp s2 ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨⟨bs₀, haddr.symm ▸ hget₀, hans⟩, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hinv, hm_out⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  change subroutine_ok callerProg (0#64 + lsmpl.base 569) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 569)
    h569_kit hCallerBlk (by decide) (by decide)

/-! ## `sessStorePoll` and kit bundles -/

theorem cliSessStorePoll_rocl_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {callerProg addrProg serProg putProg : Program}
    {callerBlk addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    (hC : AllocContractsXCliPlaced A H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A addrTextNeedPlaced))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.serializeCanonSpecX A)))
    (hPut : subroutine_ok putProg (lsmpl.base 542) (dirPutSpecPlaced A dirPutNeedPlaced))
    (hs4 : storePollNeedXPlaced ≤ s4)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).storePollOff)
      (withLsRoCl lsmpl
        (kitStorePollPlacedSpecE
          (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          E2E.Record.encodeRecord)) := by
  have h570 := StorePollX.sessStorePoll_placed_ok_of_depsX hC hAddr hSer hPut hs4
    hAddrBlk hAddrUnmut hSerBlk hSerUnmut hPutBlk hPutUnmut
  have h570_kit : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withLsCodeRoLoaded lsmpl
        (kitStorePollPlacedSpecE
          (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          E2E.Record.encodeRecord)) := by
    refine subroutine_ok_map_panic h570 ?_
    rintro ⟨call, self, d⟩ R s0 hpre
    dsimp only [withLsCodeRoLoaded, kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
      cliSessionKitSpecPlaced, cliSessionStoreSpec, cliSessStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          (Scope call.call.record ∧ (E2E.Record.encodeRecord call.call.record).length < 2 ^ 32) ∧
          call.call.addr.val = peer.val⌝ ∗
        (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
        (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
          dirAt A self d ∗ memRegion call.out 48 ∗
          protocolAddressAt A call.call.addr call.call.addrA ∗
          sessionRecordAt A call.call.recA call.call.g call.call.record ∗
          A.pool ∗ stackAt s0.sp s4 ∗ R)))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨_hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hrec, haddr⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : call.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hm_hop : s0.mem ⊨ (sessStorePollSpecPlaced A s4).pre ⟨call, self, d⟩ s0 ∗ R := by
      dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.call.addr.name.bytes.length < 2 ^ 32 ∧
            (E2E.Record.encodeRecord call.call.record).length < 2 ^ 32 ∧
            d.changed.length < 2 ^ 32⌝ ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A call.call.addr call.call.addrA ∗
            sessionRecordAt A call.call.recA call.call.g call.call.record ∗
            A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hname ▸ hinv.nameLt, hrec.2, hinv.changedLt.1⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
    refine ⟨⟨call, self, d⟩, R, hm_hop, ?_, fun _ hpan => hpan⟩
    intro sf hpost
    dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨htr, hm⟩ := hpost
    have hinv' : CliSessInv rd F0 pathOk Scope peer
        (d.put (addressText call.call.addr.val) (E2E.Record.encodeRecord call.call.record)) :=
      cliSessionStoreSpec_storeUpdate_inv (A := A) (b := 0#64)
        (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (ans := .ok ()) hinv haddr hrec
    dsimp only [withLsCodeRoLoaded, kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
      cliSessionKitSpecPlaced, cliSessionStoreSpec, cliSessStoreAt]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨.ok (), ?_⟩
    dsimp only [storePollPlacedOutAt]
    have hgoal : sf.mem ⊨
        ⌜(Except.ok () : Except Unit Unit) = .ok () ∧ sf.trace = s0.trace ++ []⌝ ∗
        (⌜CliSessInv rd F0 pathOk Scope peer
            (d.put (addressText call.call.addr.val) (E2E.Record.encodeRecord call.call.record))⌝ ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 1#8 ∗
            dirAt A self (d.put (addressText call.call.addr.val)
              (E2E.Record.encodeRecord call.call.record)) ∗
            (call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (call.out + 8#64) 40 ∗
            protocolAddressAt A call.call.addr call.call.addrA ∗
            sessionRecordAt A call.call.recA call.call.g call.call.record ∗
            A.pool ∗ stackAt s0.sp s4 ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨rfl, by rw [List.append_nil]; exact htr⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hinv', Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal
  change subroutine_ok callerProg (0#64 + lsmpl.base 570) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 570)
    h570_kit hCallerBlk (by decide) (by decide)

/-- Relocatable `SessionOnlyKitOkSE` bundle carrying `withLsRoCl lsmpl` across all six
callbacks. -/
structure SessionOnlyKitPlacedRoClOkSE [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  loadShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadShimOff) (withLsRoCl lsmpl (kitLoadShimSpec kit))
  loadPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadPollOff)
      (withLsRoCl lsmpl (kitLoadPollPlacedSpecSE kit Scope encRecord))
  loadFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadFutDropOff) (withLsRoCl lsmpl futDropSpec)
  storeShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.storeShimOff) (withLsRoCl lsmpl (kitStoreShimSpec kit))
  storePoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.storePollOff)
      (withLsRoCl lsmpl (kitStorePollPlacedSpecE kit encRecord))
  storeFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.storeFutDropOff) (withLsRoCl lsmpl futDropSpec)

/-- Assemble `SessionOnlyKitPlacedRoClOkSE` for `cliSessionKitSpecPlaced`. -/
theorem cliSessKitRoClOkSE_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg serProg : Program} {jRead deserBlk serBlk : Nat}
    [IsLsBlockProg readProg jRead H]
    [IsLsBlockProg deserProg deserBlk H]
    [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunSkeleton.RunHooksPlaced A H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A readStk)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46) (sessDeserializeSpecPlaced Scope A))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.serializeCanonSpecX A)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedRoClOkSE
      (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      Scope E2E.Record.encodeRecord H := by
  have hAddr := cliAddrText_placed_ok hh
  have hGet := cliDirGet_placed_ok hpathLen hh hRead hjRead hjRead_unmut
  have hPut := cliDirPut_placed_ok hh
  exact
    { loadShim := fun hblk => cliSessLoadShim_rocl_placed_ok hh.alloc hh.panics hs1 hblk
      loadPoll := fun hblk => cliSessLoadPoll_rocl_placed_ok hh.alloc hAddr hGet hDeser
        (hh.fs (lsProg_569 H) 569) hs2 hblk (by decide) (by decide) (by decide) (by decide)
        hDeserBlk hDeserUnmut
      loadFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk
      storeShim := fun hblk => cliSessStoreShim_rocl_placed_ok hh.alloc hh.panics hs3 hblk
      storePoll := fun hblk => cliSessStorePoll_rocl_placed_ok hh.alloc hAddr hSer hPut hs4 hblk
        (by decide) (by decide) hSerBlk hSerUnmut (by decide) (by decide)
      storeFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk }

/-- Assemble `StoreKit.SessionOnlyKitPlacedOkSE` for `cliSessionKitSpecPlaced`. -/
theorem cliSessKitOkSE_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg serProg : Program} {jRead deserBlk serBlk : Nat}
    [IsLsBlockProg readProg jRead H]
    [IsLsBlockProg deserProg deserBlk H]
    [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunSkeleton.RunHooksPlaced A H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A readStk)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46) (sessDeserializeSpecPlaced Scope A))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.serializeCanonSpecX A)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE
      (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      Scope E2E.Record.encodeRecord H := by
  have hrocl := cliSessKitRoClOkSE_placed
    (A := A) (H := H) (rd := rd) (F0 := F0) (pathOk := pathOk) (Scope := Scope) (peer := peer)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (vtSym := vtSym) (idVtSym := idVtSym)
    hDropNz hpathLen hh hRead hDeser hSer hs1 hs2 hs3 hs4 hjRead hjRead_unmut hDeserBlk hDeserUnmut
    hSerBlk hSerUnmut
  exact
    { loadShim := hrocl.loadShim
      loadPoll := hrocl.loadPoll
      loadFutDrop := hrocl.loadFutDrop
      storeShim := hrocl.storeShim
      storePoll := hrocl.storePoll
      storeFutDrop := hrocl.storeFutDrop }

/-! ## CLI specialization -/

theorem cliSessionVtablesCli_placed [LibsignalPlacement] {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat}
    {idVtSym : String} (hDropNz : lsmpl.base 547 ≠ 0#64) :
    SessionOnlyVtablesPlacedOk
      (cliSessionKitSpecPlaced E2E.HooksE.A0 cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        cliSessionVtRoSym idVtSym) :=
  cliSessionKitSpecPlaced_vtables hDropNz

private theorem hookSat_sessionMemcpy_of_frameless {H : String → Option (State → State)}
    {sym : String} (hookStack : Nat) (h : HookSat H sym framelessMemcpySpec) :
    HookSat H sym (sessionMemcpySpec hookStack) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpySpec, libcMemcpySpec, framelessMemcpySpec, memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [sessionMemcpySpec, framelessMemcpySpec] at hpost ⊢
    ac_nf at hpost ⊢

theorem serContractsX_of_runHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : RunGlue.CliGhostHooks) (W : CliHooks)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))) :
    Proofs.libsignal.Hooks2.SerContractsXPlaced E2E.HooksE.A0
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  Proofs.libsignal.Hooks2.SerContractsXPlaced.of_hooks
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    hh.codecHooks.realloc
    hh.codecHooks.shim
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (Slots.cliExternsPlaced_sessionMemmove_sat mmpl W _))
    (hookSat_sessionMemcpy_of_frameless _ hh.codecHooks.memcpy)
    (Slots.cliGhostExterns_panic_handle_error mmpl g W)
    (Slots.cliGhostExterns_panic_handle_alloc_error mmpl g W)

theorem stage2ContractsMinPlaced_of_runHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : RunGlue.CliGhostHooks) (W : CliHooks)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))) :
    Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced.of_hooks
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    hh.codecHooks.realloc
    hh.codecHooks.shim
    (hookSat_sessionMemcpy_of_frameless _ hh.codecHooks.memcpy)
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (Slots.cliExternsPlaced_sessionMemmove_sat mmpl W _))
    (Slots.cliGhostExterns_panic_handle_error mmpl g W)
    (Slots.cliGhostExterns_panic_handle_alloc_error mmpl g W)

/-- `SessionOnlyKitPlacedRoClOkSE` for CLI `SessionFiles` at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem cliSessKitRoClOkSE_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : RunGlue.CliGhostHooks) (W : CliHooks) {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    {vtSym idVtSym : String}
    {readProg deserProg : Program} {jRead deserBlk : Nat}
    [IsLsBlockProg readProg jRead (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))]
    [IsLsBlockProg deserProg deserBlk (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 readStk))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope E2E.HooksE.A0))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedRoClOkSE
      (cliSessionKitSpecPlaced E2E.HooksE.A0 cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      Scope E2E.Record.encodeRecord (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitRoClOkSE_placed
    (readProg := readProg)
    (jRead := jRead)
    (serProg := CryptoVerification.E2E.Record.Placed.lsProg_52
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)))
    (serBlk := 52)
    hDropNz
    (fun _ hp => hp.2)
    hh
    (RunSkeleton.cliReadFilePlaced_rocl_ok mmpl g W readStk hRead)
    hDeser
    (Store.SerGlueX.serializeCanonX_placed_ok_of_serContractsX
      (serContractsX_of_runHooks mmpl g W hh))
    hs1 hs2 hs3 hs4
    hjRead hjRead_unmut hDeserBlk hDeserUnmut (by decide) (by decide)

/-- `SessionOnlyKitPlacedOkSE` for CLI `SessionFiles` at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem cliSessKitOkSE_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : RunGlue.CliGhostHooks) (W : CliHooks) {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    {vtSym idVtSym : String}
    {readProg deserProg : Program} {jRead deserBlk : Nat}
    [IsLsBlockProg readProg jRead (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))]
    [IsLsBlockProg deserProg deserBlk (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 readStk))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope E2E.HooksE.A0))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE
      (cliSessionKitSpecPlaced E2E.HooksE.A0 cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      Scope E2E.Record.encodeRecord (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_placed
    (readProg := readProg)
    (jRead := jRead)
    (serProg := CryptoVerification.E2E.Record.Placed.lsProg_52
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)))
    (serBlk := 52)
    hDropNz
    (fun _ hp => hp.2)
    hh
    (RunSkeleton.cliReadFilePlaced_rocl_ok mmpl g W readStk hRead)
    hDeser
    (Store.SerGlueX.serializeCanonX_placed_ok_of_serContractsX
      (serContractsX_of_runHooks mmpl g W hh))
    hs1 hs2 hs3 hs4
    hjRead hjRead_unmut hDeserBlk hDeserUnmut (by decide) (by decide)

theorem cliSessKitRoClOkSE_cli_scopeKit_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : RunGlue.CliGhostHooks) (W : CliHooks) {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    {vtSym idVtSym : String}
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 readStk))
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)) :=
      stage2ContractsMinPlaced_of_runHooks mmpl g W hh)
    (hsub : ∀ r, Scope r → Slots.scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedRoClOkSE
      (cliSessionKitSpecPlaced E2E.HooksE.A0 cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      Scope E2E.Record.encodeRecord (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitRoClOkSE_cli_placed mmpl g W
    (readProg := readProg) (jRead := jRead)
    (deserProg := CryptoVerification.E2E.Record.Placed.lsProg_46
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)))
    (deserBlk := 46)
    hDropNz hh hRead
    (Slots.sessDeserialize_of_sub_scopeKit_placed_ok hStage2 hsub)
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut

theorem cliSessKitOkSE_cli_scopeKit_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : RunGlue.CliGhostHooks) (W : CliHooks) {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat}
    {vtSym idVtSym : String}
    {readProg : Program} {jRead : Nat}
    [IsLsBlockProg readProg jRead (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 readStk))
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)) :=
      stage2ContractsMinPlaced_of_runHooks mmpl g W hh)
    (hsub : ∀ r, Scope r → Slots.scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE
      (cliSessionKitSpecPlaced E2E.HooksE.A0 cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      Scope E2E.Record.encodeRecord (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_placed mmpl g W
    (readProg := readProg) (jRead := jRead)
    (deserProg := CryptoVerification.E2E.Record.Placed.lsProg_46
      (RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)))
    (deserBlk := 46)
    hDropNz hh hRead
    (Slots.sessDeserialize_of_sub_scopeKit_placed_ok hStage2 hsub)
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut

end CryptoVerification.SignalSession.Cli.KitInst.SessKit

namespace CryptoVerification.SignalSession.Cli.KitInst

export SessKit (cliSessionKitSpecPlaced cliSessionKitSpecPlaced_offsets
  cliSessionKitSpecPlaced_vtables cliSessionKitSpecPlaced_quiet
  cliSessionKitSpecPlaced_storeUpdate_inv
  cliSessionVtablesCli_placed
  serContractsX_of_runHooks stage2ContractsMinPlaced_of_runHooks
  cliSessKitRoClOkSE_placed cliSessKitOkSE_placed
  cliSessKitRoClOkSE_cli_placed cliSessKitOkSE_cli_placed
  cliSessKitRoClOkSE_cli_scopeKit_placed cliSessKitOkSE_cli_scopeKit_placed)

end CryptoVerification.SignalSession.Cli.KitInst

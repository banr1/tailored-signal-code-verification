/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrowPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustShimPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShimPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Budgeted CLI `IdentityStoreKitPlacedOkI` Assembly

Defines exact poll allocation envelopes (`IdentityStoreBudgetEnv`) for CLI `IdentityFiles`
and assembles the budget-threaded `IdentityStoreKitPlacedOkI` bundle under
`[LibsignalPlacement]`.
-/

@[expose] public section
set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoGames.LibsignalSessionApi (Direction IdentityChange)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsBlackBoxU8Sym
   lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack finishGrowStackX)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Getters (publicKeyEqSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal directionByte)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentityStoreSpec IdentityVtablesPlacedOk LibsignalCodeRoLoaded
   extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block savePollPlacedOutAt
   trustPollPlacedOutAt withEnvPre withLsCodeRoLoaded withLsLogOff withLsRoCl)
open CryptoVerification.SignalSession
  (lsDropOffPlaced lsDropOffPlaced_eq lsReadFileSym)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdFileWf IdGhost IdPollGhost ReadRule cliBcmpName cliBcmpSpec
   dirAt idSaveBoxAt idSaveFutVtSym idSaveOf idSaveOutAt idSaveOutAt_ok
   idSavePeers idTrustBoxAt idTrustFutVtSym idTrustOf idTrustOutAt idTrustOutAt_ok pathOf)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPC_547 blkPC_565 blkPl_547 blkPl_565 lsProg_543 lsProg_547 lsProg_565 lsProg_566 lsProg_586
   lsProg_589 lsProg_600 lsProg_601)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets pathNeed)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (CliPanicHooksPlaced ls_transfer_cl_to_lscro ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliIdInv cliIdStoreAt cliIdentityStoreSpec cliIdentityVtRoSym)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit
  (cliIdentityKitSpecPlaced cliIdentityKitSpecPlaced_offsets cliIdentityKitSpecPlaced_quiet
   cliIdentityKitSpecPlaced_saveUpdate_inv cliIdentityKitSpecPlaced_saveUpdate_own
   cliIdentityKitSpecPlaced_vtables dirPutStrNeedPlaced growOneDirNeedPlaced savePollNeedPlaced
   saveShimNeedPlaced trustPollNeedPlaced trustShimNeedPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv kitSaveShimSpec kitTrustShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI kitSavePollPlacedSpec kitSavePollPlacedSpecE kitSavePollPlacedSpecI
   kitTrustPollPlacedSpec kitTrustPollPlacedSpecE kitTrustPollPlacedSpecI ls_futDrop_ok_of_block)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeStackX)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced ReadFileRuleEnv dirGetSpecPlaced dirPutStrSpecPlaced
   growOneDirSpecPlaced idSavePollSpecPlaced idSaveShimSpecPlaced idTrustPollSpecPlaced
   idTrustShimSpecPlaced readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunHooksPlaced path_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudget (dirGet_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrowPlacedBudget
  (cliFinishGrow_placed_caller_ok_x)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.PlacedBudget
  (growOneDirBytes_placed_ok growOneDir_placed_of_bytes)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudget (dirPutStr_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustShimPlacedBudget
  (idTrustShim_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShimPlacedBudget
  (idSaveShim_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
  (CliIdTrustPollEnv idTrustPoll_placed_ok_of_deps identityKey_decode_placed_ok
   publicKeyEq_placed_ok_of_bb)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
  (CliIdSavePollEnv CliIdSaveTailEnv publicKeySerialize_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudget
  (idSavePoll_placed_ok_of_deps_core)

/-! ## Poll allocation envelopes -/

/-- Poll allocation envelope for `is_trusted_identity::{closure#0}`: `Dir::get` on `g.peers`
followed by optional buffer deallocation (`FreeOnlyEvs`). -/
def cliIdentityKitTrustPollEnv
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (g : IdGhost) (rem : AddrVal) (_key : IdentityKey) (_d : Direction) :
    List AllocEvent → Prop :=
  SeqEnv (GetEnv F0 g.peers rem.name) FreeOnlyEvs

/-- Post-`Dir::get` allocation envelope for `save_identity::{closure#0}`: empty on `.error ()`,
and optional buffer deallocation plus `PublicKey::serialize` and `Dir::put::<&str>` on `.ok _`. -/
def cliIdentityKitSaveTailEnv
    (PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (g : IdGhost) (rem : AddrVal) (key : IdentityKey)
    (gr : Except Unit (List (BitVec 8))) : List AllocEvent → Prop :=
  match gr with
  | .error () => (· = [])
  | .ok _ =>
    SeqEnv FreeOnlyEvs
      (SeqEnv PublicKeySerializeEnv
        (PutStrEnv g.peers rem.name key.serialize))

def cliIdentityKitSavePollEnv (rd : ReadRule)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (g : IdGhost) (rem : AddrVal) (key : IdentityKey) :
    List AllocEvent → Prop :=
  SeqEnv (GetEnv F0 g.peers rem.name)
    (cliIdentityKitSaveTailEnv PutStrEnv g rem key (g.peers.get rd F0 rem.name))

def cliIdentityKitBudgetEnv [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (vtSym : String := cliIdentityVtRoSym) :
    IdentityStoreBudgetEnv
      (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym) where
  trustPollEnv := cliIdentityKitTrustPollEnv GetEnv F0
  savePollEnv := cliIdentityKitSavePollEnv rd GetEnv PutStrEnv F0

abbrev cliIdentityKitDefaultBudgetEnv [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat)
    (vtSym : String := cliIdentityVtRoSym)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv rd) :
    IdentityStoreBudgetEnv
      (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym) :=
  cliIdentityKitBudgetEnv A rd F0 pathOk peer s1 s2 s3 s4
    (DirGetEnv PathEnv ReadEnv rd) DirPutStrEnv vtSym

/-! ## Shims and `futDrop` -/

section FutDrop
attribute [local irreducible] Program.fetch Program.externAt?

theorem futDropBudget_block_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_547 H) (blkPl_547).base futDropBudgetSpec := by
  dsimp only [lsProg_547, ite_true, futDropBudgetSpec]
  wp_init x s0
  wp_steps
  wp_done

end FutDrop

theorem cliIdFutDrop_rocl_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (0#64 + lsmpl.base 547) (withLsRoCl lsmpl futDropBudgetSpec) := by
  rw [BitVec.zero_add]
  exact ls_futDrop_ok_of_block (callerProg := callerProg) (j := 547)
    (futDropBudget_block_placed_ok H) hblk (by decide) (by decide)

theorem cliIdTrustShim_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : AllocContractsXCliPlaced A lim H)
    (hs1 : trustShimNeedPlaced ≤ s1) (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym).trustShimOff)
      (withLsRoCl lsmpl
        (kitTrustShimSpec M A lim
          (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym))) := by
  have h601 := idTrustShim_placed_ok_of_deps hC hs1
  have h601_kit : subroutine_ok (lsProg_601 H) (lsmpl.base 601)
      (withLsCodeRoLoaded lsmpl
        (kitTrustShimSpec M A lim
          (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym))) := by
    refine subroutine_ok_outcome_intro fun ⟨x, d, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨ (idTrustShimSpecPlaced A lim s1).pre ((x, d), st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [kitTrustShimSpec, cliIdentityKitSpecPlaced, cliIdentityStoreSpec] at hpre0 ⊢
      exact hpre0
    refine h601.mono_outcome ((x, d), st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [idTrustShimSpecPlaced, withLsCodeRoLoaded, kitTrustShimSpec,
        cliIdentityKitSpecPlaced, cliIdentityStoreSpec] at hq ⊢
      simpa only [BitVec.zero_add] using hq
    · dsimp only [idTrustShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idTrustShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idTrustShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 601) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 601)
    h601_kit hblk (by decide) (by decide)

theorem cliIdSaveShim_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : AllocContractsXCliPlaced A lim H)
    (hs3 : saveShimNeedPlaced ≤ s3) (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym).saveShimOff)
      (withLsRoCl lsmpl
        (kitSaveShimSpec M A lim
          (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym))) := by
  have h600 := idSaveShim_placed_ok_of_deps hC hs3
  have h600_kit : subroutine_ok (lsProg_600 H) (lsmpl.base 600)
      (withLsCodeRoLoaded lsmpl
        (kitSaveShimSpec M A lim
          (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym))) := by
    refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨ (idSaveShimSpecPlaced A lim s3).pre (x, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [kitSaveShimSpec, cliIdentityKitSpecPlaced, cliIdentityStoreSpec] at hpre0 ⊢
      exact hpre0
    refine h600.mono_outcome (x, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [idSaveShimSpecPlaced, withLsCodeRoLoaded, kitSaveShimSpec,
        cliIdentityKitSpecPlaced, cliIdentityStoreSpec] at hq ⊢
      simpa only [BitVec.zero_add] using hq
    · dsimp only [idSaveShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idSaveShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [idSaveShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 600) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 600)
    h600_kit hblk (by decide) (by decide)

/-! ## `Dir` helpers -/

theorem cliDirGet_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (DirGetEnv PathEnv ReadEnv rd)
        (RunBudgets.dirGetNeed ⟨readStk⟩)) :=
  dirGet_placed_ok_of_deps hpathLen hh.alloc hh.memcpyRO hh.bcmp
    (jPath := 589) (by decide) (by decide)
    (path_placed_ok (callerProg := lsProg_589 H) (i := 589) hh
      (Nat.le_refl pathNeed) (by decide))
    hjRead hjRead_unmut hRead (hh.fs (lsProg_589 H) 589)
    (Nat.le_refl (RunBudgets.dirGetNeed ⟨readStk⟩))
    (fun _ _ _ _ h => h)

theorem cliGrowOneDir_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (hpan : CliPanicHooksPlaced H) :
    subroutine_ok (lsProg_586 H) (lsmpl.base 586)
      (growOneDirSpecPlaced A lim growOneDirNeedPlaced) :=
  growOneDir_placed_of_bytes
    (growOneDirBytes_placed_ok hpan
      (cliFinishGrow_placed_caller_ok_x (callerProg := lsProg_586 H) (i := 586)
        hC (by decide)))
    (Nat.le_refl growOneDirNeedPlaced)

theorem cliDirPutStr_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (lsProg_543 H) (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim DirPutStrEnv dirPutStrNeedPlaced) :=
  dirPutStr_placed_ok_of_deps hh.alloc hh.panics hh.memcpyRO hh.bcmp
    (jGrow := 586) (by decide) (by decide)
    (cliGrowOneDir_placed_ok hh.alloc hh.panics)
    (Nat.le_refl dirPutStrNeedPlaced)

/-! ## Poll lifting -/

theorem cliIdTrustPoll_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h566 : subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) s2))
    (hCallerBlk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym).trustPollOff)
      (withLsRoCl lsmpl
        (kitTrustPollPlacedSpecI M A lim
          (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
          (cliIdentityKitBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym))) := by
  have h566_kit : subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withLsCodeRoLoaded lsmpl
        (kitTrustPollPlacedSpecI M A lim
          (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
          (cliIdentityKitBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym))) := by
    refine subroutine_ok_outcome_intro fun ⟨x, d, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
    dsimp only [withLsCodeRoLoaded, kitTrustPollPlacedSpecI, withLsLogOff,
      kitTrustPollPlacedSpecE, kitTrustPollPlacedSpec, withEnvPre,
      cliIdentityKitSpecPlaced, cliIdentityKitBudgetEnv, cliIdentityKitTrustPollEnv,
      cliIdentityStoreSpec, cliIdStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ x.call.addr.val = peer.val ∧
          FitsEnv M lim st (SeqEnv (GetEnv F0 g.peers x.call.addr.val.name) FreeOnlyEvs)⌝ ∗
        (⌜CliIdInv rd F0 pathOk peer g⌝ ∗
        (idTrustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
          dirAt A.repAlloc (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
          protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
          (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ lsLogOff ∗
          A.pool lim st s0 ∗ stackAt s0.sp s2 ∗ (dirAt A.repAlloc self g.own ∗ R))))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : x.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hfit_hop : FitsEnv M lim st (CliIdTrustPollEnv GetEnv s0.fs.files ⟨x, self, g.peers⟩) := by
      rw [hfiles]
      exact hfit
    have hhop_pure :
        s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
          x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
          pathOk (pathOf g.peers.path x.call.addr.val.name) ∧
          (∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs) ∧
          FitsEnv M lim st (CliIdTrustPollEnv GetEnv s0.fs.files ⟨x, self, g.peers⟩) :=
      ⟨hx0, hx8, hname ▸ hinv.nameLt, hinv.pathLt, haddr ▸ hinv.pathOk,
        fun bs hbs => by
          rw [hfiles, haddr] at hbs
          exact hinv.fileWf bs hbs,
        hfit_hop⟩
    have hm_hop :
        s0.mem ⊨
          (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) s2).pre
            ((⟨x, self, g.peers⟩, directionByte d), st) s0 ∗
          (dirAt A.repAlloc self g.own ∗ R) := by
      dsimp only [idTrustPollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
            x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
            pathOk (pathOf g.peers.path x.call.addr.val.name) ∧
            (∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs) ∧
            FitsEnv M lim st (CliIdTrustPollEnv GetEnv s0.fs.files ⟨x, self, g.peers⟩)⌝ ∗
          (idTrustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
            dirAt A.repAlloc (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
            protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ lsLogOff ∗
            A.pool lim st s0 ∗ stackAt s0.sp s2 ∗ (dirAt A.repAlloc self g.own ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hhop_pure, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h566.mono_outcome ((⟨x, self, g.peers⟩, directionByte d), st)
      (dirAt A.repAlloc self g.own ∗ R) s0 hpc hrun hm_hop hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [idTrustPollSpecPlaced, withLsCodeRoLoaded] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, gr, p, ⟨⟨hgr, htr⟩, hpeer, hevs⟩, hm⟩ := hpost
      rw [hfiles] at hgr hevs
      have ht1 : g.trusted rd F0 x.call.addr.val x.call.key = idTrustOf p x.call.key :=
        IdGhost.trusted_of_peerAns (hgr ▸ hpeer)
      obtain ⟨t, ht0⟩ := hinv.trusted_ok x.call.key
      have ht : g.trusted rd F0 x.call.addr.val x.call.key = .ok t := haddr.symm ▸ ht0
      have hans : idTrustOf p x.call.key = .ok t := ht1.symm.trans ht
      have hout_eq : idTrustOutAt A.repAlloc x.out (idTrustOf p x.call.key) =
          trustPollPlacedOutAt x.out (.ok t) :=
        hans.symm ▸ idTrustOutAt_ok A.repAlloc 0#64 x.out t
      rw [hout_eq] at hm
      dsimp only [withLsCodeRoLoaded, kitTrustPollPlacedSpecI, withLsLogOff,
        kitTrustPollPlacedSpecE, kitTrustPollPlacedSpec, withEnvPre,
        cliIdentityKitSpecPlaced, cliIdentityKitBudgetEnv, cliIdentityKitTrustPollEnv,
        cliIdentityStoreSpec, cliIdStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.ok t, evs, ?_⟩
      have hgoal : sf.mem ⊨
          ⌜(∃ t', g.trusted rd F0 x.call.addr.val x.call.key = .ok t' ∧
              (Except.ok t : Except Unit Bool) = .ok t') ∧
            sf.trace = s0.trace ++ [] ∧
            SeqEnv (GetEnv F0 g.peers x.call.addr.val.name) FreeOnlyEvs evs⌝ ∗
          (⌜CliIdInv rd F0 pathOk peer g⌝ ∗
            (trustPollPlacedOutAt x.out (.ok t) ∗
              idTrustBoxAt x.fut self x.call.addrA x.call.keyA 1#8 (directionByte d) ∗
              dirAt A.repAlloc self g.own ∗ dirAt A.repAlloc (self + 0x28#64) g.peers ∗
              protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
              (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
              lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s2 ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨⟨t, ht, rfl⟩, by rw [List.append_nil]; exact htr, hevs⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [idTrustPollSpecPlaced, withLsCodeRoLoaded] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [idTrustPollSpecPlaced, withLsCodeRoLoaded] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [idTrustPollSpecPlaced, withLsCodeRoLoaded] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 566) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 566)
    h566_kit hCallerBlk (by decide) (by decide)

theorem cliIdSavePoll_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h565 : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) s4))
    (hCallerBlk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym).savePollOff)
      (withLsRoCl lsmpl
        (kitSavePollPlacedSpecI M A lim
          (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
          (cliIdentityKitBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym))) := by
  have h565_kit : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (withLsCodeRoLoaded lsmpl
        (kitSavePollPlacedSpecI M A lim
          (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
          (cliIdentityKitBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym))) := by
    refine subroutine_ok_outcome_intro fun ⟨x, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
    dsimp only [withLsCodeRoLoaded, kitSavePollPlacedSpecI, withLsLogOff,
      kitSavePollPlacedSpecE, kitSavePollPlacedSpec, withEnvPre,
      cliIdentityKitSpecPlaced, cliIdentityKitBudgetEnv, cliIdentityKitSavePollEnv,
      cliIdentityStoreSpec, cliIdStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ x.call.addr.val = peer.val ∧
          FitsEnv M lim st
            (SeqEnv (GetEnv F0 g.peers x.call.addr.val.name)
              (cliIdentityKitSaveTailEnv PutStrEnv g x.call.addr.val x.call.key
                (g.peers.get rd F0 x.call.addr.val.name)))⌝ ∗
        (⌜CliIdInv rd F0 pathOk peer g⌝ ∗
        (idSaveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
          dirAt A.repAlloc (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
          protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
          (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ lsLogOff ∗
          A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ (dirAt A.repAlloc self g.own ∗ R))))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : x.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have htail_eq :
        ∀ gr,
          cliIdentityKitSaveTailEnv PutStrEnv g x.call.addr.val x.call.key gr =
            LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget.CliIdSaveTailEnv
              PutStrEnv ⟨x, self, g.peers⟩ gr := by
      rintro (_ | _) <;> rfl
    have hfit_hop :
        FitsEnv M lim st
          (CliIdSavePollEnv rd GetEnv PutStrEnv s0.fs.files ⟨x, self, g.peers⟩) := by
      rw [hfiles]
      dsimp only [CliIdSavePollEnv]
      rw [← htail_eq]
      exact hfit
    have hhop_pure :
        s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
          x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
          g.peers.changed.length < 2 ^ 32 ∧
          pathOk (pathOf g.peers.path x.call.addr.val.name) ∧
          (∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs) ∧
          FitsEnv M lim st
            (CliIdSavePollEnv rd GetEnv PutStrEnv s0.fs.files ⟨x, self, g.peers⟩) :=
      ⟨hx0, hx8, hname ▸ hinv.nameLt, hinv.pathLt, hinv.changedLt.1, haddr ▸ hinv.pathOk,
        fun bs hbs => by
          rw [hfiles, haddr] at hbs
          exact hinv.fileWf bs hbs,
        hfit_hop⟩
    have hm_hop :
        s0.mem ⊨
          (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) s4).pre
            (⟨x, self, g.peers⟩, st) s0 ∗
          (dirAt A.repAlloc self g.own ∗ R) := by
      dsimp only [idSavePollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
            x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
            g.peers.changed.length < 2 ^ 32 ∧
            pathOk (pathOf g.peers.path x.call.addr.val.name) ∧
            (∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs) ∧
            FitsEnv M lim st
              (CliIdSavePollEnv rd GetEnv PutStrEnv s0.fs.files ⟨x, self, g.peers⟩)⌝ ∗
          (idSaveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
            dirAt A.repAlloc (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
            protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ lsLogOff ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ (dirAt A.repAlloc self g.own ∗ R))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hhop_pure, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h565.mono_outcome (⟨x, self, g.peers⟩, st)
      (dirAt A.repAlloc self g.own ∗ R) s0 hpc hrun hm_hop hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [idSavePollSpecPlaced, withLsCodeRoLoaded] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, gr, p, ⟨⟨hgr, htr⟩, hpeer, hevs⟩, hm⟩ := hpost
      rw [hfiles] at hgr hevs
      dsimp only [CliIdSavePollEnv] at hevs
      rw [← htail_eq] at hevs
      obtain ⟨hs1_eq, hs2_eq⟩ := IdGhost.saveAns_of_peerAns (k := x.call.key) (hgr ▸ hpeer)
      obtain ⟨c, hc0⟩ := hinv.saveAns_ok x.call.key
      have hc : g.saveAns rd F0 x.call.addr.val x.call.key = .ok c := haddr.symm ▸ hc0
      have hans : idSaveOf p x.call.key = .ok c := hs1_eq.symm.trans hc
      have hout_eq : idSaveOutAt A.repAlloc x.out (idSaveOf p x.call.key) =
          savePollPlacedOutAt x.out (.ok c) :=
        hans.symm ▸ idSaveOutAt_ok A.repAlloc 0#64 x.out c
      have hown_eq : dirAt A.repAlloc self g.own =
          dirAt A.repAlloc self (g.saveUpd rd F0 x.call.addr.val x.call.key).own :=
        (congrArg (dirAt A.repAlloc self)
          (cliIdentityKitSpecPlaced_saveUpdate_own (A := A.repAlloc) (rd := rd) (F0 := F0)
            (pathOk := pathOk) (peer := peer) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
            (vtSym := vtSym)
            (g := g) (rem := x.call.addr.val) (k := x.call.key) (ans := .ok c))).symm
      have hpeers_eq :
          dirAt A.repAlloc (self + 0x28#64) (idSavePeers g.peers x.call.addr.val.name x.call.key p) =
            dirAt A.repAlloc (self + 0x28#64) (g.saveUpd rd F0 x.call.addr.val x.call.key).peers :=
        congrArg (dirAt A.repAlloc (self + 0x28#64)) (congrArg IdGhost.peers hs2_eq).symm
      have hinv_upd : CliIdInv rd F0 pathOk peer (g.saveUpd rd F0 x.call.addr.val x.call.key) :=
        cliIdentityKitSpecPlaced_saveUpdate_inv (A := A.repAlloc)
          (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (vtSym := vtSym)
          (k := x.call.key) (ans := .ok c) hinv haddr
      rw [hout_eq, hpeers_eq, hown_eq] at hm
      dsimp only [withLsCodeRoLoaded, kitSavePollPlacedSpecI, withLsLogOff,
        kitSavePollPlacedSpecE, kitSavePollPlacedSpec, withEnvPre,
        cliIdentityKitSpecPlaced, cliIdentityKitBudgetEnv, cliIdentityKitSavePollEnv,
        cliIdentityStoreSpec, cliIdStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.ok c, evs, ?_⟩
      have hgoal : sf.mem ⊨
          ⌜(∃ c', g.saveAns rd F0 x.call.addr.val x.call.key = .ok c' ∧
              (Except.ok c : Except Unit IdentityChange) = .ok c') ∧
            sf.trace = s0.trace ++ [] ∧
            SeqEnv (GetEnv F0 g.peers x.call.addr.val.name)
              (cliIdentityKitSaveTailEnv PutStrEnv g x.call.addr.val x.call.key
                (g.peers.get rd F0 x.call.addr.val.name)) evs⌝ ∗
          (⌜CliIdInv rd F0 pathOk peer (g.saveUpd rd F0 x.call.addr.val x.call.key)⌝ ∗
            (savePollPlacedOutAt x.out (.ok c) ∗
              idSaveBoxAt x.fut self x.call.addrA x.call.keyA 1#8 ∗
              dirAt A.repAlloc self (g.saveUpd rd F0 x.call.addr.val x.call.key).own ∗
              dirAt A.repAlloc (self + 0x28#64) (g.saveUpd rd F0 x.call.addr.val x.call.key).peers ∗
              protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
              (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
              lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨⟨c, hc, rfl⟩, by rw [List.append_nil]; exact htr, hevs⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv_upd, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [idSavePollSpecPlaced, withLsCodeRoLoaded] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [idSavePollSpecPlaced, withLsCodeRoLoaded] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [idSavePollSpecPlaced, withLsCodeRoLoaded] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 565) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 565)
    h565_kit hCallerBlk (by decide) (by decide)

/-! ## Kit bundles -/

/-- Budget-threaded `IdentityStoreKitPlacedRoClOkI` bundle carrying `withLsRoCl lsmpl` on all
six callbacks. -/
abbrev IdentityStoreKitPlacedRoClOkI [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (H : LibsignalHooks) : Prop :=
  IdentityStoreKitPlacedOkI A lim ikit ikitEnv H

theorem cliIdKitOkIE_placed_of_polls [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hC : AllocContractsXCliPlaced A lim H)
    (h566 : subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) s2))
    (h565 : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) s4))
    (hs1 : trustShimNeedPlaced ≤ s1) (hs3 : saveShimNeedPlaced ≤ s3) :
    IdentityStoreKitPlacedOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym)
      H where
  trustShim := fun hblk => cliIdTrustShim_rocl_placed_ok hC hs1 hblk
  trustPoll := fun hblk => cliIdTrustPoll_rocl_placed_ok_of_poll h566 hblk
  trustFutDrop := fun hblk => by
    dsimp only [cliIdentityKitSpecPlaced]
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk
  saveShim := fun hblk => cliIdSaveShim_rocl_placed_ok hC hs3 hblk
  savePoll := fun hblk => cliIdSavePoll_rocl_placed_ok_of_poll h565 hblk
  saveFutDrop := fun hblk => by
    dsimp only [cliIdentityKitSpecPlaced]
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk

theorem cliIdTrustPoll_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg getProg eqProg : Program} {callerBlk getBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv (RunBudgets.dirGetNeed ⟨readStk⟩)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym).trustPollOff)
      (withLsRoCl lsmpl
        (kitTrustPollPlacedSpecI M A lim
          (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
          (cliIdentityKitBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym))) := by
  have h566 := idTrustPoll_placed_ok_of_deps hC hGet
    (identityKey_decode_placed_ok (A := A) H) hEq hs2
    hGetBlk hGetUnmut (by decide) (by decide) hEqBlk hEqUnmut
  exact cliIdTrustPoll_rocl_placed_ok_of_poll h566 hCallerBlk

theorem cliIdSavePoll_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg getProg putProg eqProg : Program} {callerBlk getBlk putBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    (hC : AllocContractsXCliPlaced A lim H)
    (_hpan : CliPanicHooksPlaced H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv (RunBudgets.dirGetNeed ⟨readStk⟩)))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim PutStrEnv dirPutStrNeedPlaced))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym).savePollOff)
      (withLsRoCl lsmpl
        (kitSavePollPlacedSpecI M A lim
          (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
          (cliIdentityKitBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym))) := by
  have hSer := publicKeySerialize_lscro_of_cli
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hC (by decide)
  have hGet' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hGet (by decide) hGetBlk hGetUnmut
  have hPut' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hPut (by decide) hPutBlk hPutUnmut
  have hDec' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    (identityKey_decode_placed_ok (A := A) H) (by decide) (by decide) (by decide)
  have hEq' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hEq (by decide) hEqBlk hEqUnmut
  have h565 : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) s4) :=
    idSavePoll_placed_ok_of_deps_core hC hSer hGet' hPut' hDec' hEq' hs4
  exact cliIdSavePoll_rocl_placed_ok_of_poll h565 hCallerBlk

/-- Assemble budget-threaded `IdentityStoreKitPlacedOkI` for `cliIdentityKitSpecPlaced`. -/
theorem cliIdKitOkIE_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    IdentityStoreKitPlacedOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym ReadEnv)
      H := by
  have hGet := cliDirGet_placed_ok hpathLen hh hRead hjRead hjRead_unmut
  have hPut := cliDirPutStr_placed_ok hh
  have hEq := publicKeyEq_placed_ok_of_bb h_bb
  have h566 := idTrustPoll_placed_ok_of_deps hh.alloc hGet
    (identityKey_decode_placed_ok (A := A) H) hEq hs2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hSer := publicKeySerialize_lscro_of_cli
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hh.alloc (by decide)
  have hGet' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hGet (by decide) (by decide) (by decide)
  have hPut' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hPut (by decide) (by decide) (by decide)
  have hDec' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    (identityKey_decode_placed_ok (A := A) H) (by decide) (by decide) (by decide)
  have hEq' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hEq (by decide) (by decide) (by decide)
  have h565 : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced rd pathOk A lim
        (CliIdSavePollEnv rd (DirGetEnv PathEnv ReadEnv rd) DirPutStrEnv) s4) :=
    idSavePoll_placed_ok_of_deps_core hh.alloc hSer hGet' hPut' hDec' hEq' hs4
  exact cliIdKitOkIE_placed_of_polls hDropNz hh.alloc h566 h565 hs1 hs3

theorem cliIdKitRoClOkIE_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {readStk s1 s2 s3 s4 : Nat} {vtSym : String}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hs1 : trustShimNeedPlaced ≤ s1) (hs2 : trustPollNeedPlaced readStk ≤ s2)
    (hs3 : saveShimNeedPlaced ≤ s3) (hs4 : savePollNeedPlaced readStk ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    IdentityStoreKitPlacedRoClOkI A lim
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitDefaultBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym ReadEnv)
      H :=
  cliIdKitOkIE_placed hDropNz hpathLen hh hRead h_bb hs1 hs2 hs3 hs4 hjRead hjRead_unmut

end LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.PublicApi.StoreKit.FsFds
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Budgeted `IdentityStoreSpec` with Closed-FD Invariant

Instantiates `StoreKit`'s `fdsOk` invariant for CLI `IdentityFiles` with `FdsGe3Closed`,
proves filesystem preservation (`Spec.keepsFs`) for `futDrop` (Block `547`), `idTrustShim`
(Block `601`), and `idSaveShim` (Block `600`), lifts the `withFdsGe3Closed` poll contracts on
Blocks `566` and `565` into `IdentityStoreKitPlacedOkIFds`, and shows `writeFileHook`
(`Stores::commit`) preserves `FdsGe3Closed`.
-/

@[expose] public section
set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoGames.LibsignalSessionApi (Direction IdentityChange)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal directionByte)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentityShimCall IdentityStoreSpec IdentityVtablesPlacedOk LibsignalCodeRoLoaded
   TraceFsSound extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block savePollPlacedOutAt
   sepWP_seq_lscro trustPollPlacedOutAt withEnvPre withLsCodeRoLoaded withLsLogOff withLsRoCl)
open LibsignalBinary.Proofs.PublicApi.StoreKit.FsFds (FsAtFds)
open CryptoVerification.SignalSession
  (lsDropOffPlaced lsDropOffPlaced_eq lsRustAllocSymCli lsRustNoAllocShimSymCli writeFileHook)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdFileWf IdGhost IdPollGhost ReadRule dirAt idSaveBoxAt idSaveFutVtSym idSaveOf
   idSaveOutAt idSaveOutAt_ok idSavePeers idTrustBoxAt idTrustFutVtSym idTrustOf idTrustOutAt
   idTrustOutAt_ok pathOf)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPC_547 blkPC_600 blkPC_601 blkPl_547 blkPl_600 blkPl_601 lsProg_547 lsProg_565 lsProg_566
   lsProg_600 lsProg_601)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.IdTrustShim (idTrustShimStackPlaced)
open CryptoVerification.SignalSession.Cli.Store.IdSaveShim (idSaveShimStackPlaced)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliIdInv CliIdKitOffsetsPlaced cliIdStoreAt cliIdentityStoreSpec
   cliIdentityStoreSpec_saveUpdate_inv cliIdentityStoreSpec_saveUpdate_own cliIdentityVtRoSym
   cliIdentityVtablesPlacedOk)
open CryptoVerification.SignalSession.Cli.KitInst.IdKit
  (cliIdentityKitSpecPlaced cliIdentityKitSpecPlaced_quiet saveShimNeedPlaced trustShimNeedPlaced)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (BoxAllocEnv futDropBudgetSpec futDropBudgetSpecFs)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv kitSaveShimSpec kitTrustShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkIFds kitSavePollPlacedSpec kitSavePollPlacedSpecE
   kitSavePollPlacedSpecI kitTrustPollPlacedSpec kitTrustPollPlacedSpecE kitTrustPollPlacedSpecI
   ls_futDrop_ok_of_block_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced ReadFileRuleEnv idSavePollSpecPlaced idSaveShimSpecPlaced
   idTrustPollSpecPlaced idTrustShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOom_lscro_of_cli lift_stk_lscro_budget)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget.AllocContractsFsPlaced
  (toAllocContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget (CliIdTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
  (CliIdSavePollEnv CliIdSaveTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitBudgetEnv cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv
   cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed fdsGe3Closed_writeFileHook
   hookOk_withFdsGe3Closed_writeFileHook withFdsGe3Closed)

/-! ## Store specification and budget environments -/

/-- Relocatable `IdentityStoreSpec` for CLI `IdentityFiles` with `fdsOk := FdsGe3Closed`. -/
def cliIdentityKitSpecPlacedFds [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (trustShimStk trustPollStk saveShimStk savePollStk : Nat)
    (vtSym : String := cliIdentityVtRoSym) :
    IdentityStoreSpec A 0#64 :=
  { cliIdentityKitSpecPlaced A rd F0 pathOk peer
      trustShimStk trustPollStk saveShimStk savePollStk vtSym with
    fdsOk := fun fs => FdsGe3Closed fs }

@[simp]
theorem cliIdentityKitSpecPlacedFds_fdsOk [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat) (vtSym : String) (fs : FsState) :
    (cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 vtSym).fdsOk fs =
      FdsGe3Closed fs :=
  rfl

theorem cliIdentityKitSpecPlacedFds_offsets [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} (hDropNz : lsmpl.base 547 ≠ 0#64) :
    CliIdKitOffsetsPlaced
      (cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 cliIdentityVtRoSym) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, lsDropOffPlaced_eq hDropNz, lsDropOffPlaced_eq hDropNz,
    rfl, rfl⟩

theorem cliIdentityKitSpecPlacedFds_vtables [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} (hDropNz : lsmpl.base 547 ≠ 0#64) :
    IdentityVtablesPlacedOk
      (cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 cliIdentityVtRoSym) :=
  cliIdentityVtablesPlacedOk (cliIdentityKitSpecPlacedFds_offsets hDropNz)

theorem cliIdentityKitSpecPlacedFds_quiet [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String} :
    (cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 vtSym).Quiet :=
  cliIdentityKitSpecPlaced_quiet (A := A) (rd := rd) (F0 := F0) (pathOk := pathOk) (peer := peer)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (vtSym := vtSym)

theorem cliIdentityKitSpecPlacedFds_saveUpdate_inv [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {g : IdGhost} {rem : AddrVal} {k : IdentityKey} {ans : Except Unit IdentityChange}
    (hinv : CliIdInv rd F0 pathOk peer g) (hrem : rem = peer.val) :
    CliIdInv rd F0 pathOk peer
      ((cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 vtSym).saveUpdate
        g rem k ans) :=
  cliIdentityStoreSpec_saveUpdate_inv (A := A) (b := 0#64)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (k := k) (ans := ans) hinv hrem

theorem cliIdentityKitSpecPlacedFds_saveUpdate_own [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {g : IdGhost} {rem : AddrVal} {k : IdentityKey} {ans : Except Unit IdentityChange} :
    ((cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 vtSym).saveUpdate
      g rem k ans).own = g.own :=
  cliIdentityStoreSpec_saveUpdate_own (A := A) (b := 0#64) (rd := rd) (F0 := F0)
    (pathOk := pathOk) (peer := peer) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
    (g := g) (rem := rem) (k := k) (ans := ans)

/-- Allocation budget environment for `cliIdentityKitSpecPlacedFds`. -/
def cliIdentityKitBudgetEnvFds [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (vtSym : String := cliIdentityVtRoSym) :
    IdentityStoreBudgetEnv
      (cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 vtSym) where
  trustPollEnv := cliIdentityKitTrustPollEnv GetEnv F0
  savePollEnv := cliIdentityKitSavePollEnv rd GetEnv PutStrEnv F0

abbrev cliIdentityKitDefaultBudgetEnvFds [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat)
    (vtSym : String := cliIdentityVtRoSym)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv rd) :
    IdentityStoreBudgetEnv
      (cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 vtSym) :=
  cliIdentityKitBudgetEnvFds A rd F0 pathOk peer s1 s2 s3 s4
    (DirGetEnv PathEnv ReadEnv rd) DirPutStrEnv vtSym

/-! ## `futDrop` and shim contracts -/

section ShimsAndDrop

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Block `547` (`futDrop`) leaves `fs` unchanged (`futDropBudgetSpecFs`). -/
theorem futDropBudgetFs_block_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_547 H) (blkPl_547).base futDropBudgetSpecFs := by
  dsimp only [lsProg_547, ite_true, futDropBudgetSpecFs]
  wp_init x s0
  wp_steps
  wp_done

theorem cliIdFutDrop_fds_rocl_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (0#64 + lsmpl.base 547)
      (withLsRoCl lsmpl (futDropBudgetSpec (fun fs => FdsGe3Closed fs) true)) := by
  rw [BitVec.zero_add]
  exact ls_futDrop_ok_of_block_fs (callerProg := callerProg) (j := 547)
    (futDropBudgetFs_block_placed_ok H) (fun fs => FdsGe3Closed fs) true
    hblk (by decide) (by decide)

private theorem shim_keepsFs_lscro_of_fs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hFs : AllocContractsFsPlaced A lim H)
    {stk : Nat} (h1 : extHookStack ≤ stk := by decide) (h2 : stk ≤ 2 ^ 64 := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec stk).keepsFs) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 617) (hFs.shim stk h1 h2) hi

private theorem stackAt_idTrustShim_placed (sp : BitVec 64) :
    stackAt sp idTrustShimStackPlaced =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_32_trust_box_placed (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64,
        ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₈ b0) ∗
        ((p + 25#64) ↦₈ b1) ∗ memRegion (p + 26#64) 6) := by
  rw [memRegion_split p 8 24 (by decide),
    memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 1#64) 1 6 (by decide),
    memRegion_one, memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

/-- Block `601` (`idTrustShim`) preserves `fs` under `AllocContractsFsPlaced`. -/
theorem idTrustShim_keepsFs_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_601 H) (lsmpl.base 601)
      (idTrustShimSpecPlaced A lim idTrustShimStackPlaced).keepsFs := by
  unfold idTrustShimSpecPlaced Spec.keepsFs withLsCodeRoLoaded
  simp only [idTrustBoxAt, stackAt_idTrustShim_placed]
  cells_unfold
  dsimp only [lsProg_601]
  change subroutine_ok ((blkPC_601).rebase (blkPl_601).base H) (blkPl_601).base _
  wp_init xs s0
  obtain ⟨⟨⟨self, addrA, keyA⟩, d⟩, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 32) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 32 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 32 (rustAllocEvents 32 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 32 8) := hfit0 _ hbev
  have halloc := allocNoOom_lscro_of_cli
    (callerProg := (blkPC_601).rebase (blkPl_601).base H) (toAllocContractsX hFs)
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
    rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_601).rebase (blkPl_601).base H) hFs
      (stk := extHookStack))
    hcrl1 ()
  have hfs_shim : sf.fs = s0.fs := by assumption
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (32, 8, st)
  have hacp : AllocCallPreserved sf sf_1 := by assumption
  have hfs_alloc : sf_1.fs = s0.fs := hacp.1.trans hfs_shim
  have htr_alloc : sf_1.trace = sf.trace := hacp.2.1
  have htr_s0 : sf_1.trace = s0.trace := hacp.2.1.trans (by assumption)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_32_trust_box_placed, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWP.exists_elim fun b1 => SepWP.exists_elim fun b0 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem idTrustShim_keepsFs_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_601 H) (lsmpl.base 601)
      (idTrustShimSpecPlaced A lim stk).keepsFs :=
  lift_stk_lscro_budget (pl := lsmpl) (F := fun k => (idTrustShimSpecPlaced A lim k).keepsFs)
    (P := fun ((x, d), st) s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
        (s.readReg64 .x3).setWidth 8 = d ∧
        FitsEnv M lim st (BoxAllocEnv 32)⌝ ∗ A.pool lim st s)
    (Q := fun ((x, d), st) s0 sf =>
      ⌜sf.fs = s0.fs⌝ ∗
      ∃∗ evs : List AllocEvent,
        ⌜sf.readReg64 .x1 = lsρ idTrustFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
          BoxAllocEnv 32 evs⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          idTrustBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 d ∗
          A.pool lim (M.stepEvents evs st) sf)
    (idTrustShim_keepsFs_placed_fixed_ok hFs)
    (by dsimp [idTrustShimStackPlaced]; omega)
    (by
      intro ⟨⟨x, d⟩, st⟩ s k
      dsimp only [Spec.keepsFs, idTrustShimSpecPlaced, withLsCodeRoLoaded]
      sep_ac_rfl)
    (by
      intro ⟨⟨x, d⟩, st⟩ s0 sf k
      simp only [Spec.keepsFs, idTrustShimSpecPlaced, withLsCodeRoLoaded,
        sepExists_sepConj_left, sepExists_sepConj_right]
      exact sepExists_congr fun _ => by sep_ac_rfl)

private theorem stackAt_idSaveShim_placed (sp : BitVec 64) :
    stackAt sp idSaveShimStackPlaced =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_32_save_box_placed (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ b0 : BitVec 8, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₈ b0) ∗
        memRegion (p + 25#64) 7) := by
  rw [memRegion_split p 8 24 (by decide),
    memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

/-- Block `600` (`idSaveShim`) preserves `fs` under `AllocContractsFsPlaced`. -/
theorem idSaveShim_keepsFs_placed_fixed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_600 H) (lsmpl.base 600)
      (idSaveShimSpecPlaced A lim idSaveShimStackPlaced).keepsFs := by
  unfold idSaveShimSpecPlaced Spec.keepsFs withLsCodeRoLoaded
  simp only [idSaveBoxAt, stackAt_idSaveShim_placed]
  cells_unfold
  dsimp only [lsProg_600]
  change subroutine_ok ((blkPC_600).rebase (blkPl_600).base H) (blkPl_600).base _
  wp_init xs s0
  obtain ⟨⟨self, addrA, keyA⟩, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (BoxAllocEnv 32) := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk 32 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  have hbev : BoxAllocEnv 32 (rustAllocEvents 32 8) := Or.inr ⟨by decide, rfl⟩
  have hfit : FitsEvents M lim st (rustAllocEvents 32 8) := hfit0 _ hbev
  have halloc := allocNoOom_lscro_of_cli
    (callerProg := (blkPC_600).rebase (blkPl_600).base H) (toAllocContractsX hFs)
  dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
    rustCliAllocNoOomSpecWithStack] at halloc
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (shim_keepsFs_lscro_of_fs (callerProg := (blkPC_600).rebase (blkPl_600).base H) hFs
      (stk := extHookStack))
    hcrl1 ()
  have hfs_shim : sf.fs = s0.fs := by assumption
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro ⟨hcl2, hro2⟩
  wp_call halloc (32, 8, st)
  have hacp : AllocCallPreserved sf sf_1 := by assumption
  have hfs_alloc : sf_1.fs = s0.fs := hacp.1.trans hfs_shim
  have htr_alloc : sf_1.trace = sf.trace := hacp.2.1
  have htr_s0 : sf_1.trace = s0.trace := hacp.2.1.trans (by assumption)
  have hne0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne0
  simp only [memRegion_32_save_box_placed, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun u2 =>
    SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem idSaveShim_keepsFs_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_600 H) (lsmpl.base 600)
      (idSaveShimSpecPlaced A lim stk).keepsFs :=
  lift_stk_lscro_budget (pl := lsmpl) (F := fun k => (idSaveShimSpecPlaced A lim k).keepsFs)
    (P := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
        FitsEnv M lim st (BoxAllocEnv 32)⌝ ∗ A.pool lim st s)
    (Q := fun (x, st) s0 sf =>
      ⌜sf.fs = s0.fs⌝ ∗
      ∃∗ evs : List AllocEvent,
        ⌜sf.readReg64 .x1 = lsρ idSaveFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
          BoxAllocEnv 32 evs⌝ ∗
          A.live (sf.readReg64 .x0) 32 8 ∗
          idSaveBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 ∗
          A.pool lim (M.stepEvents evs st) sf)
    (idSaveShim_keepsFs_placed_fixed_ok hFs)
    (by dsimp [idSaveShimStackPlaced]; omega)
    (by
      intro ⟨x, st⟩ s k
      dsimp only [Spec.keepsFs, idSaveShimSpecPlaced, withLsCodeRoLoaded]
      sep_ac_rfl)
    (by
      intro ⟨x, st⟩ s0 sf k
      simp only [Spec.keepsFs, idSaveShimSpecPlaced, withLsCodeRoLoaded,
        sepExists_sepConj_left, sepExists_sepConj_right]
      exact sepExists_congr fun _ => by sep_ac_rfl)

end ShimsAndDrop

theorem cliIdTrustShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hs1 : trustShimNeedPlaced ≤ s1) (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym).trustShimOff)
      (withLsRoCl lsmpl
        (kitTrustShimSpec M A lim
          (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym) true)) := by
  have h601 := idTrustShim_keepsFs_placed_ok_of_deps hFs hs1
  have h601_kit : subroutine_ok (lsProg_601 H) (lsmpl.base 601)
      (withLsCodeRoLoaded lsmpl
        (kitTrustShimSpec M A lim
          (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym) true)) := by
    refine subroutine_ok_outcome_intro fun ⟨x, d, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitTrustShimSpec, cliIdentityKitSpecPlacedFds, cliIdentityKitSpecPlaced,
      cliIdentityStoreSpec] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hfit, hfds0⟩, hrest⟩
    have hpre' : s0.mem ⊨ ((idTrustShimSpecPlaced A lim s1).keepsFs).pre ((x, d), st) s0 ∗ R := by
      dsimp only [Spec.keepsFs]
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [idTrustShimSpecPlaced, withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hfit⟩, by simpa only [sepConj_assoc] using hrest⟩
    refine h601.mono_outcome ((x, d), st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.keepsFs, idTrustShimSpecPlaced, withLsCodeRoLoaded, kitTrustShimSpec,
        cliIdentityKitSpecPlacedFds, cliIdentityKitSpecPlaced, cliIdentityStoreSpec] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨hfs_eq, hq⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      obtain ⟨evs, hq⟩ := hq
      refine ⟨evs, ?_⟩
      simp only [BitVec.zero_add]
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hx1f, hx0f, hal, htr, hbox⟩, hsp_post⟩
      refine ⟨⟨hx1f, hx0f, hal, htr, hbox, hfs_eq ▸ hfds0⟩, ?_⟩
      simpa only [sepConj_assoc] using hsp_post
    · dsimp only [Spec.keepsFs, idTrustShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, idTrustShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, idTrustShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 601) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 601)
    h601_kit hblk (by decide) (by decide)

theorem cliIdSaveShim_fds_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hFs : AllocContractsFsPlaced A lim H)
    (hs3 : saveShimNeedPlaced ≤ s3) (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym).saveShimOff)
      (withLsRoCl lsmpl
        (kitSaveShimSpec M A lim
          (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym) true)) := by
  have h600 := idSaveShim_keepsFs_placed_ok_of_deps hFs hs3
  have h600_kit : subroutine_ok (lsProg_600 H) (lsmpl.base 600)
      (withLsCodeRoLoaded lsmpl
        (kitSaveShimSpec M A lim
          (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym) true)) := by
    refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitSaveShimSpec, cliIdentityKitSpecPlacedFds, cliIdentityKitSpecPlaced,
      cliIdentityStoreSpec] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hfit, hfds0⟩, hrest⟩
    have hpre' : s0.mem ⊨ ((idSaveShimSpecPlaced A lim s3).keepsFs).pre (x, st) s0 ∗ R := by
      dsimp only [Spec.keepsFs]
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [idSaveShimSpecPlaced, withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hfit⟩, by simpa only [sepConj_assoc] using hrest⟩
    refine h600.mono_outcome (x, st) R s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.keepsFs, idSaveShimSpecPlaced, withLsCodeRoLoaded, kitSaveShimSpec,
        cliIdentityKitSpecPlacedFds, cliIdentityKitSpecPlaced, cliIdentityStoreSpec] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      rcases hq with ⟨hfs_eq, hq⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      obtain ⟨evs, hq⟩ := hq
      refine ⟨evs, ?_⟩
      simp only [BitVec.zero_add]
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hx1f, hx0f, hal, htr, hbox⟩, hsp_post⟩
      refine ⟨⟨hx1f, hx0f, hal, htr, hbox, hfs_eq ▸ hfds0⟩, ?_⟩
      simpa only [sepConj_assoc] using hsp_post
    · dsimp only [Spec.keepsFs, idSaveShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, idSaveShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [Spec.keepsFs, idSaveShimSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 600) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 600)
    h600_kit hblk (by decide) (by decide)

/-! ## Poll lifting and `IdentityStoreKitPlacedOkIFds` assembly -/

/-- Lift `withFdsGe3Closed (idTrustPollSpecPlaced ...)` on Block `566` to
`kitTrustPollPlacedSpecI`. -/
theorem cliIdTrustPoll_fds_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h566 : subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) s2)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym).trustPollOff)
      (withLsRoCl lsmpl
        (kitTrustPollPlacedSpecI M A lim
          (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
          (cliIdentityKitBudgetEnvFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym)
          true)) := by
  have h566_kit : subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withLsCodeRoLoaded lsmpl
        (kitTrustPollPlacedSpecI M A lim
          (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
          (cliIdentityKitBudgetEnvFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym)
          true)) := by
    refine subroutine_ok_outcome_intro fun ⟨x, d, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
    dsimp only [withLsCodeRoLoaded, kitTrustPollPlacedSpecI, withLsLogOff,
      kitTrustPollPlacedSpecE, kitTrustPollPlacedSpec, withEnvPre,
      cliIdentityKitSpecPlacedFds, cliIdentityKitSpecPlaced, cliIdentityKitBudgetEnvFds,
      cliIdentityKitTrustPollEnv, cliIdentityStoreSpec, cliIdStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
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
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hfiles, hfds0⟩, hpre'⟩ := hpre'
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
          (withFdsGe3Closed
            (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) s2)).pre
              ((⟨x, self, g.peers⟩, directionByte d), st) s0 ∗
          (dirAt A.repAlloc self g.own ∗ R) := by
      dsimp only [withFdsGe3Closed, idTrustPollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
            x.call.addr.name.bytes.length < 2 ^ 32 ∧ g.peers.path.length < 2 ^ 32 ∧
            pathOk (pathOf g.peers.path x.call.addr.val.name) ∧
            (∀ bs, g.peers.get rd s0.fs.files x.call.addr.val.name = .ok bs → IdFileWf bs) ∧
            FitsEnv M lim st (CliIdTrustPollEnv GetEnv s0.fs.files ⟨x, self, g.peers⟩)⌝ ∗
          (idTrustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
            dirAt A.repAlloc (self + 0x28#64) g.peers ∗ memRegion x.out 48 ∗
            protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
            (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ lsLogOff ∗
            A.pool lim st s0 ∗ stackAt s0.sp s2 ∗ (dirAt A.repAlloc self g.own ∗ R)))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hhop_pure, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h566.mono_outcome ((⟨x, self, g.peers⟩, directionByte d), st)
      (dirAt A.repAlloc self g.own ∗ R) s0 hpc hrun hm_hop hsp ?_
    rintro sf (⟨hret, hcc, hpost0⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed, idTrustPollSpecPlaced, withLsCodeRoLoaded] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
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
        cliIdentityKitSpecPlacedFds, cliIdentityKitSpecPlaced, cliIdentityKitBudgetEnvFds,
        cliIdentityKitTrustPollEnv, cliIdentityStoreSpec, cliIdStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.ok t, evs, ?_⟩
      have hgoal : sf.mem ⊨
          ⌜((∃ t', g.trusted rd F0 x.call.addr.val x.call.key = .ok t' ∧
                (Except.ok t : Except Unit Bool) = .ok t') ∧
              sf.trace = s0.trace ++ [] ∧
              SeqEnv (GetEnv F0 g.peers x.call.addr.val.name) FreeOnlyEvs evs) ∧
            FdsGe3Closed sf.fs⌝ ∗
          (⌜CliIdInv rd F0 pathOk peer g⌝ ∗
            (trustPollPlacedOutAt x.out (.ok t) ∗
              idTrustBoxAt x.fut self x.call.addrA x.call.keyA 1#8 (directionByte d) ∗
              dirAt A.repAlloc self g.own ∗ dirAt A.repAlloc (self + 0x28#64) g.peers ∗
              protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
              (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
              lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s2 ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨⟨⟨t, ht, rfl⟩, by rw [List.append_nil]; exact htr, hevs⟩, hfds_sf⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [withFdsGe3Closed, idTrustPollSpecPlaced, withLsCodeRoLoaded] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withFdsGe3Closed, idTrustPollSpecPlaced, withLsCodeRoLoaded] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withFdsGe3Closed, idTrustPollSpecPlaced, withLsCodeRoLoaded] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 566) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 566)
    h566_kit hCallerBlk (by decide) (by decide)

/-- Lift `withFdsGe3Closed (idSavePollSpecPlaced ...)` on Block `565` to
`kitSavePollPlacedSpecI`. -/
theorem cliIdSavePoll_fds_rocl_placed_ok_of_poll [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h565 : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (withFdsGe3Closed
        (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) s4)))
    (hCallerBlk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym).savePollOff)
      (withLsRoCl lsmpl
        (kitSavePollPlacedSpecI M A lim
          (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
          (cliIdentityKitBudgetEnvFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym)
          true)) := by
  have h565_kit : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (withLsCodeRoLoaded lsmpl
        (kitSavePollPlacedSpecI M A lim
          (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
          (cliIdentityKitBudgetEnvFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym)
          true)) := by
    refine subroutine_ok_outcome_intro fun ⟨x, self, g, st⟩ R s0 hpc hrun hpre hsp => ?_
    dsimp only [withLsCodeRoLoaded, kitSavePollPlacedSpecI, withLsLogOff,
      kitSavePollPlacedSpecE, kitSavePollPlacedSpec, withEnvPre,
      cliIdentityKitSpecPlacedFds, cliIdentityKitSpecPlaced, cliIdentityKitBudgetEnvFds,
      cliIdentityKitSavePollEnv, cliIdentityStoreSpec, cliIdStoreAt] at hpre
    have hpre' : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.fs.files = F0 ∧ FdsGe3Closed s0.fs⌝ ∗
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
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hfiles, hfds0⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : x.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have htail_eq :
        ∀ gr,
          cliIdentityKitSaveTailEnv PutStrEnv g x.call.addr.val x.call.key gr =
            CliIdSaveTailEnv PutStrEnv ⟨x, self, g.peers⟩ gr := by
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
          (withFdsGe3Closed
            (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) s4)).pre
              (⟨x, self, g.peers⟩, st) s0 ∗
          (dirAt A.repAlloc self g.own ∗ R) := by
      dsimp only [withFdsGe3Closed, idSavePollSpecPlaced, withLsCodeRoLoaded]
      have h1 : s0.mem ⊨
          ⌜FdsGe3Closed s0.fs⌝ ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
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
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ (dirAt A.repAlloc self g.own ∗ R)))) := by
        rw [satisfies_pure_sepConj]; refine ⟨hfds0, ?_⟩
        rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
        rw [satisfies_pure_sepConj]; exact ⟨hhop_pure, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h565.mono_outcome (⟨x, self, g.peers⟩, st)
      (dirAt A.repAlloc self g.own ∗ R) s0 hpc hrun hm_hop hsp ?_
    rintro sf (⟨hret, hcc, hpost0⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withFdsGe3Closed, idSavePollSpecPlaced, withLsCodeRoLoaded] at hpost0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost0
      obtain ⟨hfds_sf, hpost⟩ := hpost0
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
          (cliIdentityKitSpecPlacedFds_saveUpdate_own (A := A.repAlloc) (rd := rd) (F0 := F0)
            (pathOk := pathOk) (peer := peer) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
            (vtSym := vtSym)
            (g := g) (rem := x.call.addr.val) (k := x.call.key) (ans := .ok c))).symm
      have hpeers_eq :
          dirAt A.repAlloc (self + 0x28#64) (idSavePeers g.peers x.call.addr.val.name x.call.key p) =
            dirAt A.repAlloc (self + 0x28#64) (g.saveUpd rd F0 x.call.addr.val x.call.key).peers :=
        congrArg (dirAt A.repAlloc (self + 0x28#64)) (congrArg IdGhost.peers hs2_eq).symm
      have hinv_upd : CliIdInv rd F0 pathOk peer (g.saveUpd rd F0 x.call.addr.val x.call.key) :=
        cliIdentityKitSpecPlacedFds_saveUpdate_inv (A := A.repAlloc)
          (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (vtSym := vtSym)
          (k := x.call.key) (ans := .ok c) hinv haddr
      rw [hout_eq, hpeers_eq, hown_eq] at hm
      dsimp only [withLsCodeRoLoaded, kitSavePollPlacedSpecI, withLsLogOff,
        kitSavePollPlacedSpecE, kitSavePollPlacedSpec, withEnvPre,
        cliIdentityKitSpecPlacedFds, cliIdentityKitSpecPlaced, cliIdentityKitBudgetEnvFds,
        cliIdentityKitSavePollEnv, cliIdentityStoreSpec, cliIdStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.ok c, evs, ?_⟩
      have hgoal : sf.mem ⊨
          ⌜((∃ c', g.saveAns rd F0 x.call.addr.val x.call.key = .ok c' ∧
                (Except.ok c : Except Unit IdentityChange) = .ok c') ∧
              sf.trace = s0.trace ++ [] ∧
              SeqEnv (GetEnv F0 g.peers x.call.addr.val.name)
                (cliIdentityKitSaveTailEnv PutStrEnv g x.call.addr.val x.call.key
                  (g.peers.get rd F0 x.call.addr.val.name)) evs) ∧
            FdsGe3Closed sf.fs⌝ ∗
          (⌜CliIdInv rd F0 pathOk peer (g.saveUpd rd F0 x.call.addr.val x.call.key)⌝ ∗
            (savePollPlacedOutAt x.out (.ok c) ∗
              idSaveBoxAt x.fut self x.call.addrA x.call.keyA 1#8 ∗
              dirAt A.repAlloc self (g.saveUpd rd F0 x.call.addr.val x.call.key).own ∗
              dirAt A.repAlloc (self + 0x28#64) (g.saveUpd rd F0 x.call.addr.val x.call.key).peers ∗
              protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
              (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
              lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨⟨⟨c, hc, rfl⟩, by rw [List.append_nil]; exact htr, hevs⟩, hfds_sf⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv_upd, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [withFdsGe3Closed, idSavePollSpecPlaced, withLsCodeRoLoaded] at hpan
      exact (not_satisfies_false_sepConj hpan).elim
    · dsimp only [withFdsGe3Closed, idSavePollSpecPlaced, withLsCodeRoLoaded] at hex
      exact (not_satisfies_false_sepConj hex).elim
    · dsimp only [withFdsGe3Closed, idSavePollSpecPlaced, withLsCodeRoLoaded] at hoom
      exact (not_satisfies_false_sepConj hoom).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 565) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 565)
    h565_kit hCallerBlk (by decide) (by decide)

/-- Assemble `IdentityStoreKitPlacedOkIFds` for `cliIdentityKitSpecPlacedFds` from
`AllocContractsFsPlaced` and the Block `566`/`565` poll contracts. -/
theorem cliIdKitOkIE_fds_placed_of_polls [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hFs : AllocContractsFsPlaced A lim H)
    (h566 : subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) s2)))
    (h565 : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (withFdsGe3Closed
        (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) s4)))
    (hs1 : trustShimNeedPlaced ≤ s1) (hs3 : saveShimNeedPlaced ≤ s3) :
    IdentityStoreKitPlacedOkIFds A lim
      (cliIdentityKitSpecPlacedFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitBudgetEnvFds A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym)
      H where
  trustShim := fun hblk => cliIdTrustShim_fds_rocl_placed_ok hFs hs1 hblk
  trustPoll := fun hblk => cliIdTrustPoll_fds_rocl_placed_ok_of_poll h566 hblk
  trustFutDrop := fun hblk => by
    dsimp only [cliIdentityKitSpecPlacedFds, cliIdentityKitSpecPlaced]
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk
  saveShim := fun hblk => cliIdSaveShim_fds_rocl_placed_ok hFs hs3 hblk
  savePoll := fun hblk => cliIdSavePoll_fds_rocl_placed_ok_of_poll h565 hblk
  saveFutDrop := fun hblk => by
    dsimp only [cliIdentityKitSpecPlacedFds, cliIdentityKitSpecPlaced]
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_fds_rocl_placed_ok hblk

@[simp]
theorem cliIdentityKitSpecPlaced_fdsOk [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat) (vtSym : String) (fs : FsState) :
    (cliIdentityKitSpecPlaced A rd F0 pathOk peer s1 s2 s3 s4 vtSym).fdsOk fs =
      FdsGe3Closed fs :=
  rfl

/-- `IdentityStoreKitPlacedOkIFds` on `cliIdentityKitSpecPlaced` and `cliIdentityKitBudgetEnv`. -/
theorem cliIdKitOkIE_fds_placed_direct_of_polls [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hFs : AllocContractsFsPlaced A lim H)
    (h566 : subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) s2)))
    (h565 : subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (withFdsGe3Closed
        (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) s4)))
    (hs1 : trustShimNeedPlaced ≤ s1) (hs3 : saveShimNeedPlaced ≤ s3) :
    IdentityStoreKitPlacedOkIFds A lim
      (cliIdentityKitSpecPlaced A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 vtSym)
      (cliIdentityKitBudgetEnv A.repAlloc rd F0 pathOk peer s1 s2 s3 s4 GetEnv PutStrEnv vtSym)
      H :=
  cliIdKitOkIE_fds_placed_of_polls hDropNz hFs h566 h565 hs1 hs3

/-! ## `FsAtFds` and `writeFileHook` preservation -/

theorem fsAt_cliIdentityKit_of_fdsGe3Closed [LibsignalPlacement] {A : RustAlloc}
    {envOk : FsFiles → Prop} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String} {P : Program} {s : State}
    (hP : TraceFsSound P) (henv : envOk F0) (hfiles : s.fs.files = F0) (hfds : FdsGe3Closed s.fs) :
    FsAtFds envOk
      (cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 vtSym).fdsOk
      (cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 vtSym).Quiet P s :=
  .inr ⟨cliIdentityKitSpecPlacedFds_quiet (A := A) (rd := rd) (F0 := F0) (pathOk := pathOk)
    (peer := peer) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (vtSym := vtSym),
    hP, hfiles.symm ▸ henv, hfds⟩

/-- `writeFileHook` (`Stores::commit`) preserves `FdsGe3Closed`. -/
theorem cliIdentityKitSpecPlacedFds_writeFileHook [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym : String} {s : State}
    (hfds : (cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 vtSym).fdsOk s.fs) :
    (cliIdentityKitSpecPlacedFds A rd F0 pathOk peer s1 s2 s3 s4 vtSym).fdsOk
      (writeFileHook s).fs :=
  fdsGe3Closed_writeFileHook hfds

theorem hookOk_writeFileHook_withFdsGe3Closed {α : Type} {spec : Spec α}
    (hok : HookOk writeFileHook spec) :
    HookOk writeFileHook (withFdsGe3Closed spec) :=
  hookOk_withFdsGe3Closed_writeFileHook hok

end LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitFdsPilotPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSym
public import LibsignalBinary.Proofs.Placed.BridgeReloc
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Shims
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` `IdentityFiles` Shims and Vtable Dispatch

Proves `futDrop` (`cliIdFutDropName`), stack lifting for `idOwnShimSpecPlaced`, the
`get_identity_key_pair` (Block `602`) and `get_local_registration_id` (Block `603`) shims, and
`.data.rel.ro` vtable dispatch lemmas for the CLI identity/session trait and future vtables.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs

open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs
open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PkShims.Helpers

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Stack Lifting for `idOwnShimSpecPlaced` -/

theorem idOwnShim_lift_stk_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {vtSym : String} {A : RustAlloc} {stk : Nat}
    (hInner : subroutine_ok prog entry (idOwnShimSpecPlaced vtSym A pkShimStack))
    (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok prog entry (idOwnShimSpecPlaced vtSym A stk) := by
  intro self R s0 hpc hrun hpre halign hL
  have hstk' : pkShimStack ≤ stk := by
    dsimp [pkShimStack]
    omega
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pkShimStack) ∗
        stackAt s0.sp pkShimStack := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp pkShimStack
      (stk - pkShimStack) (by omega)
    rwa [Nat.add_sub_of_le hstk'] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pkShimStack) ∗ R
  have hpre' : s0.mem ⊨ (idOwnShimSpecPlaced vtSym A pkShimStack).pre self s0 ∗ R' := by
    dsimp only [idOwnShimSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, R'] at hpre ⊢
    rw [hsplit] at hpre
    convert hpre using 1
    ac_rfl
  obtain ⟨sf, hs, ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩⟩ :=
    hInner self R' s0 hpc hrun hpre' halign hL
  · refine ⟨sf, hs, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [idOwnShimSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, R'] at hpost ⊢
    rw [hsplit]
    convert hpost using 1
    ac_rfl
  · refine ⟨sf, hs, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [idOwnShimSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, R'] at hpost ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · dsimp only [idOwnShimSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hex
    exact (not_satisfies_false_sepConj hex).elim
  · dsimp only [idOwnShimSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. Block Lookup Check for `futDrop` & Store Callbacks -/

theorem cliIdFutDrop_fnAddr_placed [LibsignalPlacement] :
    libsignalSessionLib.fnAddr lsmpl KitInst.cliIdFutDropName = lsmpl.base 547 := by
  exact ls_fnAddr_text (by decide +kernel)

theorem futDrop_block_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_547 H) (blkPl_547).base futDropSpec := by
  dsimp only [lsProg_547, ite_true, futDropSpec]
  wp_init x s0
  wp_steps
  wp_done

/-! ## 3. `get_identity_key_pair` Shim (Block `602`, `19` instructions / `76` bytes) -/

theorem idKeyPairShim_fixed_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hpanic_sym : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    subroutine_ok (lsProg_602 H) (blkPl_602).base
      (idOwnShimSpecPlaced idKeyPairFutVtSym A pkShimStack) := by
  dsimp only [lsProg_602, ite_true]
  have hshim : subroutine_ok ((blkPC_602).rebase (blkPl_602).base H)
      (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (withStack sessionShimSpec extHookStack)) :=
    ls_subroutine_ok_rocl_of_block (callerProg := (blkPC_602).rebase (blkPl_602).base H)
      (hC.shim extHookStack (Nat.le_refl _) (by decide))
  have halloc : subroutine_ok ((blkPC_602).rebase (blkPl_602).base H)
      (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustAllocSpecWithStack A extHookStack)) :=
    ls_subroutine_ok_rocl_of_block (callerProg := (blkPC_602).rebase (blkPl_602).base H) hC.alloc
  have hpanic : ((blkPC_602).rebase (blkPl_602).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") = some Rust.panicked :=
    (ls_externAt?_of_mem
      (sym := "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error")).trans hpanic_sym
  unfold idOwnShimSpecPlaced LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  simp only [idOwnFutBoxAtPlaced, stackAt_pkShim]
  cells_unfold
  wpp_init self s0
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply sepWPp_of_sepWP_lscro hcrl0 (mid := (blkPl_602).base + 32#64)
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro hcrl0 (mid := (blkPl_602).base + 16#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rintro ⟨hcl1, hro1⟩
  dsimp only [State.setMem] at hcl1 hro1
  wp_call hshim ()
  have hcrl1' : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := by assumption
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro hcrl1' (mid := (blkPl_602).base + 28#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rintro ⟨hcl2, hro2⟩
  dsimp only [State.setPC, State.writeReg64] at hcl2 hro2
  wp_call halloc (16, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro _hcrl_after
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_ownBox, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

/-! ## 4. `get_local_registration_id` Shim (Block `603`, `19` instructions / `76` bytes) -/

theorem idRegIdShim_fixed_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hpanic_sym : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    subroutine_ok (lsProg_603 H) (blkPl_603).base
      (idOwnShimSpecPlaced idRegIdFutVtSym A pkShimStack) := by
  dsimp only [lsProg_603, ite_true]
  have hshim : subroutine_ok ((blkPC_603).rebase (blkPl_603).base H)
      (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (withStack sessionShimSpec extHookStack)) :=
    ls_subroutine_ok_rocl_of_block (callerProg := (blkPC_603).rebase (blkPl_603).base H)
      (hC.shim extHookStack (Nat.le_refl _) (by decide))
  have halloc : subroutine_ok ((blkPC_603).rebase (blkPl_603).base H)
      (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustAllocSpecWithStack A extHookStack)) :=
    ls_subroutine_ok_rocl_of_block (callerProg := (blkPC_603).rebase (blkPl_603).base H) hC.alloc
  have hpanic : ((blkPC_603).rebase (blkPl_603).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") = some Rust.panicked :=
    (ls_externAt?_of_mem
      (sym := "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error")).trans hpanic_sym
  unfold idOwnShimSpecPlaced LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  simp only [idOwnFutBoxAtPlaced, stackAt_pkShim]
  cells_unfold
  wpp_init self s0
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply sepWPp_of_sepWP_lscro hcrl0 (mid := (blkPl_603).base + 32#64)
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro hcrl0 (mid := (blkPl_603).base + 16#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rintro ⟨hcl1, hro1⟩
  dsimp only [State.setMem] at hcl1 hro1
  wp_call hshim ()
  have hcrl1' : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := by assumption
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro hcrl1' (mid := (blkPl_603).base + 28#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rintro ⟨hcl2, hro2⟩
  dsimp only [State.setPC, State.writeReg64] at hcl2 hro2
  wp_call halloc (16, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro _hcrl_after
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_ownBox, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

/-! ## 5. `.data.rel.ro` Future Vtable Dispatch Lemmas under `LibsignalRoLoaded lsmpl` -/

abbrev storeVtChecksBool : Bool :=
  (fastLookupBlockSym KitInst.cliIdFutDropName == some (547, 0)) &&
  (fastLookupBlockSym idTrustPollName == some (566, 0)) &&
  (fastLookupBlockSym sessLoadPollName == some (569, 0)) &&
  (fastLookupBlockSym idKeyPairPollName == some (567, 0)) &&
  (fastLookupBlockSym idRegIdPollName == some (568, 0)) &&
  (fastLookupBlockSym idSavePollName == some (565, 0)) &&
  (fastLookupBlockSym sessStorePollName == some (570, 0)) &&
  lsroReloc64Check idTrustFutVtSym 0 KitInst.cliIdFutDropName &&
  lsroSliceCheck idTrustFutVtSym 8 (unpack64 32#64) &&
  lsroSliceCheck idTrustFutVtSym 16 (unpack64 8#64) &&
  lsroReloc64Check idTrustFutVtSym 24 idTrustPollName &&
  lsroReloc64Check sessLoadFutVtSym 0 KitInst.cliIdFutDropName &&
  lsroSliceCheck sessLoadFutVtSym 8 (unpack64 24#64) &&
  lsroSliceCheck sessLoadFutVtSym 16 (unpack64 8#64) &&
  lsroReloc64Check sessLoadFutVtSym 24 sessLoadPollName &&
  lsroReloc64Check idKeyPairFutVtSym 0 KitInst.cliIdFutDropName &&
  lsroSliceCheck idKeyPairFutVtSym 8 (unpack64 16#64) &&
  lsroSliceCheck idKeyPairFutVtSym 16 (unpack64 8#64) &&
  lsroReloc64Check idKeyPairFutVtSym 24 idKeyPairPollName &&
  lsroReloc64Check idRegIdFutVtSym 0 KitInst.cliIdFutDropName &&
  lsroSliceCheck idRegIdFutVtSym 8 (unpack64 16#64) &&
  lsroSliceCheck idRegIdFutVtSym 16 (unpack64 8#64) &&
  lsroReloc64Check idRegIdFutVtSym 24 idRegIdPollName &&
  lsroReloc64Check idSaveFutVtSym 0 KitInst.cliIdFutDropName &&
  lsroSliceCheck idSaveFutVtSym 8 (unpack64 32#64) &&
  lsroSliceCheck idSaveFutVtSym 16 (unpack64 8#64) &&
  lsroReloc64Check idSaveFutVtSym 24 idSavePollName &&
  lsroReloc64Check sessStoreFutVtSym 0 KitInst.cliIdFutDropName &&
  lsroSliceCheck sessStoreFutVtSym 8 (unpack64 32#64) &&
  lsroSliceCheck sessStoreFutVtSym 16 (unpack64 8#64) &&
  lsroReloc64Check sessStoreFutVtSym 24 sessStorePollName

private theorem storeVtChecksBool_eq : storeVtChecksBool = true := by
  decide +kernel

/-- Batch all `.rodata` future-vtable & symbol-lookup kernel checks into a single kernel reduction
so `lsroFind` / `fastLookupBlockSym` trees are unfolded once in the kernel cache. -/
private theorem storeVt_kernel_checks :
    (fastLookupBlockSym KitInst.cliIdFutDropName = some (547, 0) ∧
     fastLookupBlockSym idTrustPollName = some (566, 0) ∧
     fastLookupBlockSym sessLoadPollName = some (569, 0) ∧
     fastLookupBlockSym idKeyPairPollName = some (567, 0) ∧
     fastLookupBlockSym idRegIdPollName = some (568, 0) ∧
     fastLookupBlockSym idSavePollName = some (565, 0) ∧
     fastLookupBlockSym sessStorePollName = some (570, 0)) ∧
    (lsroReloc64Check idTrustFutVtSym 0 KitInst.cliIdFutDropName = true ∧
     lsroSliceCheck idTrustFutVtSym 8 (unpack64 32#64) = true ∧
     lsroSliceCheck idTrustFutVtSym 16 (unpack64 8#64) = true ∧
     lsroReloc64Check idTrustFutVtSym 24 idTrustPollName = true) ∧
    (lsroReloc64Check sessLoadFutVtSym 0 KitInst.cliIdFutDropName = true ∧
     lsroSliceCheck sessLoadFutVtSym 8 (unpack64 24#64) = true ∧
     lsroSliceCheck sessLoadFutVtSym 16 (unpack64 8#64) = true ∧
     lsroReloc64Check sessLoadFutVtSym 24 sessLoadPollName = true) ∧
    (lsroReloc64Check idKeyPairFutVtSym 0 KitInst.cliIdFutDropName = true ∧
     lsroSliceCheck idKeyPairFutVtSym 8 (unpack64 16#64) = true ∧
     lsroSliceCheck idKeyPairFutVtSym 16 (unpack64 8#64) = true ∧
     lsroReloc64Check idKeyPairFutVtSym 24 idKeyPairPollName = true) ∧
    (lsroReloc64Check idRegIdFutVtSym 0 KitInst.cliIdFutDropName = true ∧
     lsroSliceCheck idRegIdFutVtSym 8 (unpack64 16#64) = true ∧
     lsroSliceCheck idRegIdFutVtSym 16 (unpack64 8#64) = true ∧
     lsroReloc64Check idRegIdFutVtSym 24 idRegIdPollName = true) ∧
    (lsroReloc64Check idSaveFutVtSym 0 KitInst.cliIdFutDropName = true ∧
     lsroSliceCheck idSaveFutVtSym 8 (unpack64 32#64) = true ∧
     lsroSliceCheck idSaveFutVtSym 16 (unpack64 8#64) = true ∧
     lsroReloc64Check idSaveFutVtSym 24 idSavePollName = true) ∧
    (lsroReloc64Check sessStoreFutVtSym 0 KitInst.cliIdFutDropName = true ∧
     lsroSliceCheck sessStoreFutVtSym 8 (unpack64 32#64) = true ∧
     lsroSliceCheck sessStoreFutVtSym 16 (unpack64 8#64) = true ∧
     lsroReloc64Check sessStoreFutVtSym 24 sessStorePollName = true) := by
  have h := storeVtChecksBool_eq
  simpa only [storeVtChecksBool, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

private theorem futDrop_resolve_547 [LibsignalPlacement] :
    lsmpl.base 547 = libsignalSessionLib.resolve lsmpl KitInst.cliIdFutDropName :=
  (ls_resolve_text storeVt_kernel_checks.1.1).symm

-- `idTrustFutVtSym` (`size = 32, align = 8, poll = 566`)
theorem rodata_idTrustFut_drop_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idTrustFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr) futDrop_resolve_547 storeVt_kernel_checks.2.1.1 hP

theorem rodata_idTrustFut_size_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idTrustFutVtSym + 8#64) ↦₆₄ᵣ 32#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.1.2.1 hP

theorem rodata_idTrustFut_align_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idTrustFutVtSym + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.1.2.2.1 hP

theorem rodata_idTrustFut_poll_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idTrustFutVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 566) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text storeVt_kernel_checks.1.2.1).symm storeVt_kernel_checks.2.1.2.2.2 hP

-- `sessLoadFutVtSym` (`size = 24, align = 8, poll = 569`)
theorem rodata_sessLoadFut_drop_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ sessLoadFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr) futDrop_resolve_547 storeVt_kernel_checks.2.2.1.1 hP

theorem rodata_sessLoadFut_size_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ sessLoadFutVtSym + 8#64) ↦₆₄ᵣ 24#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.2.1.2.1 hP

theorem rodata_sessLoadFut_align_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ sessLoadFutVtSym + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.2.1.2.2.1 hP

theorem rodata_sessLoadFut_poll_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ sessLoadFutVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 569) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text storeVt_kernel_checks.1.2.2.1).symm storeVt_kernel_checks.2.2.1.2.2.2 hP

-- `idKeyPairFutVtSym` (`size = 16, align = 8, poll = 567`)
theorem rodata_idKeyPairFut_drop_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idKeyPairFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr) futDrop_resolve_547 storeVt_kernel_checks.2.2.2.1.1 hP

theorem rodata_idKeyPairFut_size_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idKeyPairFutVtSym + 8#64) ↦₆₄ᵣ 16#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.2.2.1.2.1 hP

theorem rodata_idKeyPairFut_align_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idKeyPairFutVtSym + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.2.2.1.2.2.1 hP

theorem rodata_idKeyPairFut_poll_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idKeyPairFutVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 567) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text storeVt_kernel_checks.1.2.2.2.1).symm storeVt_kernel_checks.2.2.2.1.2.2.2 hP

-- `idRegIdFutVtSym` (`size = 16, align = 8, poll = 568`)
theorem rodata_idRegIdFut_drop_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idRegIdFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr) futDrop_resolve_547 storeVt_kernel_checks.2.2.2.2.1.1 hP

theorem rodata_idRegIdFut_size_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idRegIdFutVtSym + 8#64) ↦₆₄ᵣ 16#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.2.2.2.1.2.1 hP

theorem rodata_idRegIdFut_align_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idRegIdFutVtSym + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.2.2.2.1.2.2.1 hP

theorem rodata_idRegIdFut_poll_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idRegIdFutVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 568) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text storeVt_kernel_checks.1.2.2.2.2.1).symm storeVt_kernel_checks.2.2.2.2.1.2.2.2 hP

-- `idSaveFutVtSym` (`size = 32, align = 8, poll = 565`)
theorem rodata_idSaveFut_drop_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idSaveFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr) futDrop_resolve_547 storeVt_kernel_checks.2.2.2.2.2.1.1 hP

theorem rodata_idSaveFut_size_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idSaveFutVtSym + 8#64) ↦₆₄ᵣ 32#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.2.2.2.2.1.2.1 hP

theorem rodata_idSaveFut_align_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idSaveFutVtSym + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.2.2.2.2.1.2.2.1 hP

theorem rodata_idSaveFut_poll_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idSaveFutVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 565) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text storeVt_kernel_checks.1.2.2.2.2.2.1).symm storeVt_kernel_checks.2.2.2.2.2.1.2.2.2 hP

-- `sessStoreFutVtSym` (`size = 32, align = 8, poll = 570`)
theorem rodata_sessStoreFut_drop_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ sessStoreFutVtSym) ↦₆₄ᵣ lsmpl.base 547) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr) futDrop_resolve_547 storeVt_kernel_checks.2.2.2.2.2.2.1 hP

theorem rodata_sessStoreFut_size_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ sessStoreFutVtSym + 8#64) ↦₆₄ᵣ 32#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.2.2.2.2.2.2.1 hP

theorem rodata_sessStoreFut_align_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ sessStoreFutVtSym + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  lsro64_intro hro (by lsro_addr) storeVt_kernel_checks.2.2.2.2.2.2.2.2.1 hP

theorem rodata_sessStoreFut_poll_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ sessStoreFutVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 570) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text storeVt_kernel_checks.1.2.2.2.2.2.2).symm storeVt_kernel_checks.2.2.2.2.2.2.2.2.2 hP

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs

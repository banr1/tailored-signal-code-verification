/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudgetFd
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# File-Descriptor-Predicated Bridge for `<PrivateKey>::calculate_agreement` (Block `207`)

Lifts `AgreeBudgetFd.calculateAgreement_placed_ok_fsPred` to `Initiator.Primitives` under
`withFsPred Pfs` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetFd

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_207 blkPl_207 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (CalculateAgreementGhost LibsignalCodeRoLoaded calculateAgreement
   calculateAgreementResultAt calculateAgreementStack diffieHellmanSpec
   extract_withLsCodeRoLoaded keys_ls_subroutine_ok_of_block_cro
   withLsCodeRoLoaded zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (LsFrozenInv lsDhSym lsRustAllocSym lsRustNoAllocShimSym lsSharedDropSym lsStaticDropSym)
open CryptoVerification.E2E (u8Vec)
open CryptoVerification.E2E.Pqxdh.Initiator (Bytes Primitives bytesToBv8)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PrimitivesMatchCrypto calculateAgreementResultAt_entails_pqxdh
   pqxdhCalculateAgreementResultAt u8Vec_toList_of_length)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
  (calculateAgreementEvents)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
  (calculateAgreementEvents_eq pqxdhCalculateAgreementPlacedBaseSpec
   pqxdhCalculateAgreementPlacedFrozenSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudgetFd
  (calculateAgreement_placed_ok_fsPred withFsPred)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
  (CalculateAgreementEnv calculateAgreementSpec calculateAgreementSpecWithStack ctEqSliceROSpec)

/-- Target predicate for `Pfs`-threaded budget `<PrivateKey>::calculate_agreement` (Block `207`)
wrapped in `withLsCodeRoLoaded lsmpl`. -/
def PqxdhCalculateAgreementPlacedFsOk [LibsignalPlacement] (Pfs : FsState → Prop)
    (M : AllocCostModel) (P : Primitives) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (prog : Program) : Prop :=
  subroutine_ok prog (lsmpl.base 207)
    (withLsCodeRoLoaded lsmpl (withFsPred Pfs (pqxdhCalculateAgreementPlacedBaseSpec M P A lim)))

/-- Target predicate for `Pfs`-threaded budget `<PrivateKey>::calculate_agreement` (Block `207`)
carrying `Keys.LsFrozenInv lsmpl` in `pre`. -/
def PqxdhCalculateAgreementPlacedFrozenFsOk [LibsignalPlacement] (Pfs : FsState → Prop)
    (M : AllocCostModel) (P : Primitives) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (prog : Program) : Prop :=
  subroutine_ok prog (lsmpl.base 207)
    (withFsPred Pfs (pqxdhCalculateAgreementPlacedFrozenSpec M P A lim lsmpl))

/-- `Pfs`-threaded relocatable `<PrivateKey>::calculate_agreement` (Block `207`) bridged from
`AgreeBudgetFd.calculateAgreement_placed_ok_fsPred`. -/
theorem pqxdhCalculateAgreement_placed_ok_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H lsDhSym (withFsPred Pfs (withVmPreserved (diffieHellmanSpec C.X))))
    (h_shdrop : HookSat H lsSharedDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)))
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl (withFsPred Pfs ctEqSliceROSpec)))
    (h_shim : HookSat H lsRustNoAllocShimSym (withFsPred Pfs noAllocShimBudgetSpec))
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec))) :
    PqxdhCalculateAgreementPlacedFsOk Pfs M P A lim ((blkPC_207).rebase (blkPl_207).base H) := by
  unfold PqxdhCalculateAgreementPlacedFsOk
  have hraw := calculateAgreement_placed_ok_fsPred h_dh h_shdrop hct h_shim h_alloc h_stdrop
  refine subroutine_ok_map hraw ?_
  rintro ⟨⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩, st⟩ R s0 hpre
  obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [withFsPred, pqxdhCalculateAgreementPlacedBaseSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpfs0, ⟨hx0, hx1, hx8, hsp_eq, hour, htheir, hfits⟩, hpre⟩
  let xg : CalculateAgreementGhost := ⟨ourA, ⟨u8Vec 32 ourSk32⟩, theirA, ⟨u8Vec 32 theirPk32⟩, ret⟩
  have hour_list : xg.our.bytes.toList = bytesToBv8 ourSk32 := u8Vec_toList_of_length hour
  have htheir_list : xg.their.bytes.toList = bytesToBv8 theirPk32 := u8Vec_toList_of_length htheir
  have hevs_eq :
      LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementEvents C.X xg =
        calculateAgreementEvents P ourSk32 theirPk32 :=
    calculateAgreementEvents_eq hP ourA ourSk32 theirA theirPk32 ret
  have hfits_env : FitsEnv M lim st (CalculateAgreementEnv C.X xg) := by
    intro evs hevs
    rw [CalculateAgreementEnv, hevs_eq] at hevs
    subst hevs
    exact hfits
  refine ⟨(xg, st), R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded, withFsPred, calculateAgreementSpec,
      calculateAgreementSpecWithStack]
    rw [hour_list, htheir_list, hsp_eq]
    have hcomm :
        ((⌜Pfs s0.fs⌝ ∗
          (⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret ∧
              FitsEnv M lim st (CalculateAgreementEnv C.X xg)⌝ ∗
            (xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ (xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
            memRegion xg.ret 24 ∗ A.pool lim st s0 ∗ stackAt sp calculateAgreementStack)) ∗
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜Pfs s0.fs⌝ ∗
            (⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret ∧
                FitsEnv M lim st (CalculateAgreementEnv C.X xg)⌝ ∗
              ((xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ ((xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
                (memRegion xg.ret 24 ∗ (A.pool lim st s0 ∗
                  (stackAt sp calculateAgreementStack ∗ R))))))) := by
      sep_ac_rfl
    rw [hcomm, satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hfr, hpfs0, ⟨hx0, hx1, hx8, hfits_env⟩, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, withFsPred, calculateAgreementSpec,
      calculateAgreementSpecWithStack, pqxdhCalculateAgreementPlacedBaseSpec] at hpost ⊢
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [hour_list, htheir_list, hsp_eq] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpfs_f, ⟨htr, hevs⟩, hpost⟩
    rw [CalculateAgreementEnv, hevs_eq] at hevs
    subst hevs
    refine ⟨hpfs_f, htr, ?_⟩
    have hE := calculateAgreementResultAt_entails_pqxdh hP A.repAlloc ret ourSk32 theirPk32
    have hq1 : sf.mem ⊨
        calculateAgreementResultAt A.repAlloc ret (calculateAgreement C.X xg.their xg.our) ∗
          ((ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            A.pool lim (M.stepEvents (calculateAgreementEvents P ourSk32 theirPk32) st) sf ∗
            stackAt sp calculateAgreementStack ∗ R) := by
      ac_nf at hpost ⊢
    have hq2 := Satisfies.mono (sepConj_mono_left hE) hq1
    ac_nf at hq2 ⊢

/-- Cross-block transfer of `pqxdhCalculateAgreement_placed_ok_fsPred` to any caller block
`i < 619` (including mutated caller blocks such as Block `521` or `79`). -/
theorem pqxdhCalculateAgreement_placed_ok_of_block_fsPred [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {Pfs : FsState → Prop}
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H lsDhSym (withFsPred Pfs (withVmPreserved (diffieHellmanSpec C.X))))
    (h_shdrop : HookSat H lsSharedDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)))
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl (withFsPred Pfs ctEqSliceROSpec)))
    (h_shim : HookSat H lsRustNoAllocShimSym (withFsPred Pfs noAllocShimBudgetSpec))
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)))
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFsOk Pfs M P A lim callerProg :=
  keys_ls_subroutine_ok_of_block_cro
    (pqxdhCalculateAgreement_placed_ok_fsPred hP h_dh h_shdrop hct h_shim h_alloc h_stdrop)
    hi (by decide) (by decide)

/-- Lift `PqxdhCalculateAgreementPlacedFsOk` (`withLsCodeRoLoaded`) to
`PqxdhCalculateAgreementPlacedFrozenFsOk` (`Keys.LsFrozenInv`). -/
theorem pqxdhCalculateAgreement_placed_frozen_of_cro_fsPred [LibsignalPlacement]
    {Pfs : FsState → Prop} {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program}
    (h : PqxdhCalculateAgreementPlacedFsOk Pfs M P A lim prog) :
    PqxdhCalculateAgreementPlacedFrozenFsOk Pfs M P A lim prog := by
  refine subroutine_ok_mono h ?_ (fun _ _ _ _ hq => hq)
  rintro ⟨⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩, st⟩ R s0 hp
  dsimp only [withFsPred, pqxdhCalculateAgreementPlacedFrozenSpec, withLsCodeRoLoaded,
    pqxdhCalculateAgreementPlacedBaseSpec] at hp ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨hpfs0, ⟨hF, hx0, hx1, hx8, hsp_eq, hour, htheir, hfits⟩, hsep⟩
  have hcomm :
      ((⌜Pfs s0.fs⌝ ∗
        (⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret ∧
            s0.sp = sp ∧ ourSk32.length = 32 ∧ theirPk32.length = 32 ∧
            FitsEvents M lim st (calculateAgreementEvents P ourSk32 theirPk32)⌝ ∗
          (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
          memRegion ret 24 ∗ A.pool lim st s0 ∗ stackAt sp calculateAgreementStack)) ∗
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜Pfs s0.fs⌝ ∗
          (⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret ∧
              s0.sp = sp ∧ ourSk32.length = 32 ∧ theirPk32.length = 32 ∧
              FitsEvents M lim st (calculateAgreementEvents P ourSk32 theirPk32)⌝ ∗
            ((ourA ↦ₛ bytesToBv8 ourSk32) ∗ ((theirA ↦ₛ bytesToBv8 theirPk32) ∗
              (memRegion ret 24 ∗ (A.pool lim st s0 ∗
                (stackAt sp calculateAgreementStack ∗ R))))))) := by
    sep_ac_rfl
  rw [hcomm, satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨⟨hF.code, hF.ro⟩, hpfs0, ⟨hx0, hx1, hx8, hsp_eq, hour, htheir, hfits⟩, by ac_nf at hsep ⊢⟩

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetFd

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.ProgramReflection
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Cryptographic Primitive Bridge

Proves `VmPreserved` and `RustCliAllocBudget M` relocatable contracts under `[LibsignalPlacement]`
for constant-time slice comparison (`ct_eq` on Block `213`), `<PrivateKey>::calculate_agreement`
(Block `207`), and `expand_multi_info` (`64` B and `80` B on Block `53`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp BitVec
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto PrivateKey PublicKey)
open CryptoGames.Ratchet (clampScalar)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkPC_207 blkPC_213 blkPl_207 blkPl_213 lsBlackBoxU8Sym ls_subroutine_ok_of_block
   lsmpl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet
  (CalculateAgreementGhost HkdfPlacedHooks LibsignalCodeRoLoaded
   blkPC_53 blkPl_53 calculateAgreement calculateAgreementResultAt calculateAgreementStack
   diffieHellmanSpec expandMultiInfoSpec expandMultiInfoStack extract_withLsCodeRoLoaded
   keys_ls_subroutine_ok_of_block_cro
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (LsFrozenInv calculateAgreement_eq_none calculateAgreement_eq_some
   hmacCore_entails_cells lsDhSym lsRustAllocSym lsRustNoAllocShimSym
   lsSharedDropSym lsStaticDropSym stackAt_alloc_expand)
open CryptoVerification.E2E (u8Vec vecU8)
open CryptoVerification.E2E.Pqxdh.Initiator
  (Bytes INFO_MSG_KEYS INFO_RATCHET Primitives bytesToBv8)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PrimitivesMatchCrypto bytesToBv8_hkdfExpandRef_64 bytesToBv8_hkdfExpandRef_80
   bytesToBv8_length bytesToBv8_replicate bytesToBv8_vecU8
   calculateAgreementResultAt_entails_pqxdh pqxdhCalculateAgreementResultAt
   pqxdhHmacStateAt_eq toU8_bytesToBv8 u8Vec_toList_of_length)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
  (pqxdhHkdfExpandCellsPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
  (calculateAgreementEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget
  (calculateAgreement_placed_ok calculateAgreement_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
  (CalculateAgreementEnv calculateAgreementSpec calculateAgreementSpecX)
export LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAux
  (ct_eq_ro_placed_vm_ok expand_multi_info_placed_vm_ok)

/-! ## 1. Relocatable `ct_eq` with `VmPreserved` (Block `213`) -/

theorem ct_eq_ro_placed_vm_ok_withLsCodeLoaded [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withLsCodeLoaded lsmpl
        LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.ctEqSliceROSpec) :=
  subroutine_ok_withLsCodeLoaded_of_plain (ct_eq_ro_placed_vm_ok h_bb)

theorem ct_eq_ro_placed_vm_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 213)
      (withLsCodeLoaded lsmpl
        LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.ctEqSliceROSpec) :=
  ls_subroutine_ok_of_block (ct_eq_ro_placed_vm_ok_withLsCodeLoaded h_bb)
    hi (by decide) (by decide)

/-! ## 2. Relocatable `<PrivateKey>::calculate_agreement` (Block `207`) -/

/-- Unconditional Block `207` `calculateAgreement_placed_ok` discharging Block `213` `ct_eq`
internally from `h_bb : H lsBlackBoxU8Sym = some blackBoxHook`. -/
theorem calculateAgreement_placed_ok_unconditional [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : CryptoGames.Ratchet.X25519Fn} {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec M A lim X)) :=
  calculateAgreement_placed_ok h_dh h_shdrop
    (ct_eq_ro_placed_vm_ok_of_block h_bb) h_shim h_alloc h_stdrop

/-- Unconditional Block `207` `calculateAgreement_placed_ok_x` at `calculateAgreementStackX`. -/
theorem calculateAgreement_placed_ok_x_unconditional [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : CryptoGames.Ratchet.X25519Fn} {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpecX M A lim X)) :=
  calculateAgreement_placed_ok_x h_dh h_shdrop
    (ct_eq_ro_placed_vm_ok_of_block h_bb) h_shim h_alloc h_stdrop

/-- Alignment of `Keys.DefsBudget.calculateAgreementEvents` and
`AcceptBudget.calculateAgreementEvents` under `PrimitivesMatchCrypto P C`. -/
theorem calculateAgreementEvents_eq {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C)
    (ourA : BitVec 64) (ourSk32 : Bytes) (theirA : BitVec 64) (theirPk32 : Bytes)
    (ret : BitVec 64) :
    LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementEvents C.X
      ⟨ourA, ⟨u8Vec 32 ourSk32⟩, theirA, ⟨u8Vec 32 theirPk32⟩, ret⟩ =
    calculateAgreementEvents P ourSk32 theirPk32 := by
  let ss := C.X (clampScalar (u8Vec 32 ourSk32)) (u8Vec 32 theirPk32)
  have hx25519 : P.x25519 ourSk32 theirPk32 = vecU8 ss := hP.x25519_eq ourSk32 theirPk32
  by_cases hzero : ss.toList = List.replicate 32 0#8
  · have hres :
        calculateAgreement C.X (⟨u8Vec 32 theirPk32⟩ : PublicKey)
          (⟨u8Vec 32 ourSk32⟩ : PrivateKey) = none :=
      calculateAgreement_eq_none hzero
    have hp_zero : P.x25519 ourSk32 theirPk32 = List.replicate 32 0 := by
      rw [hx25519, ← toU8_bytesToBv8 (List.replicate 32 0), bytesToBv8_replicate]
      unfold vecU8
      rw [hzero]
      rfl
    unfold LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementEvents
      calculateAgreementEvents
    simp only [hres, hp_zero, ↓reduceIte]
  · have hres :
        calculateAgreement C.X (⟨u8Vec 32 theirPk32⟩ : PublicKey)
          (⟨u8Vec 32 ourSk32⟩ : PrivateKey) = some ss :=
      calculateAgreement_eq_some hzero
    have hp_ne : P.x25519 ourSk32 theirPk32 ≠ List.replicate 32 0 := by
      intro h
      apply hzero
      have hb := congrArg bytesToBv8 h
      rw [hx25519, bytesToBv8_vecU8, bytesToBv8_replicate] at hb
      exact hb
    unfold LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementEvents
      calculateAgreementEvents
    simp only [hres, hp_ne, ↓reduceIte]

/-- Budget-threaded relocatable base `Spec` for `<PrivateKey>::calculate_agreement` (Block `207`)
at the `Initiator.Primitives` abstraction level (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under
`FitsEvents`). -/
def pqxdhCalculateAgreementPlacedBaseSpec (M : AllocCostModel) (P : Primitives)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((ourA, ourSk32, theirA, theirPk32, ret, sp), st) s =>
    ⌜s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧ s.readReg64 .x8 = ret ∧ s.sp = sp ∧
      ourSk32.length = 32 ∧ theirPk32.length = 32 ∧
      FitsEvents M lim st (calculateAgreementEvents P ourSk32 theirPk32)⌝ ∗
      (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      memRegion ret 24 ∗ A.pool lim st s ∗ stackAt sp calculateAgreementStack
  post := fun ((ourA, ourSk32, theirA, theirPk32, ret, sp), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      pqxdhCalculateAgreementResultAt P A.repAlloc ret ourSk32 theirPk32 ∗
      A.pool lim (M.stepEvents (calculateAgreementEvents P ourSk32 theirPk32) st) sf ∗
      stackAt sp calculateAgreementStack

/-- Frozen-invariant variant of `pqxdhCalculateAgreementPlacedBaseSpec` carrying
`Keys.LsFrozenInv pl s` in `pre`. -/
def pqxdhCalculateAgreementPlacedFrozenSpec (M : AllocCostModel) (P : Primitives)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (pl : Obj.MultiPlacement) :
    Spec ((BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((ourA, ourSk32, theirA, theirPk32, ret, sp), st) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧
      s.readReg64 .x8 = ret ∧ s.sp = sp ∧ ourSk32.length = 32 ∧ theirPk32.length = 32 ∧
      FitsEvents M lim st (calculateAgreementEvents P ourSk32 theirPk32)⌝ ∗
      (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
      memRegion ret 24 ∗ A.pool lim st s ∗ stackAt sp calculateAgreementStack
  post := (pqxdhCalculateAgreementPlacedBaseSpec M P A lim).post
  onPanic := (pqxdhCalculateAgreementPlacedBaseSpec M P A lim).onPanic

/-- Target predicate for budget-threaded `<PrivateKey>::calculate_agreement` (Block `207`)
wrapped in `withLsCodeRoLoaded lsmpl`. -/
def PqxdhCalculateAgreementPlacedOk [LibsignalPlacement] (M : AllocCostModel) (P : Primitives)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (prog : Program) : Prop :=
  subroutine_ok prog (lsmpl.base 207)
    (withLsCodeRoLoaded lsmpl (pqxdhCalculateAgreementPlacedBaseSpec M P A lim))

/-- Target predicate for budget-threaded `<PrivateKey>::calculate_agreement` (Block `207`)
carrying `Keys.LsFrozenInv lsmpl` in `pre`. -/
def PqxdhCalculateAgreementPlacedFrozenOk [LibsignalPlacement] (M : AllocCostModel)
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (prog : Program) : Prop :=
  subroutine_ok prog (lsmpl.base 207)
    (pqxdhCalculateAgreementPlacedFrozenSpec M P A lim lsmpl)

/-- Budget-threaded relocatable `<PrivateKey>::calculate_agreement` (Block `207`) bridged from
`AgreeBudget.calculateAgreement_placed_ok` and `ct_eq_ro_placed_vm_ok_of_block`. -/
theorem pqxdhCalculateAgreement_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {H : LibsignalHooks}
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)) :
    PqxdhCalculateAgreementPlacedOk M P A lim ((blkPC_207).rebase (blkPl_207).base H) := by
  unfold PqxdhCalculateAgreementPlacedOk
  have hraw := calculateAgreement_placed_ok_unconditional h_dh h_shdrop h_bb h_shim h_alloc h_stdrop
  refine subroutine_ok_map hraw ?_
  rintro ⟨⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩, st⟩ R s0 hpre
  obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [pqxdhCalculateAgreementPlacedBaseSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hsp_eq, hour, htheir, hfits⟩, hpre⟩
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
  · dsimp only [withLsCodeRoLoaded, calculateAgreementSpec,
      LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementSpecWithStack]
    rw [hour_list, htheir_list, hsp_eq]
    have hcomm :
        ((⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret ∧
            FitsEnv M lim st (CalculateAgreementEnv C.X xg)⌝ ∗
          (xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ (xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
          memRegion xg.ret 24 ∗ A.pool lim st s0 ∗ stackAt sp calculateAgreementStack) ∗
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret ∧
              FitsEnv M lim st (CalculateAgreementEnv C.X xg)⌝ ∗
            ((xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ ((xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
              (memRegion xg.ret 24 ∗ (A.pool lim st s0 ∗
                (stackAt sp calculateAgreementStack ∗ R)))))) := by
      sep_ac_rfl
    rw [hcomm, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hfr, ⟨hx0, hx1, hx8, hfits_env⟩, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, calculateAgreementSpec,
      LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.calculateAgreementSpecWithStack,
      pqxdhCalculateAgreementPlacedBaseSpec] at hpost ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [hour_list, htheir_list, hsp_eq] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨htr, hevs⟩, hpost⟩
    rw [CalculateAgreementEnv, hevs_eq] at hevs
    subst hevs
    refine ⟨htr, ?_⟩
    have hE := calculateAgreementResultAt_entails_pqxdh hP A.repAlloc ret ourSk32 theirPk32
    have hq1 : sf.mem ⊨
        calculateAgreementResultAt A.repAlloc ret (calculateAgreement C.X xg.their xg.our) ∗
          ((ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            A.pool lim (M.stepEvents (calculateAgreementEvents P ourSk32 theirPk32) st) sf ∗
            stackAt sp calculateAgreementStack ∗ R) := by
      ac_nf at hpost ⊢
    have hq2 := Satisfies.mono (sepConj_mono_left hE) hq1
    ac_nf at hq2 ⊢

/-- Cross-block transfer of `pqxdhCalculateAgreement_placed_ok` to any caller block `i < 619`
(including mutated caller blocks such as Block `79`). -/
theorem pqxdhCalculateAgreement_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M P A lim callerProg :=
  keys_ls_subroutine_ok_of_block_cro
    (pqxdhCalculateAgreement_placed_ok hP h_dh h_shdrop h_bb h_shim h_alloc h_stdrop)
    hi (by decide) (by decide)

/-- Lift `PqxdhCalculateAgreementPlacedOk` (`withLsCodeRoLoaded`) to
`PqxdhCalculateAgreementPlacedFrozenOk` (`Keys.LsFrozenInv`). -/
theorem pqxdhCalculateAgreement_placed_frozen_of_cro [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program}
    (h : PqxdhCalculateAgreementPlacedOk M P A lim prog) :
    PqxdhCalculateAgreementPlacedFrozenOk M P A lim prog := by
  refine subroutine_ok_mono h ?_ (fun _ _ _ _ hq => hq)
  rintro ⟨⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩, st⟩ R s0 hp
  dsimp only [pqxdhCalculateAgreementPlacedFrozenSpec, withLsCodeRoLoaded,
    pqxdhCalculateAgreementPlacedBaseSpec] at hp ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hF, hx0, hx1, hx8, hsp_eq, hour, htheir, hfits⟩, hsep⟩
  have hcomm :
      ((⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret ∧
          s0.sp = sp ∧ ourSk32.length = 32 ∧ theirPk32.length = 32 ∧
          FitsEvents M lim st (calculateAgreementEvents P ourSk32 theirPk32)⌝ ∗
        (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
        memRegion ret 24 ∗ A.pool lim st s0 ∗ stackAt sp calculateAgreementStack) ∗
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret ∧
            s0.sp = sp ∧ ourSk32.length = 32 ∧ theirPk32.length = 32 ∧
            FitsEvents M lim st (calculateAgreementEvents P ourSk32 theirPk32)⌝ ∗
          ((ourA ↦ₛ bytesToBv8 ourSk32) ∗ ((theirA ↦ₛ bytesToBv8 theirPk32) ∗
            (memRegion ret 24 ∗ (A.pool lim st s0 ∗
              (stackAt sp calculateAgreementStack ∗ R)))))) := by
    sep_ac_rfl
  rw [hcomm, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨⟨hF.code, hF.ro⟩, ⟨hx0, hx1, hx8, hsp_eq, hour, htheir, hfits⟩, by ac_nf at hsep ⊢⟩

/-- Cross-block `PqxdhCalculateAgreementPlacedFrozenOk` on any caller block `i < 619`. -/
theorem pqxdhCalculateAgreement_placed_frozen_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_frozen_of_cro
    (pqxdhCalculateAgreement_placed_ok_of_block hP h_dh h_shdrop h_bb h_shim h_alloc h_stdrop hi)

/-! ## 3. Relocatable `expand_multi_info` (Block `53`) with `VmPreserved` -/

/-- Cross-block transfer of `expand_multi_info_placed_vm_ok` to any caller block `i < 619`. -/
theorem expand_multi_info_placed_vm_ok_of_other_block [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} (H : LibsignalHooks)
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (expandMultiInfoSpec C.F))) :=
  keys_ls_subroutine_ok_of_block_cro
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (expand_multi_info_placed_vm_ok C H))
    hi (by decide) (by decide)

private theorem satisfies_withLsCodeLoaded_intro {α : Type} {pl : Obj.MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  have hcomm : (spec.pre x s0 ∗ ⌜LibsignalCodeLoaded pl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded pl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by sep_ac_rfl
  rw [hcomm, satisfies_pure_sepConj]
  exact ⟨hcl, hpre⟩

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hi' : i < xs.length := hi
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi']
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem toUTF8_toList_eq (s : String) :
    s.toUTF8.toList = s.toList.flatMap String.utf8EncodeChar := by
  rw [byteArray_toList_eq_data]
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [List.utf8Encode]

private theorem INFO_RATCHET_length : INFO_RATCHET.length = 14 := by
  unfold INFO_RATCHET
  rw [toUTF8_toList_eq]
  decide

private theorem INFO_MSG_KEYS_length : INFO_MSG_KEYS.length = 18 := by
  unfold INFO_MSG_KEYS
  rw [toUTF8_toList_eq]
  decide

/-- `HandshakeDeriveBudget.pqxdhHkdfExpandCellsPlacedSpec P lsmpl 8` (`64` B, `info = INFO_RATCHET`)
on Block `53` from `expand_multi_info_placed_vm_ok`. -/
theorem pqxdhHkdfExpand_8_placed_ok [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl 8) := by
  have hexp := expand_multi_info_placed_vm_ok C H
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpre
  rw [stackAt_alloc_expand sp, ← memRegion_cells okmA 8 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_RATCHET := by
    rcases hcases with ⟨_, hinfo, _⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩
    · exact hinfo
    · omega
    · omega
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 14 := hinfo ▸ INFO_RATCHET_length
  have hinfo_lt : info.length < 23 := by omega
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega)] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 64⟩,
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
      memRegion (sp - 4096#64) 3456 ∗ R, ?_, ?_⟩
  · apply satisfies_withLsCodeLoaded_intro hF.code
    dsimp only [withVmPreserved, expandMultiInfoSpec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inl trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, withVmPreserved, expandMultiInfoSpec,
      pqxdhHkdfExpandCellsPlacedSpec,
      CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpost ⊢
    rw [stackAt_alloc_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    rw [show 8 * 8 = 64 from rfl, bytesToBv8_hkdfExpandRef_64 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 64) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨hvm, htr, by arm64_sep_close⟩

/-- `HandshakeDeriveBudget.pqxdhHkdfExpandCellsPlacedSpec P lsmpl 10` (`80` B, `info = INFO_MSG_KEYS`)
on Block `53` from `expand_multi_info_placed_vm_ok`. -/
theorem pqxdhHkdfExpand_10_placed_ok [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl 10) := by
  have hexp := expand_multi_info_placed_vm_ok C H
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpre
  rw [stackAt_alloc_expand sp, ← memRegion_cells okmA 10 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_MSG_KEYS := by
    rcases hcases with ⟨_, _, hk⟩ | ⟨_, hinfo, _⟩ | ⟨_, _, hk⟩
    · omega
    · exact hinfo
    · omega
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 18 := hinfo ▸ INFO_MSG_KEYS_length
  have hinfo_lt : info.length < 23 := by omega
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega)] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 80⟩,
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
      memRegion (sp - 4096#64) 3456 ∗ R, ?_, ?_⟩
  · apply satisfies_withLsCodeLoaded_intro hF.code
    dsimp only [withVmPreserved, expandMultiInfoSpec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inr trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, withVmPreserved, expandMultiInfoSpec,
      pqxdhHkdfExpandCellsPlacedSpec,
      CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpost ⊢
    rw [stackAt_alloc_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    rw [show 8 * 10 = 80 from rfl, bytesToBv8_hkdfExpandRef_80 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 80) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨hvm, htr, by arm64_sep_close⟩

/-- For any `k ∉ {8, 10, 12}`, `HandshakeDeriveBudget.pqxdhHkdfExpandCellsPlacedSpec P lsmpl k`
has a contradictory precondition on any program `prog`. -/
theorem pqxdhHkdfExpand_other_placed_ok [LibsignalPlacement]
    (P : Primitives) (prog : Program) (k : Nat)
    (hk8 : k ≠ 8) (hk10 : k ≠ 10) (hk12 : k ≠ 12) :
    subroutine_ok prog (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl k) := by
  refine subroutine_ok_outcome_intro ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 _ _ hpre _
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.2.2.2.2.2.2.2 with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · exact (hk8 rfl).elim
  · exact (hk10 rfl).elim
  · exact (hk12 rfl).elim

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget

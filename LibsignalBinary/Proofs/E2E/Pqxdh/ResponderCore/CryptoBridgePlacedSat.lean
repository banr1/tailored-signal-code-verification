/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqROSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain

/-!
# `HookSat`-backed `black_box` Bridge for `<PrivateKey>::calculate_agreement` (`CryptoBridgePlacedSat`)

Replaces `H lsBlackBoxU8Sym = some blackBoxHook` with `HookSat H lsBlackBoxU8Sym blackBoxSpecSat`
in Block `207` `calculate_agreement` (`pqxdhCalculateAgreement_placed_ok_sat`,
`pqxdhCalculateAgreement_placed_ok_of_block_sat`, and
`pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat`), discharging `ct_eq`'s `64`-byte stack
frame inside `allocHookStack = 4096` B.
-/

public section

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedSat

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.Ratchet (X25519Fn)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_207 blkPl_207
   lsBlackBoxU8Sym ls_subroutine_ok_of_block lsmpl withLsCodeLoaded)
open CryptoVerification.E2E (u8Vec)
open CryptoVerification.E2E.Pqxdh.Initiator (Bytes Primitives bytesToBv8)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PqxdhCalculateAgreementPlacedFrozenOk PqxdhCalculateAgreementPlacedOk PrimitivesMatchCrypto
   calculateAgreementResultAt_entails_pqxdh pqxdhCalculateAgreementPlacedBaseSpec
   pqxdhCalculateAgreement_placed_frozen_of_cro u8Vec_toList_of_length)
open CryptoVerification.LibsignalTripleRatchet
  (CalculateAgreementGhost LibsignalCodeRoLoaded calculateAgreement
   calculateAgreementResultAt calculateAgreementSpec calculateAgreementSpecX
   calculateAgreementStack diffieHellmanSpec extract_withLsCodeRoLoaded
   keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro noAllocShimSpec
   rustAllocSpecWithStack rustAllocSpecWithStack_eq_rustAllocSpec
   withLsCodeRoLoaded zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (allocPlacedCallSpec calculateAgreement_placed_ok_of_hooks_gen
   ctEqPlacedCallSpec dhPlacedCallSpec lsDhSym lsHandleAllocErrorSym lsRustAllocSym
   lsRustNoAllocShimSym lsSharedDropSym lsStaticDropSym shimPlacedCallSpec
   subroutine_ok_calculateAgreementSpecX_of_calculateAgreementSpec zeroizePlacedCallSpec)
open CryptoVerification.RustHeap (RustAlloc allocHookStack rustAllocSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqROSat
  (ctEqSliceROMemSpec16 ct_eq_ro_mem_placed_ok_16_withLsCodeLoaded_sat)

private theorem dhPlacedCallAt_of_raw {pl : MultiPlacement} {X : X25519Fn} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (diffieHellmanSpec X)) :
    subroutine_ok prog entry (dhPlacedCallSpec pl X subStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨secA, sec, pubA, pub, ret, sp⟩ R s0 hpre
  dsimp only [dhPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hx8, hsp⟩, hpre⟩
  subst hsp
  refine ⟨(secA, sec, pubA, pub, ret), stackAt s0.sp subStack ∗ R, ?_, ?_⟩
  · dsimp only [diffieHellmanSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [diffieHellmanSpec, dhPlacedCallSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

private theorem zeroizePlacedCallAt_of_raw {pl : MultiPlacement} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry zeroizeSecretSpec) :
    subroutine_ok prog entry (zeroizePlacedCallSpec pl subStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨a, sp⟩ R s0 hpre
  dsimp only [zeroizePlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hsp⟩, hpre⟩
  subst hsp
  refine ⟨a, stackAt s0.sp subStack ∗ R, ?_, ?_⟩
  · dsimp only [zeroizeSecretSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [zeroizeSecretSpec, zeroizePlacedCallSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

private theorem shimPlacedCallAt_of_raw {pl : MultiPlacement} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry noAllocShimSpec) :
    subroutine_ok prog entry (shimPlacedCallSpec pl subStack) := by
  refine subroutine_ok_map h ?_
  rintro sp R s0 hpre
  dsimp only [shimPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hsp⟩, hpre⟩
  refine ⟨(), stackAt sp subStack ∗ R, ?_, ?_⟩
  · change s0.mem ⊨ emp ∗ (stackAt sp subStack ∗ R)
    simpa only [emp_sepConj] using hpre
  · intro sf hpost
    change sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗ (stackAt sp subStack ∗ R) at hpost
    dsimp only [shimPlacedCallSpec]
    rwa [sepConj_assoc]

private theorem allocPlacedCallAt_of_allocStack {pl : MultiPlacement} {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustAllocSpec A)) :
    subroutine_ok prog entry (allocPlacedCallSpec pl A allocHookStack) := by
  rw [← rustAllocSpecWithStack_eq_rustAllocSpec A] at h
  refine subroutine_ok_map h ?_
  rintro ⟨size, align, sp⟩ R s0 hpre
  dsimp only [allocPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hlay, hsp⟩, hpre⟩
  subst hsp
  refine ⟨(size, align), R, ?_, ?_⟩
  · dsimp only [rustAllocSpecWithStack]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay⟩, hpre⟩
  · intro sf hpost
    dsimp only [rustAllocSpecWithStack, allocPlacedCallSpec] at hpost ⊢
    exact hpost

private theorem stackAt_allocHookStack_eq_mem64 (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 64#64) 64 ∗ stackAt (sp - 64#64) 4032 := by
  rw [sepConj_comm]
  simp only [stackAt, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 4096) (n := 4032) (k := 64)
    (b' := sp - 64#64) rfl (by bv_omega) (by decide)]
  have hsub : sp - 64#64 - BitVec.ofNat 64 4032 = sp - BitVec.ofNat 64 4096 := by bv_omega
  rw [hsub]

/-- Lift `withLsCodeLoaded pl ctEqSliceROMemSpec16` (`64` B) to
`ctEqPlacedCallSpec pl allocHookStack` (`4096` B). -/
theorem ctEqPlacedCallAt_of_mem16_withLsCodeLoaded {pl : MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl ctEqSliceROMemSpec16)) :
    subroutine_ok prog entry (ctEqPlacedCallSpec pl allocHookStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  dsimp only [ctEqPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfr, hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  refine ⟨(p1, k1, p2, k2, sp), stackAt (sp - 64#64) 4032 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeLoaded, ctEqSliceROMemSpec16]
    rw [stackAt_allocHookStack_eq_mem64 sp] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr.1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hsp, hk1, hk2⟩, by simpa only [sepConj_assoc] using hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, ctEqSliceROMemSpec16, ctEqPlacedCallSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hres, htr⟩, hpost⟩
    refine ⟨⟨by rw [hres]; split <;> rfl, htr⟩, ?_⟩
    rw [stackAt_allocHookStack_eq_mem64 sp]
    simpa only [sepConj_assoc] using hpost

/-- Unconditional relocatable `<PrivateKey>::calculate_agreement` (Block `207`) under
`HookSat H lsBlackBoxU8Sym blackBoxSpecSat`. -/
theorem calculateAgreement_placed_ok_unconditional_sat [LibsignalPlacement]
    {X : X25519Fn} {A : RustAlloc} {H : String → Option (State → State)}
    (h_dh : HookSat H lsDhSym (diffieHellmanSpec X))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec X A)) := by
  have hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROMemSpec16) :=
    ls_subroutine_ok_of_block (ct_eq_ro_mem_placed_ok_16_withLsCodeLoaded_sat h_bb)
  exact calculateAgreement_placed_ok_of_hooks_gen (subStack := allocHookStack) (by decide)
    (dhPlacedCallAt_of_raw (keys_ls_hook_ok_of_mem h_dh))
    (zeroizePlacedCallAt_of_raw (keys_ls_hook_ok_of_mem h_shdrop))
    (ctEqPlacedCallAt_of_mem16_withLsCodeLoaded hct)
    (shimPlacedCallAt_of_raw (keys_ls_hook_ok_of_mem h_shim))
    (allocPlacedCallAt_of_allocStack (keys_ls_hook_ok_of_mem h_alloc))
    (zeroizePlacedCallAt_of_raw (keys_ls_hook_ok_of_mem h_stdrop))
    hpanic

/-- Unconditional relocatable `<PrivateKey>::calculate_agreement` (Block `207`) at
`calculateAgreementStackX` under `HookSat H lsBlackBoxU8Sym blackBoxSpecSat`. -/
theorem calculateAgreement_placed_ok_x_unconditional_sat [LibsignalPlacement]
    {X : X25519Fn} {A : RustAlloc} {H : String → Option (State → State)}
    (h_dh : HookSat H lsDhSym (diffieHellmanSpec X))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpecX X A)) :=
  subroutine_ok_calculateAgreementSpecX_of_calculateAgreementSpec
    (calculateAgreement_placed_ok_unconditional_sat h_dh h_shdrop h_bb h_shim h_alloc h_stdrop
      hpanic)

/-- `HookSat` `black_box` sibling of `pqxdhCalculateAgreement_placed_ok`
(`CryptoBridgePlaced.lean:88`). -/
theorem pqxdhCalculateAgreement_placed_ok_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H lsDhSym (diffieHellmanSpec C.X))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    PqxdhCalculateAgreementPlacedOk P A ((blkPC_207).rebase (blkPl_207).base H) := by
  unfold PqxdhCalculateAgreementPlacedOk
  have hraw :=
    calculateAgreement_placed_ok_unconditional_sat h_dh h_shdrop h_bb h_shim h_alloc h_stdrop hpanic
  refine subroutine_ok_outcome_intro ?_
  rintro ⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩ R s0 hpc hrun hpre hsp
  obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [pqxdhCalculateAgreementPlacedBaseSpec,
    CryptoVerification.E2E.Pqxdh.ResponderCore.calculateAgreementStack] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hsp_eq, hour, htheir⟩, hpre⟩
  let xg : CalculateAgreementGhost := ⟨ourA, ⟨u8Vec 32 ourSk32⟩, theirA, ⟨u8Vec 32 theirPk32⟩, ret⟩
  have hour_list : xg.our.bytes.toList = bytesToBv8 ourSk32 := u8Vec_toList_of_length hour
  have htheir_list : xg.their.bytes.toList = bytesToBv8 theirPk32 := u8Vec_toList_of_length htheir
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec C.X A)).pre xg s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, calculateAgreementSpec, calculateAgreementStack]
    rw [hour_list, htheir_list, hsp_eq]
    have hcomm :
        ((⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret⌝ ∗
          (xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ (xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
          memRegion xg.ret 24 ∗ A.pool ∗ stackAt sp (160 + allocHookStack)) ∗
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = xg.ourA ∧ s0.readReg64 .x1 = xg.theirA ∧ s0.readReg64 .x8 = xg.ret⌝ ∗
            ((xg.ourA ↦ₛ bytesToBv8 ourSk32) ∗ ((xg.theirA ↦ₛ bytesToBv8 theirPk32) ∗
              (memRegion xg.ret 24 ∗ (A.pool ∗ (stackAt sp (160 + allocHookStack) ∗ R)))))) := by
      sep_ac_rfl
    rw [hcomm, satisfies_pure_sepConj, satisfies_pure_sepConj]
    dsimp only [xg]
    exact ⟨hfr, ⟨hx0, hx1, hx8⟩, by ac_nf at hpre ⊢⟩
  refine (hraw.to_outcome xg R s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with
    ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, calculateAgreementSpec, calculateAgreementStack,
      pqxdhCalculateAgreementPlacedBaseSpec,
      CryptoVerification.E2E.Pqxdh.ResponderCore.calculateAgreementStack] at hq ⊢
    rw [hour_list, htheir_list, hsp_eq] at hq
    have hE := calculateAgreementResultAt_entails_pqxdh hP A ret ourSk32 theirPk32
    have hq1 : sf.mem ⊨
        calculateAgreementResultAt A ret (calculateAgreement C.X xg.their xg.our) ∗
          (⌜sf.trace = s0.trace⌝ ∗
            (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            A.pool ∗ stackAt sp (160 + allocHookStack) ∗ R) := by
      ac_nf at hq ⊢
    have hq2 := Satisfies.mono (sepConj_mono_left hE) hq1
    ac_nf at hq2 ⊢
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-- `HookSat` `black_box` sibling of `pqxdhCalculateAgreement_placed_ok_of_block`
(`CryptoBridgePlaced.lean:153`). -/
theorem pqxdhCalculateAgreement_placed_ok_of_block_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H lsDhSym (diffieHellmanSpec C.X))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk P A callerProg :=
  keys_ls_subroutine_ok_of_block_cro
    (pqxdhCalculateAgreement_placed_ok_sat hP h_dh h_shdrop h_bb h_shim h_alloc h_stdrop hpanic)
    hi (by decide) (by decide)

/-- `HookSat` `black_box` sibling of `pqxdhCalculateAgreement_placed_frozen_ok_of_block`
(`CryptoBridgePlaced.lean:199`). -/
theorem pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hP : PrimitivesMatchCrypto P C)
    (h_dh : HookSat H lsDhSym (diffieHellmanSpec C.X))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk P A callerProg :=
  pqxdhCalculateAgreement_placed_frozen_of_cro
    (pqxdhCalculateAgreement_placed_ok_of_block_sat hP h_dh h_shdrop h_bb h_shim h_alloc h_stdrop
      hpanic hi)

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedSat

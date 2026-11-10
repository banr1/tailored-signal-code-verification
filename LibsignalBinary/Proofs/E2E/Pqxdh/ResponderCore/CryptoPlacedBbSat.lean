/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat -- proof-setup: allow-public-import

/-!
# `HookSat`-backed `black_box` Layer on `CryptoPlacedSat` (`CryptoPlacedBbSat`)

Stacks `blackBox : HookSat H lsBlackBoxU8Sym blackBoxSpecSat` on top of PR #1315's
`CryptoPlacedSat.PqxdhPlacedHookContractsSat` (`CryptoPlacedSat.lean:719`), keeping identical field
names and keeping `hkdf : HkdfPlacedHooksSat C.F H` unchanged.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedBbSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsBlackBoxU8Sym lsRustDeallocSym)
open CryptoVerification.E2E.Pqxdh.Initiator
  (PqxdhHkdfExpandMultiInfoPlacedOk PqxdhHkdfExtractPlacedOk Primitives
   cryptoBoolRegStubSpec kyberDecapsStubSpec)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PqxdhCalculateAgreementPlacedFrozenOk PqxdhCalculateAgreementPlacedOk PqxdhPlacedHookContracts
   PrimitivesMatchCrypto dalekMontToEdStubSpec lsDalekMontToEdSym lsDalekTorsionFreeSym
   lsHandleErrorSym lsKyberDecapsSym)
open CryptoVerification.LibsignalTripleRatchet
  (diffieHellmanSpec noAllocShimSpec zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (lsDhSym lsHandleAllocErrorSym lsRustAllocSym lsRustNoAllocShimSym lsSharedDropSym lsStaticDropSym)
open CryptoVerification.RustHeap (RustAlloc rustAllocSpec rustDeallocSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat hookSat_blackBox_of_eq)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedSat
  (pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat pqxdhCalculateAgreement_placed_ok_of_block_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat
  (PqxdhPlacedHookContractsSat pqxdhHkdfExpandMultiInfo_placed_ok_sat
   pqxdhHkdfExtract_placed_ok_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksSat)

/-- `HookSat`-backed `black_box` sibling of `CryptoPlacedSat.PqxdhPlacedHookContractsSat`
(`CryptoPlacedSat.lean:719`), keeping identical field names and `hkdf : HkdfPlacedHooksSat C.F H`
unchanged while weakening `blackBox` to `HookSat H lsBlackBoxU8Sym blackBoxSpecSat`. -/
structure PqxdhPlacedHookContractsBbSat (P : Primitives) (C : Crypto) (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  hkdf             : HkdfPlacedHooksSat C.F H
  dh               : HookSat H lsDhSym (diffieHellmanSpec C.X)
  sharedDrop       : HookSat H lsSharedDropSym zeroizeSecretSpec
  staticDrop       : HookSat H lsStaticDropSym zeroizeSecretSpec
  blackBox         : HookSat H lsBlackBoxU8Sym blackBoxSpecSat
  noAllocShim      : HookSat H lsRustNoAllocShimSym noAllocShimSpec
  alloc            : HookSat H lsRustAllocSym (rustAllocSpec A)
  dealloc          : HookSat H lsRustDeallocSym (rustDeallocSpec A)
  handleAllocError : H lsHandleAllocErrorSym = some Rust.panicked
  handleError      : H lsHandleErrorSym = some Rust.panicked
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubSpec P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpec P)
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)

/-- Coercion `PqxdhPlacedHookContractsSat → PqxdhPlacedHookContractsBbSat` via
`hookSat_blackBox_of_eq`. -/
theorem PqxdhPlacedHookContractsSat.toBbSat {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks} (h : PqxdhPlacedHookContractsSat P C A H) :
    PqxdhPlacedHookContractsBbSat P C A H :=
  { hkdf             := h.hkdf
    dh               := h.dh
    sharedDrop       := h.sharedDrop
    staticDrop       := h.staticDrop
    blackBox         := hookSat_blackBox_of_eq h.blackBox
    noAllocShim      := h.noAllocShim
    alloc            := h.alloc
    dealloc          := h.dealloc
    handleAllocError := h.handleAllocError
    handleError      := h.handleError
    kyberDecaps      := h.kyberDecaps
    dalekMontToEd    := h.dalekMontToEd
    dalekTorsionFree := h.dalekTorsionFree }

/-- Direct coercion `PqxdhPlacedHookContracts → PqxdhPlacedHookContractsBbSat`. -/
theorem PqxdhPlacedHookContracts.toBbSat {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks} (h : PqxdhPlacedHookContracts P C A H) :
    PqxdhPlacedHookContractsBbSat P C A H :=
  PqxdhPlacedHookContractsSat.toBbSat
    (LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat.PqxdhPlacedHookContracts.toSat h)

theorem PqxdhPlacedHookContractsBbSat.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk P A callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block_sat hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.handleAllocError hi

theorem PqxdhPlacedHookContractsBbSat.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk P A callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.handleAllocError hi

theorem PqxdhPlacedHookContractsBbSat.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have _ : HkdfPlacedHooksSat C.F H := hH.hkdf
  exact pqxdhHkdfExtract_placed_ok_sat hP hi

theorem PqxdhPlacedHookContractsBbSat.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsBbSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have _ : HkdfPlacedHooksSat C.F H := hH.hkdf
  exact pqxdhHkdfExpandMultiInfo_placed_ok_sat hP hi

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedBbSat

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlaced -- proof-setup: allow-public-import

/-!
# `HookSat`-backed `black_box` Sibling of `CryptoCalleesPlaced` (`CryptoCalleesPlacedSat`)

Replaces `blackBox : H lsBlackBoxU8Sym = some blackBoxHook` in `PqxdhPlacedHookContracts`
(`CryptoCalleesPlaced.lean:643`) with `blackBox : HookSat H lsBlackBoxU8Sym blackBoxSpecSat`,
providing `PqxdhPlacedHookContractsSat`, `PqxdhPlacedHookContracts.toSat`, and the four bundle
projections (`calculateAgreement_ok`, `calculateAgreement_frozen_ok`, `hkdfExtract_ok`,
`hkdfExpandMultiInfo_ok`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedSat

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
   lsHandleErrorSym lsKyberDecapsSym pqxdhHkdfExpandMultiInfo_placed_ok pqxdhHkdfExtract_placed_ok)
open CryptoVerification.LibsignalTripleRatchet
  (HkdfPlacedHooks diffieHellmanSpec noAllocShimSpec zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (lsDhSym lsHandleAllocErrorSym lsRustAllocSym lsRustNoAllocShimSym lsSharedDropSym lsStaticDropSym)
open CryptoVerification.RustHeap (RustAlloc rustAllocSpec rustDeallocSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat hookSat_blackBox_of_eq)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedSat
  (pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat pqxdhCalculateAgreement_placed_ok_of_block_sat)

/-- `HookSat`-backed `black_box` sibling of `PqxdhPlacedHookContracts`
(`CryptoCalleesPlaced.lean:643`), replacing `blackBox : H lsBlackBoxU8Sym = some blackBoxHook`
with `blackBox : HookSat H lsBlackBoxU8Sym blackBoxSpecSat`. -/
structure PqxdhPlacedHookContractsSat (P : Primitives) (C : Crypto) (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  hkdf             : HkdfPlacedHooks C.F H
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

/-- Exact-to-`HookSat` bridge from `PqxdhPlacedHookContracts` (`CryptoCalleesPlaced.lean:643`) to
`PqxdhPlacedHookContractsSat`. -/
theorem PqxdhPlacedHookContracts.toSat {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks} (h : PqxdhPlacedHookContracts P C A H) :
    PqxdhPlacedHookContractsSat P C A H :=
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

theorem PqxdhPlacedHookContractsSat.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk P A callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block_sat hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.handleAllocError hi

theorem PqxdhPlacedHookContractsSat.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk P A callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block_sat hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.handleAllocError hi

theorem PqxdhPlacedHookContractsSat.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact pqxdhHkdfExtract_placed_ok hP hi

theorem PqxdhPlacedHookContractsSat.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact pqxdhHkdfExpandMultiInfo_placed_ok hP hi

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedSat

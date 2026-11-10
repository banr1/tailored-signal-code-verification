/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import

/-!
# `HookSat` `black_box` Sibling of `Initiate.RunHooksPlaced` (`HooksPlacedSat`)

Weakens `blackBox : H lsBlackBoxSym = some blackBoxHook` in `Initiate.RunHooksPlaced` to
`blackBox : HookSat H lsBlackBoxSym blackBoxSpecSat`, with `RunHooksPlaced.toSat`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedSat

open Arm64 ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement)
open CryptoVerification.E2E (bcmpName kemEncapsHook)
open CryptoVerification.E2E.HooksE (e2eBcmpSpec)
open CryptoVerification.LibsignalPublicApi (stringCloneSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit (TraceFsSound)
open CryptoVerification.LibsignalTripleRatchet
  (HkdfPlacedHooks derivePublicKeyBytesSpec diffieHellmanSpec formatInnerSpec framelessMemcpySpec
   memcpyName noAllocShimSpec rustAllocZeroedSpec sessionMemcpyRegionSpec zeroizeSecretSpec)
open CryptoVerification.RecordCodecsBinary (CodecHooksPlaced)
open CryptoVerification.RustHeap
  (RustAlloc rustAllocSpec rustDeallocSpec)
open CryptoVerification.SignalSession
  (CliHooks cliPanicSymbolsPlaced durationSinceExactHook lsBlackBoxSym lsDiffieHellmanSym
   lsDurationSinceSym lsFormatInnerSym lsPubFromSecretSym lsRustAllocSymCli lsRustAllocZeroedSymCli
   lsRustDeallocSymCli lsRustNoAllocShimSymCli lsSharedSecretDropSym lsStaticSecretDropSym
   lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (cliBcmpName cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.MainHops
  (AllocContractsFsPlaced AllocContractsXCliPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (RunHooksPlaced lsKemEncapsSym)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat hookSat_blackBox_of_eq)
open Proofs.libsignal.Hooks2 (SerContractsXPlaced)

/-- `HookSat` `black_box` sibling of `Initiate.RunHooksPlaced` (`HooksPlaced.lean:138`),
weakening `blackBox` to `HookSat H lsBlackBoxSym blackBoxSpecSat`. -/
structure RunHooksPlacedSat [LibsignalPlacement] (W : CliHooks) (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  alloc : AllocContractsXCliPlaced A H
  allocFs : AllocContractsFsPlaced A H
  codec : CodecHooksPlaced A H
  ser : SerContractsXPlaced A H
  shim : HookSat H lsRustNoAllocShimSymCli noAllocShimSpec
  rawAlloc : HookSat H lsRustAllocSymCli (rustAllocSpec A)
  rawDealloc : HookSat H lsRustDeallocSymCli (rustDeallocSpec A)
  framelessMemcpy : HookSat H memcpyName framelessMemcpySpec
  sessionMemcpyRegion : HookSat H memcpyName sessionMemcpyRegionSpec
  memcpyRO : HookSat H memcpyName sessionMemcpyRegionROSpec
  bcmp : HookSat H cliBcmpName cliBcmpSpec
  e2eBcmp : HookSat H bcmpName e2eBcmpSpec
  allocZeroed : HookSat H lsRustAllocZeroedSymCli (rustAllocZeroedSpec A)
  stringClone : HookSat H lsStringCloneSym (stringCloneSpec A)
  formatInner : HookSat H lsFormatInnerSym (formatInnerSpec A)
  pubFromSecret : HookSat H lsPubFromSecretSym (derivePublicKeyBytesSpec W.C.pubKey)
  dh : HookSat H lsDiffieHellmanSym (diffieHellmanSpec W.C.X)
  sharedDrop : HookSat H lsSharedSecretDropSym zeroizeSecretSpec
  staticDrop : HookSat H lsStaticSecretDropSym zeroizeSecretSpec
  blackBox : HookSat H lsBlackBoxSym blackBoxSpecSat
  hkdf : HkdfPlacedHooks W.C.F H
  kemEncaps : H lsKemEncapsSym = some (kemEncapsHook W.Q.encaps)
  durationSince : H lsDurationSinceSym = some durationSinceExactHook
  panic_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked
  panic_raw : H "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked
  panic_sym : ∀ s, s ∈ cliPanicSymbolsPlaced → H s = some Rust.panicked
  fs : ∀ {prog : Program} {i : Nat} [IsLsBlockProg prog i H], TraceFsSound prog

/-- Coercion `RunHooksPlaced → RunHooksPlacedSat` via `hookSat_blackBox_of_eq`. -/
theorem RunHooksPlaced.toSat [LibsignalPlacement] {W : CliHooks} {A : RustAlloc}
    {H : LibsignalHooks} (h : RunHooksPlaced W A H) :
    RunHooksPlacedSat W A H where
  alloc := h.alloc
  allocFs := h.allocFs
  codec := h.codec
  ser := h.ser
  shim := h.shim
  rawAlloc := h.rawAlloc
  rawDealloc := h.rawDealloc
  framelessMemcpy := h.framelessMemcpy
  sessionMemcpyRegion := h.sessionMemcpyRegion
  memcpyRO := h.memcpyRO
  bcmp := h.bcmp
  e2eBcmp := h.e2eBcmp
  allocZeroed := h.allocZeroed
  stringClone := h.stringClone
  formatInner := h.formatInner
  pubFromSecret := h.pubFromSecret
  dh := h.dh
  sharedDrop := h.sharedDrop
  staticDrop := h.staticDrop
  blackBox := hookSat_blackBox_of_eq h.blackBox
  hkdf := h.hkdf
  kemEncaps := h.kemEncaps
  durationSince := h.durationSince
  panic_alloc := h.panic_alloc
  panic_raw := h.panic_raw
  panic_sym := h.panic_sym
  fs := h.fs

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedSat

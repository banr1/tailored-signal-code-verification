/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeW
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergePhase23WPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergePlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Handshake `bytes::merge [local#5]` W-Mode Verification

Specializes the unified Block-`514` `bytesMerge3RawSpecBoth` contracts from
`SpqrH/BytesMerge6Placed.lean` to `bytesMerge3RawSpecW` (`x.bs.length < 2 ^ 62`) and lifts them to
caller blocks.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

/-- Specialize any `bytesMerge3RawSpecBoth` contract to `bytesMerge3RawSpecW` (`x.bs.length < 2 ^ 62`). -/
theorem subroutine_ok_bytesMerge3W_of_both [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (hok : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A)) := by
  intro x R s0 hpc hrun hpre hal hL
  obtain ⟨_, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMerge3RawSpecW, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hw0, hx1, hx2, hlen62⟩, _⟩ := hpre0
  have hbs_len : x.bs.length < 2 ^ 63 := by omega
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A)).pre x s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpecW, bytesMerge3RawSpecBoth] at hpre ⊢
    exact Satisfies.mono
      (Entails.of_eq (by simp only [hw0, hx1, hx2, hlen62, hbs_len, or_true, and_self])) hpre
  obtain ⟨sf, hs, hout⟩ := hok x R s0 hpc hrun hpre' hal hL
  refine ⟨sf, hs, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpecBoth, bytesMerge3RawSpecW] at hpost ⊢
    rcases hmb : mergeBytes x.wt x.bs with _ | ⟨v, rest⟩
    · simpa only [hmb] using hpost
    · simp only [hmb] at hpost ⊢
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))))))
      exact Entails.sepExists_mono fun cap' => Entails.sepExists_mono fun ptr' =>
        Entails.pure_left fun _ => Entails.refl _
  · exact Or.inr hfail

theorem bytes_merge_6_placed_ok_of_contractsW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_514 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy") framelessMemcpySpec)
    (hshim : subroutine_ok (lsProg_514 H) (lsρ lsRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_514 H) (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpecWithStack A extHookStack)))
    (hpanic : (lsProg_514 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (hDecodeVarint5 : subroutine_ok (lsProg_514 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A)))
    (hBytesFromVec : subroutine_ok (lsProg_514 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok (lsProg_514 H) (lsmpl.base 517)
      (withLsCl lsmpl (doReserve1VecSpecX A)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_514 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecX A tmpPtr v v.length))) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A)) :=
  subroutine_ok_bytesMerge3W_of_both
    (bytes_merge_6_both_placed_ok_of_contracts hdef hmc hshim halloc hpanic hDecodeVarint5
      hBytesFromVec hReserve hVtableDrop)

theorem bytes_merge_6_placed_ok_w [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A)) :=
  subroutine_ok_bytesMerge3W_of_both
    (bytes_merge_6_both_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw)

/-- Caller-lifted `bytesMerge3RawSpecW` contract at `lsmpl.base 514` (`withLsCodeRoLoaded`). -/
theorem bytes_merge_6_placed_ok_w_cro [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A)) :=
  bytes_merge_6_cro_of_514
    (bytes_merge_6_placed_ok_w hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw) hi

/-- Caller-lifted `bytesMerge3RawSpecW` contract at `lsmpl.base 514` (`withLsCl`), given `.rodata` loadedness. -/
theorem bytes_merge_6_placed_ok_w_cl [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hro : ∀ m, LibsignalCodeLoaded lsmpl m → LibsignalRoLoaded lsmpl m)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (bytesMerge3PlacedSpecW A) :=
  subroutine_ok_withLsCl_of_cro
    (bytes_merge_6_placed_ok_w_cro hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw hi)
    hro

/-- Relocatable `[LibsignalPlacement]` W-contract for `bytes::merge [local#5]` (Block `514`) on `lsProg_518 ext`. -/
def BytesMerge6Placed514OkExtW [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 514)
    (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  bytesMerge3PlacedSpecW
  BytesMerge6PlacedOkExtW
  BytesMerge6Placed514OkExtW
  subroutine_ok_bytesMerge3W_of_both
  bytes_merge_6_placed_ok_of_contractsW
  bytes_merge_6_placed_ok_w
  bytes_merge_6_placed_ok_w_cro
  bytes_merge_6_placed_ok_w_cl
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

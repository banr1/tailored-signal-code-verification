/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBase
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1SentPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirection
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Unconditional Relocatable `[LibsignalPlacement]` Closure for `PqRatchetState::encode_to_vec` (`Block 426`)

Discharges all 7 sub-message encoder callee contracts (`ChainParams`, `EpochDirection`,
`Authenticator`, `PolynomialEncoder`, `PolynomialDecoder`, `EkSentCt1Received`, `Ct1Sent`) on
`FinalPlaced` to establish unconditional `pqRatchetStateEncodeToVec_{ro_pinned_,ro_,pinned_,}placed_ok{_ext}`
under `[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Prost.MessageEncode

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup

private theorem elim_exact_cap_ptr_etv {A : RustAlloc} {v cap ptr : BitVec 64}
    {bs1 bs2 : List (BitVec 8)} (hfit : bs1.length + bs2.length ≤ cap.toNat) :
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜cap.toNat ≤ cap'.toNat ∧ (bs1.length + bs2.length ≤ cap.toNat → cap' = cap ∧ ptr' = ptr)⌝ ∗
      vecU8At A v cap' ptr' (bs1 ++ bs2)) ⊢
    vecU8At A v cap ptr (bs1 ++ bs2) :=
  Entails.sepExists_elim fun cap' => Entails.sepExists_elim fun ptr' =>
    Entails.pure_left fun ⟨_, hpres⟩ => by obtain ⟨rfl, rfl⟩ := hpres hfit; exact Entails.refl _

theorem etv_encodeChainParams_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {prog : Program} {call_pc : BitVec 64} {A : RustAlloc}
    (hcp_ok : subroutine_ok prog call_pc (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf resStack A))) :
    subroutine_ok prog call_pc (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [encodeChainParamsExactSpecOf] at hpre
  rw [stackAt_callee_eq_msgEnc48Varint hres s.sp, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hw1, hw2, hx3, htag1, htag2, hfit⟩, hm⟩
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 80
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf resStack A)).pre
      ⟨x.tag, x.p, x.v, x.cap, x.ptr, x.bs⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [withLsCodeLoaded, encodeChainParamsSpecOf, encodeChainParamsMsg]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hw0, hw1, hw2, hx3, htag1, htag2, Or.inl hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem, msgEnc48VarintStackOf]; ac_rfl)) hm
  refine hcp_ok.mono_outcome ⟨x.tag, x.p, x.v, x.cap, x.ptr, x.bs⟩ (F_rem ∗ R) s hpc hrun hpre' hal
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodeChainParamsSpecOf, encodeChainParamsMsg,
      encodeChainParamsExactSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_msgEnc48Varint hres s.sp]
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (elim_exact_cap_ptr_etv hfit)))) ?_
    exact Entails.of_eq (by dsimp only [F_rem, msgEnc48VarintStackOf]; ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCodeLoaded, encodeChainParamsSpecOf, msgEncOnPanic,
      encodeChainParamsExactSpecOf, encodeToVecOnPanic] at hq ⊢
    rw [← sepConj_assoc] at hq
    exact allowPanic_frame id hq
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_encodeChainParams_exact_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A)) :=
  etv_encodeChainParams_exact_of_lscl (by decide)
    (ls_subroutine_ok_of_block (encode_chainParams_2_placed_ok h_panic hshim halloc hrealloc))

theorem etv_encodeChainParams_exact_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A)) :=
  etv_encodeChainParams_exact_of_lscl (by decide)
    (ls_subroutine_ok_of_block (encode_chainParams_2_placed_ok_x h_panic hshim halloc hrealloc))

theorem etv_encodeEpochDirection_exact_of_lscl [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {prog : Program} {call_pc : BitVec 64} {A : RustAlloc}
    (hed_ok : subroutine_ok prog call_pc (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf resStack A))) :
    subroutine_ok prog call_pc (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [encodeEpochDirectionExactSpecOf] at hpre
  rw [stackAt_callee_eq_authEncode hres s.sp, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hx1, hx2, hfit⟩, hm⟩
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 64
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf resStack A)).pre
      ⟨x.tag, x.dirA, x.g, x.dir, x.v, x.cap, x.ptr, x.bs⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [withLsCodeLoaded, encodeEpochDirectionPinnedSpecOf, encodeEpochDirectionMsg]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hw0, hx1, hx2, Or.inl hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem, authEncodeStackOf]; ac_rfl)) hm
  refine hed_ok.mono_outcome ⟨x.tag, x.dirA, x.g, x.dir, x.v, x.cap, x.ptr, x.bs⟩ (F_rem ∗ R) s
    hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodeEpochDirectionPinnedSpecOf, encodeEpochDirectionMsg,
      encodeEpochDirectionExactSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_authEncode hres s.sp]
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (elim_exact_cap_ptr_etv hfit))))) ?_
    exact Entails.of_eq (by dsimp only [F_rem, authEncodeStackOf]; ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCodeLoaded, encodeEpochDirectionPinnedSpecOf, msgEncOnPanic,
      encodeEpochDirectionExactSpecOf, encodeToVecOnPanic] at hq ⊢
    rw [← sepConj_assoc] at hq
    exact allowPanic_frame id hq
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_encodeEpochDirection_exact_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A)) :=
  etv_encodeEpochDirection_exact_of_lscl (by decide)
    (ls_subroutine_ok_of_block (encode_epochDirection_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc))

theorem etv_encodeEpochDirection_exact_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A)) :=
  etv_encodeEpochDirection_exact_of_lscl (by decide)
    (ls_subroutine_ok_of_block (encode_epochDirection_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc))

/-! ## Unconditional Top-Level `[LibsignalPlacement]` Closure (`Block 426`) -/

theorem pqRatchetStateEncodeToVec_ro_pinned_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStack A)) :=
  pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_contracts
    h_panic hshim halloc hrealloc hmc
    (etv_encodeChainParams_exact_placed_ok h_panic hshim halloc hrealloc)
    (etv_encodeEpochDirection_exact_placed_ok h_panic hshim halloc hrealloc hmc)
    (etv_authEncode_exact_placed_ok h_panic hshim halloc hrealloc hmc)
    (etv_polyEncoderEncode_exact_placed_ok h_panic hshim halloc hrealloc hmc)
    (etv_polyDecoderEncode_exact_placed_ok h_panic hshim halloc hrealloc hmc)
    (etv_ekSentCt1ReceivedEncode_placed_ok h_panic hshim halloc hrealloc hmc)
    (etv_ct1SentEncode_placed_ok h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_ro_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPlacedSpecOf doReserveStack A)) :=
  pqRatchetStateEncodeToVec_ro_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_ro_pinned_placed_ok_ext h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_pinned_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    PqRatchetStateEncodeToVecPinnedPlacedOkExt A ext :=
  pqRatchetStateEncodeToVec_pinned_placed_ok_of_contracts
    h_panic hshim halloc hrealloc hmc
    (etv_encodeChainParams_exact_placed_ok_x h_panic hshim halloc hrealloc)
    (etv_encodeEpochDirection_exact_placed_ok_x h_panic hshim halloc hrealloc hmc)
    (etv_authEncode_exact_placed_ok_x h_panic hshim halloc hrealloc hmc)
    (etv_polyEncoderEncode_exact_placed_ok_x h_panic hshim halloc hrealloc hmc)
    (etv_polyDecoderEncode_exact_placed_ok_x h_panic hshim halloc hrealloc hmc)
    (etv_ekSentCt1ReceivedEncode_placed_ok_x h_panic hshim halloc hrealloc hmc)
    (etv_ct1SentEncode_placed_ok_x h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    PqRatchetStateEncodeToVecPlacedOkExt A ext :=
  pqRatchetStateEncodeToVec_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_pinned_placed_ok_ext h_panic hshim halloc hrealloc hmc)

theorem pqRatchetStateEncodeToVec_pinned_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    PqRatchetStateEncodeToVecPinnedPlacedOkExt A ext :=
  pqRatchetStateEncodeToVec_pinned_placed_ok_ext h_panic hshim halloc hrealloc hmc

theorem pqRatchetStateEncodeToVec_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec) :
    PqRatchetStateEncodeToVecPlacedOkExt A ext :=
  pqRatchetStateEncodeToVec_placed_ok_ext h_panic hshim halloc hrealloc hmc

end CryptoVerification.SpqrV1.Prost.EncodeToVec

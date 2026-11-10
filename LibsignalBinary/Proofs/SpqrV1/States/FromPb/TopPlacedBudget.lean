/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DecoderFromPbClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbProofClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4ePlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9PlacedBudget

/-!
# Budget-Threaded Relocatable Top-Level Proof for `<States>::from_pb` (Block `333`)

Discharges `<PolyEncoder>::from_pb` (Block `374`), `<PolyDecoder>::from_pb` (Block `376`), and all
12 `Option V1State.InnerState` branches under `[LibsignalPlacement]` and `RustCliAllocBudget M` to
prove `StatesFromPbPlacedOkExt` and `StatesFromPbPlacedOkX`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget)

private theorem hookSat_sessionMemmoveVmAcp_of_withAllocVmPreserved
    {H : String → Option (State → State)} (hookStack : Nat := 0)
    (h : HookSat H spqrMemmoveSym
      (LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget.withAllocVmPreserved
        (sessionMemmoveSpec hookStack))) :
    HookSat H spqrMemmoveSym
      (LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbInnerPlacedBudget.sessionMemmoveVmAcpSpec
        hookStack) := by
  rcases h with ⟨fn, hfn, hbody⟩
  refine ⟨fn, hfn, fun (base, buf, dst, src, len) R s0 hrun hpre hal => ?_⟩
  obtain ⟨hkf, hsym, hout⟩ := hbody (base, buf, dst, src, len) R s0 hrun hpre hal
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget.withAllocVmPreserved,
      sessionMemmoveSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hacp, hvm⟩, hpost⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0, htr⟩, hrest⟩
    dsimp only [LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbInnerPlacedBudget.sessionMemmoveVmAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, htr, hacp, hvm⟩, hrest⟩
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem encoder_from_pb_ok_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    EncoderFromPbPlacedOkExt M A lim ext :=
  Variant2aPlacedBudgetAux.encoder_from_pb_ok_of_alloc_placed hA

theorem decoder_from_pb_ok_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    DefsBudget.DecoderFromPbPlacedOkExt M A lim ext :=
  DecoderFromPbClPlacedBudget.decoder_from_pb_on_333_placed_ok_ext
    hA.alloc hA.shim hA.dealloc
    (DecoderFromPbClPlacedBudget.hookSat_sessionMemcpyVmAcp_of_allocMemcpyVm 4096 hA.memcpy)
    (hookSat_sessionMemmoveVmAcp_of_withAllocVmPreserved 0 hmemmove)

theorem rodata_statesFromPbJumpTable_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ statesFromPbJumpTablePlacedAt ∗ P :=
  rodata_statesFromPbJumpTablePlacedAt hro hP

theorem states_from_pb_keysSampled_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.KeysSampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.keysSampled s) })) :=
  Variant2PlacedBudget.states_from_pb_keysSampled_ok_ext_placed hA henc s

theorem states_from_pb_noHeaderReceived_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.NoHeaderReceived) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.noHeaderReceived s) })) :=
  Variant5PlacedBudget.states_from_pb_noHeaderReceived_ok_ext_placed hA.toPlacedBudget hdec s

theorem states_from_pb_headerReceived_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderReceived) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.headerReceived s) })) :=
  Variant6PlacedBudget.states_from_pb_headerReceived_ok_ext_placed_fromPbHooks hA hdec s

theorem states_from_pb_ekReceivedCt1Sampled_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.EkReceivedCt1Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F
          { innerState := some (.ekReceivedCt1Sampled s) })) :=
  Variant8PlacedBudget.states_from_pb_ekReceivedCt1Sampled_ok_ext_placed hA henc s

theorem states_from_pb_branch_proof_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (withAllocVmPreserved (sessionMemmoveSpec 0)))
    (pb : V1State) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (DefsBudget.statesFromPbVariantPlacedSpec M A lim F pb)) := by
  have henc : EncoderFromPbPlacedOkExt M A lim ext := encoder_from_pb_ok_of_alloc_placed hA
  have hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext :=
    decoder_from_pb_ok_of_alloc_placed hA hmemmove
  rcases pb with ⟨inner⟩
  cases inner with
  | none => exact DefsBudget.states_from_pb_none_placed_ok_ext
  | some st =>
    cases st with
    | keysUnsampled s => exact Variant1bPlacedBudget.states_from_pb_keysUnsampled_ok_ext_placed hA.toPlacedBudget s
    | keysSampled s => exact states_from_pb_keysSampled_ok_ext_placed hA henc s
    | headerSent s => exact Variant2hsPlacedBudget.states_from_pb_headerSent_ok_ext_placed hA henc hdec s
    | ct1Received s => exact Variant3PlacedBudget.states_from_pb_ct1Received_ok_ext_placed hA henc s
    | ekSentCt1Received s => exact Variant4ePlacedBudget.states_from_pb_ekSentCt1Received_ok_ext_placed hA hdec s
    | noHeaderReceived s => exact states_from_pb_noHeaderReceived_ok_ext_placed hA hdec s
    | headerReceived s => exact states_from_pb_headerReceived_ok_ext_placed hA hdec s
    | ct1Sampled s => exact Variant7PlacedBudget.states_from_pb_ct1Sampled_ok_ext_placed hA henc hdec s
    | ekReceivedCt1Sampled s => exact states_from_pb_ekReceivedCt1Sampled_ok_ext_placed hA henc s
    | ct1Acknowledged s => exact Variant9PlacedBudget.states_from_pb_ct1Acknowledged_ok_ext_placed hA hdec s
    | ct2Sampled s => exact Variant10dPlacedBudget.states_from_pb_ct2Sampled_ok_ext_placed hA henc s

theorem states_from_pb_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    DefsBudget.StatesFromPbPlacedOkExt M A lim F ext :=
  ProofPlacedBudget.states_from_pb_ok_of_forall_pb_placed (states_from_pb_branch_proof_placed hA hmemmove)

theorem states_from_pb_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    DefsBudget.StatesFromPbPlacedOkExt M A lim F ext :=
  states_from_pb_ok_ext_placed hA hmemmove

theorem states_from_pb_ok_x_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    StatesPlacedSeamsBudget.StatesFromPbPlacedOkX M A lim F ext :=
  ProofPlacedBudget.states_from_pb_okX_of_ok_ext_placed (states_from_pb_ok_ext_placed hA hmemmove)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedBudget

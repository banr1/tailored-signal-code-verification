/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtDefs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsExt
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.EncodeToVec.FinalExt
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Recv.Contracts
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Recv.Final
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKey
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ExtProof
import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed (`CliExternsOk`) `spqr::recv` Proof for Handshake `DecryptPq`

Bridges `SpqrRecvContractsExt` and `CliExternsOk P A ext` to
`spqrRecvSpecExactKeyBounded A (spqrV1Recv P.C.F P.Q.K) img` and `DecryptPq.SpqrRecvOkQF_ext`
on `tripleRatchetProgAtExt img.base (cliExternsWith ext)`.
-/

set_option maxRecDepth 200000

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (AllocContractsX spqrRecvName spqrRecvStack
  tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (MlKem TokenInit spqrRecvSpecExactKeyBounded
  spqrRecvSpecXT_imp_spqrRecvSpec spqrV1 spqrV1Recv)
open CryptoVerification.SpqrV1.Top.DecodeState (V1InnerHeapPred canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.Recv (SpqrRecvContractsExt)
open CryptoVerification.SignalSession (CliExternsOk cliExternsWith)
open CryptoVerification.SignalSession.Cli.Slots (Stage2ContractsExt)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSpqrRecv

set_option maxHeartbeats 400000

/-- Contract-backed `spqr::recv` (`spqrRecvSpecExactKeyBounded`) on `tripleRatchetProgAtExt img.base ext`
from `SpqrRecvContractsExt`. -/
theorem spqr_recv_ok_of_contracts_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img) :=
  CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecv_ok_ext_of_contracts_ext hC

/-- `DecryptPq.SpqrRecvOkQF_ext` at `S := spqrV1 F K` from `SpqrRecvContractsExt`. -/
theorem spqrRecv_okQF_of_contracts_ext
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_ext
      (·.length < 2 ^ 32) (spqrRecvStack ≤ ·) (TokenInit img)
      A (spqrV1 F K) ext img :=
  spqrRecvSpecXT_imp_spqrRecvSpec _ _ A F K img (spqr_recv_ok_of_contracts_ext hC)

private theorem hookOk_map_local {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (g : β → α) (I : State → State → Prop) (hI : ∀ s, I s (f s))
    (hh : HookOk f s₁)
    (hpre : ∀ y R s0, s0.mem ⊨ s₂.pre y s0 ∗ R → s0.mem ⊨ s₁.pre (g y) s0 ∗ R)
    (hpost : ∀ y R s0 sf, I s0 sf → s0.mem ⊨ s₂.pre y s0 ∗ R →
      sf.mem ⊨ s₁.post (g y) s0 sf ∗ R → sf.mem ⊨ s₂.post y s0 sf ∗ R)
    (hpanic : ∀ y R s0 sf, sf.mem ⊨ s₁.onPanic (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onPanic y s0 sf ∗ R)
    (hexit : ∀ y c R s0 sf,
      sf.mem ⊨ s₁.onExit (g y) c s0 sf ∗ R → sf.mem ⊨ s₂.onExit y c s0 sf ∗ R)
    (hoom : ∀ y R s0 sf, sf.mem ⊨ s₁.onOom (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onOom y s0 sf ∗ R) :
    HookOk f s₂ := by
  intro y R s0 hrun hpreY hsp
  obtain ⟨hkf, hsym, hout⟩ := hh (g y) R s0 hrun (hpre y R s0 hpreY) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp1, hp2⟩ | ⟨c, he1, he2⟩ | ⟨ho1, ho2⟩
  · exact Or.inl ⟨hret, hcc, hpost y R s0 (f s0) (hI s0) hpreY hq⟩
  · exact Or.inr (Or.inl ⟨hp1, hpanic y R s0 (f s0) hp2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he1, hexit y c R s0 (f s0) he2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho1, hoom y R s0 (f s0) ho2⟩))

/-- `SliceConcat2OkX` on `cliExternsWith ext` directly from `CliExternsOk P A ext`. -/
theorem sliceConcat2_ok_of_externsOk
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    CryptoVerification.SpqrV1.ChainProofs.SliceConcat2OkX img A (cliExternsWith ext) := by
  have hmc : HookSat (cliExternsWith ext) CryptoVerification.LibsignalTripleRatchet.memcpyName
      (CryptoVerification.SpqrV1.Alloc.session2MemcpySpecWithStack
        CryptoVerification.RustHeap.allocHookStack) :=
    CryptoVerification.SignalSession.Cli.Slots.hookSat_map
      (CryptoVerification.SignalSession.Cli.Slots.ext_memcpy hOk) fun _ hh =>
      hookOk_map_local
        (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
        (fun _ _ _ hp => by
          simpa only [CryptoVerification.SignalSession.CliExt.memcpySpec,
            libcMemcpySpec, memcpyRegionSpec,
            CryptoVerification.LibsignalTripleRatchet.withStack,
            CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
            CryptoVerification.SpqrV1.Alloc.session2MemcpySpecWithStack,
            CryptoVerification.RustHeap.allocHookStack,
            CryptoVerification.SignalSession.CliExt.memHookStack, sepConj_assoc] using hp)
        (fun _ _ _ _ _ _ hq => by
          simpa only [CryptoVerification.SignalSession.CliExt.memcpySpec,
            libcMemcpySpec, memcpyRegionSpec,
            CryptoVerification.LibsignalTripleRatchet.withStack,
            CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
            CryptoVerification.SpqrV1.Alloc.session2MemcpySpecWithStack,
            CryptoVerification.RustHeap.allocHookStack,
            CryptoVerification.SignalSession.CliExt.memHookStack, sepConj_assoc] using hq)
        (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have hRO : HookSat (cliExternsWith ext) CryptoVerification.LibsignalTripleRatchet.memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack
        CryptoVerification.RustHeap.allocHookStack) :=
    CryptoVerification.SignalSession.Cli.Slots.hookSat_map
      (CryptoVerification.SignalSession.Cli.Slots.ext_memcpyRO hOk) fun _ hh =>
      hookOk_map_local
        (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
        (fun _ _ _ hp => by
          simpa only [CryptoVerification.SignalSession.CliExt.memcpyROSpec,
            CryptoVerification.SignalSession.CliExt.withStack,
            CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack,
            CryptoVerification.RustHeap.allocHookStack,
            CryptoVerification.SignalSession.CliExt.memHookStack, sepConj_assoc] using hp)
        (fun _ _ _ _ _ _ hq => by
          simpa only [CryptoVerification.SignalSession.CliExt.memcpyROSpec,
            CryptoVerification.SignalSession.CliExt.withStack,
            CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack,
            CryptoVerification.RustHeap.allocHookStack,
            CryptoVerification.SignalSession.CliExt.memHookStack, sepConj_assoc] using hq)
        (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  exact CryptoVerification.SpqrV1.Alloc.slice_concat_2_ok_x_of_hooks
    (CryptoVerification.SignalSession.Cli.Slots.ext_shim hOk)
    (CryptoVerification.SignalSession.Cli.Slots.ext_allocHooks hOk).alloc
    hmc hRO

/-- `AuthUpdateOkExt` on `cliExternsWith ext` directly from `CliExternsOk P A ext` and `Obj.Loads`. -/
theorem authUpdate_ok_of_externsOk
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.SpqrV1.Auth.AuthUpdateOkExt img P.C.F A (cliExternsWith ext) :=
  CryptoVerification.SpqrV1.Auth.authUpdate_ok_of_contracts_ext himg
    (sliceConcat2_ok_of_externsOk hOk img)
    (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_ok_ext' img himg hOk)
    (CryptoVerification.SignalSession.Cli.Slots.ext_allocContractsX hOk img)
    (CryptoVerification.SpqrV1.Auth.allocZeroedWithStackOkX_of_hook
      (CryptoVerification.SignalSession.Cli.Slots.ext_allocZeroed hOk))

/-- `AuthNewOkExt` on `cliExternsWith ext` directly from `CliExternsOk P A ext` and `Obj.Loads`. -/
theorem authNew_ok_of_externsOk
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.SpqrV1.Auth.AuthNewOkExt img P.C.F A (cliExternsWith ext) :=
  CryptoVerification.SpqrV1.Auth.authNew_ok_of_hook_ext himg
    (authUpdate_ok_of_externsOk hOk img himg)
    (CryptoVerification.SignalSession.Cli.Slots.ext_allocContractsX hOk img)
    (CryptoVerification.SignalSession.Cli.Slots.ext_allocZeroed hOk)

/-- `InitInnerOkXExt` on `cliExternsWith ext` directly from `CliExternsOk P A ext` and `Obj.Loads`. -/
theorem initInner_ok_of_externsOk
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.SpqrV1.Top.InitInner.InitInnerOkXExt img A P.C.F (cliExternsWith ext) :=
  CryptoVerification.SpqrV1.Top.InitInner.init_inner_ok_x_ext_of_hooks4k himg
    (CryptoVerification.SignalSession.Cli.Slots.ext_allocHooks hOk)
    (CryptoVerification.SignalSession.Cli.Slots.hookSat_map
      (CryptoVerification.SignalSession.Cli.Slots.ext_shim hOk) fun _ hh =>
      hookOk_map_local
        (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
        (fun _ _ _ hp => hp) (fun _ _ _ _ _ _ hq => hq)
        (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq))
    (CryptoVerification.SignalSession.Cli.Slots.hookSat_map
      (CryptoVerification.SignalSession.Cli.Slots.ext_memcpy hOk) fun _ hh =>
      CryptoVerification.SignalSession.Cli.Slots.hookOk_sessionMemcpy_of_cliExt
        hh (Nat.le_refl _) (by decide))
    (authNew_ok_of_externsOk hOk img himg)

/-- `<spqr::v1::chunked::states::Message>::deserialize` (`MessageDeserializeOkX spqrPolyApi`)
on `cliExternsWith ext` directly from `CliExternsOk P A ext`. -/
theorem messageDeserialize_ok_of_externsOk
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    CryptoVerification.SpqrV1.Top.MessageDeserialize.MessageDeserializeOkX
      CryptoVerification.LibsignalSpqrV1.spqrPolyApi img A (cliExternsWith ext) := by
  have hFmt : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.LibsignalTripleRatchet.formatInnerName)
      (CryptoVerification.LibsignalTripleRatchet.formatInnerSpec A) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.format_inner_ok_at_ext
        img.base A (cliExternsWith ext)
        (CryptoVerification.SignalSession.Cli.Slots.ext_formatInner hOk)
        CryptoVerification.LibsignalTripleRatchet.formatInnerName 0 (Nat.add_zero _)
  have hDealloc : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.LibsignalTripleRatchet.deallocName)
      (CryptoVerification.RustHeap.rustDeallocSpec A) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.dealloc_ok_at_ext
        img.base A (cliExternsWith ext)
        (CryptoVerification.SignalSession.Cli.Slots.ext_allocHooks hOk)
        CryptoVerification.LibsignalTripleRatchet.deallocName 0 (Nat.add_zero _)
  exact CryptoVerification.SpqrV1.Top.MessageDeserialize.messageDeserialize_spqrPolyApi_ok_x
    img A (cliExternsWith ext) hFmt hDealloc

/-- `ChainNewOkExt` on `cliExternsWith ext` from `CliExternsOk`, `Obj.Loads`, and `VecDequeGrowOkX`. -/
theorem chainNew_ok_of_grow_ext
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (hGrow : CryptoVerification.SpqrV1.ChainProofs.VecDequeGrowOkX img A (cliExternsWith ext)) :
    CryptoVerification.SpqrV1.ChainProofs.ChainNewOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext) :=
  let hAx := CryptoVerification.SignalSession.Cli.Slots.ext_allocContractsX hOk img
  CryptoVerification.SpqrV1.ChainProofs.chainNew_ok_of_contracts_ext himg
    (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_ok_ext' img himg hOk)
    hGrow
    (hAx.shim CryptoVerification.LibsignalTripleRatchet.extHookStack (Nat.le_refl _) (by decide))
    hAx.alloc

/-- `ChainAddEpochOkExt` on `cliExternsWith ext` from `CliExternsOk`, `Obj.Loads`, and `VecDequeGrowOkX`. -/
theorem chainAddEpoch_ok_of_grow_ext
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (hGrow : CryptoVerification.SpqrV1.ChainProofs.VecDequeGrowOkX img A (cliExternsWith ext)) :
    CryptoVerification.SpqrV1.ChainProofs.ChainAddEpochOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext) :=
  let hAx := CryptoVerification.SignalSession.Cli.Slots.ext_allocContractsX hOk img
  CryptoVerification.SpqrV1.ChainProofs.chainAddEpoch_ok_of_contracts_ext himg
    (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_ok_ext' img himg hOk)
    hGrow
    (hAx.shim CryptoVerification.LibsignalTripleRatchet.extHookStack (Nat.le_refl _) (by decide))
    hAx.alloc hAx.dealloc

/-- `ChainRecvKeyOkExt` on `cliExternsWith ext` from `CliExternsOk`, `Obj.Loads`, and `doReserve7`. -/
theorem chainRecvKey_ok_of_doReserve_ext
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (hDoRes : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.SpqrV1.Alloc.doReserve7Name)
      ((CryptoVerification.LibsignalTripleRatchet.doReserveSpec A).inImage img)) :
    CryptoVerification.SpqrV1.ChainProofs.ChainRecvKeyOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext) :=
  CryptoVerification.SpqrV1.ChainProofs.chainRecvKey_ok_ext_ext himg
    (sliceConcat2_ok_of_externsOk hOk img)
    (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_ok_ext' img himg hOk)
    (CryptoVerification.SignalSession.Cli.Slots.ext_allocContractsX hOk img)
    hDoRes

/-- Assemble `SpqrRecvContractsExt canonicalV1InnerHeap` on `cliExternsWith ext` from `CliExternsOk P A ext`, `Obj.Loads libsignalSessionImage img`, and the remaining `spqrRecvContractsExt_of_okX` leaf contracts. -/
theorem spqrRecvContractsExt_of_leaves
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (hDecodeState : CryptoVerification.SpqrV1.Top.DecodeState.DecodeStateOkX
      canonicalV1InnerHeap img A (cliExternsWith ext))
    (hChainNew : CryptoVerification.SpqrV1.ChainProofs.ChainNewOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext))
    (hChainAddEpoch : CryptoVerification.SpqrV1.ChainProofs.ChainAddEpochOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext))
    (hChainRecvKey : CryptoVerification.SpqrV1.ChainProofs.ChainRecvKeyOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext))
    (hChainIntoPb : CryptoVerification.SpqrV1.ChainProofs.ChainIntoPbOkX
      img A (cliExternsWith ext))
    (hStatesFromPb : CryptoVerification.SpqrV1.States.FromPb.StatesFromPbOkX
      img A P.C.F (cliExternsWith ext))
    (hStatesRecv : CryptoVerification.SpqrV1.States.Recv.StatesRecvOkXExt
      img A P.C.F P.Q.K (cliExternsWith ext))
    (hStatesIntoPb : CryptoVerification.SpqrV1.States.IntoPb.StatesIntoPbOkX
      img A P.C.F (cliExternsWith ext))
    (hInitInner : CryptoVerification.SpqrV1.Top.InitInner.InitInnerOkXExt
      img A P.C.F (cliExternsWith ext) := initInner_ok_of_externsOk hOk img himg)
    (hMsgDeser : CryptoVerification.SpqrV1.Top.MessageDeserialize.MessageDeserializeOkX
      CryptoVerification.LibsignalSpqrV1.spqrPolyApi img A (cliExternsWith ext) :=
      messageDeserialize_ok_of_externsOk hOk img) :
    SpqrRecvContractsExt canonicalV1InnerHeap img A P.C.F P.Q.K
      (cliExternsWith ext) := by
  let hAx := CryptoVerification.SignalSession.Cli.Slots.ext_allocContractsX hOk img
  let hAllocHooks := CryptoVerification.SignalSession.Cli.Slots.ext_allocHooks hOk
  have hDealloc : CryptoVerification.SpqrV1.Drop.DeallocOkExt img.base A (cliExternsWith ext) := by
    simpa only [CryptoVerification.SpqrV1.Drop.DeallocOkExt,
      CryptoVerification.SpqrV1.Drop.dropProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.dealloc_ok_at_ext img.base A (cliExternsWith ext)
        hAllocHooks CryptoVerification.LibsignalTripleRatchet.deallocName 0 (Nat.add_zero _)
  exact CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContractsExt_of_okX
    himg hAx hDealloc
    hDecodeState hInitInner hChainNew hChainAddEpoch hChainRecvKey hChainIntoPb
    hMsgDeser hStatesFromPb hStatesRecv hStatesIntoPb
    (CryptoVerification.Cli.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_okX_ax hAx himg)

/-- Contract-backed `spqr::recv` (`spqrRecvSpecExactKeyBounded`) on `cliExternsWith ext` from `CliExternsOk`
and the remaining leaf contracts. -/
theorem spqr_recv_ok_of_leaves_ext
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (hDecodeState : CryptoVerification.SpqrV1.Top.DecodeState.DecodeStateOkX
      canonicalV1InnerHeap img A (cliExternsWith ext))
    (hChainNew : CryptoVerification.SpqrV1.ChainProofs.ChainNewOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext))
    (hChainAddEpoch : CryptoVerification.SpqrV1.ChainProofs.ChainAddEpochOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext))
    (hChainRecvKey : CryptoVerification.SpqrV1.ChainProofs.ChainRecvKeyOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext))
    (hChainIntoPb : CryptoVerification.SpqrV1.ChainProofs.ChainIntoPbOkX
      img A (cliExternsWith ext))
    (hStatesFromPb : CryptoVerification.SpqrV1.States.FromPb.StatesFromPbOkX
      img A P.C.F (cliExternsWith ext))
    (hStatesRecv : CryptoVerification.SpqrV1.States.Recv.StatesRecvOkXExt
      img A P.C.F P.Q.K (cliExternsWith ext))
    (hStatesIntoPb : CryptoVerification.SpqrV1.States.IntoPb.StatesIntoPbOkX
      img A P.C.F (cliExternsWith ext))
    (hInitInner : CryptoVerification.SpqrV1.Top.InitInner.InitInnerOkXExt
      img A P.C.F (cliExternsWith ext) := initInner_ok_of_externsOk hOk img himg)
    (hMsgDeser : CryptoVerification.SpqrV1.Top.MessageDeserialize.MessageDeserializeOkX
      CryptoVerification.LibsignalSpqrV1.spqrPolyApi img A (cliExternsWith ext) :=
      messageDeserialize_ok_of_externsOk hOk img) :
    subroutine_ok
      (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv P.C.F P.Q.K) img) :=
  spqr_recv_ok_of_contracts_ext
    (spqrRecvContractsExt_of_leaves hOk img himg
      hDecodeState hChainNew hChainAddEpoch hChainRecvKey hChainIntoPb
      hStatesFromPb hStatesRecv hStatesIntoPb hInitInner hMsgDeser)

/-- `DecryptPq.SpqrRecvOkQF_ext` at `S := spqrV1 P.C.F P.Q.K` on `cliExternsWith ext`
from `CliExternsOk P A ext` and the remaining leaf contracts. -/
theorem spqrRecv_okQF_of_leaves_ext
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (hDecodeState : CryptoVerification.SpqrV1.Top.DecodeState.DecodeStateOkX
      canonicalV1InnerHeap img A (cliExternsWith ext))
    (hChainNew : CryptoVerification.SpqrV1.ChainProofs.ChainNewOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext))
    (hChainAddEpoch : CryptoVerification.SpqrV1.ChainProofs.ChainAddEpochOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext))
    (hChainRecvKey : CryptoVerification.SpqrV1.ChainProofs.ChainRecvKeyOkExt
      img (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith P.C.F) A (cliExternsWith ext))
    (hChainIntoPb : CryptoVerification.SpqrV1.ChainProofs.ChainIntoPbOkX
      img A (cliExternsWith ext))
    (hStatesFromPb : CryptoVerification.SpqrV1.States.FromPb.StatesFromPbOkX
      img A P.C.F (cliExternsWith ext))
    (hStatesRecv : CryptoVerification.SpqrV1.States.Recv.StatesRecvOkXExt
      img A P.C.F P.Q.K (cliExternsWith ext))
    (hStatesIntoPb : CryptoVerification.SpqrV1.States.IntoPb.StatesIntoPbOkX
      img A P.C.F (cliExternsWith ext))
    (hInitInner : CryptoVerification.SpqrV1.Top.InitInner.InitInnerOkXExt
      img A P.C.F (cliExternsWith ext) := initInner_ok_of_externsOk hOk img himg)
    (hMsgDeser : CryptoVerification.SpqrV1.Top.MessageDeserialize.MessageDeserializeOkX
      CryptoVerification.LibsignalSpqrV1.spqrPolyApi img A (cliExternsWith ext) :=
      messageDeserialize_ok_of_externsOk hOk img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_ext
      (·.length < 2 ^ 32) (spqrRecvStack ≤ ·) (TokenInit img)
      A (spqrV1 P.C.F P.Q.K) (cliExternsWith ext) img :=
  spqrRecv_okQF_of_contracts_ext
    (spqrRecvContractsExt_of_leaves hOk img himg
      hDecodeState hChainNew hChainAddEpoch hChainRecvKey hChainIntoPb
      hStatesFromPb hStatesRecv hStatesIntoPb hInitInner hMsgDeser)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSpqrRecv

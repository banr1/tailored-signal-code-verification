/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize

/-!
# Relocatable Stage P2 Shared Definitions and Callee Bundles

Defines placed Stage P2 closure hooks (`StageP2ClosureHooksPlaced`), SPQR V1
`InitializeBobV1*Placed` contracts, and `StageP2PureCalleesPlaced{,4K}` on Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateOkX initialStateValue)
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

theorem p2_call_frame_oom_prefix_placed {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Steps prog s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ |
    ⟨_hoom_st, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hsteps R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, p2_allowPanic_oom_of_trace_prefix htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem p2_call_frame_cro_oom_prefix_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      Steps prog s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  refine p2_call_frame_oom_prefix_placed htr hcall hpc hrun hsp hlr hspec hφ hP hpan_eq hexit_false
    (fun sf hpcm hrunm hspm hsp_alm hcsm hsteps =>
      hnext sf hpcm hrunm hspm hsp_alm hcsm (hCode.of_keepsFrozen hsteps.keepsFrozen) hsteps)
    hoom_false

theorem p2_shim_at_closure_of_hookSat_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hShim : HookSat ext Keys.lsRustNoAllocShimSym noAllocShimSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ Keys.lsRustNoAllocShimSym) noAllocShimSpec := by
  dsimp only [stageP1ProgPlaced, lsProg_518]
  exact ls_hook_ok_ultra_of_mem hShim (by decide)

theorem p2_alloc_at_closure_of_hookSat_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAlloc : HookSat ext Keys.lsRustAllocSym (rustAllocSpec A)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ Keys.lsRustAllocSym) (rustAllocSpec A) := by
  dsimp only [stageP1ProgPlaced, lsProg_518]
  exact ls_hook_ok_ultra_of_mem hAlloc (by decide)

theorem p2_dealloc_at_closure_of_hookSat_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustDeallocSym) (rustDeallocSpec A) := by
  dsimp only [stageP1ProgPlaced, lsProg_518]
  exact ls_hook_ok_ultra_of_mem hDealloc (by decide)

theorem p2_memcpy_at_closure_4k_of_hookSat_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext lsMemcpySym p2Memcpy4KSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsρ lsMemcpySym) p2Memcpy4KSpec := by
  dsimp only [stageP1ProgPlaced, lsProg_518]
  exact ls_hook_ok_ultra_of_mem hMemcpy (by decide)

theorem p2_panic_at_handle_error_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hPan : ext lsHandleErrorSym = some Rust.panicked) :
    (stageP1ProgPlaced ext).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked := by
  dsimp only [stageP1ProgPlaced, lsProg_518]
  exact (ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans hPan

/-- Unified closure-level extern callee bundle for Stage P2 basic blocks on `stageP1ProgPlaced ext`
(`shim` at 0 B, `alloc`/`dealloc`/`memcpy` at `allocHookStack = 4096` B, plus `handle_error` panic). -/
structure StageP2ClosureHooksPlaced [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  shim : subroutine_ok (stageP1ProgPlaced ext) (lsρ Keys.lsRustNoAllocShimSym) noAllocShimSpec
  alloc : subroutine_ok (stageP1ProgPlaced ext) (lsρ Keys.lsRustAllocSym) (rustAllocSpec A)
  dealloc : subroutine_ok (stageP1ProgPlaced ext) (lsρ lsRustDeallocSym) (rustDeallocSpec A)
  memcpy4K : subroutine_ok (stageP1ProgPlaced ext) (lsρ lsMemcpySym) p2Memcpy4KSpec
  handleError : (stageP1ProgPlaced ext).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked

theorem StageP2ClosureHooksPlaced.of_hooks [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (hAlloc : HookSat ext Keys.lsRustAllocSym (rustAllocSpec A))
    (hDealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A))
    (hMemcpy : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hPan : ext lsHandleErrorSym = some Rust.panicked) :
    StageP2ClosureHooksPlaced A ext :=
  ⟨p2_shim_at_closure_of_hookSat_placed hShim,
   p2_alloc_at_closure_of_hookSat_placed hAlloc,
   p2_dealloc_at_closure_of_hookSat_placed hDealloc,
   p2_memcpy_at_closure_4k_of_hookSat_placed hMemcpy,
   p2_panic_at_handle_error_placed hPan⟩

/-! ## Placed Pure Callee Contracts (`InitializeBobV1OkPlaced` & `StageP2PureCalleesPlaced`) -/

/-- Memory invariant preserved across `Memory.KeepsFrozen` steps and implying
`StoreKit.LibsignalCodeRoLoaded lsmpl`. Instantiates to both `StoreKit.LibsignalCodeRoLoaded lsmpl`
and `LibsignalFrozen lsmpl`. -/
structure StageP2MemInv [LibsignalPlacement] (Φ : Memory → Prop) : Prop where
  of_keepsFrozen : ∀ {m m' : Memory}, Φ m → m.KeepsFrozen m' → Φ m'
  toCodeRo : ∀ {m : Memory}, Φ m → StoreKit.LibsignalCodeRoLoaded lsmpl m

theorem StageP2MemInv.codeRoLoaded [LibsignalPlacement] :
    StageP2MemInv (StoreKit.LibsignalCodeRoLoaded lsmpl) where
  of_keepsFrozen h hk := h.of_keepsFrozen hk
  toCodeRo h := h

theorem StageP2MemInv.frozen [LibsignalPlacement] :
    StageP2MemInv (LibsignalFrozen lsmpl) where
  of_keepsFrozen h hk := libsignalFrozen_of_keepsFrozen h hk
  toCodeRo h := ⟨LibsignalCodeLoaded.of_codeLoaded h.2, h.1⟩

/-- Stack- and memory-invariant-parameterized SPQR V1 `initialize_bob_session` success contract
under `[LibsignalPlacement]` on `stageP1ProgPlaced ext` (`lsProg_518 ext`). -/
def InitializeBobV1MemInvOkAtPlaced [LibsignalPlacement] (Φ : Memory → Prop)
    (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) (bobV1Stk : Nat) : Prop :=
  ∀ (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp),
    Φ s0.mem → s0.status = ExecStatus.Running →
    s0.pc = lsmpl.base 75 →
    s0.spAligned = true → s0.sp - 576#64 ≠ 0#64 →
    s0.readReg64 (.gpr 0#5) = argPtr → s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr →
    s0.readReg64 (.gpr 8#5) = outPtr →
    inp.trustedPeer = true → inp.replayOk = true →
    inp.hdr.opkId?.isSome = inp.opkBSk?.isSome →
    WellSizedAcceptKeysInput inp → ikBPk.length = 32 → spkBPk.length = 32 →
    Model.acceptKeys P inp = some drKey →
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp bobV1Stk ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ p2BobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr
              (BitVec.ofNat 64 (initialStateValue F (p2BobSpqrParams drKey.pqrKey)).length)
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            p2BobSpqrVecBuf A spqrCap spqrBufPtr
              (initialStateValue F (p2BobSpqrParams drKey.pqrKey)) ∗
            bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
              inp ikBPk spkBPk 0#8 ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗
            A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗
            A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp bobV1Stk ∗ A.pool ∗ Frame) ∧
          sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (BobPanicOom s0)

def InitializeBobV1MemInvOkPlaced [LibsignalPlacement] (Φ : Memory → Prop)
    (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1MemInvOkAtPlaced Φ P A F ext (stageP2bStack + 0x700)

def InitializeBobV1MemInvOkPlaced4K [LibsignalPlacement] (Φ : Memory → Prop)
    (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1MemInvOkAtPlaced Φ P A F ext (768 + Initiator.pqxdhEntryStackExt)

theorem InitializeBobV1MemInvOkPlaced.to_4K [LibsignalPlacement] {Φ : Memory → Prop}
    {P : Primitives} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h : InitializeBobV1MemInvOkPlaced Φ P A F ext) :
    InitializeBobV1MemInvOkPlaced4K Φ P A F ext := by
  intro s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + Initiator.pqxdhEntryStackExt))
      ((768 + Initiator.pqxdhEntryStackExt) - (stageP2bStack + 0x700))
  have hsplit := p2_stackAt_split_of_le s0.sp (768 + Initiator.pqxdhEntryStackExt)
    (stageP2bStack + 0x700) (by decide) (by decide)
  have hcall := h s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey (F_stk ∗ Frame) hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc
  intro R hm hL
  have hm' : s0.mem ⊨
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
        memRegion outPtr 344 ∗ lsLogFilterAddr ↦₆₄ 0#64 ∗
        stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool ∗ (F_stk ∗ Frame)) ∗ R := by
    refine Satisfies.of_eq hm ?_; dsimp only [F_stk]; rw [hsplit]; ac_rfl
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr,
    baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩ | hpan⟩ := hcall R hm' hL
  · refine ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr,
      baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2, hn1, hn2, hn3, hn4, hn5, hn6, hn7,
      Entails.trans hPf (Entails.of_eq ?_), hst'⟩⟩
    dsimp only [F_stk]; rw [hsplit]; ac_rfl
  · exact ⟨sf, hst, Or.inr hpan⟩

/-- Stack-parameterized SPQR V1 `initialize_bob_session` success contract under `[LibsignalPlacement]`
on `stageP1ProgPlaced ext` (`lsProg_518 ext`). -/
def InitializeBobV1OkAtPlaced [LibsignalPlacement] (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) (bobV1Stk : Nat) : Prop :=
  InitializeBobV1MemInvOkAtPlaced (StoreKit.LibsignalCodeRoLoaded lsmpl) P A F ext bobV1Stk

def InitializeBobV1OkPlaced [LibsignalPlacement] (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1OkAtPlaced P A F ext (stageP2bStack + 0x700)

def InitializeBobV1OkPlaced4K [LibsignalPlacement] (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1OkAtPlaced P A F ext (768 + Initiator.pqxdhEntryStackExt)

theorem InitializeBobV1OkPlaced.to_4K [LibsignalPlacement] {P : Primitives} {A : RustAlloc}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h : InitializeBobV1OkPlaced P A F ext) :
    InitializeBobV1OkPlaced4K P A F ext :=
  InitializeBobV1MemInvOkPlaced.to_4K h

/-- `LibsignalFrozen`-guarded SPQR V1 `initialize_bob_session` success contracts on `stageP1ProgPlaced ext`. -/
def InitializeBobV1FrozenOkAtPlaced [LibsignalPlacement] (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) (bobV1Stk : Nat) : Prop :=
  InitializeBobV1MemInvOkAtPlaced (LibsignalFrozen lsmpl) P A F ext bobV1Stk

def InitializeBobV1FrozenOkPlaced [LibsignalPlacement] (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1FrozenOkAtPlaced P A F ext (stageP2bStack + 0x700)

def InitializeBobV1FrozenOkPlaced4K [LibsignalPlacement] (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1FrozenOkAtPlaced P A F ext (768 + Initiator.pqxdhEntryStackExt)

theorem InitializeBobV1FrozenOkPlaced.to_4K [LibsignalPlacement] {P : Primitives} {A : RustAlloc}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h : InitializeBobV1FrozenOkPlaced P A F ext) :
    InitializeBobV1FrozenOkPlaced4K P A F ext :=
  InitializeBobV1MemInvOkPlaced.to_4K h

/-- 4K/`Ext` variant of `initializeBobSessionErrInnerPlacedSpec` at `768 + Initiator.pqxdhEntryStackExt`. -/
def initializeBobSessionErr4KInnerPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec InitBobCallGhost where
  pre := fun (g : InitBobCallGhost) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧ s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧ g.inp.trustedPeer = true ∧ g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧ WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧ g.spkBPk.length = 32 ∧ Model.acceptKeys P g.inp = none⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + Initiator.pqxdhEntryStackExt) ∗ A.pool
  post := fun (g : InitBobCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    (initBobErrAt g.outPtr ∗ anyHeap) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s0.sp (768 + Initiator.pqxdhEntryStackExt) ∗ A.pool
  onPanic := rustPanicOnOomPlaced

def initializeBobSessionErr4KPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec InitBobCallGhost :=
  StoreKit.withLsCodeRoLoaded lsmpl (initializeBobSessionErr4KInnerPlacedSpec P A)

abbrev initializeBobSessionErrExtPlacedSpec [LibsignalPlacement] :=
  initializeBobSessionErr4KPlacedSpec

theorem initializeBobSessionErrPlacedSpec_to_4K [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {P : Primitives} {A : RustAlloc}
    (h : subroutine_ok prog entry (initializeBobSessionErrPlacedSpec P A)) :
    subroutine_ok prog entry (initializeBobSessionErr4KPlacedSpec P A) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [initializeBobSessionErrPlacedSpec, initializeBobSessionErrInnerPlacedSpec,
        StoreKit.withLsCodeRoLoaded] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [initializeBobSessionErrPlacedSpec, initializeBobSessionErrInnerPlacedSpec,
        StoreKit.withLsCodeRoLoaded] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + Initiator.pqxdhEntryStackExt))
      ((768 + Initiator.pqxdhEntryStackExt) - (768 + pqxdhEntryStack))
  dsimp only [initializeBobSessionErr4KPlacedSpec, initializeBobSessionErr4KInnerPlacedSpec,
    StoreKit.withLsCodeRoLoaded] at hpre
  rw [p2_stackAt_split_of_le s0.sp (768 + Initiator.pqxdhEntryStackExt)
    (768 + pqxdhEntryStack) (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  have hnone : Model.acceptKeys P g.inp = none := hpure.2.2.2.2.2.2.2.2.2
  refine ⟨g, F_stk ∗ R, ?_, fun sf hpost => ?_, fun sf hpan => ?_⟩
  · dsimp only [initializeBobSessionErrPlacedSpec, initializeBobSessionErrInnerPlacedSpec,
      StoreKit.withLsCodeRoLoaded, F_stk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrPlacedSpec, initializeBobSessionErrInnerPlacedSpec,
      initializeBobSessionInnerPlacedSpec, initializeBobSessionErr4KPlacedSpec,
      initializeBobSessionErr4KInnerPlacedSpec, StoreKit.withLsCodeRoLoaded, F_stk] at hpost ⊢
    rw [hnone] at hpost
    rw [p2_stackAt_split_of_le s0.sp (768 + Initiator.pqxdhEntryStackExt)
      (768 + pqxdhEntryStack) (by decide) (by decide)]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, Satisfies.of_eq hpost.2 (by ac_rfl)⟩
  · dsimp only [initializeBobSessionErrPlacedSpec, initializeBobSessionErrInnerPlacedSpec,
      initializeBobSessionErr4KPlacedSpec, initializeBobSessionErr4KInnerPlacedSpec,
      StoreKit.withLsCodeRoLoaded, rustPanicOnOomPlaced, F_stk] at hpan ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
    rcases hpan with ⟨hp, hmem_pan⟩
    exact ⟨hp, Arm64.Satisfies.mono (Entails.trans
      (Entails.of_eq (show anyHeap ∗ (memRegion _ _ ∗ R) =
        (anyHeap ∗ memRegion _ _) ∗ R by ac_rfl))
      (sepConj_mono_left (entails_anyHeap _))) hmem_pan⟩

/-! ## Placed `<PublicKey>::serialize` Projections and `StageP2PureCalleesPlaced` -/

/-- `<PublicKey>::serialize` (`lsmpl.base 205`) meets `publicKeySerializeSpec A` on
`stageP1ProgPlaced ext` under `HookSat` for `noAllocShim`, `rustAlloc`, and `handle_error` panic. -/
theorem p2_publicKeySerialize_of_hooks_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (hAlloc : HookSat ext Keys.lsRustAllocSym (rustAllocSpec A))
    (hPan : ext lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)) :=
  ls_subroutine_ok_of_block (i := 518) (j := 205)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (public_key_serialize_placed_ok hShim hAlloc hPan))
    (by decide)

/-- Placed bundle of internal libsignal subroutine contracts invoked along Stage P2
on `stageP1ProgPlaced ext` (`lsProg_518 ext`). -/
structure StageP2PureCalleesPlaced [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop where
  publicKeySerialize :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A))
  promoteMatchingSessionEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 50)
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec)
  curveKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 112)
      (withLsCodeLoaded lsmpl curveKeyPairSerdeOkSpec)
  kemKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec A))
  preKeyRecordKeyPair :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 67)
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairOkSpec)
  dropSpe2 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (Getters.withLsRoLoaded lsmpl (Getters.dropSpeSpec A)))
  isSameAccount :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (WireEntries.isSameAccountDistinctSpec A uuidTryParse))
  initializeBobV1 : InitializeBobV1OkPlaced P A F ext
  initializeBobErr :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 75)
      (initializeBobSessionErrPlacedSpec P A)
  promoteStateEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmptySpec)
  dropProcessPrekeyImplState1 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 509)
      (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec)
  dropSessionStructure3 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A))

/-- Non-Bob `withLsCodeLoaded` 4K/`Ext` pure callee contracts of Stage P2 (Substages 1–4, 5.8, and 6),
provable under `[LibsignalPlacement]` without any Block `79` (`Pqxdh::accept`) seam. -/
structure StageP2BaseCalleesPlaced4K [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) : Prop where
  publicKeySerialize :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A))
  promoteMatchingSessionEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 50)
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec)
  curveKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 112)
      (withLsCodeLoaded lsmpl curveKeyPairSerdeOkSpec)
  kemKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec A))
  preKeyRecordKeyPair :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 67)
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairOkSpec)
  dropSpe2 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (Getters.withLsRoLoaded lsmpl (Getters.dropSpeSpec A)))
  isSameAccount :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 17)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A uuidTryParse))
  promoteStateEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec)
  dropProcessPrekeyImplState1 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 509)
      (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec)
  dropSessionStructure3 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A))

structure StageP2PureCalleesPlaced4K [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop extends StageP2BaseCalleesPlaced4K A ext where
  initializeBobV1 : InitializeBobV1OkPlaced4K P A F ext
  initializeBobErr :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 75)
      (initializeBobSessionErr4KPlacedSpec P A)

abbrev StageP2PureCalleesExtPlaced [LibsignalPlacement] := StageP2PureCalleesPlaced4K

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

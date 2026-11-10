/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Common Epilogue, Checkpoint States & Seam Bridges for `ChainLookup`

Provides `RustCliAllocBudget M` deallocation call-site helpers, the `VmPreserved`-strengthened
block `130` return epilogue, budget-threaded checkpoint states with bridges to `Decrypt.DefsBudget`,
and epilogue-to-outcome combinators for `try_decrypt_with_state`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
  (ChainKey Crypto SessionState SignalProtocolError TripleRatchet)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SessionGhost UuidParser decryptDraws protocolAddressAt sessionStateAt signalMessageAt tapeAfter
   uuidTryParse vecResultAt)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded SpqrModel TrGhost TryDecryptGhost decResultFnAt extHookStack
   logOff rootStack tripleRatchetProgAtExt tryDecryptFnSpec tryDecryptName tryDecryptSpec
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (tryDecryptCommonHeap tryDecryptMidMetaPlaced tryDecryptPlacedImg
   tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (blkPC_131 blkPl_131 decRel_afterTrFrom retEpiloguePC_placed sepWP_to_reaches_pc
   tryDecryptDummyImg tryDecryptEntry_placed tryDecryptMidMeta_placed tryDecryptStack_recombine)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpecBase)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliDeallocBudgetExternSpecWithStackBase)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (AllocContractsBudget AllocContractsXBudget)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
  (ConsumeMsgKeyStatePlaced DhStepStatePlaced ErrTailStatePlaced ErrTailStateXPlaced
   FindChainStatePlaced LoadRatchetStatePlaced
   tryDecryptFnOnPanic tryDecryptFnRawSpecPlaced tryDecryptFnSpecPlaced
   tryDecryptOnPanic tryDecryptRawSpecPlaced tryDecryptSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget
  (sepWP_blk130_vm)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `ChainLookupFacts`: Budget Dealloc Call-Site Helpers -/

namespace ChainLookupFacts

theorem tryDecrypt_dealloc_ok {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryDecryptName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      (rustCliDeallocBudgetSpecBase M A lim) :=
  hA.dealloc_ok_at tryDecryptName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    (by fnoff_eq)

theorem tryDecrypt_dealloc_ok_x {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      ((rustCliDeallocBudgetExternSpecWithStackBase M A lim extHookStack).inImage img) :=
  hA.dealloc_ok_at tryDecryptName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    (by fnoff_eq)

end ChainLookupFacts

/-! ## 2. Metadata Bridges & `VmPreserved`-Strengthened Epilogue (Block `130`) -/

theorem tryDecryptDummyImg_eq_placedImg [LibsignalPlacement] :
    tryDecryptDummyImg = tryDecryptPlacedImg :=
  rfl

theorem tryDecryptMidMeta_placed_to_placed [LibsignalPlacement] {s0 s : State}
    (h : tryDecryptMidMeta_placed s0 s) (hro : LibsignalRoLoaded lsmpl s.mem) :
    tryDecryptMidMetaPlaced s0 s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    ⟨h.2.2.2.2.2.2.1, hro⟩, h.2.2.2.2.2.2.2⟩

theorem tryDecryptMidMetaPlaced_to_placed [LibsignalPlacement] {s0 s : State}
    (h : tryDecryptMidMetaPlaced s0 s) :
    tryDecryptMidMeta_placed s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1.1, h.2.2.2.2.2.2.2⟩, h.2.2.2.2.2.2.1.2⟩

theorem tryDecrypt_epilogue_394_wp_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (s0 s : State) (hpc : s.pc = retEpiloguePC_placed) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1504#64) (hs0_align : s0.spAligned = true)
    (_hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
        memRegion (s0.sp - 1504#64) 1408 ∗ tryDecryptSavedRegs s0.sp s0)
      (fun sf P_f => sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ VmPreserved s sf ∧
        CalleeSavedPreserved s0 sf ∧ (P_f ⊢ stackAt s0.sp rootStack)) := by
  unfold tryDecryptSavedRegs
  dsimp only [retEpiloguePC_placed, tryDecryptEntry_placed] at hpc
  apply sepWP_blk130_vm (mid := s0.readReg64 .x30)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], hvm, ?_, ?_⟩
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, *]
  · exact tryDecryptStack_recombine s0.sp s0

/-! ## 3. Budget-Threaded Block `130` Checkpoint States & Bridges -/

def ErrTailState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ErrTailState_placed
    (A.atState lim st s) ctl x trG tr st1 e draws R s0 s

def ErrTailStateX_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ErrTailStateX_placed
    (A.atState lim st s) ctl x trG tr st1 e draws R s0 s

theorem ErrTailState_placed.toX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailState_placed A lim st ctl x trG tr st1 e draws R s0 s) :
    ErrTailStateX_placed A lim st ctl x trG tr st1 e draws R s0 s :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ErrTailState_placed.toX h

def LoadRatchetState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.LoadRatchetState_placed
    (A.atState lim st s) ctl x R s0 s

def FindChainState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.FindChainState_placed
    (A.atState lim st s) ctl x trG tr st1 R s0 s

def DhStepState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.DhStepState_placed
    (A.atState lim st s) ctl x trG tr st1 R s0 s

def ConsumeMsgKeyState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ConsumeMsgKeyState_placed
    (A.atState lim st s) ctl x trG tr st1 ck draws R s0 s

theorem LoadRatchetStatePlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : LoadRatchetState_placed A lim st ctl x R s0 s) (hro : LibsignalRoLoaded lsmpl s.mem) :
    LoadRatchetStatePlaced (blkPl_131).base A lim st ctl x R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem LoadRatchetStatePlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : LoadRatchetStatePlaced (blkPl_131).base A lim st ctl x R s0 s) :
    LoadRatchetState_placed A lim st ctl x R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

theorem FindChainStatePlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : FindChainState_placed A lim st ctl x trG tr st1 R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    FindChainStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem FindChainStatePlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : FindChainStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 R s0 s) :
    FindChainState_placed A lim st ctl x trG tr st1 R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

theorem DhStepStatePlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : DhStepState_placed A lim st ctl x trG tr st1 R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    DhStepStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem DhStepStatePlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : DhStepStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 R s0 s) :
    DhStepState_placed A lim st ctl x trG tr st1 R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

theorem ConsumeMsgKeyStatePlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ConsumeMsgKeyState_placed A lim st ctl x trG tr st1 ck draws R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    ConsumeMsgKeyStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 ck draws R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem ConsumeMsgKeyStatePlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ConsumeMsgKeyStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 ck draws R s0 s) :
    ConsumeMsgKeyState_placed A lim st ctl x trG tr st1 ck draws R s0 s ∧
      LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

theorem ErrTailStatePlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailState_placed A lim st ctl x trG tr st1 e draws R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    ErrTailStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 e draws R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem ErrTailStatePlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 e draws R s0 s) :
    ErrTailState_placed A lim st ctl x trG tr st1 e draws R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

theorem ErrTailStateXPlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailStateX_placed A lim st ctl x trG tr st1 e draws R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    ErrTailStateXPlaced (blkPl_131).base A lim st ctl x trG tr st1 e draws R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem ErrTailStateXPlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailStateXPlaced (blkPl_131).base A lim st ctl x trG tr st1 e draws R s0 s) :
    ErrTailStateX_placed A lim st ctl x trG tr st1 e draws R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

/-! ## 4. Whole-Function Contracts & Epilogue-to-Outcome Combinators -/

abbrev tryDecryptRawSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  tryDecryptRawSpecPlaced C A lim ctl uuidParse S tdEnv

def tryDecryptPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeLoaded lsmpl (tryDecryptRawSpec C A lim ctl uuidParse S tdEnv)

abbrev tryDecryptFnRawSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  tryDecryptFnRawSpecPlaced C decFn A lim ctl uuidParse S tdEnv

def tryDecryptFnPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeLoaded lsmpl (tryDecryptFnRawSpec C decFn A lim ctl uuidParse S tdEnv)

theorem reaches_epilogue_to_outcome_seam_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {remEnv : List AllocEvent → Prop}
    (x : TryDecryptGhost) (st_init st : M.σ) (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G')
    (hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st remEnv)
    (hreach : reaches_pc ((blkPC_131).rebase (blkPl_131).base H) retEpiloguePC_placed s
      (fun s1 => ∃ evs_exit : List AllocEvent, remEnv evs_exit ∧
        tryDecryptMidMeta_placed s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt (A.atState lim (M.stepEvents evs_exit st) s1)
            x.ss G' (x.model C S uuidTryParse).2 ∗
          vecResultAt (A.atState lim (M.stepEvents evs_exit st) s1)
            x.ret (x.model C S uuidTryParse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          tryDecryptCommonHeap (A.atState lim (M.stepEvents evs_exit st) s1)
            ctl tryDecryptDummyImg x (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 ∗ R))) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv) (x, st_init) R s0 s := by
  have hcomb : reaches_pc ((blkPC_131).rebase (blkPl_131).base H) (s0.readReg64 .x30) s
      (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.mem ⊨ (tryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv).post
          (x, st_init) s0 sf ∗ R)) := by
    refine reaches_pc_seq hreach ?_
    rintro s1 hpc1 _ ⟨evs_exit, hexit,
      ⟨hrun1, hsp1, hs0_align, hsp_align1, _, htrace1, _, hvregs1⟩, hm1⟩
    obtain ⟨evs_total, hst_eq, htd_tot⟩ := hsb.finish hexit
    rw [hst_eq] at hm1
    set A1 : RustAlloc := A.atState lim (M.stepEvents evs_total st_init) s1
    unfold tryDecryptCommonHeap at hm1
    have hm1_re : s1.mem ⊨
        (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
          memRegion (s0.sp - 1504#64) 1408 ∗ tryDecryptSavedRegs s0.sp s0) ∗
        (sessionStateAt A1 x.ss G' (x.model C S uuidTryParse).2 ∗
         vecResultAt A1 x.ret (x.model C S uuidTryParse).1 ∗ protocolAddressAt A1 x.rem x.remA ∗
         protocolAddressAt A1 x.loc x.locA ∗ signalMessageAt A1 x.msgG x.msgA x.msg ∗
         tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff tryDecryptDummyImg ∗ A1.pool ∗ R) := by convert hm1 using 1; sep_ac_rfl
    refine reaches_pc_mono (sepWP_to_reaches_pc
      (tryDecrypt_epilogue_394_wp_placed s0 s1 hpc1 hrun1 hsp1 hs0_align hsp_align1 htrace1 hvregs1)
      hm1_re) ?_
    intro sf _ _ ⟨P_f, hm_sf, hsp_sf, htrace_sf, hvm_sf, hcc_sf, hP_f⟩
    refine ⟨hsp_sf, hcc_sf, ?_⟩
    have hm2 := Satisfies.mono (sepConj_mono_left hP_f) hm_sf
    have hA_eq : A.atState lim (M.stepEvents evs_total st_init) sf = A1 :=
      RustCliAllocBudget.atState_eq_of_vmPreserved A lim (M.stepEvents evs_total st_init) hvm_sf
    dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptRawSpecPlaced,
      CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptRawSpecPlaced]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs_total, ?_⟩
    rw [hA_eq, ← tryDecryptDummyImg_eq_placedImg]
    simp only [tryDecryptSpec, Spec.inImage]
    have hm3 : sf.mem ⊨
        sessionStateAt A1 x.ss G' (x.model C S uuidTryParse).2 ∗
        (vecResultAt A1 x.ret (x.model C S uuidTryParse).1 ∗ protocolAddressAt A1 x.rem x.remA ∗
         protocolAddressAt A1 x.loc x.locA ∗ signalMessageAt A1 x.msgG x.msgA x.msg ∗
         tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff tryDecryptDummyImg ∗ stackAt s0.sp rootStack ∗ A1.pool ∗ R) := by
      convert hm2 using 1; sep_ac_rfl
    have hent :
        sessionStateAt A1 x.ss G' (x.model C S uuidTryParse).2 ⊢
          ⌜tdEnv (tryDecryptEnvArgs x) evs_total⌝ ∗
          ⌜(x.model C S uuidTryParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (∃∗ G'' : SessionGhost,
            ⌜x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G''⌝ ∗
            sessionStateAt A1 x.ss G'' (x.model C S uuidTryParse).2) :=
      Entails.pure_right htd_tot
        (Entails.pure_right ⟨hnpan, htrace_sf⟩
          (Entails.trans (Entails.pure_right hG' (Entails.refl _))
            (Entails.sepExists_intro
              (P := fun G'' => ⌜x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G''⌝ ∗
                sessionStateAt A1 x.ss G'' (x.model C S uuidTryParse).2) G')))
    have hm4 := Satisfies.mono (sepConj_mono_left hent) hm3
    convert hm4 using 1; sep_ac_rfl
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, hsp_sf, hcc_sf, hpost_sf⟩ | ⟨_, hfalse⟩⟩ := hcomb hL
  · exact reaches_outcome_steps hsteps
      (reaches_outcome.of_outcome (Or.inl ⟨⟨hpc_sf, hsp_sf, hrun_sf⟩, ⟨hsp_sf, hcc_sf⟩, hpost_sf⟩))
  · exact hfalse.elim

theorem reaches_epilogue_to_outcome_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (x : TryDecryptGhost) (st_init : M.σ) (evs_total : List AllocEvent)
    (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G')
    (htd : tdEnv (tryDecryptEnvArgs x) evs_total)
    (hreach : reaches_pc ((blkPC_131).rebase (blkPl_131).base H) retEpiloguePC_placed s
      (fun s1 => tryDecryptMidMeta_placed s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt (A.atState lim (M.stepEvents evs_total st_init) s1)
            x.ss G' (x.model C S uuidTryParse).2 ∗
          vecResultAt (A.atState lim (M.stepEvents evs_total st_init) s1)
            x.ret (x.model C S uuidTryParse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          tryDecryptCommonHeap (A.atState lim (M.stepEvents evs_total st_init) s1)
            ctl tryDecryptDummyImg x (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 ∗ R))) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv) (x, st_init) R s0 s := by
  have hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x))
      st_init (M.stepEvents evs_total st_init) (· = []) :=
    ⟨FitsEnv.nil, evs_total, rfl, by rintro _ rfl; simpa using htd⟩
  refine reaches_epilogue_to_outcome_seam_placed x st_init (M.stepEvents evs_total st_init)
    G' R s0 s hnpan hG' hsb (reaches_pc_mono hreach ?_)
  intro s1 _ _ ⟨hmeta, hm1⟩
  exact ⟨[], rfl, hmeta, hm1⟩

theorem reaches_epilogue_to_outcome_seam_fn_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {remEnv : List AllocEvent → Prop}
    (x : TryDecryptGhost) (st_init st : M.σ) (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.modelFn C decFn S uuidTryParse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.modelFn C decFn S uuidTryParse).1.toBool G')
    (hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st remEnv)
    (hreach : reaches_pc ((blkPC_131).rebase (blkPl_131).base H) retEpiloguePC_placed s
      (fun s1 => ∃ evs_exit : List AllocEvent, remEnv evs_exit ∧
        tryDecryptMidMeta_placed s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt (A.atState lim (M.stepEvents evs_exit st) s1)
            x.ss G' (x.modelFn C decFn S uuidTryParse).2 ∗
          decResultFnAt (A.atState lim (M.stepEvents evs_exit st) s1)
            x.ret (x.modelFn C decFn S uuidTryParse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          tryDecryptCommonHeap (A.atState lim (M.stepEvents evs_exit st) s1)
            ctl tryDecryptDummyImg x (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 ∗ R))) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptFnSpecPlaced C decFn A lim ctl uuidTryParse S tdEnv) (x, st_init) R s0 s := by
  have hcomb : reaches_pc ((blkPC_131).rebase (blkPl_131).base H) (s0.readReg64 .x30) s
      (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A lim ctl uuidTryParse S tdEnv).post
          (x, st_init) s0 sf ∗ R)) := by
    refine reaches_pc_seq hreach ?_
    rintro s1 hpc1 _ ⟨evs_exit, hexit,
      ⟨hrun1, hsp1, hs0_align, hsp_align1, _, htrace1, _, hvregs1⟩, hm1⟩
    obtain ⟨evs_total, hst_eq, htd_tot⟩ := hsb.finish hexit
    rw [hst_eq] at hm1
    set A1 : RustAlloc := A.atState lim (M.stepEvents evs_total st_init) s1
    unfold tryDecryptCommonHeap at hm1
    have hm1_re : s1.mem ⊨
        (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
          memRegion (s0.sp - 1504#64) 1408 ∗ tryDecryptSavedRegs s0.sp s0) ∗
        (sessionStateAt A1 x.ss G' (x.modelFn C decFn S uuidTryParse).2 ∗
         decResultFnAt A1 x.ret (x.modelFn C decFn S uuidTryParse).1 ∗
         protocolAddressAt A1 x.rem x.remA ∗
         protocolAddressAt A1 x.loc x.locA ∗ signalMessageAt A1 x.msgG x.msgA x.msg ∗
         tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff tryDecryptDummyImg ∗ A1.pool ∗ R) := by convert hm1 using 1; sep_ac_rfl
    refine reaches_pc_mono (sepWP_to_reaches_pc
      (tryDecrypt_epilogue_394_wp_placed s0 s1 hpc1 hrun1 hsp1 hs0_align hsp_align1 htrace1 hvregs1)
      hm1_re) ?_
    intro sf _ _ ⟨P_f, hm_sf, hsp_sf, htrace_sf, hvm_sf, hcc_sf, hP_f⟩
    refine ⟨hsp_sf, hcc_sf, ?_⟩
    have hm2 := Satisfies.mono (sepConj_mono_left hP_f) hm_sf
    have hA_eq : A.atState lim (M.stepEvents evs_total st_init) sf = A1 :=
      RustCliAllocBudget.atState_eq_of_vmPreserved A lim (M.stepEvents evs_total st_init) hvm_sf
    dsimp only [tryDecryptFnSpecPlaced, withLsCodeRoLoaded, tryDecryptFnRawSpecPlaced,
      CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptFnRawSpecPlaced]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs_total, ?_⟩
    rw [hA_eq, ← tryDecryptDummyImg_eq_placedImg]
    simp only [tryDecryptFnSpec, Spec.inImage]
    have hm3 : sf.mem ⊨
        sessionStateAt A1 x.ss G' (x.modelFn C decFn S uuidTryParse).2 ∗
        (decResultFnAt A1 x.ret (x.modelFn C decFn S uuidTryParse).1 ∗
         protocolAddressAt A1 x.rem x.remA ∗
         protocolAddressAt A1 x.loc x.locA ∗ signalMessageAt A1 x.msgG x.msgA x.msg ∗
         tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff tryDecryptDummyImg ∗ stackAt s0.sp rootStack ∗ A1.pool ∗ R) := by
      convert hm2 using 1; sep_ac_rfl
    have hent :
        sessionStateAt A1 x.ss G' (x.modelFn C decFn S uuidTryParse).2 ⊢
          ⌜tdEnv (tryDecryptEnvArgs x) evs_total⌝ ∗
          ⌜(x.modelFn C decFn S uuidTryParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (∃∗ G'' : SessionGhost,
            ⌜x.G.AfterTryDecrypt (x.modelFn C decFn S uuidTryParse).1.toBool G''⌝ ∗
            sessionStateAt A1 x.ss G'' (x.modelFn C decFn S uuidTryParse).2) :=
      Entails.pure_right htd_tot
        (Entails.pure_right ⟨hnpan, htrace_sf⟩
          (Entails.trans (Entails.pure_right hG' (Entails.refl _))
            (Entails.sepExists_intro
              (P := fun G'' =>
                ⌜x.G.AfterTryDecrypt (x.modelFn C decFn S uuidTryParse).1.toBool G''⌝ ∗
                  sessionStateAt A1 x.ss G'' (x.modelFn C decFn S uuidTryParse).2) G')))
    have hm4 := Satisfies.mono (sepConj_mono_left hent) hm3
    convert hm4 using 1; sep_ac_rfl
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, hsp_sf, hcc_sf, hpost_sf⟩ | ⟨_, hfalse⟩⟩ := hcomb hL
  · exact reaches_outcome_steps hsteps
      (reaches_outcome.of_outcome (Or.inl ⟨⟨hpc_sf, hsp_sf, hrun_sf⟩, ⟨hsp_sf, hcc_sf⟩, hpost_sf⟩))
  · exact hfalse.elim

theorem reaches_epilogue_to_outcome_fn_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (x : TryDecryptGhost) (st_init : M.σ) (evs_total : List AllocEvent)
    (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.modelFn C decFn S uuidTryParse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.modelFn C decFn S uuidTryParse).1.toBool G')
    (htd : tdEnv (tryDecryptEnvArgs x) evs_total)
    (hreach : reaches_pc ((blkPC_131).rebase (blkPl_131).base H) retEpiloguePC_placed s
      (fun s1 => tryDecryptMidMeta_placed s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt (A.atState lim (M.stepEvents evs_total st_init) s1)
            x.ss G' (x.modelFn C decFn S uuidTryParse).2 ∗
          decResultFnAt (A.atState lim (M.stepEvents evs_total st_init) s1)
            x.ret (x.modelFn C decFn S uuidTryParse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          tryDecryptCommonHeap (A.atState lim (M.stepEvents evs_total st_init) s1)
            ctl tryDecryptDummyImg x (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 ∗ R))) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptFnSpecPlaced C decFn A lim ctl uuidTryParse S tdEnv) (x, st_init) R s0 s := by
  have hsb : SeamBudget M lim (tdEnv (tryDecryptEnvArgs x))
      st_init (M.stepEvents evs_total st_init) (· = []) :=
    ⟨FitsEnv.nil, evs_total, rfl, by rintro _ rfl; simpa using htd⟩
  refine reaches_epilogue_to_outcome_seam_fn_placed x st_init (M.stepEvents evs_total st_init)
    G' R s0 s hnpan hG' hsb (reaches_pc_mono hreach ?_)
  intro s1 _ _ ⟨hmeta, hm1⟩
  exact ⟨[], rfl, hmeta, hm1⟩

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget

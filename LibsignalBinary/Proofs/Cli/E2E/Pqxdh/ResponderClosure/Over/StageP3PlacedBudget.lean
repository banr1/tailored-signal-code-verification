/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1ErrPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Stage P3 Over-Path Specification (`previous_sessions = [enc]`)

Proves budget-threaded `[LibsignalPlacement]` and `[LibsignalFullPlacement]` Stage P3 theorems
(`+0x1778 → +0x34dc` or `s0.readReg64 .x30`) over a 1-element `prevVecAt [enc]`, discharging
version-mismatch exits via `VerNeTopEnv` and bounding allocation via `StageP3Prev1Env`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto SessionState SignalMessage SignalProtocolError)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement lsHandleErrorSym lsLogFilterAddr lsMemcpySym
  lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost decryptDraws protocolAddressAt sessionStateAt
  signalMessageAt uuidTryParse vecResultAt
)
open CryptoVerification.LibsignalTripleRatchet (
  SeedsLen32 TryDecryptGhost extHookStack rootStack
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  growOneSpeStack lsLogOff setSessionStateStack
)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved decryptPrekeySavedRegsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (entails_replace_sub eq_of_sep_emp)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (
  GenP3S5FrontRem genP3S5Model genP3S5ModelPanicProp genP3S5SpillRem
  genP3SpillAll genP3SpillAll_entails_s5 memRegion344_104_240_eq
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  LsTokenInitM3 cloneExitPCPlaced dpClosureEntryM3Placed
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  overScratch prevVecAt stageP3Sub5ExtraPrePrev1 subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (OverPrevEncOK)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  CloneGenVRegsPlacedStmt StageP3ErrM3Env StageP3OkPrefixM3Env
  pollTryDecryptM3PlacedSpecP pollTryDecryptM3PlacedSpecTPTight stageP3M3TryDecryptEnvArgs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux (
  bind_sepWP_lscro_steps_m3_placed bind_sepWPp_false_steps_framed
  genP3PostPlaced genP3PrePlaced genP3S5PostFramePlaced p3_bl_tryDecrypt_placed_wp
  ret_sepWPp_frame_false sepWPp_frame_false_qp sepWPp_lift_false_qp sepWPp_weaken_frame
  stageP3ErrPostPrevEmptyM3Placed stageP3_sub5_decResult_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env cloneGen_vregs_placed_ok
  fitsEnv_postTd_of_stageP3Prev1Env fitsEnv_segClone_of_stageP3Prev1Env
  fitsEnv_td_of_stageP3Prev1Env fitsEnv_verNe_of_stageP3Prev1Env
  postTryDecrypt_entails_s5DispatchPrev1_placed
  stageP3DispatchOkMidPrev1Placed stageP3DispatchPrePrev1Placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1ErrPlacedBudget (
  stageP3ErrPrePrev1Placed stageP3_sub5_err_prev1_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  OverPrevDecodeCroPlacedAt
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWPlacedBudget (
  BytesMerge6Placed514OkExtW
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudget (
  ChainMerge5CroPlacedOkExt
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget (
  pqxdhLogClosurePlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudget (
  overVerNe_1e04_cro_placed_at overVerNe_1e04_cro_placed_of_alloc_bm6w_chain5
  overVerNe_1e04_cro_placed_of_hooks_chain5
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (
  VerNeTopEnv verNeMemcpyStackSpec
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget (tryDecryptPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget (tryDecryptOnPanicTight)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec growOneSpeSpec setSessionStateSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemmoveBudgetSpec
  sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  FromVPostTdEnv TryDecryptEnvArgs segCloneEvents tryDecryptEnvArgs
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## Version-Mismatch Exit Body and `VerNeTopEnv` Dischargers -/

/-- Budget-threaded placed version-mismatch exit body at `dpClosureEntryM3Placed + 0x1e04`,
advancing `A.pool lim st_init s1` by `verNeEnv enc`. -/
abbrev OverVerNe1e04CliAtPlacedBody [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PrevEncOK : List (BitVec 8) → Prop)
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st_init : M.σ) (s0 s s1 : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64),
    initErrsPtr ≠ 0#64 → prevCap ≠ 0#64 →
    ∀ (msgVer : BitVec 32), msgVer ≠ 4#32 →
    ∀ (b_2c0 : BitVec 8) (enc : List (BitVec 8)),
      PrevEncOK enc →
      FitsEnv M lim st_init (verNeEnv enc) →
    ∀ (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8))),
      st.version = 4#32 → rootStack ≤ s.sp.toNat →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.pc = dpClosureEntryM3Placed + 0x1e04#64 →
      s1.status = .Running → s1.sp = s.sp → (s.sp &&& 15#64 == 0#64) = true → s1.trace = s0.trace →
      s1.readReg64 .x9 = msgVer.setWidth 64 → s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 → s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x29 = s.sp + 0xc70#64 →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
        (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
         ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
         ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
         memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
         memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
         sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
         sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
         prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
         lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
         memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
         decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
         A.pool lim st_init s1 ∗ stackAt s.sp rootStack)
        (fun sf P_f =>
          (∃ (wd0 : BitVec 64) (evs : List AllocEvent),
            verNeEnv enc evs ∧
            (P_f ⊢
              ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
              ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
              memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
              memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
              stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs st_init) s0 s sf coroPtr outPtr
                (.invalidMessage .preKey .decryptionFailed))) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
        (fun _ _ => False)

theorem OverVerNe1e04CliAtPlacedBody.mono_prevEncOK [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P Q : List (BitVec 8) → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hpq : ∀ enc, P enc → Q enc)
    (h : OverVerNe1e04CliAtPlacedBody A lim Q verNeEnv ext) :
    OverVerNe1e04CliAtPlacedBody A lim P verNeEnv ext :=
  fun st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
    hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc hEnc hfits =>
    h st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
      hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc (hpq enc hEnc) hfits

private theorem sepWPp_weaken_post_false {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun _ _ => False))
    (himp : ∀ sf P_f, Q sf P_f → Q' sf P_f) :
    SepWPp prog ret s P Q' (fun _ _ => False) := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | ⟨_, _, _, hf⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, himp sf P_f hQ⟩⟩
  · exact hf.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem overVerNe1e04CliAtPlacedBody_of_cro_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    (hEncImp : ∀ enc, PrevEncOK enc → OverPrevEncOK enc)
    (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (verNeMemcpyStackSpec allocHookStack))
    (hPrevDec : OverPrevDecodeCroPlacedAt A lim ext) :
    OverVerNe1e04CliAtPlacedBody A lim PrevEncOK VerNeTopEnv ext :=
  OverVerNe1e04CliAtPlacedBody.mono_prevEncOK hEncImp
    (fun st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
        hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
        hver4 hsp_root hcro1 hpc1 hrun1 hs1_sp hsp_align htr1
        hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 =>
      sepWPp_weaken_post_false
        (overVerNe_1e04_cro_placed_at ext hLogClosure hGrow hDropSS3
          hshim halloc hdealloc hmemcpy hPrevDec
          st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
          hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
          hver4 hsp_root hcro1 hpc1 hrun1 hs1_sp hsp_align htr1
          hx9_1 hx19_1 hx24_1 hx27_1 hx29_1)
        (fun _ _ ⟨hpost, hsp, htr, hcc, hcro, _, hvregs⟩ =>
          ⟨hpost, hsp, htr, hcc, hcro, hvregs⟩))

theorem overVerNe1e04CliAtPlacedBody_of_alloc_bm6w_chain5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    (hEncImp : ∀ enc, PrevEncOK enc → OverPrevEncOK enc)
    (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (sessionMemcpyBudgetSpec allocHookStack))
    (hAlloc : AllocContractsPlaced M A lim ext)
    (hBM6W : BytesMerge6Placed514OkExtW A lim ext)
    (hChain5 : ChainMerge5CroPlacedOkExt A lim ext) :
    OverVerNe1e04CliAtPlacedBody A lim PrevEncOK VerNeTopEnv ext :=
  OverVerNe1e04CliAtPlacedBody.mono_prevEncOK hEncImp
    (fun st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
        hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
        hver4 hsp_root hcro1 hpc1 hrun1 hs1_sp hsp_align htr1
        hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 =>
      sepWPp_weaken_post_false
        (overVerNe_1e04_cro_placed_of_alloc_bm6w_chain5 ext hLogClosure hGrow hDropSS3
          hshim halloc hdealloc hmemcpy hAlloc hBM6W hChain5
          st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
          hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
          hver4 hsp_root hcro1 hpc1 hrun1 hs1_sp hsp_align htr1
          hx9_1 hx19_1 hx24_1 hx27_1 hx29_1)
        (fun _ _ ⟨hpost, hsp, htr, hcc, hcro, _, hvregs⟩ =>
          ⟨hpost, hsp, htr, hcc, hcro, hvregs⟩))

theorem overVerNe1e04CliAtPlacedBody_of_hooks_chain5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    (hEncImp : ∀ enc, PrevEncOK enc → OverPrevEncOK enc)
    (ext : LibsignalHooks)
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hshim_sat : HookSat ext lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_sat : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc_sat : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc_sat : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hmemmove_sat : HookSat ext "memmove" (sessionMemmoveBudgetSpec extHookStack))
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked)
    (hChain5 : ChainMerge5CroPlacedOkExt A lim ext) :
    OverVerNe1e04CliAtPlacedBody A lim PrevEncOK VerNeTopEnv ext :=
  OverVerNe1e04CliAtPlacedBody.mono_prevEncOK hEncImp
    (fun st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
        hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
        hver4 hsp_root hcro1 hpc1 hrun1 hs1_sp hsp_align htr1
        hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 =>
      sepWPp_weaken_post_false
        (overVerNe_1e04_cro_placed_of_hooks_chain5 ext hLogClosure hGrow hDropSS3
          hshim_sat halloc_sat hrealloc_sat hdealloc_sat hmc_sat hmemmove_sat hpanic_raw hChain5
          st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
          hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
          hver4 hsp_root hcro1 hpc1 hrun1 hs1_sp hsp_align htr1
          hx9_1 hx19_1 hx24_1 hx27_1 hx29_1)
        (fun _ _ ⟨hpost, hsp, htr, hcc, hcro, _, hvregs⟩ =>
          ⟨hpost, hsp, htr, hcc, hcro, hvregs⟩))

abbrev subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_budget :=
  @subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded

/-! ## `try_decrypt_with_state` Call and Dispatch (`previous_sessions = [enc]`) -/

private theorem stageP3_clone_prev1_vregs_prefix_placed_steps [LibsignalPlacement]
    (hClone : CloneGenVRegsPlacedStmt)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (C : Crypto) (K : MlKem) (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hcc : ChainClone3OkPlaced A lim ext) (hscc : SenderChainClone3OkPlaced A lim ext)
    (st_b : M.σ) (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (enc : List (BitVec 8)) (msgVer : BitVec 32) (b_2c0 : BitVec 8) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop)
    (hfits_clone : FitsEnv M lim st_b
      (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv recG st))
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1778#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hCont : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 →
      s1.pc = cloneExitPCPlaced st msgVer → s1.status = .Running → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl s1.mem →
      (P1 ⊢
        genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b)
          s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
        (LsTokenInitM3 ∗
          stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          overScratch s.sp ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q
        (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (LsTokenInitM3 ∗
        genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
          enc b_2c0 ∗
        overScratch s.sp ∗ F_frame)
      Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hstep := hClone ext hshim halloc hmemcpy hcc hscc st_b s0 s s.sp (s.readReg64 .x29)
    coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hfits_clone hrc_lt hsp_align hsp_root hcro hpc hrun htr
  let F : SepProp :=
    LsTokenInitM3 ∗
      stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc
        b_2c0 ∗
      overScratch s.sp ∗ F_frame
  have hP :
      (LsTokenInitM3 ∗
        genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
          enc b_2c0 ∗
        overScratch s.sp ∗ F_frame) =
      genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ F := by
    dsimp only [F]; ac_rfl
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hsteps,
      ⟨hpc1, hrun1, P1, hm1, hent1, htr1, hcro1, hvregs1_s⟩ | ⟨_, _, _, hf⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hCont s1 (P1 ∗ F) hsteps hpc1 hrun1 htr1 (hvregs1_s.trans hvregs) hcro1
        (sepConj_mono_left hent1) R hm1 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact hf.elim
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `try_decrypt_with_state` call at `dpClosureEntryM3Placed + 0x1cd4` under
`StoreKit.withLsCodeRoLoaded lsmpl`. -/
theorem stageP3_call_tryDecrypt_prev1_placed_steps [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (C : Crypto) (ctl : BitVec 64) (K : MlKem)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (hroot : subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv)))
    (st_b : M.σ) (s0 s s1 : State)
    (coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F : SepProp) (Q : State → SepProp → Prop)
    (hver : st.version = msgVer)
    (hfits_td : FitsEnv M lim st_b
      (tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)))
    (hnot_self : st.remoteIdentity ≠ some st.localIdentity ∨
      DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)
    (hseeds : SeedsLen32 st) (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hpq_lt : st.pqRatchetState.length < 2 ^ 32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (hcro1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = dpClosureEntryM3Placed + 0x1cd4#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (htr1 : s1.trace = s0.trace)
    (hx0_1 : s1.readReg64 .x0 = s.sp + 0x270#64) (hx1_1 : s1.readReg64 .x1 = s.sp + 0xa90#64)
    (hx2_1 : s1.readReg64 .x2 = remAddrPtr) (hx3_1 : s1.readReg64 .x3 = locAddrPtr)
    (hx4_1 : s1.readReg64 .x4 = whisperMsgPtr) (hx5_1 : s1.readReg64 .x5 = 3#64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr) (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hCont : ∀ (s2 : State) (G' : SessionGhost) (evs_td : List AllocEvent),
      Steps (lsProg_518 ext) s1 s2 →
      tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) evs_td →
      (genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic →
      G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G' →
      s2.pc = dpClosureEntryM3Placed + 0x1cd8#64 → s2.status = .Running →
      s2.sp = s.sp → s2.trace = s0.trace → LibsignalCodeRoLoaded lsmpl s2.mem →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x24 = s.sp + 0x370#64 →
      s2.readReg64 .x27 = ctxPtr → calleeSavedVRegs s2 = calleeSavedVRegs s1 →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s2
        ((LsTokenInitM3 ∗
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
          vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
          protocolAddressAt A.repAlloc rem remAddrPtr ∗
          protocolAddressAt A.repAlloc loc locAddrPtr ∗
          signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
          coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
          lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim (M.stepEvents evs_td st_b) s2) ∗ F)
        Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      ((LsTokenInitM3 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A.repAlloc rem remAddrPtr ∗
        protocolAddressAt A.repAlloc loc locAddrPtr ∗
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim st_b s1) ∗ F)
      Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0) := by
  have hbl := p3_bl_tryDecrypt_placed_wp A lim st_b ext s1 hpc1 hrun1
  refine bind_sepWP_lscro_steps_m3_placed hcro1 hbl (by sep_focus)
    fun sc hsteps_bl hpcc hrunc hcroc hregsc => ?_
  rcases hregsc with ⟨hspc_1, htrc_1, hx0_c, hx1_c, hx2_c, hx3_c, hx4_c, hx5_c,
    hx19_c, hx24_c, hx27_c, _, hx30_c, hvregs_c⟩
  have hspc : sc.sp = s.sp := hspc_1.trans hs1_sp
  have hspc_al : sc.spAligned = true := by simpa only [State.spAligned, hspc] using hsp_align
  have htrc_0 : sc.trace = s0.trace := htrc_1.trans htr1
  let x : TryDecryptGhost := {
    G := G₁, st := st, rem := rem, loc := loc, msgG := msgG, msg := msg,
    msgType := .preKey, ss := s.sp + 0xa90#64, remA := remAddrPtr, locA := locAddrPtr,
    msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest
  }
  intro R hm hL
  have hpre_c :
      sc.mem ⊨
        (withLsCodeRoLoaded lsmpl
          (pollTryDecryptM3PlacedSpecTPTight C A lim ctl uuidTryParse
            (spqrV1 C.F K) tdEnv)).pre (x, st_b) sc ∗ (F ∗ R) := by
    dsimp only [withLsCodeRoLoaded, pollTryDecryptM3PlacedSpecTPTight, pollTryDecryptM3PlacedSpecP,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.pollTryDecryptM3PlacedSpecP,
      CryptoVerification.Cli.CoinsTape.cliTapeAt, x]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcroc, ?_⟩
    rw [hspc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpq_lt, ?_⟩
    have hx5_byte : (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey := by
      rw [hx5_c, hx5_1]; rfl
    have hfits_x : FitsEnv M lim st_b (tdEnv (tryDecryptEnvArgs {
        G := G₁, st := st, rem := rem, loc := loc, msgG := msgG, msg := msg,
        msgType := .preKey, ss := s.sp + 0xa90#64, remA := remAddrPtr, locA := locAddrPtr,
        msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest })) := hfits_td
    have hp_fits : FitsEnv M lim st_b (tdEnv (tryDecryptEnvArgs {
        G := G₁, st := st, rem := rem, loc := loc, msgG := msgG, msg := msg,
        msgType := .preKey, ss := s.sp + 0xa90#64, remA := remAddrPtr, locA := locAddrPtr,
        msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest })) = True :=
      propext ⟨fun _ => trivial, fun _ => hfits_x⟩
    have hp2 : (sc.readReg64 .x0 = s.sp + 0x270#64 ∧ sc.readReg64 .x1 = s.sp + 0xa90#64 ∧
        sc.readReg64 .x2 = remAddrPtr ∧ sc.readReg64 .x3 = locAddrPtr ∧
        sc.readReg64 .x4 = whisperMsgPtr ∧ (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey ∧
        (st.remoteIdentity ≠ some st.localIdentity ∨
          DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) ∧
        SeedsLen32 st ∧ st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat) = True :=
      propext ⟨fun _ => trivial, fun _ =>
        ⟨hx0_c.trans hx0_1, hx1_c.trans hx1_1, hx2_c.trans hx2_1, hx3_c.trans hx3_1,
         hx4_c.trans hx4_1, hx5_byte, hnot_self, hseeds, hrc_lt, hsp_root⟩⟩
    rw [hp_fits, hp2, pure_true, emp_sepConj, emp_sepConj]
    have hpool_eq : (A.atState lim st_b sc).pool = A.pool lim st_b sc := rfl
    have hss_eq : sessionStateAt (A.atState lim st_b sc) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa1_eq : protocolAddressAt (A.atState lim st_b sc) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa2_eq : protocolAddressAt (A.atState lim st_b sc) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_b sc) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    rw [hpool_eq, hss_eq, hpa1_eq, hpa2_eq, hsm_eq]
    exact Arm64.Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  obtain ⟨s2, hsteps2, hout2, _⟩ :=
    hroot.no_fault_before_outcome (x, st_b) (F ∗ R) sc hpcc hrunc hpre_c hspc_al hL
  rcases hout2 with ⟨⟨hpc2_lr, hsp2_c, hrun2⟩, ⟨_, hcs2⟩, hm2⟩ | ⟨hpan, hm_pan⟩ | ⟨_, _, hexit⟩ | ⟨_, hoom⟩
  · dsimp only [withLsCodeRoLoaded, pollTryDecryptM3PlacedSpecTPTight, pollTryDecryptM3PlacedSpecP,
      tryDecryptPlacedSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      CryptoVerification.Cli.CoinsTape.cliTapeAfter, TryDecryptGhost.model, x] at hm2
    rw [hspc] at hm2
    have hcro2 : LibsignalCodeRoLoaded lsmpl s2.mem := hcroc.of_keepsFrozen hsteps2.keepsFrozen
    have hm2_ex_evs :
        s2.mem ⊨
          ∃∗ evs_td : List AllocEvent,
            ⌜tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) evs_td⌝ ∗
            (⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
              ((∃∗ G' : SessionGhost,
                  ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
                  sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
                    (genP3S5Model C K rem loc msg rest st).2) ∗
                LsTokenInitM3 ∗
                vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
                protocolAddressAt A.repAlloc rem remAddrPtr ∗
                protocolAddressAt A.repAlloc loc locAddrPtr ∗
                signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
                coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
                lsLogOff ∗ stackAt s.sp rootStack ∗
                A.pool lim (M.stepEvents evs_td st_b) s2 ∗ F ∗ R)) := by
      rw [sepExists_sepConj_right, sepExists_sepConj_left] at hm2
      rw [satisfies_sepExists] at hm2 ⊢
      obtain ⟨evs_td, hm2_ev⟩ := hm2
      refine ⟨evs_td, ?_⟩
      have hss_eq2 : ∀ G',
          sessionStateAt (A.atState lim (M.stepEvents evs_td st_b) s2) (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := fun _ => rfl
      have hvec_eq2 :
          vecResultAt (A.atState lim (M.stepEvents evs_td st_b) s2) (s.sp + 0x270#64)
            (genP3S5Model C K rem loc msg rest st).1 =
          vecResultAt A.repAlloc (s.sp + 0x270#64)
            (genP3S5Model C K rem loc msg rest st).1 := rfl
      have hpa1_eq2 :
          protocolAddressAt (A.atState lim (M.stepEvents evs_td st_b) s2) rem remAddrPtr =
          protocolAddressAt A.repAlloc rem remAddrPtr := rfl
      have hpa2_eq2 :
          protocolAddressAt (A.atState lim (M.stepEvents evs_td st_b) s2) loc locAddrPtr =
          protocolAddressAt A.repAlloc loc locAddrPtr := rfl
      have hsm_eq2 :
          signalMessageAt (A.atState lim (M.stepEvents evs_td st_b) s2) msgG whisperMsgPtr msg =
          signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
      have hpool_eq2 : (A.atState lim (M.stepEvents evs_td st_b) s2).pool =
          A.pool lim (M.stepEvents evs_td st_b) s2 := rfl
      have hargs_eq : tryDecryptEnvArgs {
          G := G₁, st := st, rem := rem, loc := loc, msgG := msgG, msg := msg,
          msgType := .preKey, ss := s.sp + 0xa90#64, remA := remAddrPtr, locA := locAddrPtr,
          msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest } =
        stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest := rfl
      simp only [hss_eq2, hvec_eq2, hpa1_eq2, hpa2_eq2, hsm_eq2, hpool_eq2, hargs_eq] at hm2_ev
      have heq_ev :
          (LsTokenInitM3 ∗
            (⌜tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) evs_td⌝ ∗
              (⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
                (∃∗ G' : SessionGhost,
                  ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
                  sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
                    (genP3S5Model C K rem loc msg rest st).2) ∗
                vecResultAt A.repAlloc (s.sp + 0x270#64)
                  (genP3S5Model C K rem loc msg rest st).1 ∗
                protocolAddressAt A.repAlloc rem remAddrPtr ∗
                protocolAddressAt A.repAlloc loc locAddrPtr ∗
                signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
                coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
                lsLogOff ∗ stackAt s.sp rootStack ∗
                A.pool lim (M.stepEvents evs_td st_b) s2))) ∗ (F ∗ R) =
          ⌜tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) evs_td⌝ ∗
          (⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
            ((∃∗ G' : SessionGhost,
                ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
                sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
                  (genP3S5Model C K rem loc msg rest st).2) ∗
              LsTokenInitM3 ∗
              vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
              protocolAddressAt A.repAlloc rem remAddrPtr ∗
              protocolAddressAt A.repAlloc loc locAddrPtr ∗
              signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
              coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
              lsLogOff ∗ stackAt s.sp rootStack ∗
              A.pool lim (M.stepEvents evs_td st_b) s2 ∗ F ∗ R)) := by ac_rfl
      rwa [heq_ev] at hm2_ev
    rw [satisfies_sepExists] at hm2_ex_evs
    obtain ⟨evs_td, hm2_td⟩ := hm2_ex_evs
    rw [satisfies_pure_sepConj] at hm2_td
    rcases hm2_td with ⟨htd_evs, hm2_pull⟩
    rw [satisfies_pure_sepConj] at hm2_pull
    rcases hm2_pull with ⟨⟨hnpan, htr2_c⟩, hm2_ex⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_ex
    obtain ⟨G', hm2_G⟩ := hm2_ex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2_G
    obtain ⟨hdec_rel, hm2_rest⟩ := hm2_G
    have hm2_cont :
        s2.mem ⊨
          ((LsTokenInitM3 ∗
            sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
              (genP3S5Model C K rem loc msg rest st).2 ∗
            vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A.repAlloc rem remAddrPtr ∗
            protocolAddressAt A.repAlloc loc locAddrPtr ∗
            signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
            coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim (M.stepEvents evs_td st_b) s2) ∗ F) ∗ R := by
      have heq2 :
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
          (LsTokenInitM3 ∗
            vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A.repAlloc rem remAddrPtr ∗
            protocolAddressAt A.repAlloc loc locAddrPtr ∗
            signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
            coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            lsLogOff ∗ stackAt s.sp rootStack ∗
            A.pool lim (M.stepEvents evs_td st_b) s2 ∗ F ∗ R) =
          ((LsTokenInitM3 ∗
            sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
              (genP3S5Model C K rem loc msg rest st).2 ∗
            vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A.repAlloc rem remAddrPtr ∗
            protocolAddressAt A.repAlloc loc locAddrPtr ∗
            signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
            coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            lsLogOff ∗ stackAt s.sp rootStack ∗
            A.pool lim (M.stepEvents evs_td st_b) s2) ∗ F) ∗ R := by ac_rfl
      rwa [heq2] at hm2_rest
    rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, _, _, hx27_cs2, _, _, hvregs_cs2⟩
    obtain ⟨sf, hsteps3, hout3⟩ :=
      hCont s2 G' evs_td (hsteps_bl.trans hsteps2) htd_evs hnpan hdec_rel
        (hpc2_lr.trans hx30_c) hrun2
        (hsp2_c.trans hspc) (htr2_c.trans htrc_0) hcro2
        (hx19_cs2.trans (hx19_c.trans hx19_1)) (hx24_cs2.trans (hx24_c.trans hx24_1))
        (hx27_cs2.trans (hx27_c.trans hx27_1)) (hvregs_cs2.trans hvregs_c)
        R hm2_cont (hsteps2.codeLoaded hL)
    exact ⟨sf, hsteps2.trans hsteps3, hout3⟩
  · dsimp only [withLsCodeRoLoaded, pollTryDecryptM3PlacedSpecTPTight,
      tryDecryptOnPanicTight, TryDecryptGhost.model, x] at hm_pan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pan
    rcases hm_pan with ⟨⟨hmod_pan, hpref_c⟩, hm_any⟩
    have hpref_0 : s0.trace <+: s2.trace := htrc_0 ▸ hpref_c
    have hm_any_R : s2.mem ⊨ anyHeap ∗ R := by
      rw [← sepConj_assoc] at hm_any
      exact Arm64.Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_any
    refine ⟨s2, hsteps2, Or.inr (Or.inl ⟨hpan,
      ⌜st.version = msgVer ∧ (genP3S5Model C K rem loc msg rest st).1 = .error .panic ∧
          s0.trace <+: s2.trace⌝ ∗ anyHeap, ?_, fun _ h => h⟩)⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hver, hmod_pan, hpref_0⟩, hm_any_R⟩
  · exact (allowPanic_not_exited hexit).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Stage P3 Composition (`StageP3Prev1VRegsM3PlacedStmt`) -/

/-- Budget-threaded placed Stage P3 specification (`dpClosureEntryM3Placed + 0x1778 → +0x34dc` or
`s0.readReg64 .x30`) over a 1-element `prevVecAt [enc]`. -/
def StageP3Prev1VRegsM3PlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PrevEncOK : List (BitVec 8) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop) : Prop :=
  ∀ (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : MlKem),
    subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec) →
    ChainClone3OkPlaced A lim ext →
    SenderChainClone3OkPlaced A lim ext →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv)) →
    OverVerNe1e04CliAtPlacedBody A lim PrevEncOK verNeEnv ext →
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8) (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b
        (StageP3Prev1Env tdEnv verNeEnv recG st rem loc msgG msg msgVer enc rest) →
      initErrsPtr ≠ 0#64 → prevCap ≠ 0#64 → PrevEncOK enc → st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpClosureEntryM3Placed + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (evs_ok : List AllocEvent) (s' : State) (P_s' : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_ok →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        Steps (lsProg_518 ext) s s' → s'.pc = dpClosureEntryM3Placed + 0x34dc#64 →
        s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrev1Placed A lim (M.stepEvents evs_ok st_b) s0 s s'
            coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr enc pt b_2c0 G'
            (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (evs_err : List AllocEvent)
          (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        StageP3ErrM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_err →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_err st_b) s0 s sf coroPtr
            outPtr e ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_vn : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNePrev1Env verNeEnv recG st enc evs_vn →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_vn st_b) s0 s sf coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
        (LsTokenInitM3 ∗
          genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          overScratch s.sp ∗ F_frame)
        Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)

set_option maxHeartbeats 1200000 in
private theorem stageP3Gen_prev1_ver_ne_branch_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (C : Crypto) (K : MlKem)
    (hVerNeAt : OverVerNe1e04CliAtPlacedBody A lim PrevEncOK verNeEnv ext)
    (st_b : M.σ) (s0 s s1 : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8) (enc rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop)
    (hfits : FitsEnv M lim st_b
      (StageP3Prev1Env tdEnv verNeEnv recG st rem loc msgG msg msgVer enc rest))
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap_nz : prevCap ≠ 0#64)
    (hEnc : PrevEncOK enc) (hst_ver4 : st.version = 4#32) (hver : st.version ≠ msgVer)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (hx29_s : s.readReg64 .x29 = s.sp + 0xc70#64)
    (hcro1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = dpClosureEntryM3Placed + 0x1e04#64)
    (hrun1 : s1.status = .Running) (htr1 : s1.trace = s0.trace)
    (hvregs1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hVerNe : ∀ (evs_vn : List AllocEvent) (sf : State) (P_f : SepProp),
      st.version ≠ msgVer →
      StageP3VerNePrev1Env verNeEnv recG st enc evs_vn →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_vn st_b) s0 s sf coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed) ∗
        genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAtPlaced cur rest) ∗
        overScratch s.sp) →
      sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      Q sf (P_f ∗ F_frame)) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      ((CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostNePlaced
          (A.atState lim (M.stepEvents (segCloneEvents recG st) st_b) s1)
          s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
        (LsTokenInitM3 ∗
          stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          overScratch s.sp)) ∗ F_frame)
      Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0) := by
  have hmsgVer_ne4 : msgVer ≠ 4#32 := fun h => hver (hst_ver4.trans h.symm)
  apply sepWPp_lift_false_qp
  apply sepWPp_frame_false_qp
  unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostNePlaced
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
    stageP3Sub5ExtraPrePrev1
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1⟩ => ?_
  have hx29_1' : s1.readReg64 .x29 = s.sp + 0xc70#64 := hx29_1.trans hx29_s
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun G₁ => ?_
  refine sepWPp_weaken_frame
    (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun _ => ?_
  set st_clone := M.stepEvents (segCloneEvents recG st) st_b
  have hfits_vn : FitsEnv M lim st_clone (verNeEnv enc) :=
    fitsEnv_verNe_of_stageP3Prev1Env hver hfits
  have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
  have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
      sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
  have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
      protocolAddressAt A.repAlloc rem remAddrPtr := rfl
  have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
      protocolAddressAt A.repAlloc loc locAddrPtr := rfl
  have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
      signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
  have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
  simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
  refine sepWPp_weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus) ?_
  unfold genP3S5SpillRem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun wFront => ?_
  refine sepWPp_weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_
  have hver_ne := hVerNeAt st_clone
    s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr wFront.ud0
    hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc hEnc hfits_vn G₁ recG st
    hst_ver4 hsp_root hcro1 hpc1 hrun1 hs1_sp hsp_align htr1
    hx9_1 hx19_1 hx24_1 hx27_1 hx29_1'
  refine ret_sepWPp_frame_false hver_ne (by sep_focus)
    fun sf _ _ _ ⟨⟨wd0, evs_vn, hvn_evs, hent_f⟩, hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
  let evs_vn_tot := segCloneEvents recG st ++ evs_vn
  have hevs_vn_tot : StageP3VerNePrev1Env verNeEnv recG st enc evs_vn_tot :=
    Or.inr ⟨segCloneEvents recG st, evs_vn, rfl, rfl, hvn_evs⟩
  have hstep_vn : M.stepEvents evs_vn st_clone = M.stepEvents evs_vn_tot st_b := by
    dsimp only [st_clone, evs_vn_tot]
    rw [M.stepEvents_append (segCloneEvents recG st) evs_vn st_b]
  rw [hstep_vn] at hent_f
  refine hVerNe evs_vn_tot sf _ hver hevs_vn_tot ?_ hspf htrf hcc_f
    (hvregsf_1.trans hvregs1) hcrof
  unfold genP3S5PostFramePlaced
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3S5PostFramePlaced
    genP3S5SpillRem
  have hwFront_repack :
      ((s.sp + 0x48#64) ↦₆₄ wFront.u48) ∗ ((s.sp + 0x50#64) ↦₆₄ wFront.u50) ∗
      ((s.sp + 0x5c#64) ↦₃₂ wFront.u5c) ∗ ((s.sp + 0x7c#64) ↦₃₂ wFront.u7c) ∗
      ((s.sp + 0x98#64) ↦₆₄ wFront.u98) ∗ ((s.sp + 0xd0#64) ↦₆₄ wd0) ⊢
      ∃∗ w : GenP3S5FrontRem,
        ((s.sp + 0x48#64) ↦₆₄ w.u48) ∗ ((s.sp + 0x50#64) ↦₆₄ w.u50) ∗
        ((s.sp + 0x5c#64) ↦₃₂ w.u5c) ∗ ((s.sp + 0x7c#64) ↦₃₂ w.u7c) ∗
        ((s.sp + 0x98#64) ↦₆₄ w.u98) ∗ ((s.sp + 0xd0#64) ↦₆₄ w.ud0) :=
    Entails.sepExists_right ⟨wFront.u48, wFront.u50, wFront.u98, wd0, wFront.u5c, wFront.u7c⟩
      (Entails.refl _)
  exact Entails.trans (sepConj_mono_left hent_f)
    (entails_replace_sub hwFront_repack (by sep_focus) (eq_of_sep_emp (by sep_focus)))

set_option maxHeartbeats 1200000 in
/-- Budget-threaded placed Stage P3 (`+0x1778 → +0x34dc` or `s0.readReg64 .x30`) over a 1-element
`prevVecAt [enc]`, parameterized by `CloneGenVRegsPlacedStmt`. -/
theorem stageP3Gen_prev1_vregs_at_placed_ok_of_clone [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hClone : CloneGenVRegsPlacedStmt) :
    StageP3Prev1VRegsM3PlacedStmt A lim PrevEncOK tdEnv verNeEnv := by
  intro ext C ctl K hshim halloc hdealloc hmemcpy hGrow hSetState hDropSS3 hLogClosure
    hcc hscc hroot hVerNeAt st_b s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg F_frame Q
    hfits hinit_ne hcap_nz hEnc hst_ver4 hnot_self hseeds hrc_lt hpq_lt
    hcro hpc hrun hsp_align hsp_root hx29_s htr hvregs hOk hErr hVerNe
  have hfits_clone := fitsEnv_segClone_of_stageP3Prev1Env hfits
  refine stageP3_clone_prev1_vregs_prefix_placed_steps hClone C K ext
    hshim halloc hmemcpy hcc hscc st_b
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur enc msgVer b_2c0 rest
    recG st rem loc msgG msg F_frame Q hfits_clone hrc_lt hcro hpc hrun hsp_align hsp_root
    htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 ?_
  refine SepWPp.weaken_pre
    (P' := (genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b)
        s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
          enc b_2c0 ∗
        overScratch s.sp)) ∗ F_frame)
    (Entails.of_eq (by ac_rfl)) ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostEqPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine sepWPp_weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun hclone_rel => ?_
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_td : FitsEnv M lim st_clone
        (tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)) :=
      fitsEnv_td_of_stageP3Prev1Env hver hclone_rel hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 _ Q _
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    let F_dec : SepProp :=
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc
        b_2c0 ∗
      overScratch s.sp
    refine SepWPp.weaken_pre
      (P' := (LsTokenInitM3 ∗
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A.repAlloc rem remAddrPtr ∗
        protocolAddressAt A.repAlloc loc locAddrPtr ∗
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
        memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗
        lsLogOff ∗
        stackAt s.sp rootStack ∗
        A.pool lim st_clone s1) ∗ (F_dec ∗ F_frame))
      (Entails.of_eq (eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K tdEnv hroot st_clone
      s0 s s1 coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hfits_td hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' evs_td hsteps12 htd_evs hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2
          hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    let st_td := M.stepEvents evs_td st_clone
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left
          (postTryDecrypt_entails_s5DispatchPrev1_placed A lim st_td s0 s s2
            coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
            remAddrPtr locAddrPtr whisperMsgPtr enc msgVer b_2c0
            (genP3S5Model C K rem loc msg rest st).1 G' recG
            (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    have hlog : (lsLogFilterAddr ↦₆₄ 0#64) = lsLogOff := rfl
    unfold stageP3DispatchPrePrev1Placed
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP3DispatchPrePrev1Placed
    rw [hlog]
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hfits_post : FitsEnv M lim st_td FromVPostTdEnv :=
        fitsEnv_postTd_of_stageP3Prev1Env hver hclone_rel htd_evs hfits
      have herr := stageP3_sub5_err_prev1_placed_ok ext hshim halloc hdealloc hGrow hDropSS3
        hLogClosure st_td s0 s2 coroPtr outPtr initErrsPtr prevCap prevPtr
        hfits_post hinit_ne e he_npan b_2c0 enc G' recG
        (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrev1Placed
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP3ErrPrePrev1Placed at herr
      have herr_post : ∀ st_e sf,
          stageP3ErrPostPrevEmptyM3Placed A lim st_e s0 s2 sf coroPtr outPtr e =
            stageP3ErrPostPrevEmptyM3Placed A lim st_e s0 s sf coroPtr outPtr e := by
        intro st_e sf
        unfold stageP3ErrPostPrevEmptyM3Placed
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyM3Placed
        rw [hs2_sp]
      simp only [herr_post, hs2_sp] at herr
      apply sepWPp_lift_false_qp
      apply sepWPp_frame_false_qp
      refine ret_sepWPp_frame_false herr (by sep_focus)
        fun sf _ _ _ ⟨evs_err, herr_evs, hPf_err, hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      let evs_tot := segCloneEvents recG st ++ (evs_td ++ evs_err)
      have hevs_tot : StageP3ErrM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_tot :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_err, rfl, rfl,
          Or.inr ⟨evs_td, evs_err, rfl, htd_evs, herr_evs⟩⟩
      have hstep_tot : M.stepEvents evs_err st_td = M.stepEvents evs_tot st_b := by
        dsimp only [st_td, st_clone, evs_tot]
        rw [M.stepEvents_append (segCloneEvents recG st) (evs_td ++ evs_err) st_b,
            M.stepEvents_append evs_td evs_err (M.stepEvents (segCloneEvents recG st) st_b)]
      rw [hstep_tot] at hPf_err
      refine hErr G₁ G' e evs_tot sf _ hver hclone_rel hdec_false hevs_tot hres he_npan ?_
        hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      exact Entails.trans (sepConj_mono_left hPf_err)
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hstack_set :
          stackAt s.sp growOneSpeStack =
            memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hvec_eq_s2 :
          vecResultAt (A.atState lim st_td s2) (s.sp + 0x270#64) (.ok pt) =
          vecResultAt A.repAlloc (s.sp + 0x270#64) (.ok pt) := rfl
      have hss_g_eq_s2 :
          sessionStateAt (A.atState lim st_td s2) (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hss_rec_eq_s2 :
          sessionStateAt (A.atState lim st_td s2) (coroPtr + 0xf8#64) recG st =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
      have hprev_eq_s2 :
          prevVecAt (A.atState lim st_td s2) (coroPtr + 0xe0#64) prevCap prevPtr [enc] =
          prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] := rfl
      have hpool_eq_s2 : (A.atState lim st_td s2).pool = A.pool lim st_td s2 := rfl
      simp only [hvec_eq_s2, hss_g_eq_s2, hss_rec_eq_s2, hprev_eq_s2, hpool_eq_s2]
      have hok := stageP3_sub5_decResult_placed_ok ext hmemcpy hSetState st_td
        s0 s2 coroPtr outPtr pt G' recG
        (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_false_steps_framed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨evs_free, ptCap, ptPtr, hevs_free,
          hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      let evs_ok := segCloneEvents recG st ++ (evs_td ++ evs_free)
      have hevs_ok : StageP3OkPrefixM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_ok :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_free, rfl, rfl,
          Or.inr ⟨evs_td, evs_free, rfl, htd_evs, hevs_free⟩⟩
      have hstep_ok : M.stepEvents evs_free st_td = M.stepEvents evs_ok st_b := by
        dsimp only [st_td, st_clone, evs_ok]
        rw [M.stepEvents_append (segCloneEvents recG st) (evs_td ++ evs_free) st_b,
            M.stepEvents_append evs_td evs_free (M.stepEvents (segCloneEvents recG st) st_b)]
      rw [hstep_ok] at hPs'
      refine hOk G₁ G' pt ptCap ptPtr evs_ok s' _ hver hclone_rel hdec_true hevs_ok hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      unfold stageP3DispatchOkMidPrev1Placed
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP3DispatchOkMidPrev1Placed
      rw [hlog, hstack_set]
      have hlive_s' :
          (if ptCap = 0#64 then emp
           else (A.atState lim (M.stepEvents evs_ok st_b) s').live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) =
          (if ptCap = 0#64 then emp
           else A.live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := rfl
      have hss_s' :
          sessionStateAt (A.atState lim (M.stepEvents evs_ok st_b) s') (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hprev_s' :
          prevVecAt (A.atState lim (M.stepEvents evs_ok st_b) s') (coroPtr + 0xe0#64) prevCap
            prevPtr [enc] =
          prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] := rfl
      have hpool_s' :
          (A.atState lim (M.stepEvents evs_ok st_b) s').pool =
          A.pool lim (M.stepEvents evs_ok st_b) s' := rfl
      rw [hlive_s', hss_s', hprev_s', hpool_s']
      exact Entails.trans (sepConj_mono_left hPs')
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    exact stageP3Gen_prev1_ver_ne_branch_placed ext C K hVerNeAt st_b
      s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
      recG st rem loc msgG msg F_frame Q
      hfits hinit_ne hcap_nz hEnc hst_ver4 hver hsp_align hsp_root hx29_s
      hcro1 hpc1 hrun1 htr1 hvregs1 hVerNe

theorem stageP3Gen_prev1_vregs_at_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop} :
    StageP3Prev1VRegsM3PlacedStmt A lim PrevEncOK tdEnv verNeEnv :=
  stageP3Gen_prev1_vregs_at_placed_ok_of_clone cloneGen_vregs_placed_ok

/-! ## `LibsignalFrozen` / `[LibsignalFullPlacement]` Variants -/

/-- Budget-threaded `[LibsignalFullPlacement]` version-mismatch exit body at
`dpClosureEntryM3Placed + 0x1e04` taking `LibsignalFrozen`. -/
abbrev OverVerNe1e04CliAtFrozenPlacedBody [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PrevEncOK : List (BitVec 8) → Prop)
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st_init : M.σ) (s0 s s1 : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64),
    initErrsPtr ≠ 0#64 → prevCap ≠ 0#64 →
    ∀ (msgVer : BitVec 32), msgVer ≠ 4#32 →
    ∀ (b_2c0 : BitVec 8) (enc : List (BitVec 8)),
      PrevEncOK enc →
      FitsEnv M lim st_init (verNeEnv enc) →
    ∀ (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8))),
      st.version = 4#32 → rootStack ≤ s.sp.toNat →
      CryptoVerification.LibsignalFrozen lsmpl s1.mem →
      s1.pc = dpClosureEntryM3Placed + 0x1e04#64 →
      s1.status = .Running → s1.sp = s.sp → (s.sp &&& 15#64 == 0#64) = true → s1.trace = s0.trace →
      s1.readReg64 .x9 = msgVer.setWidth 64 → s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 → s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x29 = s.sp + 0xc70#64 →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
        (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
         ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
         ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
         memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
         memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
         sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
         sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
         prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
         lsLogOff ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
         memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
         decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
         A.pool lim st_init s1 ∗ stackAt s.sp rootStack)
        (fun sf P_f =>
          (∃ (wd0 : BitVec 64) (evs : List AllocEvent),
            verNeEnv enc evs ∧
            (P_f ⊢
              ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
              ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
              memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
              memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
              stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs st_init) s0 s sf coroPtr outPtr
                (.invalidMessage .preKey .decryptionFailed))) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
        (fun _ _ => False)

theorem OverVerNe1e04CliAtFrozenPlacedBody.mono_prevEncOK [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P Q : List (BitVec 8) → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hpq : ∀ enc, P enc → Q enc)
    (h : OverVerNe1e04CliAtFrozenPlacedBody A lim Q verNeEnv ext) :
    OverVerNe1e04CliAtFrozenPlacedBody A lim P verNeEnv ext :=
  fun st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
    hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc hEnc hfits =>
    h st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
      hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc (hpq enc hEnc) hfits

theorem overVerNe1e04CliAtFrozenPlacedBody_of_frozen_placed_at [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    (hEncImp : ∀ enc, PrevEncOK enc → OverPrevEncOK enc)
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (verNeMemcpyStackSpec allocHookStack))
    (hPrevDec : OverPrevDecodeCroPlacedAt A lim ext) :
    OverVerNe1e04CliAtFrozenPlacedBody A lim PrevEncOK VerNeTopEnv ext :=
  OverVerNe1e04CliAtFrozenPlacedBody.mono_prevEncOK hEncImp
    (fun st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
        hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
        hver4 hsp_root hfr1 hpc1 hrun1 hs1_sp hsp_align htr1
        hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 =>
      sepWPp_weaken_post_false
        (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudget.overVerNe_1e04_frozen_placed_at ext hGrow hDropSS3
          hshim halloc hdealloc hmemcpy hPrevDec
          st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
          hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
          hver4 hsp_root hfr1 hpc1 hrun1 hs1_sp hsp_align htr1
          hx9_1 hx19_1 hx24_1 hx27_1 hx29_1)
        (fun _ _ ⟨hpost, hsp, htr, hcc, hcro, _, hvregs⟩ =>
          ⟨hpost, hsp, htr, hcc, hcro, hvregs⟩))

theorem overVerNe1e04CliAtFrozenPlacedBody_of_alloc_bm6w_chain5 [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    (hEncImp : ∀ enc, PrevEncOK enc → OverPrevEncOK enc)
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (sessionMemcpyBudgetSpec allocHookStack))
    (hAlloc : AllocContractsPlaced M A lim ext)
    (hBM6W : BytesMerge6Placed514OkExtW A lim ext)
    (hChain5 : ChainMerge5CroPlacedOkExt A lim ext) :
    OverVerNe1e04CliAtFrozenPlacedBody A lim PrevEncOK VerNeTopEnv ext :=
  OverVerNe1e04CliAtFrozenPlacedBody.mono_prevEncOK hEncImp
    (fun st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
        hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
        hver4 hsp_root hfr1 hpc1 hrun1 hs1_sp hsp_align htr1
        hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 =>
      sepWPp_weaken_post_false
        (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudget.overVerNe_1e04_frozen_placed_of_alloc_bm6w_chain5 ext hGrow hDropSS3
          hshim halloc hdealloc hmemcpy hAlloc hBM6W hChain5
          st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
          hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
          hver4 hsp_root hfr1 hpc1 hrun1 hs1_sp hsp_align htr1
          hx9_1 hx19_1 hx24_1 hx27_1 hx29_1)
        (fun _ _ ⟨hpost, hsp, htr, hcc, hcro, _, hvregs⟩ =>
          ⟨hpost, hsp, htr, hcc, hcro, hvregs⟩))

theorem overVerNe1e04CliAtFrozenPlacedBody_of_hooks_chain5 [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    (hEncImp : ∀ enc, PrevEncOK enc → OverPrevEncOK enc)
    (ext : LibsignalHooks)
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hshim_sat : HookSat ext lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc_sat : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_sat : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc_sat : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc_sat : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hmemmove_sat : HookSat ext "memmove" (sessionMemmoveBudgetSpec extHookStack))
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked)
    (hChain5 : ChainMerge5CroPlacedOkExt A lim ext) :
    OverVerNe1e04CliAtFrozenPlacedBody A lim PrevEncOK VerNeTopEnv ext :=
  OverVerNe1e04CliAtFrozenPlacedBody.mono_prevEncOK hEncImp
    (fun st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
        hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
        hver4 hsp_root hfr1 hpc1 hrun1 hs1_sp hsp_align htr1
        hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 =>
      sepWPp_weaken_post_false
        (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudget.overVerNe_1e04_frozen_placed_of_hooks_chain5 ext hGrow hDropSS3
          hshim_sat halloc_sat hrealloc_sat hdealloc_sat hmc_sat hmemmove_sat hpanic_raw hChain5
          st_init s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
          hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc hfits G₁ recG st
          hver4 hsp_root hfr1 hpc1 hrun1 hs1_sp hsp_align htr1
          hx9_1 hx19_1 hx24_1 hx27_1 hx29_1)
        (fun _ _ ⟨hpost, hsp, htr, hcc, hcro, _, hvregs⟩ =>
          ⟨hpost, hsp, htr, hcc, hcro, hvregs⟩))

/-- Budget-threaded `[LibsignalFullPlacement]` Stage P3 specification (`+0x1778 → +0x34dc` or
`s0.readReg64 .x30`) over a 1-element `prevVecAt [enc]`. -/
def StageP3Prev1VRegsM3FrozenPlacedStmt [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PrevEncOK : List (BitVec 8) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop) : Prop :=
  ∀ (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : MlKem),
    subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ChainClone3OkPlaced A lim ext →
    SenderChainClone3OkPlaced A lim ext →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv)) →
    OverVerNe1e04CliAtFrozenPlacedBody A lim PrevEncOK verNeEnv ext →
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8) (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b
        (StageP3Prev1Env tdEnv verNeEnv recG st rem loc msgG msg msgVer enc rest) →
      initErrsPtr ≠ 0#64 → prevCap ≠ 0#64 → PrevEncOK enc → st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      CryptoVerification.LibsignalFrozen lsmpl s.mem →
      s.pc = dpClosureEntryM3Placed + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (evs_ok : List AllocEvent) (s' : State) (P_s' : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_ok →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        Steps (lsProg_518 ext) s s' → s'.pc = dpClosureEntryM3Placed + 0x34dc#64 →
        s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrev1Placed A lim (M.stepEvents evs_ok st_b) s0 s s'
            coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr enc pt b_2c0 G'
            (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (evs_err : List AllocEvent)
          (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        StageP3ErrM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_err →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_err st_b) s0 s sf coroPtr
            outPtr e ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_vn : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNePrev1Env verNeEnv recG st enc evs_vn →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_vn st_b) s0 s sf coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
        (LsTokenInitM3 ∗
          genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          overScratch s.sp ∗ F_frame)
        Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)

set_option maxHeartbeats 1200000 in
private theorem stageP3Gen_prev1_ver_ne_branch_full_placed [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (C : Crypto) (K : MlKem)
    (hVerNeAt : OverVerNe1e04CliAtFrozenPlacedBody A lim PrevEncOK verNeEnv ext)
    (st_b : M.σ) (s0 s s1 : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8) (enc rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop)
    (hfits : FitsEnv M lim st_b
      (StageP3Prev1Env tdEnv verNeEnv recG st rem loc msgG msg msgVer enc rest))
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap_nz : prevCap ≠ 0#64)
    (hEnc : PrevEncOK enc) (hst_ver4 : st.version = 4#32) (hver : st.version ≠ msgVer)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (hx29_s : s.readReg64 .x29 = s.sp + 0xc70#64)
    (hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem)
    (hpc1 : s1.pc = dpClosureEntryM3Placed + 0x1e04#64)
    (hrun1 : s1.status = .Running) (htr1 : s1.trace = s0.trace)
    (hvregs1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hVerNe : ∀ (evs_vn : List AllocEvent) (sf : State) (P_f : SepProp),
      st.version ≠ msgVer →
      StageP3VerNePrev1Env verNeEnv recG st enc evs_vn →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_vn st_b) s0 s sf coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed) ∗
        genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAtPlaced cur rest) ∗
        overScratch s.sp) →
      sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      Q sf (P_f ∗ F_frame)) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      ((CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostNePlaced
          (A.atState lim (M.stepEvents (segCloneEvents recG st) st_b) s1)
          s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
        (LsTokenInitM3 ∗
          stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          overScratch s.sp)) ∗ F_frame)
      Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0) := by
  have hmsgVer_ne4 : msgVer ≠ 4#32 := fun h => hver (hst_ver4.trans h.symm)
  apply sepWPp_lift_false_qp
  apply sepWPp_frame_false_qp
  unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostNePlaced
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
    stageP3Sub5ExtraPrePrev1
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1⟩ => ?_
  have hx29_1' : s1.readReg64 .x29 = s.sp + 0xc70#64 := hx29_1.trans hx29_s
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun G₁ => ?_
  refine sepWPp_weaken_frame
    (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun _ => ?_
  set st_clone := M.stepEvents (segCloneEvents recG st) st_b
  have hfits_vn : FitsEnv M lim st_clone (verNeEnv enc) :=
    fitsEnv_verNe_of_stageP3Prev1Env hver hfits
  have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
  have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
      sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
  have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
      protocolAddressAt A.repAlloc rem remAddrPtr := rfl
  have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
      protocolAddressAt A.repAlloc loc locAddrPtr := rfl
  have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
      signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
  have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
  simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
  refine sepWPp_weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus) ?_
  unfold genP3S5SpillRem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun wFront => ?_
  refine sepWPp_weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_
  have hver_ne := hVerNeAt st_clone
    s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr wFront.ud0
    hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc hEnc hfits_vn G₁ recG st
    hst_ver4 hsp_root hfr1 hpc1 hrun1 hs1_sp hsp_align htr1
    hx9_1 hx19_1 hx24_1 hx27_1 hx29_1'
  refine ret_sepWPp_frame_false hver_ne (by sep_focus)
    fun sf _ _ _ ⟨⟨wd0, evs_vn, hvn_evs, hent_f⟩, hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
  let evs_vn_tot := segCloneEvents recG st ++ evs_vn
  have hevs_vn_tot : StageP3VerNePrev1Env verNeEnv recG st enc evs_vn_tot :=
    Or.inr ⟨segCloneEvents recG st, evs_vn, rfl, rfl, hvn_evs⟩
  have hstep_vn : M.stepEvents evs_vn st_clone = M.stepEvents evs_vn_tot st_b := by
    dsimp only [st_clone, evs_vn_tot]
    rw [M.stepEvents_append (segCloneEvents recG st) evs_vn st_b]
  rw [hstep_vn] at hent_f
  refine hVerNe evs_vn_tot sf _ hver hevs_vn_tot ?_ hspf htrf hcc_f
    (hvregsf_1.trans hvregs1) hcrof
  unfold genP3S5PostFramePlaced
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3S5PostFramePlaced
    genP3S5SpillRem
  have hwFront_repack :
      ((s.sp + 0x48#64) ↦₆₄ wFront.u48) ∗ ((s.sp + 0x50#64) ↦₆₄ wFront.u50) ∗
      ((s.sp + 0x5c#64) ↦₃₂ wFront.u5c) ∗ ((s.sp + 0x7c#64) ↦₃₂ wFront.u7c) ∗
      ((s.sp + 0x98#64) ↦₆₄ wFront.u98) ∗ ((s.sp + 0xd0#64) ↦₆₄ wd0) ⊢
      ∃∗ w : GenP3S5FrontRem,
        ((s.sp + 0x48#64) ↦₆₄ w.u48) ∗ ((s.sp + 0x50#64) ↦₆₄ w.u50) ∗
        ((s.sp + 0x5c#64) ↦₃₂ w.u5c) ∗ ((s.sp + 0x7c#64) ↦₃₂ w.u7c) ∗
        ((s.sp + 0x98#64) ↦₆₄ w.u98) ∗ ((s.sp + 0xd0#64) ↦₆₄ w.ud0) :=
    Entails.sepExists_right ⟨wFront.u48, wFront.u50, wFront.u98, wd0, wFront.u5c, wFront.u7c⟩
      (Entails.refl _)
  exact Entails.trans (sepConj_mono_left hent_f)
    (entails_replace_sub hwFront_repack (by sep_focus) (eq_of_sep_emp (by sep_focus)))

set_option maxHeartbeats 1200000 in
theorem stageP3Gen_prev1_vregs_at_full_placed_ok_of_clone [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hClone : CloneGenVRegsPlacedStmt) :
    StageP3Prev1VRegsM3FrozenPlacedStmt A lim PrevEncOK tdEnv verNeEnv := by
  intro ext C ctl K hshim halloc hdealloc hmemcpy hGrow hSetState hDropSS3
    hcc hscc hroot hVerNeAt st_b s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg F_frame Q
    hfits hinit_ne hcap_nz hEnc hst_ver4 hnot_self hseeds hrc_lt hpq_lt
    hfr hpc hrun hsp_align hsp_root hx29_s htr hvregs hOk hErr hVerNe
  have hcro : LibsignalCodeRoLoaded lsmpl s.mem := LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.lscro_of_frozen hfr
  have hfits_clone := fitsEnv_segClone_of_stageP3Prev1Env hfits
  refine stageP3_clone_prev1_vregs_prefix_placed_steps hClone C K ext
    hshim halloc hmemcpy hcc hscc st_b
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur enc msgVer b_2c0 rest
    recG st rem loc msgG msg F_frame Q hfits_clone hrc_lt hcro hpc hrun hsp_align hsp_root
    htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  have hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem := CryptoVerification.libsignalFrozen_of_keepsFrozen hfr hsteps01.keepsFrozen
  refine SepWPp.weaken_pre hent1 ?_
  refine SepWPp.weaken_pre
    (P' := (genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b)
        s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
          enc b_2c0 ∗
        overScratch s.sp)) ∗ F_frame)
    (Entails.of_eq (by ac_rfl)) ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostEqPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine sepWPp_weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun hclone_rel => ?_
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_td : FitsEnv M lim st_clone
        (tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)) :=
      fitsEnv_td_of_stageP3Prev1Env hver hclone_rel hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 _ Q _
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    let F_dec : SepProp :=
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc
        b_2c0 ∗
      overScratch s.sp
    refine SepWPp.weaken_pre
      (P' := (LsTokenInitM3 ∗
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A.repAlloc rem remAddrPtr ∗
        protocolAddressAt A.repAlloc loc locAddrPtr ∗
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
        memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗
        lsLogOff ∗
        stackAt s.sp rootStack ∗
        A.pool lim st_clone s1) ∗ (F_dec ∗ F_frame))
      (Entails.of_eq (eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K tdEnv hroot st_clone
      s0 s s1 coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hfits_td hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' evs_td hsteps12 htd_evs hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2
          hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    have hfr2 : CryptoVerification.LibsignalFrozen lsmpl s2.mem := CryptoVerification.libsignalFrozen_of_keepsFrozen hfr hsteps02.keepsFrozen
    let st_td := M.stepEvents evs_td st_clone
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left
          (postTryDecrypt_entails_s5DispatchPrev1_placed A lim st_td s0 s s2
            coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
            remAddrPtr locAddrPtr whisperMsgPtr enc msgVer b_2c0
            (genP3S5Model C K rem loc msg rest st).1 G' recG
            (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    have hlog : (lsLogFilterAddr ↦₆₄ 0#64) = lsLogOff := rfl
    unfold stageP3DispatchPrePrev1Placed
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP3DispatchPrePrev1Placed
    rw [hlog]
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hfits_post : FitsEnv M lim st_td FromVPostTdEnv :=
        fitsEnv_postTd_of_stageP3Prev1Env hver hclone_rel htd_evs hfits
      have herr := LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1ErrPlacedBudget.stageP3_sub5_err_prev1_full_placed_ok ext hshim halloc hdealloc hGrow hDropSS3
        st_td s0 s2 coroPtr outPtr initErrsPtr prevCap prevPtr
        hfits_post hinit_ne e he_npan b_2c0 enc G' recG
        (genP3S5Model C K rem loc msg rest st).2 st
        hfr2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrev1Placed
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP3ErrPrePrev1Placed at herr
      have herr_post : ∀ st_e sf,
          stageP3ErrPostPrevEmptyM3Placed A lim st_e s0 s2 sf coroPtr outPtr e =
            stageP3ErrPostPrevEmptyM3Placed A lim st_e s0 s sf coroPtr outPtr e := by
        intro st_e sf
        unfold stageP3ErrPostPrevEmptyM3Placed
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyM3Placed
        rw [hs2_sp]
      simp only [herr_post, hs2_sp] at herr
      apply sepWPp_lift_false_qp
      apply sepWPp_frame_false_qp
      refine ret_sepWPp_frame_false herr (by sep_focus)
        fun sf _ _ _ ⟨evs_err, herr_evs, hPf_err, hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      let evs_tot := segCloneEvents recG st ++ (evs_td ++ evs_err)
      have hevs_tot : StageP3ErrM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_tot :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_err, rfl, rfl,
          Or.inr ⟨evs_td, evs_err, rfl, htd_evs, herr_evs⟩⟩
      have hstep_tot : M.stepEvents evs_err st_td = M.stepEvents evs_tot st_b := by
        dsimp only [st_td, st_clone, evs_tot]
        rw [M.stepEvents_append (segCloneEvents recG st) (evs_td ++ evs_err) st_b,
            M.stepEvents_append evs_td evs_err (M.stepEvents (segCloneEvents recG st) st_b)]
      rw [hstep_tot] at hPf_err
      refine hErr G₁ G' e evs_tot sf _ hver hclone_rel hdec_false hevs_tot hres he_npan ?_
        hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      exact Entails.trans (sepConj_mono_left hPf_err)
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hstack_set :
          stackAt s.sp growOneSpeStack =
            memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hvec_eq_s2 :
          vecResultAt (A.atState lim st_td s2) (s.sp + 0x270#64) (.ok pt) =
          vecResultAt A.repAlloc (s.sp + 0x270#64) (.ok pt) := rfl
      have hss_g_eq_s2 :
          sessionStateAt (A.atState lim st_td s2) (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hss_rec_eq_s2 :
          sessionStateAt (A.atState lim st_td s2) (coroPtr + 0xf8#64) recG st =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
      have hprev_eq_s2 :
          prevVecAt (A.atState lim st_td s2) (coroPtr + 0xe0#64) prevCap prevPtr [enc] =
          prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] := rfl
      have hpool_eq_s2 : (A.atState lim st_td s2).pool = A.pool lim st_td s2 := rfl
      simp only [hvec_eq_s2, hss_g_eq_s2, hss_rec_eq_s2, hprev_eq_s2, hpool_eq_s2]
      have hok := stageP3_sub5_decResult_placed_ok ext hmemcpy hSetState st_td
        s0 s2 coroPtr outPtr pt G' recG
        (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_false_steps_framed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨evs_free, ptCap, ptPtr, hevs_free,
          hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      let evs_ok := segCloneEvents recG st ++ (evs_td ++ evs_free)
      have hevs_ok : StageP3OkPrefixM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_ok :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_free, rfl, rfl,
          Or.inr ⟨evs_td, evs_free, rfl, htd_evs, hevs_free⟩⟩
      have hstep_ok : M.stepEvents evs_free st_td = M.stepEvents evs_ok st_b := by
        dsimp only [st_td, st_clone, evs_ok]
        rw [M.stepEvents_append (segCloneEvents recG st) (evs_td ++ evs_free) st_b,
            M.stepEvents_append evs_td evs_free (M.stepEvents (segCloneEvents recG st) st_b)]
      rw [hstep_ok] at hPs'
      refine hOk G₁ G' pt ptCap ptPtr evs_ok s' _ hver hclone_rel hdec_true hevs_ok hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      unfold stageP3DispatchOkMidPrev1Placed
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP3DispatchOkMidPrev1Placed
      rw [hlog, hstack_set]
      have hlive_s' :
          (if ptCap = 0#64 then emp
           else (A.atState lim (M.stepEvents evs_ok st_b) s').live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) =
          (if ptCap = 0#64 then emp
           else A.live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := rfl
      have hss_s' :
          sessionStateAt (A.atState lim (M.stepEvents evs_ok st_b) s') (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hprev_s' :
          prevVecAt (A.atState lim (M.stepEvents evs_ok st_b) s') (coroPtr + 0xe0#64) prevCap
            prevPtr [enc] =
          prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] := rfl
      have hpool_s' :
          (A.atState lim (M.stepEvents evs_ok st_b) s').pool =
          A.pool lim (M.stepEvents evs_ok st_b) s' := rfl
      rw [hlive_s', hss_s', hprev_s', hpool_s']
      exact Entails.trans (sepConj_mono_left hPs')
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    exact stageP3Gen_prev1_ver_ne_branch_full_placed ext C K hVerNeAt st_b
      s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
      recG st rem loc msgG msg F_frame Q
      hfits hinit_ne hcap_nz hEnc hst_ver4 hver hsp_align hsp_root hx29_s
      hfr1 hpc1 hrun1 htr1 hvregs1 hVerNe

theorem stageP3Gen_prev1_vregs_at_full_placed_ok [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PrevEncOK : List (BitVec 8) → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop} :
    StageP3Prev1VRegsM3FrozenPlacedStmt A lim PrevEncOK tdEnv verNeEnv :=
  stageP3Gen_prev1_vregs_at_full_placed_ok_of_clone cloneGen_vregs_placed_ok

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget

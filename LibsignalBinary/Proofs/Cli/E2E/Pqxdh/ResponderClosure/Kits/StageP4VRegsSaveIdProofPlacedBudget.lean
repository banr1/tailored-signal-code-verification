/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwindPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProofPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveId
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4SaveIdPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP4
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P4.1 Dispatch Proof: `save_identity`

Budget-threaded `[LibsignalPlacement]` Substage P4.1 dispatch proof on Block `518`
(`lsProg_518 ext`), threading `A.pool` across `SaveStepEnv` on `Ok c` (`→ kyberMarkUsedShimAddr`)
and `StageP4MatchedSaveErrEnv` on `Err ()` (`→ s0.readReg64 .x30`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProofPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding IdentityStoreKitPlacedOkI
  kitSaveShimSpec kitSavePollPlacedSpec kitSavePollPlacedSpecE kitSavePollPlacedSpecI
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity hiding kitSaveShimSpec
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  saveIdVtablesAt_placed_intro savePollPlacedErr_unpack_repack
)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv SaveStepEnv kitSaveShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI kitSavePollPlacedSpec kitSavePollPlacedSpecE kitSavePollPlacedSpecI
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlacedBudget (
  bind_sepWP_steps_frame_placed call_rocl_entails_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwindPlacedBudget (
  stageP4_err_unwind_550_vregs_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdPlacedBudget (
  p4_seg1a_vregs_placed_wp p4_seg1b_vregs_placed_wp p4_seg1c_gen_vregs_placed_wp
  p4_seg1d_err_vregs_placed_wp p4_seg1d_ok_vregs_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget (
  StageP4MatchedSaveErrEnv
)

private theorem sepWPp_intro_ro {prog : Program} {ret : BitVec 64} {s : State}
    {R_ro P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : ∀ {R : SepProp}, s.mem ⊨ P ∗ R → s.mem ⊨ R_ro ∗ (P ∗ R))
    (h : SepWPp prog ret s (R_ro ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (R_ro ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact hro hm
  exact h R hm' hL

private theorem saveShim_pre_intro_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {s : State} {sp self addrA keyA : BitVec 64}
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = self)
    (hx1 : s.readReg64 .x1 = addrA)
    (hx2 : s.readReg64 .x2 = keyA)
    (hfits : FitsEnv M lim st (BoxAllocEnv ikit.saveBoxSize)) :
    A.pool lim st s ∗ stackAt sp ikit.saveShimStack ⊢
      (kitSaveShimSpec M A lim ikit).pre
        (({ self := self, addrA := addrA, keyA := keyA } : IdentityShimCall), st) s := by
  dsimp only [kitSaveShimSpec]
  rw [hsp]
  exact Entails.pure_right ⟨hx0, hx1, hx2, hfits⟩ (Entails.refl _)

private theorem savePoll_pre_intro_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {s : State} {sp fut self addrA keyA : BitVec 64}
    {peer : AddrGhost} {remoteIk : IdentityKey}
    (henv : ikit.envOk s.fs.files)
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = fut)
    (hx8 : s.readReg64 .x8 = sp + 0x3e0#64)
    (haddr : ikit.addrOk peer.val)
    (hfits : FitsEnv M lim st (ikitEnv.savePollEnv ist0 peer.val remoteIk)) :
    ikit.saveBoxAt fut self addrA keyA 0#8 ∗
      ikit.identityAt self ist0 ∗
      memRegion (sp + 0x3e0#64) 48 ∗
      protocolAddressAt A.repAlloc peer addrA ∗
      (keyA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
      A.pool lim st s ∗
      stackAt sp ikit.savePollStack ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ⊢
      (kitSavePollPlacedSpecI M A lim ikit ikitEnv).pre
        (({ fut := fut, out := sp + 0x3e0#64,
            call := { addrA := addrA, addr := peer, keyA := keyA, key := remoteIk } }
            : IdentityPollCall),
          self, ist0, st) s := by
  dsimp only [kitSavePollPlacedSpecI, StoreKit.withLsLogOff,
    kitSavePollPlacedSpecE, withEnvPre, kitSavePollPlacedSpec, FromRecordCallees.lsLogOff]
  rw [hsp]
  have h1 :
      ikit.saveBoxAt fut self addrA keyA 0#8 ∗
        ikit.identityAt self ist0 ∗
        memRegion (sp + 0x3e0#64) 48 ∗
        protocolAddressAt A.repAlloc peer addrA ∗
        (keyA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
        A.pool lim st s ∗
        stackAt sp ikit.savePollStack ⊢
      ⌜ikit.envOk s.fs.files⌝ ∗
        (⌜s.readReg64 .x0 = fut ∧ s.readReg64 .x8 = sp + 0x3e0#64 ∧ ikit.addrOk peer.val ∧
            FitsEnv M lim st (ikitEnv.savePollEnv ist0 peer.val remoteIk)⌝ ∗
          ikit.saveBoxAt fut self addrA keyA 0#8 ∗
          ikit.identityAt self ist0 ∗
          memRegion (sp + 0x3e0#64) 48 ∗
          protocolAddressAt A.repAlloc peer addrA ∗
          (keyA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
          A.pool lim st s ∗
          stackAt sp ikit.savePollStack) :=
    Entails.pure_right henv (Entails.pure_right ⟨hx0, hx8, haddr, hfits⟩ (Entails.refl _))
  simpa only [sepConj_assoc] using sepConj_mono_left (Q := lsLogFilterAddr ↦₆₄ 0#64) h1

/-! ## Spatial bundles for Substage P4.1 -/

/-- Resources shared unchanged across the entry, `Ok c` exit, and `Err ()` exit of Placed
Substage P4.1, separating the stack-frame anchor `s` from the pool state `s_pool`. -/
def stageP4SaveIdSharedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (s0 s s_pool : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr kyberStoreVt prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) : SepProp :=
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0xa0#64) ↦₆₄ ikit.id_vt) ∗
  ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0xd0#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
  memRegion (s.sp + 0x250#64) 20 ∗
  ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
  ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x2b0#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
  (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool lim st s_pool ∗
  stackAt s.sp (saveIdCallStack ikit)

/-- Spatial precondition of Placed Substage P4.1 at `(blkPl_518).base + 0x34dc`. -/
def stageP4SaveIdPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr kyberStoreVt prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (ist0 : ikit.IdState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  stageP4SaveIdSharedPlaced A lim st0 ikit s0 s s coroPtr msgPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr kyberStoreVt prevStatesPtr ptCap ptPtr v_3d0 pt peer remoteIk ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ssSt ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist0

/-- Spatial postcondition of Placed Substage P4.1 on `Ok c` at `kyberMarkUsedShimAddr`. -/
def stageP4SaveIdOkPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st1 : M.σ)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (s0 s s1 : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (ist0 : ikit.IdState) (c : IdentityChange)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  stageP4SaveIdSharedPlaced A lim st1 ikit s0 s s1 coroPtr msgPtr remoteAddrPtr remoteIkPtr
    idStorePtr kyberStorePtr kyberStoreVt prevStatesPtr ptCap ptPtr v_3d0 pt peer remoteIk ∗
  saveIdVtablesAt ikit ∗
  ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr) ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ssSt ∗
  ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
  ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
  ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  ((coroPtr + 0x298#64) ↦₆₄ (opkId ++ opkIdIsSome)) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
  ((coroPtr + 0x2ac#64) ↦₃₂ opkIdIsSome) ∗
  ((coroPtr + 0x2b0#64) ↦₃₂ opkId) ∗
  ((coroPtr + 0x2b4#64) ↦₃₂ 1#32) ∗
  ((coroPtr + 0x2b8#64) ↦₃₂ kyberPreKeyId) ∗
  ((coroPtr + 0x2bc#64) ↦₃₂ signedPreKeyId) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))

/-- Spatial postcondition of Placed Substage P4.1 on `Err ()` at closure return `s0.readReg64 .x30`. -/
def stageP4SaveIdErrPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (s0 s sf : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (ist0 : ikit.IdState) : SepProp :=
  stageP4SaveIdSharedPlaced A lim stf ikit s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr
    idStorePtr kyberStorePtr kyberStoreVt prevStatesPtr ptCap ptPtr v_3d0 pt peer remoteIk ∗
  saveIdVtablesAt ikit ∗
  ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr) ∗
  savePollPlacedOutAt outPtr (.error ()) ∗
  memRegion (coroPtr + 0xf8#64) 344 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x298#64) ↦₃₂ opkIdIsSome) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkId) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr (ikit.saveUpdate ist0 peer.val remoteIk (.error ()))

/-! ## Budget-threaded Substage P4.1 dispatch proof -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalPlacement]` Substage P4.1 (`(blkPl_518).base + 0x34dc →
kyberMarkUsedShimAddr` / `x30`) preserving `calleeSavedVRegs`. -/
theorem stageP4_saveIdentity_dispatch_vregs_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (ikitEnv : IdentityStoreBudgetEnv ikit)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hikit : IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext)
    (hiVt : IdentityVtablesPlacedOk ikit)
    {Qfs : Prop} {Qp : State → SepProp → Prop}
    (st0 : M.σ) (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
     kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (ist0 : ikit.IdState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (haddrOk : ikit.addrOk peer.val)
    (hfits : FitsEnv M lim st0 (SaveStepEnv ikit ikitEnv ist0 peer.val remoteIk))
    (hopk_ne2 : opkIdIsSome - 2#32 ≠ 0#32)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : saveIdCallStack ikit ≤ 2 ^ 64)
    (hkSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      m ⊨ ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr) ∗ P)
    (hfs : FsAt ikit.envOk Qfs (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (c : IdentityChange) (evs : List AllocEvent) (s1 : State) (P1 : SepProp),
      SaveStepEnv ikit ikitEnv ist0 peer.val remoteIk evs →
      Steps (lsProg_518 ext) s s1 →
      ikit.saveRel ist0 peer.val remoteIk (.ok c) →
      s1.pc = kyberMarkUsedShimAddr →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) →
      s1.readReg64 .x0 = kyberStorePtr →
      s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 →
      s1.readReg64 .x2 = signedPreKeyId.zeroExtend 64 →
      s1.readReg64 .x3 = msgPtr + 0xa8#64 →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x25 = s.sp + 0x210#64 →
      s1.readReg64 .x26 = outPtr →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x28 = 0xfffffffffffffffe#64 →
      s1.readReg64 .x30 = (blkPl_518).base + 0x350#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢ stageP4SaveIdOkPostPlaced A lim (M.stepEvents evs st0) ikit s0 s s1 coroPtr msgPtr
        outPtr remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr kyberStoreVt
        kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 c G ssSt ∗ F) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q Qp)
    (hErr : ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4MatchedSaveErrEnv ikit ikitEnv ist0 peer.val remoteIk evs →
      Steps (lsProg_518 ext) s sf →
      ikit.saveRel ist0 peer.val remoteIk (.error ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4SaveIdErrPostPlaced A lim (M.stepEvents evs st0) ikit s0 s sf coroPtr msgPtr
        outPtr remoteAddrPtr remoteIkPtr idStorePtr kyberStorePtr kyberStoreVt
        kyberMarkUsedShimAddr prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId pt peer remoteIk ist0 ∗ F) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4SaveIdPrePlaced A lim st0 ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
        idStorePtr kyberStorePtr kyberStoreVt prevStatesPtr ptCap ptPtr v_3d0
        opkIdIsSome opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G ssSt ∗ F)
      Q Qp := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  have hbox_eq : ikit.saveBoxSize = (BitVec.ofNat 64 ikit.saveBoxSize).toNat :=
    (Nat.mod_eq_of_lt ikit.saveBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  refine sepWPp_intro_ro
    (R_ro := saveIdVtablesAt ikit ∗ ((kyberStoreVt + 0x28#64) ↦₆₄ᵣ kyberMarkUsedShimAddr))
    (fun hm => by rw [sepConj_assoc]; exact saveIdVtablesAt_placed_intro hiVt hcro.2 (hkSlot hcro.2 hm)) ?_
  unfold stageP4SaveIdPrePlaced stageP4SaveIdSharedPlaced saveIdVtablesAt
  simp only [sepConj_assoc]
  let ptLen := BitVec.ofNat 64 pt.length
  have hpt_sp :
      ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗ ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
      ((s.sp + 0x288#64) ↦₆₄ ptLen) =
      ((s.sp + 0x278#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((s.sp + 0x27c#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((s.sp + 0x284#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((s.sp + 0x28c#64) ↦₃₂ ptLen.extractLsb' 32 32) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      words3_eq_head_mid_tail (s.sp + 0x278#64) ptCap ptPtr ptLen
  have hpt_coro :
      ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗ ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
      ((coroPtr + 0x290#64) ↦₆₄ ptLen) =
      ((coroPtr + 0x280#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((coroPtr + 0x284#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((coroPtr + 0x28c#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((coroPtr + 0x294#64) ↦₃₂ ptLen.extractLsb' 32 32) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      words3_eq_head_mid_tail (coroPtr + 0x280#64) ptCap ptPtr ptLen
  have h280_un :
      memRegion (coroPtr + 0x280#64) 24 =
      ∃∗ u3 : BitVec 32, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 32,
        ((coroPtr + 0x280#64) ↦₃₂ u0) ∗ ((coroPtr + 0x284#64) ↦₆₄ u1) ∗
        ((coroPtr + 0x28c#64) ↦₆₄ u2) ∗ ((coroPtr + 0x294#64) ↦₃₂ u3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion24_eq_unaligned_cells (coroPtr + 0x280#64)
  have h250_un :
      memRegion (s.sp + 0x250#64) 20 =
      ∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((s.sp + 0x250#64) ↦₆₄ u0) ∗ ((s.sp + 0x258#64) ↦₆₄ u1) ∗
        ((s.sp + 0x260#64) ↦₃₂ u2) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_eq_cells (s.sp + 0x250#64)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_sp) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq h280_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_coro294 => SepWPp.exists_elim fun u_coro28c =>
    SepWPp.exists_elim fun u_coro284 => SepWPp.exists_elim fun u_coro280 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq h250_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  have h1a := p4_seg1a_vregs_placed_wp (A := A) (lim := lim) ext st0 s coroPtr idStorePtr ikit.id_vt
    (0#64 + ikit.saveShimOff) remoteAddrPtr remoteIkPtr
    (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
    (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
    u_250 u_258 u_coro284 u_coro28c v_3d0
    (ptCap.extractLsb' 0 32) (ptLen.extractLsb' 32 32) u_260 u_coro280 u_coro294
    hpc hrun hsp_al hx19 hx25 hx28
  refine bind_sepWP_steps_frame_placed hcro h1a (by sep_focus)
    fun s1 hst1 hpc1 hrun1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1,
      hx19_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hlr1, hvregs1⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_coro.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_sp.symm) (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ ptLen.extractLsb' 32 32) ⊢ memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      cells20_entails_memRegion20 (s.sp + 0x250#64) _ _ _
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_al
  have hfs1 := hfs.of_steps_nil hst1 htr1
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_shim ikit s.sp hsp_ub))
    (by sep_focus) ?_
  have hfits_box : FitsEnv M lim st0 (BoxAllocEnv ikit.saveBoxSize) := hfits.seq_left
  refine call_rocl_entails_steps_frame_placed
    (spec := kitSaveShimSpec M A lim ikit)
    (x := (({ self := idStorePtr, addrA := remoteAddrPtr, keyA := remoteIkPtr } : IdentityShimCall), st0))
    (P_spec := A.pool lim st0 s1 ∗ stackAt s.sp ikit.saveShimStack)
    hcro1 (hikit.saveShim (by decide)) hpc1 hrun1 hsp1_al hlr1
    (saveShim_pre_intro_placed hsp1 hx0_1 hx1_1 hx2_1 hfits_box)
    (by sep_focus)
    (hnext := fun s2 hst2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 => ?_)
    (hpan_false := fun _ => by unfold kitSaveShimSpec; rfl)
    (hexit_false := fun _ _ => by unfold kitSaveShimSpec; rfl)
    (hoom_false := fun _ => by unfold kitSaveShimSpec; rfl)
  dsimp only [kitSaveShimSpec]
  rw [hsp1]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_shim => ?_
  refine SepWPp.pure_elim fun ⟨hx1_2, _, _, htr2_1, hevs_shim⟩ => ?_
  have hfits_after_shim := hfits.seq_right hevs_shim
  have hfits_poll :
      FitsEnv M lim (M.stepEvents evs_shim st0)
        (ikitEnv.savePollEnv ist0 peer.val remoteIk) :=
    hfits_after_shim.seq_left
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_shim ikit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hfs2 := hfs1.of_steps_nil hst2 htr2_1
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs_cs2⟩
  let saveIdFutPtr := s2.readReg64 .x0
  have h2c8_un :
      memRegion (coroPtr + 0x2c8#64) 16 =
      ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((coroPtr + 0x2c8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ u1) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion16_eq_cells (coroPtr + 0x2c8#64)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq h2c8_un) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0 => SepWPp.exists_elim fun u_2c8 => ?_
  have h1b := p4_seg1b_vregs_placed_wp (A := A) (lim := lim) ext (M.stepEvents evs_shim st0) s2
    coroPtr ctxPtr saveIdFutPtr (0#64 + ikit.saveFutVtOff) (0#64 + ikit.savePollOff) u_2c8 u_2d0
    hpc2 hrun2 rfl hx1_2 (hx19_cs2.trans hx19_1) (hx27_cs2.trans (hx27_1.trans hx27))
  refine bind_sepWP_steps_frame_placed hcro2 h1b (by sep_focus)
    fun s3 hst3 hpc3 hrun3 hcro3 ⟨hsp3_2, htr3_2, hx0_3, _, hx8_3,
      hx19_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _, hlr3, hvregs3_2⟩ => ?_
  have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
  have hsp3_al : s3.spAligned = true := by simpa [State.spAligned, hsp3] using hsp_al
  have hfs3 := hfs2.of_steps_nil hst3 htr3_2
  rw [hsp2] at hx8_3
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_poll ikit s.sp hsp_ub))
    (by sep_focus) ?_
  let pollCall : IdentityPollCall :=
    { fut := saveIdFutPtr
      out := s.sp + 0x3e0#64
      call := { addrA := remoteAddrPtr, addr := peer, keyA := remoteIkPtr, key := remoteIk } }
  refine call_rocl_entails_steps_frame_placed
    (spec := kitSavePollPlacedSpecI M A lim ikit ikitEnv)
    (x := (pollCall, idStorePtr, ist0, M.stepEvents evs_shim st0))
    (P_spec := ikit.saveBoxAt saveIdFutPtr idStorePtr remoteAddrPtr remoteIkPtr 0#8 ∗
          ikit.identityAt idStorePtr ist0 ∗ memRegion (s.sp + 0x3e0#64) 48 ∗
          protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
          (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
          A.pool lim (M.stepEvents evs_shim st0) s3 ∗
          stackAt s.sp ikit.savePollStack ∗ (lsLogFilterAddr ↦₆₄ 0#64))
    hcro3 (hikit.savePoll (by decide)) hpc3 hrun3 hsp3_al hlr3
    (savePoll_pre_intro_placed hfs3.envOk_here hsp3 hx0_3 hx8_3 haddrOk hfits_poll)
    (by sep_focus)
    (hnext := fun s4 hst4 hpc4 hrun4 hsp4_3 hsp4_al hcs4 hcro4 => ?_)
  dsimp only [kitSavePollPlacedSpecI, StoreKit.withLsLogOff, kitSavePollPlacedSpecE,
    withEnvPre, kitSavePollPlacedSpec, FromRecordCallees.lsLogOff, pollCall]
  rw [hsp3]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.exists_elim fun evs_poll => ?_
  refine SepWPp.pure_elim fun ⟨hrel, htr4_3, hevs_poll⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_poll ikit s.sp hsp_ub).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x2b0#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0s => SepWPp.exists_elim fun u_2c8s =>
    SepWPp.exists_elim fun u_2c0s => SepWPp.exists_elim fun u_2b8s =>
    SepWPp.exists_elim fun u_2b0s => ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  rcases hcs4 with ⟨hx19_cs4, _, _, _, _, hx24_cs4, hx25_cs4, hx26_cs4, hx27_cs4, hx28_cs4, _, hvregs_cs4⟩
  have hvregs_4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 :=
    hvregs_cs4.trans (hvregs3_2.trans (hvregs_cs2.trans (hvregs1.trans hvregs)))
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx24_4 : s4.readReg64 .x24 = s4.sp + 0x370#64 := by
    rw [hx24_cs4, hx24_3, hx24_cs2, hx24_1, hx24, hsp4]
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by
    rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1, hsp4]
  have hx26_4 : s4.readReg64 .x26 = outPtr :=
    hx26_cs4.trans (hx26_3.trans (hx26_cs2.trans (hx26_1.trans hx26)))
  have hx27_4 : s4.readReg64 .x27 = ctxPtr := hx27_cs4.trans hx27_3
  have htr3_s : s3.trace = s.trace := htr3_2.trans (htr2_1.trans htr1)
  have hst_to4 : Steps (lsProg_518 ext) s s4 :=
    hst1.trans (hst2.trans (hst3.trans hst4))
  have hfold_2c8 :
      ((coroPtr + 0x2c8#64) ↦₆₄ saveIdFutPtr) ∗
      ((coroPtr + 0x2d0#64) ↦₆₄ (0#64 + ikit.saveFutVtOff)) ⊢
      memRegion (coroPtr + 0x2c8#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      cells16_entails_memRegion16 (coroPtr + 0x2c8#64) _ _
  have hbox_dealloc :
      A.live saveIdFutPtr ikit.saveBoxSize 8 ∗
      ikit.saveBoxAt saveIdFutPtr idStorePtr remoteAddrPtr remoteIkPtr 1#8 ⊢
      A.live saveIdFutPtr (BitVec.ofNat 64 ikit.saveBoxSize).toNat (8#64).toNat ∗
      memRegion saveIdFutPtr (BitVec.ofNat 64 ikit.saveBoxSize).toNat := by
    refine Entails.trans (sepConj_mono_right (ikit.saveBoxAt_memRegion _ _ _ _ _)) ?_
    rw [← hbox_eq]; exact Entails.refl _
  let st_poll := M.stepEvents evs_poll (M.stepEvents evs_shim st0)
  let evs_save := evs_shim ++ (evs_poll ++ rustDeallocEvents ikit.saveBoxSize 8)
  have hevs_save : SaveStepEnv ikit ikitEnv ist0 peer.val remoteIk evs_save :=
    SeqEnv.append hevs_shim (SeqEnv.append hevs_poll rfl)
  have hst_save_eq :
      M.stepEvents (rustDeallocEvents (BitVec.ofNat 64 ikit.saveBoxSize).toNat (8#64).toNat) st_poll =
      M.stepEvents evs_save st0 := by
    have h8 : (8#64).toNat = 8 := rfl
    rw [← hbox_eq, h8]
    dsimp only [st_poll, evs_save]
    simp only [AllocCostModel.stepEvents_append]
  rcases ans with ⟨⟩ | c
  · -- Err () arm: +0x6c → saveFutDrop → +0x2ec → +0x550 → x30
    refine P3P4.SepWPp.weaken_frame (savePollPlacedErr_unpack_repack (s.sp + 0x3e0#64))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun o1 =>
      SepWPp.exists_elim fun o2 => SepWPp.exists_elim fun o3 =>
      SepWPp.exists_elim fun o4 => SepWPp.exists_elim fun o5 =>
      SepWPp.exists_elim fun o6 => SepWPp.exists_elim fun H_err => ?_
    refine SepWPp.pure_elim fun ⟨hw0_eq, hrepack⟩ => ?_
    subst hw0_eq
    have h1c := p4_seg1c_gen_vregs_placed_wp (A := A) (lim := lim) ext st_poll s4 coroPtr saveIdFutPtr
      (0#64 + ikit.saveFutVtOff) (0#64 + ikit.saveFutDropOff)
      0x800000000000001A#64 o2 o3 o4 o5 u_2b0s u_2b8s u_2c0s u_2c8s o1 o6 u_2d0s
      (by decide) (ikit.saveFutDrop_ne_zero rfl) hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h1c
    refine bind_sepWP_steps_frame_placed hcro4 h1c (by sep_focus)
      fun s5 hst5 hpc5 hrun5 hcro5 ⟨hsp5_4, htr5_4, _, hx19_5, hx21_5, hx22_5, hx23_5,
        hx24_5, hx25_5, hx26_5, _, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    have hsp5 : s5.sp = s.sp := hsp5_4
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_al
    refine call_rocl_entails_steps_frame_placed
      (spec := futDropBudgetSpec) (x := ()) (P_spec := emp)
      hcro5 (hikit.saveFutDrop (by decide)) hpc5 hrun5 hsp5_al hlr5
      (Entails.refl _) (by sep_focus)
      (hpan_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hexit_false := fun _ _ => by unfold futDropBudgetSpec; rfl)
      (hoom_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hnext := fun s6 hst6 hpc6 hrun6 hsp6_5 hsp6_al hcs6 hcro6 => ?_)
    dsimp only [futDropBudgetSpec]
    refine SepWPp.pure_elim fun ⟨htr6_5, hvm6⟩ => ?_
    rw [← A.pool_transport lim st_poll s5 s6 hvm6]
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, hx22_cs6, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, _, hx28_cs6, _, hvregs_cs6⟩
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_errUnwind ikit s.sp hsp_ub))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
      (by sep_focus) ?_
    have h1d_err := p4_seg1d_err_vregs_placed_wp (A := A) (lim := lim) ext hdealloc st_poll s6
      coroPtr saveIdFutPtr (0#64 + ikit.saveFutVtOff) (BitVec.ofNat 64 ikit.saveBoxSize) 8#64
      0x800000000000001A#64 ikit.saveBoxSize_ne_zero (by decide) hpc6 hrun6 hsp6_al
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      (hx28_cs6.trans hx28_5)
    rw [hsp6] at h1d_err
    refine bind_sepWP_steps_frame_placed hcro6 h1d_err (by sep_focus)
      fun s7 hst7 hpc7 hrun7 hcro7 ⟨hsp7_6, htr7_6, hx8_7, hx19_7, hx22_7,
        hx24_7, hx25_7, hx26_7, _, hx28_7, _, hvregs7_6⟩ => ?_
    rw [hst_save_eq]
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hsp7 : s7.sp = s.sp := hsp7_6
    have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hsp7]; exact hsp_align
    have hx22_7' : s7.readReg64 .x22 = o1.zeroExtend 64 :=
      hx22_7.trans (hx22_cs6.trans hx22_5)
    have hx24_7' : s7.readReg64 .x24 = s7.sp + 0x370#64 := by
      rw [hx24_7, hx24_cs6, hx24_5, hsp7]
    have hx25_7' : s7.readReg64 .x25 = s7.sp + 0x210#64 := by
      rw [hx25_7, hx25_cs6, hx25_5, hsp7]
    have hx26_7' : s7.readReg64 .x26 = outPtr :=
      hx26_7.trans (hx26_cs6.trans (hx26_5.trans hx26_4))
    have hunwind := stageP4_err_unwind_550_vregs_placed_ok ext hdealloc hDropSS3
      (M.stepEvents evs_save st0) s0 s7
      coroPtr (s.sp + 0x2b0#64) ptCap ptPtr outPtr 0x800000000000001A#64 prevStatesPtr
      o2 o3 o4 o5 o1 o6 b_2c0 pt G ssSt (fun _ _ => False)
      hpt_le herr_ub hcro7 hpc7 hrun7 hsp7_align hx8_7 hx19_7 hx22_7'
      hx24_7' hx25_7' hx26_7' hx28_7
      (hvregs7_6.trans (hvregs_cs6.trans (hvregs5_4.trans hvregs_4)))
    rw [hsp7] at hunwind
    refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.SepWPp.bind_false_frame
      hunwind (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_unw, ⟨evs_unw, hfree_unw, hP1⟩, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hP1) ?_
    have hst_all : Steps (lsProg_518 ext) s sf :=
      hst_to4.trans (hst5.trans (hst6.trans (hst7.trans hst_unw)))
    have htr_all : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()) := by
      rw [htrf, htr7_6, htr6_5, htr5_4, htr4_3, htr3_s]
    have hevs_err : StageP4MatchedSaveErrEnv ikit ikitEnv ist0 peer.val remoteIk
        (evs_save ++ evs_unw) :=
      SeqEnv.append hevs_save hfree_unw
    have hst_err_eq :
        M.stepEvents evs_unw (M.stepEvents evs_save st0) =
        M.stepEvents (evs_save ++ evs_unw) st0 :=
      (M.stepEvents_append evs_save evs_unw st0).symm
    refine SepWPp.done hpcf hrunf ?_
    refine hErr (evs_save ++ evs_unw) sf _ hevs_err hst_all hrel hpcf hrunf hspf htr_all
      hcsf hvregsf hcrof ?_
    have hreplace :
        ∀ {A B R P Q : SepProp},
          (A ⊢ B) → P = A ∗ R → B ∗ R = Q → (P ⊢ Q) := by
      intro A B R P Q hab hp hq
      rw [hp, ← hq]
      exact sepConj_mono_left hab
    rw [hst_err_eq]
    unfold stageP4SaveIdErrPostPlaced stageP4SaveIdSharedPlaced saveIdVtablesAt
    rw [stack_saveId_to_errUnwind ikit s.sp hsp_ub]
    exact hreplace (hrepack outPtr) (by sep_focus) (by sep_ac_rfl)
  · -- Ok c arm: +0x6c → saveFutDrop → +0x2ec → kyberMarkUsedShimAddr
    have hsave_ok_eq :
        savePollPlacedOutAt (s.sp + 0x3e0#64) (.ok c) =
        savePollOutAt 0#64 (s.sp + 0x3e0#64) (.ok c) := rfl
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (hsave_ok_eq.trans (savePollOk_eq_exists_pollCells 0#64 (s.sp + 0x3e0#64) c)))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun o6 => SepWPp.exists_elim fun o5 =>
      SepWPp.exists_elim fun o4 => SepWPp.exists_elim fun o3 =>
      SepWPp.exists_elim fun o2 => ?_
    have h1c := p4_seg1c_gen_vregs_placed_wp (A := A) (lim := lim) ext st_poll s4 coroPtr saveIdFutPtr
      (0#64 + ikit.saveFutVtOff) (0#64 + ikit.saveFutDropOff)
      0xfffffffffffffffe#64 o2 o3 o4 o5 u_2b0s u_2b8s u_2c0s u_2c8s
      (if c == .replacedExisting then 1#32 else 0#32) o6 u_2d0s
      (by decide) (ikit.saveFutDrop_ne_zero rfl) hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h1c
    refine bind_sepWP_steps_frame_placed hcro4 h1c (by sep_focus)
      fun s5 hst5 hpc5 hrun5 hcro5 ⟨hsp5_4, htr5_4, _, hx19_5, hx21_5, _, hx23_5,
        hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    have hsp5 : s5.sp = s.sp := hsp5_4
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5] using hsp_al
    refine call_rocl_entails_steps_frame_placed
      (spec := futDropBudgetSpec) (x := ()) (P_spec := emp)
      hcro5 (hikit.saveFutDrop (by decide)) hpc5 hrun5 hsp5_al hlr5
      (Entails.refl _) (by sep_focus)
      (hpan_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hexit_false := fun _ _ => by unfold futDropBudgetSpec; rfl)
      (hoom_false := fun _ => by unfold futDropBudgetSpec; rfl)
      (hnext := fun s6 hst6 hpc6 hrun6 hsp6_5 hsp6_al hcs6 hcro6 => ?_)
    dsimp only [futDropBudgetSpec]
    refine SepWPp.pure_elim fun ⟨htr6_5, hvm6⟩ => ?_
    rw [← A.pool_transport lim st_poll s5 s6 hvm6]
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, _, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, hx27_cs6, hx28_cs6, _, hvregs_cs6⟩
    have h2ac_un :
        memRegion (coroPtr + 0x2ac#64) 20 =
        ∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
          ((coroPtr + 0x2ac#64) ↦₆₄ u0) ∗ ((coroPtr + 0x2b4#64) ↦₆₄ u1) ∗
          ((coroPtr + 0x2bc#64) ↦₃₂ u2) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion20_eq_cells (coroPtr + 0x2ac#64)
    refine P3P4.SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq h2ac_un) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_errUnwind ikit s.sp hsp_ub))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u_2bc => SepWPp.exists_elim fun u_2b4 =>
      SepWPp.exists_elim fun u_2ac => ?_
    have h1d_ok := p4_seg1d_ok_vregs_placed_wp (A := A) (lim := lim) ext hdealloc st_poll s6
      coroPtr msgPtr kyberStorePtr kyberStoreVt kyberMarkUsedShimAddr saveIdFutPtr
      (0#64 + ikit.saveFutVtOff) (BitVec.ofNat 64 ikit.saveBoxSize) 8#64
      u_2ac u_2b4 opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2bc
      ikit.saveBoxSize_ne_zero hopk_ne2 hpc6 hrun6 hsp6_al
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      (hx28_cs6.trans hx28_5)
    rw [hsp6] at h1d_ok
    refine bind_sepWP_steps_frame_placed hcro6 h1d_ok (by sep_focus)
      fun s7 hst7 hpc7 hrun7 hcro7 ⟨hsp7_6, htr7_6, hx0_7, hx1_7, hx2_7, hx3_7,
        hx19_7, hx24_7, hx25_7, hx26_7, hx27_7, hx28_7, _, hlr7, hvregs7_6⟩ => ?_
    rw [hst_save_eq]
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_saveId_to_errUnwind ikit s.sp hsp_ub).symm)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (stagingCellsAt_entails_memRegion36 (s.sp + 0x2b0#64) _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hst_all : Steps (lsProg_518 ext) s s7 :=
      hst_to4.trans (hst5.trans (hst6.trans hst7))
    have htr_all : s7.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.ok c) := by
      rw [htr7_6, htr6_5, htr5_4, htr4_3, htr3_s]
    refine hOk c evs_save s7 _ hevs_save hst_all hrel hpc7 hrun7 hsp7_6 htr_all
      hx0_7 hx1_7 hx2_7 hx3_7 hx19_7
      (hx24_7.trans (hx24_cs6.trans hx24_5))
      (hx25_7.trans (hx25_cs6.trans hx25_5))
      (hx26_7.trans (hx26_cs6.trans (hx26_5.trans hx26_4)))
      (hx27_7.trans (hx27_cs6.trans (hx27_5.trans hx27_4)))
      hx28_7 hlr7 hcro7
      (hvregs7_6.trans (hvregs_cs6.trans (hvregs5_4.trans hvregs_4))) ?_
    unfold stageP4SaveIdOkPostPlaced stageP4SaveIdSharedPlaced saveIdVtablesAt
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProofPlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# Budget-Threaded Parsing Callee `SepWPp` Wrappers for Arm `R1b`

Budget-threaded `SepWPp` call wrappers on Block `579` for `split_signed` (Block `592`), `split_id`
(Block `593`), `<PublicKey>::deserialize` (Block `201`), and `kem::PublicKey::deserialize` (Block `590`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (deserializeFullPlacedSpec deserializeResult33At)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt speWord strRefAt utf8)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession.Cli
  (splitId splitIdResultAt splitOkTag splitSigned splitSignedResultAt)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers (vecU8_to_ownedBytes)
open CryptoVerification.SignalSession.Cli.RunCompose
  (InRunPlaced PanicK RunNeeds RunSem r1b_CodeOk r1b_StackBounds r1b_cells2_to_region16
   r1b_sepWPp_drop_left r1b_spAligned_of_fsp runFsp runPcPlaced runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs (kemDeserResAt kemPkDeserialize)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_placed r1b_files_eq_of_trace_eq_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
  (cliKemDeserializeSpec kemDeserializeEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced pkDeserializeFull_vm_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (splitIdSpecPlaced splitSignedSpecPlaced)

theorem r1b_call_splitSigned_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret fp : BitVec 64} {file : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hc : RunCalleesPlaced A lim cEnvs H B σ)
    (hbnd : r1b_StackBounds B resStack) (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 592) (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0) (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0) (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ret) (hx1 : st_bl.readReg64 .x1 = fp)
    (hx2 : (st_bl.readReg64 .x2).toNat = file.length)
    (hfit : FitsEnv M lim st (cEnvs.splitSigned file))
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent) (eCap ePtr : BitVec 64) (eBs : List (BitVec 8)),
      cEnvs.splitSigned file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitSigned file = none → sf.fs.files = st_bl.fs.files → sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom)
    (hok : ∀ (sf : State) (evs : List AllocEvent) (id : BitVec 32) (key sig : List (BitVec 8)),
      cEnvs.splitSigned file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitSigned file = some (id, key, sig) → sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ splitOkTag) ∗
          ((ret + 8#64) ↦₆₄ (fp + 4#64)) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 key.length) ∗
          ((ret + 24#64) ↦₃₂ id) ∗ memRegion (ret + 28#64) 4 ∗
          ((ret + 32#64) ↦₆₄ (fp + 4#64 + BitVec.ofNat 64 key.length)) ∗
          ((ret + 40#64) ↦₆₄ 64#64) ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      ((fp ↦ₛ file) ∗ memRegion ret 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed (x := ({ ret := ret, fp := fp, file := file, ro := false }, st))
    (hc.splitSigned hbnd.splitSigned) hinv hpc hrun hal_bl hlr hpanicK
    (F := F) ?_ (hnext := ?_)
  · dsimp only [splitSignedSpecPlaced, withLsCodeRoLoaded, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [splitSignedSpecPlaced, withLsCodeRoLoaded, bytesAt, splitSignedResultAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun ⟨htr_f, hevs⟩ => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
    cases hsp_res : splitSigned file with
    | none =>
      dsimp only [speAt]
      have hstr_drop : strRefAt (ret + 32#64) (utf8 "bundle") ⊢
          ∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "bundle") ∗ memRegion (ret + 32#64) 16 := by
        dsimp only [strRefAt]
        refine Entails.sepExists_elim fun fnPtr => Entails.sepExists_right fnPtr ?_
        have hcells :
            ((ret + 32#64) ↦₆₄ fnPtr) ∗
              ((ret + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "bundle").length) ⊢
            memRegion (ret + 32#64) 16 := r1b_cells2_to_region16 _ _ _
        exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_right hcells)
      have hev : ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc (ret + 8#64) bs)) ⊢
          ∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (ret ↦₆₄ speWord 1) ∗
            ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs := by
        rw [sepExists_sepConj_right]
        refine Entails.sepExists_elim fun eBs => Entails.sepExists_right eBs ?_
        have hv := vecU8_to_ownedBytes A.repAlloc (ret + 8#64) eBs
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
        exact Entails.trans (sepConj_mono_right hv) (by
          simp only [sepExists_sepConj_right]
          exact Entails.sepExists_elim fun eCap => Entails.sepExists_right eCap
            (Entails.sepExists_elim fun ePtr => Entails.sepExists_right ePtr
              (Entails.of_eq (by sep_ac_rfl))))
      refine sepWPp_weaken_pre
        (P' := (∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
          (ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs) ∗
          (∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "bundle") ∗ memRegion (ret + 32#64) 16) ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) ?_ ?_
      · rw [hsp]
        refine Entails.trans (Entails.of_eq (show _ =
          ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc (ret + 8#64) bs)) ∗
          strRefAt (ret + 32#64) (utf8 "bundle") ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F by sep_ac_rfl)) ?_
        exact sepConj_mono hev (sepConj_mono_left hstr_drop)
      · simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun fnPtr =>
          SepWPp.exists_elim fun eBs =>
          SepWPp.exists_elim fun eCap =>
          SepWPp.exists_elim fun ePtr => ?_
        refine sepWPp_weaken_pre
          (P' := (fnPtr ↦ᵣ utf8 "bundle") ∗
            ((ret ↦₆₄ speWord 1) ∗
              ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
              ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
              memRegion (ret + 32#64) 16 ∗
              ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
              (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim (M.stepEvents evs st) sf ∗ F))
          (Entails.of_eq (by sep_ac_rfl)) ?_
        exact r1b_sepWPp_drop_left (herr sf evs eCap ePtr eBs hevs hin_f hcs_f hsp_res hfiles_f htr_f)
    | some triple =>
      rcases triple with ⟨id, key, sig⟩
      dsimp only
      refine sepWPp_weaken_pre ?_
        (hok sf evs id key sig hevs hin_f hcs_f hsp_res hfiles_f htr_f)
      rw [hsp]
      exact Entails.of_eq (by sep_ac_rfl)

theorem r1b_call_splitId_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {cEnvs : RunCalleesEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret fp : BitVec 64} {file : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hc : RunCalleesPlaced A lim cEnvs H B σ)
    (hbnd : r1b_StackBounds B resStack) (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 593) (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0) (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0) (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ret) (hx1 : st_bl.readReg64 .x1 = fp)
    (hx2 : (st_bl.readReg64 .x2).toNat = file.length)
    (hfit : FitsEnv M lim st (cEnvs.splitId file))
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (evs : List AllocEvent) (eCap ePtr : BitVec 64) (eBs : List (BitVec 8)),
      cEnvs.splitId file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitId file = none → sf.fs.files = st_bl.fs.files → sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom)
    (hok : ∀ (sf : State) (evs : List AllocEvent) (id : BitVec 32) (key : List (BitVec 8)),
      cEnvs.splitId file evs →
      InRunPlaced r1b_CodeOk s0 sf retOff → CalleeSavedPreserved st_bl sf →
      splitId file = some (id, key) → sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ splitOkTag) ∗
          ((ret + 8#64) ↦₃₂ id) ∗ memRegion (ret + 12#64) 4 ∗
          ((ret + 16#64) ↦₆₄ (fp + 4#64)) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 key.length) ∗
          memRegion (ret + 32#64) 16 ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      ((fp ↦ₛ file) ∗ memRegion ret 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed (x := ({ ret := ret, fp := fp, file := file, ro := false }, st))
    (hc.splitId hbnd.splitId) hinv hpc hrun hal_bl hlr hpanicK
    (F := F) ?_ (hnext := ?_)
  · dsimp only [splitIdSpecPlaced, withLsCodeRoLoaded, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [splitIdSpecPlaced, withLsCodeRoLoaded, bytesAt, splitIdResultAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun ⟨htr_f, hevs⟩ => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
    cases hsp_res : splitId file with
    | none =>
      dsimp only [speAt]
      have hstr_drop : strRefAt (ret + 32#64) (utf8 "bundle") ⊢
          ∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "bundle") ∗ memRegion (ret + 32#64) 16 := by
        dsimp only [strRefAt]
        refine Entails.sepExists_elim fun fnPtr => Entails.sepExists_right fnPtr ?_
        have hcells :
            ((ret + 32#64) ↦₆₄ fnPtr) ∗
              ((ret + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "bundle").length) ⊢
            memRegion (ret + 32#64) 16 := r1b_cells2_to_region16 _ _ _
        exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_right hcells)
      have hev : ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc (ret + 8#64) bs)) ⊢
          ∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (ret ↦₆₄ speWord 1) ∗
            ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs := by
        rw [sepExists_sepConj_right]
        refine Entails.sepExists_elim fun eBs => Entails.sepExists_right eBs ?_
        have hv := vecU8_to_ownedBytes A.repAlloc (ret + 8#64) eBs
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
        exact Entails.trans (sepConj_mono_right hv) (by
          simp only [sepExists_sepConj_right]
          exact Entails.sepExists_elim fun eCap => Entails.sepExists_right eCap
            (Entails.sepExists_elim fun ePtr => Entails.sepExists_right ePtr
              (Entails.of_eq (by sep_ac_rfl))))
      refine sepWPp_weaken_pre
        (P' := (∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
          (ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs) ∗
          (∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "bundle") ∗ memRegion (ret + 32#64) 16) ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) ?_ ?_
      · rw [hsp]
        refine Entails.trans (Entails.of_eq (show _ =
          ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc (ret + 8#64) bs)) ∗
          strRefAt (ret + 32#64) (utf8 "bundle") ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F by sep_ac_rfl)) ?_
        exact sepConj_mono hev (sepConj_mono_left hstr_drop)
      · simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun fnPtr =>
          SepWPp.exists_elim fun eBs =>
          SepWPp.exists_elim fun eCap =>
          SepWPp.exists_elim fun ePtr => ?_
        refine sepWPp_weaken_pre
          (P' := (fnPtr ↦ᵣ utf8 "bundle") ∗
            ((ret ↦₆₄ speWord 1) ∗
              ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
              ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
              memRegion (ret + 32#64) 16 ∗
              ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
              (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim (M.stepEvents evs st) sf ∗ F))
          (Entails.of_eq (by sep_ac_rfl)) ?_
        exact r1b_sepWPp_drop_left (herr sf evs eCap ePtr eBs hevs hin_f hcs_f hsp_res hfiles_f htr_f)
    | some pair =>
      rcases pair with ⟨id, key⟩
      dsimp only
      refine sepWPp_weaken_pre ?_
        (hok sf evs id key hevs hin_f hcs_f hsp_res hfiles_f htr_f)
      rw [hsp]
      exact Entails.of_eq (by sep_ac_rfl)

theorem r1b_call_pkDeserialize_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {g : RunCall} {s0 st_bl : State} {retOff : Nat}
    {ptr sret : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 201)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ptr)
    (hx1 : (st_bl.readReg64 .x1).toNat = bs.length)
    (hx8 : st_bl.readReg64 .x8 = sret)
    (hlen : bs.length < 2 ^ 63)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      VmPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (deserializeResult33At sret (PublicKey.deserialize bs) ∗
          (ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      ((ptr ↦ₛ bs) ∗ memRegion sret 33 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed (ptr, bs, sret)
    (pkDeserializeFull_vm_placed_ok (callerProg := runProgPlaced H) (i := 579) H)
    hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hnext := ?_)
  · dsimp only [withVmPreserved, deserializeFullPlacedSpec]
    simp only [sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx8, hlen⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [withVmPreserved, deserializeFullPlacedSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hvm_f => SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
    refine sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf hin_f hcs_f hvm_f hfiles_f htr_f)

theorem r1b_call_pkDeserialize_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {g : RunCall} {s0 st_bl : State} {retOff : Nat}
    {ptr sret : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 201)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ptr)
    (hx1 : (st_bl.readReg64 .x1).toNat = bs.length)
    (hx8 : st_bl.readReg64 .x8 = sret)
    (hlen : bs.length < 2 ^ 63)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (deserializeResult33At sret (PublicKey.deserialize bs) ∗
          (ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      ((ptr ↦ₛ bs) ∗ memRegion sret 33 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool lim st st_bl ∗ F)
      Q Qp oom :=
  r1b_call_pkDeserialize_placed hh hinv hpc hrun hsp hfp hvregs hsp0 hlr
    hx0 hx1 hx8 hlen hpanicK fun sf hin_f hcs_f hvm_f hfiles_f htr_f => by
      rw [← A.pool_of_vmPreserved hvm_f]
      exact hnext sf hin_f hcs_f hfiles_f htr_f

theorem r1b_call_kemDeserialize_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {r p : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs))
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 590)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = r)
    (hx1 : st_bl.readReg64 .x1 = p)
    (hx2 : st_bl.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hlen : bs.length < 2 ^ 63)
    (hfit : FitsEvents M lim st (kemDeserializeEvents bs))
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (kemDeserResAt A.repAlloc r (kemPkDeserialize bs) ∗
          (p ↦ₛ bs) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (kemDeserializeEvents bs) st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (memRegion r 24 ∗ (p ↦ₛ bs) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed (x := ({ r := r, ro := false, p := p, bs := bs }, st))
    (hc.kemDeserialize (resStack - runFrame) hbnd.kem hbnd.sub63)
    hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hnext := ?_)
  · dsimp only [cliKemDeserializeSpec, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hlen, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [cliKemDeserializeSpec, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
    refine sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hfiles_f htr_f)
    rw [hsp]
    exact Entails.of_eq (by sep_ac_rfl)


theorem r1b_call_kemDeserialize_of_kem_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {r p : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hkem : (slotsOfPlaced A lim sEnvs S needs).kemDeserialize.OkPlaced
      (CryptoVerification.SignalSession.Cli.Run.Placed.lsProg_579 H)
      (CryptoVerification.SignalSession.Cli.Placed.blkPl_590).base)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 590)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = r)
    (hx1 : st_bl.readReg64 .x1 = p)
    (hx2 : st_bl.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hlen : bs.length < 2 ^ 63)
    (hfit : FitsEvents M lim st (kemDeserializeEvents bs))
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (kemDeserResAt A.repAlloc r (kemPkDeserialize bs) ∗
          (p ↦ₛ bs) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (kemDeserializeEvents bs) st) sf ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (memRegion r 24 ∗ (p ↦ₛ bs) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st st_bl ∗ F)
      Q Qp oom := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed (x := ({ r := r, ro := false, p := p, bs := bs }, st))
    (hkem (resStack - runFrame) hbnd.kem hbnd.sub63)
    hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hnext := ?_)
  · dsimp only [cliKemDeserializeSpec, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc, sepConj_emp]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hlen, hfit⟩
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [cliKemDeserializeSpec, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
    refine sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hfiles_f htr_f)
    rw [hsp]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudget

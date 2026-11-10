/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.SliceHelpers

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

theorem r1b_call_splitSigned {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret fp : BitVec 64} {file : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% ((2 ^ 64 + ls_off% "libsignal_cli::public::split_signed" -
        ls_off% "libsignal_cli::run") % 2 ^ 64))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = ret)
    (hx1 : st_bl.readReg64 .x1 = fp)
    (hx2 : (st_bl.readReg64 .x2).toNat = file.length)
    (htr0 : s0.trace <+: st_bl.trace)
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (eCap ePtr : BitVec 64) (eBs : List (BitVec 8)),
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      splitSigned file = none →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0))
    (hok : ∀ (sf : State) (id : BitVec 32) (key sig : List (BitVec 8)),
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      splitSigned file = some (id, key, sig) →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ splitOkTag) ∗
          ((ret + 8#64) ↦₆₄ (fp + 4#64)) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 key.length) ∗
          ((ret + 24#64) ↦₃₂ id) ∗ memRegion (ret + 28#64) 4 ∗
          ((ret + 32#64) ↦₆₄ (fp + 4#64 + BitVec.ofNat 64 key.length)) ∗
          ((ret + 40#64) ↦₆₄ 64#64) ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      ((fp ↦ₛ file) ∗ memRegion ret 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call (x := { ret := ret, fp := fp, file := file, ro := false })
    (r1b_splitSigned_ok himg hh hbnd.splitSigned) hinv hpc hrun hal_bl hlr hpanicK
    (F := F) ?_ (hpanic := ?_) (hnext := ?_)
  · dsimp only [Spec.inImage, splitSignedSpec, SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc]
    apply Entails.pure_right hinv
    apply Entails.pure_right ⟨hx0, hx1, hx2⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf R' _ hpost
    dsimp only [Spec.inImage, splitSignedSpec] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (r1b_allocFailedIn_sub htr0 hpost.1.1)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, splitSignedSpec, SpqrV1.ChainProofs.bytesAt, splitSignedResultAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq hh hsteps htr_f
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
        exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right hcells)
      have hev : ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (ret + 8#64) bs)) ⊢
          ∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (ret ↦₆₄ speWord 1) ∗
            ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs := by
        rw [sepExists_sepConj_right]
        refine Entails.sepExists_elim fun eBs => Entails.sepExists_right eBs ?_
        have hv := M3Helpers.vecU8_to_ownedBytes A (ret + 8#64) eBs
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
        exact Entails.trans (sepConj_mono_right hv) (by
          simp only [sepExists_sepConj_right]
          exact Entails.sepExists_elim fun eCap => Entails.sepExists_right eCap
            (Entails.sepExists_elim fun ePtr => Entails.sepExists_right ePtr
              (Entails.of_eq (by ac_rfl))))
      refine MainHops.sepWPp_weaken_pre
        (P' := (∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
          (ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs) ∗
          (∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "bundle") ∗ memRegion (ret + 32#64) 16) ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) ?_ ?_
      · rw [hsp]
        refine Entails.trans (Entails.of_eq (show _ =
          ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (ret + 8#64) bs)) ∗
          strRefAt (ret + 32#64) (utf8 "bundle") ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F by ac_rfl)) ?_
        exact sepConj_mono hev (sepConj_mono_left hstr_drop)
      · simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun fnPtr =>
          SepWPp.exists_elim fun eBs =>
          SepWPp.exists_elim fun eCap =>
          SepWPp.exists_elim fun ePtr => ?_
        refine MainHops.sepWPp_weaken_pre
          (P' := (fnPtr ↦ᵣ utf8 "bundle") ∗
            ((ret ↦₆₄ speWord 1) ∗
              ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
              ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
              memRegion (ret + 32#64) 16 ∗
              ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
              (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F))
          (Entails.of_eq (by ac_rfl)) ?_
        exact r1b_sepWPp_drop_left (herr sf eCap ePtr eBs hin_f hcs_f hsp_res hfiles_f htr_f)
    | some triple =>
      rcases triple with ⟨id, key, sig⟩
      dsimp only
      refine MainHops.sepWPp_weaken_pre ?_
        (hok sf id key sig hin_f hcs_f hsp_res hfiles_f htr_f)
      rw [hsp]; exact Entails.of_eq (by ac_rfl)

theorem r1b_call_splitId {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret fp : BitVec 64} {file : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% ((2 ^ 64 + ls_off% "libsignal_cli::public::split_id" -
        ls_off% "libsignal_cli::run") % 2 ^ 64))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = ret)
    (hx1 : st_bl.readReg64 .x1 = fp)
    (hx2 : (st_bl.readReg64 .x2).toNat = file.length)
    (htr0 : s0.trace <+: st_bl.trace)
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (eCap ePtr : BitVec 64) (eBs : List (BitVec 8)),
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      splitId file = none →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0))
    (hok : ∀ (sf : State) (id : BitVec 32) (key : List (BitVec 8)),
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      splitId file = some (id, key) →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ splitOkTag) ∗
          ((ret + 8#64) ↦₃₂ id) ∗ memRegion (ret + 12#64) 4 ∗
          ((ret + 16#64) ↦₆₄ (fp + 4#64)) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 key.length) ∗
          memRegion (ret + 32#64) 16 ∗
          (fp ↦ₛ file) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      ((fp ↦ₛ file) ∗ memRegion ret 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call (x := { ret := ret, fp := fp, file := file, ro := false })
    (r1b_splitId_ok himg hh hbnd.splitId) hinv hpc hrun hal_bl hlr hpanicK
    (F := F) ?_ (hpanic := ?_) (hnext := ?_)
  · dsimp only [Spec.inImage, splitIdSpec, SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc]
    apply Entails.pure_right hinv
    apply Entails.pure_right ⟨hx0, hx1, hx2⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf R' _ hpost
    dsimp only [Spec.inImage, splitIdSpec] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (r1b_allocFailedIn_sub htr0 hpost.1.1)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, splitIdSpec, SpqrV1.ChainProofs.bytesAt, splitIdResultAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq hh hsteps htr_f
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
        exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right hcells)
      have hev : ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (ret + 8#64) bs)) ⊢
          ∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (ret ↦₆₄ speWord 1) ∗
            ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs := by
        rw [sepExists_sepConj_right]
        refine Entails.sepExists_elim fun eBs => Entails.sepExists_right eBs ?_
        have hv := M3Helpers.vecU8_to_ownedBytes A (ret + 8#64) eBs
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
        exact Entails.trans (sepConj_mono_right hv) (by
          simp only [sepExists_sepConj_right]
          exact Entails.sepExists_elim fun eCap => Entails.sepExists_right eCap
            (Entails.sepExists_elim fun ePtr => Entails.sepExists_right ePtr
              (Entails.of_eq (by ac_rfl))))
      refine MainHops.sepWPp_weaken_pre
        (P' := (∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
          (ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs) ∗
          (∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "bundle") ∗ memRegion (ret + 32#64) 16) ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) ?_ ?_
      · rw [hsp]
        refine Entails.trans (Entails.of_eq (show _ =
          ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (ret + 8#64) bs)) ∗
          strRefAt (ret + 32#64) (utf8 "bundle") ∗
          (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F by ac_rfl)) ?_
        exact sepConj_mono hev (sepConj_mono_left hstr_drop)
      · simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun fnPtr =>
          SepWPp.exists_elim fun eBs =>
          SepWPp.exists_elim fun eCap =>
          SepWPp.exists_elim fun ePtr => ?_
        refine MainHops.sepWPp_weaken_pre
          (P' := (fnPtr ↦ᵣ utf8 "bundle") ∗
            ((ret ↦₆₄ speWord 1) ∗
              ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
              ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
              memRegion (ret + 32#64) 16 ∗
              ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
              (fp ↦ₛ file) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F))
          (Entails.of_eq (by ac_rfl)) ?_
        exact r1b_sepWPp_drop_left (herr sf eCap ePtr eBs hin_f hcs_f hsp_res hfiles_f htr_f)
    | some pair =>
      rcases pair with ⟨id, key⟩
      dsimp only
      refine MainHops.sepWPp_weaken_pre ?_
        (hok sf id key hin_f hcs_f hsp_res hfiles_f htr_f)
      rw [hsp]; exact Entails.of_eq (by ac_rfl)

theorem r1b_call_pkDeserialize {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {g : RunCall} {s0 st_bl : State} {retOff : Nat}
    {ptr sret : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hinv : ImgCallInv img st_bl)
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% ((2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::deserialize" -
        ls_off% "libsignal_cli::run") % 2 ^ 64))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = ptr)
    (hx1 : (st_bl.readReg64 .x1).toNat = bs.length)
    (hx8 : st_bl.readReg64 .x8 = sret)
    (hlen : bs.length < 2 ^ 63)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (Wire.deserializeResult33At sret (PublicKey.deserialize bs) ∗
          (ptr ↦ₛ bs) ∗ logOff img ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      ((ptr ↦ₛ bs) ∗ memRegion sret 33 ∗ logOff img ∗ F)
      Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call (ptr, bs, sret) (r1b_pkDeserializeFull_ok img ext)
    hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hnext := ?_)
  · change _ ⊢
      (⌜ImgCallInv img st_bl⌝ ∗
        ⌜st_bl.readReg64 .x0 = ptr ∧ (st_bl.readReg64 .x1).toNat = bs.length ∧
          st_bl.readReg64 .x8 = sret ∧ bs.length < 2 ^ 63 ∧ img.base &&& 0xfff#64 = 0#64⌝ ∗
        (ptr ↦ₛ bs) ∗ memRegion sret 33 ∗ logOff img) ∗ (F ∗ emp)
    simp only [sepConj_assoc, sepConj_emp]
    apply Entails.pure_right hinv
    apply Entails.pure_right ⟨hx0, hx1, hx8, hlen, RunSkeleton.base_aligned himg⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    change SepWPp (mProg img ext) (s0.readReg64 .lr) sf
      ((⌜sf.trace = st_bl.trace⌝ ∗
        (ptr ↦ₛ bs) ∗ Wire.deserializeResult33At sret (PublicKey.deserialize bs) ∗
        logOff img) ∗ F) Q Qp (runOom s0)
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq hh hsteps htr_f
    refine MainHops.sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sf hin_f hcs_f hfiles_f htr_f)

theorem r1b_call_kemDeserialize {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {r p : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% ((2 ^ 64 +
        ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize" -
        ls_off% "libsignal_cli::run") % 2 ^ 64))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = r)
    (hx1 : st_bl.readReg64 .x1 = p)
    (hx2 : st_bl.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hlen : bs.length < 2 ^ 63)
    (htr0 : s0.trace <+: st_bl.trace)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (RunProofs.kemDeserResAt A r (RunProofs.kemPkDeserialize bs) ∗
          (p ↦ₛ bs) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      (memRegion r 24 ∗ (p ↦ₛ bs) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call (x := { r := r, ro := false, p := p, bs := bs })
    (r1b_kemDeserialize_ok hc hbnd.kem hbnd.sub63)
    hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hpanic := ?_) (hnext := ?_)
  · dsimp only [Spec.inImage, RunProofs.cliKemDeserializeSpec, SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc]
    apply Entails.pure_right hinv
    apply Entails.pure_right ⟨hx0, hx1, hx2, hlen⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf R' _ hpost
    dsimp only [Spec.inImage, RunProofs.cliKemDeserializeSpec] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (r1b_allocFailedIn_sub htr0 hpost.1.1)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, RunProofs.cliKemDeserializeSpec, SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq hh hsteps htr_f
    refine MainHops.sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hfiles_f htr_f)
    rw [hsp]; exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunCompose

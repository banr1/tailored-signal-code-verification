/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliImgPlacement
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliImgLift
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4StepsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Specification Bridge at the `signal_session::run` Call Boundary

Bridges `runSpecPlaced` (`[LibsignalPlacement]`) and `(runSpecTight ...).inImage img` at `main`'s
`signal_session::run` call site (`lsmpl.base 579` → `mPcPlaced 0x7a4`) on `cliProg img ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace CryptoVerification.SignalSession.Cli.MainHops.CliImgSpecs

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.MainHops.CliImgPlacement
open CryptoVerification.LibsignalPublicApi.StoreKit

private theorem allocFailedIn_of_start_trace_eq {s0 sm sf : State}
    (htr : sm.trace = s0.trace) (h : allocFailedIn sm sf) : allocFailedIn s0 sf := by
  unfold allocFailedIn at h ⊢
  rwa [htr] at h

/-- Under `himg : Obj.Loads libsignalSessionImage img` and `instLibsignalFullPlacementOfLoads img himg`,
`runSpecPlaced.pre` entails `runSpecTight.pre` (dropping `CodeOk s.mem` and rewriting placed statics). -/
theorem runSpecPlaced_pre_entails_runSpecTight {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {CodeOk : Memory → Prop} {A : RustAlloc} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    (g : RunCall) (s : State) :
    (@runSpecPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
      CodeOk A uuidParse Run wrOk resStack).pre g s ⊢
      (runSpecTight A img uuidParse Run wrOk resStack).pre g s := by
  dsimp only [runSpecTight, runSpec, runSpecPlaced]
  rw [coinsInstalledPlaced_eq_coinsInstalled img himg,
    tokenInitPlacedAt_eq_tokenInit img himg,
    lsLogOff_eq_logOff img himg]
  exact sepConj_mono_left (Entails.pure_mono fun h => h.2)

/-- Invokes `hrun : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr runName) ((runSpecTight ...).inImage img)`
directly on `cliProg img ext` at state `s3` (`AtM4RunCallPlaced`), re-establishing both `img.CallInv sf`
and `LibsignalFrozen (imgMultiPlacement img) sf.mem` at return `mPcPlaced 0x7a4`. -/
theorem call_run_on_cliProg {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {ext : String → Option (State → State)}
    {A : RustAlloc} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    {s0 s3 : State} {ret : BitVec 64} {n : Nat}
    {buf inCap inPtr : BitVec 64} {inLen : Nat}
    {g_run : RunCall} {frameRun : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hrun : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr runName)
      ((runSpecTight A img uuidParse Run wrOk resStack).inImage img))
    (hs3 : @AtM4RunCallPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
      (LibsignalFrozen (imgMultiPlacement img)) s0 s3 n buf inCap inPtr inLen)
    (htr3_0 : s3.trace = s0.trace)
    (hinv3 : img.CallInv s3)
    (hpanic : ∀ sf Pf, (g_run.a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hnext : ∀ sf : State,
      img.CallInv sf →
      LibsignalFrozen (imgMultiPlacement img) sf.mem →
      sf.pc = @mPcPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement 0x7a4 →
      sf.status = .Running →
      sf.sp = s3.sp →
      CalleeSavedPreserved s3 sf →
      SepWPp (cliProg img ext) ret sf
        ((@runSpecTightPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
          (LibsignalFrozen (imgMultiPlacement img)) A uuidParse Run wrOk resStack).post g_run s3 sf ∗
          frameRun)
        Q Qp (mainOom s0)) :
    SepWPp (cliProg img ext) ret s3
      ((@runSpecPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
        (LibsignalFrozen (imgMultiPlacement img)) A uuidParse Run wrOk resStack).pre g_run s3 ∗
        frameRun)
      Q Qp (mainOom s0) := by
  letI : LibsignalFullPlacement := instLibsignalFullPlacementOfLoads img himg
  have hrun_cli : subroutine_ok (cliProg img ext) ((mProg img ext).fnAddr runName)
      ((runSpecTight A img uuidParse Run wrOk resStack).inImage img) := by
    rw [cliProg_eq_mProg himg ext]
    exact hrun
  have hpc3 : s3.pc = (mProg img ext).fnAddr runName :=
    hs3.pc.trans (base579_eq_run_fnAddr himg ext)
  refine main_call_inImage (prog := cliProg img ext) (img := img)
    (entry := (mProg img ext).fnAddr runName)
    (ret_pc := mPcPlaced 0x7a4) (ret := ret)
    (spec := runSpecTight A img uuidParse Run wrOk resStack) (F := frameRun)
    g_run hrun_cli hinv3 hpc3 hs3.run hs3.spAligned hs3.lr
    (sepConj_mono_left (runSpecPlaced_pre_entails_runSpecTight himg g_run s3))
    (hpanic := fun sf R' _ hp => ?_)
    (hoom := fun sf R' _ ho => ?_)
    (hnext := fun sf hinv_f hpcm hrunm hspm hcsm =>
      hnext sf hinv_f (img_libsignalFrozen himg hinv_f.1) hpcm hrunm hspm hcsm)
    (s0 := s3)
  · dsimp only [runSpecTight, runSpec] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    exact hpanic sf _ (hp.1.imp_right (allocFailedIn_of_start_trace_eq htr3_0))
  · dsimp only [runSpecTight, runSpec] at ho
    exact (not_satisfies_false_sepConj ho).elim

end CryptoVerification.SignalSession.Cli.MainHops.CliImgSpecs

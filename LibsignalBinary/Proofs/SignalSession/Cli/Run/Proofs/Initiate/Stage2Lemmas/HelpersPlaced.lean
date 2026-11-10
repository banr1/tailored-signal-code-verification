/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Helpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_OkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section
set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.LibsignalPublicApi.StoreSession
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

theorem sepWPp_panic_handleError_placed [LibsignalPlacement] {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {target_pc : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsρ lsRawVecHandleErrorSym)
    (hrun : s.status = .Running)
    (hpan : Qp (Rust.panicked s) P) :
    SepWPp (initProgPlaced mmpl gh W) target_pc s P Q Qp oom :=
  SepWPp.panic hrun (hpc ▸ ((ls_externAt?_of_mem (sym := lsRawVecHandleErrorSym)).trans rfl)) hpan

theorem initPanicPostPlaced_of_false [LibsignalPlacement] (A : RustAlloc) (S : RunSem)
    (x : InitGhost) (stk : Nat) {s0 sf : State} (F : SepProp) :
    InitPanicPostPlaced A S x stk s0 sf (⌜False⌝ ∗ F) :=
  Entails.pure_left False.elim

theorem inInitiatePlaced_after_call [LibsignalPlacement] {s0 s sm sf : State} {k0 k1 : Nat}
    (hctrl : InInitiatePlaced s0 s k0)
    (hsp1 : sm.sp = s.sp)
    (hfp1 : sm.readReg64 .fp = s.readReg64 .fp)
    (hx19_1 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hvregs1 : calleeSavedVRegs sm = calleeSavedVRegs s)
    (hkf1 : s.mem.KeepsFrozen sm.mem)
    (hfiles1 : sm.fs.files = s.fs.files)
    (hpc2 : sf.pc = initPcPlaced k1)
    (hrun2 : sf.status = .Running)
    (hsp2 : sf.sp = sm.sp)
    (hcs2 : CalleeSavedPreserved sm sf)
    (hkf2 : sm.mem.KeepsFrozen sf.mem)
    (hfiles2 : sf.fs.files = sm.fs.files) :
    InInitiatePlaced s0 sf k1 := by
  rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hvregs2⟩
  exact
    { pc := hpc2
      run := hrun2
      sp := hsp2.trans (hsp1.trans hctrl.sp)
      fp := hfp2.trans (hfp1.trans hctrl.fp)
      x19 := hx19_2.trans (hx19_1.trans hctrl.x19)
      files0 := hfiles2.trans (hfiles1.trans hctrl.files0)
      inv := (hctrl.inv.of_keepsFrozen hkf1).of_keepsFrozen hkf2
      vregs := hvregs2.trans (hvregs1.trans hctrl.vregs)
      spAligned := hctrl.spAligned }

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

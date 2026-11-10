/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudgetFd

/-!
# `FdsGe3Closed`-Threaded Work Frame (`r1b_OkCtxPlacedFd`) for Arm `R1b`

Extends `r1b_OkCtxPlaced` with `FdsGe3Closed s.fs` and provides step, call, and error-projection
combinators across Arm `R1b` (`R+0x074c → R+0x28f0`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd

open Arm64 (CalleeSavedPreserved Memory State)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall cliIo)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRunEntryPlaced InRunPlaced Init1Data RunSem r1b_ErrCtxPlaced r1b_OkCtxPlaced
   readBundleV runFiles)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudgetFd
  (fdsGe3Closed_of_fs_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
  (AtInit1PlacedFd AtRunEntryPlacedFd)

/-- Happy-path Arm `R1b` context pairing `r1b_OkCtxPlaced` with `FdsGe3Closed s.fs`. -/
structure r1b_OkCtxPlacedFd [LibsignalPlacement] (CodeOk : Memory → Prop) (S : RunSem)
    (g : RunCall) (d : Init1Data) (s0 s : State) (off : Nat) : Prop
    extends ok : r1b_OkCtxPlaced CodeOk S g d s0 s off where
  fds : FdsGe3Closed s.fs

abbrev r1b_OkCtxPlacedFd.base [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s : State} {off : Nat}
    (hok : r1b_OkCtxPlacedFd CodeOk S g d s0 s off) :
    r1b_OkCtxPlaced CodeOk S g d s0 s off :=
  hok.ok

theorem r1b_OkCtxPlacedFd.of_init1 [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s1 : State}
    (he : AtRunEntryPlaced CodeOk S g s0) (hi1 : AtInit1PlacedFd CodeOk g d s0 s1) :
    r1b_OkCtxPlacedFd CodeOk S g d s0 s1 0x74c :=
  { ok := r1b_OkCtxPlaced.of_init1 he hi1.1
    fds := hi1.2 }

theorem r1b_OkCtxPlacedFd.of_init1_fd [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s1 : State}
    (he : AtRunEntryPlacedFd CodeOk S g s0) (hi1 : AtInit1PlacedFd CodeOk g d s0 s1) :
    r1b_OkCtxPlacedFd CodeOk S g d s0 s1 0x74c :=
  r1b_OkCtxPlacedFd.of_init1 he.1 hi1

theorem r1b_OkCtxPlacedFd.of_step [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s sm : State} {off off' : Nat}
    (hok : r1b_OkCtxPlacedFd CodeOk S g d s0 s off)
    (hin : InRunPlaced CodeOk s0 sm off')
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20 : sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5))
    (hx21 : sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5))
    (hx22 : sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5))
    (htr : sm.trace = s.trace)
    (hfs_eq : sm.fs = s.fs) :
    r1b_OkCtxPlacedFd CodeOk S g d s0 sm off' :=
  { ok := hok.ok.of_step hin hx19 hx20 hx21 hx22 htr (congrArg (·.files) hfs_eq)
    fds := fdsGe3Closed_of_fs_eq hfs_eq hok.fds }

theorem r1b_OkCtxPlacedFd.of_step_fds [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s sm : State} {off off' : Nat}
    (hok : r1b_OkCtxPlacedFd CodeOk S g d s0 s off)
    (hin : InRunPlaced CodeOk s0 sm off')
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20 : sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5))
    (hx21 : sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5))
    (hx22 : sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5))
    (htr : sm.trace = s.trace)
    (hfs : sm.fs.files = s.fs.files)
    (hfds : FdsGe3Closed sm.fs) :
    r1b_OkCtxPlacedFd CodeOk S g d s0 sm off' :=
  { ok := hok.ok.of_step hin hx19 hx20 hx21 hx22 htr hfs
    fds := hfds }

theorem r1b_OkCtxPlacedFd.of_call [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 st_bl sf : State} {off off' : Nat}
    (hok : r1b_OkCtxPlacedFd CodeOk S g d s0 st_bl off)
    (hin : InRunPlaced CodeOk s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hfs_eq : sf.fs = st_bl.fs)
    (htr : sf.trace = st_bl.trace) :
    r1b_OkCtxPlacedFd CodeOk S g d s0 sf off' :=
  hok.of_step hin hcs.1 hcs.2.1 hcs.2.2.1 hcs.2.2.2.1 htr hfs_eq

theorem r1b_OkCtxPlacedFd.of_call_fds [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 st_bl sf : State} {off off' : Nat}
    (hok : r1b_OkCtxPlacedFd CodeOk S g d s0 st_bl off)
    (hin : InRunPlaced CodeOk s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hfs : sf.fs.files = st_bl.fs.files)
    (htr : sf.trace = st_bl.trace)
    (hfds : FdsGe3Closed sf.fs) :
    r1b_OkCtxPlacedFd CodeOk S g d s0 sf off' :=
  hok.of_step_fds hin hcs.1 hcs.2.1 hcs.2.2.1 hcs.2.2.2.1 htr hfs hfds

theorem r1b_OkCtxPlacedFd.after_call [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s st_bl sf : State} {off off' : Nat}
    (hok : r1b_OkCtxPlacedFd CodeOk S g d s0 s off)
    (hx19_bl : st_bl.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20_bl : st_bl.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5))
    (hx21_bl : st_bl.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5))
    (hx22_bl : st_bl.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5))
    (htr_bl : st_bl.trace = s.trace)
    (hfs_bl : st_bl.fs = s.fs)
    (hin : InRunPlaced CodeOk s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hfs_eq : sf.fs = st_bl.fs)
    (htr : sf.trace = st_bl.trace) :
    r1b_OkCtxPlacedFd CodeOk S g d s0 sf off' :=
  hok.of_step hin (hcs.1.trans hx19_bl) (hcs.2.1.trans hx20_bl)
    (hcs.2.2.1.trans hx21_bl) (hcs.2.2.2.1.trans hx22_bl)
    (htr.trans htr_bl) (hfs_eq.trans hfs_bl)

theorem r1b_OkCtxPlacedFd.after_call_fds [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s st_bl sf : State} {off off' : Nat}
    (hok : r1b_OkCtxPlacedFd CodeOk S g d s0 s off)
    (hx19_bl : st_bl.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20_bl : st_bl.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5))
    (hx21_bl : st_bl.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5))
    (hx22_bl : st_bl.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5))
    (htr_bl : st_bl.trace = s.trace)
    (hfs_bl : st_bl.fs.files = s.fs.files)
    (hin : InRunPlaced CodeOk s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hfs : sf.fs.files = st_bl.fs.files)
    (htr : sf.trace = st_bl.trace)
    (hfds : FdsGe3Closed sf.fs) :
    r1b_OkCtxPlacedFd CodeOk S g d s0 sf off' :=
  hok.of_step_fds hin (hcs.1.trans hx19_bl) (hcs.2.1.trans hx20_bl)
    (hcs.2.2.1.trans hx21_bl) (hcs.2.2.2.1.trans hx22_bl)
    (htr.trans htr_bl) (hfs.trans hfs_bl) hfds

theorem r1b_OkCtxPlacedFd.to_err [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s : State} {off : Nat}
    (hok : r1b_OkCtxPlacedFd CodeOk S g d s0 s off)
    (hnone : readBundleV (runFiles g.i) d.dir d.peerV.device = none) :
    r1b_ErrCtxPlaced CodeOk g d s0 s off :=
  hok.ok.to_err hnone

theorem r1b_OkCtxPlacedFd.to_readErr [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 st_bl sf : State} {off off' : Nat} {path : List (BitVec 8)}
    (hok : r1b_OkCtxPlacedFd CodeOk S g d s0 st_bl off)
    (hin : InRunPlaced CodeOk s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hout : cliIo.rd st_bl.fs.files path = .error () ∧
      sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace)
    (hnone_of_err : cliIo.rd (runFiles g.i) path = .error () →
      readBundleV (runFiles g.i) d.dir d.peerV.device = none) :
    r1b_ErrCtxPlaced CodeOk g d s0 sf off' :=
  hok.ok.to_readErr hin hcs hout hnone_of_err

theorem r1b_OkCtxPlacedFd.after_readErr [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s st_bl sf : State} {off off' : Nat}
    {path : List (BitVec 8)}
    (hok : r1b_OkCtxPlacedFd CodeOk S g d s0 s off)
    (hx19_bl : st_bl.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20_bl : st_bl.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5))
    (hx21_bl : st_bl.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5))
    (hx22_bl : st_bl.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5))
    (htr_bl : st_bl.trace = s.trace)
    (hfs_bl : st_bl.fs.files = s.fs.files)
    (hin : InRunPlaced CodeOk s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hout : cliIo.rd st_bl.fs.files path = .error () ∧
      sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace)
    (hnone_of_err : cliIo.rd (runFiles g.i) path = .error () →
      readBundleV (runFiles g.i) d.dir d.peerV.device = none) :
    r1b_ErrCtxPlaced CodeOk g d s0 sf off' :=
  hok.ok.after_readErr
    hx19_bl hx20_bl hx21_bl hx22_bl htr_bl hfs_bl hin hcs hout hnone_of_err

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd

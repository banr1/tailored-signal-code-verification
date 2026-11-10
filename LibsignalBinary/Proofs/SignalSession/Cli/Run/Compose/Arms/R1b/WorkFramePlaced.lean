/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFrame
public meta import Lean
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import all Init.Data.String.Defs

/-!
# Relocatable Work Frame and `r1b_OkCtxPlaced` for Arm `R1b`

Relocatable (`[LibsignalPlacement]`) counterparts of `R1b.WorkFrame` on Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

structure r1b_OkCtxPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (S : RunSem)
    (g : RunCall) (d : Init1Data) (s0 s : State) (off : Nat) : Prop where
  st : InRunPlaced CodeOk s0 s off
  he : AtRunEntryPlaced CodeOk S g s0
  callEq : g.c = .init d.peerV d.dir
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  x20 : s.readReg64 (.gpr 20#5) = g.res
  x21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap
  x22 : s.readReg64 (.gpr 22#5) = d.ikW2
  peerVal : d.peerG.val = addrValOf d.peerV
  meVal : d.meG.val = addrValOf d.meV
  ownSem : ∃ ownB : Bytes,
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
      addrParse uuidTryParse ownB = some d.meV
  ikSem : ∃ ikB : Bytes,
    bundleFile (runFiles g.i) d.dir "identity-key" = some ikB ∧
      exceptOpt (decodeIdentityKey ikB) = some d.idKey
  ikWords : Words32Eq d.idKey.publicKey.bytes.toList d.ikW0 d.ikW1 d.ikW2 d.ikW3
  rejectIfNone : readBundleV (runFiles g.i) d.dir d.peerV.device = none → g.a = some none
  trace : s0.trace <+: s.trace
  fs : s.fs.files = runFiles g.i
  stdout : Arm64.Process.ProcessOutcome.traceStreamBytes .stdout s.trace = []

theorem r1b_OkCtxPlaced.of_init1 [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s1 : State}
    (he : AtRunEntryPlaced CodeOk S g s0) (hi1 : AtInit1Placed CodeOk g d s0 s1) :
    r1b_OkCtxPlaced CodeOk S g d s0 s1 0x74c := {
  st := hi1.base, he := he, callEq := hi1.callEq,
  x19 := hi1.x19, x20 := hi1.x20, x21 := hi1.x21, x22 := hi1.x22,
  peerVal := hi1.peerVal, meVal := hi1.meVal, ownSem := hi1.ownSem,
  ikSem := hi1.ikSem, ikWords := hi1.ikWords,
  rejectIfNone := r1b_reject_of_readBundle_none_placed he hi1,
  trace := hi1.trace, fs := hi1.fs, stdout := hi1.stdout
}

theorem r1b_OkCtxPlaced.of_step [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s sm : State} {off off' : Nat}
    (hok : r1b_OkCtxPlaced CodeOk S g d s0 s off)
    (hin : InRunPlaced CodeOk s0 sm off')
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20 : sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5))
    (hx21 : sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5))
    (hx22 : sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5))
    (htr : sm.trace = s.trace)
    (hfs : sm.fs.files = s.fs.files) :
    r1b_OkCtxPlaced CodeOk S g d s0 sm off' := {
  st := hin, he := hok.he, callEq := hok.callEq,
  x19 := hx19.trans hok.x19, x20 := hx20.trans hok.x20,
  x21 := hx21.trans hok.x21, x22 := hx22.trans hok.x22,
  peerVal := hok.peerVal, meVal := hok.meVal, ownSem := hok.ownSem,
  ikSem := hok.ikSem, ikWords := hok.ikWords, rejectIfNone := hok.rejectIfNone,
  trace := htr ▸ hok.trace, fs := hfs.trans hok.fs,
  stdout := r1b_stdout_eq_of_trace_eq htr hok.stdout
}

theorem r1b_OkCtxPlaced.of_call [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 st_bl sf : State} {off off' : Nat}
    (hok : r1b_OkCtxPlaced CodeOk S g d s0 st_bl off)
    (hin : InRunPlaced CodeOk s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hfs : sf.fs.files = st_bl.fs.files)
    (htr : sf.trace = st_bl.trace) :
    r1b_OkCtxPlaced CodeOk S g d s0 sf off' :=
  hok.of_step hin hcs.1 hcs.2.1 hcs.2.2.1 hcs.2.2.2.1 htr hfs

theorem r1b_OkCtxPlaced.to_err [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s : State} {off : Nat}
    (hok : r1b_OkCtxPlaced CodeOk S g d s0 s off)
    (hnone : readBundleV (runFiles g.i) d.dir d.peerV.device = none) :
    r1b_ErrCtxPlaced CodeOk g d s0 s off := {
  st := hok.st, x19 := hok.x19, x20 := hok.x20, x21 := hok.x21,
  trace := hok.trace, hist := ⟨hok.fs, hok.stdout⟩,
  ans := hok.rejectIfNone hnone
}

theorem r1b_OkCtxPlaced.to_readErr [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 st_bl sf : State} {off off' : Nat} {path : List (BitVec 8)}
    (hok : r1b_OkCtxPlaced CodeOk S g d s0 st_bl off)
    (hin : InRunPlaced CodeOk s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hout : cliIo.rd st_bl.fs.files path = .error () ∧
      sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace)
    (hnone_of_err : cliIo.rd (runFiles g.i) path = .error () →
      readBundleV (runFiles g.i) d.dir d.peerV.device = none) :
    r1b_ErrCtxPlaced CodeOk g d s0 sf off' :=
  (hok.of_call hin hcs hout.2.1 hout.2.2).to_err (hnone_of_err (hok.fs ▸ hout.1))

theorem r1b_ErrCtxPlaced.of_step [LibsignalPlacement] {CodeOk : Memory → Prop}
    {g : RunCall} {d : Init1Data} {s0 s sm : State} {off off' : Nat}
    (hc : r1b_ErrCtxPlaced CodeOk g d s0 s off)
    (hin : InRunPlaced CodeOk s0 sm off')
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20 : sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5))
    (hx21 : sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5))
    (htr : sm.trace = s.trace)
    (hfs : sm.fs.files = s.fs.files) :
    r1b_ErrCtxPlaced CodeOk g d s0 sm off' := {
  st := hin, x19 := hx19.trans hc.x19, x20 := hx20.trans hc.x20, x21 := hx21.trans hc.x21,
  trace := htr ▸ hc.trace,
  hist := ⟨hfs.trans hc.hist.1, htr ▸ hc.hist.2⟩,
  ans := hc.ans
}

theorem r1b_OkCtxPlaced.after_call [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s st_bl sf : State} {off off' : Nat}
    (hok : r1b_OkCtxPlaced CodeOk S g d s0 s off)
    (hx19_bl : st_bl.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hx20_bl : st_bl.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5))
    (hx21_bl : st_bl.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5))
    (hx22_bl : st_bl.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5))
    (htr_bl : st_bl.trace = s.trace)
    (hfs_bl : st_bl.fs.files = s.fs.files)
    (hin : InRunPlaced CodeOk s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hfs : sf.fs.files = st_bl.fs.files)
    (htr : sf.trace = st_bl.trace) :
    r1b_OkCtxPlaced CodeOk S g d s0 sf off' :=
  hok.of_step hin (hcs.1.trans hx19_bl) (hcs.2.1.trans hx20_bl)
    (hcs.2.2.1.trans hx21_bl) (hcs.2.2.2.1.trans hx22_bl)
    (htr.trans htr_bl) (hfs.trans hfs_bl)

theorem r1b_OkCtxPlaced.after_readErr [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init1Data} {s0 s st_bl sf : State} {off off' : Nat}
    {path : List (BitVec 8)}
    (hok : r1b_OkCtxPlaced CodeOk S g d s0 s off)
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
  (hok.after_call hx19_bl hx20_bl hx21_bl hx22_bl htr_bl hfs_bl hin hcs hout.2.1 hout.2.2).to_err
    (hnone_of_err (hok.fs ▸ hfs_bl ▸ hout.1))

noncomputable abbrev r1b_relocSym579 (off : Nat) : String :=
  match lsBlocksTree.get? 579 with
  | some b =>
    match b.relocAt? off with
    | some r => r.sym
    | none => ""
  | none => ""

noncomputable abbrev r1b_regIdSym : String := "libsignal_cli:.rodata..Lanon.13"
noncomputable abbrev r1b_unreadSym : String := "libsignal_cli:.rodata..Lanon.65"
noncomputable abbrev r1b_spkSym : String := r1b_relocSym579 0xc80
noncomputable abbrev r1b_malfSym : String := "libsignal_cli:.rodata..Lanon.67"
noncomputable abbrev r1b_kpkSym : String := r1b_relocSym579 0x1268
noncomputable abbrev r1b_opkSym : String := r1b_relocSym579 0x12dc

theorem r1b_ro_reg_id_placed [LibsignalPlacement] {m : Memory} {R : SepProp}
    (hinv : r1b_CodeOk m) (hm : m ⊨ R) :
    m ⊨ (lsρ r1b_regIdSym ↦ᵣ utf8 "registration-id") ∗ R :=
  lsro_intro_chk hinv.2 (sym := r1b_regIdSym) (bs := utf8 "registration-id") (by decide +kernel) hm

theorem r1b_ro_unreadable_placed [LibsignalPlacement] {m : Memory} {R : SepProp}
    (hinv : r1b_CodeOk m) (hm : m ⊨ R) :
    m ⊨ (lsρ r1b_unreadSym ↦ᵣ utf8 "file could not be read") ∗ R :=
  lsro_intro_chk hinv.2 (sym := r1b_unreadSym) (bs := utf8 "file could not be read") (by decide +kernel) hm

theorem r1b_ro_spk_placed [LibsignalPlacement] {m : Memory} {R : SepProp}
    (hinv : r1b_CodeOk m) (hm : m ⊨ R) :
    m ⊨ (lsρ r1b_spkSym ↦ᵣ utf8 "signed-pre-key") ∗ R :=
  lsro_intro_chk hinv.2 (sym := r1b_spkSym) (bs := utf8 "signed-pre-key") (by decide +kernel) hm

theorem r1b_ro_malformed_placed [LibsignalPlacement] {m : Memory} {R : SepProp}
    (hinv : r1b_CodeOk m) (hm : m ⊨ R) :
    m ⊨ (lsρ r1b_malfSym ↦ᵣ utf8 "malformed file") ∗ R :=
  lsro_intro_chk hinv.2 (sym := r1b_malfSym) (bs := utf8 "malformed file") (by decide +kernel) hm

theorem r1b_ro_kpk_placed [LibsignalPlacement] {m : Memory} {R : SepProp}
    (hinv : r1b_CodeOk m) (hm : m ⊨ R) :
    m ⊨ (lsρ r1b_kpkSym ↦ᵣ utf8 "kyber-pre-key") ∗ R :=
  lsro_intro_chk hinv.2 (sym := r1b_kpkSym) (bs := utf8 "kyber-pre-key") (by decide +kernel) hm

theorem r1b_ro_opk_placed [LibsignalPlacement] {m : Memory} {R : SepProp}
    (hinv : r1b_CodeOk m) (hm : m ⊨ R) :
    m ⊨ (lsρ r1b_opkSym ↦ᵣ utf8 "one-time-pre-key") ∗ R :=
  lsro_intro_chk hinv.2 (sym := r1b_opkSym) (bs := utf8 "one-time-pre-key") (by decide +kernel) hm

def r1b_invCore_placed [LibsignalPlacement] (A : RustAlloc) (g : RunCall) (d : Init1Data)
    (s0 : State) : SepProp :=
  let fsp := runFsp s0
  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    addrNameHeap A d.meG ∗ runSaved s0 ∗
    memRegion (fsp + 0x118#64) 4 ∗ memRegion (fsp + 0x160#64) 4 ∗
    ((fsp + 0x180#64) ↦₆₄ d.ikW0) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗
    ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗
    memRegion (fsp + 0x1d0#64) 0x90 ∗
    addrUpperAt (fsp + 0x260#64) d.meG ∗
    memRegion (fsp + 0x270#64) 0x30 ∗
    protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗
    memRegion (fsp + 0x2c0#64) 0x210 ∗
    memRegion (fsp + 0x500#64) 0x1250 ∗
    memRegion (fsp + 0x1768#64) 0x1288

theorem r1b_init1Mem_unpack_placed [LibsignalPlacement] (A : RustAlloc) (g : RunCall) (d : Init1Data)
    (s0 : State) (resStack : Nat) :
    let fsp := runFsp s0
    init1MemPlaced A g d s0 resStack ⊢
      r1b_invCore_placed A g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 8 ∗ memRegion (fsp + 0x128#64) 8 ∗
        memRegion (fsp + 0x130#64) 8 ∗ memRegion (fsp + 0x138#64) 8 ∗
        memRegion (fsp + 0x140#64) 8 ∗ memRegion (fsp + 0x148#64) 8 ∗
        memRegion (fsp + 0x150#64) 8 ∗ memRegion (fsp + 0x158#64) 8 ∗
        memRegion (fsp + 0x164#64) 4 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        memRegion (fsp + 0x198#64) 16 ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗
        memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool := by
  intro fsp
  dsimp only [init1MemPlaced, init1Cells, runLocals, runLocalsFrom, runLocalBytes,
    r1b_invCore_placed, FromRecordCallees.lsLogOff, fsp]
  simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.add_zero,
    memRegion_zero, emp_sepConj]
  have h000 : memRegion (runFsp s0) 0x180 =
      memRegion (runFsp s0) 0x110 ∗ memRegion (runFsp s0 + 0x110#64) 8 ∗
      memRegion (runFsp s0 + 0x118#64) 4 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
      memRegion (runFsp s0 + 0x120#64) 8 ∗ memRegion (runFsp s0 + 0x128#64) 8 ∗
      memRegion (runFsp s0 + 0x130#64) 8 ∗ memRegion (runFsp s0 + 0x138#64) 8 ∗
      memRegion (runFsp s0 + 0x140#64) 8 ∗ memRegion (runFsp s0 + 0x148#64) 8 ∗
      memRegion (runFsp s0 + 0x150#64) 8 ∗ memRegion (runFsp s0 + 0x158#64) 8 ∗
      memRegion (runFsp s0 + 0x160#64) 4 ∗ memRegion (runFsp s0 + 0x164#64) 4 ∗
      memRegion (runFsp s0 + 0x168#64) 8 ∗ memRegion (runFsp s0 + 0x170#64) 8 ∗
      memRegion (runFsp s0 + 0x178#64) 8 := by
    rw [ProofLib.memRegion_split (runFsp s0) 0x110 0x70 (by decide),
      r1b_split_region (runFsp s0) 0x110 8 0x68,
      r1b_split_region (runFsp s0) 0x118 4 0x64,
      r1b_split_region (runFsp s0) 0x11c 4 0x60,
      r1b_split_region (runFsp s0) 0x120 8 0x58,
      r1b_split_region (runFsp s0) 0x128 8 0x50,
      r1b_split_region (runFsp s0) 0x130 8 0x48,
      r1b_split_region (runFsp s0) 0x138 8 0x40,
      r1b_split_region (runFsp s0) 0x140 8 0x38,
      r1b_split_region (runFsp s0) 0x148 8 0x30,
      r1b_split_region (runFsp s0) 0x150 8 0x28,
      r1b_split_region (runFsp s0) 0x158 8 0x20,
      r1b_split_region (runFsp s0) 0x160 4 0x1c,
      r1b_split_region (runFsp s0) 0x164 4 0x18,
      r1b_split_region (runFsp s0) 0x168 8 0x10,
      r1b_split_region (runFsp s0) 0x170 8 8]
  have h2c0 : memRegion (runFsp s0 + 0x2c0#64) 0x2730 =
      memRegion (runFsp s0 + 0x2c0#64) 0x210 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      memRegion (runFsp s0 + 0x500#64) 0x1250 ∗ memRegion (runFsp s0 + 0x1750#64) 24 ∗
      memRegion (runFsp s0 + 0x1768#64) 0x1288 := by
    rw [r1b_split_region (runFsp s0) 0x2c0 0x210 0x2520,
      r1b_split_region (runFsp s0) 0x4d0 0x30 0x24f0,
      r1b_split_region (runFsp s0) 0x500 0x1250 0x12a0,
      r1b_split_region (runFsp s0) 0x1750 0x18 0x1288]
  rw [h000, h2c0]
  exact Entails.of_eq (by ac_rfl)

theorem r1b_invCore_to_errCommon_placed [LibsignalPlacement] (A : RustAlloc) (g : RunCall)
    (d : Init1Data) (s0 : State) (resStack : Nat) :
    let fsp := runFsp s0
    (r1b_invCore_placed A g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
      memRegion (fsp + 0x164#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool) ⊢
      r1b_errCommon A g d s0 resStack := by
  intro fsp
  dsimp only [r1b_invCore_placed, r1b_errCommon, r1b_errCore, r1b_errFrameRest]
  have hfsp : runFsp s0 = fsp := rfl
  simp only [hfsp]
  have hheap :
      coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ (lsLogFilterAddr ↦₆₄ 0#64) ⊢ anyHeap :=
    entails_anyHeap _
  have h180 : ((fsp + 0x180#64) ↦₆₄ d.ikW0) ⊢ memRegion (fsp + 0x180#64) 8 :=
    pointsTo64_entails_memRegion _ _
  have h160 : memRegion (fsp + 0x160#64) 4 ∗ memRegion (fsp + 0x164#64) 4 =
      memRegion (fsp + 0x160#64) 8 := r1b_join_region fsp 0x160 4 4
  have h1d0 :
      memRegion (fsp + 0x1d0#64) 0x90 ∗ addrUpperAt (fsp + 0x260#64) d.meG ∗
        memRegion (fsp + 0x270#64) 0x30 ⊢ memRegion (fsp + 0x1d0#64) 0xd0 := by
    refine Entails.trans (sepConj_mono_right
      (sepConj_mono_left (addrUpperAt_entails_memRegion (fsp + 0x260#64) d.meG))) ?_
    rw [r1b_join_region fsp 0x260 0x10 0x30, r1b_join_region fsp 0x1d0 0x90 0x40]
    exact Entails.refl _
  have h500 :
      memRegion (fsp + 0x500#64) 0x1250 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        memRegion (fsp + 0x1768#64) 0x1288 = memRegion (fsp + 0x500#64) 0x24f0 := by
    rw [r1b_join_region fsp 0x1750 0x18 0x1288,
      r1b_join_region fsp 0x500 0x1250 0x12a0]
  refine r1b_entails_frame_core
    (A1 := (coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ (lsLogFilterAddr ↦₆₄ 0#64)) ∗
      ((fsp + 0x180#64) ↦₆₄ d.ikW0) ∗
      (memRegion (fsp + 0x160#64) 4 ∗ memRegion (fsp + 0x164#64) 4) ∗
      (memRegion (fsp + 0x1d0#64) 0x90 ∗ addrUpperAt (fsp + 0x260#64) d.meG ∗
        memRegion (fsp + 0x270#64) 0x30) ∗
      (memRegion (fsp + 0x500#64) 0x1250 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        memRegion (fsp + 0x1768#64) 0x1288))
    (A2 := anyHeap ∗ memRegion (fsp + 0x180#64) 8 ∗ memRegion (fsp + 0x160#64) 8 ∗
      memRegion (fsp + 0x1d0#64) 0xd0 ∗ memRegion (fsp + 0x500#64) 0x24f0)
    (R := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A d.meG ∗ runSaved s0 ∗
      ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      memRegion fsp 0x110 ∗ memRegion (fsp + 0x118#64) 4 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
      ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗
      ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗
      protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗ memRegion (fsp + 0x2c0#64) 0x210 ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool)
    (by ac_rfl) ?_ (by ac_rfl)
  rw [h160, h500]
  exact sepConj_mono hheap (sepConj_mono h180
    (sepConj_mono_right (sepConj_mono_left h1d0)))

theorem r1b_stage_to_err_placed [LibsignalPlacement] (A : RustAlloc) (g : RunCall) (d : Init1Data)
    (s0 : State) (resStack : Nat) (v164 : BitVec 32) :
    let fsp := runFsp s0
    (r1b_invCore_placed A g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
      ((fsp + 0x164#64) ↦₃₂ v164) ∗
      ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
      ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
      ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
      memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool) ⊢
      r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 := by
  intro fsp
  have h164 : ((fsp + 0x164#64) ↦₃₂ v164) ⊢ memRegion (fsp + 0x164#64) 4 :=
    pointsTo32_entails_memRegion _ _
  have hcore :
      (r1b_invCore_placed A g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        ((fsp + 0x164#64) ↦₃₂ v164) ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool) ⊢
        r1b_errCommon A g d s0 resStack :=
    Entails.trans (r1b_entails_frame (by ac_rfl) h164 (by ac_rfl))
      (r1b_invCore_to_errCommon_placed A g d s0 resStack)
  have h190 : ((fsp + 0x190#64) ↦₆₄ d.ikW3) ⊢ memRegion (fsp + 0x190#64) 8 :=
    pointsTo64_entails_memRegion _ _
  have h1a8 :
      ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ⊢ memRegion (fsp + 0x1a8#64) 16 := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (pointsTo32_entails_memRegion _ _))) ?_
    rw [r1b_join_region fsp 0x1b0 4 4]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cell64_cons (a := fsp + 0x1a8#64) d.ikW1 (n := 8) (by decide)
  exact r1b_entails_frame (by dsimp only [fsp]; ac_rfl)
    (sepConj_mono hcore (sepConj_mono h190 h1a8))
    rfl

end CryptoVerification.SignalSession.Cli.RunCompose

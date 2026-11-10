/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.States
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` Machine-Level Hop States for `signal_session::run`

Defines the placed cut-point state predicates (`AtRunEntryPlaced`, `AtDispatchPlaced`,
`AtInit1Placed`, `AtInit2Placed`, `AtJoinPlaced`, `AtRejectPlaced`), spatial footprints, stack
budget bounds, and `runSpecPlaced` entry/exit bridge lemmas on Block `579` (`lsProg_579`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalProtoCodec

/-! ## 1. Block `579` Program, PCs, and Post-Prologue Invariant (`InRunPlaced`) -/

/-- Block `579` (`signal_session::run`) program under `[LibsignalPlacement]`. -/
noncomputable abbrev runProgPlaced [LibsignalPlacement] (H : LibsignalHooks) : Program :=
  lsProg_579 H

/-- Address `k` bytes past `signal_session::run`'s entry point (`lsmpl.base 579 + k`). -/
abbrev runPcPlaced [LibsignalPlacement] (k : Nat) : BitVec 64 :=
  lsmpl.base 579 + BitVec.ofNat 64 k

theorem runProgPlaced_eq [LibsignalPlacement] (H : LibsignalHooks) :
    runProgPlaced H = (blkPC_579).rebase (blkPl_579).base H := rfl

theorem runPcPlaced_eq [LibsignalPlacement] (k : Nat) :
    runPcPlaced k = (blkPl_579).base + BitVec.ofNat 64 k := rfl

theorem runPcPlaced_zero [LibsignalPlacement] :
    runPcPlaced 0 = lsmpl.base 579 := by
  change lsmpl.base 579 + 0#64 = lsmpl.base 579
  exact BitVec.add_zero _

theorem LsCodeInv.codeLoaded_runProgPlaced [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {m : Memory} (h : CodeOk m) (H : LibsignalHooks) :
    (runProgPlaced H).CodeLoaded m := by
  have heq : runProgPlaced H = libsignalSessionLib.blockProgram lsmpl 579 H :=
    IsLsBlockProg.eq_blockProgram (prog := lsProg_579 H) (i := 579) (H := H)
  rw [heq]
  exact (hCI.toRoCl h).1 579 (by decide) (by decide) H (fun _ => none) Syscall.standard

/-- Common post-prologue machine invariant inside `run` (Block `579`) at offset `R + k`. -/
structure InRunPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (s0 s : State) (k : Nat) : Prop where
  pc : s.pc = runPcPlaced k
  run : s.status = .Running
  sp : s.sp = runFsp s0
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  inv : CodeOk s.mem
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s0.spAligned = true

theorem InRunPlaced.spAligned_cur [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s : State} {k : Nat} (h : InRunPlaced CodeOk s0 s k) : s.spAligned = true := by
  have hs0 : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using h.spAligned
  have hfsp : (s0.sp - 0x2a50#64) &&& 15#64 = 0#64 := by
    bv_bits
  simp only [State.spAligned, h.sp, runFsp, hfsp, beq_self_eq_true]

/-! ## 2. Callee Stack-Budget Bounds from `runNeed` (`slotsOfPlaced`) -/

theorem runNeed_bounds_placed [LibsignalPlacement] {A : RustAlloc} {B : RunBudgets}
    {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hres : runNeed B (slotsOfPlaced A S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    let sub := resStack - runFrame
    runFrame ≤ resStack ∧
      sub ≤ 2 ^ 63 ∧
      sub ≤ 2 ^ 64 ∧
      0xB0 + extHookStack ≤ sub ∧
      finishGrowStackX ≤ sub ∧
      B.readFile ≤ sub ∧
      pathNeed ≤ sub ∧
      B.dirGetNeed ≤ sub ∧
      B.bundleReadNeed ≤ sub ∧
      splitIdNeed ≤ sub ∧
      splitSignedNeed ≤ sub ∧
      0x60 ≤ sub ∧
      smallRootStack ≤ sub ∧
      CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ≤ sub ∧
      32 + extHookStack ≤ sub ∧
      96 + extHookStack ≤ sub ∧
      extHookStack ≤ sub ∧
      needs.encrypt ≤ sub ∧
      needs.decryptSignal ≤ sub ∧
      needs.initiate ≤ sub ∧
      needs.decryptPrekey ≤ sub ∧
      48 + extHookStack ≤ sub := by
  have hres' : runNeed B (slotsOf A default S needs) ≤ resStack := hres
  exact runNeed_bounds hres' hres64
/-! ## 3. Named Machine Boundary States under `[LibsignalPlacement]` -/

/-- Entry state at `R + 0x0`: `run`'s ABI registers and precondition assertions from
`runSpecPlaced CodeOk A uuidTryParse (runRel S) cliWrOk resStack`. -/
structure AtRunEntryPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (S : RunSem)
    (g : RunCall) (s0 : State) : Prop where
  pc : s0.pc = runPcPlaced 0
  run : s0.status = .Running
  inv : CodeOk s0.mem
  spAligned : s0.spAligned = true
  rel : runRel S g.i g.a
  parse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c
  x0 : s0.readReg64 .x0 = g.res
  x1 : s0.readReg64 .x1 = g.call
  x2 : s0.readReg64 .x2 = g.stores
  x3 : s0.readReg64 .x3 = g.inp
  x4 : s0.readReg64 .x4 = BitVec.ofNat 64 (inputOf g.i g.c).length
  fs : s0.fs.files = runFiles g.i
  stdout : ProcessOutcome.traceStreamBytes .stdout s0.trace = []

/-- Entry spatial footprint of `run` under `[LibsignalPlacement]`. -/
def runEntryMemPlaced [LibsignalPlacement] (A : RustAlloc) (g : RunCall) (s0 : State)
    (resStack : Nat) : SepProp :=
  memRegion g.res runResSize ∗ callAt A g.call g.c ∗
    storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
    A.pool ∗ stackAt s0.sp resStack

/-- Post-own-address-check dispatch state at `R + 0x214` under `[LibsignalPlacement]`. -/
structure AtDispatchPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (g : RunCall) (me : MeAtDispatch) (s0 s : State) : Prop where
  base : InRunPlaced CodeOk s0 s 0x214
  x8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 g.c.tag
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  x20 : s.readReg64 (.gpr 20#5) = g.res
  x23 : s.readReg64 (.gpr 23#5) = g.inp
  x24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length
  x25 : s.readReg64 (.gpr 25#5) = g.call
  x26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64
  x27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64
  meRegs : match me with
    | .none => s.readReg64 (.gpr 21#5) = noneCap
    | .some meV meG =>
      s.readReg64 (.gpr 21#5) = meG.name.cap ∧
        s.readReg64 (.gpr 28#5) = meG.name.ptr ∧
        meG.name.bytes = meV.name ∧
        meG.name.cap = BitVec.ofNat 64 meV.name.length ∧
        meG.device = meV.device
  ownSem : ∃ ownB : Bytes,
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
      match me with
      | .none => addrParse uuidTryParse ownB = Option.none
      | .some meV _ => addrParse uuidTryParse ownB = Option.some meV
  trace : s0.trace <+: s.trace
  fs : s.fs.files = runFiles g.i
  stdout : ProcessOutcome.traceStreamBytes .stdout s.trace = []

/-- Spatial footprint at `AtDispatchPlaced` (`R + 0x214`). -/
def dispatchMemPlaced [LibsignalPlacement] (A : RustAlloc) (g : RunCall) (me : MeAtDispatch)
    (s0 : State) (resStack : Nat) : SepProp :=
  let fsp := runFsp s0
  memRegion g.res runResSize ∗ callAt A g.call g.c ∗
    storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
    dispatchMeHeap A me ∗
    runSaved s0 ∗ runLocals fsp (dispatchCells fsp me) ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool

/-- Init checkpoint 1 (`R + 0x74c`) under `[LibsignalPlacement]`. -/
structure AtInit1Placed [LibsignalPlacement] (CodeOk : Memory → Prop)
    (g : RunCall) (d : Init1Data) (s0 s : State) : Prop where
  base : InRunPlaced CodeOk s0 s 0x74c
  callEq : g.c = .init d.peerV d.dir
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  x20 : s.readReg64 (.gpr 20#5) = g.res
  x21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap
  x22 : s.readReg64 (.gpr 22#5) = d.ikW2
  x28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length
  peerVal : d.peerG.val = addrValOf d.peerV
  meVal : d.meG.val = addrValOf d.meV
  ownSem : ∃ ownB : Bytes,
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
      addrParse uuidTryParse ownB = some d.meV
  ikSem : ∃ ikB : Bytes,
    bundleFile (runFiles g.i) d.dir "identity-key" = some ikB ∧
      exceptOpt (decodeIdentityKey ikB) = some d.idKey
  ikWords : Words32Eq d.idKey.publicKey.bytes.toList d.ikW0 d.ikW1 d.ikW2 d.ikW3
  trace : s0.trace <+: s.trace
  fs : s.fs.files = runFiles g.i
  stdout : ProcessOutcome.traceStreamBytes .stdout s.trace = []

/-- Spatial footprint at `AtInit1Placed` (`R + 0x74c`). -/
def init1MemPlaced [LibsignalPlacement] (A : RustAlloc) (g : RunCall) (d : Init1Data)
    (s0 : State) (resStack : Nat) : SepProp :=
  let fsp := runFsp s0
  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
    addrNameHeap A d.meG ∗
    ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
    runSaved s0 ∗ runLocals fsp (init1Cells A fsp d) ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool
/-- Init checkpoint 2 (`R + 0x28f0`) under `[LibsignalPlacement]`. -/
structure AtInit2Placed [LibsignalPlacement] (CodeOk : Memory → Prop)
    (g : RunCall) (d : Init2Data) (s0 s : State) : Prop where
  base : InRunPlaced CodeOk s0 s 0x28f0
  callEq : g.c = .init d.peerV d.dir
  x0 : s.readReg64 .x0 = runFsp s0 + 0x2a0#64
  x1 : s.readReg64 .x1 = runFsp s0 + 0x320#64
  x2 : s.readReg64 .x2 = g.stores + 0xf0#64
  x3 : s.readReg64 .x3 = sessVtPlaced
  x4 : s.readReg64 .x4 = g.stores
  x5 : s.readReg64 .x5 = idVtPlaced
  x6 : s.readReg64 .x6 = runFsp s0 + 0x4d0#64
  x7 : s.readReg64 .x7 = 0#64
  x8 : s.readReg64 .x8 = runFsp s0 + 0x23b0#64
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  x20 : s.readReg64 (.gpr 20#5) = g.res
  x21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap
  peerVal : d.peerG.val = addrValOf d.peerV
  meVal : d.meG.val = addrValOf d.meV
  ownSem : ∃ ownB : Bytes,
    StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
      addrParse uuidTryParse ownB = some d.meV
  bundleSem : readBundleV (runFiles g.i) d.dir d.peerV.device = some d.bundle
  ptrsNeZero : d.spkSigPtr ≠ 0 ∧ d.kpkSigPtr ≠ 0 ∧ d.kpkPtr ≠ 0
  trace : s0.trace <+: s.trace
  fs : s.fs.files = runFiles g.i
  stdout : ProcessOutcome.traceStreamBytes .stdout s.trace = []

/-- Spatial footprint at `AtInit2Placed` (`R + 0x28f0`). -/
def init2MemPlaced [LibsignalPlacement] (A : RustAlloc) (g : RunCall) (d : Init2Data)
    (s0 : State) (resStack : Nat) : SepProp :=
  let fsp := runFsp s0
  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalledPlaced g.coins (MainHops.coinsOf g.i) ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗
    A.live d.spkSigPtr 64 1 ∗ A.live d.kpkSigPtr 64 1 ∗ A.live d.kpkPtr 1568 1 ∗
    ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
    runSaved s0 ∗ runLocals fsp (init2Cells A fsp d) ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool

/-- Accept join state (`R + 0xf8c`) under `[LibsignalPlacement]`. -/
structure AtJoinPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (g : RunCall) (g' : StoresGhost) (out : Bytes) (s0 s : State) : Prop where
  base : InRunPlaced CodeOk s0 s 0xf8c
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  x20 : s.readReg64 (.gpr 20#5) = g.res
  trace : s0.trace <+: s.trace
  hist : RunHistOk g.i s0 s
  ans : g.a = some (some (namedWrites g'.writes, out))
  wrOk : ∀ pw ∈ g'.writes, cliWrOk pw.1

/-- Reject state (`R + 0x2c7c` or `R + 0x124`) under `[LibsignalPlacement]`. -/
structure AtRejectPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (g : RunCall) (g' : StoresGhost) (rk : RejectKind) (s0 s : State) : Prop where
  base : InRunPlaced CodeOk s0 s rk.pcOff
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  preRegs : rk = .preDispatch →
    s.readReg64 (.gpr 20#5) = g.res ∧ s.readReg64 (.gpr 25#5) = g.call
  trace : s0.trace <+: s.trace
  hist : RunHistOk g.i s0 s
  ans : g.a = some none

/-- Concrete normal-return postcondition established by `run_hop_join_placed` at `s0.readReg64 .lr`. -/
def runPostPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (A : RustAlloc)
    (g : RunCall) (resStack : Nat) (s0 sf : State) (Pf : SepProp) : Prop :=
  CodeOk sf.mem ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    s0.trace <+: sf.trace ∧ RunHistOk g.i s0 sf ∧
    ∃ a' : RunAnswer, a' ≠ none ∧ a' = g.a ∧
      (Pf ⊢ memRegion g.call 56 ∗ memRegion g.stores 320 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ A.pool ∗ stackAt s0.sp resStack ∗
        runResAt A cliWrOk g.res a' ∗ anyHeap)

/-! ## 4. Entry / Exit `runSpecPlaced` Bridge Lemmas -/

theorem runEntry_of_placed_pre [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustAlloc} {g : RunCall} {resStack : Nat} {R : SepProp} {s0 : State}
    (hpc : s0.pc = lsmpl.base 579)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (runSpecPlaced CodeOk A uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗ R)
    (hsp : s0.spAligned = true) :
    AtRunEntryPlaced CodeOk S g s0 ∧ (s0.mem ⊨ runEntryMemPlaced A g s0 resStack ∗ R) := by
  simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hinv, hrel, hparse, hx0, hx1, hx2, hx3, hx4, hfs, hout, _hspb⟩, hmem⟩
  refine ⟨⟨?_, hrun, hinv, hsp, hrel, hparse, hx0, hx1, hx2, hx3, hx4, hfs, hout⟩, ?_⟩
  · rw [runPcPlaced_zero, hpc]
  · simpa only [runEntryMemPlaced, sepConj_assoc] using hmem

theorem placed_post_of_runPost [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustAlloc} {g : RunCall} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hfs0 : s0.fs.files = runFiles g.i)
    (hout0 : ProcessOutcome.traceStreamBytes .stdout s0.trace = [])
    (hp : runPostPlaced CodeOk A g resStack s0 sf Pf)
    (hmf : sf.mem ⊨ Pf ∗ R) :
    (sf.mem ⊨ (runSpecPlaced CodeOk A uuidTryParse (runRel S) cliWrOk resStack).post g s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
  rcases hp with ⟨_, hsp, hcs, htr, ⟨hf, ho⟩, a', ha_ne, ha_eq, hent⟩
  refine ⟨?_, hsp, hcs⟩
  have hex :
      runResAt A cliWrOk g.res a' ⊢
        ∃∗ a'', ⌜a'' ≠ none ∧ a'' = g.a⌝ ∗
          runResAt A cliWrOk g.res a'' :=
    Entails.sepExists_right a' (Entails.pure_right ⟨ha_ne, ha_eq⟩ (Entails.refl _))
  have hent' :
      Pf ⊢ memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        A.pool ∗ stackAt s0.sp resStack ∗
        (∃∗ a'', ⌜a'' ≠ none ∧ a'' = g.a⌝ ∗
          runResAt A cliWrOk g.res a'') ∗
        anyHeap :=
    Entails.trans hent
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hex))))))
  have hmem1 := Satisfies.mono (sepConj_mono_left hent') hmf
  simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr, hf.trans hfs0.symm, ho.trans hout0.symm⟩, by simpa only [sepConj_assoc] using hmem1⟩
theorem placed_onPanic_of_runPanic [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustAlloc} {g : RunCall} {resStack : Nat} {R Pf : SepProp} {s0 sf : State}
    (hpan : runPanicProp g s0 sf) (hmf : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨
      (runSpecPlaced CodeOk A uuidTryParse (runRel S) cliWrOk resStack).onPanic g s0 sf ∗ R := by
  simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpan, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmf⟩

theorem placed_onOom_eq [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {A : RustAlloc} (g : RunCall) (resStack : Nat) (s0 : State) :
    (runSpecPlaced CodeOk A uuidTryParse (runRel S) cliWrOk resStack).onOom g s0 =
      runOom s0 := rfl

/-! ## 5. Pure Side-Condition & Semantics Extraction Lemmas under `[LibsignalPlacement]` -/

theorem AtRunEntryPlaced.bounds_pre [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {s0 : State} (he : AtRunEntryPlaced CodeOk S g s0) :
    (MainHops.coinsOf g.i).length < 2 ^ 63 ∧
      (∀ bs, StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok bs →
        ∀ b ∈ bs, b.toNat < 128) :=
  ⟨he.rel.2.1.1, he.rel.2.1.2.2.2.1⟩

theorem AtRunEntryPlaced.reject_of_own_err [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {s0 : State} (he : AtRunEntryPlaced CodeOk S g s0)
    (herr : StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .error ()) :
    g.a = some none := by
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  simp [he.parse, herr]

theorem AtDispatchPlaced.reject_of_me_none [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {s0 s : State}
    (he : AtRunEntryPlaced CodeOk S g s0) (hd : AtDispatchPlaced CodeOk g .none s0 s) :
    g.a = some none := by
  rcases hd.ownSem with ⟨ownB, hget, hnone⟩
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  simp [he.parse, hget, hnone]

theorem AtDispatchPlaced.send_facts [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {peerV : AddrV} {meV : AddrV} {meG : AddrGhost} {s0 s : State}
    (he : AtRunEntryPlaced CodeOk S g s0)
    (hd : AtDispatchPlaced CodeOk g (.some meV meG) s0 s)
    (hc : g.c = .send peerV) :
    g.i.stdin.length < 2 ^ 32 ∧
      (MainHops.coinsOf g.i).length < 2 ^ 63 ∧
      s.fs.files = runFiles g.i ∧
      S.filesOk (runFiles g.i) (addrValOf peerV) (addrValOf meV) ∧
      S.encOk (runFiles g.i) (addrValOf peerV) (MainHops.coinsOf g.i) ∧
      g.a = finish (S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV)
        g.i.stdin (MainHops.coinsOf g.i)) ctWire := by
  rcases hd.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
    hc ▸ he.parse
  refine ⟨he.rel.2.1.2.1 peerV hparse, he.rel.2.1.1, hd.fs,
    he.rel.2.2.1 (.send peerV) peerV ownB meV hparse rfl hget hme,
    he.rel.2.2.2.1 peerV ownB meV hparse hget hme, ?_⟩
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  simp [hparse, hget, hme]

theorem AtRunEntryPlaced.init_bundlePaths_ok [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {peerV : AddrV} {dir : Bytes} {s0 : State}
    (he : AtRunEntryPlaced CodeOk S g s0) (hc : g.c = .init peerV dir) :
    ∀ name ∈ bundleNames, cliWrOk (bundlePath dir name) :=
  he.rel.2.1.2.2.2.2 peerV dir (hc ▸ he.parse)

theorem AtInit2Placed.init_facts [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {d : Init2Data} {s0 s : State}
    (he : AtRunEntryPlaced CodeOk S g s0) (hi : AtInit2Placed CodeOk g d s0 s) :
    (MainHops.coinsOf g.i).length < 2 ^ 63 ∧
      s.fs.files = runFiles g.i ∧
      d.bundle.spkSig.length = 64 ∧
      d.bundle.kpkSig.length = 64 ∧
      d.bundle.kpk.length = 1568 ∧
      S.filesOk (runFiles g.i) d.peerG.val d.meG.val ∧
      S.initOk (runFiles g.i) d.peerG.val d.meG.val ∧
      g.a = finish (S.initiate (runFiles g.i) d.peerG.val d.meG.val
        d.bundle (MainHops.coinsOf g.i)) (fun _ => []) := by
  rcases hi.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.init d.peerV d.dir) :=
    hi.callEq ▸ he.parse
  have hlen := readBundleV_slice_lengths hi.bundleSem
  refine ⟨he.rel.2.1.1, hi.fs, hlen.1, hlen.2.1, hlen.2.2, ?_, ?_, ?_⟩
  · rw [hi.peerVal, hi.meVal]
    exact he.rel.2.2.1 (.init d.peerV d.dir) d.peerV ownB d.meV hparse rfl hget hme
  · rw [hi.peerVal, hi.meVal]
    exact he.rel.2.2.2.2.1.1 d.peerV d.dir ownB d.meV hparse hget hme
  · rw [he.rel.2.2.2.2.2, hi.peerVal, hi.meVal]
    unfold runAns
    simp [hparse, hget, hme, hi.bundleSem]

theorem AtDispatchPlaced.recvW_facts [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {peerV : AddrV} {meV : AddrV} {meG : AddrGhost} {rest : Bytes} {s0 s : State}
    (he : AtRunEntryPlaced CodeOk S g s0)
    (hd : AtDispatchPlaced CodeOk g (.some meV meG) s0 s)
    (hc : g.c = .recv peerV)
    (hstdin : g.i.stdin = 2#8 :: rest) :
    rest.length < 2 ^ 32 ∧
      (MainHops.coinsOf g.i).length < 2 ^ 63 ∧
      s.fs.files = runFiles g.i ∧
      S.filesOk (runFiles g.i) (addrValOf peerV) (addrValOf meV) ∧
      g.a = (match SignalMessage.tryFrom protoSignalCodec rest with
        | .ok m => finish (S.decryptSignal (runFiles g.i) (addrValOf peerV) (addrValOf meV)
            m (MainHops.coinsOf g.i)) id
        | .error _ => some none) := by
  rcases hd.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
    hc ▸ he.parse
  have htail : g.i.stdin.tail.length < 2 ^ 32 := he.rel.2.1.2.2.1 peerV hparse
  rw [hstdin] at htail
  refine ⟨htail, he.rel.2.1.1, hd.fs,
    he.rel.2.2.1 (.recv peerV) peerV ownB meV hparse rfl hget hme, ?_⟩
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  simp [hparse, hget, hme, hstdin]; rfl
theorem AtDispatchPlaced.recvP_facts [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {peerV : AddrV} {meV : AddrV} {meG : AddrGhost} {rest : Bytes} {s0 s : State}
    (he : AtRunEntryPlaced CodeOk S g s0)
    (hd : AtDispatchPlaced CodeOk g (.some meV meG) s0 s)
    (hc : g.c = .recv peerV)
    (hstdin : g.i.stdin = 3#8 :: rest) :
    rest.length < 2 ^ 32 ∧
      (MainHops.coinsOf g.i).length < 2 ^ 63 ∧
      s.fs.files = runFiles g.i ∧
      S.filesOk (runFiles g.i) (addrValOf peerV) (addrValOf meV) ∧
      (∀ pm, S.pksmParse rest = some pm →
        S.decPkOk (runFiles g.i) (addrValOf peerV) (addrValOf meV) pm) ∧
      g.a = (match S.pksmParse rest with
        | some m => finish (S.decryptPrekey (runFiles g.i) (addrValOf peerV) (addrValOf meV)
            m (MainHops.coinsOf g.i)) id
        | none => some none) := by
  rcases hd.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
    hc ▸ he.parse
  have htail : g.i.stdin.tail.length < 2 ^ 32 := he.rel.2.1.2.2.1 peerV hparse
  rw [hstdin] at htail
  refine ⟨htail, he.rel.2.1.1, hd.fs,
    he.rel.2.2.1 (.recv peerV) peerV ownB meV hparse rfl hget hme,
    fun pm hpm => he.rel.2.2.2.2.1.2 peerV ownB meV rest pm hparse hget hme hstdin hpm, ?_⟩
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  simp [hparse, hget, hme, hstdin]; rfl

theorem AtDispatchPlaced.recvBad_reject [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {peerV : AddrV} {me : MeAtDispatch} {s0 s : State}
    (he : AtRunEntryPlaced CodeOk S g s0)
    (hd : AtDispatchPlaced CodeOk g me s0 s)
    (hc : g.c = .recv peerV)
    (hbad : g.i.stdin = [] ∨ ∃ t rest, g.i.stdin = t :: rest ∧ t ≠ 2#8 ∧ t ≠ 3#8) :
    g.a = some none := by
  cases me with
  | none => exact hd.reject_of_me_none he
  | some meV meG =>
    rcases hd.ownSem with ⟨ownB, hget, hme⟩
    have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
      hc ▸ he.parse
    rw [he.rel.2.2.2.2.2]
    unfold runAns
    rcases hbad with hnil | ⟨t, rest, hcons, ht2, ht3⟩
    · simp [hparse, hget, hme, hnil]
    · simp [hparse, hget, hme, hcons, ht2, ht3]

end CryptoVerification.SignalSession.Cli.RunCompose

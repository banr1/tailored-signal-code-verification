/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.MainOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.LitsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FreeArgsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M6Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseArgsShape
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Relocatable Hop Composer for `main` (`[LibsignalPlacement]`, Block `617`)

Composes the six placed hop continuations (`step1`..`step6`) into `mainSpecTightPlaced` over
`MainCaseB2 Run IsSendOverCap` on Block `617`, and provides `main_ok_tight_compose_m1_m6_placed`
instantiated at `main_m1_placed_proof`, `main_m6_proof_placed`, and `main_ret_placed_proof`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

namespace MainOkPlacedHelpers

theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hQ : ∀ sf Pf, Q sf Pf → Q' sf Pf)
    (h : ProofLib.SepWPp prog ret s P Q Qp oom) :
    ProofLib.SepWPp prog ret s P Q' Qp oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, Pf, hmf, hq⟩ | hpan | hoom
  · exact Or.inl ⟨hpc, hrun, Pf, hmf, hQ sf Pf hq⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hoom)

theorem traceStreamBytes_nil : ProcessOutcome.traceStreamBytes .stdout [] = [] := by
  simp [ProcessOutcome.traceStreamBytes]

theorem post_of_mem {A : RustAlloc} {r : MainResult} {s0 sf : State}
    {stk : Nat} {Pf R : SepProp}
    (hpost : MainPost r s0 sf ∨ allocFailedIn s0 sf)
    (hPf : Pf ⊢ stackAt s0.sp stk ∗ A.pool ∗ anyHeap)
    (hmf : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨ (⌜MainPost r s0 sf ∨ allocFailedIn s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R := by
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hpost, ?_⟩
  rw [← sepConj_assoc]
  exact Satisfies.mono
    (sepConj_mono_left (Entails.trans hPf (sepConj_mono_right (entails_anyHeap _)))) hmf

theorem panic_of_mem {r : MainResult} {s0 sf : State} {Pf R : SepProp}
    (hpan : r = .abort ∨ allocFailedIn s0 sf)
    (hmf : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R := by
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpan, Satisfies.mono (sepConj_mono_left (entails_anyHeap Pf)) hmf⟩

theorem post_of_mem_tight {A : RustAlloc} {r : MainResult} {s0 sf : State}
    {stk : Nat} {Pf R : SepProp}
    (hpost : MainPost r s0 sf)
    (hPf : Pf ⊢ stackAt s0.sp stk ∗ A.pool ∗ anyHeap)
    (hmf : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨ (⌜MainPost r s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R := by
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hpost, ?_⟩
  rw [← sepConj_assoc]
  exact Satisfies.mono
    (sepConj_mono_left (Entails.trans hPf (sepConj_mono_right (entails_anyHeap _)))) hmf

theorem exitK_main_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {r : MainResult} {s0 : State} {stk : Nat} {R : SepProp}
    {G : Nat → State → Prop}
    (hstk : mainFrameSize ≤ stk)
    (hG : ∀ code s, G code s → ∀ sf, sf.trace = s.trace → sf.fs = s.fs →
      (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code →
      MainPost r s0 sf ∨ allocFailedIn s0 sf) :
    ExitKPlaced CodeOk H A s0 stk G
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜MainPost r s0 sf ∨ allocFailedIn s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R)) := by
  intro s code hs hg
  exact sepWPp_mono_post
    (fun sf Pf ⟨hsp, hcs, hx0, htr, hfs, hPf⟩ =>
      ⟨post_of_mem (hG code s hg sf htr hfs hx0) hPf, hsp, hcs⟩)
    (main_ret_placed_proof hstk hs)

theorem exitK_main_tight_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {r : MainResult} {s0 : State} {stk : Nat} {R : SepProp}
    {G : Nat → State → Prop}
    (hstk : mainFrameSize ≤ stk)
    (hG : ∀ code s, G code s → ∀ sf, sf.trace = s.trace → sf.fs = s.fs →
      (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code →
      MainPost r s0 sf) :
    ExitKPlaced CodeOk H A s0 stk G
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜MainPost r s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R)) := by
  intro s code hs hg
  exact sepWPp_mono_post
    (fun sf Pf ⟨hsp, hcs, hx0, htr, hfs, hPf⟩ =>
      ⟨post_of_mem_tight (hG code s hg sf htr hfs hx0) hPf, hsp, hcs⟩)
    (main_ret_placed_proof hstk hs)

end MainOkPlacedHelpers

open MainOkPlacedHelpers in
/-- Composes specialized hop continuations `step1`..`step6` into `mainSpecTightPlaced`
(`MainCaseB2 Run IsSendOverCap`) on Block `617` (`mProgPlaced H`). -/
theorem main_ok_tight_compose_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc}
    {io : IoModel} {Run : Inputs → RunAnswer → Prop} {stk : Nat}
    (hfacts : MainIoFacts io)
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hstk_frame : mainFrameSize ≤ stk)
    (step1 : ∀ {i : Inputs} {s0 : State} {Statics : SepProp} {Q Qp : State → SepProp → Prop}
      {oom : State → SepProp},
      AtEntryPlaced CodeOk i s0 →
      CliInputsOk i →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp →
      (∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64),
        i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
        AtM1EndPlaced CodeOk s0 s i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
          (argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ Statics)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0 (mainFrame A stk Statics i s0)
        Q Qp oom)
    (step2 : ∀ {i : Inputs} {s0 s : State} {buf p0 : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {Statics : SepProp}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      CliInputsOk i → i.argv ≠ [] →
      ps.map (·.2) = i.argv.map bytesOfString →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s' => code = 2 ∧ parseArgs uuidTryParse (i.argv.map bytesOfString) = none ∧
          s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp →
      (∀ (s' : State) (w : CallW) (c : CallV),
        parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
        AtCallPlaced CodeOk s0 s' w i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ Statics)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ Statics)
        Q Qp oom)
    (step3 : ∀ {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
      {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      s0.fs = initFsState (cliInputs i) → s0.trace = [] →
      io.stdin (initFsState (cliInputs i)) = some i.stdin →
      io.pathOk (utf8 "coins") →
      (∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
        r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i)) →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s w i.argv.length buf →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
          (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
        Q Qp →
      (∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64),
        (inputOf i c).length ≤ stdinCapBytes →
        AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
            ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom)
    (step4_overCap : ∀ {i : Inputs} {peer : AddrV} {w : CallW} {s0 s : State}
      {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop},
      stk ≤ s0.sp.toNat →
      s0.trace = [] →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer) →
      1_000_000 < i.stdin.length →
      AtM4Placed CodeOk i s0 s w (.send peer) i.argv.length buf coinsCap coinsPtr inCap →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s' => code = 1 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
          s'.trace = s.trace) Q Qp →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
            (inputOf i (.send peer)) ∗
          callHeap A w (.send peer) ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp (mainOom s0))
    (step4_call : ∀ {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
      {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop},
      stk ≤ s0.sp.toNat →
      s0.trace = [] →
      Run i a → ¬ IsSendOverCap i →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap →
      (∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
          s.trace <+: s'.trace) Q Qp →
      (∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)),
        a = some (some (namedWrites g.writes, out)) →
        (∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) → s.trace <+: s'.trace →
        AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m5CellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ anyHeap)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp (mainOom s0))
    (step5 : ∀ {i : Inputs} {c : CallV} {g : StoresGhost} {out : List (BitVec 8)}
      {s0 s : State} {buf inCap inPtr : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
      {Q Qp : State → SepProp → Prop},
      s0.trace = [] →
      (∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) →
      AtM4EndPlaced CodeOk i s0 s c i.argv.length buf inCap →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      (∀ (s' : State) (ok : Bool) (outCap outPtr : BitVec 64),
        (match commitFiles io.wr s.fs.files g.writes with
         | some F => ok = true ∧ s'.fs.files = F
         | none => ok = false) →
        s.trace <+: s'.trace →
        ProcessOutcome.traceStreamBytes .stdout s'.trace =
          ProcessOutcome.traceStreamBytes .stdout s.trace →
        AtM6Placed CodeOk s0 s' ok i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                (BitVec.ofNat 64 out.length) inCap inPtr) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ anyHeap)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0))
    (step6 : ∀ {s0 s : State} {ok : Bool} {n : Nat}
      {buf outCap outPtr inCap inPtr : BitVec 64}
      {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
      {Q Qp : State → SepProp → Prop},
      AtM6Placed CodeOk s0 s ok n buf →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s' => s'.fs.files = s.fs.files ∧
          (if ok then code = 0 ∧ s.trace <+: s'.trace ∧
              ProcessOutcome.traceStreamBytes .stdout s'.trace =
              ProcessOutcome.traceStreamBytes .stdout s.trace ++ out
           else code = 2 ∧ s'.trace = s.trace)) Q Qp →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    subroutine_ok (mProgPlaced H) (lsmpl.base 617)
      (mainSpecTightPlaced CodeOk A stk cliStaticsPlaced Run) := by
  apply subroutine_ok_of_sepWPp_init
  intro ⟨i, r⟩ R s0 hpc hrun0 hpre hal
  simp only [mainSpecTightPlaced, MainEntryFacts, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hCO, hcase, hok, ⟨hargc, hfs0, htr0⟩, hsp⟩, hm⟩ := hpre
  refine ⟨mainFrame A stk cliStaticsPlaced i s0, ?_, ?_⟩
  · simpa only [mainFrame, sepConj_assoc] using hm
  · apply sepWPp_mainFrame_mainLitsPlaced (hCI.toRoCl hCO).2
    change SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
      (mainFrame A stk (cliStaticsPlaced ∗ mainLitsBlk617) i s0)
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜MainPost r s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R))
      (mainOom s0)
    have hs0 : AtEntryPlaced CodeOk i s0 :=
      { pc := by rw [hpc]; exact (BitVec.add_zero (lsmpl.base 617)).symm
        run := hrun0
        inv := hCO
        argc := hargc
        spAligned := hal }
    have hpanicA : ∀ (sf : State) (Pf : SepProp), allocFailedIn s0 sf →
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (⌜r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R)) :=
      fun _ _ ha => panic_of_mem (Or.inr ha)
    cases hcase with
    | usage hascii hshape =>
      have hfail : parseArgs uuidTryParse (i.argv.map bytesOfString) = none :=
        parseArgs_none_of_shape_proof uuidTryParse hascii hshape
      have hexit2 : ExitKPlaced CodeOk H A s0 stk
          (fun code s => code = 2 ∧ s.trace = s0.trace ∧ s.fs = s0.fs)
          (fun sf Pf =>
            ((sf.mem ⊨ Pf ∗ R) →
              (sf.mem ⊨ (⌜MainPost (.ret 2 [] []) s0 sf⌝ ∗
                stackAt s0.sp stk ∗ anyHeap) ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf Pf =>
            (sf.mem ⊨ Pf ∗ R) →
              (sf.mem ⊨ (⌜(.ret 2 [] [] : MainResult) = .abort ∨ allocFailedIn s0 sf⌝ ∗
                anyHeap) ∗ R)) :=
        exitK_main_tight_placed hstk_frame fun code s ⟨hcode, htr_s, hfs_s⟩ sf htr_f hfs_f hx0 =>
          ⟨2, [], [], rfl,
            hx0.trans (congrArg (BitVec.ofNat 32) hcode),
            congrArg FsState.files (hfs_f.trans hfs_s),
            by rw [htr_f, htr_s, htr0]; exact traceStreamBytes_nil⟩
      refine step1 hs0 hok hpanicA
        (fun s code hs ⟨hcode, _, htr_s, hfs_s⟩ => hexit2 s code hs ⟨hcode, htr_s, hfs_s⟩) ?_
      intro s1 buf ps p0 hne hps hs1
      refine step2 (p0 := p0) hok hne hps hs1 hpanicA
        (fun s' code hs' ⟨hcode, _, htr_s, hfs_s⟩ => hexit2 s' code hs' ⟨hcode, htr_s, hfs_s⟩) ?_
      intro _ _ _ hpc_parse _
      exact (nomatch hfail.symm.trans hpc_parse)
    | stdinOverCap hover =>
      obtain ⟨⟨c0, hparse_c0, htag_c0⟩, hgt_stdin⟩ := hover
      refine step1 hs0 hok hpanicA ?_ ?_
      · intro s code _ ⟨_, hnil, _, _⟩
        rw [hnil] at hparse_c0
        cases hparse_c0
      · intro s1 buf ps p0 hne hps hs1
        refine step2 (p0 := p0) hok hne hps hs1 hpanicA ?_ ?_
        · intro s' code _ ⟨_, hnone, _, _⟩
          rw [hnone] at hparse_c0
          cases hparse_c0
        · intro s2 w c hpc_parse hs2
          have hc_eq : c = c0 := Option.some.inj (hpc_parse.symm.trans hparse_c0)
          subst hc_eq
          refine step3 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
            (hfacts.coins i hok) hparse_c0 hs2 hpanicA ?_ ?_
          · refine exitK_main_tight_placed hstk_frame
              fun code s' ⟨hcode, hfiles', _, htr'⟩ sf htr_f hfs_f hx0 => ?_
            refine ⟨2, [], [], rfl,
              hx0.trans (congrArg (BitVec.ofNat 32) hcode), ?_, ?_⟩
            · rw [hfs_f, hfiles', hfs0]; rfl
            · rw [htr_f, htr', hs2.trace, htr0]
              exact traceStreamBytes_nil
          · intro _ _ _ _ _ hin_le _
            simp only [inputOf, htag_c0, ↓reduceIte] at hin_le
            omega
    | sendOverCap hover hnstin hcr =>
      obtain ⟨⟨peer, hparse_send⟩, hlen_gt⟩ := hover
      refine step1 hs0 hok hpanicA ?_ ?_
      · intro s code _ ⟨_, hnil, _, _⟩
        rw [hnil] at hparse_send
        cases hparse_send
      · intro s1 buf ps p0 hne hps hs1
        refine step2 (p0 := p0) hok hne hps hs1 hpanicA ?_ ?_
        · intro s' code _ ⟨_, hnone, _, _⟩
          rw [hnone] at hparse_send
          cases hparse_send
        · intro s2 w c hpc_parse hs2
          have hc_eq : c = .send peer := Option.some.inj (hpc_parse.symm.trans hparse_send)
          subst hc_eq
          refine step3 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
            (hfacts.coins i hok) hparse_send hs2 hpanicA ?_ ?_
          · intro s' code _ ⟨_, _, hex_or, _⟩
            rcases hex_or with hncr | ⟨htag, hgt⟩
            · exact absurd hcr hncr
            · exact absurd ⟨⟨.send peer, hparse_send, htag⟩, hgt⟩ hnstin
          · intro s3 coinsCap coinsPtr inCap inPtr _ hs3
            refine step4_overCap hsp htr0 hparse_send hlen_gt hs3 hpanicA ?_
            refine exitK_main_tight_placed hstk_frame
              fun code s' ⟨hcode, hfiles', htr'⟩ sf htr_f hfs_f hx0 => ?_
            refine ⟨1, [], [], rfl,
              hx0.trans (congrArg (BitVec.ofNat 32) hcode), ?_, ?_⟩
            · rw [hfs_f, hfiles', hfs0]
              rfl
            · rw [htr_f, htr', hs3.trace, htr0]
              exact traceStreamBytes_nil
    | @call a hRun hnover hnstin hcr hco =>
      have hsome : (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome :=
        hparse i a hRun
      refine step1 hs0 hok hpanicA ?_ ?_
      · intro s code _ ⟨_, hnil, _, _⟩
        rw [hnil] at hsome
        cases hsome
      · intro s1 buf ps p0 hne hps hs1
        refine step2 (p0 := p0) hok hne hps hs1 hpanicA ?_ ?_
        · intro s' code _ ⟨_, hnone, _, _⟩
          rw [hnone] at hsome
          cases hsome
        · intro s2 w c hpc_parse hs2
          refine step3 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
            (hfacts.coins i hok) hpc_parse hs2 hpanicA ?_ ?_
          · intro s' code _ ⟨_, _, hex_or, _⟩
            rcases hex_or with hncr | ⟨htag, hgt⟩
            · exact absurd hcr hncr
            · exact absurd ⟨⟨c, hpc_parse, htag⟩, hgt⟩ hnstin
          · intro s3 coinsCap coinsPtr inCap inPtr _ hs3
            refine step4_call hsp htr0 hRun hnover hpc_parse hs3 ?_ ?_ ?_
            · intro sf Pf hpan
              rcases hpan with rfl | ha
              · exact panic_of_mem (Or.inl rfl)
              · exact panic_of_mem (Or.inr ha)
            · refine exitK_main_tight_placed hstk_frame
                fun code s' ⟨hcode, ha_eq, ⟨hfiles', hstdout'⟩, _⟩ sf htr_f hfs_f hx0 => ?_
              subst ha_eq
              refine ⟨1, [], [], rfl,
                hx0.trans (congrArg (BitVec.ofNat 32) hcode), ?_, ?_⟩
              · rw [hfs_f, hfiles', hfs0]
                rfl
              · rw [htr_f, hstdout']
            · intro s4 g out hans hwr _ hs4
              subst hans
              refine step5 htr0 hwr hs4.toAtM4EndPlaced hpanicA ?_
              · intro s5 ok outCap outPtr hcommit htr45 hstdout5 hs5
                refine step6 hs5 ?_
                · refine exitK_main_tight_placed hstk_frame
                    fun code s6 ⟨hfiles6, hbr6⟩ sf htr_f hfs_f hx0 => ?_
                  rcases hs4.hist with ⟨hfiles4, hstdout4⟩
                  have hcf :
                      commitFiles io.wr (initFsState (cliInputs i)).files g.writes =
                        some (MainPost.writeAll (initFsState (cliInputs i))
                          (namedWrites g.writes)).files :=
                    hfacts.commit i hok g.writes (fun pw hpw => (hwr pw hpw).1) hco
                  rw [hfiles4, hcf] at hcommit
                  obtain ⟨hok_eq, hfiles5⟩ := hcommit
                  subst hok_eq
                  obtain ⟨hcode, _, hstdout6⟩ := hbr6
                  refine ⟨0, namedWrites g.writes, out, rfl,
                    hx0.trans (congrArg (BitVec.ofNat 32) hcode), ?_, ?_⟩
                  · rw [hfs_f, hfiles6, hfiles5, hfs0]
                  · rw [htr_f, hstdout6, hstdout5, hstdout4, List.nil_append]

/-- Instantiates `main_ok_tight_compose_placed` at `main_m1_placed_proof`, `main_m6_proof_placed`,
and `main_ret_placed_proof`. -/
theorem main_ok_tight_compose_m1_m6_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc}
    {io : IoModel} {Run : Inputs → RunAnswer → Prop} {stk hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidTryParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack) (hfacts : MainIoFacts io)
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (step2 : ∀ {i : Inputs} {s0 s : State} {buf p0 : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {Statics : SepProp}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      CliInputsOk i → i.argv ≠ [] →
      ps.map (·.2) = i.argv.map bytesOfString →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s' => code = 2 ∧ parseArgs uuidTryParse (i.argv.map bytesOfString) = none ∧
          s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp →
      (∀ (s' : State) (w : CallW) (c : CallV),
        parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
        AtCallPlaced CodeOk s0 s' w i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ Statics)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ Statics)
        Q Qp oom)
    (step3 : ∀ {i : Inputs} {c : CallV} {w : CallW} {s0 s : State}
      {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      s0.fs = initFsState (cliInputs i) → s0.trace = [] →
      io.stdin (initFsState (cliInputs i)) = some i.stdin →
      io.pathOk (utf8 "coins") →
      (∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
        r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i)) →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s w i.argv.length buf →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
          (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
        Q Qp →
      (∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64),
        (inputOf i c).length ≤ stdinCapBytes →
        AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
            ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
          Q Qp oom) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom)
    (step4_overCap : ∀ {i : Inputs} {peer : AddrV} {w : CallW} {s0 s : State}
      {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop},
      stk ≤ s0.sp.toNat →
      s0.trace = [] →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer) →
      1_000_000 < i.stdin.length →
      AtM4Placed CodeOk i s0 s w (.send peer) i.argv.length buf coinsCap coinsPtr inCap →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s' => code = 1 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
          s'.trace = s.trace) Q Qp →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
            (inputOf i (.send peer)) ∗
          callHeap A w (.send peer) ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp (mainOom s0))
    (step4_call : ∀ {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
      {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop},
      stk ≤ s0.sp.toNat →
      s0.trace = [] →
      Run i a → ¬ IsSendOverCap i →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap →
      (∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
          s.trace <+: s'.trace) Q Qp →
      (∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)),
        a = some (some (namedWrites g.writes, out)) →
        (∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) → s.trace <+: s'.trace →
        AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m5CellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ anyHeap)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp (mainOom s0))
    (step5 : ∀ {i : Inputs} {c : CallV} {g : StoresGhost} {out : List (BitVec 8)}
      {s0 s : State} {buf inCap inPtr : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
      {Q Qp : State → SepProp → Prop},
      s0.trace = [] →
      (∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32) →
      AtM4EndPlaced CodeOk i s0 s c i.argv.length buf inCap →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      (∀ (s' : State) (ok : Bool) (outCap outPtr : BitVec 64),
        (match commitFiles io.wr s.fs.files g.writes with
         | some F => ok = true ∧ s'.fs.files = F
         | none => ok = false) →
        s.trace <+: s'.trace →
        ProcessOutcome.traceStreamBytes .stdout s'.trace =
          ProcessOutcome.traceStreamBytes .stdout s.trace →
        AtM6Placed CodeOk s0 s' ok i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
            locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
                (BitVec.ofNat 64 out.length) inCap inPtr) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ anyHeap)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    subroutine_ok (mProgPlaced H) (lsmpl.base 617)
      (mainSpecTightPlaced CodeOk A stk cliStaticsPlaced Run) :=
  main_ok_tight_compose_placed hfacts hparse
    (Nat.le_trans (Nat.le_add_right mainFrameSize _) hstk)
    (fun hs0 hok hp hex hn => main_m1_placed_proof hc hstk hstk64 hs0 hok hp hex hn)
    step2 step3 step4_overCap step4_call step5
    (fun hs5 hex => main_m6_proof_placed hc hio hstk hstk64 hs5 hex)

end CryptoVerification.SignalSession.Cli.MainHops

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DirStepPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable M5 Outer Commit Loop (`M+0x8b8 .. M+0xae0 → M+0xf70`, Block `617`)

Verifies `Stores::commit`'s 8-`Dir` outer induction (`m5_loop_from_placed`, `m5_loop_placed`) and
completion hop into `AtM6Placed … true` on Block `617` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops

open LoopDrop

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open Arm64.Process
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint DoReserveNorm
open CryptoVerification.SignalSession.Cli.Path.Helpers

attribute [local irreducible] SepWPp Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace LoopDrop

/-! ## Outer Induction (`m5_loop_from_placed`) & Top-Level `m5_loop_placed` -/

set_option maxHeartbeats 1600000 in
/-- Run remaining `8 - k` `Dir`s from `AtM5LoopPlaced … k` (`k ≤ 8`) through `M+0xadc -> M+0xc5c -> M+0xf70`. -/
theorem m5_loop_from_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n : Nat}
    {outCap outPtr inCap inPtr buf : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 : State} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack)
    (hs0tr : s0.trace = [])
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (herr : ∀ (k : Nat) (se : State) (errE : M5ErrEntryPlaced) (curCap curPtr : BitVec 64)
        (curEntries : List (List (BitVec 8) × List (BitVec 8))),
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k curEntries errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced A s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          curEntries errE)
        Q Qp (mainOom s0))
    (hok : ∀ s' : State,
      commitFiles io.wr F0 g.writes = some s'.fs.files →
      tr0 <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      AtM6Placed CodeOk s0 s' true n buf →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s'
        (ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
              outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ∀ (rem k : Nat) (s : State),
      rem + k = 8 →
      AtM5LoopPlaced CodeOk io F0 tr0 g s0 s n buf k →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
        (m5LoopMemPlaced A s0 stk n outCap outPtr inCap inPtr buf out inp ps g k)
        Q Qp (mainOom s0) := by
  intro rem; induction rem with
  | zero =>
    intro k s hrem hs
    have hk8 : k = 8 := by m5_omega
    subst hk8; exact m5_done_placed hs hok
  | succ rem ih =>
    intro k s hrem hs
    have hk : k < 8 := by m5_omega
    exact m5_dir_step_placed hc hio hs0tr hpanic hstk hstk64 hk hpaths hs (herr k) fun sf hsf =>
      ih (k + 1) sf (by m5_omega) hsf

end LoopDrop

set_option maxHeartbeats 1600000 in
/-- Executes `Stores::commit`'s 8-`Dir` outer and inner loops (`M+0x8b8 .. M+0xae0`) and completion
hop (`M+0xadc -> M+0xc5c -> M+0xf70`), handing write errors at `M+0xbcc` / `M+0xbdc` / `M+0xbf4` to
`herr`, OOM panics to `hpanic`, and full commit completion to `hok` at `AtM6Placed … true`. -/
theorem m5_loop_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser} {io : IoModel}
    {F0 : FsFiles} {tr0 : List TraceEvent} {g : StoresGhost}
    {hookStack resStack stk n : Nat}
    {outCap outPtr inCap inPtr buf : BitVec 64}
    {out inp : List (BitVec 8)} {ps : List (BitVec 64 × List (BitVec 8))}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0tr : s0.trace = [])
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hs : AtM5LoopPlaced CodeOk io F0 tr0 g s0 s n buf 0)
    (hP : P ⊢ m5LoopMemPlaced A s0 stk n outCap outPtr inCap inPtr buf out inp ps g 0)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (herr : ∀ (k : Nat) (se : State) (errE : M5ErrEntryPlaced) (curCap curPtr : BitVec 64)
        (curEntries : List (List (BitVec 8) × List (BitVec 8))),
      M5LoopErrPlaced CodeOk io F0 tr0 g s0 se n buf k curEntries errE →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) se
        (m5ErrMemPlaced A s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k
          curEntries errE)
        Q Qp (mainOom s0))
    (hok : ∀ s' : State,
      commitFiles io.wr F0 g.writes = some s'.fs.files →
      tr0 <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      AtM6Placed CodeOk s0 s' true n buf →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s'
        (ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize)
              outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) :=
  SepWPp.weaken_pre hP
    (m5_loop_from_placed hc hio hs0tr hpanic hstk hstk64 hpaths herr hok 8 0 s rfl hs)

end CryptoVerification.SignalSession.Cli.MainHops

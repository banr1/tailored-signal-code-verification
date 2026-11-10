/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5MovesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `main` Hop M5 (`M+0x7b0 → M+0xf70`, Block `617`)

Composes `m5_moves_placed`, `m5_loop_placed`, and `m5_drop_for_m5_placed` into `main_m5_proof_placed`
(`M+0x7b0 → M+0xf70`) on Block `617` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Relocatable M5 hop (`M+0x7b0 → M+0xf70`): `m5_moves_placed` up to `AtM5LoopPlaced … 0`
(`M+0x8b8`), then `m5_loop_placed` across all 8 `Dir`s (`AtM6Placed … true`), with
`m5_drop_for_m5_placed` handling any `write_file` failure (`AtM6Placed … false`). -/
theorem main_m5_proof_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc}
    {uuidParse : UuidParser} {io : IoModel} {i : Inputs} {c : CallV} {g : StoresGhost}
    {out : List (BitVec 8)} {s0 s : State} {stk hookStack resStack : Nat}
    {buf inCap inPtr : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0tr : s0.trace = [])
    (hpaths : ∀ pw ∈ g.writes, io.pathOk pw.1 ∧ pw.1.length < 2 ^ 32)
    (hs : AtM4EndPlaced CodeOk i s0 s c i.argv.length buf inCap)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hnext : ∀ (s' : State) (ok : Bool) (outCap outPtr : BitVec 64),
      (match commitFiles io.wr s.fs.files g.writes with
       | some F => ok = true ∧ s'.fs.files = F
       | none => ok = false) →
      s.trace <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout s.trace →
      AtM6Placed CodeOk s0 s' ok i.argv.length buf →
      ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s'
        (ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s
      (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5CellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ anyHeap)
      Q Qp (mainOom s0) := by
  have hext : mainFrameSize + extHookStack ≤ stk := by omega
  exact m5_moves_placed (inp := inputOf i c) (n := i.argv.length) (io := io) (g := g) (out := out)
    (ps := ps) hc.allocFs hext hs
    (fun _s1 outCap outPtr _hfs _htr hloop =>
      m5_loop_placed (F0 := s.fs.files) (tr0 := s.trace) hc hio hstk hstk64 hs0tr hpaths
        hloop (Entails.refl _) hpanic
        (fun _k _se _e _curCap _curPtr _curEntries herr =>
          m5_drop_for_m5_placed (s := s) (i := i) (c := c) hc.allocFs hext herr hnext)
        (fun s' hcommit hpre hstdout hat6 =>
          hnext s' true outCap outPtr (by rw [hcommit]; exact ⟨rfl, rfl⟩) hpre hstdout hat6))

end CryptoVerification.SignalSession.Cli.MainHops

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve

/-!
# Budget-Threaded In-Image Callee Contracts for `signal-session` `main`

`RustCliAllocBudget` counterparts of `addressSpec`, `reserve16Spec`, and `tryAllocateInSpecOf`
paired with their deterministic `AllocEvent` envelopes (`AddressEnv`, `Reserve16Env`,
`TryAllocateInEnv`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEnv FitsEvents
   NullAllowed OomPreserved rustAllocEvents rustReallocEvents)
open CryptoVerification.RustHeap (LayoutOk allocFailedEvent)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser protocolAddressAt)
open CryptoVerification.E2E.Pqxdh.Shared (TryAllocateInCall)
open CryptoVerification.SpqrV1.Alloc (reserveCapStride)
open CryptoVerification.SignalSession.Cli.MainHops (AddressCall Reserve16Call addrParse vec16At)

/-! ## `signal_session::address` -/

/-- Deterministic `AllocEvent` list emitted by `signal_session::address`:
`[]` when `addrParse` returns `none`, else `rustAllocEvents a.name.length 1` for the owned name. -/
def addressEvents (uuidParse : UuidParser) (bs : List (BitVec 8)) : List AllocEvent :=
  match addrParse uuidParse bs with
  | none => []
  | some a => rustAllocEvents a.name.length 1

def AddressEnv (uuidParse : UuidParser) (x : AddressCall) (evs : List AllocEvent) : Prop :=
  evs = addressEvents uuidParse x.bs

theorem addressEnv_events (uuidParse : UuidParser) (x : AddressCall) :
    AddressEnv uuidParse x (addressEvents uuidParse x.bs) :=
  rfl

theorem fitsEvents_address_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    (uuidParse : UuidParser) (x : AddressCall)
    (h : FitsEnv M lim st (AddressEnv uuidParse x)) :
    FitsEvents M lim st (addressEvents uuidParse x.bs) :=
  h (addressEvents uuidParse x.bs) rfl

def addressSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (uuidParse : UuidParser) (resStack : Nat) : Spec (AddressCall × M.σ) where
  pre := fun (x, st) s0 =>
    ⌜s0.readReg64 .x0 = x.out ∧ s0.readReg64 .x1 = x.p ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧
      FitsEnv M lim st (AddressEnv uuidParse x)⌝ ∗
      (x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ A.pool lim st s0 ∗ stackAt s0.sp resStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs ∧ AddressEnv uuidParse x evs⌝ ∗
        (x.p ↦ₛ x.bs) ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp resStack ∗
        (match addrParse uuidParse x.bs with
         | none => (x.out ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.out + 8#64) 24
         | some a => ∃∗ g : AddrGhost,
             ⌜g.name.bytes = a.name ∧ g.name.cap = BitVec.ofNat 64 a.name.length ∧
               g.device = a.device⌝ ∗ protocolAddressAt A.repAlloc g x.out)

/-! ## `do_reserve_and_handle` (`reserve16Spec`) -/

/-- Deterministic `AllocEvent` list emitted by `reserve16` (`additional = 1`, `stride = 16`, `align = 8`). -/
def reserve16Events (x : Reserve16Call) : List AllocEvent :=
  let new := reserveCapStride 16 x.cap.toNat (x.bs.length / 16) 1
  if x.cap = 0#64 then
    rustAllocEvents (16 * new) 8
  else
    rustReallocEvents (16 * x.cap.toNat) (16 * new) 8

def Reserve16Env (x : Reserve16Call) (evs : List AllocEvent) : Prop :=
  evs = reserve16Events x

theorem reserve16Env_events (x : Reserve16Call) :
    Reserve16Env x (reserve16Events x) :=
  rfl

theorem fitsEvents_reserve16_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    (x : Reserve16Call) (h : FitsEnv M lim st (Reserve16Env x)) :
    FitsEvents M lim st (reserve16Events x) :=
  h (reserve16Events x) rfl

def reserve16Spec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (resStack : Nat) : Spec (Reserve16Call × M.σ) where
  pre := fun (x, st) s0 =>
    ⌜s0.readReg64 .x0 = x.v ∧ s0.readReg64 .x1 = BitVec.ofNat 64 (x.bs.length / 16) ∧
      s0.readReg64 .x2 = 1#64 ∧ s0.readReg64 .x3 = 8#64 ∧ s0.readReg64 .x4 = 16#64 ∧
      16 * (x.bs.length / 16 + 1) < 2 ^ 62 ∧ 16 * x.cap.toNat < 2 ^ 62 ∧
      FitsEnv M lim st (Reserve16Env x)⌝ ∗
      vec16At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s0 ∗ stackAt s0.sp resStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs ∧ Reserve16Env x evs⌝ ∗
        (∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
          ⌜x.bs.length / 16 + 1 ≤ cap'.toNat⌝ ∗ vec16At A.repAlloc x.v cap' p' x.bs) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp resStack

/-! ## `try_allocate_in` (`tryAllocateInSpecOf`) -/

def tryAllocateInEvents (x : TryAllocateInCall) : List AllocEvent :=
  rustAllocEvents (x.new.toNat * x.stride.toNat) x.align.toNat

def TryAllocateInEnv (x : TryAllocateInCall) (evs : List AllocEvent) : Prop :=
  evs = tryAllocateInEvents x

theorem tryAllocateInEnv_events (x : TryAllocateInCall) :
    TryAllocateInEnv x (tryAllocateInEvents x) :=
  rfl

theorem fitsEvents_tryAllocateIn_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    (x : TryAllocateInCall) (h : FitsEnv M lim st (TryAllocateInEnv x)) :
    FitsEvents M lim st (tryAllocateInEvents x) :=
  h (tryAllocateInEvents x) rfl

/-- Total-correctness (`FitsEnv`) contract of `try_allocate_in`: under `LayoutOk` and `FitsEnv`,
`__rust_alloc` cannot return null, so the `Err(AllocError)` (`tag = 1`) branch is dead. -/
def tryAllocateInSpecOf {M : AllocCostModel} (resStack : Nat) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TryAllocateInCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.new ∧
      s.readReg64 .x2 = x.align ∧ s.readReg64 .x3 = x.stride ∧
      0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
      FitsEnv M lim st (TryAllocateInEnv x)⌝ ∗
    memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp resStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ x.new) ∗ ((x.out + 16#64) ↦₆₄ p') ∗
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace ∧
        TryAllocateInEnv x evs⌝ ∗
      A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗
      memRegion p' (x.new.toNat * x.stride.toNat) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp resStack

/-- Conditional-OOM variant of `tryAllocateInSpecOf` without `FitsEnv` in `pre`. -/
def tryAllocateInCondSpecOf {M : AllocCostModel} (resStack : Nat) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TryAllocateInCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.new ∧
      s.readReg64 .x2 = x.align ∧ s.readReg64 .x3 = x.stride ∧
      0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
    memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp resStack
  post := fun (x, st) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗
      (if tag = 1#64 then
        ((x.out + 8#64) ↦₆₄ x.align) ∗
        ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
        ⌜NullAllowed (x.new.toNat * x.stride.toNat) x.align.toNat ∧
          p' = 0#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        A.pool lim st sf
       else
        ((x.out + 8#64) ↦₆₄ x.new) ∗
        ((x.out + 16#64) ↦₆₄ p') ∗
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗
          memRegion p' (x.new.toNat * x.stride.toNat) ∗
          A.pool lim (M.stepEvents (tryAllocateInEvents x) st) sf) ∗
      stackAt s0.sp resStack
  onOom := fun (x, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (tryAllocateInEvents x) ∧ OomPreserved s0 sf⌝

end LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget

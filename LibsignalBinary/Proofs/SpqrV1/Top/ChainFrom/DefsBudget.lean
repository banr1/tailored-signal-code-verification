/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Defs

/-!
# Budget-Threaded Specifications for `spqr::chain_from` and `<Chain>::from_pb`

`RustCliAllocBudget` specifications (`chainFromPbSpecX`, `chainFromSpecX`, `chainFromSpecExt`)
with `ChainFromEnv` (`FreeOnlyEvs` + optional 32-byte `Chain::new` root-key allocation).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.LibsignalSpqrV1
  (Chain ChainPB Direction HkdfFn VersionNegotiationPB chainFrom)
open CryptoVerification.LibsignalTripleRatchet
  (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
  (chainResultAt)
open CryptoVerification.SpqrV1.Top.ChainFrom
  (ChainFromCall ChainFromPbCall chainFromName chainFromPbName chainFromPbStackX
   chainFromStackExt chainFromStackX chainPBAt optChainPBAt optVersionNegotiationRefAt)

/-- Deterministic `AllocEvent` list emitted by `<spqr::chain::Chain>::new` (`0x5fea4`):
four `Vec<u8>` allocations (`72, 32, 72, 32`), initial `<VecDeque<ChainEpoch>>::grow`
from `0` to `4` (`4 * 112 = 448`, align `8`), and the 32-byte `next_root` `Vec<u8>`. -/
def chainNewEvents : List AllocEvent :=
  rustAllocEvents 72 1 ++ rustAllocEvents 32 1 ++
  rustAllocEvents 72 1 ++ rustAllocEvents 32 1 ++
  rustAllocEvents 448 8 ++ rustAllocEvents 32 1

/-- Allocation envelope of `spqr::chain_from_version_negotiation`:
`chainNewEvents` when `Direction.fromI32? v.direction` and `v.chainParams` are both `some`,
otherwise `[]`. -/
def ChainFromVersionNegotiationEnv (v : VersionNegotiationPB) (evs : List AllocEvent) : Prop :=
  if (Direction.fromI32? v.direction).isSome && v.chainParams.isSome then
    evs = chainNewEvents
  else
    evs = []

/-- Precondition allocation envelope of `spqr::chain_from` (only the `pb = none, vn = some v`
branch allocates; `pb = some _` only deallocates via `Chain::from_pb`). -/
def ChainFromAllocEnv (pb : Option ChainPB) (vn : Option VersionNegotiationPB)
    (evs : List AllocEvent) : Prop :=
  match pb, vn with
  | none, some v => ChainFromVersionNegotiationEnv v evs
  | _, _ => evs = []

/-- Full postcondition event envelope of `spqr::chain_from`:
- `pb = some _`: `FreeOnlyEvs evs` (`Chain::from_pb` converts in place and only deallocates);
- `pb = none, vn = some v`: `ChainFromVersionNegotiationEnv v evs`;
- `pb = none, vn = none`: `evs = []`. -/
def ChainFromEnv (pb : Option ChainPB) (vn : Option VersionNegotiationPB)
    (evs : List AllocEvent) : Prop :=
  match pb, vn with
  | some _, _ => FreeOnlyEvs evs
  | none, some v => ChainFromVersionNegotiationEnv v evs
  | none, none => evs = []

theorem chainFromAllocEnv_imp_chainFromEnv {pb : Option ChainPB}
    {vn : Option VersionNegotiationPB} {evs : List AllocEvent}
    (h : ChainFromAllocEnv pb vn evs) :
    ChainFromEnv pb vn evs := by
  cases pb with
  | some _ =>
    dsimp only [ChainFromAllocEnv] at h
    subst h
    exact FreeOnlyEvs.nil
  | none =>
    cases vn <;> exact h

theorem fitsEnv_chainFromAllocEnv_of_chainFromEnv {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {pb : Option ChainPB}
    {vn : Option VersionNegotiationPB}
    (h : FitsEnv M lim st (ChainFromEnv pb vn)) :
    FitsEnv M lim st (ChainFromAllocEnv pb vn) :=
  FitsEnv.mono (fun _ => chainFromAllocEnv_imp_chainFromEnv) h

/-- Unplaced base spec of `<spqr::chain::Chain>::from_pb` (`FreeOnlyEvs`, `onPanic = ⌜False⌝`,
`onOom = ⌜False⌝`, no `FitsEnv` precondition required). -/
def chainFromPbSpecXBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ChainFromPbCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbPtr⌝ ∗
      memRegion x.out 88 ∗ chainPBAt A.repAlloc x.gPb x.pbPtr x.pb ∗
      A.pool lim st s ∗ stackAt s.sp chainFromPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      chainResultAt A.repAlloc x.out (Chain.fromPb x.pb) ∗
      memRegion x.pbPtr 80 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainFromPbStackX

/-- Budget-threaded spec of `<spqr::chain::Chain>::from_pb` (`FreeOnlyEvs`, `onPanic = ⌜False⌝`,
`onOom = ⌜False⌝`, no `FitsEnv` precondition required). -/
def chainFromPbSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (ChainFromPbCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbPtr ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.out 88 ∗ chainPBAt A.repAlloc x.gPb x.pbPtr x.pb ∗
      A.pool lim st s ∗ stackAt s.sp chainFromPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      chainResultAt A.repAlloc x.out (Chain.fromPb x.pb) ∗
      memRegion x.pbPtr 80 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainFromPbStackX

/-- `<spqr::chain::Chain>::from_pb` meets `(chainFromPbSpecXBase M A lim).inImage img` on
`tripleRatchetProgAtExt img.base ext`. -/
def ChainFromPbOkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainFromPbName)
    ((chainFromPbSpecXBase M A lim).inImage img)

/-- Budget-threaded spec of `spqr::chain_from` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chainFromSpecX (hkdf : HkdfFn) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (ChainFromCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbPtr ∧ s.readReg64 .x2 = x.vnOptPtr ∧
      FitsEnv M lim st (ChainFromAllocEnv x.pb x.vn)⌝ ∗
      memRegion x.out 88 ∗
      optChainPBAt A.repAlloc x.gPb x.pbPtr x.pb ∗
      optVersionNegotiationRefAt A.repAlloc x.vnPin x.vnOptPtr x.vn ∗
      A.pool lim st s ∗ stackAt s.sp chainFromStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ ChainFromEnv x.pb x.vn evs⌝ ∗
      chainResultAt A.repAlloc x.out (chainFrom hkdf x.pb x.vn) ∗
      memRegion x.pbPtr 80 ∗
      optVersionNegotiationRefAt A.repAlloc x.vnPin x.vnOptPtr x.vn ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainFromStackX

/-- `spqr::chain_from` meets `(chainFromSpecX hkdf M A lim).inImage img` on
`tripleRatchetProgAtExt img.base ext`. -/
def ChainFromOkX (img : Obj.Image) (hkdf : HkdfFn) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainFromName)
    ((chainFromSpecX hkdf M A lim).inImage img)

/-- Budget-threaded contract-backed (`chainFromStackExt`) spec of `spqr::chain_from`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chainFromSpecExt (hkdf : HkdfFn) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (ChainFromCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbPtr ∧ s.readReg64 .x2 = x.vnOptPtr ∧
      FitsEnv M lim st (ChainFromAllocEnv x.pb x.vn)⌝ ∗
      memRegion x.out 88 ∗
      optChainPBAt A.repAlloc x.gPb x.pbPtr x.pb ∗
      optVersionNegotiationRefAt A.repAlloc x.vnPin x.vnOptPtr x.vn ∗
      A.pool lim st s ∗ stackAt s.sp chainFromStackExt
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ ChainFromEnv x.pb x.vn evs⌝ ∗
      chainResultAt A.repAlloc x.out (chainFrom hkdf x.pb x.vn) ∗
      memRegion x.pbPtr 80 ∗
      optVersionNegotiationRefAt A.repAlloc x.vnPin x.vnOptPtr x.vn ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainFromStackExt

/-- Contract-backed callee-contract predicate for `spqr::chain_from` (`0x531ac`). -/
def ChainFromOkExt (img : Obj.Image) (hkdf : HkdfFn) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainFromName)
    ((chainFromSpecExt hkdf M A lim).inImage img)

end LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget

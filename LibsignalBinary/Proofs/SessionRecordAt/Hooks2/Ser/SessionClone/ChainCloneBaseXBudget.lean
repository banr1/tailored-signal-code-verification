/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseX

/-!
# Budget-Threaded `Chain::clone [local#1]` Envelopes and Specifications (Block `82`)

Defines deterministic `AllocEvent` traces (`chainCloneEvents`, `senderChainCloneEvents`), envelopes
(`ChainCloneEnv`, `SenderChainCloneEnv`), and budget-threaded specifications (`protoChainCloneSpecX`,
`chainCloneSpecX`, `senderChainCloneSpecX`) at `chainCloneStackX` for Block `82`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ReceiverChain SenderChain)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl LibsignalCodeLoaded withLsCodeLoaded sepWP_mono_lscl
)
open CryptoVerification.E2E.Record.Placed (lsProg_82 blkPl_82)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SenderChainGhost optSenderChainAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (
  ChainCloneGhost SenderChainCloneGhost
)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (
  protoChainAt chainCloneStackX
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEvents FitsEnv rustAllocEvents
)

/-! ## Deterministic `AllocEvent` traces and envelopes -/

/-- Deterministic `AllocEvent` sequence emitted by `<session_structure::Chain as Clone>::clone`
    in execution order:
    1. `sender_ratchet_key` (`len > 0` → `rustAllocEvents len 1`);
    2. `sender_ratchet_key_private` (`len > 0` → `rustAllocEvents len 1`);
    3. `chain_key` (`some _` → `rustAllocEvents 32 1`);
    4. `message_keys` (`nonempty` → `rustAllocEvents (104 * len) 8` followed by `len` per-element
       `seed` allocations `rustAllocEvents mkg.seed.length 1`). -/
def chainCloneEvents (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  (if gc.1.srk.bytes.length = 0 then [] else rustAllocEvents gc.1.srk.bytes.length 1) ++
  (if gc.1.priv.bytes.length = 0 then [] else rustAllocEvents gc.1.priv.bytes.length 1) ++
  (match gc.2.chainKey with
   | none => []
   | some _ => rustAllocEvents 32 1) ++
  (if gc.2.messageKeys = [] then []
   else rustAllocEvents (104 * gc.2.messageKeys.length) 8 ++
     gc.2.messageKeys.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1))

/-- Allocation envelope for `<session_structure::Chain as Clone>::clone` on `gc`. -/
def ChainCloneEnv (gc : ChainGhost × ReceiverChain) (evs : List AllocEvent) : Prop :=
  evs = chainCloneEvents gc

theorem chainCloneEnv_events (gc : ChainGhost × ReceiverChain) :
    ChainCloneEnv gc (chainCloneEvents gc) := rfl

theorem fitsEvents_chainClone_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits)
    (st : M.σ) (gc : ChainGhost × ReceiverChain) (h : FitsEnv M lim st (ChainCloneEnv gc)) :
    FitsEvents M lim st (chainCloneEvents gc) :=
  h (chainCloneEvents gc) rfl

/-- Underlying `(ChainGhost × ReceiverChain)` view of a `Some` sender chain `(g, sc)`. -/
def senderChainAsProtoGhost (g : SenderChainGhost) (sc : SenderChain) :
    ChainGhost × ReceiverChain :=
  (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
    ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩)

/-- Deterministic `AllocEvent` sequence emitted when cloning a `Some` sender chain `(g, sc)`. -/
def senderChainCloneEvents (g : SenderChainGhost) (sc : SenderChain) : List AllocEvent :=
  chainCloneEvents (senderChainAsProtoGhost g sc)

/-- Allocation envelope for cloning a `Some` sender chain `(g, sc)`. -/
def SenderChainCloneEnv (g : SenderChainGhost) (sc : SenderChain)
    (evs : List AllocEvent) : Prop :=
  evs = senderChainCloneEvents g sc

theorem senderChainCloneEnv_events (g : SenderChainGhost) (sc : SenderChain) :
    SenderChainCloneEnv g sc (senderChainCloneEvents g sc) := rfl

/-! ## Budget-threaded specifications at `chainCloneStackX` -/

/-- Budget-threaded `protoChainCloneSpecX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under
`FitsEnv M lim st (ChainCloneEnv x.gc)`). -/
def protoChainCloneSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (ChainCloneEnv x.gc)⌝ ∗
      memRegion x.dst 104 ∗ protoChainAt A.repAlloc x.gc x.src ∗
      A.pool lim st s ∗ stackAt s.sp chainCloneStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ ChainCloneEnv x.gc evs⌝ ∗
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        protoChainAt A.repAlloc (g', x.gc.2) x.dst) ∗
      protoChainAt A.repAlloc x.gc x.src ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStackX

/-- Budget-threaded `chainCloneSpecX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under
`FitsEnv M lim st (ChainCloneEnv x.gc)`). -/
def chainCloneSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (ChainCloneEnv x.gc)⌝ ∗
      memRegion x.dst 104 ∗ chainAt A.repAlloc x.gc x.src ∗
      A.pool lim st s ∗ stackAt s.sp chainCloneStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ ChainCloneEnv x.gc evs⌝ ∗
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        chainAt A.repAlloc (g', x.gc.2) x.dst) ∗
      chainAt A.repAlloc x.gc x.src ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStackX

/-- Budget-threaded `senderChainCloneSpecX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under
`FitsEnv M lim st (SenderChainCloneEnv x.g x.sc)`). -/
def senderChainCloneSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SenderChainCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (SenderChainCloneEnv x.g x.sc)⌝ ∗
      memRegion x.dst 104 ∗ optSenderChainAt A.repAlloc x.src (some x.g) (some x.sc) ∗
      A.pool lim st s ∗ stackAt s.sp chainCloneStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SenderChainCloneEnv x.g x.sc evs⌝ ∗
      (∃∗ g' : SenderChainGhost,
        ⌜g'.srk.bytes = x.g.srk.bytes ∧ g'.priv.bytes = x.g.priv.bytes⌝ ∗
        optSenderChainAt A.repAlloc x.dst (some g') (some x.sc)) ∗
      optSenderChainAt A.repAlloc x.src (some x.g) (some x.sc) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStackX

/-! ## Relocatable `[LibsignalPlacement]` contracts and `SepWPpLs` combinators -/

/-- OOM-parameterized `SepWPp` guarded by `LibsignalCodeLoaded lsmpl s.mem`. -/
abbrev SepWPpLs [LibsignalPlacement] (prog : Program) (ret : BitVec 64) (s : State)
    (P : SepProp) (Q Qp : State → SepProp → Prop)
    (oom : State → SepProp := fun _ => ⌜False⌝) : Prop :=
  LibsignalCodeLoaded lsmpl s.mem → SepWPp prog ret s P Q Qp oom

theorem SepWPpLs.of_sepWP [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpLs prog ret sm Pm Q Qp oom) oom) :
    SepWPpLs prog ret s P Q Qp oom :=
  fun hcl => SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm hnext => hnext hclm)

theorem SepWPpLs.weaken_pre [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hent : P ⊢ P') (h : SepWPpLs prog ret s P' Q Qp oom) :
    SepWPpLs prog ret s P Q Qp oom :=
  fun hcl => SepWPp.weaken_pre hent (h hcl)

theorem SepWPpLs.pure_elim [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (h : φ → SepWPpLs prog ret s P Q Qp oom) :
    SepWPpLs prog ret s (⌜φ⌝ ∗ P) Q Qp oom :=
  fun hcl => SepWPp.pure_elim fun hφ => h hφ hcl

theorem sepWPp_of_sepWP_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm hnext => hnext hclm)

/-- `Chain::clone [local#1]` (Block `82`) at budget `protoChainCloneSpecX`, with `LibsignalCodeLoaded`. -/
def ProtoChainCloneLocal1PlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_82 H) (blkPl_82).base
    (withLsCodeLoaded lsmpl (protoChainCloneSpecX M A lim))

/-- `Chain::clone [local#1]` (Block `82`) at budget `chainCloneSpecX`, with `LibsignalCodeLoaded`. -/
def ChainCloneLocal1PlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_82 H) (blkPl_82).base
    (withLsCodeLoaded lsmpl (chainCloneSpecX M A lim))

/-- `Chain::clone [local#1]` (Block `82`) at budget `senderChainCloneSpecX`, with `LibsignalCodeLoaded`. -/
def SenderChainCloneLocal1PlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_82 H) (blkPl_82).base
    (withLsCodeLoaded lsmpl (senderChainCloneSpecX M A lim))

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseXBudget

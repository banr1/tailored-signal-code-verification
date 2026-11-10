/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssembly
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailWPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# Budget-Threaded `[LibsignalPlacement]` Allocator Envelopes and Post-Loop Interface

Defines the branch-indexed allocator event envelopes (`PksmFrom*Env`, `PksmPostEnv`,
`PksmTryFromEnvGen`, `PksmTryFromEnv`), continuation postcondition combinators
(`w8bRetPost`), and `PreKeyPostLoopOkWPlaced` over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSession (PublicKey SignalMessage SignalProtocolError)
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111)
open CryptoVerification.E2E.Pqxdh.ResponderWire (preKeyCalleeSavedAt preKeyPlacedProg preKeyTryFromStack preKeyTryFromSubStack)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAt lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Wire (entails_of_eq pure_true_emp tryFromQp)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (PreKeyLoopExitStatePlaced pksmErrE pksmResAt_err_of_parse preKeyLoopExitMem stackAt_preKeyTryFromSubStack_skipField wirePreKeyOf)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget

open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv FitsEvents FreeOnlyEvs SeqEnv
   rustAllocEvents fitsEvents_append)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (pksmTryFromSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget (TryFromLoopEnv)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux (TryFromEnvGen)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget
  (IntoBoxedOptBoundedEnv TryFromPostEnv)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget
  (IntoBoxedOptCapEnv TryCloneBytesEnv)

/-! ## 1. Continuation Post & `SepWPp` Post Combinators for `pksmTryFromSpecPlaced` -/

/-- Shared `SepWPp` return postcondition at `s0.readReg64 .x30` from intermediate cost-model
state `st` with remaining allocation-event envelope `RemEnv`. -/
def w8bRetPost [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (RemEnv : List AllocEvent → Prop)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 sf : State) (Pf : SepProp) : Prop :=
  sf.sp = s0.sp ∧
    (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
    ∃ evs : List AllocEvent, RemEnv evs ∧
      (Pf ⊢ ⌜sf.trace = s0.trace⌝ ∗
        CryptoVerification.SignalSession.Cli.RunCompose.pksmResAt A.repAlloc x.ret (CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes) ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗
        A.pool lim (M.stepEvents evs st) sf)

/-- Prepends a segment event trace `evs₁` onto `w8bRetPost` using `M.stepEvents_append`. -/
theorem w8bRetPost_prepend [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {E2 OutEnv : List AllocEvent → Prop}
    {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost} {st : M.σ} {s0 sf : State} {Pf : SepProp}
    {evs₁ : List AllocEvent}
    (hsub : ∀ evs₂, E2 evs₂ → OutEnv (evs₁ ++ evs₂))
    (hq : w8bRetPost A lim E2 x (M.stepEvents evs₁ st) s0 sf Pf) :
    w8bRetPost A lim OutEnv x st s0 sf Pf := by
  rcases hq with ⟨hsp, hcs, evs₂, hevs₂, hent⟩
  refine ⟨hsp, hcs, evs₁ ++ evs₂, hsub evs₂ hevs₂, ?_⟩
  rw [M.stepEvents_append]
  exact hent

/-- Monotonicity of `w8bRetPost` in the remaining event envelope. -/
theorem w8bRetPost_mono [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {E1 E2 : List AllocEvent → Prop}
    {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost} {st : M.σ} {s0 sf : State} {Pf : SepProp}
    (hsub : ∀ evs, E1 evs → E2 evs)
    (hq : w8bRetPost A lim E1 x st s0 sf Pf) :
    w8bRetPost A lim E2 x st s0 sf Pf := by
  rcases hq with ⟨hsp, hcs, evs, hevs, hent⟩
  exact ⟨hsp, hcs, evs, hsub evs hevs, hent⟩

/-- Converts `w8bRetPost A lim (Env x) x st s0 sf Pf` to `(pksmTryFromSpecPlaced M A lim Env).post`. -/
theorem w8bRetPost_to_specPost [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost → List AllocEvent → Prop}
    {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost} {st : M.σ} {s0 sf : State} {Pf : SepProp}
    (hq : w8bRetPost A lim (Env x) x st s0 sf Pf) :
    sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ (pksmTryFromSpecPlaced M A lim Env).post (x, st) s0 sf) := by
  rcases hq with ⟨hsp, hcs, evs, hevs, hent⟩
  refine ⟨hsp, hcs, ?_⟩
  dsimp only [pksmTryFromSpecPlaced, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  refine Entails.sepExists_right evs (Entails.trans hent (Entails.pure_left fun htr => ?_))
  rw [pure_true_emp ⟨htr, hevs⟩, emp_sepConj]
  exact Entails.refl _

/-- Builds `w8bRetPost` on an error branch (`Pksm.pksmParse x.bytes = none`) with leftover `R`. -/
theorem w8b_errRetPost_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RemEnv : List AllocEvent → Prop}
    {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost} {st : M.σ} {s0 sf : State}
    {Pf R : SepProp} {fn : List (BitVec 8)} {e : SignalProtocolError}
    {evs : List AllocEvent}
    (hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none)
    (hevs : RemEnv evs)
    (h : sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ ⌜sf.trace = s0.trace⌝ ∗
        (pksmErrE A.repAlloc fn x.ret e ∗ R) ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool lim (M.stepEvents evs st) sf)) :
    w8bRetPost A lim RemEnv x st s0 sf Pf := by
  rcases h with ⟨hsp, hcs, hent⟩
  refine ⟨hsp, hcs, evs, hevs, Entails.trans hent ?_⟩
  exact sepConj_mono_right
    (sepConj_mono_left (pksmResAt_err_of_parse A.repAlloc fn x.ret x.bytes e R hparse))

/-- Zero-event (`evs = []`) specialization of `w8b_errRetPost_placed`. -/
theorem w8b_errRetPost_nil_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RemEnv : List AllocEvent → Prop}
    {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost} {st : M.σ} {s0 sf : State}
    {Pf R : SepProp} {fn : List (BitVec 8)} {e : SignalProtocolError}
    (hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none)
    (hnil : RemEnv [])
    (h : sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ ⌜sf.trace = s0.trace⌝ ∗
        (pksmErrE A.repAlloc fn x.ret e ∗ R) ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool lim st sf)) :
    w8bRetPost A lim RemEnv x st s0 sf Pf :=
  w8b_errRetPost_placed hparse hnil (evs := []) h

/-- Heap-free (`R = emp`) specialization of `w8b_errRetPost_placed`. -/
theorem w8b_errRetPost_noHeap_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RemEnv : List AllocEvent → Prop}
    {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost} {st : M.σ} {s0 sf : State}
    {Pf : SepProp} {fn : List (BitVec 8)} {e : SignalProtocolError}
    {evs : List AllocEvent}
    (hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none)
    (hevs : RemEnv evs)
    (h : sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ ⌜sf.trace = s0.trace⌝ ∗
        pksmErrE A.repAlloc fn x.ret e ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool lim (M.stepEvents evs st) sf)) :
    w8bRetPost A lim RemEnv x st s0 sf Pf := by
  rcases h with ⟨hsp, hcs, hent⟩
  refine ⟨hsp, hcs, evs, hevs, Entails.trans hent ?_⟩
  have herr : pksmErrE A.repAlloc fn x.ret e ⊢
      CryptoVerification.SignalSession.Cli.RunCompose.pksmResAt A.repAlloc x.ret (CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes) := by
    simpa [sepConj_emp] using pksmResAt_err_of_parse A.repAlloc fn x.ret x.bytes e emp hparse
  exact sepConj_mono_right (sepConj_mono_left herr)

/-! ## 2. Bounded Branch-Indexed Allocator Event Envelopes -/

/-- Allocator event envelope of the inner `<SignalMessage as TryFrom<&[u8]>>::try_from` call
on `msg` (depends only on `msg`, independent of `bytesA` and `ret`). -/
def SigMsgCallEnv (msg : List (BitVec 8)) : List AllocEvent → Prop :=
  TryFromEnvGen (fun g => TryFromPostEnv g.bytes) { bytesA := 0#64, bytes := msg, ret := 0#64 }

theorem sigMsgCallEnv_iff_ghost (ptr ret : BitVec 64) (msg : List (BitVec 8))
    (evs : List AllocEvent) :
    TryFromEnvGen (fun g => TryFromPostEnv g.bytes) { bytesA := ptr, bytes := msg, ret := ret } evs ↔
      SigMsgCallEnv msg evs := by
  constructor <;> intro h <;> cases h
  · exact .nil
  · exact .loopOnly ‹_›
  · exact .loopPost ‹_› ‹_›
  · exact .nil
  · exact .loopOnly ‹_›
  · exact .loopPost ‹_› ‹_›

theorem fitsEnv_sigMsgCall_iff_ghost {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (ptr ret : BitVec 64) (msg : List (BitVec 8)) :
    FitsEnv M lim st
        (TryFromEnvGen (fun g => TryFromPostEnv g.bytes) { bytesA := ptr, bytes := msg, ret := ret }) ↔
      FitsEnv M lim st (SigMsgCallEnv msg) := by
  constructor
  · exact fun h evs hevs => h evs ((sigMsgCallEnv_iff_ghost ptr ret msg evs).mpr hevs)
  · exact fun h evs hevs => h evs ((sigMsgCallEnv_iff_ghost ptr ret msg evs).mp hevs)

/-- Allocation-phase envelope from `+0x864` (`2148`):
`SigMsgCallEnv msg` on `.error _`, and `SeqEnv (SigMsgCallEnv msg) (TryCloneBytesEnv xBytes)` on `.ok _`. -/
def PksmFrom864PreEnv (xBytes msg : List (BitVec 8)) : List AllocEvent → Prop :=
  match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg with
  | .error _ => SigMsgCallEnv msg
  | .ok _ => SeqEnv (SigMsgCallEnv msg) (TryCloneBytesEnv xBytes)

/-- Remaining-events envelope from `+0x864` (`2148`) to function return. -/
def PksmFrom864Env (xBytes msg : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (PksmFrom864PreEnv xBytes msg) FreeOnlyEvs

/-- Allocation-phase envelope from `+0x830` (`2096`). -/
def PksmFrom830PreEnv (xBytes ik msg : List (BitVec 8)) : List AllocEvent → Prop :=
  match CryptoGames.LibsignalSession.PublicKey.deserialize ik with
  | .error _ => (· = [])
  | .ok _ => PksmFrom864PreEnv xBytes msg

/-- Remaining-events envelope from `+0x830` (`2096`) to function return. -/
def PksmFrom830Env (xBytes ik msg : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (PksmFrom830PreEnv xBytes ik msg) FreeOnlyEvs

/-- Allocation-phase envelope from `+0x684` (`1668`). -/
def PksmFrom684PreEnv (vb : BitVec 8) (xBytes ik msg : List (BitVec 8))
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8))) :
    List AllocEvent → Prop :=
  if (kpkOpt.isSome != kyberOpt.isSome) = true then
    (· = rustAllocEvents 68 1)
  else if kpkOpt = none ∧ kyberOpt = none ∧ 0x40 ≤ vb.toNat then
    (· = rustAllocEvents 54 1)
  else
    SeqEnv (IntoBoxedOptBoundedEnv kyberOpt) (PksmFrom830PreEnv xBytes ik msg)

/-- Remaining-events envelope from `+0x684` (`1668`) to function return. -/
def PksmFrom684Env (vb : BitVec 8) (xBytes ik msg : List (BitVec 8))
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8))) :
    List AllocEvent → Prop :=
  SeqEnv (PksmFrom684PreEnv vb xBytes ik msg kpkOpt kyberOpt) FreeOnlyEvs

/-- Allocation-phase envelope from `+0x5b4` (`1460`). -/
def PksmFrom5b4PreEnv (vb : BitVec 8) (xBytes bk ik msg : List (BitVec 8))
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8))) :
    List AllocEvent → Prop :=
  match CryptoGames.LibsignalSession.PublicKey.deserialize bk with
  | .error _ => (· = [])
  | .ok _ => PksmFrom684PreEnv vb xBytes ik msg kpkOpt kyberOpt

/-- Remaining-events envelope from `+0x5b4` (`1460`) to function return. -/
def PksmFrom5b4Env (vb : BitVec 8) (xBytes bk ik msg : List (BitVec 8))
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8))) :
    List AllocEvent → Prop :=
  SeqEnv (PksmFrom5b4PreEnv vb xBytes bk ik msg kpkOpt kyberOpt) FreeOnlyEvs

/-- Allocation-phase envelope from `+0x460` (`1120`, post-loop presence check) on decoded `m`:
leading `FreeOnlyEvs` from `post_seg1_xok_to_5b4`'s `drop_in_place::<SignalProtocolError>` calls
followed by `PksmFrom5b4PreEnv` when all four required fields are present, else `(· = [])`. -/
def PksmPostPreEnv (vb : BitVec 8) (xBytes : List (BitVec 8)) (m : ProtoPreKeySignalMessage) :
    List AllocEvent → Prop :=
  match m.baseKey, m.identityKey, m.message, m.signedPreKeyId with
  | some bk, some ik, some msg, some _ =>
    SeqEnv FreeOnlyEvs (PksmFrom5b4PreEnv vb xBytes bk ik msg m.kyberPreKeyId m.kyberCiphertext)
  | _, _, _, _ => (· = [])

/-- Remaining-events envelope from `+0x460` (`1120`, post-loop decode `some m`) to function return. -/
def PksmPostEnv (vb : BitVec 8) (xBytes : List (BitVec 8)) (m : ProtoPreKeySignalMessage) :
    List AllocEvent → Prop :=
  SeqEnv (PksmPostPreEnv vb xBytes m) FreeOnlyEvs

/-- Post-loop envelope from `+0x460` (`1120`) parameterized by `Pksm.decodeProto (b1 :: bs1)`:
`FreeOnlyEvs` on protobuf decode failure (`none`), and `PksmPostEnv vb xBytes m` on `some m`. -/
def PksmAfterLoopEnv (vb : BitVec 8) (xBytes : List (BitVec 8)) :
    Option ProtoPreKeySignalMessage → List AllocEvent → Prop
  | none => FreeOnlyEvs
  | some m => PksmPostEnv vb xBytes m

/-- Concrete loop envelope for `PreKeySignalMessage::try_from` on `x`. -/
abbrev PksmLoopEnv (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) : List AllocEvent → Prop :=
  TryFromLoopEnv (2 * (x.bytes.length - 1) + 2) x.bytes.length

/-- Top-level allocator event envelope of `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`
parameterized by `LoopEnv`. -/
inductive PksmTryFromEnvGen (LoopEnv : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost → List AllocEvent → Prop)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) : List AllocEvent → Prop where
  | nil : PksmTryFromEnvGen LoopEnv x []
  | loopOnly {vb b1 : BitVec 8} {bs1 : List (BitVec 8)} {evs₁ : List AllocEvent} :
      x.bytes = vb :: b1 :: bs1 →
      ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
      LoopEnv x evs₁ →
      PksmTryFromEnvGen LoopEnv x evs₁
  | loopAfter {vb b1 : BitVec 8} {bs1 : List (BitVec 8)} {evs₁ evs₂ : List AllocEvent} :
      x.bytes = vb :: b1 :: bs1 →
      ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
      LoopEnv x evs₁ →
      PksmAfterLoopEnv vb x.bytes (CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1)) evs₂ →
      PksmTryFromEnvGen LoopEnv x (evs₁ ++ evs₂)

/-- Concrete top-level allocator event envelope of `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`. -/
abbrev PksmTryFromEnv : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost → List AllocEvent → Prop :=
  PksmTryFromEnvGen PksmLoopEnv

/-! ### `SeqEnv` & Envelope Step/Reduction Lemmas -/

theorem seqEnv_nil_freeOnly {evs : List AllocEvent} (hf : FreeOnlyEvs evs) :
    SeqEnv (· = []) FreeOnlyEvs evs :=
  LibsignalBinary.Heap.SeqEnv.append (evs₁ := []) (evs₂ := evs) rfl hf

theorem pksmPostEnv_prepend_some {vb : BitVec 8} {xBytes : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {bk ik msg : List (BitVec 8)} {spkId : BitVec 32}
    {evs₀ evs₂ : List AllocEvent}
    (hbk : m.baseKey = some bk) (hik : m.identityKey = some ik)
    (hmsg : m.message = some msg) (hspk : m.signedPreKeyId = some spkId)
    (hf : FreeOnlyEvs evs₀)
    (h2 : PksmFrom5b4Env vb xBytes bk ik msg m.kyberPreKeyId m.kyberCiphertext evs₂) :
    PksmPostEnv vb xBytes m (evs₀ ++ evs₂) := by
  unfold PksmPostEnv PksmPostPreEnv
  rw [hbk, hik, hmsg, hspk]
  rcases h2 with hpre | ⟨a, b, rfl, hpre, hfb⟩
  · exact Or.inl (LibsignalBinary.Heap.SeqEnv.append hf hpre)
  · rw [← List.append_assoc]
    exact LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hf hpre) hfb

theorem fitsEnv_pksmPost_step_freeOnly {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {vb : BitVec 8} {xBytes : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {bk ik msg : List (BitVec 8)} {spkId : BitVec 32}
    {evs₀ : List AllocEvent}
    (hbk : m.baseKey = some bk) (hik : m.identityKey = some ik)
    (hmsg : m.message = some msg) (hspk : m.signedPreKeyId = some spkId)
    (hf : FreeOnlyEvs evs₀)
    (hfit : FitsEnv M lim st (PksmPostEnv vb xBytes m)) :
    FitsEnv M lim (M.stepEvents evs₀ st)
      (PksmFrom5b4Env vb xBytes bk ik msg m.kyberPreKeyId m.kyberCiphertext) := by
  intro evs₂ h2
  have hcomb := pksmPostEnv_prepend_some hbk hik hmsg hspk hf h2
  exact ((fitsEvents_append M lim evs₀ evs₂ st).mp (hfit _ hcomb)).2

theorem pksmPostEnv_of_missing_freeOnly {vb : BitVec 8} {xBytes : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {evs : List AllocEvent}
    (hmiss : m.baseKey = none ∨ m.identityKey = none ∨ m.message = none ∨ m.signedPreKeyId = none)
    (hf : FreeOnlyEvs evs) :
    PksmPostEnv vb xBytes m evs := by
  unfold PksmPostEnv PksmPostPreEnv
  rcases hmiss with h | h | h | h <;> rw [h]
  · exact seqEnv_nil_freeOnly hf
  · cases m.baseKey <;> exact seqEnv_nil_freeOnly hf
  · cases m.baseKey <;> cases m.identityKey <;> exact seqEnv_nil_freeOnly hf
  · cases m.baseKey <;> cases m.identityKey <;> cases m.message <;> exact seqEnv_nil_freeOnly hf

theorem pksmFrom5b4Env_of_ok_eq {vb : BitVec 8} {xBytes bk ik msg : List (BitVec 8)}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))} {pk : PublicKey}
    (hok : CryptoGames.LibsignalSession.PublicKey.deserialize bk = .ok pk) :
    PksmFrom5b4Env vb xBytes bk ik msg kpkOpt kyberOpt =
      PksmFrom684Env vb xBytes ik msg kpkOpt kyberOpt := by
  unfold PksmFrom5b4Env PksmFrom5b4PreEnv PksmFrom684Env
  rw [hok]

theorem pksmFrom5b4Env_of_err_freeOnly {vb : BitVec 8} {xBytes bk ik msg : List (BitVec 8)}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {e : SignalProtocolError} {evs : List AllocEvent}
    (herr : CryptoGames.LibsignalSession.PublicKey.deserialize bk = .error e) (hf : FreeOnlyEvs evs) :
    PksmFrom5b4Env vb xBytes bk ik msg kpkOpt kyberOpt evs := by
  unfold PksmFrom5b4Env PksmFrom5b4PreEnv
  rw [herr]
  exact seqEnv_nil_freeOnly hf

theorem pksmFrom684PreEnv_of_half {vb : BitVec 8} {xBytes ik msg : List (BitVec 8)}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    (hhalf : (kpkOpt.isSome != kyberOpt.isSome) = true) :
    PksmFrom684PreEnv vb xBytes ik msg kpkOpt kyberOpt = (· = rustAllocEvents 68 1) := by
  unfold PksmFrom684PreEnv
  simp only [hhalf, ↓reduceIte]

theorem pksmFrom684PreEnv_of_v4 {vb : BitVec 8} {xBytes ik msg : List (BitVec 8)}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    (hv4 : kpkOpt = none ∧ kyberOpt = none ∧ 0x40 ≤ vb.toNat) :
    PksmFrom684PreEnv vb xBytes ik msg kpkOpt kyberOpt = (· = rustAllocEvents 54 1) := by
  rcases hv4 with ⟨hkpk, hkyb, hvb⟩
  unfold PksmFrom684PreEnv
  subst hkpk; subst hkyb
  simp [hvb]

theorem pksmFrom684PreEnv_of_ok {vb : BitVec 8} {xBytes ik msg : List (BitVec 8)}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    (hok : (kpkOpt.isSome == kyberOpt.isSome) = true ∧
      (kpkOpt = none → kyberOpt = none → vb.toNat < 0x40)) :
    PksmFrom684PreEnv vb xBytes ik msg kpkOpt kyberOpt =
      SeqEnv (IntoBoxedOptBoundedEnv kyberOpt) (PksmFrom830PreEnv xBytes ik msg) := by
  rcases hok with ⟨heq, hlt⟩
  have hnhalf : ¬ ((kpkOpt.isSome != kyberOpt.isSome) = true) := by
    cases kpkOpt <;> cases kyberOpt <;> simp at heq ⊢
  have hnv4 : ¬ (kpkOpt = none ∧ kyberOpt = none ∧ 0x40 ≤ vb.toNat) := by
    rintro ⟨hk, hy, hge⟩
    have := hlt hk hy
    omega
  unfold PksmFrom684PreEnv
  simp [hnhalf, hnv4]

theorem intoBoxedOptBounded_of_cap {kyberCap : BitVec 64}
    {kyberOpt : Option (List (BitVec 8))} {evs : List AllocEvent}
    (hbnd : ∀ ct, kyberOpt = some ct → ct.length ≤ kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63)
    (h : IntoBoxedOptCapEnv kyberCap kyberOpt evs) :
    IntoBoxedOptBoundedEnv kyberOpt evs := by
  cases kyberOpt with
  | none => exact h
  | some ct =>
    obtain ⟨hle, hlt⟩ := hbnd ct rfl
    exact ⟨kyberCap, hle, hlt, h⟩

theorem fitsEnv_pksmFrom684_ok_box {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {vb : BitVec 8} {xBytes ik msg : List (BitVec 8)}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))} {kyberCap : BitVec 64}
    (hok : (kpkOpt.isSome == kyberOpt.isSome) = true ∧
      (kpkOpt = none → kyberOpt = none → vb.toNat < 0x40))
    (hbnd : ∀ ct, kyberOpt = some ct → ct.length ≤ kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63)
    (hfit : FitsEnv M lim st (PksmFrom684Env vb xBytes ik msg kpkOpt kyberOpt)) :
    FitsEnv M lim st (IntoBoxedOptCapEnv kyberCap kyberOpt) := by
  intro evsK hK
  refine hfit evsK ?_
  unfold PksmFrom684Env
  rw [pksmFrom684PreEnv_of_ok hok]
  exact Or.inl (Or.inl (intoBoxedOptBounded_of_cap hbnd hK))

theorem fitsEnv_pksmFrom684_ok_step {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {vb : BitVec 8} {xBytes ik msg : List (BitVec 8)}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {kyberCap : BitVec 64} {evsK : List AllocEvent}
    (hok : (kpkOpt.isSome == kyberOpt.isSome) = true ∧
      (kpkOpt = none → kyberOpt = none → vb.toNat < 0x40))
    (hbnd : ∀ ct, kyberOpt = some ct → ct.length ≤ kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63)
    (hK : IntoBoxedOptCapEnv kyberCap kyberOpt evsK)
    (hfit : FitsEnv M lim st (PksmFrom684Env vb xBytes ik msg kpkOpt kyberOpt)) :
    FitsEnv M lim (M.stepEvents evsK st) (PksmFrom830Env xBytes ik msg) := by
  intro evs₂ h2
  have hKb := intoBoxedOptBounded_of_cap hbnd hK
  have hcomb : PksmFrom684Env vb xBytes ik msg kpkOpt kyberOpt (evsK ++ evs₂) := by
    unfold PksmFrom684Env
    rw [pksmFrom684PreEnv_of_ok hok]
    rcases h2 with hpre | ⟨a, b, rfl, hpre, hfb⟩
    · exact Or.inl (LibsignalBinary.Heap.SeqEnv.append hKb hpre)
    · rw [← List.append_assoc]
      exact LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hKb hpre) hfb
  exact ((fitsEvents_append M lim evsK evs₂ st).mp (hfit _ hcomb)).2

theorem pksmFrom684Env_of_ok {vb : BitVec 8} {xBytes ik msg : List (BitVec 8)}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {kyberCap : BitVec 64} {evsK evs₂ : List AllocEvent}
    (hok : (kpkOpt.isSome == kyberOpt.isSome) = true ∧
      (kpkOpt = none → kyberOpt = none → vb.toNat < 0x40))
    (hbnd : ∀ ct, kyberOpt = some ct → ct.length ≤ kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63)
    (hK : IntoBoxedOptCapEnv kyberCap kyberOpt evsK)
    (h2 : PksmFrom830Env xBytes ik msg evs₂) :
    PksmFrom684Env vb xBytes ik msg kpkOpt kyberOpt (evsK ++ evs₂) := by
  have hKb := intoBoxedOptBounded_of_cap hbnd hK
  unfold PksmFrom684Env
  rw [pksmFrom684PreEnv_of_ok hok]
  rcases h2 with hpre | ⟨a, b, rfl, hpre, hfb⟩
  · exact Or.inl (LibsignalBinary.Heap.SeqEnv.append hKb hpre)
  · rw [← List.append_assoc]
    exact LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hKb hpre) hfb

theorem pksmFrom830Env_of_ok_eq {xBytes ik msg : List (BitVec 8)} {ipk : PublicKey}
    (hok : CryptoGames.LibsignalSession.PublicKey.deserialize ik = .ok ipk) :
    PksmFrom830Env xBytes ik msg = PksmFrom864Env xBytes msg := by
  unfold PksmFrom830Env PksmFrom830PreEnv PksmFrom864Env
  rw [hok]

theorem pksmFrom830Env_of_err_freeOnly {xBytes ik msg : List (BitVec 8)}
    {e : SignalProtocolError} {evs : List AllocEvent}
    (herr : CryptoGames.LibsignalSession.PublicKey.deserialize ik = .error e) (hf : FreeOnlyEvs evs) :
    PksmFrom830Env xBytes ik msg evs := by
  unfold PksmFrom830Env PksmFrom830PreEnv
  rw [herr]
  exact seqEnv_nil_freeOnly hf

theorem fitsEnv_pksmFrom864_call {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {xBytes msg : List (BitVec 8)}
    (hfit : FitsEnv M lim st (PksmFrom864Env xBytes msg)) :
    FitsEnv M lim st (SigMsgCallEnv msg) := by
  intro evsS hS
  refine hfit evsS ?_
  unfold PksmFrom864Env PksmFrom864PreEnv
  cases CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg with
  | error _ => exact Or.inl hS
  | ok _ => exact Or.inl (Or.inl hS)

theorem fitsEnv_pksmFrom864_ok_clone {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {xBytes msg : List (BitVec 8)} {inner : SignalMessage} {evsS : List AllocEvent}
    (hok : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg = .ok inner)
    (hS : SigMsgCallEnv msg evsS)
    (hfit : FitsEnv M lim st (PksmFrom864Env xBytes msg)) :
    FitsEnv M lim (M.stepEvents evsS st) (TryCloneBytesEnv xBytes) := by
  intro evsC hC
  have hcomb : PksmFrom864Env xBytes msg (evsS ++ evsC) := by
    unfold PksmFrom864Env PksmFrom864PreEnv
    rw [hok]
    exact Or.inl (LibsignalBinary.Heap.SeqEnv.append hS hC)
  exact ((fitsEvents_append M lim evsS evsC st).mp (hfit _ hcomb)).2

theorem pksmFrom864Env_of_err {xBytes msg : List (BitVec 8)} {e : SignalProtocolError}
    {evsS evsF : List AllocEvent}
    (herr : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg = .error e)
    (hS : SigMsgCallEnv msg evsS) (hF : FreeOnlyEvs evsF) :
    PksmFrom864Env xBytes msg (evsS ++ evsF) := by
  unfold PksmFrom864Env PksmFrom864PreEnv
  rw [herr]
  exact LibsignalBinary.Heap.SeqEnv.append hS hF

theorem pksmFrom864Env_of_ok {xBytes msg : List (BitVec 8)} {inner : SignalMessage}
    {evsS evsC evsF : List AllocEvent}
    (hok : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec msg = .ok inner)
    (hS : SigMsgCallEnv msg evsS)
    (hC : TryCloneBytesEnv xBytes evsC)
    (hF : FreeOnlyEvs evsF) :
    PksmFrom864Env xBytes msg (evsS ++ (evsC ++ evsF)) := by
  rw [← List.append_assoc]
  unfold PksmFrom864Env PksmFrom864PreEnv
  rw [hok]
  exact LibsignalBinary.Heap.SeqEnv.append (LibsignalBinary.Heap.SeqEnv.append hS hC) hF

theorem fitsEnv_pksmTryFrom_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {LoopEnv : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost → List AllocEvent → Prop} {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost}
    {vb b1 : BitVec 8} {bs1 : List (BitVec 8)}
    (hcons : x.bytes = vb :: b1 :: bs1)
    (hge3 : ¬ (vb >>> 4) < 3#8) (hle4 : ¬ 4#8 < (vb >>> 4))
    (hfit : FitsEnv M lim st (PksmTryFromEnvGen LoopEnv x)) :
    FitsEnv M lim st (LoopEnv x) :=
  fun evs₁ h1 => hfit evs₁ (.loopOnly hcons hge3 hle4 h1)

theorem fitsEnv_pksmTryFrom_post {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {LoopEnv : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost → List AllocEvent → Prop} {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost}
    {vb b1 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {evs₁ : List AllocEvent}
    (hcons : x.bytes = vb :: b1 :: bs1)
    (hge3 : ¬ (vb >>> 4) < 3#8) (hle4 : ¬ 4#8 < (vb >>> 4))
    (hdec : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m)
    (h1 : LoopEnv x evs₁)
    (hfit : FitsEnv M lim st (PksmTryFromEnvGen LoopEnv x)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (PksmPostEnv vb x.bytes m) := by
  intro evs₂ h2
  have hafter : PksmAfterLoopEnv vb x.bytes (CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1)) evs₂ := by
    rw [hdec]; exact h2
  exact ((fitsEvents_append M lim evs₁ evs₂ st).mp
    (hfit (evs₁ ++ evs₂) (.loopAfter hcons hge3 hle4 h1 hafter))).2

/-! ## 3. Post-Loop Interface (`+0x460`, Decode Ok) & Loop-Exit Regroup -/

/-- Post-loop `Ok` continuation `+0x460 → ret` (`1120 → ret`) under `[LibsignalPlacement]`:
from the loop exit with `x24 = 0` and decoded `m` of `b1 :: bs1` (version byte `vb` in the
accepted window), `preKeyPlacedProg H` returns with `w8bRetPost A lim (PksmPostEnv vb x.bytes m)`. -/
def PreKeyPostLoopOkWPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 s : State)
    (vb b1 : BitVec 8) (bs1 : List (BitVec 8)) (m : ProtoPreKeySignalMessage),
    FitsEnv M lim st (PksmPostEnv vb x.bytes m) →
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    PreKeyLoopExitStatePlaced s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr vb s →
    s.pc = (blkPl_111).base + 1120#64 →
    s.status = .Running →
    s.readReg64 .x24 = 0#64 →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (wirePreKeyOf A.repAlloc (s0.sp - 608#64 + 312#64) m ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        A.pool lim st s ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack)
      (w8bRetPost A lim (PksmPostEnv vb x.bytes m) x st s0)
      (tryFromQp s0)

/-- Loop-exit glue under `[LibsignalPlacement]`: regroups `preKeyLoopExitMem (A.atState lim st s)`
(+ the frame kept across `+0x000 → +0x460`) into `A.repAlloc` containers + `A.pool lim st s`. -/
theorem w8b_loopExit_regroup_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (s0 s : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (x24 : BitVec 64) (res : Option ProtoPreKeySignalMessage) (hcons : x.bytes = vb :: b1 :: bs1) :
    ((x.ptr ↦₈ vb) ∗
        preKeyLoopExitMem (A.atState lim st s) (s0.sp - 608#64) (x.ptr + 1#64) (b1 :: bs1) x24 res ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0) ∗
      (memRegion x.ret 248 ∗ lsLogOff ∗ memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack)
          (preKeyTryFromSubStack - CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ⊢
      (match res with
        | some m' => ⌜x24 = 0#64⌝ ∗ wirePreKeyOf A.repAlloc (s0.sp - 608#64 + 312#64) m'
        | none =>
          ⌜x24 ≠ 0#64⌝ ∗ decodeErrorAt A.repAlloc x24 ∗
            (∃∗ mErr, wirePreKeyOf A.repAlloc (s0.sp - 608#64 + 312#64) mErr)) ∗
      (memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        A.pool lim st s ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack) := by
  have h440 := pointsTo64_entails_memRegion (s0.sp - 608#64 + 440#64) (s0.sp - 608#64 + 296#64)
  have hw : ∀ m', wirePreKeyOf (A.atState lim st s) (s0.sp - 608#64 + 312#64) m' =
      wirePreKeyOf A.repAlloc (s0.sp - 608#64 + 312#64) m' := fun _ => rfl
  have hd : decodeErrorAt (A.atState lim st s) x24 = decodeErrorAt A.repAlloc x24 := rfl
  have hpool : (A.atState lim st s).pool = A.pool lim st s := rfl
  unfold preKeyLoopExitMem
  rw [hcons, stackAt_preKeyTryFromSubStack_skipField (s0.sp - 608#64)]
  simp only [pointsToBytes_cons]
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left h440))))
  cases res <;> simp only [hw, hd, hpool] <;> (apply entails_of_eq; sep_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget

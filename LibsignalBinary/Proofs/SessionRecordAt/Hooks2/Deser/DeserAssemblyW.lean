/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs

@[expose] public section

set_option autoImplicit false

/-!
# Leaf-Parameterized `SessionRecord::deserialize` Assembly

Assembles `chainMergeGenW_ok`, `mergeFieldGenW_ok`, `deserializeExactW_ok`, and
`deserializeBodyGW_ok` from abstract leaf bundles (`ChainLeavesW`, `MergeFieldLeavesW`,
`DeserLeavesW`) across fixed-allocator, arbitrary-allocator (`A : RustAlloc`), and relocatable
`[LibsignalPlacement]` formulations.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp CryptoVerification
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization

theorem L1_DeserAssemblyW : True := trivial

/-! ## 1. `ChainMerge` Assembly (`ChainLeavesW` → `ChainMergeGenOkAtW`) -/

/-- Return state of `chainMerge` with `(chainMergeGenSpecAtW img).post` (defeq `Leaf.ChainExitG.ChainRetGAtW`). -/
def ChainRetGAtW (img : Obj.Image) (x : ChainMergeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ (chainMergeGenSpecAtW img).post x s0 sf ∗ R)

/-- Bundle of the 5 `ChainMerge` leaf theorems on `SP2Ext img.base ext` (`ChainStepGAtW` / `ChainLoopGAtW`). -/
structure ChainLeavesW (img : Obj.Image) (ext : String → Option (State → State)) : Prop where
  entry : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName →
    s0.status = .Running →
    (s0.mem ⊨ (chainMergeGenSpecAtW img).pre x s0 ∗ R) →
    s0.spAligned = true →
    ChainStepGAtW img ext x R s0 s0 (ChainLoopGAtW img ext x R s0 0)
  srk : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    ((x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2) →
    ChainLoopGAtW img ext x R s0 k s →
    ChainStepGAtW img ext x R s0 s (ChainLoopGAtW img ext x R s0 (k + 1))
  ck : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 3 →
    ChainLoopGAtW img ext x R s0 k s →
    ChainStepGAtW img ext x R s0 s (ChainLoopGAtW img ext x R s0 (k + 1))
  keys : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 4 →
    ChainLoopGAtW img ext x R s0 k s →
    ChainStepGAtW img ext x R s0 s (ChainLoopGAtW img ext x R s0 (k + 1))
  exit : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State),
    ChainLoopGAtW img ext x R s0 x.c.fields.length s →
    ChainStepGAtW img ext x R s0 s (ChainRetGAtW img x R s0)

/-- Induction over the remaining `m` fields of `x.c.fields` on `SP2Ext img.base ext`. -/
theorem chainLoopGW_run (img : Obj.Image) (ext : String → Option (State → State))
    (hL : ChainLeavesW img ext) {x : ChainMergeGenGhost} {R : SepProp} {s0 : State} :
    ∀ (m k : Nat) (s : State), k + m = x.c.fields.length →
      ChainLoopGAtW img ext x R s0 k s →
      reaches_outcome (SP2Ext img.base ext) (chainMergeGenSpecAtW img) x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (hL.exit x R s0 s hs) ?_
    intro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < x.c.fields.length := by omega
    have next : ∀ s', ChainLoopGAtW img ext x R s0 (k + 1) s' →
        reaches_outcome (SP2Ext img.base ext) (chainMergeGenSpecAtW img) x R s0 s' :=
      fun s' hs' => ih (k + 1) s' (by omega) hs'
    rcases chainField_tag_cases (x.c.fields[k]'hlt) with h12 | h3 | h4
    · exact segStepG_then (hL.srk x R s0 k s hlt h12 hs) next
    · exact segStepG_then (hL.ck x R s0 k s hlt h3 hs) next
    · exact segStepG_then (hL.keys x R s0 k s hlt h4 hs) next

/-- `Chain::merge` on an arbitrary well-formed `ChainG` on `SP2Ext img.base ext`. -/
theorem chainMergeGenW_ok (img : Obj.Image) (ext : String → Option (State → State))
    (hL : ChainLeavesW img ext) :
    ChainMergeGenOkAtW img ext := by
  unfold ChainMergeGenOkAtW OkAtX
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  exact segStepG_then (hL.entry x R s0 hpc hrun hpre hal) fun s hs =>
    chainLoopGW_run img ext hL x.c.fields.length 0 s (Nat.zero_add _) hs

/-! ## 2. `MergeField` Assembly (`MergeFieldLeavesW` → `MergeFieldGenOkAtW`) -/

/-- Bundle of the 6 `MergeField` tag-leaf theorems on `SP2Ext img.base ext` (`MergeFieldGenOkAtW`). -/
structure MergeFieldLeavesW (img : Obj.Image) (ext : String → Option (State → State)) : Prop where
  tag1 : MergeFieldGenOkAtW img ext (fun fl => fl.tag = 1)
  tag234 : MergeFieldGenOkAtW img ext (fun fl => fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4)
  tag5 : MergeFieldGenOkAtW img ext (fun fl => fl.tag = 5)
  tag6 : ChainMergeGenOkAtW img ext → MergeFieldGenOkAtW img ext (fun fl => fl.tag = 6)
  tag7 : ChainMergeGenOkAtW img ext → MergeFieldGenOkAtW img ext (fun fl => fl.tag = 7)
  tag9 : MergeFieldGenOkAtW img ext (fun fl => fl.tag = 9)

theorem mergeFieldGenSpecAtW_pre_iff (img : Obj.Image) {P : GenField → Prop}
    {x : MergeFieldGenGhost} {s0 : State} {R : SepProp} :
    (s0.mem ⊨ (mergeFieldGenSpecAtW img P).pre x s0 ∗ R) ↔
      P x.fld ∧ (s0.mem ⊨ (mergeFieldGenSpecAtW img (fun _ => True)).pre x s0 ∗ R) := by
  simp only [mergeFieldGenSpecAtW, sepConj_assoc, satisfies_pure_sepConj]
  tauto

theorem mergeFieldGenOkAtW_of_imp (img : Obj.Image) (ext : String → Option (State → State))
    {P Q : GenField → Prop} (h : ∀ fl, P fl → Q fl)
    (hQ : MergeFieldGenOkAtW img ext Q) :
    MergeFieldGenOkAtW img ext P := by
  unfold MergeFieldGenOkAtW OkAtX at hQ ⊢
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  rw [mergeFieldGenSpecAtW_pre_iff] at hpre
  exact hQ.mono_outcome x R s0 hpc hrun (mergeFieldGenSpecAtW_pre_iff img |>.mpr ⟨h x.fld hpre.1, hpre.2⟩) hal (fun _ hout => hout)

theorem mergeFieldGenOkAtW_or (img : Obj.Image) (ext : String → Option (State → State))
    {P Q : GenField → Prop}
    (hP : MergeFieldGenOkAtW img ext P) (hQ : MergeFieldGenOkAtW img ext Q) :
    MergeFieldGenOkAtW img ext (fun fl => P fl ∨ Q fl) := by
  unfold MergeFieldGenOkAtW OkAtX at hP hQ ⊢
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  rw [mergeFieldGenSpecAtW_pre_iff] at hpre
  rcases hpre.1 with hp | hq
  · exact hP.mono_outcome x R s0 hpc hrun (mergeFieldGenSpecAtW_pre_iff img |>.mpr ⟨hp, hpre.2⟩) hal (fun _ hout => hout)
  · exact hQ.mono_outcome x R s0 hpc hrun (mergeFieldGenSpecAtW_pre_iff img |>.mpr ⟨hq, hpre.2⟩) hal (fun _ hout => hout)

/-- `SessionStructure::merge_field` on all in-scope `GenField` tags on `SP2Ext img.base ext`. -/
theorem mergeFieldGenW_ok (img : Obj.Image) (ext : String → Option (State → State))
    (hL : MergeFieldLeavesW img ext) (hCh : ChainMergeGenOkAtW img ext) :
    MergeFieldGenOkAtW img ext (fun _ => True) := by
  have hAll :=
    mergeFieldGenOkAtW_or img ext hL.tag1
      (mergeFieldGenOkAtW_or img ext hL.tag234
        (mergeFieldGenOkAtW_or img ext hL.tag5
          (mergeFieldGenOkAtW_or img ext (hL.tag6 hCh)
            (mergeFieldGenOkAtW_or img ext (hL.tag7 hCh) hL.tag9))))
  refine mergeFieldGenOkAtW_of_imp img ext (fun fl _ => ?_) hAll
  cases fl <;> simp [GenField.tag]

/-! ## 3. `SessionRecord::deserialize` Exact & General Assembly (`DeserLeavesW`) -/

/-- Exact-postcondition `SessionRecord::deserialize` contract (`deserOutRecordG` niche form),
parameterized by a loaded `img`. Definitionally equal (`rfl`) to `deserializeExactSpecAtX img`
in `Proofs/Hooks2/Deser/DeserTransportX.lean`. -/
noncomputable def deserializeExactSpecAtW (img : Obj.Image) : Spec DeserializeGenGhost where
  pre := (deserializeGenSpecAt img).pre
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ CryptoVerification.E2E.Record.encodeRecord x.r) ∗
      deserOutRecordG x.out x.r ∗
      stackAt s0.sp recDeserializeStack
  onPanic := (deserializeGenSpecAt img).onPanic

/-- Bundle of the 3 `SessionRecord::deserialize` leaf theorems on `SP2Ext img.base ext`
(`deserLoopEntryG_ok_atW`, `deserLoopIterG_ok_atW`, `deserLoopExitG_ok_extW`). -/
structure DeserLeavesW (img : Obj.Image) (ext : String → Option (State → State)) : Prop where
  entry : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName →
    s0.status = .Running →
    (s0.mem ⊨ (deserializeGenSpecAt img).pre x s0 ∗ R) →
    s0.spAligned = true →
    DeserStepGAtW img ext x R s0 s0 (DeserLoopGAtW img ext x R s0 0)
  iter : MergeFieldGenOkAtW img ext (fun _ => True) →
    ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State),
      DeserializeScope x.r →
      k < (recFields x.r).length →
      DeserLoopGAtW img ext x R s0 k s →
      DeserStepGAtW img ext x R s0 s (DeserLoopGAtW img ext x R s0 (k + 1))
  exit : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 s : State),
    DeserializeScope x.r →
    DeserLoopGAtW img ext x R s0 (recFields x.r).length s →
    DeserStepGAtW img ext x R s0 s (DeserRetGAt img x R s0)

/-- Induction over the remaining `m` fields of `recFields x.r` for the exact contract
`deserializeExactSpecAtW img` (port of `CalleesStoreRecord.deserLoopG_run_exact`). -/
theorem deserLoopGW_run_exact (img : Obj.Image) (ext : String → Option (State → State))
    (hD : DeserLeavesW img ext) (hMF : MergeFieldGenOkAtW img ext (fun _ => True))
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScope x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFields x.r).length →
      DeserLoopGAtW img ext x R s0 k s →
      reaches_outcome (SP2Ext img.base ext) (deserializeExactSpecAtW img) x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (hD.exit x R s0 s hr hs) ?_
    rintro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < (recFields x.r).length := by omega
    exact segStepG_then (hD.iter hMF x R s0 k s hr hlt hs) fun s' hs' =>
      ih (k + 1) s' (by omega) hs'

/-- Exact `SessionRecord::deserialize` contract on `SP2Ext img.base ext`
(port of `CalleesStoreRecord.deserializeExact_ok`).
Conclusion is definitionally equal to
`subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName) (deserializeExactSpecAtX img)`. -/
theorem deserializeExactW_ok (img : Obj.Image) (ext : String → Option (State → State))
    (hD : DeserLeavesW img ext) (hMF : MergeFieldGenOkAtW img ext (fun _ => True)) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName)
      (deserializeExactSpecAtW img) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have hr : DeserializeScope x.r := by
    have h := hpre
    simp only [deserializeExactSpecAtW, deserializeGenSpecAt, sepConj_assoc, satisfies_pure_sepConj] at h
    exact h.1.2.2.2.1
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre hal) fun s hs =>
    deserLoopGW_run_exact img ext hD hMF hr _ 0 s (Nat.zero_add _) hs

/-- Combined assembly from `ChainLeavesW`, `MergeFieldLeavesW`, and `DeserLeavesW`. -/
theorem deserializeExactW_ok_of_leaves (img : Obj.Image) (ext : String → Option (State → State))
    (hChain : ChainLeavesW img ext) (hMF : MergeFieldLeavesW img ext) (hD : DeserLeavesW img ext) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName)
      (deserializeExactSpecAtW img) :=
  deserializeExactW_ok img ext hD (mergeFieldGenW_ok img ext hMF (chainMergeGenW_ok img ext hChain))

/-- Representation bridge from `deserOutRawG` to `(deserializeGenSpecAt img).post`
(port of `Root.deserOutG_post`, parameterized over `hRepr : deserReprG_ok`). -/
theorem deserOutGW_post (img : Obj.Image)
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordG out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r)
    (x : DeserializeGenGhost) (hr : DeserializeScope x.r) (s0 sf : State) :
    deserOutRawG x s0 sf ⊢ (deserializeGenSpecAt img).post x s0 sf := by
  dsimp only [deserOutRawG, deserializeGenSpecAt]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (hRepr x.r hr x.out)) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
  rw [sepConj_assoc]
  exact Entails.refl _

/-- Induction over `recFields x.r` for `(deserializeGenSpecAt img)` (port of `Root.deserLoopG_run`). -/
theorem deserLoopGW_run (img : Obj.Image) (ext : String → Option (State → State))
    (hD : DeserLeavesW img ext) (hMF : MergeFieldGenOkAtW img ext (fun _ => True))
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordG out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r)
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScope x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFields x.r).length →
      DeserLoopGAtW img ext x R s0 k s →
      reaches_outcome (SP2Ext img.base ext) (deserializeGenSpecAt img) x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (hD.exit x R s0 s hr hs) ?_
    rintro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc,
      Satisfies.mono (sepConj_mono_left (deserOutGW_post img hRepr x hr s0 sf)) hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < (recFields x.r).length := by omega
    exact segStepG_then (hD.iter hMF x R s0 k s hr hlt hs) fun s' hs' =>
      ih (k + 1) s' (by omega) hs'

/-- General `SessionRecord::deserialize` contract on `SP2Ext img.base ext` (port of `Root.deserializeBodyG_ok`). -/
theorem deserializeBodyGW_ok (img : Obj.Image) (ext : String → Option (State → State))
    (hD : DeserLeavesW img ext) (hMF : MergeFieldGenOkAtW img ext (fun _ => True))
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordG out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r) :
    OkAtX img.base ext recDeserializeName (deserializeGenSpecAt img) := by
  unfold OkAtX
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have hr : DeserializeScope x.r := by
    have h := hpre
    simp only [deserializeGenSpecAt, sepConj_assoc, satisfies_pure_sepConj] at h
    exact h.1.2.2.2.1
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre hal) fun s hs =>
    deserLoopGW_run img ext hD hMF hRepr hr (recFields x.r).length 0 s (Nat.zero_add _) hs

/-! ## 4. Arbitrary-Allocator (`A : RustAlloc`) `*WA` Assembly -/

/-- Bundle of the 5 `ChainMerge` leaf theorems on `SP2Ext img.base ext` for `(A : RustAlloc)`. -/
structure ChainLeavesWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  entry : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName →
    s0.status = .Running →
    (s0.mem ⊨ (chainMergeGenSpecAtWA A img).pre x s0 ∗ R) →
    s0.spAligned = true →
    ChainStepGAtWA img A ext x R s0 s0 (ChainLoopGAtWA img A ext x R s0 0)
  srk : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    ((x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2) →
    ChainLoopGAtWA img A ext x R s0 k s →
    ChainStepGAtWA img A ext x R s0 s (ChainLoopGAtWA img A ext x R s0 (k + 1))
  ck : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 3 →
    ChainLoopGAtWA img A ext x R s0 k s →
    ChainStepGAtWA img A ext x R s0 s (ChainLoopGAtWA img A ext x R s0 (k + 1))
  keys : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 4 →
    ChainLoopGAtWA img A ext x R s0 k s →
    ChainStepGAtWA img A ext x R s0 s (ChainLoopGAtWA img A ext x R s0 (k + 1))
  exit : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State),
    ChainLoopGAtWA img A ext x R s0 x.c.fields.length s →
    ChainStepGAtWA img A ext x R s0 s (ChainRetGAtWA img A x R s0)

theorem chainLoopGWA_run (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hL : ChainLeavesWA img A ext) {x : ChainMergeGenGhost} {R : SepProp} {s0 : State} :
    ∀ (m k : Nat) (s : State), k + m = x.c.fields.length →
      ChainLoopGAtWA img A ext x R s0 k s →
      reaches_outcome (SP2Ext img.base ext) (chainMergeGenSpecAtWA A img) x R s0 s := by
  intro m; induction m with
  | zero =>
    intro k s hk hs; simp only [Nat.add_zero] at hk; subst hk
    refine segStepG_then (hL.exit x R s0 s hs) ?_
    intro sf ⟨hret, hcc, hmem⟩; exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs; have hlt : k < x.c.fields.length := by omega
    have next : ∀ s', ChainLoopGAtWA img A ext x R s0 (k + 1) s' →
        reaches_outcome (SP2Ext img.base ext) (chainMergeGenSpecAtWA A img) x R s0 s' :=
      fun s' hs' => ih (k + 1) s' (by omega) hs'
    rcases chainField_tag_cases (x.c.fields[k]'hlt) with h12 | h3 | h4
    · exact segStepG_then (hL.srk x R s0 k s hlt h12 hs) next
    · exact segStepG_then (hL.ck x R s0 k s hlt h3 hs) next
    · exact segStepG_then (hL.keys x R s0 k s hlt h4 hs) next

theorem chainMergeGenWA_ok (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hL : ChainLeavesWA img A ext) :
    ChainMergeGenOkAtWA img A ext := by
  unfold ChainMergeGenOkAtWA OkAtX
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  exact segStepG_then (hL.entry x R s0 hpc hrun hpre hal) fun s hs =>
    chainLoopGWA_run img A ext hL x.c.fields.length 0 s (Nat.zero_add _) hs

/-- Bundle of the 6 `MergeField` tag-leaf theorems on `SP2Ext img.base ext` for `(A : RustAlloc)`. -/
structure MergeFieldLeavesWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  tag1 : MergeFieldGenOkAtWA img A ext (fun fl => fl.tag = 1)
  tag234 : MergeFieldGenOkAtWA img A ext (fun fl => fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4)
  tag5 : MergeFieldGenOkAtWA img A ext (fun fl => fl.tag = 5)
  tag6 : ChainMergeGenOkAtWA img A ext → MergeFieldGenOkAtWA img A ext (fun fl => fl.tag = 6)
  tag7 : ChainMergeGenOkAtWA img A ext → MergeFieldGenOkAtWA img A ext (fun fl => fl.tag = 7)
  tag9 : MergeFieldGenOkAtWA img A ext (fun fl => fl.tag = 9)

theorem mergeFieldGenSpecAtWA_pre_iff (A : RustAlloc) (img : Obj.Image) {P : GenField → Prop}
    {x : MergeFieldGenGhost} {s0 : State} {R : SepProp} :
    (s0.mem ⊨ (mergeFieldGenSpecAtWA A img P).pre x s0 ∗ R) ↔
      P x.fld ∧ (s0.mem ⊨ (mergeFieldGenSpecAtWA A img (fun _ => True)).pre x s0 ∗ R) := by
  simp only [mergeFieldGenSpecAtWA, sepConj_assoc, satisfies_pure_sepConj]; tauto

theorem mergeFieldGenOkAtWA_of_imp (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    {P Q : GenField → Prop} (h : ∀ fl, P fl → Q fl)
    (hQ : MergeFieldGenOkAtWA img A ext Q) :
    MergeFieldGenOkAtWA img A ext P := by
  unfold MergeFieldGenOkAtWA OkAtX at hQ ⊢
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal; rw [mergeFieldGenSpecAtWA_pre_iff] at hpre
  exact hQ.mono_outcome x R s0 hpc hrun (mergeFieldGenSpecAtWA_pre_iff A img |>.mpr ⟨h x.fld hpre.1, hpre.2⟩) hal (fun _ hout => hout)

theorem mergeFieldGenOkAtWA_or (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) {P Q : GenField → Prop}
    (hP : MergeFieldGenOkAtWA img A ext P) (hQ : MergeFieldGenOkAtWA img A ext Q) :
    MergeFieldGenOkAtWA img A ext (fun fl => P fl ∨ Q fl) := by
  unfold MergeFieldGenOkAtWA OkAtX at hP hQ ⊢
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal; rw [mergeFieldGenSpecAtWA_pre_iff] at hpre
  rcases hpre.1 with hp | hq
  · exact hP.mono_outcome x R s0 hpc hrun (mergeFieldGenSpecAtWA_pre_iff A img |>.mpr ⟨hp, hpre.2⟩) hal (fun _ hout => hout)
  · exact hQ.mono_outcome x R s0 hpc hrun (mergeFieldGenSpecAtWA_pre_iff A img |>.mpr ⟨hq, hpre.2⟩) hal (fun _ hout => hout)

theorem mergeFieldGenWA_ok (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hL : MergeFieldLeavesWA img A ext) (hCh : ChainMergeGenOkAtWA img A ext) :
    MergeFieldGenOkAtWA img A ext (fun _ => True) := by
  have hAll :=
    mergeFieldGenOkAtWA_or img A ext hL.tag1
      (mergeFieldGenOkAtWA_or img A ext hL.tag234
        (mergeFieldGenOkAtWA_or img A ext hL.tag5
          (mergeFieldGenOkAtWA_or img A ext (hL.tag6 hCh)
            (mergeFieldGenOkAtWA_or img A ext (hL.tag7 hCh) hL.tag9))))
  refine mergeFieldGenOkAtWA_of_imp img A ext (fun fl _ => ?_) hAll
  cases fl <;> simp [GenField.tag]

noncomputable def deserializeExactSpecAtWA (A : RustAlloc) (img : Obj.Image) : Spec DeserializeGenGhost where
  pre := (deserializeGenSpecAtA A img).pre
  post := fun x s0 sf => deserOutRawGA A x s0 sf
  onPanic := (deserializeGenSpecAtA A img).onPanic

structure DeserLeavesWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  entry : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName →
    s0.status = .Running →
    (s0.mem ⊨ (deserializeGenSpecAtA A img).pre x s0 ∗ R) →
    s0.spAligned = true →
    DeserStepGAtWA img A ext x R s0 s0 (DeserLoopGAtWA img A ext x R s0 0)
  iter : MergeFieldGenOkAtWA img A ext (fun _ => True) →
    ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State),
      DeserializeScope x.r → k < (recFields x.r).length →
      DeserLoopGAtWA img A ext x R s0 k s →
      DeserStepGAtWA img A ext x R s0 s (DeserLoopGAtWA img A ext x R s0 (k + 1))
  exit : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 s : State),
    DeserializeScope x.r →
    DeserLoopGAtWA img A ext x R s0 (recFields x.r).length s →
    DeserStepGAtWA img A ext x R s0 s (DeserRetGAtA img A x R s0)

theorem deserLoopGWA_run_exact (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hD : DeserLeavesWA img A ext) (hMF : MergeFieldGenOkAtWA img A ext (fun _ => True))
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScope x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFields x.r).length →
      DeserLoopGAtWA img A ext x R s0 k s →
      reaches_outcome (SP2Ext img.base ext) (deserializeExactSpecAtWA A img) x R s0 s := by
  intro m; induction m with
  | zero =>
    intro k s hk hs; simp only [Nat.add_zero] at hk; subst hk
    refine segStepG_then (hD.exit x R s0 s hr hs) ?_
    rintro sf ⟨hret, hcc, hmem⟩; exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs; have hlt : k < (recFields x.r).length := by omega
    exact segStepG_then (hD.iter hMF x R s0 k s hr hlt hs) fun s' hs' =>
      ih (k + 1) s' (by omega) hs'

theorem deserializeExactWA_ok (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hD : DeserLeavesWA img A ext) (hMF : MergeFieldGenOkAtWA img A ext (fun _ => True)) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName)
      (deserializeExactSpecAtWA A img) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have hr : DeserializeScope x.r := by
    have h := hpre
    simp only [deserializeExactSpecAtWA, deserializeGenSpecAtA, sepConj_assoc, satisfies_pure_sepConj] at h
    exact h.1.2.2.2.1
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre hal) fun s hs =>
    deserLoopGWA_run_exact img A ext hD hMF hr _ 0 s (Nat.zero_add _) hs

theorem deserializeExactWA_ok_of_leaves (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hChain : ChainLeavesWA img A ext) (hMF : MergeFieldLeavesWA img A ext)
    (hD : DeserLeavesWA img A ext) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName)
      (deserializeExactSpecAtWA A img) :=
  deserializeExactWA_ok img A ext hD (mergeFieldGenWA_ok img A ext hMF (chainMergeGenWA_ok img A ext hChain))

theorem deserOutGWA_post (img : Obj.Image) (A : RustAlloc)
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordGA A out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A out g r)
    (x : DeserializeGenGhost) (hr : DeserializeScope x.r) (s0 sf : State) :
    deserOutRawGA A x s0 sf ⊢ (deserializeGenSpecAtA A img).post x s0 sf := by
  dsimp only [deserOutRawGA, deserializeGenSpecAtA]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (hRepr x.r hr x.out)) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
  rw [sepConj_assoc]; exact Entails.refl _

theorem deserLoopGWA_run (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hD : DeserLeavesWA img A ext) (hMF : MergeFieldGenOkAtWA img A ext (fun _ => True))
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordGA A out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A out g r)
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScope x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFields x.r).length →
      DeserLoopGAtWA img A ext x R s0 k s →
      reaches_outcome (SP2Ext img.base ext) (deserializeGenSpecAtA A img) x R s0 s := by
  intro m; induction m with
  | zero =>
    intro k s hk hs; simp only [Nat.add_zero] at hk; subst hk
    refine segStepG_then (hD.exit x R s0 s hr hs) ?_; rintro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc,
      Satisfies.mono (sepConj_mono_left (deserOutGWA_post img A hRepr x hr s0 sf)) hmem⟩)
  | succ m ih =>
    intro k s hk hs; have hlt : k < (recFields x.r).length := by omega
    exact segStepG_then (hD.iter hMF x R s0 k s hr hlt hs) fun s' hs' =>
      ih (k + 1) s' (by omega) hs'

theorem deserializeBodyGWA_ok (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hD : DeserLeavesWA img A ext) (hMF : MergeFieldGenOkAtWA img A ext (fun _ => True))
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordGA A out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A out g r) :
    OkAtX img.base ext recDeserializeName (deserializeGenSpecAtA A img) := by
  unfold OkAtX
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have hr : DeserializeScope x.r := by
    have h := hpre
    simp only [deserializeGenSpecAtA, sepConj_assoc, satisfies_pure_sepConj] at h
    exact h.1.2.2.2.1
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre hal) fun s hs =>
    deserLoopGWA_run img A ext hD hMF hRepr hr (recFields x.r).length 0 s (Nat.zero_add _) hs

/-! ## 5. Relocatable `[LibsignalPlacement]` Assembly (`ChainLeavesPlacedW`, `MergeFieldLeavesPlacedW`, `DeserLeavesPlacedW`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_DeserAssemblyW_Placed : True := trivial

/-- Return state of relocatable `chainMerge` (block `11`) with `chainMergeGenPlacedSpecW.post`. -/
def ChainRetGPlacedW [LibsignalPlacement] (x : ChainMergeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ chainMergeGenPlacedSpecW.post x s0 sf ∗ R)

/-- Bundle of the 5 relocatable `ChainMerge` leaf theorems on `lsProg_11 H`. -/
structure ChainLeavesPlacedW [LibsignalPlacement] (H : LibsignalHooks) : Prop where
  entry : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = (blkPl_11).base →
    s0.status = .Running →
    (s0.mem ⊨ chainMergeGenPlacedSpecW.pre x s0 ∗ R) →
    s0.spAligned = true →
    ChainStepGPlacedW H x R s0 s0 (ChainLoopGPlacedW x R s0 0)
  srk : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    ((x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2) →
    ChainLoopGPlacedW x R s0 k s →
    ChainStepGPlacedW H x R s0 s (ChainLoopGPlacedW x R s0 (k + 1))
  ck : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 3 →
    ChainLoopGPlacedW x R s0 k s →
    ChainStepGPlacedW H x R s0 s (ChainLoopGPlacedW x R s0 (k + 1))
  keys : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 4 →
    ChainLoopGPlacedW x R s0 k s →
    ChainStepGPlacedW H x R s0 s (ChainLoopGPlacedW x R s0 (k + 1))
  exit : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State),
    ChainLoopGPlacedW x R s0 x.c.fields.length s →
    ChainStepGPlacedW H x R s0 s (ChainRetGPlacedW x R s0)

/-- Induction over the remaining `m` fields of `x.c.fields` on `lsProg_11 H`. -/
theorem chainLoopGPlacedW_run [LibsignalPlacement] (H : LibsignalHooks)
    (hL : ChainLeavesPlacedW H) {x : ChainMergeGenGhost} {R : SepProp} {s0 : State} :
    ∀ (m k : Nat) (s : State), k + m = x.c.fields.length →
      ChainLoopGPlacedW x R s0 k s →
      reaches_outcome (lsProg_11 H) chainMergeGenPlacedSpecW x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (hL.exit x R s0 s hs) ?_
    intro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < x.c.fields.length := by omega
    have next : ∀ s', ChainLoopGPlacedW x R s0 (k + 1) s' →
        reaches_outcome (lsProg_11 H) chainMergeGenPlacedSpecW x R s0 s' :=
      fun s' hs' => ih (k + 1) s' (by omega) hs'
    rcases chainField_tag_cases (x.c.fields[k]'hlt) with h12 | h3 | h4
    · exact segStepG_then (hL.srk x R s0 k s hlt h12 hs) next
    · exact segStepG_then (hL.ck x R s0 k s hlt h3 hs) next
    · exact segStepG_then (hL.keys x R s0 k s hlt h4 hs) next

/-- Relocatable `Chain::merge` (block `11`) on an arbitrary well-formed `ChainG`. -/
theorem chainMergeGenPlacedW_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hL : ChainLeavesPlacedW H) :
    ChainMergeGenPlacedOkW H := by
  unfold ChainMergeGenPlacedOkW
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  exact segStepG_then (hL.entry x R s0 hpc hrun hpre hal) fun s hs =>
    chainLoopGPlacedW_run H hL x.c.fields.length 0 s (Nat.zero_add _) hs

/-- Bundle of the 6 relocatable `MergeField` tag-leaf theorems on `lsProg_15 H`. -/
structure MergeFieldLeavesPlacedW [LibsignalPlacement] (H : LibsignalHooks) : Prop where
  tag1 : MergeFieldGenPlacedOkW H (fun fl => fl.tag = 1)
  tag234 : MergeFieldGenPlacedOkW H (fun fl => fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4)
  tag5 : MergeFieldGenPlacedOkW H (fun fl => fl.tag = 5)
  tag6 : ChainMergeGenPlacedOkW H → MergeFieldGenPlacedOkW H (fun fl => fl.tag = 6)
  tag7 : ChainMergeGenPlacedOkW H → MergeFieldGenPlacedOkW H (fun fl => fl.tag = 7)
  tag9 : MergeFieldGenPlacedOkW H (fun fl => fl.tag = 9)

theorem mergeFieldGenPlacedSpecW_pre_iff [LibsignalPlacement] {P : GenField → Prop}
    {x : MergeFieldGenGhost} {s0 : State} {R : SepProp} :
    (s0.mem ⊨ (mergeFieldGenPlacedSpecW P).pre x s0 ∗ R) ↔
      P x.fld ∧ (s0.mem ⊨ (mergeFieldGenPlacedSpecW (fun _ => True)).pre x s0 ∗ R) := by
  have hraw (Q : GenField → Prop) :
      (s0.mem ⊨ (mergeFieldGenPlacedSpecW Q).pre x s0 ∗ R) ↔
        LibsignalCodeRoLoaded lsmpl s0.mem ∧ (s0.mem ⊨ (mergeFieldGenRawSpecW Q).pre x s0 ∗ R) := by
    dsimp only [mergeFieldGenPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [hraw P, hraw (fun _ => True)]
  simp only [mergeFieldGenRawSpecW, sepConj_assoc, satisfies_pure_sepConj]
  tauto

theorem mergeFieldGenPlacedOkW_of_imp [LibsignalPlacement] (H : LibsignalHooks)
    {P Q : GenField → Prop} (h : ∀ fl, P fl → Q fl)
    (hQ : MergeFieldGenPlacedOkW H Q) :
    MergeFieldGenPlacedOkW H P := by
  unfold MergeFieldGenPlacedOkW at hQ ⊢
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  rw [mergeFieldGenPlacedSpecW_pre_iff] at hpre
  exact hQ.mono_outcome x R s0 hpc hrun (mergeFieldGenPlacedSpecW_pre_iff.mpr ⟨h x.fld hpre.1, hpre.2⟩) hal (fun _ hout => hout)

theorem mergeFieldGenPlacedOkW_or [LibsignalPlacement] (H : LibsignalHooks)
    {P Q : GenField → Prop}
    (hP : MergeFieldGenPlacedOkW H P) (hQ : MergeFieldGenPlacedOkW H Q) :
    MergeFieldGenPlacedOkW H (fun fl => P fl ∨ Q fl) := by
  unfold MergeFieldGenPlacedOkW at hP hQ ⊢
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  rw [mergeFieldGenPlacedSpecW_pre_iff] at hpre
  rcases hpre.1 with hp | hq
  · exact hP.mono_outcome x R s0 hpc hrun (mergeFieldGenPlacedSpecW_pre_iff.mpr ⟨hp, hpre.2⟩) hal (fun _ hout => hout)
  · exact hQ.mono_outcome x R s0 hpc hrun (mergeFieldGenPlacedSpecW_pre_iff.mpr ⟨hq, hpre.2⟩) hal (fun _ hout => hout)

/-- Relocatable `SessionStructure::merge_field` (block `15`) on all in-scope `GenField` tags. -/
theorem mergeFieldGenPlacedW_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hL : MergeFieldLeavesPlacedW H) (hCh : ChainMergeGenPlacedOkW H) :
    MergeFieldGenPlacedOkW H (fun _ => True) := by
  have hAll :=
    mergeFieldGenPlacedOkW_or H hL.tag1
      (mergeFieldGenPlacedOkW_or H hL.tag234
        (mergeFieldGenPlacedOkW_or H hL.tag5
          (mergeFieldGenPlacedOkW_or H (hL.tag6 hCh)
            (mergeFieldGenPlacedOkW_or H (hL.tag7 hCh) hL.tag9))))
  refine mergeFieldGenPlacedOkW_of_imp H (fun fl _ => ?_) hAll
  cases fl <;> simp [GenField.tag]

/-- Image-free exact-postcondition `SessionRecord::deserialize` contract (`deserOutRecordG` niche form). -/
noncomputable def deserializeExactRawSpecW : Spec DeserializeGenGhost where
  pre := deserializeGenRawSpec.pre
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ CryptoVerification.E2E.Record.encodeRecord x.r) ∗
      deserOutRecordG x.out x.r ∗
      stackAt s0.sp recDeserializeStack
  onPanic := deserializeGenRawSpec.onPanic

/-- Relocatable exact-postcondition `SessionRecord::deserialize` contract on block `46`, carrying
`LibsignalCodeRoLoaded lsmpl`. -/
noncomputable abbrev deserializeExactPlacedSpecW [LibsignalPlacement] : Spec DeserializeGenGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl deserializeExactRawSpecW

/-- Return state of relocatable `SessionRecord::deserialize` (block `46`) with `deserOutRawG`. -/
def DeserRetGPlaced (x : DeserializeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧ (sf.mem ⊨ deserOutRawG x s0 sf ∗ R)

/-- Bundle of the 3 relocatable `SessionRecord::deserialize` leaf theorems on `lsProg_46 H`. -/
structure DeserLeavesPlacedW [LibsignalPlacement] (H : LibsignalHooks) : Prop where
  entry : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = (blkPl_46).base →
    s0.status = .Running →
    (s0.mem ⊨ deserializeGenPlacedSpec.pre x s0 ∗ R) →
    s0.spAligned = true →
    DeserStepGPlacedW H x R s0 s0 (DeserLoopGPlacedW x R s0 0)
  iter : MergeFieldGenPlacedOkW H (fun _ => True) →
    ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State),
      DeserializeScope x.r →
      k < (recFields x.r).length →
      DeserLoopGPlacedW x R s0 k s →
      DeserStepGPlacedW H x R s0 s (DeserLoopGPlacedW x R s0 (k + 1))
  exit : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 s : State),
    DeserializeScope x.r →
    DeserLoopGPlacedW x R s0 (recFields x.r).length s →
    DeserStepGPlacedW H x R s0 s (DeserRetGPlaced x R s0)

/-- Induction over the remaining `m` fields of `recFields x.r` for `deserializeExactPlacedSpecW`. -/
theorem deserLoopGPlacedW_run_exact [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesPlacedW H) (hMF : MergeFieldGenPlacedOkW H (fun _ => True))
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScope x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFields x.r).length →
      DeserLoopGPlacedW x R s0 k s →
      reaches_outcome (lsProg_46 H) deserializeExactPlacedSpecW x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (hD.exit x R s0 s hr hs) ?_
    rintro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < (recFields x.r).length := by omega
    exact segStepG_then (hD.iter hMF x R s0 k s hr hlt hs) fun s' hs' =>
      ih (k + 1) s' (by omega) hs'

/-- Relocatable exact `SessionRecord::deserialize` contract on `lsProg_46 H`. -/
theorem deserializeExactPlacedW_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesPlacedW H) (hMF : MergeFieldGenPlacedOkW H (fun _ => True)) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecW := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have ⟨_, hpre0⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  have hr : DeserializeScope x.r := by
    simp only [deserializeExactRawSpecW, deserializeGenRawSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre0
    exact hpre0.1.2.2.2
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre hal) fun s hs =>
    deserLoopGPlacedW_run_exact H hD hMF hr _ 0 s (Nat.zero_add _) hs

/-- Combined relocatable assembly from `ChainLeavesPlacedW`, `MergeFieldLeavesPlacedW`, and `DeserLeavesPlacedW`. -/
theorem deserializeExactPlacedW_ok_of_leaves [LibsignalPlacement] (H : LibsignalHooks)
    (hChain : ChainLeavesPlacedW H) (hMF : MergeFieldLeavesPlacedW H) (hD : DeserLeavesPlacedW H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecW :=
  deserializeExactPlacedW_ok H hD (mergeFieldGenPlacedW_ok H hMF (chainMergeGenPlacedW_ok H hChain))

/-- Representation bridge from `deserOutRawG` to `deserializeGenSpec.post`. -/
theorem deserOutGPlacedW_post
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordG out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r)
    (x : DeserializeGenGhost) (hr : DeserializeScope x.r) (s0 sf : State) :
    deserOutRawG x s0 sf ⊢ deserializeGenSpec.post x s0 sf := by
  dsimp only [deserOutRawG, deserializeGenSpec]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (hRepr x.r hr x.out)) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
  rw [sepConj_assoc]
  exact Entails.refl _

/-- Induction over `recFields x.r` for `deserializeGenPlacedSpec` on `lsProg_46 H`. -/
theorem deserLoopGPlacedW_run [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesPlacedW H) (hMF : MergeFieldGenPlacedOkW H (fun _ => True))
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordG out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r)
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScope x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFields x.r).length →
      DeserLoopGPlacedW x R s0 k s →
      reaches_outcome (lsProg_46 H) deserializeGenPlacedSpec x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (hD.exit x R s0 s hr hs) ?_
    rintro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc,
      Satisfies.mono (sepConj_mono_left (deserOutGPlacedW_post hRepr x hr s0 sf)) hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < (recFields x.r).length := by omega
    exact segStepG_then (hD.iter hMF x R s0 k s hr hlt hs) fun s' hs' =>
      ih (k + 1) s' (by omega) hs'

/-- Relocatable general `SessionRecord::deserialize` contract on `lsProg_46 H`. -/
theorem deserializeBodyGPlacedW_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesPlacedW H) (hMF : MergeFieldGenPlacedOkW H (fun _ => True))
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordG out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeGenPlacedSpec := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have ⟨_, hpre0⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  have hr : DeserializeScope x.r := by
    simp only [deserializeGenRawSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre0
    exact hpre0.1.2.2.2
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre hal) fun s hs =>
    deserLoopGPlacedW_run H hD hMF hRepr hr (recFields x.r).length 0 s (Nat.zero_add _) hs

end Placed

end Proofs.libsignal.Hooks2

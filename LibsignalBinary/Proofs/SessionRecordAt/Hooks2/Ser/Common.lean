/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.FromRecordCalleesCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymA
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymB
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymD
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SepWPpIn
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Shared Serialization Callee Contracts and `SepWPpIn` Helpers

Defines `.inImage img` and `[LibsignalPlacement]` callee-contract abbreviations for the subroutines
called during `SessionRecord::serialize` (`encode_varint`, `do_reserve_and_handle`, `encode::<Chain>`,
`SessionStructure::encode_raw`, `SessionStructure::clone`, and `drop_glue::<SessionStructure>`),
along with framed call and stack-splitting helpers.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization

theorem L1_SerCommon : True := trivial

/-! ## Callee contracts on `SP2Ext` -/

/-- `encode_varint` (`0x30a0`) at `encodeVarintStackX`, in image. -/
abbrev EncodeVarintOkX (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr Prost.encodeVarintName)
    ((Prost.encodeVarintSpecX A).inImage img)

/-- `do_reserve_and_handle` (`0x4cac`) at `Proofs.libsignal.Hooks2.doReserveStackX`, in image. -/
abbrev DoReserveOkX (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr doReserveName)
    ((Proofs.libsignal.Hooks2.doReserveSpecX A).inImage img)

/-- `encode::<Chain>` (`0x44b0`) at `encodeChainStackX`, in image. -/
abbrev EncodeChainOkX (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr encodeChainName)
    ((encodeChainSpecX A).inImage img)

/-- `SessionStructure::encode_raw` (`0x4d38`) at `encodeRawStackX`, in image. -/
abbrev EncodeRawOkX (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr encodeRawName)
    ((encodeRawSpecX A).inImage img)

/-- `SessionStructure::clone` (`0x240f0`) at `sessionCloneStackX`, in image. -/
abbrev SessionCloneOkX (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr sessionCloneName)
    ((sessionCloneSpecX A).inImage img)

/-- `drop_glue<SessionStructure> [local#1]` (`0x25b4`) at `dropSessionStructureLocal1StackX`, in image. -/
abbrev DropSessionStructureLocal1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext)
    ((SP2Ext img.base ext).fnAddr FromRecordCallees.dropSessionStructureLocal1Name)
    ((dropSessionStructureLocal1SpecX A).inImage img)

/-! ## `SepWPpIn` helpers -/

namespace SepWPpIn

variable {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
  {Q Qp : State → SepProp → Prop}

theorem congr_pre {P' : SepProp} (hP : P = P') (h : SepWPpIn img prog ret s P' Q Qp) :
    SepWPpIn img prog ret s P Q Qp := hP ▸ h

theorem panic (hrun : s.status = .Running) (hext : prog.externAt? s.pc = some Rust.panicked)
    (hqp : Qp (Rust.panicked s) P) : SepWPpIn img prog ret s P Q Qp :=
  fun _ _ => SepWPp.panic hrun hext hqp

/-- Framed call rule for `.inImage img` subroutine contracts in `SepWPpIn`. -/
theorem call_frame_inImage {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpIn img prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPpIn img prog ret s P Q Qp := by
  refine call_inImage (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

end SepWPpIn

theorem sepWPpIn_extract_vecU8Buf_bounds {img : Obj.Image} {A : RustAlloc} {cap ptr : BitVec 64}
    {bs : List (BitVec 8)} {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hP : P = vecU8Buf A cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPpIn img prog ret s P Q Qp) :
    SepWPpIn img prog ret s P Q Qp := by
  intro hF hsym R hm hL
  have hhm : s.mem ⊨ vecU8Buf A cap ptr bs ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  obtain ⟨h1, h2, h3⟩ := Prost.vecU8Buf_bounds hhm
  exact h h1 h2 h3 hF hsym R hm hL

/-! ## Stack slack splitting -/

/-- `stackAt sp n = memRegion (sp - n) (n - m) ∗ stackAt sp m` for `m ≤ n ≤ 2^64`. -/
theorem stackAt_sub_split_ser (sp : BitVec 64) (m n : Nat) (hmn : m ≤ n) (hn : n ≤ 2 ^ 64) :
    stackAt sp n = memRegion (sp - BitVec.ofNat 64 n) (n - m) ∗ stackAt sp m := by
  simp only [stackAt]
  have h1 : n = (n - m) + m := (Nat.sub_add_cancel hmn).symm
  have h2 : sp - BitVec.ofNat 64 m = sp - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - m) := by
    have e1 : BitVec.ofNat 64 n = BitVec.ofNat 64 m + BitVec.ofNat 64 (n - m) := by
      rw [← BitVec.ofNat_add, Nat.add_sub_of_le hmn]
    rw [e1, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  exact memRegion_split' h1 h2 hn

/-! ## Relocatable `[LibsignalPlacement]` contracts and call helpers -/

section Placed

open CryptoVerification.E2E.Record.Placed

/-- Block `10` (`encode_varint`) at `encodeVarintStackX` under `[LibsignalPlacement]`. -/
abbrev EncodeVarintPlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
    (withLsCodeLoaded lsmpl (Prost.encodeVarintSpecX A))

/-- Block `13` (`do_reserve_and_handle`) at `Hooks2.doReserveStackX` under `[LibsignalPlacement]`. -/
abbrev DoReservePlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
    (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.doReserveSpecX A))

/-- Block `12` (`encode::<Chain, Vec<u8>>`) at `encodeChainStackX` under `[LibsignalPlacement]`. -/
abbrev EncodeChainPlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_12 H) (blkPl_12).base
    (withLsCodeLoaded lsmpl (encodeChainSpecX A))

/-- Block `14` (`SessionStructure::encode_raw`) at `encodeRawStackX` under `[LibsignalPlacement]`. -/
abbrev EncodeRawPlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_14 H) (blkPl_14).base
    (withLsCodeLoaded lsmpl (encodeRawSpecX A))

/-- Block `80` (`SessionStructure::clone`) at `sessionCloneStackX` under `[LibsignalPlacement]`. -/
abbrev SessionClonePlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_80 H) (blkPl_80).base
    (withLsCodeLoaded lsmpl (sessionCloneSpecX A))

/-- Block `6` (`drop_glue<SessionStructure> [local#1]`) at `dropSessionStructureLocal1StackX`
under `[LibsignalPlacement]`. -/
abbrev DropSessionStructureLocal1PlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (blkPl_6).base
    (withLsCodeLoaded lsmpl (dropSessionStructureLocal1SpecX A))

namespace SepWPpLsCl

variable {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
  {Q Qp : State → SepProp → Prop}

theorem congr_pre {P' : SepProp} (hP : P = P') (h : SepWPpLsCl pl prog ret s P' Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := hP ▸ h

theorem panic (hrun : s.status = .Running) (hext : prog.externAt? s.pc = some Rust.panicked)
    (hqp : Qp (Rust.panicked s) P) : SepWPpLsCl pl prog ret s P Q Qp :=
  fun _ => SepWPp.panic hrun hext hqp

/-- Framed call rule for `withLsCodeLoaded` contracts in `SepWPpLsCl`. -/
theorem call_frame_withLsCodeLoaded {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α}
    {φ : Prop} {T F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLsCl pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  refine call_withLsCodeLoaded (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

/-- Framed call rule for `withLsCl` contracts in `SepWPpLsCl`. -/
theorem call_frame_withLsCl {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α}
    {φ : Prop} {T F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLsCl pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  refine call_withLsCl (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

end SepWPpLsCl

theorem sepWPpLsCl_extract_vecU8Buf_bounds {pl : Obj.MultiPlacement} {A : RustAlloc}
    {cap ptr : BitVec 64} {bs : List (BitVec 8)} {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = Prost.vecU8Buf A cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPpLsCl pl prog ret s P Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  intro hcl R hm hL
  have hhm : s.mem ⊨ Prost.vecU8Buf A cap ptr bs ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  obtain ⟨h1, h2, h3⟩ := Prost.vecU8Buf_bounds hhm
  exact h h1 h2 h3 hcl R hm hL

end Placed

end Proofs.libsignal.Hooks2

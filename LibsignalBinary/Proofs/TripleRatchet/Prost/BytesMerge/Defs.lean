/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefs
public import LibsignalBinary.Proofs.TripleRatchet.OptImageHelper
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.Defs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost
import ProofLib.SepLogic.WPp

/-!
# Helpers and Epilogues for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`

Shared definitions, `BytesMut` `KIND_VEC` arithmetic, stack/memory splitting helpers, `SepWPp`
combinators, and epilogue lemmas for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Fetch macros and offset lemma -/

open Lean Elab Tactic in
/-- `code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-- Fetch hypotheses for `bytes::merge` (`0x2788`), from fn-relative offset `k0`, `len` bytes. -/
elab "merge_fetches " b:term:max C:term:max ctl:term:max abs:term:max
    hfn:term:max k0:term:max len:term:max : tactic => open Lean Meta Elab Tactic in do
  let offLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat (← `((num% (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))) "merge_fetches "))
  let k0Lit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat k0 "merge_fetches "))
  let lenLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat len "merge_fetches "))
  let hfnId : Ident ← if hfn.raw.isIdent then pure ⟨hfn.raw⟩ else do
    let g ← getMainGoal
    let c? ← g.withContext do
      tryCatchRuntimeEx (do
        let e := (← instantiateMVars (← Term.elabTermAndSynthesize hfn none)).consumeMData
        return if e.isConst then some e.constName! else none) (fun _ => pure none)
    match c? with
    | some c => pure (mkCIdentFrom hfn c)
    | none =>
      let id := mkIdent `_hfn_layout
      evalTactic (← `(tactic| have $id := $hfn))
      pure id
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin $b (Rust.withPanics (tripleRatchetExterns $C $ctl $abs)) $hfnId:ident $offLit:num $k0Lit:num $lenLit:num))

/-- Fetch hypotheses for `bytes::merge` (`0x2788`) on arbitrary `H`, from fn-relative offset `k0`, `len` bytes. -/
elab "merge_fetches_H " b:term:max H:term:max
    hfn:term:max k0:term:max len:term:max : tactic => open Lean Meta Elab Tactic in do
  let offLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat (← `((num% (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))) "merge_fetches_H "))
  let k0Lit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat k0 "merge_fetches_H "))
  let lenLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat len "merge_fetches_H "))
  let hfnId : Ident ← if hfn.raw.isIdent then pure ⟨hfn.raw⟩ else do
    let g ← getMainGoal
    let c? ← g.withContext do
      tryCatchRuntimeEx (do
        let e := (← instantiateMVars (← Term.elabTermAndSynthesize hfn none)).consumeMData
        return if e.isConst then some e.constName! else none) (fun _ => pure none)
    match c? with
    | some c => pure (mkCIdentFrom hfn c)
    | none =>
      let id := mkIdent `_hfn_layout
      evalTactic (← `(tactic| have $id := $hfn))
      pure id
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin $b $H $hfnId:ident $offLit:num $k0Lit:num $lenLit:num))

@[local simp, local arm64_norm] theorem bytesMerge_fnOff :
    libsignalSessionCode.fnOff bytesMergeName = num% (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") :=
  (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")

/-! ## Arithmetic and `BytesMut` `KIND_VEC` helpers -/

/-- The `BytesMut::with_capacity` `data` word computed at `+0x168..+0x194`:
    `1 ||| (min((64 - clz(len >>> 10)), 7) <<< 2)`. -/
def bytesMutDataWord (len : BitVec 64) : BitVec 64 :=
  let r := len >>> 10
  let c := 64#64 - BitVec.ofNat 64 (countLeadingZeros r)
  let m := if BitVec.ult c 7#64 then c else 7#64
  1#64 ||| (m <<< 2)

@[arm64_norm, local simp]
theorem bytesMutDataWord_zero : bytesMutDataWord 0#64 = 1#64 := rfl

namespace BytesMergeFacts

theorem bytesMutDataWord_cases (len : BitVec 64) :
    bytesMutDataWord len = 1#64 ∨ bytesMutDataWord len = 5#64 ∨
    bytesMutDataWord len = 9#64 ∨ bytesMutDataWord len = 13#64 ∨
    bytesMutDataWord len = 17#64 ∨ bytesMutDataWord len = 21#64 ∨
    bytesMutDataWord len = 25#64 ∨ bytesMutDataWord len = 29#64 := by
  unfold bytesMutDataWord
  dsimp only
  generalize 64#64 - BitVec.ofNat 64 (countLeadingZeros (len >>> 10)) = c
  by_cases h : c.ult 7#64 = true
  · simp only [h, ↓reduceIte]
    have hc : c.toNat < 7 := by simpa [BitVec.ult] using h
    have hval : c = 0#64 ∨ c = 1#64 ∨ c = 2#64 ∨ c = 3#64 ∨ c = 4#64 ∨ c = 5#64 ∨ c = 6#64 := by
      rcases (by omega : c.toNat = 0 ∨ c.toNat = 1 ∨ c.toNat = 2 ∨ c.toNat = 3 ∨ c.toNat = 4 ∨ c.toNat = 5 ∨ c.toNat = 6) with
        h0 | h1 | h2 | h3 | h4 | h5 | h6
      · exact Or.inl (BitVec.eq_of_toNat_eq h0)
      · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h1))
      · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h3))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h4)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h5))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq h6))))))
    rcases hval with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have hf : c.ult 7#64 = false := Bool.eq_false_iff.mpr h
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    decide

end BytesMergeFacts

/-- Bit 0 of `bytesMutDataWord len` is always `1` (`KIND_VEC`), so `+0x23c: tbnz w22, #0, +0x24c`
    is always taken and `bytes_mut::SHARED_VTABLE` (`+0x240..+0x248`) is unreachable. -/
@[arm64_norm, local simp]
theorem bytesMutDataWord_bit0 (len : BitVec 64) :
    ((bytesMutDataWord len).setWidth 32 &&& 1#32 != 0#32) = true := by
  rcases BytesMergeFacts.bytesMutDataWord_cases len with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

@[arm64_norm, local simp]
theorem bytesMutDataWord_getLsbD_zero (len : BitVec 64) :
    (bytesMutDataWord len).getLsbD 0 = true := by
  rcases BytesMergeFacts.bytesMutDataWord_cases len with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

@[arm64_norm, local simp]
theorem bytesMutDataWord_getElem_zero (len : BitVec 64) :
    (bytesMutDataWord len)[0] = true := by
  change (bytesMutDataWord len).getLsbD 0 = true
  exact bytesMutDataWord_getLsbD_zero len

/-- Shifting `bytesMutDataWord len` right by 5 (`+0x24c: lsr x23, x22, #5`) always yields `0#64`
    (`voff = 0`), because `m ≤ 7` fits in bits `0..2`, so `m <<< 2` fits in bits `2..4`. -/
@[arm64_norm, local simp]
theorem bytesMutDataWord_lsr5 (len : BitVec 64) :
    bytesMutDataWord len >>> 5 = 0#64 := by
  rcases BytesMergeFacts.bytesMutDataWord_cases len with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

@[arm64_norm, local simp]
theorem bitvec_ult_zero (a : BitVec 64) : a.ult 0#64 = false := by
  simp [BitVec.ult]

/-! ## `SepWP` / `SepWPp` invariant and `.rodata` vtable slot helpers -/

theorem SepWP.with_vtableSlot {prog : Program} {target_pc : BitVec 64}
    {img : Obj.Image} (hVtableSlot : BytesVtableSlotLoadedStmt)
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (ptr : BitVec 64) (len : Nat) (hfl : img.FrozenLoaded s)
    (h : SepWP prog target_pc s
      (((bytesVtable img.base ptr len + 0x20#64) ↦₆₄ᵣ bytesDropFnAddr img.base ptr len) ∗ P)
      post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (by rw [sepConj_assoc]; exact (hVtableSlot ptr len himg hfl).2.2 hm)

theorem SepWP.drop_left {prog : Program} {target_pc : BitVec 64}
    {s : State} {V P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s P post) :
    SepWP prog target_pc s (V ∗ P) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm)

theorem SepWPp.bm_of_sepWP_inv {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · have hfl' : img.FrozenLoaded sm := hfl.of_keepsFrozen hsteps.keepsFrozen
    have hsym' : sm.symtab = img.symtab := hsteps.symtab_eq.trans hsym
    obtain ⟨sf, hsteps', hout⟩ :=
      hnext hfl' hsym' R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

theorem SepWPp.bm_call_inv {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  refine ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hfl hsym hpc hrun hsp hlr ?_ hexit
    (fun sf hpan _ => hpanic sf hpan) hnext hoom
  intro R hm
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hfl, hsym⟩, hpre R hm⟩

theorem SepWPp.bm_call_frame_inv {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.bm_call_inv (x := x) (F := F) hcall hfl hsym hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

theorem SepWPp.call_keep {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  exact ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hfl hsym hpc hrun hsp hlr hpre hexit
    (fun sf hpan _ => hpanic sf hpan) hnext hoom

theorem SepWPp.call_frame_keep {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_keep (x := x) (F := F) hcall hfl hsym hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

/-! ## Callee and hook lemmas on `tripleRatchetProgAt` -/

theorem decodeErrorFrom_ok_at_tripleRatchet {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hDef : AllocHooks A abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff decodeErrorFromName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (decodeErrorFromSpec A) := by
  have h := LibsignalTripleRatchet.decodeErrorFrom_ok b C A ctl abs hDef
  rwa [← Program.fnAddr_rel rfl rfl hk]

theorem fnAddr_offset_eq {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {name callee : String} {k : BitVec 64}
    (hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff name) + k =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff callee) := by fnoff_eq) :
    (tripleRatchetProgAt b C ctl abs).fnAddr name + k = (tripleRatchetProgAt b C ctl abs).fnAddr callee := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, BitVec.add_assoc, hk]

theorem fnAddr_offset_eq_H {b : BitVec 64} {H : String → Option (State → State)}
    {name callee : String} {k : BitVec 64}
    (hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff name) + k =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff callee) := by fnoff_eq) :
    (libsignalSessionCode.rebase b H).fnAddr name + k = (libsignalSessionCode.rebase b H).fnAddr callee := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, BitVec.add_assoc, hk]

def BytesMergeOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMergeName)
    (bytesMergeSpec A img)

/-! ## Stack and memory splitting lemmas -/

theorem stackAt_split_sub (sp : BitVec 64) (a b : Nat) (h : a + b ≤ 2 ^ 64 := by decide) :
    stackAt sp (a + b) =
      memRegion (sp - BitVec.ofNat 64 (a + b)) a ∗ stackAt sp b := by
  simp only [stackAt]
  rw [memRegion_split _ a b h]
  have heq : sp - BitVec.ofNat 64 (a + b) + BitVec.ofNat 64 a = sp - BitVec.ofNat 64 b := by
    rw [Nat.add_comm a b, BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [heq]

theorem stackAt_bytesMerge_entry (sp0 : BitVec 64) :
    stackAt sp0 bytesMergeStack =
      stackAt (sp0 - 224#64) decodeVarintSliceStack ∗
      memRegion (sp0 - 224#64) 8 ∗
      memRegion (sp0 - 216#64) 48 ∗
      memRegion (sp0 - 168#64) 104 ∗
      cells (sp0 - 64#64) 8 := by
  have h1 : stackAt sp0 bytesMergeStack =
      stackAt (sp0 - 224#64) decodeVarintSliceStack ∗ memRegion (sp0 - 224#64) 224 := by
    simp only [bytesMergeStack, decodeVarintSliceStack, decodeErrorHookStack, allocHookStack, stackAt]
    rw [show (224 + (80 + 2 * 4096) : Nat) = (80 + 2 * 4096) + 224 from rfl,
      memRegion_split _ (80 + 2 * 4096) 224 (by decide)]
    have e1 : sp0 - BitVec.ofNat 64 ((80 + 2 * 4096) + 224) =
        sp0 - 224#64 - BitVec.ofNat 64 (80 + 2 * 4096) := by bv_omega
    have e2 : sp0 - BitVec.ofNat 64 ((80 + 2 * 4096) + 224) + BitVec.ofNat 64 (80 + 2 * 4096) =
        sp0 - 224#64 := by bv_omega
    rw [e2, e1]
  have h2 : memRegion (sp0 - 224#64) 224 =
      memRegion (sp0 - 224#64) 8 ∗ memRegion (sp0 - 216#64) 48 ∗
      memRegion (sp0 - 168#64) 104 ∗ cells (sp0 - 64#64) 8 := by
    rw [show (224 : Nat) = 8 + (48 + (104 + 8 * 8)) from rfl,
      memRegion_split (sp0 - 224#64) 8 (48 + (104 + 8 * 8)) (by decide),
      memRegion_split (sp0 - 224#64 + 8#64) 48 (104 + 8 * 8) (by decide),
      memRegion_split (sp0 - 224#64 + 8#64 + 48#64) 104 (8 * 8) (by decide),
      memRegion_cells _ 8 (by decide)]
    have e1 : sp0 - 224#64 + 8#64 = sp0 - 216#64 := by bv_omega
    have e2 : sp0 - 224#64 + 8#64 + 48#64 = sp0 - 168#64 := by bv_omega
    have e3 : sp0 - 224#64 + 8#64 + 48#64 + 104#64 = sp0 - 64#64 := by bv_omega
    rw [e3, e2, e1]
  rw [h1, h2]

theorem memRegion_cons_sub (sp0 : BitVec 64) (off : Nat) (v : BitVec 64) (n : Nat)
    (h1 : 8 < off := by decide) (h2 : off < 2 ^ 64 := by decide)
    (hn : 8 ≤ n := by decide) (hlen : n ≤ 2 ^ 64 := by decide) :
    ((sp0 - BitVec.ofNat 64 off) ↦₆₄ v) ∗
      memRegion (sp0 - BitVec.ofNat 64 (off - 8)) (n - 8) ⊢
      memRegion (sp0 - BitVec.ofNat 64 off) n := by
  have c := memRegion_cons (sp0 - BitVec.ofNat 64 off) v (n := n) hn hlen
  rwa [bv_sub_add_lit sp0 off 8 h1 h2] at c

theorem fold_cells_8 (sp0 : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    ((sp0 - 64#64) ↦₆₄ w0) ∗ ((sp0 - 56#64) ↦₆₄ w1) ∗
    ((sp0 - 48#64) ↦₆₄ w2) ∗ ((sp0 - 40#64) ↦₆₄ w3) ∗
    ((sp0 - 32#64) ↦₆₄ w4) ∗ ((sp0 - 24#64) ↦₆₄ w5) ∗
    ((sp0 - 16#64) ↦₆₄ w6) ∗ ((sp0 - 8#64) ↦₆₄ w7) ⊢
    cells (sp0 - 64#64) 8 := by
  rw [← memRegion_cells (sp0 - 64#64) 8 (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (pointsTo64_entails_memRegion (sp0 - 8#64) w7)))))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (memRegion_cons_sub sp0 16 w6 16))))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (memRegion_cons_sub sp0 24 w5 24)))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (memRegion_cons_sub sp0 32 w4 32))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (memRegion_cons_sub sp0 40 w3 40)))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (memRegion_cons_sub sp0 48 w2 48))) ?_
  refine Entails.trans (sepConj_mono_right (memRegion_cons_sub sp0 56 w1 56))
    (memRegion_cons_sub sp0 64 w0 64)

theorem fold_stackAt_bytesMerge (sp0 : BitVec 64)
    (w29 w30 w24 w23 w22 w21 w20 w19 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStack ∗
    memRegion (sp0 - 224#64) 8 ∗
    memRegion (sp0 - 216#64) 48 ∗
    memRegion (sp0 - 168#64) 104 ∗
    ((sp0 - 64#64) ↦₆₄ w29) ∗ ((sp0 - 56#64) ↦₆₄ w30) ∗
    ((sp0 - 48#64) ↦₆₄ w24) ∗ ((sp0 - 40#64) ↦₆₄ w23) ∗
    ((sp0 - 32#64) ↦₆₄ w22) ∗ ((sp0 - 24#64) ↦₆₄ w21) ∗
    ((sp0 - 16#64) ↦₆₄ w20) ∗ ((sp0 - 8#64) ↦₆₄ w19) ⊢
    stackAt sp0 bytesMergeStack := by
  rw [stackAt_bytesMerge_entry sp0]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (fold_cells_8 sp0 w29 w30 w24 w23 w22 w21 w20 w19))))

theorem memRegion_104_unfold (sp0 : BitVec 64) :
    memRegion (sp0 - 168#64) 104 =
      cells (sp0 - 168#64) 7 ∗
      memRegion (sp0 - 112#64) 32 ∗
      (∃∗ w80 : BitVec 64, ((sp0 - 80#64) ↦₆₄ w80) ∗ memRegion (sp0 - 72#64) 8) := by
  rw [show (104 : Nat) = (8 * 7) + (32 + (8 + 8)) from rfl,
    memRegion_split (sp0 - 168#64) (8 * 7) (32 + (8 + 8)) (by decide),
    memRegion_split (sp0 - 168#64 + 56#64) 32 (8 + 8) (by decide),
    memRegion_split (sp0 - 168#64 + 56#64 + 32#64) 8 8 (by decide),
    memRegion_cells (sp0 - 168#64) 7 (by decide)]
  have e1 : sp0 - 168#64 + 56#64 = sp0 - 112#64 := by bv_omega
  have e2 : sp0 - 168#64 + 56#64 + 32#64 = sp0 - 80#64 := by bv_omega
  have e3 : sp0 - 168#64 + 56#64 + 32#64 + 8#64 = sp0 - 72#64 := by bv_omega
  rw [e3, e2, e1, memRegion_eight (sp0 - 80#64), sepExists_sepConj_left]

theorem memRegion_104_fold (sp0 : BitVec 64)
    (w0 w1 w2 w3 vcap vptr vlen bvtab bptr blen bdata w80 : BitVec 64) :
    ((sp0 - 168#64) ↦₆₄ w0) ∗ ((sp0 - 160#64) ↦₆₄ w1) ∗
    ((sp0 - 152#64) ↦₆₄ w2) ∗ ((sp0 - 144#64) ↦₆₄ w3) ∗
    ((sp0 - 136#64) ↦₆₄ vcap) ∗ ((sp0 - 128#64) ↦₆₄ vptr) ∗ ((sp0 - 120#64) ↦₆₄ vlen) ∗
    ((sp0 - 112#64) ↦₆₄ bvtab) ∗ ((sp0 - 104#64) ↦₆₄ bptr) ∗
    ((sp0 - 96#64) ↦₆₄ blen) ∗ ((sp0 - 88#64) ↦₆₄ bdata) ∗
    ((sp0 - 80#64) ↦₆₄ w80) ∗ memRegion (sp0 - 72#64) 8 ⊢
    memRegion (sp0 - 168#64) 104 := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (memRegion_cons_sub sp0 80 w80 16)))))))))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (memRegion_cons_sub sp0 88 bdata 24))))))))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (memRegion_cons_sub sp0 96 blen 32)))))))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (memRegion_cons_sub sp0 104 bptr 40))))))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (memRegion_cons_sub sp0 112 bvtab 48)))))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (memRegion_cons_sub sp0 120 vlen 56))))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (memRegion_cons_sub sp0 128 vptr 64)))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (memRegion_cons_sub sp0 136 vcap 72))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (memRegion_cons_sub sp0 144 w3 80)))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (memRegion_cons_sub sp0 152 w2 88))) ?_
  refine Entails.trans (sepConj_mono_right (memRegion_cons_sub sp0 160 w1 96))
    (memRegion_cons_sub sp0 168 w0 104)

theorem memRegion_48_invalidWireType (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ w0 : BitVec 64, ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ b0) ∗ ((a + 9#64) ↦₈ b1) ∗ memRegion (a + 10#64) 38 := by
  rw [show (48 : Nat) = 8 + (1 + (1 + 38)) from rfl,
    memRegion_split a 8 (1 + (1 + 38)) (by decide),
    memRegion_split (a + 8#64) 1 (1 + 38) (by decide),
    memRegion_split (a + 8#64 + 1#64) 1 38 (by decide)]
  have e1 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  have e2 : a + 8#64 + 1#64 + 1#64 = a + 10#64 := by bv_omega
  rw [e2, e1, memRegion_eight a, sepExists_sepConj_left]
  apply congrArg SepProp.sepExists; funext w0
  rw [memRegion_one (a + 8#64), sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext b0
  rw [memRegion_one (a + 9#64), sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]

theorem fold_memRegion_40_bytes (a : BitVec 64) (b0 b1 : BitVec 8) :
    ((a + 8#64) ↦₈ b0) ∗ ((a + 9#64) ↦₈ b1) ∗ memRegion (a + 10#64) 38 ⊢
      memRegion (a + 8#64) 40 := by
  rw [show (40 : Nat) = 1 + (1 + 38) from rfl,
    memRegion_split (a + 8#64) 1 (1 + 38) (by decide),
    memRegion_split (a + 8#64 + 1#64) 1 38 (by decide)]
  have e1 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  have e2 : a + 8#64 + 1#64 + 1#64 = a + 10#64 := by bv_omega
  rw [e2, e1]
  exact sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo8_entails_memRegion _ _))

theorem memRegion_48_simple (a : BitVec 64) :
    memRegion a 48 = (∃∗ w0 : BitVec 64, (a ↦₆₄ w0) ∗ memRegion (a + 8#64) 40) := by
  rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide),
    memRegion_eight a, sepExists_sepConj_left]

theorem fold_memRegion_48_simple (a w0 : BitVec 64) :
    (a ↦₆₄ w0) ∗ memRegion (a + 8#64) 40 ⊢ memRegion a 48 :=
  memRegion_cons a w0 (n := 48) (by decide) (by decide)

theorem memRegion_48_sret24 (a : BitVec 64) :
    memRegion a 48 = memRegion a 24 ∗ memRegion (a + 24#64) 24 :=
  memRegion_split a 24 24 (by decide)

theorem stackAt_slice_to_decodeError (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStack =
      memRegion (sp0 - 8496#64) 80 ∗ stackAt (sp0 - 224#64) decodeErrorHookStack := by
  have h : sp0 - 224#64 - 8272#64 = sp0 - 8496#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 80 decodeErrorHookStack (by decide)

theorem stackAt_slice_to_varintSlow (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStack =
      memRegion (sp0 - 8496#64) 16 ∗ stackAt (sp0 - 224#64) varintSlowStack := by
  have h : sp0 - 224#64 - 8272#64 = sp0 - 8496#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 16 varintSlowStack (by decide)

theorem stackAt_slice_to_alloc (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStack =
      memRegion (sp0 - 8496#64) 4176 ∗ stackAt (sp0 - 224#64) allocHookStack := by
  have h : sp0 - 224#64 - 8272#64 = sp0 - 8496#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 4176 allocHookStack (by decide)

theorem stackAt_slice_to_bytesFromVec (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStack =
      memRegion (sp0 - 8496#64) 8224 ∗ stackAt (sp0 - 224#64) bytesFromVecStack := by
  have h : sp0 - 224#64 - 8272#64 = sp0 - 8496#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 8224 bytesFromVecStack (by decide)

theorem stackAt_slice_to_doReserve (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStack =
      memRegion (sp0 - 8496#64) 4064 ∗ stackAt (sp0 - 224#64) doReserveStack := by
  have h : sp0 - 224#64 - 8272#64 = sp0 - 8496#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 4064 doReserveStack (by decide)

theorem stackAt_slice_to_vtableDrop (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStack =
      memRegion (sp0 - 8496#64) 4128 ∗ stackAt (sp0 - 224#64) bytesVtableDropStack := by
  have h : sp0 - 224#64 - 8272#64 = sp0 - 8496#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 4128 bytesVtableDropStack (by decide)

theorem cells_sub_succ (sp : BitVec 64) (off k : Nat)
    (h : 8 < off := by decide) (ha : off < 2 ^ 64 := by decide) :
    cells (sp - BitVec.ofNat 64 off) (k + 1) =
      ∃∗ v : BitVec 64,
        ((sp - BitVec.ofNat 64 off) ↦₆₄ v) ∗
        cells (sp - BitVec.ofNat 64 (off - 8)) k := by
  rw [cells_succ, bv_sub_add_lit sp off 8 h ha]

theorem fold_slot_16 (slot w0 w1 : BitVec 64) :
    (slot ↦₆₄ w0) ∗ ((slot + 8#64) ↦₆₄ w1) ⊢ memRegion slot 16 := by
  refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion (slot + 8#64) w1)) ?_
  exact memRegion_cons slot w0 (n := 16) (by decide) (by decide)

/-! ## Shared postcondition, saved-register, and error epilogue lemmas -/

abbrev MergePost (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergeRawSpec A).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePanic (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergeRawSpec A).onPanic x s0 sf ∗ R)

abbrev savedRegsStack (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

def bm_HighCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem bm_HighCalleeSaved.refl (s0 : State) : bm_HighCalleeSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bm_HighCalleeSaved.of_calleeSaved {s0 s sf : State}
    (h : bm_HighCalleeSaved s0 s) (hcs : CalleeSavedPreserved s sf) :
    bm_HighCalleeSaved s0 sf := by
  rcases h with ⟨h25, h26, h27, h28, hv⟩
  rcases hcs with ⟨_, _, _, _, _, _, c25, c26, c27, c28, _, cv⟩
  exact ⟨c25.trans h25, c26.trans h26, c27.trans h27, c28.trans h28, cv.trans hv⟩

theorem spAligned_sub_224 {s : State} (h : s.spAligned = true) :
    ((s.sp - 224#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned] at h
  simpa only [arm64_norm] using h


/-! ## `Vec<u8>` clear/copy helpers and epilogue drop -/

def bm_vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    (if cap = 0#64 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem bm_vecU8At_eq_header_sep_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ bm_vecU8Buf A cap ptr bs := by
  unfold vecU8At bm_vecU8Buf
  ac_rfl

theorem vecU8Buf_clear (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    bm_vecU8Buf A cap ptr bs ⊢ bm_vecU8Buf A cap ptr [] := by
  unfold bm_vecU8Buf
  apply Entails.pure_left
  rintro ⟨hlen, hcap_lt, hptr⟩
  apply Entails.pure_right ⟨Nat.zero_le _, hcap_lt, hptr⟩
  by_cases hcap : cap = 0#64
  · simp only [hcap, ↓reduceIte]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte, List.length_nil, BitVec.add_zero,
      Nat.sub_zero, pointsToBytes_nil, emp_sepConj]
    apply sepConj_mono_right
    have hsplit : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
    conv => rhs; rw [hsplit, memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

theorem fold_vecU8At_clear (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗ bm_vecU8Buf A cap ptr bs ⊢
      vecU8At A v cap ptr [] := by
  rw [bm_vecU8At_eq_header_sep_buf, vecHeader]
  simp only [List.length_nil, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (vecU8Buf_clear A cap ptr bs)))

theorem vecU8At_nil_eq (A : RustAlloc) (valPtr cap' ptr' : BitVec 64)
    (v : List (BitVec 8)) (hpos : 0 < v.length) (hle : v.length ≤ cap'.toNat) :
    vecU8At A valPtr cap' ptr' [] =
      (⌜0 ≤ cap'.toNat ∧ cap'.toNat < 2 ^ 63 ∧ ptr' ≠ 0#64⌝ ∗
        (valPtr ↦₆₄ cap') ∗ ((valPtr + 8#64) ↦₆₄ ptr') ∗ ((valPtr + 16#64) ↦₆₄ 0#64) ∗
        A.live ptr' cap'.toNat 1 ∗
        memRegion ptr' v.length ∗
        memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length)) := by
  have hcap_ne : cap' ≠ 0#64 := by
    rintro rfl
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hle
    omega
  have hsplit : cap'.toNat = v.length + (cap'.toNat - v.length) := by omega
  have hmr : memRegion ptr' cap'.toNat =
      memRegion ptr' v.length ∗ memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length) := by
    conv => lhs; rw [hsplit]
    exact memRegion_split ptr' v.length (cap'.toNat - v.length) (by omega)
  rw [bm_vecU8At_eq_header_sep_buf]
  unfold vecHeader bm_vecU8Buf
  simp only [List.length_nil, hcap_ne, ↓reduceIte, BitVec.add_zero,
    Nat.sub_zero, pointsToBytes_nil, emp_sepConj, hmr]
  ac_rfl

theorem vecU8At_copied_eq (A : RustAlloc) (valPtr cap' ptr' : BitVec 64)
    (v : List (BitVec 8)) (hpos : 0 < v.length) (hle : v.length ≤ cap'.toNat) :
    vecU8At A valPtr cap' ptr' v =
      (⌜v.length ≤ cap'.toNat ∧ cap'.toNat < 2 ^ 63 ∧ ptr' ≠ 0#64⌝ ∗
        (valPtr ↦₆₄ cap') ∗ ((valPtr + 8#64) ↦₆₄ ptr') ∗
        ((valPtr + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗
        A.live ptr' cap'.toNat 1 ∗ (ptr' ↦ₛ v) ∗
        memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length)) := by
  have hcap_ne : cap' ≠ 0#64 := by
    rintro rfl
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hle
    omega
  rw [bm_vecU8At_eq_header_sep_buf]
  unfold vecHeader bm_vecU8Buf
  simp only [hcap_ne, ↓reduceIte]
  ac_rfl

theorem fold_vecU8At_copied (A : RustAlloc) (valPtr cap' ptr' : BitVec 64)
    (v : List (BitVec 8)) (hpos : 0 < v.length) (hle : v.length ≤ cap'.toNat)
    (hcap_lt : cap'.toNat < 2 ^ 63) (hptr : ptr' ≠ 0#64) :
    (valPtr ↦₆₄ cap') ∗ ((valPtr + 8#64) ↦₆₄ ptr') ∗
      ((valPtr + 16#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗
      A.live ptr' cap'.toNat 1 ∗ (ptr' ↦ₛ v) ∗
      memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length) ⊢
      vecU8At A valPtr cap' ptr' v := by
  rw [vecU8At_copied_eq A valPtr cap' ptr' v hpos hle]
  exact Entails.pure_right ⟨hle, hcap_lt, hptr⟩ (Entails.refl _)

theorem bytesBoxU8Buf_nonempty (A : RustAlloc) (tmpPtr : BitVec 64)
    (v : List (BitVec 8)) (hpos : 0 < v.length) :
    bytesBoxU8Buf A tmpPtr v =
      (⌜tmpPtr ≠ 0#64 ∧ v.length < 2 ^ 63⌝ ∗ A.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v)) := by
  have hne : v ≠ [] := List.ne_nil_of_length_pos hpos
  unfold bytesBoxU8Buf
  simp only [hne, ↓reduceIte]
  rfl

theorem vecU8At_entails_exists (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    {restLen : Nat} (hcapOk : BytesMergeCapOk cap restLen) :
    vecU8At A v cap ptr bs ⊢
      ∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜BytesMergeCapOk cap' restLen⌝ ∗ vecU8At A v cap' ptr' bs :=
  Entails.sepExists_right cap
    (Entails.sepExists_right ptr (Entails.pure_right hcapOk (Entails.refl _)))


theorem fold_bytesBoxU8Buf_nonempty (A : RustAlloc) (tmpPtr : BitVec 64)
    (v : List (BitVec 8)) (hpos : 0 < v.length)
    (htmp : tmpPtr ≠ 0#64) (hlt : v.length < 2 ^ 63) :
    A.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v) ⊢ bytesBoxU8Buf A tmpPtr v := by
  rw [bytesBoxU8Buf_nonempty A tmpPtr v hpos]
  exact Entails.pure_right ⟨htmp, hlt⟩ (Entails.refl _)


/-! ## `Stage2ContractsX` / `AllocContractsX` variants -/

/-- `0x40 + decodeErrorHookStackX` (`32832` bytes) for `decode_varint_slow` on `Stage2ContractsX`. -/
abbrev varintSlowStackX : Nat := 64 + decodeErrorHookStackX

/-- `decode_varint_slow` contract with `varintSlowStackX` (`32832` bytes). -/
def decodeVarintSlowSpecBMX (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (slotA, slot, ptr, bs) s =>
    ⌜s.readReg64 .x0 = slotA ∧ bs.length < 2 ^ 64⌝ ∗
      (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp varintSlowStackX
  post := fun (slotA, slot, ptr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp varintSlowStackX ∗
      match varintSlow bs with
      | some (v, k) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝ ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k))
      | none =>
        ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length))) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length))
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `__rust_no_alloc_shim_is_unstable_v2` contract with `decodeVarintSliceStackX` (`32848` bytes). -/
def session2ShimSpecBMX : Spec Unit where
  pre := fun _ s => ⌜True⌝ ∗ stackAt s.sp decodeVarintSliceStackX
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp decodeVarintSliceStackX

/-- `memcpy` contract with `decodeVarintSliceStackX` (`32848` bytes). -/
def session2MemcpySpecBMX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp decodeVarintSliceStackX)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
      stackAt s0.sp decodeVarintSliceStackX

def BytesMergeOkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMergeName)
    (bytesMergeSpecX A img)

theorem stackAt_bytesMergeX_entry (sp0 : BitVec 64) :
    stackAt sp0 bytesMergeStackX =
      stackAt (sp0 - 224#64) decodeVarintSliceStackX ∗
      memRegion (sp0 - 224#64) 8 ∗
      memRegion (sp0 - 216#64) 48 ∗
      memRegion (sp0 - 168#64) 104 ∗
      cells (sp0 - 64#64) 8 := by
  have h1 : stackAt sp0 bytesMergeStackX =
      stackAt (sp0 - 224#64) decodeVarintSliceStackX ∗ memRegion (sp0 - 224#64) 224 := by
    simp only [bytesMergeStackX, decodeVarintSliceStackX, decodeErrorHookStackX, extHookStack, stackAt]
    rw [show (224 + (80 + 2 * 2 ^ 14) : Nat) = (80 + 2 * 2 ^ 14) + 224 from rfl,
      memRegion_split _ (80 + 2 * 2 ^ 14) 224 (by decide)]
    have e1 : sp0 - BitVec.ofNat 64 ((80 + 2 * 2 ^ 14) + 224) =
        sp0 - 224#64 - BitVec.ofNat 64 (80 + 2 * 2 ^ 14) := by bv_omega
    have e2 : sp0 - BitVec.ofNat 64 ((80 + 2 * 2 ^ 14) + 224) + BitVec.ofNat 64 (80 + 2 * 2 ^ 14) =
        sp0 - 224#64 := by bv_omega
    rw [e2, e1]
  have h2 : memRegion (sp0 - 224#64) 224 =
      memRegion (sp0 - 224#64) 8 ∗ memRegion (sp0 - 216#64) 48 ∗
      memRegion (sp0 - 168#64) 104 ∗ cells (sp0 - 64#64) 8 := by
    rw [show (224 : Nat) = 8 + (48 + (104 + 8 * 8)) from rfl,
      memRegion_split (sp0 - 224#64) 8 (48 + (104 + 8 * 8)) (by decide),
      memRegion_split (sp0 - 224#64 + 8#64) 48 (104 + 8 * 8) (by decide),
      memRegion_split (sp0 - 224#64 + 8#64 + 48#64) 104 (8 * 8) (by decide),
      memRegion_cells _ 8 (by decide)]
    have e1 : sp0 - 224#64 + 8#64 = sp0 - 216#64 := by bv_omega
    have e2 : sp0 - 224#64 + 8#64 + 48#64 = sp0 - 168#64 := by bv_omega
    have e3 : sp0 - 224#64 + 8#64 + 48#64 + 104#64 = sp0 - 64#64 := by bv_omega
    rw [e3, e2, e1]
  rw [h1, h2]

theorem fold_stackAt_bytesMergeX (sp0 : BitVec 64)
    (w29 w30 w24 w23 w22 w21 w20 w19 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackX ∗
    memRegion (sp0 - 224#64) 8 ∗
    memRegion (sp0 - 216#64) 48 ∗
    memRegion (sp0 - 168#64) 104 ∗
    ((sp0 - 64#64) ↦₆₄ w29) ∗ ((sp0 - 56#64) ↦₆₄ w30) ∗
    ((sp0 - 48#64) ↦₆₄ w24) ∗ ((sp0 - 40#64) ↦₆₄ w23) ∗
    ((sp0 - 32#64) ↦₆₄ w22) ∗ ((sp0 - 24#64) ↦₆₄ w21) ∗
    ((sp0 - 16#64) ↦₆₄ w20) ∗ ((sp0 - 8#64) ↦₆₄ w19) ⊢
    stackAt sp0 bytesMergeStackX := by
  rw [stackAt_bytesMergeX_entry sp0]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (fold_cells_8 sp0 w29 w30 w24 w23 w22 w21 w20 w19))))

theorem stackAt_sliceX_to_decodeErrorX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackX =
      memRegion (sp0 - 33072#64) 80 ∗ stackAt (sp0 - 224#64) decodeErrorHookStackX := by
  have h : sp0 - 224#64 - 32848#64 = sp0 - 33072#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 80 decodeErrorHookStackX (by decide)

theorem stackAt_sliceX_to_varintSlowX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackX =
      memRegion (sp0 - 33072#64) 16 ∗ stackAt (sp0 - 224#64) varintSlowStackX := by
  have h : sp0 - 224#64 - 32848#64 = sp0 - 33072#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 16 varintSlowStackX (by decide)

theorem stackAt_sliceX_to_allocX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackX =
      memRegion (sp0 - 33072#64) 16464 ∗ stackAt (sp0 - 224#64) extHookStack := by
  have h : sp0 - 224#64 - 32848#64 = sp0 - 33072#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 16464 extHookStack (by decide)

theorem stackAt_sliceX_to_bytesFromVecX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackX =
      memRegion (sp0 - 33072#64) 32800 ∗ stackAt (sp0 - 224#64) bytesFromVecStack := by
  have h : sp0 - 224#64 - 32848#64 = sp0 - 33072#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 32800 bytesFromVecStack (by decide)

theorem stackAt_sliceX_to_doReserveX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackX =
      memRegion (sp0 - 33072#64) 16352 ∗ stackAt (sp0 - 224#64) doReserveStackX := by
  have h : sp0 - 224#64 - 32848#64 = sp0 - 33072#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 16352 doReserveStackX (by decide)

theorem stackAt_sliceX_to_vtableDropX (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarintSliceStackX =
      memRegion (sp0 - 33072#64) 16416 ∗ stackAt (sp0 - 224#64) bytesVtableDropStackX := by
  have h : sp0 - 224#64 - 32848#64 = sp0 - 33072#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 16416 bytesVtableDropStackX (by decide)

abbrev MergePostX (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergeRawSpecX A).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePanicX (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergeRawSpecX A).onPanic x s0 sf ∗ R)


/-! ## Unified Stack & Spec Parameterization (`base` / `_x` / `W`) -/

theorem SepWPp.bm_call_inv_opt {α : Type} {prog : Program} {oimg : Option Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (specWithOptInv oimg spec))
    (hinv : CryptoVerification.InImageLift.OptCallInv oimg s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      CryptoVerification.InImageLift.OptCallInv oimg sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  have hmid :
      SepWPp prog ret_pc s P
        (fun sm P_m => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ P_m = spec.post x s sm ∗ F)
        Qp := by
    refine ProofLib.SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩) hoom
    intro R hm
    rw [specWithOptInv, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, hpre R hm⟩
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out⟩ := hmid R hm hL
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hinv.of_steps hsteps) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

theorem SepWPp.bm_call_frame_opt_inv {α : Type} {prog : Program} {oimg : Option Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (specWithOptInv oimg spec))
    (hinv : CryptoVerification.InImageLift.OptCallInv oimg s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      CryptoVerification.InImageLift.OptCallInv oimg sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.bm_call_inv_opt (x := x) (F := F) hcall hinv hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

abbrev bmSliceStack (errStack : Nat) : Nat := 0x50 + errStack
abbrev bmTotalStack (errStack : Nat) : Nat := 0xe0 + bmSliceStack errStack

def bmExtraStack (sp0 : BitVec 64) (errStack subStack : Nat) : SepProp :=
  memRegion (sp0 - BitVec.ofNat 64 (bmTotalStack errStack)) (bmSliceStack errStack - subStack)

theorem stackAt_bytesMergeGen_entry (sp0 : BitVec 64) (errStack : Nat)
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64) :
    stackAt sp0 (bmTotalStack errStack) =
      stackAt (sp0 - 224#64) (bmSliceStack errStack) ∗
      memRegion (sp0 - 224#64) 8 ∗
      memRegion (sp0 - 216#64) 48 ∗
      memRegion (sp0 - 168#64) 104 ∗
      cells (sp0 - 64#64) 8 := by
  have h1 : stackAt sp0 (bmTotalStack errStack) =
      stackAt (sp0 - 224#64) (bmSliceStack errStack) ∗ memRegion (sp0 - 224#64) 224 := by
    dsimp only [bmTotalStack, bmSliceStack, stackAt] at hbnd ⊢
    rw [Nat.add_comm 224 (80 + errStack),
      memRegion_split _ (80 + errStack) 224 (by omega)]
    have e1 : sp0 - BitVec.ofNat 64 ((80 + errStack) + 224) =
        sp0 - 224#64 - BitVec.ofNat 64 (80 + errStack) := by
      rw [BitVec.sub_sub, show (224#64 : BitVec 64) = BitVec.ofNat 64 224 from rfl,
        ← BitVec.ofNat_add, Nat.add_comm]
    have e2 : sp0 - BitVec.ofNat 64 ((80 + errStack) + 224) + BitVec.ofNat 64 (80 + errStack) =
        sp0 - 224#64 := by
      rw [e1, BitVec.sub_add_cancel]
    rw [e2, e1]
  have h2 : memRegion (sp0 - 224#64) 224 =
      memRegion (sp0 - 224#64) 8 ∗ memRegion (sp0 - 216#64) 48 ∗
      memRegion (sp0 - 168#64) 104 ∗ cells (sp0 - 64#64) 8 := by
    rw [show (224 : Nat) = 8 + (48 + (104 + 8 * 8)) from rfl,
      memRegion_split (sp0 - 224#64) 8 (48 + (104 + 8 * 8)) (by decide),
      memRegion_split (sp0 - 224#64 + 8#64) 48 (104 + 8 * 8) (by decide),
      memRegion_split (sp0 - 224#64 + 8#64 + 48#64) 104 (8 * 8) (by decide),
      memRegion_cells _ 8 (by decide)]
    have e1 : sp0 - 224#64 + 8#64 = sp0 - 216#64 := by bv_omega
    have e2 : sp0 - 224#64 + 8#64 + 48#64 = sp0 - 168#64 := by bv_omega
    have e3 : sp0 - 224#64 + 8#64 + 48#64 + 104#64 = sp0 - 64#64 := by bv_omega
    rw [e3, e2, e1]
  rw [h1, h2]

theorem fold_stackAt_bytesMergeGen (sp0 : BitVec 64) (errStack : Nat)
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (w29 w30 w24 w23 w22 w21 w20 w19 : BitVec 64) :
    stackAt (sp0 - 224#64) (bmSliceStack errStack) ∗
    memRegion (sp0 - 224#64) 8 ∗
    memRegion (sp0 - 216#64) 48 ∗
    memRegion (sp0 - 168#64) 104 ∗
    ((sp0 - 64#64) ↦₆₄ w29) ∗ ((sp0 - 56#64) ↦₆₄ w30) ∗
    ((sp0 - 48#64) ↦₆₄ w24) ∗ ((sp0 - 40#64) ↦₆₄ w23) ∗
    ((sp0 - 32#64) ↦₆₄ w22) ∗ ((sp0 - 24#64) ↦₆₄ w21) ∗
    ((sp0 - 16#64) ↦₆₄ w20) ∗ ((sp0 - 8#64) ↦₆₄ w19) ⊢
    stackAt sp0 (bmTotalStack errStack) := by
  rw [stackAt_bytesMergeGen_entry sp0 errStack hbnd]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (fold_cells_8 sp0 w29 w30 w24 w23 w22 w21 w20 w19))))

theorem stackAt_sliceGen_split (sp0 : BitVec 64) (errStack subStack : Nat)
    (hle : subStack ≤ bmSliceStack errStack)
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64) :
    stackAt (sp0 - 224#64) (bmSliceStack errStack) =
      bmExtraStack sp0 errStack subStack ∗ stackAt (sp0 - 224#64) subStack := by
  dsimp only [bmExtraStack, bmTotalStack, bmSliceStack] at hle hbnd ⊢
  have hsub : (80 + errStack - subStack) + subStack = 80 + errStack := Nat.sub_add_cancel hle
  have h : sp0 - 224#64 - BitVec.ofNat 64 (80 + errStack) =
      sp0 - BitVec.ofNat 64 (224 + (80 + errStack)) := by
    rw [BitVec.sub_sub, show (224#64 : BitVec 64) = BitVec.ofNat 64 224 from rfl, ← BitVec.ofNat_add]
  have hs := stackAt_split_sub (sp0 - 224#64) (80 + errStack - subStack) subStack (by omega)
  rwa [hsub, h] at hs

abbrev bmCapCond (reqCap : Bool) (cap : BitVec 64) (n : Nat) : Prop :=
  match reqCap with
  | true => BytesMergeCapOk cap n
  | false => True

theorem bmCapCond_zero {reqCap : Bool} {n : Nat} : bmCapCond reqCap 0#64 n := by
  cases reqCap <;> [exact trivial; exact bytesMergeCapOk_zero]

theorem bmCapCond_mono {reqCap : Bool} {cap : BitVec 64} {n m : Nat}
    (h : bmCapCond reqCap cap m) (hle : n ≤ m) : bmCapCond reqCap cap n := by
  cases reqCap
  · exact trivial
  · exact bytesMergeCapOk_mono h hle

theorem bmCapCond_after_reserve {reqCap : Bool} {cap : BitVec 64} {vLen restLen bsLen : Nat}
    (h : bmCapCond reqCap cap bsLen) (hult : cap.toNat < vLen)
    (hsum : 1 + vLen + restLen ≤ bsLen) (hbs : bsLen < 2 ^ 63) :
    bmCapCond reqCap (BitVec.ofNat 64 (reserveCap cap.toNat 0 vLen)) restLen := by
  cases reqCap
  · exact trivial
  · exact bytesMergeCapOk_after_reserve h hult hsum hbs

abbrev bmPreBound (reqCap : Bool) (s : State) (x : BytesMergeGhost) : Prop :=
  match reqCap with
  | true =>
    (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length
  | false =>
    (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 62

abbrev bmPostVec (reqCap : Bool) (A : RustAlloc) (valPtr : BitVec 64)
    (v rest : List (BitVec 8)) : SepProp :=
  match reqCap with
  | true =>
    ∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A valPtr cap' ptr' v
  | false =>
    ∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64, vecU8At A valPtr cap' ptr' v

theorem vecU8At_entails_bmPostVec (reqCap : Bool) (A : RustAlloc)
    (v cap ptr : BitVec 64) (bs rest : List (BitVec 8))
    (hcapOk : bmCapCond reqCap cap rest.length) :
    vecU8At A v cap ptr bs ⊢ bmPostVec reqCap A v bs rest := by
  cases reqCap
  · exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))
  · exact vecU8At_entails_exists A v cap ptr bs hcapOk

def bytesMergeRawSpecGen (A : RustAlloc) (errStack : Nat) (reqCap : Bool) : Spec BytesMergeGhost where
  pre := fun x s =>
    ⌜bmPreBound reqCap s x⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (bmTotalStack errStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp (bmTotalStack errStack) ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          bmPostVec reqCap A x.valPtr v rest ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def bytesMergeSpecGen (A : RustAlloc) (errStack : Nat) (reqCap : Bool) (img : Obj.Image) :
    Spec BytesMergeGhost :=
  (bytesMergeRawSpecGen A errStack reqCap).inImage img

theorem bytesMergeRawSpecGen_base_eq (A : RustAlloc) :
    bytesMergeRawSpecGen A decodeErrorHookStack true = bytesMergeRawSpec A := rfl

theorem bytesMergeRawSpecGen_x_eq (A : RustAlloc) :
    bytesMergeRawSpecGen A decodeErrorHookStackX true = bytesMergeRawSpecX A := rfl

abbrev MergePostGen (errStack : Nat) (reqCap : Bool) (A : RustAlloc)
    (x : BytesMergeGhost) (s0 : State) (R : SepProp) (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergeRawSpecGen A errStack reqCap).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePanicGen (errStack : Nat) (reqCap : Bool) (A : RustAlloc)
    (x : BytesMergeGhost) (s0 : State) (R : SepProp) (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMergeRawSpecGen A errStack reqCap).onPanic x s0 sf ∗ R)

def bmShimSpecGen (errStack : Nat) : Spec Unit where
  pre := fun _ s => ⌜True⌝ ∗ stackAt s.sp (bmSliceStack errStack)
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp (bmSliceStack errStack)

def bmMemcpySpecGen (errStack : Nat) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp (bmSliceStack errStack))
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
      stackAt s0.sp (bmSliceStack errStack)

def decodeVarintSlowSpecBMGen (A : RustAlloc) (errStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (slotA, slot, ptr, bs) s =>
    ⌜s.readReg64 .x0 = slotA ∧ bs.length < 2 ^ 64⌝ ∗
      (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp (64 + errStack)
  post := fun (slotA, slot, ptr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp (64 + errStack) ∗
      match varintSlow bs with
      | some (v, k) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝ ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k))
      | none =>
        ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length))) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length))
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def decodeVarintSliceSpecBMGen (A : RustAlloc) (errStack : Nat) : Spec DecodeVarintSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ptr ∧
      (s.readReg64 .x2).toNat = x.bs.length ∧ x.bs.length < 2 ^ 63 ∧ VarintSlicePre x.bs⌝ ∗
      memRegion x.ret 24 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s.sp (bmSliceStack errStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ varintSliceResultAt A x.ret x.bs (decodeVarint x.bs) ∗
      (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt s0.sp (bmSliceStack errStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def bytesVtableDropSpecBMGen (A : RustAlloc) (hStack : Nat) (ptr : BitVec 64)
    (bs : List (BitVec 8)) (off : Nat) : Spec Unit where
  pre := fun _ s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp (hStack + 48)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp (hStack + 48)

theorem bmShim_inImage_of_base {img : Obj.Image} {prog : Program} {addr : BitVec 64}
    {errStack : Nat} (hshim : subroutine_ok prog addr sessionShimSpec) :
    subroutine_ok prog addr ((bmShimSpecGen errStack).inImage img) := by
  apply subroutine_ok_inImage_of_subroutine_ok img
  have h := subroutine_ok_withStack_of_subroutine_ok hshim (bmSliceStack errStack)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack sessionShimSpec (bmSliceStack errStack)).pre x s0 ∗ R := by
    dsimp only [withStack, sessionShimSpec, bmShimSpecGen] at hpre ⊢
    simpa only [pure_true, emp_sepConj, sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionShimSpec, bmShimSpecGen] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem bmMemcpy_inImage_of_frameless {img : Obj.Image} {prog : Program} {addr : BitVec 64}
    {errStack : Nat} (hmc : subroutine_ok prog addr framelessMemcpySpec) :
    subroutine_ok prog addr ((bmMemcpySpecGen errStack).inImage img) := by
  apply subroutine_ok_inImage_of_subroutine_ok img
  have h := subroutine_ok_withStack_of_subroutine_ok hmc (bmSliceStack errStack)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack framelessMemcpySpec (bmSliceStack errStack)).pre x s0 ∗ R := by
    dsimp only [withStack, framelessMemcpySpec, bmMemcpySpecGen] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, framelessMemcpySpec, bmMemcpySpecGen] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

section FnOffShield
attribute [local irreducible] _root_.Arm64.Program.fnOff

theorem epilogue_err_0x0a4_gen {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 164#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 ≠ 0#64)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (decodeErrorAtStackLen A (s.readReg64 .x0) 0 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨h25, h26, h27, h28⟩ := hhigh
  merge_fetches_H img.base H bytesMerge_fnOff 164 24
  dsimp only [savedRegsStack] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp errStack hbnd
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  dsimp only [Reg.x0] at hx0 hmf ⊢
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64, Reg.x0, hx0, htrace,
    ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj]
  convert hmf using 2
  ac_rfl


theorem epilogue_decodeErrorFrom_gen {img : Obj.Image} {oimg : Option Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      (specWithOptInv oimg (decodeErrorFromSpecWithStack A errStack)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w)
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hinv : CryptoVerification.InImageLift.OptCallInv oimg s) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  merge_fetches_H img.base H bytesMerge_fnOff 248 32
  dsimp only [savedRegsStack] at hpc hdef ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_optImage hinv (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hinv_call
  refine SepWPp.bm_call_frame_opt_inv (x := (s0.sp - 216#64, w))
    (T := ((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
      A.pool ∗ stackAt (s0.sp - 224#64) errStack)
    hdef hinv_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeErrorFromSpecWithStack, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [KindNoHeap, wp_norm, arm64_norm, hsp, hw, and_self])
    (by rw [stackAt_sliceGen_split s0.sp errStack errStack (Nat.le_add_left errStack 0x50) hbnd]; sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      simp only [bytesMergeRawSpecGen, decodeErrorFromSpecWithStack,
        State.trace_setPC, State.trace_writeReg64, allocFailedIn, htrace] at hm ⊢
      exact allowPanic_frame id hm) ?_
  intro sf_de hpcf hrunf hspf hcsf _
  have hhigh' : bm_HighCalleeSaved s0 sf_de := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [decodeErrorFromSpecWithStack, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨hx0, htr⟩ => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    (by rw [stackAt_sliceGen_split s0.sp errStack errStack (Nat.le_add_left errStack 0x50) hbnd]; exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp errStack hbnd
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64, Reg.x0, hx0, htr,
    ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj]
  convert hmf using 2
  ac_rfl


theorem epilogue_vtableDrop_0x2d8_gen {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hdrop_le : hStack + 48 ≤ bmSliceStack errStack)
    (himg : Obj.Loads libsignalSessionImage img)
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr v.length)
      ((bytesVtableDropSpecBMGen A hStack tmpPtr v v.length).inImage img))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hcapOk : bmCapCond reqCap cap' rest.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 728#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length + BitVec.ofNat 64 v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesVtable img.base tmpPtr v.length) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr cap' ptr' v ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  merge_fetches_H img.base H bytesMerge_fnOff 728 48
  dsimp only [savedRegsStack] at hpc hVtableDrop ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
  examples_hide_fetches
  apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := bytesDropFnAddr img.base tmpPtr v.length)
  apply SepWP.with_vtableSlot hVtableSlot himg tmpPtr v.length hfl
  wp_steps
  apply SepWP.drop_left
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl_call hsym_call
  refine SepWPp.bm_call_frame_inv (x := ())
    (T := bytesBoxU8Buf A tmpPtr v ∗ A.pool ∗ stackAt (s0.sp - 224#64) (hStack + 48))
    hVtableDrop hfl_call hsym_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesVtableDropSpecBMGen, arm64_norm, hsp]; rfl)
    (by simp only [Nat.le_refl, Nat.sub_self, BitVec.ofNat_eq_ofNat, and_self])
    (by rw [stackAt_sliceGen_split s0.sp errStack (hStack + 48) hdrop_le hbnd]; sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (by intro _ _ hm; dsimp only [bytesVtableDropSpecBMGen] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
  intro sf_dr hpcf hrunf hspf hcsf hflf hsymf
  have hhigh' : bm_HighCalleeSaved s0 sf_dr := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [bytesVtableDropSpecBMGen, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun htr => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    (by rw [stackAt_sliceGen_split s0.sp errStack (hStack + 48) hdrop_le hbnd]; exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp errStack hbnd
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.fold (vecU8At_entails_bmPostVec reqCap A x.valPtr cap' ptr' v rest hcapOk)
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64, Reg.x0, htr, ↓reduceIte,
    pure_true, emp_sepConj]
  convert hmf using 2
  ac_rfl


theorem phase3_from_0x2b4_gen {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hdrop_le : hStack + 48 ≤ bmSliceStack errStack)
    (himg : Obj.Loads libsignalSessionImage img)
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmMemcpySpecGen errStack).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr v.length)
      ((bytesVtableDropSpecBMGen A hStack tmpPtr v v.length).inImage img))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hcapOk : bmCapCond reqCap cap' rest.length)
    (hcap' : v.length ≤ cap'.toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 692#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = bytesVtable img.base tmpPtr v.length) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr cap' ptr' [] ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  rcases v with _ | ⟨b0, v'⟩
  · have hep := fun {s : State} =>
      @epilogue_vtableDrop_0x2d8_gen img A H hStack errStack reqCap hbnd hdrop_le himg hVtableSlot x s0 s R [] rest tmpPtr cap' ptr' hVtableDrop hmerge hcapOk
    merge_fetches_H img.base H bytesMerge_fnOff 692 4
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
    examples_hide_fetches
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (728))
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl1 hsym1
    exact hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      hhigh hfl1 hsym1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24])
  · set v := b0 :: v'
    have hep := fun {s : State} =>
      @epilogue_vtableDrop_0x2d8_gen img A H hStack errStack reqCap hbnd hdrop_le himg hVtableSlot x s0 s R v rest tmpPtr cap' ptr' hVtableDrop hmerge hcapOk
    have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
      apply beq_false_of_ne
      intro h
      have h2 := congrArg BitVec.toNat h
      rw [hlen_toNat] at h2
      exact absurd h2 (by dsimp [v]; omega)
    have hbytesPtr : bytesPtr tmpPtr v.length = tmpPtr := by
      unfold bytesPtr
      have : v.length ≠ 0 := by omega
      simp [this]
    rw [vecU8At_nil_eq A x.valPtr cap' ptr' v hpos hcap', sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, hcap_lt, hptr'⟩ => ?_
    rw [bytesBoxU8Buf_nonempty A tmpPtr v hpos]
    refine SepWPp.weaken_pre (P' := ⌜tmpPtr ≠ 0#64 ∧ v.length < 2 ^ 63⌝ ∗
      ((x.valPtr ↦₆₄ cap') ∗ ((x.valPtr + 8#64) ↦₆₄ ptr') ∗ ((x.valPtr + 16#64) ↦₆₄ 0#64) ∗
        A.live ptr' cap'.toNat 1 ∗ memRegion ptr' v.length ∗
        memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length) ∗
        A.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v) ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨htmp_ne, hv_lt63⟩ => ?_
    merge_fetches_H img.base H bytesMerge_fnOff 692 36
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
    examples_hide_fetches
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl1 hsym1
    refine SepWPp.bm_call_frame_inv (x := (ptr', tmpPtr, v))
      (T := memRegion ptr' v.length ∗ (tmpPtr ↦ₛ v) ∗ stackAt (s0.sp - 224#64) (bmSliceStack errStack))
      hmc hfl1 hsym1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm, hlen_toNat, and_self])
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; dsimp only [bmMemcpySpecGen] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
    intro sf_mc hpcf hrunf hspf hcsf hflf hsymf
    have hhigh' : bm_HighCalleeSaved s0 sf_mc := hhigh.of_calleeSaved hcsf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, _, _, _, _, h29f⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h29f
    simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp, htrace]
    refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
    apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + bv% (728))
    wp_steps
    apply SepWP.fold (fold_bytesBoxU8Buf_nonempty A tmpPtr v hpos htmp_ne hv_lt63)
      (by sep_focus)
    apply SepWP.fold (fold_vecU8At_copied A x.valPtr cap' ptr' v hpos hcap' hcap_lt hptr')
      (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hfl2 hsym2
    refine SepWPp.weaken_pre ?_ (hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by obtain ⟨h25, h26, h27, h28⟩ := hhigh'; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
      hfl2 hsym2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21, h20f, hx20, hbytesPtr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24]))
    exact Entails.of_eq (by ac_rfl)


end FnOffShield

/-! ## Base & `_x` Specializations -/

theorem epilogue_err_0x0a4 {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 164#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 ≠ 0#64)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (decodeErrorAtStackLen A (s.readReg64 .x0) 0 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) :=
  epilogue_err_0x0a4_gen (errStack := decodeErrorHookStack) (reqCap := true)
    (by decide) hmerge hpc hrun hsp hsp_align htrace hx0 hhigh

theorem epilogue_err_0x0a4_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 164#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 ≠ 0#64)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (decodeErrorAtStackLen A (s.readReg64 .x0) 0 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostX A x s0 R) (MergePanicX A x s0 R) :=
  epilogue_err_0x0a4_gen (errStack := decodeErrorHookStackX) (reqCap := true)
    (by decide) hmerge hpc hrun hsp hsp_align htrace hx0 hhigh

theorem epilogue_decodeErrorFrom {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      (decodeErrorFromSpec A))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w)
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) :=
  epilogue_decodeErrorFrom_gen (oimg := none) (errStack := decodeErrorHookStack) (reqCap := true)
    (by decide) (subroutine_ok_to_optNone hdef) hw hmerge hpc hrun hsp hsp_align htrace hhigh trivial

theorem epilogue_decodeErrorFrom_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w)
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostX A x s0 R) (MergePanicX A x s0 R) :=
  epilogue_decodeErrorFrom_gen (oimg := some img) (errStack := decodeErrorHookStackX) (reqCap := true)
    (by decide) hdef hw hmerge hpc hrun hsp hsp_align htrace hhigh ⟨hfl, hsym⟩

theorem epilogue_vtableDrop_0x2d8 {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr v.length)
      ((bytesVtableDropSpec A tmpPtr v v.length).inImage img))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hcapOk : BytesMergeCapOk cap' rest.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 728#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length + BitVec.ofNat 64 v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesVtable img.base tmpPtr v.length) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr cap' ptr' v ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) :=
  epilogue_vtableDrop_0x2d8_gen (hStack := allocHookStack) (errStack := decodeErrorHookStack)
    (reqCap := true) (by decide) (by decide) himg hVtableSlot hVtableDrop hmerge hcapOk
    hpc hrun hsp hsp_align htrace hhigh hfl hsym hx21 hx22 hx24

theorem epilogue_vtableDrop_0x2d8_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr v.length)
      ((bytesVtableDropSpecX A tmpPtr v v.length).inImage img))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hcapOk : BytesMergeCapOk cap' rest.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 728#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length + BitVec.ofNat 64 v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesVtable img.base tmpPtr v.length) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr cap' ptr' v ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostX A x s0 R) (MergePanicX A x s0 R) :=
  epilogue_vtableDrop_0x2d8_gen (hStack := extHookStack) (errStack := decodeErrorHookStackX)
    (reqCap := true) (by decide) (by decide) himg hVtableSlot hVtableDrop hmerge hcapOk
    hpc hrun hsp hsp_align htrace hhigh hfl hsym hx21 hx22 hx24

theorem phase3_from_0x2b4 {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      framelessMemcpySpec)
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr v.length)
      ((bytesVtableDropSpec A tmpPtr v v.length).inImage img))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hcapOk : BytesMergeCapOk cap' rest.length)
    (hcap' : v.length ≤ cap'.toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 692#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = bytesVtable img.base tmpPtr v.length) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr cap' ptr' [] ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) :=
  phase3_from_0x2b4_gen (hStack := allocHookStack) (errStack := decodeErrorHookStack)
    (reqCap := true) (by decide) (by decide) himg (bmMemcpy_inImage_of_frameless hmc)
    hVtableSlot hVtableDrop hmerge hcapOk hcap' hv_len hpc hrun hsp hsp_align htrace hhigh
    hfl hsym hx19 hx20 hx21 hx22 hx23 hx24

theorem phase3_from_0x2b4_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      (session2MemcpySpecBMX.inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr v.length)
      ((bytesVtableDropSpecX A tmpPtr v v.length).inImage img))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hcapOk : BytesMergeCapOk cap' rest.length)
    (hcap' : v.length ≤ cap'.toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 692#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = bytesVtable img.base tmpPtr v.length) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr cap' ptr' [] ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostX A x s0 R) (MergePanicX A x s0 R) :=
  phase3_from_0x2b4_gen (hStack := extHookStack) (errStack := decodeErrorHookStackX)
    (reqCap := true) (by decide) (by decide) himg hmc
    hVtableSlot hVtableDrop hmerge hcapOk hcap' hv_len hpc hrun hsp hsp_align htrace hhigh
    hfl hsym hx19 hx20 hx21 hx22 hx23 hx24

/-! ## Relocatable `[LibsignalPlacement]` helpers and epilogues -/

theorem SepWP.with_vtableSlot_placed [LibsignalPlacement] {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (ptr : BitVec 64) (len : Nat) (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s
      (((bytesPlacedVtable ptr len + 0x20#64) ↦₆₄ᵣ bytesPlacedDropFnAddr ptr len) ∗ P)
      post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (by rw [sepConj_assoc]; exact bytesVtableSlotLoaded_placed_intro hro ptr len hm)

theorem SepWPp.bm_of_sepWP_lscl {prog : Program} {pl : Obj.MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem) (hro : LibsignalRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → LibsignalRoLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · have hcl' : LibsignalCodeLoaded pl sm.mem := hcl.of_keepsFrozen hsteps.keepsFrozen
    have hro' : LibsignalRoLoaded pl sm.mem := libsignalRoLoaded_of_keepsFrozen hro hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout⟩ :=
      hnext hcl' hro' R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

theorem SepWPp.bm_call_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem) (hro : LibsignalRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem → LibsignalRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  have hmid :
      SepWPp prog ret_pc s P
        (fun sm P_m => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ P_m = (withLsCl pl spec).post x s sm ∗ F)
        Qp := by
    refine ProofLib.SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩) hoom
    intro R hm
    dsimp only [withLsCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre R hm⟩
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hpost, hspm, hcsm, rfl⟩ | hpan | hoom_out⟩ := hmid R hm hL
  · dsimp only [withLsCl] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hclm, hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    have hrom : LibsignalRoLoaded pl sm.mem := libsignalRoLoaded_of_keepsFrozen hro hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hclm hrom R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

theorem SepWPp.bm_call_frame_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem) (hro : LibsignalRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem → LibsignalRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.bm_call_lscl (x := x) (F := F) hcall hcl hro hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

theorem epilogue_err_0x0a4_placed_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (blkPl_7).base + 164#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 ≠ 0#64)
    (hhigh : bm_HighCalleeSaved s0 s) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (decodeErrorAtStackLen A (s.readReg64 .x0) 0 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨h25, h26, h27, h28⟩ := hhigh
  dsimp only [savedRegsStack] at hpc ⊢
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp errStack hbnd
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  dsimp only [Reg.x0] at hx0 hmf ⊢
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64, Reg.x0, hx0, htrace,
    ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj]
  convert hmf using 2
  ac_rfl

theorem epilogue_decodeErrorFrom_placed_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A errStack)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w)
    (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (blkPl_7).base + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  dsimp only [savedRegsStack] at hpc hdef ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 261)
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl_call hro_call
  refine SepWPp.bm_call_frame_lscl (x := (s0.sp - 216#64, w))
    (T := ((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
      A.pool ∗ stackAt (s0.sp - 224#64) errStack)
    hdef hcl_call hro_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeErrorFromSpecWithStack, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [KindNoHeap, wp_norm, arm64_norm, hsp, hw, and_self])
    (by rw [stackAt_sliceGen_split s0.sp errStack errStack (Nat.le_add_left errStack 0x50) hbnd]; sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      simp only [bytesMergeRawSpecGen, decodeErrorFromSpecWithStack,
        State.trace_setPC, State.trace_writeReg64, allocFailedIn, htrace] at hm ⊢
      exact allowPanic_frame id hm) ?_
  intro sf_de hpcf hrunf hspf hcsf _ _
  have hhigh' : bm_HighCalleeSaved s0 sf_de := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [decodeErrorFromSpecWithStack, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨hx0, htr⟩ => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    (by rw [stackAt_sliceGen_split s0.sp errStack errStack (Nat.le_add_left errStack 0x50) hbnd]; exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp errStack hbnd
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64, Reg.x0, hx0, htr,
    ↓reduceIte, ne_eq, not_false_eq_true, pure_true, emp_sepConj]
  convert hmf using 2
  ac_rfl

theorem epilogue_vtableDrop_0x2d8_placed_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hdrop_le : hStack + 48 ≤ bmSliceStack errStack)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A hStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hcapOk : bmCapCond reqCap cap' rest.length)
    (hpc : s.pc = (blkPl_7).base + 728#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length + BitVec.ofNat 64 v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr cap' ptr' v ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  dsimp only [savedRegsStack] at hpc hVtableDrop ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := bytesPlacedDropFnAddr tmpPtr v.length)
  apply SepWP.with_vtableSlot_placed tmpPtr v.length hro
  wp_steps
  apply SepWP.drop_left
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl_call hro_call
  refine SepWPp.bm_call_frame_lscl (x := ())
    (T := bytesBoxU8Buf A tmpPtr v ∗ A.pool ∗ stackAt (s0.sp - 224#64) (hStack + 48))
    hVtableDrop hcl_call hro_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesVtableDropSpecBMGen, arm64_norm, hsp]; rfl)
    (by simp only [Nat.le_refl, Nat.sub_self, BitVec.ofNat_eq_ofNat, and_self])
    (by rw [stackAt_sliceGen_split s0.sp errStack (hStack + 48) hdrop_le hbnd]; sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (by intro _ _ hm; dsimp only [bytesVtableDropSpecBMGen] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
  intro sf_dr hpcf hrunf hspf hcsf _ _
  have hhigh' : bm_HighCalleeSaved s0 sf_dr := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [bytesVtableDropSpecBMGen, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun htr => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    (by rw [stackAt_sliceGen_split s0.sp errStack (hStack + 48) hdrop_le hbnd]; exact Entails.refl _) (by sep_focus)
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp errStack hbnd
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
    (by sep_focus)
  apply SepWP.fold (vecU8At_entails_bmPostVec reqCap A x.valPtr cap' ptr' v rest hcapOk)
    (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  simp (config := { decide := true }) only [bytesMergeRawSpecGen, hmerge, State.readReg64_setPC,
    State.readReg64_writeReg64, State.trace_setPC, State.trace_writeReg64, Reg.x0, htr, ↓reduceIte,
    pure_true, emp_sepConj]
  convert hmf using 2
  ac_rfl

theorem phase3_from_0x2b4_placed_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hdrop_le : hStack + 48 ≤ bmSliceStack errStack)
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (blkPl_7.ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr cap' ptr' : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A hStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hcapOk : bmCapCond reqCap cap' rest.length)
    (hcap' : v.length ≤ cap'.toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_7).base + 692#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr cap' ptr' [] ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  rcases v with _ | ⟨b0, v'⟩
  · have hep := fun {s : State} =>
      @epilogue_vtableDrop_0x2d8_placed_gen _ A H hStack errStack reqCap hbnd hdrop_le x s0 s R [] rest tmpPtr cap' ptr' hVtableDrop hmerge hcapOk
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_7).base + bv% (728))
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    exact hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      hhigh hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24])
  · set v := b0 :: v'
    have hep := fun {s : State} =>
      @epilogue_vtableDrop_0x2d8_placed_gen _ A H hStack errStack reqCap hbnd hdrop_le x s0 s R v rest tmpPtr cap' ptr' hVtableDrop hmerge hcapOk
    have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
      apply beq_false_of_ne
      intro h
      have h2 := congrArg BitVec.toNat h
      rw [hlen_toNat] at h2
      exact absurd h2 (by dsimp [v]; omega)
    have hbytesPtr : bytesPtr tmpPtr v.length = tmpPtr := by
      unfold bytesPtr
      have : v.length ≠ 0 := by omega
      simp [this]
    rw [vecU8At_nil_eq A x.valPtr cap' ptr' v hpos hcap', sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, hcap_lt, hptr'⟩ => ?_
    rw [bytesBoxU8Buf_nonempty A tmpPtr v hpos]
    refine SepWPp.weaken_pre (P' := ⌜tmpPtr ≠ 0#64 ∧ v.length < 2 ^ 63⌝ ∗
      ((x.valPtr ↦₆₄ cap') ∗ ((x.valPtr + 8#64) ↦₆₄ ptr') ∗ ((x.valPtr + 16#64) ↦₆₄ 0#64) ∗
        A.live ptr' cap'.toNat 1 ∗ memRegion ptr' v.length ∗
        memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length) ∗
        A.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v) ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨htmp_ne, hv_lt63⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := blkPl_7.ρ "memcpy")
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.bm_call_frame_lscl (x := (ptr', tmpPtr, v))
      (T := memRegion ptr' v.length ∗ (tmpPtr ↦ₛ v) ∗ stackAt (s0.sp - 224#64) (bmSliceStack errStack))
      hmc hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm, hlen_toNat, and_self])
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; dsimp only [bmMemcpySpecGen] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
    intro sf_mc hpcf hrunf hspf hcsf hclf hrof
    have hhigh' : bm_HighCalleeSaved s0 sf_mc := hhigh.of_calleeSaved hcsf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, _, _, _, _, h29f⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h29f
    simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp, htrace]
    refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (728))
    wp_steps
    apply SepWP.fold (fold_bytesBoxU8Buf_nonempty A tmpPtr v hpos htmp_ne hv_lt63)
      (by sep_focus)
    apply SepWP.fold (fold_vecU8At_copied A x.valPtr cap' ptr' v hpos hcap' hcap_lt hptr')
      (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (hep
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by obtain ⟨h25, h26, h27, h28⟩ := hhigh'; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21, h20f, hx20, hbytesPtr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24]))
    exact Entails.of_eq (by ac_rfl)

theorem subroutine_ok_withLsCl_of_withLsCodeLoaded {α : Type} {prog : Program} {addr : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog addr (withLsCodeLoaded pl spec)) :
    subroutine_ok prog addr (withLsCl pl spec) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨sf, hsteps, hout, -⟩ := subroutine_ok.no_fault_before_outcome h x R s0 hpc hrun hpre hsp hL
  have hclf : LibsignalCodeLoaded pl sf.mem := hcl0.of_keepsFrozen hsteps.keepsFrozen
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hclf, hpost⟩
  · exact Or.inr hrest

theorem subroutine_ok_withLsCl_of_plain {α : Type} {prog : Program} {addr : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog addr spec) :
    subroutine_ok prog addr (withLsCl pl spec) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (subroutine_ok_withLsCodeLoaded_of_plain h)

theorem bmShim_placed_of_base [LibsignalPlacement] {prog : Program} {addr : BitVec 64}
    {errStack : Nat} (hshim : subroutine_ok prog addr sessionShimSpec) :
    subroutine_ok prog addr (withLsCl lsmpl (bmShimSpecGen errStack)) := by
  apply subroutine_ok_withLsCl_of_plain
  have h := subroutine_ok_withStack_of_subroutine_ok hshim (bmSliceStack errStack)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack sessionShimSpec (bmSliceStack errStack)).pre x s0 ∗ R := by
    dsimp only [withStack, sessionShimSpec, bmShimSpecGen] at hpre ⊢
    simpa only [pure_true, emp_sepConj, sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionShimSpec, bmShimSpecGen] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem bmMemcpy_placed_of_frameless [LibsignalPlacement] {prog : Program} {addr : BitVec 64}
    {errStack : Nat} (hmc : subroutine_ok prog addr framelessMemcpySpec) :
    subroutine_ok prog addr (withLsCl lsmpl (bmMemcpySpecGen errStack)) := by
  apply subroutine_ok_withLsCl_of_plain
  have h := subroutine_ok_withStack_of_subroutine_ok hmc (bmSliceStack errStack)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack framelessMemcpySpec (bmSliceStack errStack)).pre x s0 ∗ R := by
    dsimp only [withStack, framelessMemcpySpec, bmMemcpySpecGen] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, framelessMemcpySpec, bmMemcpySpecGen] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

end CryptoVerification.LibsignalTripleRatchet.Prost

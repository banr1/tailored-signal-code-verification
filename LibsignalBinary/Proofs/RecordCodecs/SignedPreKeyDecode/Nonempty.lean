/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Epilogue
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Loop

/-!
# Full-Domain and Non-Empty Contracts for `SignedPreKeyRecordStructure::decode`

Proves the 206-instruction `SignedPreKeyRecordStructure::decode::<&[u8]>` binary across all inputs
(`signedDecodeActual_ok_of_deps`, matching `spkActualDecode` where `[] ↦ none` and
`b :: bs ↦ decode (b :: bs)`) and specializes to non-empty slices (`signedDecode_nonempty_ok_of_deps`,
X-form, and relocatable `[LibsignalPlacement]` Block `562`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers

/-- Exact contract satisfied by the compiled `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
across all inputs (`x.bytes = []` returns `Err(UnexpectedEof)` = `none`; all `x.bytes ≠ []` return
`SignedPreKeyRecordStructure.decode x.bytes`). -/
def signedDecodeActualSpec (A : RustAlloc) (img : Obj.Image) : Spec DecodeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
          (s.readReg64 .x2).toNat = x.bytes.length ∧ x.bytes.length < 2 ^ 32⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          signedDecodeResultAt A x.ret (spkActualDecode x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- `signedDecodeSpec` restricted to non-empty slices (`x.bytes ≠ []`), matching all CLI
call sites (`cli/src/stores.rs`). -/
def signedDecodeNonemptySpec (A : RustAlloc) (img : Obj.Image) : Spec DecodeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
          (s.readReg64 .x2).toNat = x.bytes.length ∧ x.bytes.length < 2 ^ 32 ∧ x.bytes ≠ []⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          signedDecodeResultAt A x.ret (SignedPreKeyRecordStructure.decode x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Complete 206-instruction verification: `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
meets `signedDecodeActualSpec A img` on all inputs (`x.bytes.length < 2 ^ 32`). -/
theorem signedDecodeActual_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooks img.base A ext) (d : SignedPortDeps img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName)
      (signedDecodeActualSpec A img) := by
  let _ := hb
  have hB := SpkBundle.of_legacy hH d
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [signedDecodeActualSpec, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, ⟨hx0, hx1, hx2_nat, hlt⟩, hmem⟩
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx2_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp signedDecodeStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have h1 := prologue_0_to_converge_wp hB (x := x) hlt hpc hrun hsp hF hsym hx0 hx1 hx2
  have hfull : Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp signedDecodeStack ∗ A.pool)
      (spkRetPost spkCfgLegacy A s0 x (spkActualDecode x.bytes))
      (tryFromQp s0) := by
    refine Wire.SepWPp.bind h1 ?_
    intro sm Pm hpcm hrunm ⟨hstm, hentm⟩
    exact Wire.SepWPp.mono_pre hentm
      (converge_656_to_ret_wp hB (x := x) (out := spkActualDecode x.bytes) hstm hpcm hrunm)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩, ?_⟩
    dsimp only [signedDecodeActualSpec, Spec.inImage]
    exact Satisfies.mono (sepConj_mono_left hent_f) hmf
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [signedDecodeActualSpec, Spec.inImage]
    exact htr_f R hmf
  · exact (allowPanic_not_exited hoom).elim

/-- Outcome bridge from `signedDecodeSpec.pre` for any non-empty input `x.bytes ≠ []`. -/
theorem signedDecode_outcome_of_nonempty {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooks img.base A ext) (d : SignedPortDeps img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    {x : DecodeGhost} {R : SepProp} {s0 : State}
    (hne : x.bytes ≠ [])
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (signedDecodeSpec A img).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (signedDecodeSpec A img) x R s0 s0 := by
  have hpre_act : s0.mem ⊨ (signedDecodeActualSpec A img).pre x s0 ∗ R := by
    dsimp only [signedDecodeSpec, Spec.inImage] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨himg, ⟨hx0, hx1, hx2, _hpos, hlt⟩, hmem⟩
    dsimp only [signedDecodeActualSpec, Spec.inImage]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨himg, ⟨hx0, hx1, hx2, hlt⟩, hmem⟩
  refine (signedDecodeActual_ok_of_deps hH d hb).mono_outcome x R s0 hpc hrun hpre_act hsp ?_
  intro sf hout
  dsimp only [SubroutineOutcome, signedDecodeActualSpec, signedDecodeSpec, Spec.inImage] at hout ⊢
  rw [spkActualDecode_of_nonempty hne] at hout
  exact hout

/-- Non-empty contract: `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
meets `signedDecodeNonemptySpec A img` (`x.bytes ≠ []`). -/
theorem signedDecode_nonempty_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooks img.base A ext) (d : SignedPortDeps img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName)
      (signedDecodeNonemptySpec A img) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [signedDecodeNonemptySpec, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg, ⟨hx0, hx1, hx2, hlt, hne⟩, hmem⟩
  have hpre_spec : s0.mem ⊨ (signedDecodeSpec A img).pre x s0 ∗ R := by
    dsimp only [signedDecodeSpec, Spec.inImage]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨himg, ⟨hx0, hx1, hx2, List.length_pos_of_ne_nil hne, hlt⟩, hmem⟩
  exact (signedDecode_outcome_of_nonempty hH d hb hne hpc hrun hpre_spec hsp).mono_outcome
    fun _ hout => hout

/-! ## X-form (`AllocContractsX` / `SignedHooksX` / `SignedPortDepsX`) inner decoder proofs -/

/-- X-form exact contract across all inputs (`signedDecodeStackX`). -/
def signedDecodeActualSpecX (A : RustAlloc) (img : Obj.Image) : Spec DecodeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
          (s.readReg64 .x2).toNat = x.bytes.length ∧ x.bytes.length < 2 ^ 32⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStackX ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          signedDecodeResultAt A x.ret (spkActualDecode x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStackX ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- X-form `signedDecodeSpecX` restricted to non-empty slices (`x.bytes ≠ []`). -/
def signedDecodeNonemptySpecX (A : RustAlloc) (img : Obj.Image) : Spec DecodeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
          (s.readReg64 .x2).toNat = x.bytes.length ∧ x.bytes.length < 2 ^ 32 ∧ x.bytes ≠ []⌝ ∗
          (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStackX ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          signedDecodeResultAt A x.ret (SignedPreKeyRecordStructure.decode x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStackX ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- X-form complete 206-instruction verification on all inputs (`signedDecodeStackX`). -/
theorem signedDecodeActual_ok_of_deps_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooksX img A ext) (d : SignedPortDepsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName)
      (signedDecodeActualSpecX A img) := by
  let _ := hb
  have hB := SpkBundle.of_x hH d
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [signedDecodeActualSpecX, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, ⟨hx0, hx1, hx2_nat, hlt⟩, hmem⟩
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx2_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp signedDecodeStackX ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have h1 := prologue_0_to_converge_wp hB (x := x) hlt hpc hrun hsp hF hsym hx0 hx1 hx2
  have hfull : Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp signedDecodeStackX ∗ A.pool)
      (spkRetPost spkCfgX A s0 x (spkActualDecode x.bytes))
      (tryFromQp s0) := by
    refine Wire.SepWPp.bind h1 ?_
    intro sm Pm hpcm hrunm ⟨hstm, hentm⟩
    exact Wire.SepWPp.mono_pre hentm
      (converge_656_to_ret_wp hB (x := x) (out := spkActualDecode x.bytes) hstm hpcm hrunm)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩, ?_⟩
    dsimp only [signedDecodeActualSpecX, Spec.inImage]
    exact Satisfies.mono (sepConj_mono_left hent_f) hmf
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [signedDecodeActualSpecX, Spec.inImage]
    exact htr_f R hmf
  · exact (allowPanic_not_exited hoom).elim

/-- X-form outcome bridge from `signedDecodeSpecX.pre` for any non-empty input `x.bytes ≠ []`. -/
theorem signedDecode_outcome_of_nonempty_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooksX img A ext) (d : SignedPortDepsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    {x : DecodeGhost} {R : SepProp} {s0 : State}
    (hne : x.bytes ≠ [])
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (signedDecodeSpecX A img).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (signedDecodeSpecX A img) x R s0 s0 := by
  have hpre_act : s0.mem ⊨ (signedDecodeActualSpecX A img).pre x s0 ∗ R := by
    dsimp only [signedDecodeSpecX, Spec.inImage] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨himg, ⟨hx0, hx1, hx2, _hpos, hlt⟩, hmem⟩
    dsimp only [signedDecodeActualSpecX, Spec.inImage]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨himg, ⟨hx0, hx1, hx2, hlt⟩, hmem⟩
  refine (signedDecodeActual_ok_of_deps_x hH d hb).mono_outcome x R s0 hpc hrun hpre_act hsp ?_
  intro sf hout
  dsimp only [SubroutineOutcome, signedDecodeActualSpecX, signedDecodeSpecX, Spec.inImage] at hout ⊢
  rw [spkActualDecode_of_nonempty hne] at hout
  exact hout

/-- X-form non-empty contract: `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
meets `signedDecodeNonemptySpecX A img` (`x.bytes ≠ []`). -/
theorem signedDecode_nonempty_ok_of_deps_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hH : SignedHooksX img A ext) (d : SignedPortDepsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName)
      (signedDecodeNonemptySpecX A img) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [signedDecodeNonemptySpecX, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg, ⟨hx0, hx1, hx2, hlt, hne⟩, hmem⟩
  have hpre_spec : s0.mem ⊨ (signedDecodeSpecX A img).pre x s0 ∗ R := by
    dsimp only [signedDecodeSpecX, Spec.inImage]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨himg, ⟨hx0, hx1, hx2, List.length_pos_of_ne_nil hne, hlt⟩, hmem⟩
  exact (signedDecode_outcome_of_nonempty_x hH d hb hne hpc hrun hpre_spec hsp).mono_outcome
    fun _ hout => hout

/-! ## Relocatable `[LibsignalPlacement]` Verification (Block `562`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

/-- Image-free raw contract satisfied by `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
across all inputs (`x.bytes = []` returns `none`; `x.bytes ≠ []` returns `decode x.bytes`). -/
def signedDecodeActualRawSpec (A : RustAlloc) : Spec DecodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
      (s.readReg64 .x2).toNat = x.bytes.length ∧ x.bytes.length < 2 ^ 32⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      signedDecodeResultAt A x.ret (spkActualDecode x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable `[LibsignalPlacement]` contract of `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
(block `562`) across all inputs (`[]` and `b :: bs`). -/
abbrev signedDecodeActualPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec DecodeGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (signedDecodeActualRawSpec A)

/-- Image-free raw `signedDecodeSpec` restricted to `x.bytes ≠ []`. -/
def signedDecodeNonemptyRawSpec (A : RustAlloc) : Spec DecodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
      (s.readReg64 .x2).toNat = x.bytes.length ∧ x.bytes.length < 2 ^ 32 ∧ x.bytes ≠ []⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      signedDecodeResultAt A x.ret (SignedPreKeyRecordStructure.decode x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable `[LibsignalPlacement]` contract of `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
(block `562`) restricted to `x.bytes ≠ []`. -/
abbrev signedDecodeNonemptyPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec DecodeGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (signedDecodeNonemptyRawSpec A)

/-- Complete 206-instruction relocatable verification: block `562` meets
`signedDecodeActualPlacedSpec A` across all inputs (`x.bytes.length < 2 ^ 32`). -/
theorem signedDecodeActual_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H) :
    subroutine_ok (lsProg_562 H) (blkPl_562).base (signedDecodeActualPlacedSpec A) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  obtain ⟨hcrl, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [signedDecodeActualRawSpec] at hpre_raw
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2_nat, hlt⟩, hmem⟩
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx2_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp signedDecodeStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have h1 := prologue_0_to_converge_placed_wp hH d (x := x) hlt hpc hrun hsp hcrl hx0 hx1 hx2
  have hfull : Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp signedDecodeStack ∗ A.pool)
      (spkRetPost spkCfgLegacy A s0 x (spkActualDecode x.bytes))
      (tryFromQp s0) := by
    refine Wire.SepWPp.bind h1 ?_
    intro sm Pm hpcm hrunm ⟨hstm, hentm⟩
    exact Wire.SepWPp.mono_pre hentm
      (converge_656_to_ret_placed_wp hH (x := x) (out := spkActualDecode x.bytes) hstm hpcm hrunm)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩, ?_⟩
    dsimp only [signedDecodeActualPlacedSpec, LibsignalTripleRatchet.withLsCodeRoLoaded, signedDecodeActualRawSpec]
    exact Satisfies.mono (sepConj_mono_left hent_f) hmf
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [signedDecodeActualPlacedSpec, LibsignalTripleRatchet.withLsCodeRoLoaded, signedDecodeActualRawSpec]
    exact htr_f R hmf
  · exact (allowPanic_not_exited hoom).elim

/-- Relocatable outcome bridge from `signedDecodePlacedSpec.pre` for any non-empty input `x.bytes ≠ []`. -/
theorem signedDecode_placed_outcome_of_nonempty [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H)
    {x : DecodeGhost} {R : SepProp} {s0 : State}
    (hne : x.bytes ≠ [])
    (hpc : s0.pc = (blkPl_562).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (signedDecodePlacedSpec A).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    reaches_outcome (lsProg_562 H) (signedDecodePlacedSpec A) x R s0 s0 := by
  have hpre_act : s0.mem ⊨ (signedDecodeActualPlacedSpec A).pre x s0 ∗ R := by
    obtain ⟨hcrl, hraw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
    dsimp only [signedDecodeRawSpec] at hraw
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hraw
    rcases hraw with ⟨⟨hx0, hx1, hx2, _hpos, hlt⟩, hmem⟩
    have hact_raw : s0.mem ⊨ (signedDecodeActualRawSpec A).pre x s0 ∗ R := by
      dsimp only [signedDecodeActualRawSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hlt⟩, hmem⟩
    dsimp only [signedDecodeActualPlacedSpec, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [show ((signedDecodeActualRawSpec A).pre x s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ ((signedDecodeActualRawSpec A).pre x s0 ∗ R) by ac_rfl,
      satisfies_pure_sepConj]
    exact ⟨hcrl, hact_raw⟩
  refine (signedDecodeActual_placed_ok_of_deps hH d).mono_outcome x R s0 hpc hrun hpre_act hsp ?_
  intro sf hout
  dsimp only [SubroutineOutcome, signedDecodeActualPlacedSpec, signedDecodePlacedSpec,
    LibsignalTripleRatchet.withLsCodeRoLoaded, signedDecodeActualRawSpec, signedDecodeRawSpec] at hout ⊢
  rw [spkActualDecode_of_nonempty hne] at hout
  exact hout

/-- Relocatable non-empty contract: block `562` meets `signedDecodeNonemptyPlacedSpec A`. -/
theorem signedDecode_nonempty_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H) :
    subroutine_ok (lsProg_562 H) (blkPl_562).base (signedDecodeNonemptyPlacedSpec A) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hraw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [signedDecodeNonemptyRawSpec] at hraw
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hraw
  rcases hraw with ⟨⟨hx0, hx1, hx2, hlt, hne⟩, hmem⟩
  have hpre_spec : s0.mem ⊨ (signedDecodePlacedSpec A).pre x s0 ∗ R := by
    have hspec_raw : s0.mem ⊨ (signedDecodeRawSpec A).pre x s0 ∗ R := by
      dsimp only [signedDecodeRawSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, List.length_pos_of_ne_nil hne, hlt⟩, hmem⟩
    dsimp only [signedDecodePlacedSpec, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [show ((signedDecodeRawSpec A).pre x s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ ((signedDecodeRawSpec A).pre x s0 ∗ R) by ac_rfl,
      satisfies_pure_sepConj]
    exact ⟨hcrl, hspec_raw⟩
  exact (signedDecode_placed_outcome_of_nonempty hH d hne hpc hrun hpre_spec hsp).mono_outcome
    fun _ hout => hout

end Placed

end CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode

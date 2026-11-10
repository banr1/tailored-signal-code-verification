/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RecordCodecsBinary
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSlice
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import ProofLib.SepLogic.WPFrozen
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSym -- shake: keep

/-!
# Callee Contracts for Record Decoders

Defines the callee contract bundles (`DecodeDeps`, `CodecHooksPlaced`, `PortDepsPlaced`),
relocatable `[LibsignalPlacement]` specifications, and `withLsCodeRoLoaded` cross-block call
combinators shared by `PreKeyRecord::deserialize` (Block `65`),
`<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (Block `84`), and `IdentityKey::decode`
(Block `18`).
-/

@[expose] public section

namespace CryptoVerification.RecordCodecsBinary

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- The proved in-image callees of the three record decoders, on
`tripleRatchetProgAtExt img.base ext`. -/
structure DecodeDeps (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop where
  varintSlice : Prost.DecodeVarintSliceOkExtX img A ext
  int32Merge : Prost.Int32MergeOkExtX img A ext
  skipField : Prost.SkipFieldOkExtX img A ext
  dropDecodeError : Prost.DropDecodeErrorOkExtX img A ext
  bytesMerge : Prost.BytesMergeOkExtX img A ext
  pkTryFrom :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkTryFromName) (pkTryFromCodeSpec img)

/-! ## The entry points are symbols of the image

Each fails to elaborate if the symbol is missing from (or not unique in) the current image, so a
re-export that drops or renames one is reported here. -/

example : libsignalSessionCode.fnOff preKeyDeserializeName =
    num% (ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize") :=
  ls_lemma% fnOff "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"

example : libsignalSessionCode.fnOff identityKeyPairTryFromName =
    num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from") :=
  ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"

example : libsignalSessionCode.fnOff identityKeyDecodeName =
    num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode") :=
  ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::decode"

/-! ## Relocatable `[LibsignalPlacement]` Contracts & Callee Dependencies -/

section Placed

open CryptoVerification CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecs.Placed

/-- External hook contracts (`__rust_alloc`, `__rust_realloc`, `__rust_dealloc`,
`__rust_no_alloc_shim_is_unstable_v2`, `memcpy`, and OOM panic stubs) sufficient to discharge all
`RecordCodecs` callees on a relocatable `[LibsignalPlacement]`. -/
structure CodecHooksPlaced (A : RustAlloc) (H : LibsignalHooks) : Prop where
  shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec
  alloc : HookSat H lsRustAllocSym (rustAllocSpec A)
  realloc : HookSat H lsRustReallocSym (rustReallocSpec A)
  dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)
  memcpy : HookSat H lsMemcpySym framelessMemcpySpec
  panic_alloc : H Prost.lsHandleAllocErrorSym = some Rust.panicked
  panic_raw : H lsHandleErrorSym = some Rust.panicked

/-- Relocatable `[LibsignalPlacement]` callee contracts for `PreKeyRecord::deserialize` (Block `65`),
`IdentityKey::decode` (Block `18`), and `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (Block `84`). -/
structure PortDepsPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  varintSlice :
    subroutine_ok ((blkPC_76).rebase (blkPl_76).base H) (blkPl_76).base
      (withLsCodeLoaded lsmpl (Prost.decodeVarintSliceSpecX A))
  int32Merge :
    subroutine_ok ((blkPC_8).rebase (blkPl_8).base H) (blkPl_8).base
      (withLsCodeLoaded lsmpl (Prost.int32MergeSpecX A))
  skipField :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H) (blkPl_1).base
      (withLsCodeLoaded lsmpl (Prost.skipFieldSpecX A))
  dropDecodeError :
    subroutine_ok ((blkPC_4).rebase (blkPl_4).base H) (blkPl_4).base
      (Prost.dropDecodeErrorSpecX A)
  bytesMerge :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (Prost.bytesMergeRawSpecX A))
  pkTryFrom :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H) (blkPl_211).base
      pkTryFromPlacedSpec
  varintSlow :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H) (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)))
  decodeErrorFrom :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (decodeErrorFromSpecWithStack A (2 * extHookStack))
  decodeErrorPush :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushExternSpecWithStack A (2 * extHookStack)))
  dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)

/-- Image-free inner specification of `PreKeyRecord::deserialize`. -/
def preKeyDeserializeRawSpec (A : RustAlloc) : Spec DecodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
      x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗ stackAt s.sp smallRootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ preKeyResultAt A x.ret (PreKeyRecord.deserialize x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp smallRootStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable `[LibsignalPlacement]` specification of `PreKeyRecord::deserialize` (Block `65`). -/
abbrev preKeyDeserializePlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec DecodeGhost :=
  withLsCodeRoLoaded lsmpl (preKeyDeserializeRawSpec A)

/-- Image-free inner specification of `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` using `lsLogOff`. -/
def identityKeyPairTryFromRawSpec [LibsignalPlacement] (A : RustAlloc) : Spec DecodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
      x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ lsLogOff ∗
      stackAt s.sp smallRootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗ stackAt s0.sp smallRootStack ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable `[LibsignalPlacement]` specification of `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (Block `84`). -/
abbrev identityKeyPairTryFromPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec DecodeGhost :=
  withLsCodeRoLoaded lsmpl (identityKeyPairTryFromRawSpec A)

/-- Image-free inner specification of `IdentityKey::decode` using `lsLogOff`. -/
def identityKeyDecodeRawSpec [LibsignalPlacement] (A : RustAlloc) : Spec DecodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
      s.readReg64 .x8 = x.ret⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 48 ∗ lsLogOff ∗ stackAt s.sp 0x60
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ identityKeyResultAt A x.ret (decodeIdentityKey x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗ stackAt s0.sp 0x60

/-- Relocatable `[LibsignalPlacement]` specification of `IdentityKey::decode` (Block `18`). -/
abbrev identityKeyDecodePlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec DecodeGhost :=
  withLsCodeLoaded lsmpl (identityKeyDecodeRawSpec A)

/-! ### Cross-Block `withLsCodeRoLoaded` Transfer & `Wire.SepWPp` Combinators -/

/-- Transfer `subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec)` across blocks `j` → `i`. -/
theorem ls_subroutine_ok_lscro_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec))
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcrl0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcrl0.1 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact Arm64.reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

theorem ls_subroutine_ok_lscro_of_cl [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  ls_subroutine_ok_lscro_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee) hi hj hj_unmut

theorem ls_subroutine_ok_lscro_of_plain [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  ls_subroutine_ok_lscro_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hcallee) hi hj hj_unmut

theorem ls_dealloc_lscro_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide) (hi_unmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (rustDeallocExternWithStack_of_rustDealloc
      (ls_hook_ok_of_mem hdealloc (by decide) hi hi_unmut) (by decide) (by decide))

/-- Relocatable analogue of `Wire.SepWPp.of_sepWP_frozen`, threading `LibsignalCodeRoLoaded pl ·.mem`
and `Wire.VRegsAt`. -/
theorem sepWPp_of_sepWP_lscro {prog : Program} {pl : Obj.MultiPlacement} {ret mid : BitVec 64}
    {s : Arm64.State} {P : SepProp} {Q Qp : Arm64.State → SepProp → Prop}
    {oom : Arm64.State → SepProp}
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (h : ProofLib.SepWP prog mid s P (fun sm Pm =>
      Wire.VRegsAt s sm ∧
      (LibsignalCodeRoLoaded pl sm.mem →
        Wire.SepWPp prog ret sm Pm Q Qp oom)) oom) :
    Wire.SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hv, hnext⟩ | hoom⟩
  · have hcrl_m := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpc, hrun, Pf, hmf, hq, hvf⟩ | hpan⟩ :=
      hnext hcrl_m R hmm (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc, hrun, Pf, hmf, hq, hvf.trans hv.eq⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpan⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-- Relocatable analogue of `Wire.SepWPp.call_tryFrom`, calling a `withLsCodeRoLoaded pl spec`
contract and threading `LibsignalCodeRoLoaded pl ·.mem`, `spAligned`, and `CalleeSavedPreserved`. -/
theorem sepWPp_call_lscro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {ret entry ret_pc : BitVec 64} {s0 s : Arm64.State} {P T F : SepProp} {φ : Prop}
    {Q : Arm64.State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      Wire.SepWPp prog ret sf (spec.post x s sf ∗ F) Q (Wire.tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by
      intros; exact Entails.refl _)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    Wire.SepWPp prog ret s P Q (Wire.tryFromQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [Arm64.State.spAligned, hspm, ← Arm64.State.spAligned]; exact hsp
    have hcrl_m := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hcrl_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    have hpost' := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (hpan sm))) hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost', Wire.tryFromQp_of_call htr⟩)⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hexit sm code] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hoom
    rw [hoom_eq sm] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-- Relocatable analogue of `Wire.SepWPp.of_sepWP_end`, threading `LibsignalCodeRoLoaded pl ·.mem`. -/
theorem sepWPp_of_sepWP_end_lscro {prog : Program} {pl : Obj.MultiPlacement} {ret : BitVec 64}
    {s0 s : Arm64.State} {P : SepProp} {Q : Arm64.State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (h : ProofLib.SepWP prog ret s P (fun sf Pf =>
      Wire.VRegsAt s sf ∧
      (LibsignalCodeRoLoaded pl sf.mem → Q sf Pf))) :
    Wire.SepWPp prog ret s P Q (Wire.tryFromQp s0) := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      hq (hcrl.of_keepsFrozen hsteps.keepsFrozen), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end Placed

end CryptoVerification.RecordCodecsBinary

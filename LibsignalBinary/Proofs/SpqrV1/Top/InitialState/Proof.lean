/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Steps
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Final
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ExtProof
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `spqr::initial_state` (`0x542d0`)

Proves `InitialStateOkX` and `InitialStateOkXExt` for `spqr::initial_state` (`0x542d0`) by
version dispatch (`p.version = .v0` vs `.v1`), composing `auth_key.to_vec()`, `ChainParams.intoPb`
default elision, `spqr::init_inner`, `<PqRatchetState as prost::Message>::encode_to_vec`, and
`drop_glue::<PqRatchetState>`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.InitialState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

/-! ## 1. Callee contract bundle -/

/-- Callee contracts of `spqr::initial_state` (`0x542d0`). `drop_glue::<PqRatchetState>`
(`0x4c460`) needs no field: it is proved unconditionally from `hA.dealloc`
(`drop_proto_pq_ratchet_state_ok_ext`, `Drop/ProtoTop2.lean`). The `.rodata` jump tables come from
`himg` (`rodata_statesIntoPbJumpTable`, `rodata_optProtoInnerStateJumpTable`,
`Top/Recv/Contracts.lean`). -/
structure InitialStateContracts (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop where
  /-- Base page alignment (`img.base &&& 0xfff#64 = 0#64`). -/
  base_aligned : img.base &&& 0xfff#64 = 0#64
  /-- The libsignal session object image is loaded in `img`. -/
  himg : Obj.Loads libsignalSessionImage img
  /-- Rust allocator / `memcpy` / no-alloc-shim hook contracts. -/
  hA : AllocContracts img.base A ext
  /-- `spqr::init_inner` (`0x532dc`). -/
  initInner_ok : InitInnerOkX img A F ext
  /-- `<PqRatchetState as prost::Message>::encode_to_vec` (`0x6d010`). -/
  encodeToVec_ok : PqRatchetStateEncodeToVecOkX img A ext

/-- Assemble `InitialStateContracts` from `Obj.Loads`, `AllocContracts`, `InitInnerOkX`, and `PqRatchetStateEncodeToVecOkX`. -/
theorem initialStateContracts_of_okX
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hAuthNew : AuthNewOkX img F A ext) :
    InitialStateContracts img A F ext where
  base_aligned := ProofLib.ObjectLoad.base_aligned_of_loads himg
  himg := himg
  hA := hA
  initInner_ok := init_inner_ok_x himg hA hAuthNew
  encodeToVec_ok := pqRatchetStateEncodeToVec_okX hA himg

/-! ## 2. Dispatch on `params.version` -/

/-- `initialStateSpecX` restricted to `p.version = v`. -/
def initialStateVSpecX (A : RustAlloc) (F : ShaCompress) (img : Obj.Image) (v : Version) :
    Spec InitialStateGhost :=
  { initialStateSpecX A F img with
    pre := fun x s => ⌜x.p.version = v⌝ ∗ (initialStateSpecX A F img).pre x s }

theorem initialState_ok_of_versions
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h0 : subroutine_ok (LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext)
      ((LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext).fnAddr initialStateName)
      (initialStateVSpecX A F img .v0))
    (h1 : subroutine_ok (LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext)
      ((LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext).fnAddr initialStateName)
      (initialStateVSpecX A F img .v1)) :
    InitialStateOkX img A F ext := by
  unfold InitialStateOkX
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have key : ∀ v, x.p.version = v →
      s0.mem ⊨ (initialStateVSpecX A F img v).pre x s0 ∗ R := by
    intro v hv
    dsimp only [initialStateVSpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hv, hpre⟩
  cases hv : x.p.version with
  | v0 => exact (h0.to_outcome x R s0 hpc hrun (key .v0 hv) hsp).mono_outcome fun _ hout => hout
  | v1 => exact (h1.to_outcome x R s0 hpc hrun (key .v1 hv) hsp).mono_outcome fun _ hout => hout

/-! ## 3. `ChainParams` Default-Elision Helpers -/

/-- `csel` default elision at `0x54408..0x54410` matches `cp.intoPb.maxJump`. -/
theorem chainParams_csel_maxJump (cp : ChainParams) :
    (if cp.maxJump = 25000#32 then 0#32 else cp.maxJump) = cp.intoPb.maxJump := by
  unfold ChainParams.intoPb DEFAULT_CHAIN_PARAMS
  by_cases h : cp.maxJump = 25000#32 <;> simp [h]

/-- `csel` default elision at `0x54418..0x54420` matches `cp.intoPb.maxOooKeys`. -/
theorem chainParams_csel_maxOoo (cp : ChainParams) :
    (if cp.maxOooKeys = 2000#32 then 0#32 else cp.maxOooKeys) = cp.intoPb.maxOooKeys := by
  unfold ChainParams.intoPb DEFAULT_CHAIN_PARAMS
  by_cases h : cp.maxOooKeys = 2000#32 <;> simp [h]

/-! ## 4. Version Branches and Layout Bridge -/

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  Expand.sp_sub_496_eq_esp Expand.sp_add_neg496_eq_esp Expand.esp_add_496_sub_496
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_add_688_sub_688 Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

private def initialStateSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

private theorem initialStateSavedCells_entails_memRegion (s0 : State) :
    initialStateSavedCells s0 ⊢ memRegion (s0.sp - 96#64) 96 := by
  unfold initialStateSavedCells
  rw [ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)]
  cells_unfold
  refine Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x27)
          (Entails.sepExists_right (s0.readReg64 .x26)
            (Entails.sepExists_right (s0.readReg64 .x25)
              (Entails.sepExists_right (s0.readReg64 .x24)
                (Entails.sepExists_right (s0.readReg64 .x23)
                  (Entails.sepExists_right (s0.readReg64 .x22)
                    (Entails.sepExists_right (s0.readReg64 .x21)
                      (Entails.sepExists_right (s0.readReg64 .x20)
                        (Entails.sepExists_right (s0.readReg64 .x19) ?_)))))))))))
  exact Entails.of_eq (by simp only [arm64_norm])

private theorem stackAt_initialState_split (sp : BitVec 64) :
    stackAt sp initialStateStack =
      stackAt (sp - 496#64) initialStateCalleeStack ∗
      memRegion (sp - 496#64) 400 ∗
      cells (sp - 96#64) 12 := by
  unfold stackAt initialStateStack initialStateFrame
  rw [ProofLib.memRegion_split'
        (b := sp - BitVec.ofNat 64 (0x1f0 + initialStateCalleeStack))
        (n := initialStateCalleeStack) (k := 496)
        (b' := sp - 496#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 496#64) (n := 400) (k := 96)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : (sp - 496#64) - BitVec.ofNat 64 initialStateCalleeStack =
      sp - BitVec.ofNat 64 (0x1f0 + initialStateCalleeStack) := by
    dsimp only [initialStateCalleeStack, initInnerStack, initInnerFrame, authNewStackX,
      encodeToVecStackX, dropStack96, allocHookStack]
    bv_omega
  rw [hsub]

private theorem stack_restore_initialState (s0 : State) :
    stackAt (s0.sp - 496#64) initialStateCalleeStack ∗
    memRegion (s0.sp - 496#64) 400 ∗
    initialStateSavedCells s0 ⊢
    stackAt s0.sp initialStateStack := by
  rw [stackAt_initialState_split s0.sp, ← ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (initialStateSavedCells_entails_memRegion s0))

private theorem initialStateResultAt_v0_of_cells (A : RustAlloc) (F : ShaCompress)
    (ret : BitVec 64) (p : CryptoVerification.LibsignalSpqrV1.Params) (hv : p.version = .v0) :
    (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗
    ((ret + 16#64) ↦₆₄ 1#64) ∗ ((ret + 24#64) ↦₆₄ 0#64) ⊢
    initialStateResultAt A ret (initialStateValue F p) := by
  unfold initialStateResultAt initialStateValue
  rw [hv]
  dsimp [emptyState]
  have h16 : (ret + 8#64) + 8#64 = ret + 16#64 := by bv_omega
  have h24 : (ret + 8#64) + 16#64 = ret + 24#64 := by bv_omega
  have hvec := vecU8_nil_of_cells A (ret + 8#64)
  rw [h16, h24] at hvec
  exact sepConj_mono_right hvec

private theorem adrp_logOff_addr {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    (((b + 323288#64 + 32#64) &&& 0xfffffffffffff000#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x4e000)) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  bv_bits

private theorem initialState_v0_step
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (s0 : State) (x : InitialStateGhost) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (LibsignalTripleRatchet.tripleRatchetProgAtExt b ext).fnAddr initialStateName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.pA)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hv : x.p.version = .v0) :
    SepWP (LibsignalTripleRatchet.tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0
      (paramsAt x.pA x.akPtr x.p ∗
       memRegion x.ret 32 ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       stackAt s0.sp initialStateStack ∗
       Rest)
      (fun sf Pf =>
        (Pf ⊢
          paramsAt x.pA x.akPtr x.p ∗
          initialStateResultAt A x.ret (initialStateValue F x.p) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          stackAt s0.sp initialStateStack ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hadrp :
      ((((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
          "spqr::initial_state" + 32#64) &&& 0xfffffffffffff000#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x4e000)) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
        b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
    change (((b + BitVec.ofNat 64 (libsignalSessionCode.fnOff "spqr::initial_state") + 32#64) &&&
        0xfffffffffffff000#64) + bv% (ls_xref% 0x4eef8 - 0x4e000)) + bv% ((ls_xref% 0x4eef8 0x4ef04) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)
    rw [libsignalSessionCode_fnOff_0x4eed8]
    exact adrp_logOff_addr hb
  have hrestore :
      paramsAt x.pA x.akPtr x.p ∗
      ((x.ret ↦₆₄ 0#64) ∗ ((x.ret + 8#64) ↦₆₄ 0#64) ∗
       ((x.ret + 16#64) ↦₆₄ 1#64) ∗ ((x.ret + 24#64) ↦₆₄ 0#64)) ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      (stackAt (s0.sp - 496#64) initialStateCalleeStack ∗
       memRegion (s0.sp - 496#64) 400 ∗
       initialStateSavedCells s0) ∗
      Rest ⊢
      paramsAt x.pA x.akPtr x.p ∗
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      stackAt s0.sp initialStateStack ∗
      Rest :=
    sepConj_mono_right (sepConj_mono (initialStateResultAt_v0_of_cells A F x.ret x.p hv)
      (sepConj_mono_right (sepConj_mono_left (stack_restore_initialState s0))))
  refine SepWP.strengthen_entails_const hrestore ?_
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hv_i32 : x.p.version.toI32 = 0#32 := by rw [hv]; rfl
  initial_state_fetches_range b (Rust.withPanics ext) 0 56
  initial_state_fetches_range b (Rust.withPanics ext) 172 12
  initial_state_fetches_range b (Rust.withPanics ext) 208 16
  initial_state_fetches_range b (Rust.withPanics ext) 396 32
  dsimp only [LibsignalTripleRatchet.tripleRatchetProgAtExt, initialStateName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::initial_state" = entry
  examples_hide_fetches
  rw [ProofLib.memRegion_cells x.ret 4 (by decide),
      stackAt_initialState_split s0.sp]
  unfold paramsAt
  rw [hv_i32]
  dsimp only [initialStateSavedCells]
  simp only [sepConj_assoc]
  cells_unfold
  dsimp only [ProofLib.cells]
  simp only [sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- `version ≠ .v1` path (`0x542d0..0x54384`, `0x543a0..0x543ac`, epilogue): writes empty `Ok(Vec::new())` to sret without calls. -/
theorem initialState_v0_ok
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContracts img A F ext) :
    subroutine_ok (LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext)
      ((LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext).fnAddr initialStateName)
      (initialStateVSpecX A F img .v0) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp0_align hcode => ?_
  dsimp only [initialStateVSpecX, initialStateSpecX, Spec.inImage, initialStateSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hinv0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, _hak_ne, _hlen⟩, hm⟩
  have hpre_eq :
      (paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp initialStateStack) ∗ R =
      (paramsAt x.pA x.akPtr x.p ∗ memRegion x.ret 32 ∗ ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       stackAt s0.sp initialStateStack ∗ ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool)) ∗ R := by
    ac_rfl
  rw [hpre_eq] at hm
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hent, hspf, hcsf, htrf⟩ | ⟨_, hoom⟩⟩ :=
    (initialState_v0_step (A := A) (F := F) hC.base_aligned s0 x
      ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool) hsp0_align hpc hrun hx0 hx8 hv).elim hm hcode
  · refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, ?_⟩))
    dsimp only [initialStateVSpecX, initialStateSpecX, Spec.inImage, initialStateSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrf, ?_⟩
    have hmf' := Satisfies.mono (sepConj_mono_left hent) hmf
    have hpost_eq :
        (paramsAt x.pA x.akPtr x.p ∗ initialStateResultAt A x.ret (initialStateValue F x.p) ∗
         ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ stackAt s0.sp initialStateStack ∗
         ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool)) ∗ R =
        (paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
         initialStateResultAt A x.ret (initialStateValue F x.p) ∗
         ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp initialStateStack) ∗ R := by
      ac_rfl
    rwa [hpost_eq] at hmf'
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem wp6_h61_len_rawV1State_initV1State_le (F : ShaCompress)
    (d : Direction) (authKey : Bytes) :
    CryptoVerification.SpqrV1.Top.StateSize.rawV1State (initV1State F d authKey).into_pb ≤ 424 := by
  have hauth := CryptoVerification.SpqrV1.Top.StateSize.Authenticator.new_rawAuth_le F authKey 1#64
  cases d with
  | a2b =>
    dsimp only [initV1State, States.into_pb, Chunked.SendEk.KeysUnsampled.into_pb,
      Unchunked.SendEk.KeysUnsampled.into_pb, spqrAuthApi,
      CryptoVerification.SpqrV1.Top.StateSize.rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChKeysUnsampled,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcKeysUnsampled]
    omega
  | b2a =>
    have hdec : CryptoVerification.SpqrV1.Top.StateSize.rawPolyDec
        (spqrPolyApi.decoder_into_pb initHdrDecoder) = 352 := rfl
    dsimp only [initV1State, States.into_pb, Chunked.SendCt.NoHeaderReceived.into_pb,
      Unchunked.SendCt.NoHeaderReceived.into_pb, spqrAuthApi,
      CryptoVerification.SpqrV1.Top.StateSize.rawV1State,
      CryptoVerification.SpqrV1.Top.StateSize.optRaw,
      CryptoVerification.SpqrV1.Top.StateSize.rawInnerState,
      CryptoVerification.SpqrV1.Top.StateSize.rawChNoHeaderReceived,
      CryptoVerification.SpqrV1.Top.StateSize.rawUcNoHeaderReceived]
    omega

/-- Encoded byte length of `initialStatePB F p` is `< 2 ^ 63` when `p.authKey.length < 2 ^ 32`. -/
theorem initialStatePB_encodeRaw_length_lt (F : ShaCompress)
    (p : CryptoVerification.LibsignalSpqrV1.Params) (hlen : p.authKey.length < 2 ^ 32) :
    (PqRatchetState.encodeRaw (initialStatePB F p)).length < 2 ^ 63 := by
  have h1 : (PqRatchetState.encodeRaw (initialStatePB F p)).length ≤
      CryptoVerification.SpqrV1.Top.StateSize.rawPqState (initialStatePB F p) + 752 :=
    CryptoVerification.SpqrV1.Top.StateSize.encodeState_length_le_rawPqState (initialStatePB F p)
  have hraw : CryptoVerification.SpqrV1.Top.StateSize.rawPqState (initialStatePB F p) =
      p.authKey.length + 0 +
        CryptoVerification.SpqrV1.Top.StateSize.rawV1State
          (initV1State F p.direction p.authKey).into_pb := rfl
  have h2 := wp6_h61_len_rawV1State_initV1State_le F p.direction p.authKey
  omega

/-- Assembles the 352-byte `pqRatchetStatePBAt A (sp + 0x28) (initialStatePB F p)` from
`spqr::init_inner`'s output at `sp + 0xa8` and the `VersionNegotiationPB` / `chain = None` stores. -/
theorem initialState_pbAt_of_cells (A : RustAlloc) (F : ShaCompress)
    (p : CryptoVerification.LibsignalSpqrV1.Params) (hv : p.version = .v1)
    (a cap ptr : BitVec 64) :
    (vecU8At A a cap ptr p.authKey ∗
      ((a + 0x18#64) ↦₃₂ 1#32) ∗
      ((a + 0x1c#64) ↦₃₂ p.chainParams.intoPb.maxJump) ∗
      ((a + 0x20#64) ↦₃₂ p.chainParams.intoPb.maxOooKeys) ∗
      ((a + 0x24#64) ↦₃₂ p.direction.toI32) ∗
      ((a + 0x28#64) ↦₃₂ p.minVersion.toI32) ∗
      memRegion (a + 0x2c#64) 4 ∗
      ((a + 0x30#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x38#64) 72 ∗
      initInnerResultAt A (F := F) (a + 0x80#64) .v1 p.direction p.authKey) ⊢
    pqRatchetStatePBAt A a (initialStatePB F p) := by
  have hvec : vecU8At A a cap ptr p.authKey ⊢ vecU8 A a p.authKey :=
    Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))
  refine Entails.trans (sepConj_mono_left hvec) ?_
  dsimp only [pqRatchetStatePBAt, initialStatePB, optVersionNegotiationPBAt, versionNegotiationPBAt,
    initialStateVN, rustBytesVecAt, optChainParamsPBAt, chainParamsPBAt,
    optChainPBAt, optPqRatchetInnerPBAt]
  have h1c : a + 0x18#64 + 4#64 = a + 0x1c#64 := by bv_omega
  have h20 : a + 0x1c#64 + 4#64 = a + 0x20#64 := by bv_omega
  have h38 : a + 48#64 + 8#64 = a + 0x38#64 := by bv_omega
  rw [h1c, h20, h38,
      CryptoVerification.SpqrV1.Top.Recv.v1StatePBAt_eq_optProtoInnerStateAt A (a + 128#64)
        (initV1State F p.direction p.authKey).into_pb,
      initInnerResultAt_v1]
  exact Entails.of_eq (by ac_rfl)

private theorem rodata_optProtoInnerStateJumpTable {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ optProtoInnerStateJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_bytes% "220036000561663b870a")) (n := 10) (bs := optProtoInnerStateJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

private theorem rodata_statesIntoPbJumpTable {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ States.IntoPb.statesIntoPbJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_bytes% "0000c7005d0098000a00fc001d01b600")) (n := 22) (bs := States.IntoPb.statesIntoPbJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

def InitialStateV1PostGen (calleeStack : Nat) (A : RustAlloc) (F : ShaCompress) (b : BitVec 64)
    (s0 : State) (x : InitialStateGhost) : State → SepProp → Prop :=
  fun sf Pf =>
    (Pf ⊢
      States.IntoPb.statesIntoPbJumpTableAt b ∗ optProtoInnerStateJumpTableAt b ∗
      paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s0.sp (calleeStack + 496)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace

section V1BodyGen

attribute [local irreducible] Program.fnOff

theorem initial_state_v1_body_gen
    {calleeStack : Nat} {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hinit : subroutine_ok (LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext)
      ((LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext).fnAddr initInnerName)
      ((initInnerSpecGen calleeStack A F img.base).inImage img))
    (henc : PqRatchetStateEncodeToVecOkX img A ext)
    (s0 : State) (x : InitialStateGhost) (R : SepProp) (hinv0 : ImgCallInv img s0)
    (hpc : s0.pc = (LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext).fnAddr initialStateName)
    (hrun : s0.status = .Running) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hv : x.p.version = .v1) (hx0 : s0.readReg64 .x0 = x.pA) (hx8 : s0.readReg64 .x8 = x.ret)
    (hak_ne : x.akPtr ≠ 0#64) (hlen : x.p.authKey.length < 2 ^ 32)
    (hlen_pb : (PqRatchetState.encodeRaw (initialStatePB F x.p)).length < 2 ^ 63)
    (hproto_eq : protoPqRatchetStateAt A (s0.sp - 456#64) (initialStatePB F x.p) =
      pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p))
    (hpbAt : ∀ ptr : BitVec 64,
      (vecU8At A (s0.sp - 456#64) (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
        (((s0.sp - 456#64) + 0x18#64) ↦₃₂ 1#32) ∗
        (((s0.sp - 456#64) + 0x1c#64) ↦₃₂ x.p.chainParams.intoPb.maxJump) ∗
        (((s0.sp - 456#64) + 0x20#64) ↦₃₂ x.p.chainParams.intoPb.maxOooKeys) ∗
        (((s0.sp - 456#64) + 0x24#64) ↦₃₂ x.p.direction.toI32) ∗
        (((s0.sp - 456#64) + 0x28#64) ↦₃₂ x.p.minVersion.toI32) ∗
        memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
        (((s0.sp - 456#64) + 0x30#64) ↦₆₄ noneCap) ∗
        memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
        initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey) ⊢
      pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p))
    (hge_ext : extHookStack ≤ calleeStack := by decide)
    (hge_enc : encodeToVecStackX ≤ calleeStack := by decide)
    (hge_drp : dropStack96 ≤ calleeStack := by decide)
    (hmax : calleeStack + 496 ≤ 2 ^ 64 := by decide) :
    SepWPp (LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0
      (States.IntoPb.statesIntoPbJumpTableAt img.base ∗ optProtoInnerStateJumpTableAt img.base ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       A.pool ∗ stackAt s0.sp (calleeStack + 496))
      (InitialStateV1PostGen calleeStack A F img.base s0 x)
      (InitInnerPanic s0 R) := by
  have hc_max : calleeStack ≤ 2 ^ 64 := by omega
  have hlt63 : x.p.authKey.length < 2 ^ 63 := by omega
  have hlt32_63 : 32 + x.p.authKey.length < 2 ^ 63 := by omega
  refine SepWPp.weaken_pre (P' :=
      cells (s0.sp - 96#64) 12 ∗ paramsAt x.pA x.akPtr x.p ∗
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) calleeStack ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ States.IntoPb.statesIntoPbJumpTableAt img.base ∗
       optProtoInnerStateJumpTableAt img.base))
    (by rw [h61s_stackAt_split_gen s0.sp calleeStack hmax]; exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP
    (initial_state_prologue_v1 s0 x _ hb hsp0_align hpc hrun hx0 hx8 hv hlen) ?_
  intro s1 hpc1 hrun1 hinv1 ⟨hsp1, hx29_1, hx19_1, hx20_1, hx21_1, hx22_1, hw25_1, htr1, hvregs1⟩
  refine SepWPp.weaken_pre (P' :=
      (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗
      (memRegion ((s0.sp - 496#64) - BitVec.ofNat 64 calleeStack) (calleeStack - extHookStack) ∗
       paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ States.IntoPb.statesIntoPbJumpTableAt img.base ∗
       optProtoInnerStateJumpTableAt img.base))
    (by rw [stackAt_callee_split (s0.sp - 496#64) calleeStack extHookStack hge_ext hc_max]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine initial_state_to_vec_ext hAx s0 s1 x _ R (hinv1 img hinv0) hsp0_align hlt63
    hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx21_1 hx22_1 hw25_1 htr1 hvregs1 ?_
  intro s2 ptr hpc2 hrun2 hinv_s2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hw25_2 htr2 hvregs2
  refine SepWPp.weaken_pre (P' :=
      paramsAt x.pA x.akPtr x.p ∗
      (memRegion (s0.sp - 456#64) 352 ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       States.IntoPb.statesIntoPbJumpTableAt img.base ∗ A.pool ∗ stackAt (s0.sp - 496#64) calleeStack ∗
       RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
       h61s_initialStateSavedCells s0 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ optProtoInnerStateJumpTableAt img.base))
    (by rw [stackAt_callee_split (s0.sp - 496#64) calleeStack extHookStack hge_ext hc_max]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP
    (initial_state_pre_init_inner s0 s2 x ptr _ hsp0_align
      hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hw25_2 htr2 hvregs2) ?_
  intro s3 hpc3 hrun3 hinv3
    ⟨hsp3, hlr3, hx0_3, hw1_3, hw2_3, hx3_3, hx4_3, hx29_3, hx19_3, hw20_3, hx21_3, hx23_3,
     hw24_3, hw25_3, hw26_3, hw27_3, htr3, hvregs3⟩
  refine SepWPp.weaken_pre (P' :=
      (memRegion ((s0.sp - 456#64) + 0x80#64) optProtoInnerStateSize ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ States.IntoPb.statesIntoPbJumpTableAt img.base ∗
       A.pool ∗ stackAt (s0.sp - 496#64) calleeStack) ∗
      (cells (s0.sp - 456#64) 3 ∗
       (∃∗ v0 : BitVec 32, ((s0.sp - 456#64) + 0x18#64) ↦₃₂ v0) ∗
       (∃∗ v1 : BitVec 32, ((s0.sp - 456#64) + 0x1c#64) ↦₃₂ v1) ∗
       (∃∗ v2 : BitVec 32, ((s0.sp - 456#64) + 0x20#64) ↦₃₂ v2) ∗
       (∃∗ v3 : BitVec 32, ((s0.sp - 456#64) + 0x24#64) ↦₃₂ v3) ∗
       (∃∗ v4 : BitVec 32, ((s0.sp - 456#64) + 0x28#64) ↦₃₂ v4) ∗
       memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
       (∃∗ w6 : BitVec 64, ((s0.sp - 456#64) + 0x30#64) ↦₆₄ w6) ∗
       memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
       RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
       paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ optProtoInnerStateJumpTableAt img.base))
    (by rw [memRegion_pqState_split (s0.sp - 456#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  have hinv_s3 : ImgCallInv img s3 := hinv3 img hinv_s2
  refine call_initInner_gen hinit hb s0 s3 x _ R hinv_s3 hsp0_align hak_ne hlt32_63
    hpc3 hrun3 hsp3 hlr3 hx0_3 hw1_3 hw2_3 hx3_3 hx4_3 htr3 ?_
  intro s4 hpc4 hrun4 hinv4 hsp4 hcs4 htr4
  obtain ⟨hx19_4, hx20_4, hx21_4, _, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, _, hx29_4⟩ := hcs4
  refine SepWPp.weaken_pre (P' :=
      cells (s0.sp - 456#64) 3 ∗
      (∃∗ v0 : BitVec 32, ((s0.sp - 456#64) + 0x18#64) ↦₃₂ v0) ∗
      (∃∗ v1 : BitVec 32, ((s0.sp - 456#64) + 0x1c#64) ↦₃₂ v1) ∗
      (∃∗ v2 : BitVec 32, ((s0.sp - 456#64) + 0x20#64) ↦₃₂ v2) ∗
      (∃∗ v3 : BitVec 32, ((s0.sp - 456#64) + 0x24#64) ↦₃₂ v3) ∗
      (∃∗ v4 : BitVec 32, ((s0.sp - 456#64) + 0x28#64) ↦₃₂ v4) ∗
      memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
      (∃∗ w6 : BitVec 64, ((s0.sp - 456#64) + 0x30#64) ↦₆₄ w6) ∗
      memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
      initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey ∗
      RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
      (memRegion x.ret 32 ∗ A.pool ∗ stackAt (s0.sp - 496#64) calleeStack ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 104#64) 8 ∗
       States.IntoPb.statesIntoPbJumpTableAt img.base ∗ optProtoInnerStateJumpTableAt img.base))
    (Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP
    (initial_state_pre_encode_to_vec s0 s4 x ptr _ (hpbAt ptr) hsp0_align
      hpc4 hrun4 hsp4
      (hx29_4.1.trans hx29_3) (hx19_4.trans hx19_3)
      ((readReg32_of_eq hx20_4).trans hw20_3)
      (hx21_4.trans hx21_3) (hx23_4.trans hx23_3)
      ((readReg32_of_eq hx24_4).trans hw24_3)
      ((readReg32_of_eq hx25_4).trans hw25_3)
      ((readReg32_of_eq hx26_4).trans hw26_3)
      ((readReg32_of_eq hx27_4).trans hw27_3) htr4 (hx29_4.2.trans hvregs3)) ?_
  intro s5 hpc5 hrun5 hinv5 ⟨hsp5, hlr5, hx0_5, hx1_5, hx29_5, hx19_5, htr5, hvregs5⟩
  refine SepWPp.weaken_pre (P' :=
      ∃∗ r0 : BitVec 64,
        (memRegion (x.ret + 8#64) 24 ∗
         pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
         A.pool ∗ stackAt (s0.sp - 496#64) encodeToVecStackX) ∗
        ((x.ret ↦₆₄ r0) ∗
         memRegion ((s0.sp - 496#64) - BitVec.ofNat 64 calleeStack) (calleeStack - encodeToVecStackX) ∗
         (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
         ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
         memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 104#64) 8 ∗
         States.IntoPb.statesIntoPbJumpTableAt img.base ∗ optProtoInnerStateJumpTableAt img.base))
    (by
      rw [memRegion_ret_32_split x.ret,
          stackAt_callee_split (s0.sp - 496#64) calleeStack encodeToVecStackX hge_enc hc_max]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Arm64.Entails.sepExists_elim; intro r0
      exact Entails.sepExists_right r0 (Entails.of_eq (by ac_rfl))) ?_
  refine SepWPp.exists_elim fun r0 => ?_
  have hinv_s5 : ImgCallInv img s5 := hinv5 img hinv4
  refine call_encodeToVec_x henc s0 s5 x _ R hinv_s5 hsp0_align hlen_pb
    hpc5 hrun5 hsp5 hlr5 hx0_5 hx1_5 htr5 ?_
  intro s6 hpc6 hrun6 _ hsp6 hcs6 htr6
  obtain ⟨hx19_6, _, _, _, _, _, _, _, _, _, hx29_6⟩ := hcs6
  refine SepWPp.weaken_pre (P' :=
      (x.ret ↦₆₄ r0) ∗ vecU8 A (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p)) ∗
      (pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
       optProtoInnerStateJumpTableAt img.base ∗ A.pool ∗ stackAt (s0.sp - 496#64) calleeStack ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 104#64) 8 ∗
       States.IntoPb.statesIntoPbJumpTableAt img.base))
    (by rw [stackAt_callee_split (s0.sp - 496#64) calleeStack encodeToVecStackX hge_enc hc_max]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP
    (initial_state_pre_drop s0 s6 x r0 _ hv hsp0_align
      hpc6 hrun6 hsp6 (hx29_6.1.trans hx29_5) (hx19_6.trans hx19_5) htr6 (hx29_6.2.trans hvregs5)) ?_
  intro s7 hpc7 hrun7 _ ⟨hsp7, hlr7, hx0_7, hx29_7, htr7, hvregs7⟩
  refine SepWPp.weaken_pre (P' :=
      (pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
       optProtoInnerStateJumpTableAt img.base ∗ A.pool ∗ stackAt (s0.sp - 496#64) dropStack96) ∗
      (memRegion ((s0.sp - 496#64) - BitVec.ofNat 64 calleeStack) (calleeStack - dropStack96) ∗
       initialStateResultAt A x.ret (initialStateValue F x.p) ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 104#64) 8 ∗
       States.IntoPb.statesIntoPbJumpTableAt img.base))
    (by rw [stackAt_callee_split (s0.sp - 496#64) calleeStack dropStack96 hge_drp hc_max]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine call_dropPqRatchetState hdealloc hb s0 s7 x _ R hproto_eq hsp0_align
    hpc7 hrun7 hsp7 hlr7 hx0_7 htr7 ?_
  intro s8 hpc8 hrun8 hsp8 hcs8 htr8
  refine SepWPp.weaken_pre (P' :=
      stackAt (s0.sp - 496#64) calleeStack ∗ memRegion (s0.sp - 496#64) 40 ∗
      memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
      h61s_initialStateSavedCells s0 ∗
      (States.IntoPb.statesIntoPbJumpTableAt img.base ∗ optProtoInnerStateJumpTableAt img.base ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       initialStateResultAt A x.ret (initialStateValue F x.p) ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       A.pool))
    (by rw [stackAt_callee_split (s0.sp - 496#64) calleeStack dropStack96 hge_drp hc_max]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP
    (initial_state_epilogue s0 s8 _ hsp0_align hpc8 hrun8 hsp8 htr8
      (hcs8.2.2.2.2.2.2.2.2.2.2.2.trans hvregs7) hmax) ?_
  intro sf hpcf hrunf _ ⟨hspf, hcsf, htrf⟩
  exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), hspf, hcsf, htrf⟩

end V1BodyGen

theorem sepWPp_of_initialState_v1_wpp {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (x : InitialStateGhost) (P R : SepProp)
    (hwpp : SepWPp (LibsignalTripleRatchet.tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0 P
      (InitialStateV1PostGen initInnerStack A F b s0 x) (InitInnerPanic s0 R)) :
    SepWPp (LibsignalTripleRatchet.tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0 P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initialStateSpec A F b).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initialStateSpec A F b).onPanic x s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hent, hspf, hcsf, htrf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR; dsimp only [initialStateSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrf, ?_⟩
    rw [show initialStateStack = initInnerStack + 496 from rfl]
    have hm1 := Satisfies.mono (sepConj_mono_left hent) hmR
    have hm2 : sf.mem ⊨
        (States.IntoPb.statesIntoPbJumpTableAt b ∗ optProtoInnerStateJumpTableAt b) ∗
        ((paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
          initialStateResultAt A x.ret (initialStateValue F x.p) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          A.pool ∗ stackAt s0.sp (initInnerStack + 496)) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1
    exact Satisfies.of_sep_right hm2
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, ?_⟩)⟩
    intro hmR; dsimp only [initialStateSpec, initialStateOnPanic]
    simpa [sepConj_assoc] using hqp hmR
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- `version = .v1` path of `spqr::initial_state`: clones `auth_key`, runs `spqr::init_inner`,
encodes `initialStatePB F p` into `ret + 8`, and drops the stack `PqRatchetState`. -/
theorem initialState_v1_ok
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContracts img A F ext) :
    subroutine_ok (LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext)
      ((LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext).fnAddr initialStateName)
      (initialStateVSpecX A F img .v1) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hcode => ?_
  have hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp
  dsimp only [initialStateVSpecX, initialStateSpecX, Spec.inImage, initialStateSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hv, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hak_ne, hlen⟩, hmem⟩ := hpre
  have hmem1 := rodata_optProtoInnerStateJumpTable hC.himg hinv0.1 hmem
  have hmem2 := rodata_statesIntoPbJumpTable hC.himg hinv0.1 hmem1
  have hmem3 : s0.mem ⊨
      (States.IntoPb.statesIntoPbJumpTableAt img.base ∗ optProtoInnerStateJumpTableAt img.base ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       A.pool ∗ stackAt s0.sp (initInnerStack + 496)) ∗ R := by
    rw [show initInnerStack + 496 = initialStateStack from rfl]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
  have hwpp := initial_state_v1_body_gen (calleeStack := initInnerStack)
    hC.base_aligned (AllocContractsX.of_AllocContracts hC.hA) hC.hA.dealloc
    hC.initInner_ok hC.encodeToVec_ok
    s0 x R hinv0 hpc hrun hsp_align hv hx0 hx8 hak_ne hlen
    (initialStatePB_encodeRaw_length_lt F x.p hlen)
    (Top.Recv.protoPqRatchetStateAt_eq_pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p))
    (fun ptr => initialState_pbAt_of_cells A F x.p hv (s0.sp - 456#64)
      (BitVec.ofNat 64 x.p.authKey.length) ptr)
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hq, hspf, hcsf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩ :=
    sepWPp_of_initialState_v1_wpp s0 x _ R hwpp R hmem3 hcode
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, hq hmf⟩))
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hqp hmf⟩)))
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 5. Top-level theorems -/

/-- `InitialStateOkX` from `InitialStateContracts`. -/
theorem initialState_ok_x_of_contracts
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContracts img A F ext) :
    InitialStateOkX img A F ext :=
  initialState_ok_of_versions (initialState_v0_ok hC) (initialState_v1_ok hC)

/-- `InitialStateOkX` from `Obj.Loads`, `AllocContracts`, and `AuthNewOkX`. -/
theorem initial_state_ok_x
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hAuthNew : AuthNewOkX img F A ext) :
    InitialStateOkX img A F ext :=
  initialState_ok_x_of_contracts (initialStateContracts_of_okX himg hA hAuthNew)

/-- Entrypoint correctness of `spqr::initial_state` on `Program.ofImage img (Rust.withPanics ext)`. -/
theorem initial_state_ok_entry
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hAuthNew : AuthNewOkX img F A ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img initialStateName) (initialStateSpecX A F img) :=
  root_of_tripleRatchetProgAtExt himg (initial_state_ok_x himg hA hAuthNew)

/-! ## 6. Contract-Backed (`*Ext`, `initialStateStackExt = 19408`B) Theorems -/

/-- Monotonicity lift from `InitialStateOkExt` (`18176`B) to `InitialStateBaseOkExt` (`19408`B). -/
theorem InitialStateOkExt.toBaseExt {b : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} (h : InitialStateOkExt b A F ext) :
    InitialStateBaseOkExt b A F ext := by
  unfold InitialStateBaseOkExt
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let F_stk : SepProp := memRegion (s0.sp - 19408#64) 1232
  have hpre' : s0.mem ⊨ (initialStateSpec A F b).pre x s0 ∗ (F_stk ∗ R) := by
    dsimp only [F_stk, initialStateSpecExt, initialStateSpec] at hpre ⊢
    rw [stackAt_initialStateExt_split_base s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine (h.to_outcome x (F_stk ∗ R) s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [F_stk, initialStateSpecExt, initialStateSpec] at hpost ⊢
    rw [stackAt_initialStateExt_split_base s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [initialStateSpecExt, initialStateSpec, initialStateOnPanic] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    simpa only [sepConj_assoc] using ProofLib.allowPanic_frame id hpost
  · exact (ProofLib.allowPanic_not_exited hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-- Monotonicity lift from `InitialStateOkX` (`18176`B) to `InitialStateOkXExt` (`19408`B). -/
theorem InitialStateOkX.toExt {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} (h : InitialStateOkX img A F ext) :
    InitialStateOkXExt img A F ext := by
  unfold InitialStateOkXExt
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let F_stk : SepProp := memRegion (s0.sp - 19408#64) 1232
  have hpre' : s0.mem ⊨ (initialStateSpecX A F img).pre x s0 ∗ (F_stk ∗ R) := by
    dsimp only [F_stk, initialStateSpecXExt, initialStateSpecX, Spec.inImage,
      initialStateSpecExt, initialStateSpec] at hpre ⊢
    rw [stackAt_initialStateExt_split_base s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine (h.to_outcome x (F_stk ∗ R) s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [F_stk, initialStateSpecXExt, initialStateSpecX, Spec.inImage,
      initialStateSpecExt, initialStateSpec] at hpost ⊢
    rw [stackAt_initialStateExt_split_base s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [initialStateSpecXExt, initialStateSpecX, Spec.inImage,
      initialStateSpecExt, initialStateSpec, initialStateOnPanic] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    simpa only [sepConj_assoc] using ProofLib.allowPanic_frame id hpost
  · exact (ProofLib.allowPanic_not_exited hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-- Extended (`*Ext`) callee contract bundle for `spqr::initial_state` at `initialStateStackExt`
(`19408`B), parameterized over `AllocContractsX`, `DeallocOkExt`, `InitInnerOkXExt`, and
`PqRatchetStateEncodeToVecOkX`. -/
structure InitialStateContractsExt (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop where
  /-- Base page alignment (`img.base &&& 0xfff#64 = 0#64`). -/
  base_aligned : img.base &&& 0xfff#64 = 0#64
  /-- The libsignal session object image is loaded in `img`. -/
  himg : Obj.Loads libsignalSessionImage img
  /-- Extended (`extHookStack = 16384`B) Rust allocator / `memcpy` / no-alloc-shim contracts. -/
  hAx : AllocContractsX img A ext
  /-- Deallocator contract for `drop_glue::<PqRatchetState>`. -/
  hdealloc : DeallocOkExt img.base A ext
  /-- Contract-backed `spqr::init_inner` (`initInnerStackExt = 18912`B). -/
  initInner_ok : InitInnerOkXExt img A F ext
  /-- `<PqRatchetState as prost::Message>::encode_to_vec`. -/
  encodeToVec_ok : PqRatchetStateEncodeToVecOkX img A ext

def initialStateVSpecXExt (A : RustAlloc) (F : ShaCompress) (img : Obj.Image) (v : Version) :
    Spec InitialStateGhost :=
  { initialStateSpecXExt A F img with
    pre := fun x s => ⌜x.p.version = v⌝ ∗ (initialStateSpecXExt A F img).pre x s }

theorem initialState_ok_ext_of_versions
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h0 : subroutine_ok (LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext)
      ((LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext).fnAddr initialStateName)
      (initialStateVSpecXExt A F img .v0))
    (h1 : subroutine_ok (LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext)
      ((LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext).fnAddr initialStateName)
      (initialStateVSpecXExt A F img .v1)) :
    InitialStateOkXExt img A F ext := by
  unfold InitialStateOkXExt
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have key : ∀ v, x.p.version = v →
      s0.mem ⊨ (initialStateVSpecXExt A F img v).pre x s0 ∗ R := by
    intro v hv
    dsimp only [initialStateVSpecXExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hv, hpre⟩
  cases hv : x.p.version with
  | v0 => exact (h0.to_outcome x R s0 hpc hrun (key .v0 hv) hsp).mono_outcome fun _ hout => hout
  | v1 => exact (h1.to_outcome x R s0 hpc hrun (key .v1 hv) hsp).mono_outcome fun _ hout => hout

theorem InitialStateContracts.toExt
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContracts img A F ext) :
    InitialStateContractsExt img A F ext where
  base_aligned := hC.base_aligned
  himg := hC.himg
  hAx := AllocContractsX.of_AllocContracts hC.hA
  hdealloc := hC.hA.dealloc
  initInner_ok := hC.initInner_ok.toExt
  encodeToVec_ok := hC.encodeToVec_ok

/-- V0 path at `initialStateStackExt` (`19408`B). -/
theorem initialState_v0_ok_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContractsExt img A F ext) :
    subroutine_ok (LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext)
      ((LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext).fnAddr initialStateName)
      (initialStateVSpecXExt A F img .v0) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp0_align hcode => ?_
  dsimp only [initialStateVSpecXExt, initialStateSpecXExt, Spec.inImage, initialStateSpecExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hinv0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, _hak_ne, _hlen⟩, hm⟩
  rw [stackAt_initialStateExt_split_base s0.sp] at hm
  have hpre_eq :
      (paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       A.pool ∗ (stackAt s0.sp initialStateStack ∗ memRegion (s0.sp - 19408#64) 1232)) ∗ R =
      (paramsAt x.pA x.akPtr x.p ∗ memRegion x.ret 32 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       stackAt s0.sp initialStateStack ∗
       ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ memRegion (s0.sp - 19408#64) 1232)) ∗ R := by
    ac_rfl
  rw [hpre_eq] at hm
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hent, hspf, hcsf, htrf⟩ | ⟨_, hoom⟩⟩ :=
    (initialState_v0_step (A := A) (F := F) hC.base_aligned s0 x
      ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ memRegion (s0.sp - 19408#64) 1232)
      hsp0_align hpc hrun hx0 hx8 hv).elim hm hcode
  · refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, ?_⟩))
    dsimp only [initialStateVSpecXExt, initialStateSpecXExt, Spec.inImage, initialStateSpecExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrf, ?_⟩
    have hmf' := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [stackAt_initialStateExt_split_base s0.sp]
    have hpost_eq :
        (paramsAt x.pA x.akPtr x.p ∗ initialStateResultAt A x.ret (initialStateValue F x.p) ∗
         ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
         stackAt s0.sp initialStateStack ∗
         ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ memRegion (s0.sp - 19408#64) 1232)) ∗ R =
        (paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
         initialStateResultAt A x.ret (initialStateValue F x.p) ∗
         ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
         A.pool ∗ (stackAt s0.sp initialStateStack ∗ memRegion (s0.sp - 19408#64) 1232)) ∗ R := by
      ac_rfl
    rwa [hpost_eq] at hmf'
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_of_initialState_v1_wpp_ext {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (x : InitialStateGhost) (P R : SepProp)
    (hwpp : SepWPp (LibsignalTripleRatchet.tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0 P
      (InitialStateV1PostGen initInnerStackExt A F b s0 x) (InitInnerPanic s0 R)) :
    SepWPp (LibsignalTripleRatchet.tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0 P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initialStateSpecExt A F b).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initialStateSpecExt A F b).onPanic x s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hent, hspf, hcsf, htrf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR; dsimp only [initialStateSpecExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrf, ?_⟩
    rw [show initialStateStackExt = initInnerStackExt + 496 from rfl]
    have hm1 := Satisfies.mono (sepConj_mono_left hent) hmR
    have hm2 : sf.mem ⊨
        (States.IntoPb.statesIntoPbJumpTableAt b ∗ optProtoInnerStateJumpTableAt b) ∗
        ((paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
          initialStateResultAt A x.ret (initialStateValue F x.p) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          A.pool ∗ stackAt s0.sp (initInnerStackExt + 496)) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1
    exact Satisfies.of_sep_right hm2
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, ?_⟩)⟩
    intro hmR; dsimp only [initialStateSpecExt, initialStateOnPanic]
    simpa [sepConj_assoc] using hqp hmR
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- V1 path at `initialStateStackExt` (`19408`B). -/
theorem initialState_v1_ok_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContractsExt img A F ext) :
    subroutine_ok (LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext)
      ((LibsignalTripleRatchet.tripleRatchetProgAtExt img.base ext).fnAddr initialStateName)
      (initialStateVSpecXExt A F img .v1) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hcode => ?_
  have hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp
  dsimp only [initialStateVSpecXExt, initialStateSpecXExt, Spec.inImage, initialStateSpecExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hv, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hak_ne, hlen⟩, hmem⟩ := hpre
  have hmem1 := rodata_optProtoInnerStateJumpTable hC.himg hinv0.1 hmem
  have hmem2 := rodata_statesIntoPbJumpTable hC.himg hinv0.1 hmem1
  have hmem3 : s0.mem ⊨
      (States.IntoPb.statesIntoPbJumpTableAt img.base ∗ optProtoInnerStateJumpTableAt img.base ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       A.pool ∗ stackAt s0.sp (initInnerStackExt + 496)) ∗ R := by
    rw [show initInnerStackExt + 496 = initialStateStackExt from rfl]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
  have hwpp := initial_state_v1_body_gen (calleeStack := initInnerStackExt)
    hC.base_aligned hC.hAx hC.hdealloc hC.initInner_ok hC.encodeToVec_ok
    s0 x R hinv0 hpc hrun hsp_align hv hx0 hx8 hak_ne hlen
    (initialStatePB_encodeRaw_length_lt F x.p hlen)
    (Top.Recv.protoPqRatchetStateAt_eq_pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p))
    (fun ptr => initialState_pbAt_of_cells A F x.p hv (s0.sp - 456#64)
      (BitVec.ofNat 64 x.p.authKey.length) ptr)
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hq, hspf, hcsf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩ :=
    sepWPp_of_initialState_v1_wpp_ext s0 x _ R hwpp R hmem3 hcode
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, hq hmf⟩))
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hqp hmf⟩)))
  · exact (not_satisfies_false_sepConj hoom).elim

/-- `InitialStateOkXExt` from `InitialStateContractsExt`. -/
theorem initialState_ok_x_ext_of_contracts
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContractsExt img A F ext) :
    InitialStateOkXExt img A F ext :=
  initialState_ok_ext_of_versions (initialState_v0_ok_ext hC) (initialState_v1_ok_ext hC)

/-- Entrypoint correctness of `spqr::initial_state` at `initialStateStackExt` from `InitialStateContractsExt`. -/
theorem initialState_ok_entry_ext_of_contracts
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContractsExt img A F ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img initialStateName) (initialStateSpecXExt A F img) :=
  root_of_tripleRatchetProgAtExt hC.himg (initialState_ok_x_ext_of_contracts hC)

/-- Construct `InitialStateContractsExt` from `AllocContractsX`, 4K extern hooks (`AllocHooks`,
`sessionShimSpec`, `sessionMemcpySpec allocHookStack`), `AuthNewOkExt`, and
`PqRatchetStateEncodeToVecOkX`. -/
theorem initialStateContractsExt_of_hooks4k
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAx : AllocContractsX img A ext)
    (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext shimName sessionShimSpec)
    (hMemcpy : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (hAuthNew : AuthNewOkExt img F A ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecOkX img A ext) :
    InitialStateContractsExt img A F ext where
  base_aligned := ProofLib.ObjectLoad.base_aligned_of_loads himg
  himg := himg
  hAx := hAx
  hdealloc := by
    simpa only [DeallocOkExt, dropProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      dealloc_ok_at_ext img.base A ext hAlloc LibsignalTripleRatchet.deallocName 0 (Nat.add_zero _)
  initInner_ok := init_inner_ok_x_ext_of_hooks4k himg hAlloc hShim hMemcpy hAuthNew
  encodeToVec_ok := hEncodeToVec

/-- `InitialStateOkXExt` from `AllocContractsX`, 4K extern hooks, `AuthNewOkExt`, and `PqRatchetStateEncodeToVecOkX`. -/
theorem initialState_ok_x_ext_of_hooks4k
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAx : AllocContractsX img A ext)
    (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext shimName sessionShimSpec)
    (hMemcpy : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (hAuthNew : AuthNewOkExt img F A ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecOkX img A ext) :
    InitialStateOkXExt img A F ext :=
  initialState_ok_x_ext_of_contracts
    (initialStateContractsExt_of_hooks4k himg hAx hAlloc hShim hMemcpy hAuthNew hEncodeToVec)

/-- Entrypoint correctness of `spqr::initial_state` at `initialStateStackExt` from 4K extern hooks and `AuthNewOkExt`. -/
theorem initialState_ok_entry_ext_of_hooks4k
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAx : AllocContractsX img A ext)
    (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext shimName sessionShimSpec)
    (hMemcpy : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (hAuthNew : AuthNewOkExt img F A ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecOkX img A ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img initialStateName) (initialStateSpecXExt A F img) :=
  root_of_tripleRatchetProgAtExt himg
    (initialState_ok_x_ext_of_hooks4k himg hAx hAlloc hShim hMemcpy hAuthNew hEncodeToVec)

/-- `InitialStateOkXExt` from `Obj.Loads`, `AllocContracts`, and `AuthNewOkExt`. -/
theorem initial_state_ok_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hAuthNew : AuthNewOkExt img F A ext) :
    InitialStateOkXExt img A F ext :=
  initialState_ok_x_ext_of_contracts
    { base_aligned := ProofLib.ObjectLoad.base_aligned_of_loads himg
      himg := himg
      hAx := AllocContractsX.of_AllocContracts hA
      hdealloc := hA.dealloc
      initInner_ok := init_inner_ok_x_ext himg hA hAuthNew
      encodeToVec_ok := pqRatchetStateEncodeToVec_okX hA himg }

/-- Entrypoint correctness of `spqr::initial_state` at `initialStateStackExt` from `Obj.Loads`, `AllocContracts`, and `AuthNewOkExt`. -/
theorem initial_state_ok_entry_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hAuthNew : AuthNewOkExt img F A ext) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext))
      (entryOf img initialStateName) (initialStateSpecXExt A F img) :=
  root_of_tripleRatchetProgAtExt himg (initial_state_ok_x_ext himg hA hAuthNew)

end CryptoVerification.SpqrV1.Top.InitialState

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Proof
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# V1 Path Step Lemmas for `spqr::initial_state`

Basic-block and callee-bridge lemmas for the `.v1` execution path (`0x542d0..0x5447c`) of
`spqr::initial_state`.
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
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::initial_state")
  (ls_lemma% fnOff "spqr::init_inner")
  (ls_lemma% fnOff "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")
  (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

/-! ## 1. Stack Frame, Memory Splits, and Address Helpers -/

/-- Callee-saved register save area at `[s0.sp - 96 .. s0.sp)` (`96` bytes = 12 words). -/
def h61s_initialStateSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem h61s_initialStateSavedCells_entails_memRegion (s0 : State) :
    h61s_initialStateSavedCells s0 ⊢ memRegion (s0.sp - 96#64) 96 := by
  unfold h61s_initialStateSavedCells
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

theorem stackAt_initialStateExt_split_base (sp : BitVec 64) :
    stackAt sp initialStateStackExt =
      stackAt sp initialStateStack ∗ memRegion (sp - 19408#64) 1232 := by
  change memRegion (sp - 19408#64) 19408 =
    memRegion (sp - 18176#64) 18176 ∗ memRegion (sp - 19408#64) 1232
  rw [ProofLib.memRegion_split' (b := sp - 19408#64) (n := 1232) (k := 18176)
        (b' := sp - 18176#64) rfl (by bv_omega) (by decide), sepConj_comm]

theorem h61s_stackAt_split_gen (sp : BitVec 64) (calleeStack : Nat)
    (hmax : calleeStack + 496 ≤ 2 ^ 64 := by decide) :
    stackAt sp (calleeStack + 496) =
      stackAt (sp - 496#64) calleeStack ∗ memRegion (sp - 496#64) 40 ∗
      memRegion (sp - 456#64) 352 ∗ memRegion (sp - 104#64) 8 ∗ cells (sp - 96#64) 12 := by
  have h1 := ProofLib.stackAt_split_cells sp (calleeStack + 400) 12
    (by change (calleeStack + 400) + 96 ≤ 2 ^ 64; omega)
  have h1b : BitVec.ofNat 64 (8 * 12) = 96#64 := rfl
  rw [show calleeStack + 496 = (calleeStack + 400) + 8 * 12 by omega, h1, h1b]
  have h2 : stackAt (sp - 96#64) (calleeStack + 400) =
      memRegion ((sp - 496#64) - BitVec.ofNat 64 calleeStack) calleeStack ∗
      memRegion (sp - 496#64) 40 ∗ memRegion (sp - 456#64) 352 ∗ memRegion (sp - 104#64) 8 := by
    unfold stackAt
    have hsub1 : (sp - 96#64) - BitVec.ofNat 64 (calleeStack + 400) =
        (sp - 496#64) - BitVec.ofNat 64 calleeStack := by
      rw [BitVec.ofNat_add, show BitVec.ofNat 64 400 = 400#64 from rfl]; bv_omega
    rw [hsub1,
        ProofLib.memRegion_split' (b := (sp - 496#64) - BitVec.ofNat 64 calleeStack)
          (n := calleeStack) (k := 400) (b' := sp - 496#64) (by omega)
          (by bv_omega) (by omega),
        ProofLib.memRegion_split' (b := sp - 496#64) (n := 40) (k := 360)
          (b' := sp - 456#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 456#64) (n := 352) (k := 8)
          (b' := sp - 104#64) rfl (by bv_omega) (by decide)]
  rw [h2]; unfold stackAt; ac_rfl

theorem h61s_stack_restore_gen (s0 : State) (calleeStack : Nat)
    (hmax : calleeStack + 496 ≤ 2 ^ 64 := by decide) :
    stackAt (s0.sp - 496#64) calleeStack ∗ memRegion (s0.sp - 496#64) 40 ∗
    memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
    h61s_initialStateSavedCells s0 ⊢ stackAt s0.sp (calleeStack + 496) := by
  rw [h61s_stackAt_split_gen s0.sp calleeStack hmax,
      ← ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (h61s_initialStateSavedCells_entails_memRegion s0))))

theorem stackAt_callee_split (sp : BitVec 64) (calleeStack subStack : Nat)
    (hle : subStack ≤ calleeStack := by decide)
    (hmax : calleeStack ≤ 2 ^ 64 := by decide) :
    stackAt sp calleeStack =
      stackAt sp subStack ∗
        memRegion (sp - BitVec.ofNat 64 calleeStack) (calleeStack - subStack) := by
  have h := ProofLib.stackAt_split_bottom sp subStack (calleeStack - subStack) (by omega)
  rw [Nat.add_sub_of_le hle] at h
  rw [h, sepConj_comm]

theorem memRegion_ret_32_split (ret : BitVec 64) :
    memRegion ret 32 = (∃∗ r0 : BitVec 64, ret ↦₆₄ r0) ∗ memRegion (ret + 8#64) 24 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 24)
        (b' := ret + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight ret]

theorem memRegion_pqState_split (a : BitVec 64) :
    memRegion a 352 =
      cells a 3 ∗
      (∃∗ v0 : BitVec 32, (a + 0x18#64) ↦₃₂ v0) ∗ (∃∗ v1 : BitVec 32, (a + 0x1c#64) ↦₃₂ v1) ∗
      (∃∗ v2 : BitVec 32, (a + 0x20#64) ↦₃₂ v2) ∗ (∃∗ v3 : BitVec 32, (a + 0x24#64) ↦₃₂ v3) ∗
      (∃∗ v4 : BitVec 32, (a + 0x28#64) ↦₃₂ v4) ∗ memRegion (a + 0x2c#64) 4 ∗
      (∃∗ w6 : BitVec 64, (a + 0x30#64) ↦₆₄ w6) ∗ memRegion (a + 0x38#64) 72 ∗
      memRegion (a + 0x80#64) optProtoInnerStateSize := by
  change memRegion a 352 =
    cells a 3 ∗
    (∃∗ v0 : BitVec 32, (a + 0x18#64) ↦₃₂ v0) ∗ (∃∗ v1 : BitVec 32, (a + 0x1c#64) ↦₃₂ v1) ∗
    (∃∗ v2 : BitVec 32, (a + 0x20#64) ↦₃₂ v2) ∗ (∃∗ v3 : BitVec 32, (a + 0x24#64) ↦₃₂ v3) ∗
    (∃∗ v4 : BitVec 32, (a + 0x28#64) ↦₃₂ v4) ∗ memRegion (a + 0x2c#64) 4 ∗
    (∃∗ w6 : BitVec 64, (a + 0x30#64) ↦₆₄ w6) ∗ memRegion (a + 0x38#64) 72 ∗
    memRegion (a + 0x80#64) 224
  rw [ProofLib.memRegion_split' (b := a) (n := 24) (k := 328) (b' := a + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x18#64) (n := 4) (k := 324) (b' := a + 0x1c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x1c#64) (n := 4) (k := 320) (b' := a + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x20#64) (n := 4) (k := 316) (b' := a + 0x24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x24#64) (n := 4) (k := 312) (b' := a + 0x28#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x28#64) (n := 4) (k := 308) (b' := a + 0x2c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x2c#64) (n := 4) (k := 304) (b' := a + 0x30#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x30#64) (n := 8) (k := 296) (b' := a + 0x38#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x38#64) (n := 72) (k := 224) (b' := a + 0x80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells a 3 (by decide),
      ProofLib.memRegion_four (a + 0x18#64), ProofLib.memRegion_four (a + 0x1c#64),
      ProofLib.memRegion_four (a + 0x20#64), ProofLib.memRegion_four (a + 0x24#64),
      ProofLib.memRegion_four (a + 0x28#64), ProofLib.memRegion_eight (a + 0x30#64)]

theorem adrp_542f0 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr "spqr::initial_state" + 32#64) &&&
      0xfffffffffffff000#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x4e000) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  rw [Program.fnAddr_rebase, initialState_fnOff]; revert hb; bv_bits

theorem testBit63_ofNat_of_lt {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have hbv : BitVec.ofNat 64 n < 0x100000000#64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h
  revert hbv; generalize BitVec.ofNat 64 n = v; bv_bits

/-! ## 2. Prologue (`+0 -> +232`) and Epilogue (`+396 -> +424 -> ret`) -/

theorem initial_state_prologue_v1 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (x : InitialStateGhost) (Rest : SepProp) (hb : b &&& 0xfff#64 = 0#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr initialStateName)
    (hrun : s0.status = .Running) (hx0 : s0.readReg64 .x0 = x.pA) (hx8 : s0.readReg64 .x8 = x.ret)
    (hv : x.p.version = .v1) (hlen : x.p.authKey.length < 2 ^ 32) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initialStateName + 232#64) s0
      (cells (s0.sp - 96#64) 12 ∗ paramsAt x.pA x.akPtr x.p ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ h61s_initialStateSavedCells s0 ∗ paramsAt x.pA x.akPtr x.p ∗
              ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Rest) ∧
        s1.sp = s0.sp - 496#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x19 = x.ret ∧ s1.readReg64 .x20 = x.pA ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
        s1.readReg64 .x22 = x.akPtr ∧ s1.readReg32 .x25 = 1#32 ∧ s1.trace = s0.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0) := by
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hadrp := adrp_542f0 (b := b) (H := Rust.withPanics ext) hb
  have htbz := testBit63_ofNat_of_lt hlen
  initial_state_fetches_range b (Rust.withPanics ext) 0 56
  initial_state_fetches_range b (Rust.withPanics ext) 172 20
  initial_state_fetches_range b (Rust.withPanics ext) 224 8
  dsimp only [tripleRatchetProgAtExt, initialStateName, paramsAt,
    State.readReg32, Reg.x0, Reg.x8, Reg.x25, BitVec.ofNat_eq_ofNat]
    at hpc hx0 hx8 hadrp ⊢
  simp only [hv, Version.toI32]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::initial_state" = entry
  examples_hide_fetches; cells_unfold; wp_pull_exists
  dsimp only [h61s_initialStateSavedCells]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

theorem initial_state_epilogue {b : BitVec 64} {ext : String → Option (State → State)}
    {calleeStack : Nat}
    (s0 s : State) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initialStateName + 396#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64) (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hmax : calleeStack + 496 ≤ 2 ^ 64 := by decide) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 496#64) calleeStack ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       h61s_initialStateSavedCells s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp (calleeStack + 496) ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrestore :
      (stackAt (s0.sp - 496#64) calleeStack ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       h61s_initialStateSavedCells s0) ∗ Rest ⊢ stackAt s0.sp (calleeStack + 496) ∗ Rest :=
    sepConj_mono_left (h61s_stack_restore_gen s0 calleeStack hmax)
  refine SepWP.strengthen_entails_const hrestore ?_
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  initial_state_fetches_range b (Rust.withPanics ext) 396 32
  dsimp only [tripleRatchetProgAtExt, initialStateName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::initial_state" = entry
  examples_hide_fetches; dsimp only [h61s_initialStateSavedCells]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-! ## 3. `auth_key.to_vec()` (`+232 -> +284`) and OOM Panic (`+196 -> +204`) -/

theorem vecU8Buf_nil (A : RustAlloc) : (emp : SepProp) ⊢ RustHeap.vecU8Buf A 0#64 1#64 [] := by
  unfold RustHeap.vecU8Buf
  exact Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)

theorem vecU8Buf_nonempty (A : RustAlloc) (ptr : BitVec 64) (bs : Bytes)
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs) ⊢
      RustHeap.vecU8Buf A (BitVec.ofNat 64 bs.length) ptr bs := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h; have := congrArg BitVec.toNat h
    rw [htoNat] at this; change bs.length = 0 at this; omega
  unfold RustHeap.vecU8Buf
  refine Entails.pure_right ⟨by omega, by omega, hptr⟩ ?_
  rw [ite_eq_right_iff.mpr (fun h => absurd h hcap_ne),
    htoNat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  exact Entails.refl _

theorem initial_state_to_vec_empty {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (Rest : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initialStateName + 232#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.pA) (hx21 : s.readReg64 .x21 = 0#64)
    (hx22 : s.readReg64 .x22 = x.akPtr) (hw25 : s.readReg32 .x25 = 1#32)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initialStateName + 284#64) s Rest
      (fun s2 P2 =>
        (P2 ⊢ RustHeap.vecU8Buf A 0#64 1#64 [] ∗ Rest) ∧
        s2.sp = s0.sp - 496#64 ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x19 = x.ret ∧ s2.readReg64 .x20 = x.pA ∧
        s2.readReg64 .x21 = 0#64 ∧ s2.readReg64 .x22 = x.akPtr ∧
        s2.readReg64 .x23 = 1#64 ∧ s2.readReg32 .x25 = 1#32 ∧ s2.trace = s0.trace ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0) := by
  have hbuf : Rest ⊢ RustHeap.vecU8Buf A 0#64 1#64 [] ∗ Rest :=
    Entails.trans (Entails.of_eq (emp_sepConj Rest).symm) (sepConj_mono_left (vecU8Buf_nil A))
  refine SepWP.strengthen_entails_const hbuf ?_
  initial_state_fetches_range b (Rust.withPanics ext) 232 4
  initial_state_fetches_range b (Rust.withPanics ext) 280 4
  dsimp only [tripleRatchetProgAtExt, initialStateName,
    State.readReg32, Reg.x25, BitVec.ofNat_eq_ofNat] at hpc hw25 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::initial_state" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem initial_state_panic_196 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initialStateName + 196#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (InitInnerPanic s0 R) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext) (name := initialStateName)
    (k := num% (ls_rel% "spqr::initial_state" "alloc::raw_vec::handle_error"))
  initial_state_fetches_range b (Rust.withPanics ext) 196 12
  dsimp only [tripleRatchetProgAtExt, initialStateName, BitVec.ofNat_eq_ofNat]
    at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::initial_state" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_rel% "spqr::initial_state" "alloc::raw_vec::handle_error"))
  wp_steps
  apply ProofLib.SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [InitInnerPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-! ## 4. Callee Address Bridges and `spqr::init_inner` Call (`+284 -> +340`) -/

def initInnerSpecGen (calleeStack : Nat) (A : RustAlloc) (F : ShaCompress) (b : BitVec 64) :
    Spec InitInnerGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63 ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s.sp calleeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      initInnerResultAt A (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp calleeStack
  onPanic := fun _ s0 sf => initInnerOnPanic s0 sf

private theorem spqrInitInner_fnOff :
    libsignalSessionCode.fnOff initInnerName = num% (ls_off% "spqr::init_inner") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "spqr::init_inner")

theorem initialState_initInner_ok_gen
    {calleeStack : Nat} {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hinit : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initInnerName)
      ((initInnerSpecGen calleeStack A F img.base).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initialStateName +
        bv% (2 ^ 64 - ls_rel% "spqr::init_inner" "spqr::initial_state"))
      ((initInnerSpecGen calleeStack A F img.base).inImage img) := by
  have hrel : (tripleRatchetProgAtExt img.base ext).fnAddr initialStateName =
      (tripleRatchetProgAtExt img.base ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "spqr::initial_state") :=
    Program.fnAddr_rel (k := num% (ls_rel% "spqr::init_inner" "spqr::initial_state"))
      (b := img.base) (X := Rust.withPanics ext)
      spqrInitInner_fnOff (ls_lemma% fnOff "spqr::initial_state") (by decide)
  exact sub_ok_of_addr_eq (by rw [hrel]; bv_omega) hinit

theorem initialState_encodeToVec_ok
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (henc : PqRatchetStateEncodeToVecOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initialStateName +
        bv% (ls_rel% "spqr::initial_state" "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      ((pqRatchetStateEncodeToVecSpecX A).inImage img) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "spqr::initial_state" "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (b := img.base) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "spqr::initial_state") spqrEncodeToVec_fnOff (by decide))
    henc

theorem initialState_dropPqRatchetState_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initialStateName +
        bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "spqr::initial_state"))
      (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStateSpec A b) := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr initialStateName =
      (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "spqr::initial_state") :=
    Program.fnAddr_rel
      (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "spqr::initial_state"))
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>")
      (ls_lemma% fnOff "spqr::initial_state") (by decide)
  refine sub_ok_of_addr_eq ?_ (drop_proto_pq_ratchet_state_ok_ext hdealloc)
  rw [hrel, BitVec.add_assoc]; simp

theorem csel_maxJump_eq (cp : ChainParams) :
    BitVec.truncate 32
      (if (cp.maxJump == 25000#32) = true then 0#64 else BitVec.truncate 64 cp.maxJump) =
      cp.intoPb.maxJump := by
  unfold ChainParams.intoPb DEFAULT_CHAIN_PARAMS
  by_cases h : cp.maxJump = 25000#32 <;> simp [h]

theorem csel_maxOoo_eq (cp : ChainParams) :
    BitVec.truncate 32
      (if (cp.maxOooKeys == 2000#32) = true then 0#64 else BitVec.truncate 64 cp.maxOooKeys) =
      cp.intoPb.maxOooKeys := by
  unfold ChainParams.intoPb DEFAULT_CHAIN_PARAMS
  by_cases h : cp.maxOooKeys = 2000#32 <;> simp [h]

attribute [local wp_norm] csel_maxJump_eq csel_maxOoo_eq

theorem initial_state_pre_init_inner {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (ptr : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initialStateName + 284#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.pA) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length)
    (hx22 : s.readReg64 .x22 = x.akPtr) (hx23 : s.readReg64 .x23 = ptr)
    (hw25 : s.readReg32 .x25 = 1#32) (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initialStateName +
        bv% (2 ^ 64 - ls_rel% "spqr::init_inner" "spqr::initial_state")) s
      (paramsAt x.pA x.akPtr x.p ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ paramsAt x.pA x.akPtr x.p ∗ Rest) ∧
        s2.sp = s0.sp - 496#64 ∧
        s2.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initialStateName + 344#64 ∧
        s2.readReg64 .x0 = (s0.sp - 456#64) + 0x80#64 ∧
        s2.readReg32 .x1 = Version.v1.toI32 ∧ s2.readReg32 .x2 = x.p.direction.toI32 ∧
        s2.readReg64 .x3 = x.akPtr ∧ s2.readReg64 .x4 = BitVec.ofNat 64 x.p.authKey.length ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧ s2.readReg64 .x19 = x.ret ∧
        s2.readReg32 .x20 = x.p.minVersion.toI32 ∧
        s2.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧ s2.readReg64 .x23 = ptr ∧
        s2.readReg32 .x24 = x.p.direction.toI32 ∧ s2.readReg32 .x25 = 1#32 ∧
        s2.readReg32 .x26 = x.p.chainParams.intoPb.maxJump ∧
        s2.readReg32 .x27 = x.p.chainParams.intoPb.maxOooKeys ∧ s2.trace = s0.trace ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0) := by
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  initial_state_fetches_range b (Rust.withPanics ext) 284 60
  dsimp only [tripleRatchetProgAtExt, initialStateName, paramsAt, Version.toI32,
    State.readReg32, Reg.x1, Reg.x2, Reg.x20, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
    BitVec.ofNat_eq_ofNat] at hpc hw25 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::initial_state" = entry
  examples_hide_fetches; wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

theorem sepWPp_call_inImage {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {α : Type} {entry ret_pc : BitVec 64}
    {spec : Spec α} {img : Obj.Image} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry spec) (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp :=
  ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hinv.1 hinv.2 hpc hrun hsp hlr hpre hexit
    (fun sf hpan _ => hpanic sf hpan)
    (fun sf hpcm hrunm hspm hcsm hfz hsym => hnext sf hpcm hrunm hspm hcsm ⟨hfz, hsym⟩)
    (fun sf _ _ hpost => by rw [hoom_eq] at hpost; exact (not_satisfies_false_sepConj hpost).elim)

theorem call_initInner_gen
    {calleeStack : Nat} {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hinit : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initInnerName)
      ((initInnerSpecGen calleeStack A F img.base).inImage img))
    (hb : img.base &&& 0xfff#64 = 0#64)
    {Q : State → SepProp → Prop}
    (s0 s : State) (x : InitialStateGhost) (Frame R : SepProp)
    (hinv : ImgCallInv img s) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hak_ne : x.akPtr ≠ 0#64) (hlt : 32 + x.p.authKey.length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initialStateName +
      bv% (2 ^ 64 - ls_rel% "spqr::init_inner" "spqr::initial_state"))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hlr : s.readReg64 .x30 = (tripleRatchetProgAtExt img.base ext).fnAddr initialStateName + 344#64)
    (hx0 : s.readReg64 .x0 = (s0.sp - 456#64) + 0x80#64)
    (hw1 : s.readReg32 .x1 = Version.v1.toI32) (hw2 : s.readReg32 .x2 = x.p.direction.toI32)
    (hx3 : s.readReg64 .x3 = x.akPtr) (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 x.p.authKey.length)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initialStateName + 344#64 →
      sf.status = .Running → ImgCallInv img sf → sf.sp = s0.sp - 496#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
        ((initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey ∗
          (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTableAt img.base ∗
          A.pool ∗ stackAt (s0.sp - 496#64) calleeStack) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      ((memRegion ((s0.sp - 456#64) + 0x80#64) optProtoInnerStateSize ∗
        (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTableAt img.base ∗
        A.pool ∗ stackAt (s0.sp - 496#64) calleeStack) ∗ Frame)
      Q (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hcall := initialState_initInner_ok_gen hinit
  let gx : InitInnerGhost := ⟨(s0.sp - 456#64) + 0x80#64, .v1, x.p.direction, x.akPtr, x.p.authKey⟩
  refine sepWPp_call_inImage hcall (x := gx) (F := Frame) hinv
    hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr ?_
    (fun _ _ _ _ h => ProofLib.allowPanic_not_exited h) (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    dsimp only [Spec.inImage, initInnerSpecGen, gx]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨hinv, ⟨hx0, hw1, hw2, hx3, hx4, hak_ne, hlt, hb⟩, hm⟩
  · change (sf.mem ⊨ (((initInnerSpecGen calleeStack A F img.base).inImage img).onPanic gx s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem
    dsimp only [Spec.inImage, initInnerSpecGen, initInnerOnPanic] at hmem
    rw [← sepConj_assoc]
    have hpan := ProofLib.allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by
        unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [Spec.inImage, initInnerSpecGen, gx]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hnext' := hnext sf hpc_sf hrun_sf hinv_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hnext'

/-! ## 5. `PqRatchetState` Stores (`+344 -> +380`) and `encode_to_vec` Call -/

theorem initial_state_pre_encode_to_vec
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (ptr : BitVec 64) (Rest : SepProp)
    (hpbAt :
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
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initialStateName + 344#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hw20 : s.readReg32 .x20 = x.p.minVersion.toI32)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length) (hx23 : s.readReg64 .x23 = ptr)
    (hw24 : s.readReg32 .x24 = x.p.direction.toI32) (hw25 : s.readReg32 .x25 = 1#32)
    (hw26 : s.readReg32 .x26 = x.p.chainParams.intoPb.maxJump)
    (hw27 : s.readReg32 .x27 = x.p.chainParams.intoPb.maxOooKeys) (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initialStateName +
        bv% (ls_rel% "spqr::initial_state" "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) s
      (cells (s0.sp - 456#64) 3 ∗
       (∃∗ v0 : BitVec 32, ((s0.sp - 456#64) + 0x18#64) ↦₃₂ v0) ∗
       (∃∗ v1 : BitVec 32, ((s0.sp - 456#64) + 0x1c#64) ↦₃₂ v1) ∗
       (∃∗ v2 : BitVec 32, ((s0.sp - 456#64) + 0x20#64) ↦₃₂ v2) ∗
       (∃∗ v3 : BitVec 32, ((s0.sp - 456#64) + 0x24#64) ↦₃₂ v3) ∗
       (∃∗ v4 : BitVec 32, ((s0.sp - 456#64) + 0x28#64) ↦₃₂ v4) ∗
       memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
       (∃∗ w6 : BitVec 64, ((s0.sp - 456#64) + 0x30#64) ↦₆₄ w6) ∗
       memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
       initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey ∗
       RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗ Rest) ∧
        s2.sp = s0.sp - 496#64 ∧
        s2.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initialStateName + 384#64 ∧
        s2.readReg64 .x0 = x.ret + 8#64 ∧ s2.readReg64 .x1 = s0.sp - 456#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧ s2.readReg64 .x19 = x.ret ∧ s2.trace = s0.trace ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0) := by
  have hfold :
      ((((s0.sp - 456#64) ↦₆₄ BitVec.ofNat 64 x.p.authKey.length) ∗
        ((s0.sp - 448#64) ↦₆₄ ptr) ∗
        ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 x.p.authKey.length) ∗
        RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey) ∗
       (((s0.sp - 456#64) + 0x18#64) ↦₃₂ 1#32) ∗
       (((s0.sp - 456#64) + 0x1c#64) ↦₃₂ x.p.chainParams.intoPb.maxJump) ∗
       (((s0.sp - 456#64) + 0x20#64) ↦₃₂ x.p.chainParams.intoPb.maxOooKeys) ∗
       (((s0.sp - 456#64) + 0x24#64) ↦₃₂ x.p.direction.toI32) ∗
       (((s0.sp - 456#64) + 0x28#64) ↦₃₂ x.p.minVersion.toI32) ∗
       memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
       (((s0.sp - 456#64) + 0x30#64) ↦₆₄ noneCap) ∗
       memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
       initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey) ∗
      Rest ⊢ pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗ Rest := by
    refine sepConj_mono_left (Entails.trans ?_ hpbAt)
    dsimp only [vecU8At, vecHeader, RustHeap.vecU8At, RustHeap.vecAt, RustHeap.vecHeader, RustHeap.vecU8Buf]
    exact Entails.of_eq (by simp only [arm64_norm])
  refine SepWP.strengthen_entails_const hfold ?_
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  initial_state_fetches_range b (Rust.withPanics ext) 344 40
  dsimp only [tripleRatchetProgAtExt, initialStateName, noneCap,
    State.readReg32, Reg.x20, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
    BitVec.ofNat_eq_ofNat] at hpc hw20 hw24 hw25 hw26 hw27 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::initial_state" = entry
  examples_hide_fetches; cells_unfold; wp_pull_exists; wp_steps
  refine Drop.align_pre (by simp only [arm64_norm]; ac_rfl) ?_
  wp_done

theorem call_encodeToVec_x
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (henc : PqRatchetStateEncodeToVecOkX img A ext)
    {Q : State → SepProp → Prop}
    (s0 s : State) (x : InitialStateGhost) (Frame R : SepProp)
    (hinv : ImgCallInv img s) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen_pb : (PqRatchetState.encodeRaw (initialStatePB F x.p)).length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initialStateName +
      bv% (ls_rel% "spqr::initial_state" "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hlr : s.readReg64 .x30 = (tripleRatchetProgAtExt img.base ext).fnAddr initialStateName + 384#64)
    (hx0 : s.readReg64 .x0 = x.ret + 8#64) (hx1 : s.readReg64 .x1 = s0.sp - 456#64)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initialStateName + 384#64 →
      sf.status = .Running → ImgCallInv img sf → sf.sp = s0.sp - 496#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
        ((vecU8 A (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p)) ∗
          pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
          A.pool ∗ stackAt (s0.sp - 496#64) encodeToVecStackX) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      ((memRegion (x.ret + 8#64) 24 ∗
        pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
        A.pool ∗ stackAt (s0.sp - 496#64) encodeToVecStackX) ∗ Frame)
      Q (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hcall := initialState_encodeToVec_ok henc
  let gx : PqRatchetStateEncodeToVecGhost := ⟨x.ret + 8#64, s0.sp - 456#64, initialStatePB F x.p⟩
  refine sepWPp_call_inImage hcall (x := gx) (F := Frame) hinv
    hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr ?_
    (fun _ _ _ _ h => ProofLib.allowPanic_not_exited h) (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    dsimp only [Spec.inImage, pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf, gx]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨hinv, ⟨hx0, hx1, hlen_pb⟩, hm⟩
  · change (sf.mem ⊨ (((pqRatchetStateEncodeToVecSpecX A).inImage img).onPanic gx s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem
    dsimp only [Spec.inImage, pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf] at hmem
    rw [← sepConj_assoc]
    have hpan := ProofLib.allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by
        unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [Spec.inImage, pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf, gx]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hnext' := hnext sf hpc_sf hrun_sf hinv_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hnext'

/-! ## 6. `Ok` Tag Store (`+384 -> +392`) and `drop_glue::<PqRatchetState>` Call -/

theorem initial_state_pre_drop
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (r0 : BitVec 64) (Rest : SepProp)
    (hv : x.p.version = .v1) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initialStateName + 384#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initialStateName +
        bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "spqr::initial_state")) s
      ((x.ret ↦₆₄ r0) ∗
       vecU8 A (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p)) ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ initialStateResultAt A x.ret (initialStateValue F x.p) ∗ Rest) ∧
        s2.sp = s0.sp - 496#64 ∧
        s2.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initialStateName + 396#64 ∧
        s2.readReg64 .x0 = s0.sp - 456#64 ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) := by
  have hres :
      ((x.ret ↦₆₄ 0#64) ∗
       vecU8 A (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p))) ∗ Rest ⊢
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗ Rest := by
    unfold initialStateResultAt initialStateValue; rw [hv]; exact Entails.refl _
  refine SepWP.strengthen_entails_const hres ?_
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  initial_state_fetches_range b (Rust.withPanics ext) 384 12
  dsimp only [tripleRatchetProgAtExt, initialStateName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::initial_state" = entry
  examples_hide_fetches; wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

theorem call_dropPqRatchetState
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext) (hb : b &&& 0xfff#64 = 0#64)
    {Q : State → SepProp → Prop}
    (s0 s : State) (x : InitialStateGhost) (Frame R : SepProp)
    (hproto_eq : protoPqRatchetStateAt A (s0.sp - 456#64) (initialStatePB F x.p) =
      pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initialStateName +
      bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "spqr::initial_state"))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hlr : s.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initialStateName + 396#64)
    (hx0 : s.readReg64 .x0 = s0.sp - 456#64) (htrace : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr initialStateName + 396#64 →
      sf.status = .Running → sf.sp = s0.sp - 496#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        ((memRegion (s0.sp - 456#64) 352 ∗ optProtoInnerStateJumpTableAt b ∗
          A.pool ∗ stackAt (s0.sp - 496#64) dropStack96) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      ((pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
        optProtoInnerStateJumpTableAt b ∗
        A.pool ∗ stackAt (s0.sp - 496#64) dropStack96) ∗ Frame)
      Q (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  rw [← hproto_eq]
  have hcall := initialState_dropPqRatchetState_ok hdealloc
  let gx : DropProtoPqRatchetStateGhost := ⟨s0.sp - 456#64, initialStatePB F x.p⟩
  refine SepWPp.call hcall (x := gx) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr ?_
    (fun _ _ _ _ h => by dsimp only [dropProtoPqRatchetStateSpec, gx] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    dsimp only [dropProtoPqRatchetStateSpec, gx]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hb⟩, hm⟩
  · dsimp only [dropProtoPqRatchetStateSpec, gx] at hmem
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1
  · dsimp only [dropProtoPqRatchetStateSpec, protoPqRatchetStateSize, gx]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hnext' := hnext sf hpc_sf hrun_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hnext'

/-! ## 7. `AllocContractsX`-Backed `auth_key.to_vec()` and Generic V1 Path Composition -/

theorem readReg32_of_eq {s1 s2 : State} {r : Reg} (h : s2.readReg64 r = s1.readReg64 r) :
    s2.readReg32 r = s1.readReg32 r :=
  congrArg (BitVec.truncate 32) h

theorem initial_state_to_vec_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (hAx : AllocContractsX img A ext)
    (s0 s : State) (x : InitialStateGhost) (Frame R : SepProp)
    (hinv : ImgCallInv img s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hlt : x.p.authKey.length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initialStateName + 232#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.pA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length)
    (hx22 : s.readReg64 .x22 = x.akPtr) (hw25 : s.readReg32 .x25 = 1#32)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initialStateName + 284#64 →
      sm.status = .Running → ImgCallInv img sm →
      sm.sp = s0.sp - 496#64 → sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = x.ret → sm.readReg64 .x20 = x.pA →
      sm.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length →
      sm.readReg64 .x22 = x.akPtr → sm.readReg64 .x23 = ptr →
      sm.readReg32 .x25 = 1#32 → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sm
        (RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
         (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗ Frame)
      Q (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  by_cases hlen_zero : x.p.authKey.length = 0
  · have hnil : x.p.authKey = [] := List.eq_nil_of_length_eq_zero hlen_zero
    have hx21_0 : s.readReg64 .x21 = 0#64 := by rw [hx21, hlen_zero]
    refine initInner_seq_sepWP
      (initial_state_to_vec_empty (A := A) s0 s x
        ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗ Frame)
        hpc hrun hsp hx29 hx19 hx20 hx21_0 hx22 hw25 htrace hvregs) ?_
    intro sm hpcm hrunm hinvm ⟨hspm, hx29m, hx19m, hx20m, hx21m, hx22m, hx23m, hw25m, htrm, hvregsm⟩
    have hbuf_eq : RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) 1#64 x.p.authKey =
        RustHeap.vecU8Buf A 0#64 1#64 [] := by
      conv => lhs; rw [hnil]; dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length := by rw [hx21m, hlen_zero]
    rw [← hbuf_eq]
    exact hnext sm 1#64 hpcm hrunm (hinvm img hinv) hspm hx29m hx19m hx20m hx21m' hx22m hx23m hw25m htrm hvregsm
  · have hpos : 0 < x.p.authKey.length := Nat.pos_of_ne_zero hlen_zero
    have htoNat_len : (BitVec.ofNat 64 x.p.authKey.length).toNat = x.p.authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hne_bv0 : BitVec.ofNat 64 x.p.authKey.length ≠ 0#64 := by
      intro h; have h1 := congrArg BitVec.toNat h; rw [htoNat_len] at h1
      change x.p.authKey.length = 0 at h1; omega
    have hbeq0 : (BitVec.ofNat 64 x.p.authKey.length == 0#64) = false := beq_eq_false_iff_ne.mpr hne_bv0
    have hne0 : (BitVec.ofNat 64 x.p.authKey.length != 0#64) = true := bne_iff_ne.mpr hne_bv0
    have hlay : LayoutOk x.p.authKey.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
    have hshim := hAx.shim_ok_at initialStateName
      (num% (ls_rel% "spqr::initial_state" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      extHookStack (by decide) (by decide)
      (by rw [Eq.trans (congrArg libsignalSessionCode.fnOff (rfl : initialStateName = _))
                (ls_lemma% fnOff "spqr::initial_state"),
              Eq.trans (congrArg libsignalSessionCode.fnOff (rfl : shimName = _))
                (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
    have halloc := hAx.alloc_ok_at initialStateName
      (num% (ls_rel% "spqr::initial_state" "__rustc::__rust_alloc"))
      (by rw [Eq.trans (congrArg libsignalSessionCode.fnOff (rfl : initialStateName = _))
                (ls_lemma% fnOff "spqr::initial_state"),
              Eq.trans (congrArg libsignalSessionCode.fnOff (rfl : allocName = _))
                (ls_stub% "__rustc::__rust_alloc")])
    have hmemcpy := hAx.session_memcpy_ok_at initialStateName
      (num% (ls_rel% "spqr::initial_state" "memcpy"))
      extHookStack (by decide) (by decide)
      (by rw [Eq.trans (congrArg libsignalSessionCode.fnOff (rfl : initialStateName = _))
                (ls_lemma% fnOff "spqr::initial_state"),
              Eq.trans (congrArg libsignalSessionCode.fnOff (rfl : memcpyName = _))
                (ls_stub% "memcpy")])
    let prog := tripleRatchetProgAtExt img.base ext
    let fn := prog.fnAddr initialStateName
    have hstepA : SepWP prog
        (fn + bv% (ls_rel% "spqr::initial_state" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) s
        ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗ Frame)
        (fun sa Pa =>
          (Pa ⊢ (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗ Frame) ∧
          sa.sp = s0.sp - 496#64 ∧ sa.readReg64 .x30 = fn + 240#64 ∧
          sa.readReg64 .x29 = s0.sp - 96#64 ∧ sa.readReg64 .x19 = x.ret ∧
          sa.readReg64 .x20 = x.pA ∧ sa.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
          sa.readReg64 .x22 = x.akPtr ∧ sa.readReg32 .x25 = 1#32 ∧
          sa.trace = s0.trace ∧ calleeSavedVRegs sa = calleeSavedVRegs s0) := by
      initial_state_fetches_range img.base (Rust.withPanics ext) 232 8
      dsimp only [prog, fn, tripleRatchetProgAtExt, initialStateName,
        State.readReg32, Reg.x25, BitVec.ofNat_eq_ofNat] at hpc hw25 ⊢
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        "spqr::initial_state" = entry
      examples_hide_fetches; wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    refine initInner_seq_sepWP hstepA fun sa hpca hruna hinva
      ⟨hspa, hlra, hx29a, hx19a, hx20a, hx21a, hx22a, hw25a, htra, hvregsa⟩ => ?_
    have hinv_sa : ImgCallInv img sa := hinva img hinv
    refine sepWPp_call_inImage hshim (x := ())
      (F := (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ Frame) hinv_sa
      (by simpa only [prog, fn, BitVec.ofNat_eq_ofNat] using hpca) hruna
      (by rw [State.spAligned, hspa]; exact hfsp_align) hlra ?_
      (fun _ _ _ _ h => by
        dsimp only [Spec.inImage, withStack, sessionShimSpec] at h
        exact (not_satisfies_false_sepConj h).elim)
      (fun _ _ h => by
        dsimp only [Spec.inImage, withStack, sessionShimSpec] at h; simp only [sepConj_assoc] at h
        exact (not_satisfies_false_sepConj h).elim)
      (fun sb hpcb hrunb hspb hcsb hinv_sb => ?_)
    · intro R' hm
      dsimp only [Spec.inImage, withStack, sessionShimSpec]; rw [hspa]
      simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      exact ⟨hinv_sa, by simpa [sepConj_assoc] using Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
    · dsimp only [Spec.inImage, withStack, sessionShimSpec]; rw [hspa, sepConj_assoc]
      refine SepWPp.pure_left fun htrb => ?_
      obtain ⟨hx19b, hx20b, hx21b, hx22b, _, _, hx25b, _, _, _, hx29b⟩ := hcsb
      have hstepB : SepWP prog
          (fn + bv% (ls_rel% "spqr::initial_state" "__rustc::__rust_alloc")) sb
          (stackAt (s0.sp - 496#64) extHookStack ∗ ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ Frame))
          (fun sc Pc =>
            (Pc ⊢ (A.pool ∗ stackAt (s0.sp - 496#64) extHookStack) ∗
              ((x.akPtr ↦ₛ x.p.authKey) ∗ Frame)) ∧
            sc.sp = s0.sp - 496#64 ∧ sc.readReg64 .x30 = fn + 256#64 ∧
            sc.readReg64 .x0 = BitVec.ofNat 64 x.p.authKey.length ∧ sc.readReg64 .x1 = 1#64 ∧
            sc.readReg64 .x29 = s0.sp - 96#64 ∧ sc.readReg64 .x19 = x.ret ∧
            sc.readReg64 .x20 = x.pA ∧ sc.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
            sc.readReg64 .x22 = x.akPtr ∧ sc.readReg32 .x25 = 1#32 ∧
            sc.trace = s0.trace ∧ calleeSavedVRegs sc = calleeSavedVRegs s0) := by
        have hsp_b : sb.sp = s0.sp - 496#64 := hspb.trans hspa
        have hx29_b : sb.readReg64 .x29 = s0.sp - 96#64 := hx29b.1.trans hx29a
        have hx19_b : sb.readReg64 .x19 = x.ret := hx19b.trans hx19a
        have hx20_b : sb.readReg64 .x20 = x.pA := hx20b.trans hx20a
        have hx21_b : sb.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length := hx21b.trans hx21a
        have hx22_b : sb.readReg64 .x22 = x.akPtr := hx22b.trans hx22a
        have hw25_b : sb.readReg32 .x25 = 1#32 := (readReg32_of_eq hx25b).trans hw25a
        have htr_b : sb.trace = s0.trace := htrb.trans htra
        have hvregs_b : calleeSavedVRegs sb = calleeSavedVRegs s0 := hx29b.2.trans hvregsa
        initial_state_fetches_range img.base (Rust.withPanics ext) 240 16
        dsimp only [prog, fn, tripleRatchetProgAtExt, initialStateName,
          State.readReg32, Reg.x25, BitVec.ofNat_eq_ofNat] at hpcb hw25_b ⊢
        generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
          "spqr::initial_state" = entry
        examples_hide_fetches; wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
      refine initInner_seq_sepWP hstepB fun sc hpcc hrunc hinvc
        ⟨hspc, hlrc, hx0c, hx1c, hx29c, hx19c, hx20c, hx21c, hx22c, hw25c, htrc, hvregsc⟩ => ?_
      have hinv_sc : ImgCallInv img sc := hinvc img hinv_sb
      refine sepWPp_call_inImage halloc (x := (x.p.authKey.length, 1))
        (F := (x.akPtr ↦ₛ x.p.authKey) ∗ Frame) hinv_sc
        (by simpa only [prog, fn, BitVec.ofNat_eq_ofNat] using hpcc) hrunc
        (by rw [State.spAligned, hspc]; exact hfsp_align) hlrc ?_
        (fun _ _ _ _ h => by
          dsimp only [Spec.inImage, rustAllocSpecWithStack] at h
          exact (not_satisfies_false_sepConj h).elim)
        (fun _ _ h => by
          dsimp only [Spec.inImage, rustAllocSpecWithStack] at h; simp only [sepConj_assoc] at h
          exact (not_satisfies_false_sepConj h).elim)
        (fun sd hpcd hrund hspd hcsd hinv_sd => ?_)
      · intro R' hm
        dsimp only [Spec.inImage, rustAllocSpecWithStack]; rw [hspc]
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
        exact ⟨hinv_sc, ⟨by rw [hx0c]; exact htoNat_len, by rw [hx1c]; rfl, hlay⟩,
          by simpa [sepConj_assoc] using Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
      · dsimp only [Spec.inImage, rustAllocSpecWithStack]; rw [hspc]
        have hsp_d : sd.sp = s0.sp - 496#64 := hspd.trans hspc
        by_cases hoom : sd.readReg64 .x0 = 0#64
        · have hzero : sd.readReg64 .x0 = 0 := hoom
          conv => arg 4; simp only [hzero, ↓reduceIte]
          have hpull_oom :
              (A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗
                ⌜sd.trace = sc.trace ++ [allocFailedEvent]⌝) ∗
              ((x.akPtr ↦ₛ x.p.authKey) ∗ Frame) =
              ⌜sd.trace = sc.trace ++ [allocFailedEvent]⌝ ∗
              (A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗
                (x.akPtr ↦ₛ x.p.authKey) ∗ Frame) := by ac_rfl
          rw [hpull_oom]
          refine SepWPp.pure_left fun htr_oom => ?_
          have hstepOom : SepWP prog (fn + 196#64) sd
              (A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ Frame)
              (fun se Pe =>
                (Pe ⊢ A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗
                  (x.akPtr ↦ₛ x.p.authKey) ∗ Frame) ∧
                se.trace = s0.trace ++ [allocFailedEvent]) := by
            have htr_d : sd.trace = s0.trace ++ [allocFailedEvent] := by rw [htr_oom, htrc]
            initial_state_fetches_range img.base (Rust.withPanics ext) 256 4
            dsimp only [prog, fn, tripleRatchetProgAtExt, initialStateName,
              Reg.x0, BitVec.ofNat_eq_ofNat] at hpcd hoom ⊢
            generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
              "spqr::initial_state" = entry
            examples_hide_fetches; wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
          refine initInner_seq_sepWP hstepOom fun se hpce hrune _ htre => ?_
          exact initial_state_panic_196 s0 se _ R hpce hrune htre
        · have hne_zero : sd.readReg64 .x0 ≠ 0 := hoom
          have hoom_beq : (sd.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
          have hoom_bne : (sd.readReg64 .x0 != 0#64) = true := bne_iff_ne.mpr hoom
          conv => arg 4; simp only [hne_zero, ↓reduceIte]
          let ptr_c := sd.readReg64 .x0
          have hpull_ok :
              (A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗
                (⌜ptr_c.toNat % 1 = 0 ∧ sd.trace = sc.trace⌝ ∗
                  A.live ptr_c x.p.authKey.length 1 ∗ memRegion ptr_c x.p.authKey.length)) ∗
              ((x.akPtr ↦ₛ x.p.authKey) ∗ Frame) =
              ⌜ptr_c.toNat % 1 = 0 ∧ sd.trace = sc.trace⌝ ∗
              (memRegion ptr_c x.p.authKey.length ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
                stackAt (s0.sp - 496#64) extHookStack ∗
                A.pool ∗ A.live ptr_c x.p.authKey.length 1 ∗ Frame) := by ac_rfl
          rw [hpull_ok]
          refine SepWPp.pure_left fun ⟨_, htrd⟩ => ?_
          obtain ⟨hx19d, hx20d, hx21d, hx22d, _, _, hx25d, _, _, _, hx29d⟩ := hcsd
          have hstepC : SepWP prog
              (fn + bv% (ls_rel% "spqr::initial_state" "memcpy")) sd
              (memRegion ptr_c x.p.authKey.length ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
                stackAt (s0.sp - 496#64) extHookStack ∗
                A.pool ∗ A.live ptr_c x.p.authKey.length 1 ∗ Frame)
              (fun se Pe =>
                (Pe ⊢ (memRegion ptr_c x.p.authKey.length ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
                  stackAt (s0.sp - 496#64) extHookStack) ∗
                  (A.pool ∗ A.live ptr_c x.p.authKey.length 1 ∗ Frame)) ∧
                se.sp = s0.sp - 496#64 ∧ se.readReg64 .x30 = fn + 276#64 ∧
                se.readReg64 .x0 = ptr_c ∧ se.readReg64 .x1 = x.akPtr ∧
                se.readReg64 .x2 = BitVec.ofNat 64 x.p.authKey.length ∧
                se.readReg64 .x29 = s0.sp - 96#64 ∧ se.readReg64 .x19 = x.ret ∧
                se.readReg64 .x20 = x.pA ∧ se.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
                se.readReg64 .x22 = x.akPtr ∧ se.readReg64 .x23 = ptr_c ∧
                se.readReg32 .x25 = 1#32 ∧ se.trace = s0.trace ∧
                calleeSavedVRegs se = calleeSavedVRegs s0) := by
            have hx29_d : sd.readReg64 .x29 = s0.sp - 96#64 := hx29d.1.trans hx29c
            have hx19_d : sd.readReg64 .x19 = x.ret := hx19d.trans hx19c
            have hx20_d : sd.readReg64 .x20 = x.pA := hx20d.trans hx20c
            have hx21_d : sd.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length := hx21d.trans hx21c
            have hx22_d : sd.readReg64 .x22 = x.akPtr := hx22d.trans hx22c
            have hw25_d : sd.readReg32 .x25 = 1#32 := (readReg32_of_eq hx25d).trans hw25c
            have htr_d : sd.trace = s0.trace := htrd.trans htrc
            have hvregs_d : calleeSavedVRegs sd = calleeSavedVRegs s0 := hx29d.2.trans hvregsc
            have hx0_d : sd.readReg64 .x0 = ptr_c := rfl
            initial_state_fetches_range img.base (Rust.withPanics ext) 256 20
            dsimp only [prog, fn, tripleRatchetProgAtExt, initialStateName,
              State.readReg32, Reg.x0, Reg.x25, BitVec.ofNat_eq_ofNat]
              at hpcd hx0_d hoom_beq hoom_bne hw25_d ⊢
            generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
              "spqr::initial_state" = entry
            examples_hide_fetches; wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
          refine initInner_seq_sepWP hstepC fun se hpce hrune hinve
            ⟨hspe, hlre, hx0e, hx1e, hx2e, hx29e, hx19e, hx20e, hx21e, hx22e, hx23e, hw25e, htre, hvregse⟩ => ?_
          have hinv_se : ImgCallInv img se := hinve img hinv_sd
          refine sepWPp_call_inImage hmemcpy (x := (ptr_c, x.akPtr, x.p.authKey))
            (F := A.pool ∗ A.live ptr_c x.p.authKey.length 1 ∗ Frame) hinv_se
            (by simpa only [prog, fn, BitVec.ofNat_eq_ofNat] using hpce) hrune
            (by rw [State.spAligned, hspe]; exact hfsp_align) hlre ?_
            (fun _ _ _ _ h => by
              dsimp only [Spec.inImage, sessionMemcpySpec, libcMemcpySpec] at h
              exact (not_satisfies_false_sepConj h).elim)
            (fun _ _ h => by
              dsimp only [Spec.inImage, sessionMemcpySpec, libcMemcpySpec] at h
              simp only [sepConj_assoc] at h; exact (not_satisfies_false_sepConj h).elim)
            (fun sf hpcf hrunf hspf hcsf hinv_sf => ?_)
          · intro R' hm
            dsimp only [Spec.inImage, sessionMemcpySpec, libcMemcpySpec]; rw [hspe]
            simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
            exact ⟨hinv_se, ⟨hx0e, hx1e, by rw [hx2e]; exact htoNat_len⟩,
              by simpa [sepConj_assoc] using Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
          · dsimp only [Spec.inImage, sessionMemcpySpec, libcMemcpySpec]; rw [hspe, sepConj_assoc]
            refine SepWPp.pure_left fun ⟨_, htrf⟩ => ?_
            obtain ⟨hx19f, hx20f, hx21f, hx22f, hx23f, _, hx25f, _, _, _, hx29f⟩ := hcsf
            have hbuf := vecU8Buf_nonempty A ptr_c x.p.authKey hpos hlt hoom
            have hstepD : SepWP prog (fn + 284#64) sf
                (((ptr_c ↦ₛ x.p.authKey) ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
                  stackAt (s0.sp - 496#64) extHookStack) ∗
                  (A.pool ∗ A.live ptr_c x.p.authKey.length 1 ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr_c x.p.authKey ∗
                    (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗ Frame) ∧
                  sm.sp = s0.sp - 496#64 ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧
                  sm.readReg64 .x19 = x.ret ∧ sm.readReg64 .x20 = x.pA ∧
                  sm.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
                  sm.readReg64 .x22 = x.akPtr ∧ sm.readReg64 .x23 = ptr_c ∧
                  sm.readReg32 .x25 = 1#32 ∧ sm.trace = s0.trace ∧
                  calleeSavedVRegs sm = calleeSavedVRegs s0) := by
              have hsp_f : sf.sp = s0.sp - 496#64 := hspf.trans hspe
              have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hx29f.1.trans hx29e
              have hx19_f : sf.readReg64 .x19 = x.ret := hx19f.trans hx19e
              have hx20_f : sf.readReg64 .x20 = x.pA := hx20f.trans hx20e
              have hx21_f : sf.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length := hx21f.trans hx21e
              have hx22_f : sf.readReg64 .x22 = x.akPtr := hx22f.trans hx22e
              have hx23_f : sf.readReg64 .x23 = ptr_c := hx23f.trans hx23e
              have hw25_f : sf.readReg32 .x25 = 1#32 := (readReg32_of_eq hx25f).trans hw25e
              have htr_f : sf.trace = s0.trace := htrf.trans htre
              have hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0 := hx29f.2.trans hvregse
              initial_state_fetches_range img.base (Rust.withPanics ext) 276 4
              dsimp only [prog, fn, tripleRatchetProgAtExt, initialStateName,
                State.readReg32, Reg.x25, BitVec.ofNat_eq_ofNat] at hpcf hw25_f ⊢
              generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
                "spqr::initial_state" = entry
              examples_hide_fetches; wp_steps
              have hent :
                  ((ptr_c ↦ₛ x.p.authKey) ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
                    stackAt (s0.sp - 496#64) extHookStack) ∗
                    (A.pool ∗ A.live ptr_c x.p.authKey.length 1 ∗ Frame) ⊢
                  RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr_c x.p.authKey ∗
                    (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗ Frame := by
                refine Entails.trans (Entails.of_eq (show _ =
                  (A.live ptr_c x.p.authKey.length 1 ∗ (ptr_c ↦ₛ x.p.authKey)) ∗
                  ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) extHookStack ∗ Frame)
                  by ac_rfl)) ?_
                exact sepConj_mono_left hbuf
              exact SepWP.weaken_pre hent (by wp_done)
            refine initInner_seq_sepWP hstepD fun sm hpcm hrunm hinvm
              ⟨hspm, hx29m, hx19m, hx20m, hx21m, hx22m, hx23m, hw25m, htrm, hvregsm⟩ => ?_
            exact hnext sm ptr_c hpcm hrunm (hinvm img hinv_sf) hspm hx29m hx19m hx20m hx21m hx22m hx23m hw25m htrm hvregsm

end CryptoVerification.SpqrV1.Top.InitialState

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.CalleesW
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SepWPpIn
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorFrom.Core
import ProofLib.SepLogic.WPp

/-!
# `<DecodeError as From<DecodeErrorKind>>::from`

Verifies `<DecodeError as From<DecodeErrorKind>>::from` (`0x4ada0`, block `261`) on
`contractProg img.base ext` and under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.WireX
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorFrom
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_DecodeErrorFromX : True := trivial

/-! ## Stack helpers -/

/-- `decodeErrorHookStackW = (0x20 + 16384) + 8160`: split off the 8160-byte slack at the bottom. -/
theorem stackAt_decodeErrorFromX_slack (sp : BitVec 64) :
    stackAt sp decodeErrorHookStackW =
      memRegion (sp - BitVec.ofNat 64 decodeErrorHookStackW) 8160 ∗ stackAt sp (0x20 + 16384) :=
  ProofLib.stackAt_split_bottom sp (0x20 + 16384) 8160 (by decide)

theorem stackAt_decodeErrorFromX_cells (sp : BitVec 64) :
    stackAt sp (0x20 + 16384) =
      stackAt (sp - 32#64) extHookStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  have h1 := ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)
  change stackAt sp (0x20 + 16384) =
    stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 at h1
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [h1, hc4]

theorem stackAt_decodeErrorFromX_bottom (sp : BitVec 64) :
    stackAt sp (0x20 + 16384) =
      memRegion (sp - BitVec.ofNat 64 (0x20 + 16384)) 32 ∗ stackAt sp extHookStack :=
  ProofLib.stackAt_split_bottom sp extHookStack 32 (by decide)

theorem stackAt_decodeErrorFromX_tail (sp v0 v1 v2 v3 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      stackAt sp (0x20 + 16384) := by
  rw [stackAt_decodeErrorFromX_cells]
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

theorem stackAt_decodeErrorFromX_recombine (sp v0 v1 v2 v3 : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 decodeErrorHookStackW) 8160 ∗
      stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      stackAt sp decodeErrorHookStackW := by
  rw [stackAt_decodeErrorFromX_slack]
  refine sepConj_mono_right ?_
  exact stackAt_decodeErrorFromX_tail sp v0 v1 v2 v3

/-- Any call to `alloc::alloc::handle_alloc_error` panics on `SP2Ext b ext`. -/
theorem panic_at_handle_alloc_error_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {k : Nat}
    (hk : num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") + k = num% (ls_off% "alloc::alloc::handle_alloc_error") := by decide) :
    (contractProg b ext).externAt? ((contractProg b ext).fnAddr decodeErrorFromName + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") hk (by decide) (ls_hook% "alloc::alloc::handle_alloc_error")
    (by simp [Rust.isPanicSymbol])

/-! ## Main proof -/

theorem decodeErrorFrom_okW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    DecodeErrorFromOkW img A ext := by
  unfold DecodeErrorFromOkW Spec.inImage decodeErrorFromSpecX
  simp only [stackAt_decodeErrorFromX_slack, stackAt_decodeErrorFromX_cells,
    sepExists_sepConj_right]
  have hshim := hA.shim_ok_at decodeErrorFromName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
    (by simp only [decodeErrorFromName, (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"), arm64_norm])
  have halloc := hA.alloc_ok_at decodeErrorFromName
    (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
    (by simp only [decodeErrorFromName, (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"), arm64_norm])
  have hpanic := panic_at_handle_alloc_error_ext (b := img.base) (ext := ext)
    (k := num% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff decodeErrorFromName = num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") :=
    (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")
  code_fetches CryptoVerification.libsignalSessionCode
    libsignalSessionBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")) 92
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨k, w⟩ := x
  dsimp only at *
  have hpow2 : ∃ j, 8 = 2 ^ j := ⟨3, rfl⟩
  have hlay : LayoutOk 72 8 := ⟨by decide, hpow2, by decide⟩
  have hinv0 : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s0 := ⟨h_2, h_1⟩
  apply _root_.ProofLib.SepWPp.of_sepWP_inImage (mid := entry + bv% (20)) hinv0
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF1, hsym1⟩
  wp_call hshim ()
  apply SepWP.done hpc_sf hrun_sf
  rintro hinv2
  apply SepWPp.of_sepWP (mid := entry + bv% (32))
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")) hinv2
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_call halloc (72, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true]
    refine SepWPp.pure_elim fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_40_cells (k + 8#64), memRegion_72_cells,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun k0 => SepWPp.exists_elim fun k1 =>
      SepWPp.exists_elim fun k2 => SepWPp.exists_elim fun k3 =>
      SepWPp.exists_elim fun k4 =>
      SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
      SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 =>
      SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u7 =>
      SepWPp.exists_elim fun u8 => ?_
    refine SepWPp.pure_elim fun ⟨hmod, htrace⟩ => ?_
    have htr0 : sf_1.trace = s0.trace := htrace.trans hpost
    apply SepWPp.of_sepWP_ret
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    apply SepWP.fold (decodeErrorWith_zero_entails A _ w _ _ _ _ _ ‹KindNoHeap w›) (by sep_frame)
    apply SepWP.fold (cells6_entails_memRegion48 k w _ _ _ _ _) (by sep_frame)
    rw [hsp_sf]
    wp_done

/-! ## Relocatable `[LibsignalPlacement]` Proofs (Block `261`) -/

section Placed

private theorem of_sepWP_lscl {pl : Obj.MultiPlacement} {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  (Proofs.libsignal.Hooks2.SepWPpLsCl.of_sepWP h) hcl

/-- Relocatable `<DecodeError as From<DecodeErrorKind>>::from` (Block `261`) meets
`DecodeErrorFromPlacedOkW A H` under `Stage1X.AllocContractsPlaced A H`. -/
theorem decodeErrorFrom_placed_okW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    DecodeErrorFromPlacedOkW A H := by
  have hpanic : ((blkPC_261).rebase (blkPl_261).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") = some Rust.panicked :=
    hA.externAt_handle_alloc_error
  unfold DecodeErrorFromPlacedOkW withLsCodeLoaded decodeErrorFromSpecX
  simp only [stackAt_decodeErrorFromX_slack, stackAt_decodeErrorFromX_cells, sepExists_sepConj_right]
  wpp_init x s0
  obtain ⟨k, w⟩ := x
  dsimp only at *
  have hpow2 : ∃ j, 8 = 2 ^ j := ⟨3, rfl⟩
  have hlay : LayoutOk 72 8 := ⟨by decide, hpow2, by decide⟩
  apply of_sepWP_lscl (mid := lsρ lsRustNoAllocShimSym) ‹_›
  wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl1
  apply of_sepWP_lscl (mid := lsρ lsRustAllocSym) hcl1
  have hshim_call := lscall_of_withLsCl (hA.shim (callerProg := (blkPC_261).rebase (blkPl_261).base H)) hcl1
  wp_call hshim_call ()
  wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl2
  have halloc_call := lscall_of_withLsCl (hA.alloc (callerProg := (blkPC_261).rebase (blkPl_261).base H)) hcl2
  wpp_call halloc_call (x := (72, 8))
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · simp only [hoom, ite_true]
    refine SepWPp.pure_elim fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error")
    wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using allowPanic_panicked
      (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · simp only [hoom, ite_false, memRegion_40_cells (k + 8#64), memRegion_72_cells,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun k0 => SepWPp.exists_elim fun k1 =>
      SepWPp.exists_elim fun k2 => SepWPp.exists_elim fun k3 =>
      SepWPp.exists_elim fun k4 =>
      SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
      SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 =>
      SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u7 =>
      SepWPp.exists_elim fun u8 => ?_
    refine SepWPp.pure_elim fun ⟨hmod, htrace⟩ => ?_
    have htr0 : sf_1.trace = s0.trace := by simp only [wp_norm, arm64_norm, *]
    apply SepWPp.of_sepWP_ret
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    apply SepWP.fold (decodeErrorWith_zero_entails A _ w _ _ _ _ _ ‹KindNoHeap w›) (by sep_frame)
    apply SepWP.fold (cells6_entails_memRegion48 k w _ _ _ _ _) (by sep_frame)
    rw [hsp_sf]
    wp_done

end Placed

end CryptoVerification.LibsignalTripleRatchet.Prost.X

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExt
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowExt
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofExt
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1Sent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProof
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorFrom.Core
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.GrowOne
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.Slow
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# 4K-Contract Companion for `spqr::decode_state` (`DecodeStateOkX`)

Lifts all callees of `spqr::decode_state` (`DecodeError::from`, `DecodeError::push`,
`decode_varint_slow`, `decode_varint [local#2]`, `skip_field [local#3]`,
`ChainParams::merge`, `EpochDirection::merge`, `PolynomialEncoder::merge`,
`PolynomialDecoder::merge`, and `V1State::merge`) from zero-stack `Stage2Contracts`
to `SpqrV1.Alloc.AllocContracts4K` + `SpqrHooks` (`4,096`-byte hook stack).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

section DecodeError4K

open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorFrom
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush
open BS31

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_realloc")
  (ls_stub% "alloc::alloc::handle_alloc_error")
  (ls_stub% "alloc::raw_vec::handle_error")

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `<prost::error::DecodeError as From<DecodeErrorKind>>::from` on `tripleRatchetProgAtExt b ext`
under `AllocContracts4K b A ext` (`decodeErrorHookStack = 4,288`B). -/
theorem decodeErrorFrom_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A) := by
  simp only [decodeErrorFromSpec, stackAt_decodeErrorFrom]
  cells_unfold
  have hshim := hA.shim_ok_at decodeErrorFromName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
  have halloc := hA.alloc_ok_at decodeErrorFromName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
  have hpanic := panic_at_handle_alloc_error_ext b ext decodeErrorFromName
    (num% (ls_off% "alloc::alloc::handle_alloc_error" -
      ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
  clear hA
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff decodeErrorFromName =
      num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") :=
    ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorFrom.libsignalSessionBin b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")) 92
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decodeErrorFromName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr decodeErrorFromName = entry
  examples_hide_fetches
  obtain ⟨k, w⟩ := x
  dsimp only at *
  have hpow2 : ∃ j, 8 = 2 ^ j := ⟨3, rfl⟩
  have hlay : LayoutOk 72 8 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (32))
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" -
        ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_eq
          (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›])) hm
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
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    apply SepWP.fold (decodeErrorWith_zero_entails A _ w _ _ _ _ _ ‹KindNoHeap w›) (by sep_focus)
    apply SepWP.fold (cells6_entails_memRegion48 k w _ _ _ _ _) (by sep_focus)
    wp_done

private theorem realloc_uninit_ok_at_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustReallocUninitSpec A) := by
  refine subroutine_ok.of_codeLoaded fun ⟨p, old, align, new⟩ R s0 hpc hrun hpre hsp _ => ?_
  have hpre' : s0.mem ⊨ (rustReallocSpec A).pre (p, old, align, new, []) s0 ∗ R := by
    simp only [rustReallocSpec, rustReallocUninitSpec, List.length_nil, Nat.zero_le,
      and_true, pointsToBytes_nil, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero,
      emp_sepConj, sepConj_assoc] at hpre ⊢
    exact hpre
  refine (hA.realloc_ok_at name k hk).mono_outcome (p, old, align, new, []) R s0 hpc hrun
    hpre' hsp fun sf hout => ?_
  simpa only [SubroutineOutcome, rustReallocSpec, rustReallocUninitSpec, List.length_nil,
    pointsToBytes_nil, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero,
    emp_sepConj, sepConj_assoc] using hout

private theorem finish_grow_7_zero_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow7Name)
      (finishGrow7ZeroSpec A) := by
  unfold finishGrow7ZeroSpec
  cells_unfold
  have hfn := ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]"
  have hshim := hA.shim_ok_at finishGrow7Name
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := hA.alloc_ok_at finishGrow7Name
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.libsignalSessionBin b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]")) 164
  dsimp only [tripleRatchetProgAtExt, finishGrow7Name] at hshim halloc ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨out, cap, ptr, new, o0, o1, o2, fsp⟩ := x
  dsimp only at *
  have hnew_pos : 0 < new.toNat := by assumption
  subst fsp
  subst cap
  have hlsr59 := lsr59_eq_zero (new := new) (by omega)
  have hhi := hi_32_eq_false (new := new) (by omega)
  have hcbz := beq_lsl5_zero_eq_false hnew_pos (by omega)
  have hlsl : (new <<< 5).toNat = new.toNat * 32 := lsl5_toNat (by omega)
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk (new.toNat * 32) 8 := ⟨by omega, hpow8, by omega⟩
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 0#64
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 1#64
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 8#64
    simp only [ite_true]
    wp_done

private theorem finish_grow_7_ne_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrow7Name)
      (finishGrow7NeSpec A) := by
  unfold finishGrow7NeSpec
  cells_unfold
  have hfn := ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]"
  have hrealloc := realloc_uninit_ok_at_4k hA finishGrow7Name
    (num% (ls_off% "__rustc::__rust_realloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_realloc")])
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.libsignalSessionBin b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]")) 164
  dsimp only [tripleRatchetProgAtExt, finishGrow7Name] at hrealloc ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨out, cap, ptr, new, o0, o1, o2, fsp⟩ := x
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  subst fsp
  have hlsr59 := lsr59_eq_zero (new := new) (by omega)
  have hhi := hi_32_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hlsl_cap : (cap <<< 5).toNat = cap.toNat * 32 := lsl5_toNat (by omega)
  have hlsl_new : (new <<< 5).toNat = new.toNat * 32 := lsl5_toNat (by omega)
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk (new.toNat * 32) 8 := ⟨by omega, hpow8, by omega⟩
  wp_steps
  wp_apply
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 0#64
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 1#64
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 8#64
    simp only [ite_true]
    wp_done

private theorem grow_amortized_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growAmortizedName)
      (growAmortizedSpec A) := by
  unfold growAmortizedSpec
  have hc8 : ∀ gsp : BitVec 64, cells (gsp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((gsp - 64#64) ↦₆₄ v0) ∗ ((gsp - 56#64) ↦₆₄ v1) ∗ ((gsp - 48#64) ↦₆₄ v2) ∗
        ((gsp - 40#64) ↦₆₄ v3) ∗ ((gsp - 32#64) ↦₆₄ v4) ∗ ((gsp - 24#64) ↦₆₄ v5) ∗
        ((gsp - 16#64) ↦₆₄ v6) ∗ ((gsp - 8#64) ↦₆₄ v7)) := by
    intro gsp; cells_unfold
  simp only [hc8]
  clear hc8
  have hfn := ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::grow_amortized"
  have hfg0 := finish_grow_7_zero_ok_4k hA
  have hfg1 := finish_grow_7_ne_ok_4k hA
  rw [fnAddr_back_164 (name := "<alloc::raw_vec::RawVecInner>::grow_amortized")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]") (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.libsignalSessionBin b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner>::grow_amortized")) 124
  dsimp only [tripleRatchetProgAtExt, growAmortizedName] at hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<alloc::raw_vec::RawVecInner>::grow_amortized" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨v, cap, ptr, gsp⟩ := x
  dsimp only at *
  have hcap_lt : cap.toNat < 2 ^ 32 := by assumption
  subst gsp
  have hnew_eq := grow_amortized_new_eq hcap_lt
  have hnew_toNat : (newCap cap).toNat = max (2 * cap.toNat) 4 := newCap_toNat hcap_lt
  have hnew_pos : 0 < (newCap cap).toNat := by omega
  have hnew_bound : (newCap cap).toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    wp_steps
    wp_apply
    by_cases htag : w = 1#64
    · subst htag
      wp_simp_pre [ite_true, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw1, htrace⟩
      subst hw1
      wp_steps
      apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 8#64
      apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 0#64
      simp only [(by decide : (8#64 : BitVec 64) = 0xffffffffffffffff#64 ↔ False), ite_false]
      wp_done
    · wp_simp_pre [htag, ite_false, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw0, hp', htrace⟩
      subst hw0
      wp_steps
      apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 0xffffffffffffffff#64
      apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists w_1
      simp only [ite_true, (by decide : newCap 0#64 = 4#64)]
      wp_done
  · wp_simp_pre [hcap0, ite_false]
    have hcap_bound : cap.toNat * 32 < 2 ^ 63 := by omega
    wp_steps
    wp_apply
    by_cases htag : w = 1#64
    · subst htag
      wp_simp_pre [ite_true, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw1, htrace⟩
      subst hw1
      wp_steps
      apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 8#64
      apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 0#64
      simp only [(by decide : (8#64 : BitVec 64) = 0xffffffffffffffff#64 ↔ False), hcap0, ite_false]
      wp_done
    · wp_simp_pre [htag, ite_false, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw0, hp', htrace⟩
      subst hw0
      wp_steps
      apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists 0xffffffffffffffff#64
      apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists w_1
      simp only [ite_true]
      wp_done

private theorem grow_one_str_pair_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr growOneStrPairName)
      (growOneStrPairSpec A) := by
  unfold growOneStrPairSpec
  have hc2 : ∀ osp : BitVec 64, cells (osp - 16#64) 2 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((osp - 16#64) ↦₆₄ v0) ∗ ((osp - 8#64) ↦₆₄ v1)) := by
    intro osp; cells_unfold
  simp only [hc2]
  clear hc2
  have hfn := ls_lemma% fnOff "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one"
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := growOneStrPairName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hga := grow_amortized_ok_4k hA
  rw [Program.fnAddr_rel (name := "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::grow_amortized") (k := 200) (by decide)] at hga
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.libsignalSessionBin b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one")) 36
  dsimp only [tripleRatchetProgAtExt, growOneStrPairName] at hpanic hga ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, osp⟩ := x
  dsimp only at *
  subst osp
  apply SepWPp.of_sepWP (mid := entry + bv% (16))
  wp_steps
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hres : w = 0xffffffffffffffff#64
  · conv => arg 4; simp only [hres, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0, hp', htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists w_1
    wp_done
  · conv => arg 4; simp only [hres, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw8, hx0, htrace⟩ => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
        ls_off% "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_eq
          (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm

/-- `<prost::error::DecodeError>::push` on `tripleRatchetProgAtExt b ext`
under `AllocContracts4K b A ext` (`decodeErrorHookStack = 4,288`B). -/
theorem decodeErrorPush_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A) := by
  unfold decodeErrorPushSpec decodeErrorAtStackLen vecOf vecAt vecHeader vecBuf
  simp only [List.length_replicate, sepExists_sepConj_left, sepExists_sepConj_right]
  simp only [stackAt_push]
  have hfn := ls_lemma% fnOff "<prost::error::DecodeError>::push"
  have hgrow := grow_one_str_pair_ok_4k hA
  rw [Program.fnAddr_rel (name := "<prost::error::DecodeError>::push")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one") (k := 128) (by decide)] at hgrow
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.libsignalSessionBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<prost::error::DecodeError>::push")) 128
  dsimp only [tripleRatchetProgAtExt, decodeErrorPushName, growOneStrPairName] at hgrow ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<prost::error::DecodeError>::push" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨d, e, n⟩ := x
  dsimp only at *
  have hn_lt32 : n < 2 ^ 32 := by assumption
  have hptr_ne0 : v_stk_2 ≠ 0#64 := by assumption
  obtain ⟨hkind1, hkind2⟩ : KindNoHeap v_stk := by assumption
  have hn_toNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  conv =>
    arg 4
    simp only [BitVec.ofNat_eq_ofNat,
      vecBuf_stackEntryAt_memRegion A n v_stk_1 v_stk_2 (by omega) (by omega)]
  by_cases heq : BitVec.ofNat 64 n = v_stk_1
  · subst v_stk_1
    have hcap_lt : (BitVec.ofNat 64 n).toNat < 2 ^ 32 := by rw [hn_toNat]; exact hn_lt32
    have hnew_toNat : (newCap (BitVec.ofNat 64 n)).toNat = max (2 * n) 4 := by
      rw [newCap_toNat hcap_lt, hn_toNat]
    have hn_lt_new : n < (newCap (BitVec.ofNat 64 n)).toNat := by omega
    have hn1_le_new : n + 1 ≤ (newCap (BitVec.ofNat 64 n)).toNat := by omega
    have hnew_bound : (newCap (BitVec.ofNat 64 n)).toNat * 32 < 2 ^ 63 := by omega
    have hnew_ne0 : newCap (BitVec.ofNat 64 n) ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      change (newCap (BitVec.ofNat 64 n)).toNat = 0 at ht
      omega
    apply SepWPp.of_sepWP (mid := entry + bv% (128))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.call_frame (ret_pc := entry + bv% (108))
      (x := (e, BitVec.ofNat 64 n, v_stk_2, s0.sp - 64#64))
      hgrow (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) rfl
      ⟨by wp_norm_goal, by wp_norm_goal, hcap_lt, hptr_ne0⟩
      (by
        simp only [bv_sub_64_sub]
        sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sf _ hm => allowPanic_frame id hm)
      (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    rcases hcs_sf with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
    simp only [wp_norm, arm64_norm] at hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hsp_sf
    conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc, bv_sub_64_sub]
    apply SepWPp.exists_elim; intro p'
    refine SepWPp.pure_elim fun ⟨hp', htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_simp_pre [memRegion_split_entry p' n (newCap (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists v_stk
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists (newCap (BitVec.ofNat 64 n))
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists p'
    simp only [BitVec.ofNat_eq_ofNat, hnew_ne0, ite_false,
      vecBuf_stackEntryAt_memRegion A (n + 1) (newCap (BitVec.ofNat 64 n)) p' hn1_le_new hnew_bound,
      memRegion_split_entry p' n (newCap (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound]
    wp_done
  · have hbeq : (BitVec.ofNat 64 n == v_stk_1) = false := beq_eq_false_iff_ne.mpr heq
    have hne_nat : n ≠ v_stk_1.toNat := by
      intro hnat
      apply heq
      apply BitVec.eq_of_toNat_eq
      rw [hn_toNat, hnat]
    have hn_lt_cap : n < v_stk_1.toNat := by omega
    have hn1_le_cap : n + 1 ≤ v_stk_1.toNat := by omega
    have hcap_ne0 : v_stk_1 ≠ 0#64 := by
      intro h0
      subst h0
      change n < 0 at hn_lt_cap
      omega
    apply SepWPp.of_sepWP_ret
    wp_simp_pre [hcap_ne0, ite_false,
      memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega),
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists v_stk
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists v_stk_1
    apply CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.SepWP.instantiate_post_exists v_stk_2
    simp only [BitVec.ofNat_eq_ofNat, hcap_ne0, ite_false,
      vecBuf_stackEntryAt_memRegion A (n + 1) v_stk_1 v_stk_2 hn1_le_cap (by omega),
      memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega)]
    wp_done

end DecodeError4K

/-- `prost::encoding::varint::decode_varint_slow::<&mut &[u8]>` on `tripleRatchetProgAtExt b ext`
under `AllocContracts4K b A ext`. -/
theorem decodeVarintSlow_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr varintSlowName)
      (Prost.decodeVarintSlowSpec A) :=
  Prost.decodeVarintSlow_ok_of_session2
    (CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow.decodeVarintSlow_ok_F
      b A ext (decodeErrorFrom_ok_4k hA))

/-- `prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]` on
`tripleRatchetProgAtExt b ext` under `AllocContracts4K b A ext`. -/
theorem decodeVarint2_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    Varint.DecodeVarint2OkExt b A ext := by
  refine Varint.decodeVarint2_ok_of_contracts ?_ ?_
  · rw [Varint.decodeVarint2_add_from_eq_fnAddr]
    exact decodeErrorFrom_ok_4k hA
  · exact Prost.decodeVarintSlow_ok_at_of_contract Varint.decodeVarint2_fnOff
      (k := num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" -
        ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]"))
      (by decide)
      (decodeVarintSlow_ok_4k hA)

/-- `prost::encoding::skip_field::<&mut &[u8]> [local#3]` on `tripleRatchetProgAtExt b ext`
under `AllocContracts4K b A ext`. -/
theorem skipField3_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr skipField3Name)
      (skipField3Spec A) := by
  rw [skipField3Name_eq]
  refine Varint.skipField3_ok_of_contracts ?_ (decodeVarint2_ok_4k hA)
  rw [Varint.skipField3_add_from_eq_fnAddr]
  exact decodeErrorFrom_ok_4k hA

/-- `ChainParams::merge` on `tripleRatchetProgAtExt b ext` under `AllocContracts4K b A ext`. -/
theorem chainParamsMerge_canonical_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainParamsMergeName)
      (chainParamsMergeSpec A) := by
  have hok : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Prost.MessageMerge.chainParamsMergeName)
      (Prost.MessageMerge.chainParamsMergeSpec A) := by
    refine Prost.MessageMerge.chainParamsMerge_ok_of_contracts ?_ ?_ ?_ ?_
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.chainParamsMergeName)
        (callee := decodeErrorFromName)]
      exact decodeErrorFrom_ok_4k hA
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.chainParamsMergeName)
        (callee := decodeErrorPushName)]
      exact decodeErrorPush_ok_4k hA
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.chainParamsMergeName)
        (callee := Varint.decodeVarint2Name)]
      exact decodeVarint2_ok_4k hA
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.chainParamsMergeName)
        (callee := Varint.skipField3Name)]
      rw [← skipField3Name_eq]
      exact skipField3_ok_4k hA
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let x' : Prost.MessageMerge.ChainParamsMergeGhost :=
    ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  refine hok.mono_outcome x' R s0 hpc hrun hpre halign fun _ hout => ?_
  exact hout

/-- `EpochDirection::merge` on `tripleRatchetProgAtExt img.base ext` under
`AllocContracts4K img.base A ext` and `bytesMerge3`. -/
theorem epochDirectionMerge_canonical_ok_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr epochDirectionMergeName)
      ((epochDirectionMergeSpec A).inImage img) := by
  have hok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Prost.MessageMerge.epochDirectionMergeName)
      ((Prost.MessageMerge.epochDirectionMergeSpec A).inImage img) := by
    refine Prost.MessageMerge.epochDirectionMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.epochDirectionMergeName)
        (callee := decodeErrorFromName)]
      exact decodeErrorFrom_ok_4k hA
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.epochDirectionMergeName)
        (callee := decodeErrorPushName)]
      exact decodeErrorPush_ok_4k hA
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.epochDirectionMergeName)
        (callee := Varint.decodeVarint2Name)]
      exact decodeVarint2_ok_4k hA
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.epochDirectionMergeName)
        (callee := Varint.skipField3Name)]
      rw [← skipField3Name_eq]
      exact skipField3_ok_4k hA
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.epochDirectionMergeName)
        (callee := bytesMerge3Name)]
      exact hBytes
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let x' : Prost.MessageMerge.EpochDirectionMergeGhost :=
    ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  refine hok.mono_outcome x' R s0 hpc hrun hpre halign fun _ hout => ?_
  exact hout

/-- `PolynomialEncoder::merge` on `tripleRatchetProgAtExt img.base ext` under
`AllocContracts4K img.base A ext`, `bytesMerge3`, and `growOneVecU8`. -/
theorem polyEncoderMerge_ok_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img))
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyEncoderMergeName)
      ((polyEncoderMergeSpec A).inImage img) := by
  refine polyEncoderMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := decodeErrorFromName)]
    exact decodeErrorFrom_ok_4k hA
  · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := decodeErrorPushName)]
    exact decodeErrorPush_ok_4k hA
  · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := Varint.decodeVarint2Name)]
    exact decodeVarint2_ok_4k hA
  · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := Varint.skipField3Name)]
    rw [← skipField3Name_eq]
    exact skipField3_ok_4k hA
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyEncoderMergeName +
        bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]"
          "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name := by
      change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff polyEncoderMergeName)) +
          bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]"
            "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") =
        img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff bytesMerge3Name)
      rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>"),
          (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]")]
      bv_omega
    rw [h_off]; exact hBytes
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyEncoderMergeName +
        bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
          ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name := by
      change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff polyEncoderMergeName)) +
          bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
            ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") =
        img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff growOneVecU8Name)
      rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>"),
          (ls_lemma% fnOff "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one")]
      bv_omega
    rw [h_off]; exact hGrow

/-- `PolynomialDecoder::merge` on `tripleRatchetProgAtExt img.base ext` under
`AllocContracts4K img.base A ext`, `bytesMerge3`, and `growOneVecU8`. -/
theorem polyDecoderMerge_ok_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img))
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName)
      ((polyDecoderMergeSpec A).inImage img) := by
  refine polyDecoderMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := decodeErrorFromName)]
    exact decodeErrorFrom_ok_4k hA
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := decodeErrorPushName)]
    exact decodeErrorPush_ok_4k hA
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := Varint.decodeVarint2Name)]
    exact decodeVarint2_ok_4k hA
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := Varint.skipField3Name)]
    rw [← skipField3Name_eq]
    exact skipField3_ok_4k hA
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName +
        bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]"
          "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name := by
      change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff polyDecoderMergeName)) +
          bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]"
            "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff bytesMerge3Name)
      rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"),
          (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]")]
      bv_omega
    rw [h_off]; exact hBytes
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName +
        bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
          ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name := by
      change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff polyDecoderMergeName)) +
          bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
            ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff growOneVecU8Name)
      rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"),
          (ls_lemma% fnOff "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one")]
      bv_omega
    rw [h_off]; exact hGrow

/-- Canonical verification of `V1State::merge` on `tripleRatchetProgAtExt img.base ext` under
`AllocContracts4K img.base A ext`, `bytesMerge3`, and `growOneVecU8`. -/
theorem v1StateMerge_canonical_ok_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img))
    (hGrowVecU8 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr v1StateMergeName)
      ((Prost.MessageMerge.v1StateMergeSpec A img.base).inImage img) := by
  have hFrom := decodeErrorFrom_ok_4k hA
  have hPush := decodeErrorPush_ok_4k hA
  have hVarint := decodeVarint2_ok_4k hA
  have hSkip : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Varint.skipField3Name)
      (Varint.skipField3Spec A) := by
    rw [← skipField3Name_eq]
    exact skipField3_ok_4k hA
  have hDealloc : CryptoVerification.SpqrV1.Drop.DeallocOkExt img.base A ext := hA.dealloc
  have hAuth : CryptoVerification.SpqrV1.Auth.AuthMergeOkX img A ext :=
    CryptoVerification.SpqrV1.Auth.auth_merge_ok_ext hFrom hPush hVarint hSkip hBytes
  have hAuthPb := CryptoVerification.SpqrV1.Auth.auth_merge_ok_of_fnAddr
    hFrom hPush hVarint hSkip hBytes
  have hUcEk := unchunkedEkSentCt1ReceivedMerge_ok_of_fnAddr hFrom hPush hVarint hSkip hBytes hAuthPb
  have hUcCt1 := unchunkedCt1SentMerge_ok_of_fnAddr hFrom hPush hVarint hSkip hBytes hAuthPb
  have hPolyEnc := polyEncoderMerge_ok_4k hA hBytes hGrowVecU8
  have hPolyDec := polyDecoderMerge_ok_4k hA hBytes hGrowVecU8
  exact v1State_merge_ok_of_fnAddr
    hFrom hPush hVarint hSkip hDealloc
    (CryptoVerification.SpqrV1.Drop.drop_opt_proto_inner_state_ok_ext hDealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_ct1_received_ok_ext hDealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_header_sent_ok_ext hDealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_ek_sent_ct1_received_ok_ext hDealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_no_header_received_ok_ext hDealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_header_received_ok_ext hDealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_unchunked_ct1_sent_ek_received_ok_ext hDealloc)
    (CryptoVerification.SpqrV1.Drop.drop_glue_proto_poly_encoder_ok_ext hDealloc)
    (chunked_keys_unsampled_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth)
    (chunked_keys_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc)
    (chunked_header_sent_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc hPolyDec)
    (chunkedCt1Received_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcEk hPolyEnc)
    (chunkedEkSentCt1Received_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcEk hPolyDec)
    (chunked_no_header_received_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hPolyDec)
    (chunked_header_received_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hBytes hPolyDec)
    (chunkedCt1Sampled_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcCt1 hPolyEnc hPolyDec)
    (chunked_ek_received_ct1_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc)
    (chunkedCt1Acknowledged_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcCt1 hPolyDec)
    (chunked_ct2_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hPolyEnc)

/-- `V1State::merge` under `AllocContracts4K` and `bytesMerge3`. -/
theorem v1StateMerge_canonical_ok_of_hook_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr v1StateMergeName)
      ((Prost.MessageMerge.v1StateMergeSpec A img.base).inImage img) :=
  v1StateMerge_canonical_ok_4k hA hBytes (growOneVecU8_ok_ext_4k img.base A ext hA)

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]` meets
`bytesMerge3RawSpec A` in `img` under `AllocContracts4K img.base A ext`. -/
theorem bytesMerge3_ok_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img) :=
  bytes_merge_3_ok_ext_4k himg hA
    (decodeErrorFrom_ok_4k hA)
    (subroutine_ok_inImage_of_subroutine_ok img (decodeVarint2_ok_4k hA))
    (bytesFromVecOk_ext himg rfl)
    (CryptoVerification.SpqrV1.Alloc.do_reserve_7_ok_ext_4k hA)
    bytesVtableSlotLoaded
    (fun p v => subroutine_ok_inImage_of_subroutine_ok img
      (bytesVtableDrop_base_ok_4k hA p v v.length))

/-- Assemble `DecodeStateCalleeContracts4K canonicalV1InnerHeap b A ext` from
`AllocContracts4K b A ext`. -/
theorem decodeStateCalleeContracts4K_of_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hA : AllocContracts4K b A ext) :
    DecodeStateCalleeContracts4K canonicalV1InnerHeap b A ext :=
  { b_page_aligned := hb
    of_drop_inner := of_drop_inner_canonical A
    of_cap_inner := of_cap_inner_ok A
    alloc := ⟨hA.dealloc, hA.memcpy, hA.session_memcpy⟩
    decodeErrorFrom := decodeErrorFrom_ok_4k hA
    decodeErrorPush := decodeErrorPush_ok_4k hA
    decodeVarint2 := decodeVarint2_ok_4k hA
    skipField3 := skipField3_ok_4k hA
    chainParamsMerge := chainParamsMerge_canonical_ok_4k hA
    growOneChainEpoch := CryptoVerification.SpqrV1.Alloc.grow_one_chain_epoch_full_ok_ext_4k hA
    dropOptProtoInnerState := dropOptProtoInnerState_canonical_ok hb hA.dealloc
    dropProtoPqRatchetState := dropProtoPqRatchetState_canonical_ok hb hA.dealloc }

/-- Assemble `DecodeStateCalleeContractsX4K canonicalV1InnerHeap img img.base A ext` from
`Obj.Loads libsignalSessionImage img` and `AllocContracts4K img.base A ext`. -/
theorem decodeStateCalleeContractsX4K_of_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts4K img.base A ext) :
    DecodeStateCalleeContractsX4K canonicalV1InnerHeap img img.base A ext :=
  let hBytes := bytesMerge3_ok_4k himg hA
  { decodeStateCalleeContracts4K_of_4k (ProofLib.base_aligned_of_loads himg) hA with
    bytesMerge3 := hBytes
    epochDirectionMerge := epochDirectionMerge_canonical_ok_4k hA hBytes
    v1StateMerge := v1StateMerge_canonical_ok_of_hook_4k hA hBytes }

/-- 4K-stack top-level verification of `spqr::decode_state` with `canonicalV1InnerHeap`,
discharging all callees from `Obj.Loads libsignalSessionImage img` and
`AllocContracts4K img.base A ext`. -/
theorem spqr_decode_state_ok_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts4K img.base A ext) :
    DecodeStateOkX canonicalV1InnerHeap img A ext :=
  decodeState_ok_4k (decodeStateCalleeContractsX4K_of_4k himg hA)

end CryptoVerification.SpqrV1.Top.DecodeState

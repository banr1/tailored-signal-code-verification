/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Path.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint DoReserveNorm
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm

/-- Allocate initial heap backing `vecU8RestAt A cap0 ptr0 dir` (`+64 .. +120`, OOM `+40 .. +48`)
with `cap0 = BitVec.ofNat 64 dir.length` and `ptr0 ≠ 0#64`, unifying `dir = []` and `dir ≠ []`. -/
theorem step_to_owned {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk : Nat}
    {s0 s : State} {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret dirA nameA ret_lr : BitVec 64} {dir name : List (BitVec 8)} {dirRo : Bool}
    (hshim : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName +
        BitVec.ofNat 64
          (ls_rel% "libsignal_cli::stores::path" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (withEncRepeatedCS s0 session2ShimSpecX))
    (halloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::path" "__rustc::__rust_alloc"))
      (withEncRepeatedCS s0 (rustAllocSpecWithStack A)))
    (hmc_dir : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::path" "memcpy"))
      (withEncRepeatedCS s0 (session2MemcpyBytesAtSpecX dirRo)))
    (hpanic : (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::path" "alloc::raw_vec::handle_error")) =
      some Rust.panicked)
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64)
    (hdir_lt : dir.length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pathName + BitVec.ofNat 64 64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = dirA)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 dir.length)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗ A.pool ∗
      stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (ptr0 : BitVec 64),
      ptr0 ≠ 0#64 →
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pathName + BitVec.ofNat 64 120 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 name.length →
      sm.readReg64 .x21 = nameA →
      sm.readReg64 .x22 = BitVec.ofNat 64 dir.length →
      sm.readReg64 .x23 = ptr0 →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret_lr sm
        ((vecU8RestAt A (BitVec.ofNat 64 dir.length) ptr0 dir ∗
          SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗ A.pool ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanic A img stk x0 s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret_lr s P Q
      (pathOnPanic A img stk x0 s0 R) := by
  have f40 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 40) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 40))
  have f44 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 44) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 44))
  have f48 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 48) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 48))
  have f64 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 64) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 64))
  have f68 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 68) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 68))
  have f72 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 72) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 72))
  have f76 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 76) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 76))
  have f80 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 80) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 80))
  have f84 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 84) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 84))
  have f88 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 88) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 88))
  have f92 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 92) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 92))
  have f96 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 96) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 96))
  have f100 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 100) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 100))
  have f104 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 104) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 104))
  have f108 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 108) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 108))
  have f112 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 112) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 112))
  have f116 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 116) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 116))
  dsimp only [tripleRatchetProgAtExt] at f40 f44 f48 f64 f68 f72 f76 f80 f84 f88 f92 f96 f100 f104 f108 f112 f116 hpc
  generalize hpEntry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pathName = pEntry
    at f40 f44 f48 f64 f68 f72 f76 f80 f84 f88 f92 f96 f100 f104 f108 f112 f116 hpc
  examples_hide_fetches
  subst hP
  rcases (show dir = [] ∨ 0 < dir.length by cases dir <;> simp) with rfl | hdir_pos
  · apply SepWPp.of_sepWP_cs (mid := pEntry + BitVec.ofNat 64 120)
    dsimp only [tripleRatchetProgAtExt]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    refine SepWPp.weaken_pre ?_
      (hnext _ 1#64 (by decide)
        (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *])))
    simp only [vecU8RestAt, List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  · have hdir_lt64 : dir.length < 2 ^ 64 := by omega
    have hdir_beq0 : (BitVec.ofNat 64 dir.length == 0#64) = false :=
      ofNat_beq_zero_false hdir_pos hdir_lt64
    have hdir_toNat : (BitVec.ofNat 64 dir.length).toNat = dir.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdir_lt64]
    have hlay : LayoutOk dir.length 1 := ⟨hdir_pos, ⟨0, rfl⟩, by omega⟩
    rw [stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt]
    apply SepWPp.of_sepWP_cs
      (mid := pEntry + BitVec.ofNat 64
        (ls_rel% "libsignal_cli::stores::path" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    dsimp only [tripleRatchetProgAtExt]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *])
    intro hinv1
    refine step_shim_call hshim
      (fsp := fsp) (ret_pc := pEntry + BitVec.ofNat 64 84)
      (F := SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗ A.pool ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - extHookStack) ∗ F)
      (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hfsp_align
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *]))
      (by ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hcs1 hcs_s1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, _, hx24_1, _⟩
    simp only [arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx24_1
    apply SepWPp.of_sepWP_cs
      (mid := pEntry + BitVec.ofNat 64
        (ls_rel% "libsignal_cli::stores::path" "__rustc::__rust_alloc"))
    dsimp only [tripleRatchetProgAtExt]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *])
    intro hinv2
    refine step_alloc_call halloc (size := dir.length)
      (fsp := fsp) (ret_pc := pEntry + BitVec.ofNat 64 100)
      (F := SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - extHookStack) ∗ F)
      (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hfsp_align
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]; try rfl) hlay
      (hcs_s1.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *]))
      (by ac_rfl) ?_ ?_
    · intro s2 hpc2 hrun2 hsp2 hoom2 htr2 _ _
      apply SepWPp.of_sepWP
        (mid := pEntry + BitVec.ofNat 64
          (ls_rel% "libsignal_cli::stores::path" "alloc::raw_vec::handle_error"))
      dsimp only [tripleRatchetProgAtExt]
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega)
        (by simp only [arm64_norm, *])
      exact step_handle_error_panic hpanic
        (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *]; try bv_omega)
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
    · intro s2 hpc2 hrun2 hsp2 hptr_ne0 htr2 hcs2 hcs_s2
      rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, _, hx24_2, _⟩
      simp only [arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx24_2
      have hptr_beq0 : (s2.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hptr_ne0
      apply SepWPp.of_sepWP_cs
        (mid := pEntry + BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::path" "memcpy"))
      dsimp only [tripleRatchetProgAtExt]
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega)
        (by simp only [arm64_norm, *])
      intro hinv3
      refine step_memcpy_ro_call hmc_dir
        (dst := s2.readReg64 Reg.x0) (src := dirA) (fsp := fsp)
        (ret_pc := pEntry + BitVec.ofNat 64 120) (bs := dir)
        (F := A.pool ∗ A.live (s2.readReg64 Reg.x0) dir.length 1 ∗
          memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
            (max resStack extHookStack - extHookStack) ∗ F)
        (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *]; try bv_omega)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hfsp_align
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by omega)
        (hcs_s2.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *]))
        (by ac_rfl) ?_
      intro s3 hpc3 hrun3 hsp3 htr3 hcs3 hcs_s3
      rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, _⟩
      simp only [arm64_norm, *] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3
      have hcap0_ne : BitVec.ofNat 64 dir.length ≠ 0#64 := ofNat_ne_zero hdir_pos hdir_lt64
      have hrest_eq :
          A.live (s2.readReg64 Reg.x0) dir.length 1 ∗ ((s2.readReg64 Reg.x0) ↦ₛ dir) =
            vecU8RestAt A (BitVec.ofNat 64 dir.length) (s2.readReg64 Reg.x0) dir := by
        simp only [vecU8RestAt, BitVec.ofNat_eq_ofNat, hcap0_ne, ite_false, hdir_toNat,
          Nat.sub_self, memRegion_zero, sepConj_emp]
      refine SepWPp.weaken_pre ?_
        (hnext s3 (s2.readReg64 Reg.x0) hptr_ne0
          (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *])
          hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hcs_s3)
      rw [stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt, ← hrest_eq]
      exact Entails.of_eq (by ac_rfl)

/-- Reserve space for `'/'` (`+120 .. +180`), write `0x2f#8` at index `dir.length`, and establish
`vecU8At A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8])` at `+180`. -/
theorem step_push_slash {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk : Nat}
    {s0 s : State} {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret nameA ptr0 v1 v2 v3 ret_lr : BitVec 64} {dir name : List (BitVec 8)}
    (hres_rel : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName -
        BitVec.ofNat 64
          (ls_rel%
            "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
            "libsignal_cli::stores::path"))
      (withEncRepeatedCS s0 (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64)
    (hdir_lt : dir.length < 2 ^ 32)
    (hptr0 : ptr0 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pathName + BitVec.ofNat 64 120)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 dir.length)
    (hx23 : s.readReg64 .x23 = ptr0)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
      vecU8RestAt A (BitVec.ofNat 64 dir.length) ptr0 dir ∗ A.pool ∗
      stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      dir.length + 1 ≤ cap1.toNat →
      cap1.toNat < 2 ^ 34 →
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pathName + BitVec.ofNat 64 180 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      sm.readReg64 .x9 = cap1 - BitVec.ofNat 64 (dir.length + 1) →
      sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 name.length →
      sm.readReg64 .x21 = nameA →
      sm.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1) →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret_lr sm
        ((vecU8At A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]) ∗ A.pool ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanic A img stk x0 s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret_lr s P Q
      (pathOnPanic A img stk x0 s0 R) := by
  have f120 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 120) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 120))
  have f124 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 124) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 124))
  have f128 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 128) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 128))
  have f132 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 132) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 132))
  have f136 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 136) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 136))
  have f140 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 140) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 140))
  have f144 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 144) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 144))
  have f148 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 148) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 148))
  have f152 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 152) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 152))
  have f156 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 156) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 156))
  have f160 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 160) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 160))
  have f164 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 164) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 164))
  have f168 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 168) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 168))
  have f172 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 172) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 172))
  have f176 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 176) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 176))
  dsimp only [tripleRatchetProgAtExt] at f120 f124 f128 f132 f136 f140 f144 f148 f152 f156 f160 f164 f168 f172 f176 hpc
  generalize hpEntry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pathName = pEntry
    at f120 f124 f128 f132 f136 f140 f144 f148 f152 f156 f160 f164 f168 f172 f176 hpc
  examples_hide_fetches
  subst hP
  have hdir_lt64 : dir.length < 2 ^ 64 := by omega
  have hdir_toNat : (BitVec.ofNat 64 dir.length).toNat = dir.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdir_lt64]
  rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt]
  apply SepWPp.of_sepWP_cs
    (mid := pEntry - BitVec.ofNat 64
      (ls_rel%
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
        "libsignal_cli::stores::path"))
  dsimp only [tripleRatchetProgAtExt]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; bv_omega) (by simp only [arm64_norm, *])
  intro hinv1
  have hvec0 :
      ((fsp + 8#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        ((fsp + 16#64) ↦₆₄ ptr0) ∗
        ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        vecU8RestAt A (BitVec.ofNat 64 dir.length) ptr0 dir =
      vecU8At A (fsp + 8#64) (BitVec.ofNat 64 dir.length) ptr0 dir := by
    have h0 := vecU8At_of_header_rest A (fsp + 8#64) (BitVec.ofNat 64 dir.length) ptr0 dir
      (by omega) (by omega) hptr0
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h0
  have hbound1 : reserveCap (BitVec.ofNat 64 dir.length).toNat dir.length 1 + 1 ≤ 2 ^ 63 := by
    simp only [reserveCap, hdir_toNat]; omega
  refine step_cli_reserve_call hres_rel hbound1
    (v := fsp + 8#64) (curCap := BitVec.ofNat 64 dir.length) (curPtr := ptr0)
    (fsp := fsp) (ret_pc := pEntry + BitVec.ofNat 64 152) (curBs := dir) (additional := 1)
    (F := memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
      (max resStack extHookStack - resStack) ∗ F)
    (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *]; bv_omega)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hfsp_align
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; try rfl)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *]))
    (by rw [← hvec0]; ac_rfl) ?_
  intro s1 ptr1 hpc1 hrun1 hsp1 htr1 hcs1 hcs_s1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, _⟩
  simp only [arm64_norm, *] at hx19_1 hx20_1 hx21_1
  set cap1 : BitVec 64 := BitVec.ofNat 64 (reserveCap (BitVec.ofNat 64 dir.length).toNat dir.length 1)
  have hcap1_lt34 : cap1.toNat < 2 ^ 34 := by
    simp only [cap1, reserveCap, hdir_toNat, BitVec.toNat_ofNat]
    omega
  have hcap1_ge : dir.length + 1 ≤ cap1.toNat := by
    have hlt64 : reserveCap dir.length dir.length 1 < 2 ^ 64 := by simp only [reserveCap]; omega
    simp only [cap1, hdir_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
    simp only [reserveCap]; omega
  simp only [vecU8At_eq_header_rest A (fsp + 8#64) cap1 ptr1 dir, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hle_v1, hlt_v1, hptr1⟩ => ?_
  have hback1 :
      ((fsp + 8#64) ↦₆₄ cap1) ∗ (((fsp + 8#64) + 8#64) ↦₆₄ ptr1) ∗
        (((fsp + 8#64) + 16#64) ↦₆₄ BitVec.ofNat 64 dir.length) ∗
        vecU8RestAt A cap1 ptr1 dir ∗ A.pool ∗ stackAt fsp resStack ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - resStack) ∗ F =
      vecU8At A (fsp + 8#64) cap1 ptr1 dir ∗ A.pool ∗ stackAt fsp resStack ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - resStack) ∗ F := by
    rw [← vecU8At_of_header_rest A (fsp + 8#64) cap1 ptr1 dir hle_v1 hlt_v1 hptr1]
    ac_rfl
  rw [hback1,
    vecU8At_expose_slice A (fsp + 8#64) cap1 ptr1 dir 1 hcap1_ge (by omega) hptr1 (by decide),
    memRegion_1_eq_pointsTo8]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWPp.exists_elim fun b0 => ?_
  apply SepWPp.of_sepWP_cs (mid := pEntry + BitVec.ofNat 64 180)
  dsimp only [tripleRatchetProgAtExt]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv2
  have hadd1 : BitVec.ofNat 64 dir.length + 1#64 = BitVec.ofNat 64 (dir.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  rw [hadd1] at hinv2
  have hpack1 := vecU8At_pack_slice A (fsp + 8#64) cap1 ptr1 dir [0x2f#8]
    (by simpa using hcap1_ge) (by omega) hptr1 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, List.length_singleton] at hpack1
  refine SepWPp.weaken_pre ?_
    (hnext _ cap1 ptr1 hcap1_ge hcap1_lt34
      (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs_s1.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *])))
  rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt,
    pointsTo8_eq_singleton, ← hpack1]
  exact Entails.of_eq (by ac_rfl)

/-- Copy non-empty `name` into `ptr2 + (dir.length + 1)` via `memcpy` (`+192 .. +212`). -/
theorem step_copy_name {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk : Nat}
    {s0 s : State} {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret nameA cap2 ptr2 ret_lr : BitVec 64} {dir name : List (BitVec 8)} {nameRo : Bool}
    (hmc_name : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::path" "memcpy"))
      (withEncRepeatedCS s0 (session2MemcpyBytesAtSpecX nameRo)))
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64)
    (hname_lt : name.length < 2 ^ 32)
    (hne : name ≠ [])
    (hle : (dir.length + 1) + name.length ≤ cap2.toNat)
    (hcap2 : cap2.toNat < 2 ^ 63)
    (hptr2 : ptr2 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pathName + BitVec.ofNat 64 192)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1))
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8]) ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗
      stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (v_len : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pathName + BitVec.ofNat 64 212 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 name.length →
      sm.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1) →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret_lr sm
        ((((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗ ((fsp + 24#64) ↦₆₄ v_len) ∗
          vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗
          SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanic A img stk x0 s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret_lr s P Q
      (pathOnPanic A img stk x0 s0 R) := by
  have f192 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 192) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 192))
  have f196 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 196) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 196))
  have f200 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 200) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 200))
  have f204 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 204) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 204))
  have f208 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 208) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 208))
  dsimp only [tripleRatchetProgAtExt] at f192 f196 f200 f204 f208 hpc
  generalize hpEntry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pathName = pEntry
    at f192 f196 f200 f204 f208 hpc
  examples_hide_fetches
  subst hP
  have hpos : 0 < name.length := List.length_pos_of_ne_nil hne
  have hname_toNat : (BitVec.ofNat 64 name.length).toNat = name.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen1 : (dir ++ [0x2f#8]).length = dir.length + 1 := by simp
  rw [vecU8At_expose_slice A (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8]) name.length
      (by simpa [hlen1] using hle) hcap2 hptr2 hpos,
    stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, hlen1]
  apply SepWPp.of_sepWP_cs
    (mid := pEntry + BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::path" "memcpy"))
  dsimp only [tripleRatchetProgAtExt]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega)
    (by simp only [arm64_norm, *])
  intro hinv1
  refine step_memcpy_ro_call hmc_name
    (dst := ptr2 + BitVec.ofNat 64 (dir.length + 1)) (src := nameA) (fsp := fsp)
    (ret_pc := pEntry + BitVec.ofNat 64 212) (bs := name)
    (F := ((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗
      ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 (dir.length + 1)) ∗
      A.live ptr2 cap2.toNat 1 ∗ (ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗
      memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
        (cap2.toNat - (dir.length + 1) - name.length) ∗
      memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
        (max resStack extHookStack - extHookStack) ∗ F)
    (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *]; try bv_omega)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hfsp_align
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by omega)
    (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *]))
    (by ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hcsm hcs_s0
  rcases hcsm with ⟨hx19m, hx20m, _, hx22m, _⟩
  simp only [arm64_norm, *] at hx19m hx20m hx22m
  have hcap2_ne : cap2 ≠ 0 := by
    intro h0; subst h0; simp at hle
  have htot_len : (dir ++ [0x2f#8] ++ name).length = dir.length + 1 + name.length := by
    simp; omega
  have htot_bv :
      ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length =
        ptr2 + BitVec.ofNat 64 (dir ++ [0x2f#8] ++ name).length := by
    rw [htot_len, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hrest2 :
      A.live ptr2 cap2.toNat 1 ∗
        ((ptr2 ↦ₛ (dir ++ [0x2f#8])) ∗ ((ptr2 + BitVec.ofNat 64 (dir.length + 1)) ↦ₛ name)) ∗
        memRegion (ptr2 + BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)
          (cap2.toNat - (dir.length + 1) - name.length) =
      vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) := by
    have happ := pointsToBytes_append ptr2 (dir ++ [0x2f#8]) name
    rw [hlen1] at happ
    rw [← happ, htot_bv]
    simp only [vecU8RestAt, hcap2_ne, ite_false, htot_len, Nat.sub_sub]
  refine SepWPp.weaken_pre ?_
    (hnext sm (BitVec.ofNat 64 (dir.length + 1))
      (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *])
      hrunm hspm htrm hx19m hx20m hx22m hcs_s0)
  rw [stackAt_split_ge fsp (Nat.le_max_right resStack extHookStack) hsub_lt, ← hrest2]
  exact Entails.of_eq (by ac_rfl)

/-- Append `name` (`+180 .. +212`, including optional capacity growth at `+260 .. +288`) and join
at `+212`. -/
theorem step_append_name {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk : Nat}
    {s0 s : State} {x0 : PathGhost} {R P F : SepProp} {Q : State → SepProp → Prop}
    {fsp ret nameA cap1 ptr1 ret_lr : BitVec 64} {dir name : List (BitVec 8)} {nameRo : Bool}
    (hres_rel : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName -
        BitVec.ofNat 64
          (ls_rel%
            "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
            "libsignal_cli::stores::path"))
      (withEncRepeatedCS s0 (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hmc_name : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::path" "memcpy"))
      (withEncRepeatedCS s0 (session2MemcpyBytesAtSpecX nameRo)))
    (hsub_lt : max resStack extHookStack ≤ 2 ^ 64)
    (hname_lt : name.length < 2 ^ 32)
    (hcap1_ge : dir.length + 1 ≤ cap1.toNat)
    (hcap1_lt : cap1.toNat < 2 ^ 34)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pathName + BitVec.ofNat 64 180)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hfsp_align : fsp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx9 : s.readReg64 .x9 = cap1 - BitVec.ofNat 64 (dir.length + 1))
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = nameA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1))
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (vecU8At A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]) ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗
      stackAt fsp (max resStack extHookStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 v_len : BitVec 64),
      (dir ++ [0x2f#8] ++ name).length ≤ cap2.toNat →
      cap2.toNat < 2 ^ 63 →
      ptr2 ≠ 0#64 →
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pathName + BitVec.ofNat 64 212 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 name.length →
      sm.readReg64 .x22 = BitVec.ofNat 64 (dir.length + 1) →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret_lr sm
        ((((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗ ((fsp + 24#64) ↦₆₄ v_len) ∗
          vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗
          SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗
          stackAt fsp (max resStack extHookStack)) ∗ F)
        Q (pathOnPanic A img stk x0 s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret_lr s P Q
      (pathOnPanic A img stk x0 s0 R) := by
  have f180 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 180) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 180))
  have f184 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 184) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 184))
  have f188 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 188) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 188))
  have f260 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 260) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 260))
  have f264 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 264) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 264))
  have f268 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 268) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 268))
  have f272 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 272) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 272))
  have f276 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 276) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 276))
  have f280 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 280) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 280))
  have f284 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 284) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 284))
  have f288 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 288) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 288))
  dsimp only [tripleRatchetProgAtExt] at f180 f184 f188 f260 f264 f268 f272 f276 f280 f284 f288 hpc
  generalize hpEntry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pathName = pEntry
    at f180 f184 f188 f260 f264 f268 f272 f276 f280 f284 f288 hpc
  examples_hide_fetches
  subst hP
  have hlen1 : (dir ++ [0x2f#8]).length = dir.length + 1 := by simp
  have hult_iff := elem_len_ult_spare_iff (cap := cap1) (bsLen := dir.length + 1)
    (elemLen := name.length) hcap1_ge (by omega) (by omega)
  by_cases hgrow : (cap1 - BitVec.ofNat 64 (dir.length + 1)).ult (BitVec.ofNat 64 name.length) = true
  · have hlt_cap : cap1.toNat < (dir.length + 1) + name.length := hult_iff.mp hgrow
    have hname_pos : 0 < name.length := by omega
    have hne : name ≠ [] := List.ne_nil_of_length_pos hname_pos
    have hlen1_toNat : (BitVec.ofNat 64 (dir.length + 1)).toNat = dir.length + 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hname_toNat : (BitVec.ofNat 64 name.length).toNat = name.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt]
    apply SepWPp.of_sepWP_cs
      (mid := pEntry - BitVec.ofNat 64
        (ls_rel%
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
          "libsignal_cli::stores::path"))
    dsimp only [tripleRatchetProgAtExt]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; bv_omega) (by simp only [arm64_norm, *])
    intro hinv1
    have hbound2 : reserveCap cap1.toNat (dir ++ [0x2f#8]).length name.length + 1 ≤ 2 ^ 63 := by
      simp only [reserveCap, hlen1]; omega
    refine step_cli_reserve_call hres_rel hbound2
      (v := fsp + 8#64) (curCap := cap1) (curPtr := ptr1)
      (fsp := fsp) (ret_pc := pEntry + BitVec.ofNat 64 284)
      (curBs := dir ++ [0x2f#8]) (additional := name.length)
      (F := SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗
        memRegion (fsp - BitVec.ofNat 64 (max resStack extHookStack))
          (max resStack extHookStack - resStack) ∗ F)
      (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *]; bv_omega)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hfsp_align
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *]))
      (by ac_rfl) ?_
    intro s1 ptr2 hpc1 hrun1 hsp1 htr1 hcs1 hcs_s1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, _⟩
    simp only [arm64_norm, *] at hx19_1 hx20_1 hx21_1
    set cap2 : BitVec 64 := BitVec.ofNat 64 (reserveCap cap1.toNat (dir ++ [0x2f#8]).length name.length)
    have hcap2_lt : cap2.toNat < 2 ^ 63 := by
      simp only [cap2, reserveCap, hlen1, BitVec.toNat_ofNat]; omega
    have hcap2_ge : (dir.length + 1) + name.length ≤ cap2.toNat := by
      have hlt64 : reserveCap cap1.toNat (dir.length + 1) name.length < 2 ^ 64 := by
        simp only [reserveCap]; omega
      simp only [cap2, hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
      simp only [reserveCap]; omega
    simp only [vecU8At_eq_header_rest A (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8]),
      BitVec.add_assoc, BitVec.reduceAdd, hlen1, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hle_v2, hlt_v2, hptr2⟩ => ?_
    apply SepWPp.of_sepWP_cs (mid := pEntry + BitVec.ofNat 64 192)
    dsimp only [tripleRatchetProgAtExt]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *])
    intro hinv2
    refine step_copy_name (ret := ret) (nameA := nameA) hmc_name hsub_lt hname_lt hne
      hcap2_ge hcap2_lt hptr2 (F := A.pool ∗ F)
      (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hfsp_align
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs_s1.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *]))
      (by
        rw [stackAt_split_ge fsp (Nat.le_max_left resStack extHookStack) hsub_lt]
        have hhdr := vecU8At_of_header_rest A (fsp + 8#64) cap2 ptr2 (dir ++ [0x2f#8])
          (by omega) hlt_v2 hptr2
        simp only [BitVec.add_assoc, BitVec.reduceAdd, hlen1] at hhdr
        rw [← hhdr]
        ac_rfl) ?_
    intro sm v_len hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm cap2 ptr2 v_len (by simp; omega) hcap2_lt hptr2
        hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm)
  · have hgrow_f : (cap1 - BitVec.ofNat 64 (dir.length + 1)).ult (BitVec.ofNat 64 name.length) = false :=
      Bool.eq_false_iff.mpr hgrow
    have hfit : (dir.length + 1) + name.length ≤ cap1.toNat := by
      have := mt hult_iff.mpr hgrow; omega
    simp only [vecU8At_eq_header_rest A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]), sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hle_v1, hlt_v1, hptr1⟩ => ?_
    have hrepack1 :
        ((fsp + 8#64) ↦₆₄ cap1) ∗ (((fsp + 8#64) + 8#64) ↦₆₄ ptr1) ∗
          (((fsp + 8#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (dir ++ [0x2f#8]).length) ∗
          vecU8RestAt A cap1 ptr1 (dir ++ [0x2f#8]) ∗
          SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗
          stackAt fsp (max resStack extHookStack) ∗ F =
        (vecU8At A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8]) ∗
          SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗
          stackAt fsp (max resStack extHookStack)) ∗ F := by
      rw [← vecU8At_of_header_rest A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8])
        hle_v1 hlt_v1 hptr1]
      ac_rfl
    rw [hrepack1]
    rcases (show name = [] ∨ 0 < name.length by cases name <;> simp) with rfl | hname_pos
    · apply SepWPp.of_sepWP_cs (mid := pEntry + BitVec.ofNat 64 212)
      dsimp only [tripleRatchetProgAtExt]
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv1
      refine SepWPp.weaken_pre ?_
        (hnext _ cap1 ptr1 (BitVec.ofNat 64 (dir.length + 1))
          (by simpa using hfit) (by omega) hptr1
          (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *])))
      have hhdr1 := vecU8At_of_header_rest A (fsp + 8#64) cap1 ptr1 (dir ++ [0x2f#8])
        hle_v1 hlt_v1 hptr1
      simp only [BitVec.add_assoc, BitVec.reduceAdd, hlen1] at hhdr1
      rw [← hhdr1, List.append_nil]
      exact Entails.of_eq (by ac_rfl)
    · have hname_beq0 : (BitVec.ofNat 64 name.length == 0#64) = false :=
        ofNat_beq_zero_false hname_pos (by omega)
      have hne : name ≠ [] := List.ne_nil_of_length_pos hname_pos
      apply SepWPp.of_sepWP_cs (mid := pEntry + BitVec.ofNat 64 192)
      dsimp only [tripleRatchetProgAtExt]
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv1
      refine step_copy_name (ret := ret) (nameA := nameA) hmc_name hsub_lt hname_lt hne
        hfit (by omega) hptr1 (F := A.pool ∗ F)
        (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hfsp_align
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *]))
        (by ac_rfl) ?_
      intro sm v_len hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hnext sm cap1 ptr1 v_len (by simp; omega) (by omega) hptr1
          hpcm hrunm hspm htrm hx19m hx20m hx22m hcsm)

theorem path_ok_of_deps_core_roX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : SpqrV1.Alloc.MemcpyROOkExtX img ext)
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hstk : 0x70 + max resStack extHookStack ≤ stk)
    (_hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img stk) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  rcases x with ⟨dirA, dir, dirRo, nameA, name, nameRo, ret⟩
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (⌜s0.readReg64 .x0 = ret ∧ s0.readReg64 .x1 = dirA ∧
      (s0.readReg64 .x2).toNat = dir.length ∧ s0.readReg64 .x3 = nameA ∧
      (s0.readReg64 .x4).toNat = name.length ∧
      dir.length < 2 ^ 32 ∧ name.length < 2 ^ 32⌝ ∗
      SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ memRegion ret 24 ∗
      stackAt s0.sp stk ∗ A.pool)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg0, ⟨hx0, hx1, hx2_nat, hx3, hx4_nat, hdir_lt, hname_lt⟩, hmem⟩
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 dir.length := bv_eq_ofNat_of_toNat hx2_nat
  have hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 name.length := bv_eq_ofNat_of_toNat hx4_nat
  have hshim := subroutine_ok_withEncRepeatedCS_x img s0 himg0
    (shim_ok_at2_ext_x hC (name := pathName)
      (k := ls_rel% "libsignal_cli::stores::path" "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      (by rw [path_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]))
  have halloc := subroutine_ok_withEncRepeatedCS_x img s0 himg0
    (alloc_ok_at_norm_ext_x hC (name := pathName)
      (k := ls_rel% "libsignal_cli::stores::path" "__rustc::__rust_alloc")
      (by rw [path_fnOff, (ls_stub% "__rustc::__rust_alloc")]))
  have hmc_dir := subroutine_ok_withEncRepeatedCS_x img s0 himg0 (memcpy_bytesAt_ok_at_roX hC hRO dirRo)
  have hmc_name := subroutine_ok_withEncRepeatedCS_x img s0 himg0 (memcpy_bytesAt_ok_at_roX hC hRO nameRo)
  have hres_cs : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName -
        BitVec.ofNat 64
          (ls_rel%
            "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
            "libsignal_cli::stores::path"))
      (withEncRepeatedCS s0 (SpqrV1.Varint.doReserveSpecOf resStack A)) :=
    @Eq.mp _ _
      (@congrArg (BitVec 64) Prop _ _
        (fun addr => subroutine_ok (tripleRatchetProgAtExt img.base ext) addr
          (withEncRepeatedCS s0 (SpqrV1.Varint.doReserveSpecOf resStack A)))
        (cliDoReserve_fnAddr_eq img.base ext).symm)
      (subroutine_ok_withEncRepeatedCS_x img s0 himg0 hRes)
  clear hRes
  have hpanic := panic_at_handle_error_norm_ext (b := img.base) (ext := ext)
    (name := pathName)
    (k := ls_rel% "libsignal_cli::stores::path" "alloc::raw_vec::handle_error")
    (by rw [path_fnOff, (ls_stub% "alloc::raw_vec::handle_error")])
  have hmem_stk : s0.mem ⊨ memRegion ret 24 ∗ stackAt s0.sp stk ∗
      (SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
        SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗ R) := by
    convert hmem using 1; ac_rfl
  have hstk_lt : stk < 2 ^ 64 := stk_lt_two_pow_64 hmem_stk
  have hsub_lt : max resStack extHookStack ≤ 2 ^ 64 := by omega
  have halign64 : s0.sp &&& 15#64 = 0#64 := by
    simpa only [State.spAligned, beq_iff_eq] using halign
  refine ⟨SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
    SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ memRegion ret 24 ∗
    stackAt s0.sp stk ∗ A.pool, R, hmem, ?_⟩
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry (b := img.base) (H := Rust.withPanics ext) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path"))
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 4) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 4))
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 8) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 8))
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 12) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 12))
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 16) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 16))
  have f20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 20) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 20))
  have f24 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 24) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 24))
  have f28 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 28) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 28))
  have f32 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 32) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 32))
  have f52 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 52) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 52))
  have f56 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 56) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 56))
  have f60 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 60) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 60))
  dsimp only [tripleRatchetProgAtExt] at f0 f4 f8 f12 f16 f20 f24 f28 f32 f52 f56 f60 hpc
  generalize hpEntry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pathName = pEntry
    at f0 f4 f8 f12 f16 f20 f24 f28 f32 f52 f56 f60 hpc
  have hbit63 : (BitVec.ofNat 64 dir.length).getLsbD 63 = false := ofNat_getLsbD_63_false (by omega)
  have helem63 : (BitVec.ofNat 64 dir.length)[63] = false := ofNat_getElem_63_false (by omega)
  rw [stackAt_split_ge s0.sp hstk (by omega), stackAt_path_frame s0.sp (by omega)]
  generalize hfsp : s0.sp - 112#64 = fsp
  have hfsp_align : fsp &&& 15#64 = 0#64 := by rw [← hfsp]; exact sp_sub_112_aligned halign64
  rw [memRegion_24_cells ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun r0 => ?_
  refine SepWPp.exists_elim fun r1 => ?_
  refine SepWPp.exists_elim fun r2 => ?_
  rw [cells_14_eq fsp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v0 => ?_
  refine SepWPp.exists_elim fun v1 => ?_
  refine SepWPp.exists_elim fun v2 => ?_
  refine SepWPp.exists_elim fun v3 => ?_
  refine SepWPp.exists_elim fun v4 => ?_
  refine SepWPp.exists_elim fun v5 => ?_
  refine SepWPp.exists_elim fun v6 => ?_
  refine SepWPp.exists_elim fun v7 => ?_
  refine SepWPp.exists_elim fun v8 => ?_
  refine SepWPp.exists_elim fun v9 => ?_
  refine SepWPp.exists_elim fun v10 => ?_
  refine SepWPp.exists_elim fun v11 => ?_
  refine SepWPp.exists_elim fun v12 => ?_
  refine SepWPp.exists_elim fun v13 => ?_
  apply SepWPp.of_sepWP_cs (mid := pEntry + BitVec.ofNat 64 4)
  dsimp only [tripleRatchetProgAtExt]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_sp
  apply SepWPp.of_sepWP_cs (mid := pEntry + BitVec.ofNat 64 64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_pro
  set savedFrame : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (0x70 + max resStack extHookStack)) ∗
    (ret ↦₆₄ r2) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r0) ∗
    (fsp ↦₆₄ v0) ∗
    ((fsp + 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((fsp + 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((fsp + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
    ((fsp + 56#64) ↦₆₄ v7) ∗
    ((fsp + 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
    ((fsp + 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
    ((fsp + 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((fsp + 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((fsp + 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((fsp + 104#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) with hsaved_def
  clear_value savedFrame
  refine step_to_owned (ret := ret) (dirA := dirA) (nameA := nameA) (name := name)
    hshim halloc hmc_dir hpanic hsub_lt hdir_lt
    (F := ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ savedFrame)
    (by dsimp only [tripleRatchetProgAtExt]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) hfsp_align
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by
      have hinv0 := hinv_sp.trans hinv_pro
      simp only [EncRepeatedCalleeSaved, arm64_norm, hinv0])
    (by rw [hsaved_def]; ac_rfl) ?_
  intro s1 ptr0 hptr0 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
  refine step_push_slash hres_cs hsub_lt hdir_lt hptr0
    (v1 := v1) (v2 := v2) (v3 := v3)
    (F := SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ savedFrame)
    hpc1 hrun1 hsp1 hfsp_align htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    (by ac_rfl) ?_
  intro s2 cap1 ptr1 hcap1_ge hcap1_lt hpc2 hrun2 hsp2 htr2 hx9_2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2
  refine step_append_name hres_cs hmc_name hsub_lt hname_lt hcap1_ge hcap1_lt
    (F := SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗ savedFrame)
    hpc2 hrun2 hsp2 hfsp_align htr2 hx9_2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2
    (by ac_rfl) ?_
  intro s3 cap2 ptr2 v_len hcap2_ge hcap2_lt hptr2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx22_3 hcs3
  rcases hcs3 with ⟨hx26_3, hx27_3, hx28_3, hvregs_3, _⟩
  have f212 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 212) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 212))
  have f216 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 216) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 216))
  have f220 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 220) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 220))
  have f224 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 224) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 224))
  have f228 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 228) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 228))
  have f232 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 232) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 232))
  have f236 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 236) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 236))
  have f240 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 240) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 240))
  have f244 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 244) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 244))
  have f248 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 248) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 248))
  have f252 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 252) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 252))
  have f256 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 256) path_fnOff (by decide) (ls_decode% pathDec (ls_off% "libsignal_cli::stores::path" + 256))
  dsimp only [tripleRatchetProgAtExt] at f212 f216 f220 f224 f228 f232 f236 f240 f244 f248 f252 f256 hpc3
  rw [hpEntry] at f212 f216 f220 f224 f228 f232 f236 f240 f244 f248 f252 f256 hpc3
  rw [hsaved_def]
  have hq_pre :
      (((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗ ((fsp + 24#64) ↦₆₄ v_len) ∗
        vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗
        SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ A.pool ∗
        stackAt fsp (max resStack extHookStack)) ∗
        SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (0x70 + max resStack extHookStack)) ∗
          (ret ↦₆₄ r2) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r0) ∗
          (fsp ↦₆₄ v0) ∗
          ((fsp + 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((fsp + 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((fsp + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
          ((fsp + 56#64) ↦₆₄ v7) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
          ((fsp + 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((fsp + 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((fsp + 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((fsp + 104#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
      (ret ↦₆₄ r2) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r0) ∗
        vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) ∗
        SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
        SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (0x70 + max resStack extHookStack)) ∗
        stackAt fsp (max resStack extHookStack) ∗
        (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ cap2) ∗ ((fsp + 16#64) ↦₆₄ ptr2) ∗
        ((fsp + 24#64) ↦₆₄ v_len) ∗
        ((fsp + 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((fsp + 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((fsp + 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((fsp + 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((fsp + 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((fsp + 104#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        A.pool := by
    ac_rfl
  have hs3_spAligned : s3.spAligned = true := by simp [State.spAligned, hsp3, hfsp_align]
  rw [hq_pre]
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  dsimp only [tripleRatchetProgAtExt]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  refine ⟨?_, ?_, by simp only [CalleeSavedPreserved, arm64_norm, *]⟩
  · intro hPR
    have htot_bv :
        BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length =
          BitVec.ofNat 64 (dir ++ [0x2f#8] ++ name).length := by
      simp only [List.length_append, List.length_singleton, ← BitVec.ofNat_add]
    have hvec_out :
        (ret ↦₆₄ cap2) ∗ ((ret + 8#64) ↦₆₄ ptr2) ∗
          ((ret + 16#64) ↦₆₄ (BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length)) ∗
          vecU8RestAt A cap2 ptr2 (dir ++ [0x2f#8] ++ name) =
        vecU8At A ret cap2 ptr2 (dir ++ [0x2f#8] ++ name) := by
      rw [htot_bv]
      exact vecU8At_of_header_rest A ret cap2 ptr2 (dir ++ [0x2f#8] ++ name) hcap2_ge hcap2_lt hptr2
    change _ ⊨ (⌜_ = s0.trace⌝ ∗ vecU8 A ret (dir ++ [0x2f#8] ++ name) ∗
      SpqrV1.ChainProofs.bytesAt dirRo dirA dir ∗
      SpqrV1.ChainProofs.bytesAt nameRo nameA name ∗ stackAt s0.sp stk ∗ A.pool) ∗ R
    simp only [vecU8, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨cap2, ptr2, by simp only [arm64_norm, *], ?_⟩
    rw [stackAt_split_ge s0.sp hstk (by omega), stackAt_path_frame s0.sp (by omega),
      hfsp, cells_14_eq fsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc]
    refine ⟨v0, cap2, ptr2,
      BitVec.ofNat 64 (dir.length + 1) + BitVec.ofNat 64 name.length,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 25#5), v7,
      s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
      s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5), ?_⟩
    rw [← hvec_out]
    simp only [sepConj_assoc] at hPR ⊢
    exact hPR
  · simp only [arm64_norm, ← hfsp, fsp_add_112_eq]

theorem path_ok_of_deps_core {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hstk : 0x70 + max resStack extHookStack ≤ stk)
    (_hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img stk) :=
  path_ok_of_deps_core_roX hC (SpqrV1.Alloc.memcpyROOkExtX_of_hookSat hRO) hRes hstk _hb

theorem path_ok_of_deps_core_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk roStk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk))
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hstk : 0x70 + max resStack extHookStack ≤ stk)
    (_hb : (img.base &&& 0xfff#64) = 0#64)
    (hro : roStk ≤ extHookStack := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img stk) :=
  path_ok_of_deps_core_roX hC (memcpyROOkExtX_of_withStack hro hRO) hRes hstk _hb

end CryptoVerification.SignalSession.Cli.Path.Helpers

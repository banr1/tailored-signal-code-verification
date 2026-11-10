/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.CallInv

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.PutStr.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## 1. Layout-Independent Instruction Decodes & Cut-Point Helper -/

abbrev atOff (fnBase : BitVec 64) (k : Nat) : BitVec 64 :=
  fnBase + BitVec.ofNat 64 k

gen_decodes libsignalSessionCode_tree dirPutStrBin
  [(ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") →
   (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>" + 348)]

/-! ## 2. Callee Bridges & `ImgCallInv`-Preserving Call Rules -/

theorem panic_at_dirPutStr_handle_error (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr dirPutStrName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>"
            "alloc::raw_vec::handle_error")) =
      some Rust.panicked :=
  panic_at_panicSymbol (P := libsignalSessionCode) (hname := handleErrorName)
    dirPutStr_fnOff
    (by decide)
    (by decide)
    (ls_lemma% hookAtOff "alloc::raw_vec::handle_error")
    (by
      unfold Rust.isPanicSymbol
      cases (handleErrorName.startsWith "core::panicking::") <;> rfl)

theorem shim_ok_at_dirPutStr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>"
            "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (session2ShimSpecX.inImage img) :=
  shim_ok_at2_ext_x hC (name := dirPutStrName)
    (k := ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [dirPutStr_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])

theorem alloc_ok_at_dirPutStr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "__rustc::__rust_alloc"))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  alloc_ok_at_norm_ext_x hC (name := dirPutStrName)
    (k := ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "__rustc::__rust_alloc")
    (by rw [dirPutStr_fnOff, (ls_stub% "__rustc::__rust_alloc")])

theorem dealloc_ok_at_dirPutStr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hC (name := dirPutStrName)
    (k := ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "__rustc::__rust_dealloc")
    (by rw [dirPutStr_fnOff, (ls_stub% "__rustc::__rust_dealloc")])

theorem memcpy_ro_ok_at_dirPutStr (img : Obj.Image)
    (ext : String → Option (State → State))
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "memcpy"))
      ((withStack SpqrV1.Alloc.sessionMemcpyRegionROSpec extHookStack).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_withStack_of_subroutine_ok
      (hook_ok_at (P := libsignalSessionCode) (hname := memcpyName)
        dirPutStr_fnOff
        (by decide)
        (by decide)
        (ls_lemma% hookAtOff "memcpy")
        (by decide)
        hRO)
      extHookStack)

theorem memcpy_bytesAt_inImage_ok_at (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (ro : Bool) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "memcpy"))
      ((withStack (SpqrV1.Alloc.sessionMemcpyBytesAtSpec ro) extHookStack).inImage img) := by
  cases ro
  · apply subroutine_ok_outcome_intro
    rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp
    have hmc := hC.session_memcpy_region_ok_at dirPutStrName
      (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "memcpy")
      extHookStack (by decide) (by decide)
      (by rw [dirPutStr_fnOff, (ls_stub% "memcpy")])
    have hpre' : s0.mem ⊨
        ((withStack sessionMemcpyRegionSpec extHookStack).inImage img).pre
          (dst, src, bs) s0 ∗ R := by
      simp only [Spec.inImage, withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionSpec, memcpyRegionSpec, SpqrV1.ChainProofs.bytesAt_false,
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      exact ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2.1, hpre.2.1.2.2.1⟩, hpre.2.2⟩
    exact (hmc.to_outcome (dst, src, bs) R s0 hpc hrun hpre' hsp).mono_outcome fun _ h => h
  · exact memcpy_ro_ok_at_dirPutStr img ext hRO

theorem bcmp_inImage_ok_at_dirPutStr (img : Obj.Image)
    (ext : String → Option (State → State))
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "bcmp"))
      (cliBcmpSpec.inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (hook_ok_at (P := libsignalSessionCode) (hname := cliBcmpName)
      dirPutStr_fnOff
      (by decide)
      (by decide)
      (ls_lemma% hookAtOff "bcmp")
      (by decide)
      hBcmp)

/-- Unwrapped inner `Spec` of `growOneDirSpec A img stk` (`(growOneDirBaseSpec A stk).inImage img = growOneDirSpec A img stk`). -/
def growOneDirBaseSpec (A : RustAlloc) (stk : Nat) : Spec GrowOneDirGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.cap.toNat < 2 ^ 32⌝ ∗
      RustHeap.vecAt A 48 8 (dirEntryAt A) x.v x.cap x.ptr x.xs ∗ stackAt s.sp stk ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ ptr' : BitVec 64, RustHeap.vecAt A 48 8 (dirEntryAt A) x.v
        (BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ptr' x.xs) ∗
      stackAt s0.sp stk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem growOne_ok_at_dirPutStr {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk : Nat}
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>"
            "<alloc::raw_vec::RawVec<(alloc::string::String, alloc::vec::Vec<u8>)>>::grow_one"))
      ((growOneDirBaseSpec A growStk).inImage img) :=
  sub_ok_at_of_fnAddr hGrow dirPutStrName _
    (by rw [dirPutStr_fnOff, growOneDir_fnOff])

/-- Framed `SepWPp` call rule for `(spec.inImage img)` callees that also preserves `ImgCallInv img`
    into the `SepWPp` continuation. -/
theorem call_inImage_wpp {α : Type} {prog : Program} {callee ret_pc target_pc : BitVec 64}
    {spec : Spec α} {img : Obj.Image}
    (hcall : subroutine_ok prog callee (spec.inImage img))
    (x : α) {s : State} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    {φ : Prop} (hspec : spec.pre x s = ⌜φ⌝ ∗ T) (hφ : φ) (hP : P = T ∗ F)
    (hpan : ∀ sf, Qp sf (spec.onPanic x s sf ∗ F))
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog target_pc s P Q Qp := by
  refine SepWPp.call_inImage_frame (x := x) hcall hinv.1 hinv.2 hpc hrun hsp_align hlr
    hspec hφ hP ?_ (fun sf _ => hpan sf)
    (fun sf hpcm hrunm hspm hcsm hfz hsym => hnext sf hpcm hrunm hspm hcsm ⟨hfz, hsym⟩) ?_
  · intro sf code R' _ hpost
    rw [hexit] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sf R' _ hpost
    rw [hoom] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-- Normal-return `SepWPp` postcondition matching `wpp_init` on `dirPutStrSpec`. -/
abbrev DirPutStrPost (A : RustAlloc) (img : Obj.Image) (x : DirPutStrGhost)
    (s0 : State) (stk : Nat) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutStrSpec A img stk).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Panic `SepWPp` postcondition matching `wpp_init` on `dirPutStrSpec`. -/
abbrev DirPutStrPanic (A : RustAlloc) (img : Obj.Image) (x : DirPutStrGhost)
    (s0 : State) (stk : Nat) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutStrSpec A img stk).onPanic x s0 sf ∗ R)

/-- Sequence a `SepWP` segment up to `mid` into `SepWPp`, automatically propagating
    `ImgCallInv img` across `Steps prog s sm`. -/
theorem sepWPp_cut {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {img : Obj.Image}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P fun sm Pm =>
      ∀ s', s' = sm → ImgCallInv img s' → SepWPp prog ret s' Pm Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_frozen hinv.1 hinv.2
    (h.mono fun sm Pm _ _ hcont hfz hsym => hcont sm rfl ⟨hfz, hsym⟩)

theorem spAligned_of_sub80 {s0 s1 : State} (h0 : s0.spAligned = true)
    (hsp : s1.sp = s0.sp - 80#64) : s1.spAligned = true := by
  simpa only [State.spAligned, hsp] using s0.spAligned_sub 80#64 h0

/-- Sequence a `SepWP` block on the rebased program up to `mid` without unfolding
    `tripleRatchetProgAtExt` inside the `SepWPp` continuation. -/
theorem sepWPp_cut_rebase {b : BitVec 64} {ext : String → Option (State → State)}
    {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {img : Obj.Image}
    (hinv : ImgCallInv img s)
    (h : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) mid s P fun sm Pm =>
      ∀ s1 P1, ImgCallInv img s1 → (s1 = sm ∧ P1 = Pm) →
        SepWPp (tripleRatchetProgAtExt b ext) ret s1 P1 Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  change SepWP (tripleRatchetProgAtExt b ext) mid s P _ at h
  exact SepWPp.of_sepWP_frozen hinv.1 hinv.2
    (h.mono fun sm Pm _ _ hcont hfz hsym => hcont sm Pm ⟨hfz, hsym⟩ ⟨rfl, rfl⟩)

theorem sepWPp_pure_left {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom :=
  SepWPp.pure_elim h

theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (h : ∀ a, SepWPp prog ret s (Φ a ∗ P) Q Qp oom) :
    SepWPp prog ret s ((∃∗ a, Φ a) ∗ P) Q Qp oom := by
  rw [sepExists_sepConj_left]
  exact SepWPp.exists_elim h

theorem panic_false_wpp {A : RustAlloc} {img : Obj.Image} {x : DirPutStrGhost}
    {s0 : State} {stk : Nat} {R : SepProp} {sf : State} {F : SepProp} :
    DirPutStrPanic A img x s0 stk R sf (⌜False⌝ ∗ F) := by
  intro hm
  rw [sepConj_assoc] at hm
  exact (not_satisfies_false_sepConj hm).elim

/-- Framed tail-call combinator for `(spec.inImage img)` callees (`b __rust_dealloc`). -/
theorem tailcall_inImage_frame {α : Type} {prog : Program} {callee ret : BitVec 64}
    {spec : Spec α} {img : Obj.Image}
    (hcall : subroutine_ok prog callee (spec.inImage img))
    (x : α) {φ : Prop} {s : State} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T) (hφ : φ) (hP : P = T ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝)
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hret : ∀ sf : State, sf.pc = ret → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Q sf (spec.post x s sf ∗ F)) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr ?_ ?_ ?_
    (fun sf hpcf hrunf hspf hcsf => SepWPp.done hpcf hrunf (hret sf hpcf hrunf hspf hcsf)) ?_
  · intro R' hm
    dsimp [Spec.inImage]
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj,
      ← sepConj_assoc, ← hP]
    exact ⟨hinv, hφ, hm⟩
  · intro sf code R' _ hpost
    dsimp [Spec.inImage] at hpost
    rw [hexit] at hpost
    exact not_satisfies_false_sepConj hpost
  · rintro sf _ ⟨R', hpost⟩
    dsimp [Spec.inImage] at hpost
    rw [hpan] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro sf R' _ hpost
    dsimp [Spec.inImage] at hpost
    rw [hoom] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-! ## 3. Stack & Region Lemmas (Arbitrary `stk` Bound + Frame Split/Merge) -/

/-- Any region separated from an owned byte strictly fits inside the 64-bit address space. -/
theorem memRegion_lt_two_pow_64_of_pointsTo8 {m : Memory} {base a : BitVec 64}
    {v : BitVec 8} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion base n ∗ ((a ↦₈ v) ∗ R)) : n < 2 ^ 64 := by
  by_contra hge
  have hle : 2 ^ 64 ≤ n := Nat.le_of_not_lt hge
  let m' : Memory := m.write8 a (v + 1#8)
  have hag : AgreesOutside m m' base n :=
    (AgreesOutside.rfl' m base n).write8 (by unfold InRegion; have := (a - base).isLt; omega)
  have hm' : m' ⊨ memRegion base n ∗ ((a ↦₈ v) ∗ R) :=
    (IsBlock.memRegion base n).update (IsBlock.memRegion base n) (Nat.le_refl _) h hag trivial
  have hm'_a : m' ⊨ (a ↦₈ v) ∗ (memRegion base n ∗ R) := by
    rwa [← sepConj_assoc, sepConj_comm (memRegion base n), sepConj_assoc] at hm'
  have hr1 : m'.read8 a = v := (IsBlock.pointsTo8 a v).read hm'_a
  have hr2 : m'.read8 a = v + 1#8 := Memory.read8_write8_same m a (v + 1#8)
  rw [hr2] at hr1
  bv_omega

/-- Any region separated from an owned 64-bit cell satisfies `n ≤ 2 ^ 64`. -/
theorem memRegion_le_two_pow_64_of_pointsTo64 {m : Memory} {base a v : BitVec 64}
    {n : Nat} {R : SepProp}
    (h : m ⊨ (a ↦₆₄ v) ∗ memRegion base n ∗ R) : n ≤ 2 ^ 64 := by
  have ha8 : (a ↦₆₄ v) ⊢ memRegion a 1 ∗ memRegion (a + 1#64) 7 := by
    rw [← memRegion_split a 1 7 (by decide)]
    exact pointsTo64_entails_memRegion a v
  have h1 : m ⊨ memRegion a 1 ∗ memRegion (a + 1#64) 7 ∗ memRegion base n ∗ R := by
    simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left ha8) h
  rw [memRegion_one, sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨b0, hb0⟩
  have hb0' : m ⊨ memRegion base n ∗ ((a ↦₈ b0) ∗ (memRegion (a + 1#64) 7 ∗ R)) := by
    ac_nf at hb0 ⊢
  exact Nat.le_of_lt (memRegion_lt_two_pow_64_of_pointsTo8 hb0')

theorem stackAt_split_sub (sp : BitVec 64) {sub big : Nat}
    (hle : sub ≤ big) (hmax : big ≤ 2 ^ 64) :
    stackAt sp big =
      memRegion (sp - BitVec.ofNat 64 big) (big - sub) ∗ stackAt sp sub := by
  have h1 := stackAt_split_bottom sp sub (big - sub) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

/-- Split `stackAt sp stk` (`80 + cal ≤ stk ≤ 2 ^ 64`) into the bottom spare bytes,
`stackAt (sp - 80#64) cal`, and the ten 8-byte stack frame slots of `Dir::put::<&str>`. -/
theorem stackAt_dirPutStr_split (sp : BitVec 64) {cal stk : Nat}
    (hstk : 80 + cal ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
      stackAt (sp - 80#64) cal ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
  have hw := wrapperFrame_split sp (wrapperStack := stk) (hookStack := cal) 10
    (by omega) hmax
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
        ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
        ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
        ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9)) := by
    cells_unfold
  simpa only [BitVec.ofNat_eq_ofNat, hc10, sepConj_assoc] using hw

/-- Recombine the ten 8-byte stack slots + `stackAt (sp - 80#64) cal` + bottom spare region
back into `stackAt sp stk`. -/
theorem stackAt_dirPutStr_merge (sp : BitVec 64) {cal stk : Nat}
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64)
    (hstk : 80 + cal ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
      stackAt (sp - 80#64) cal ∗
      ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗
      ((sp - 64#64) ↦₆₄ v2) ∗ ((sp - 56#64) ↦₆₄ v3) ∗
      ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
      ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗
      ((sp - 16#64) ↦₆₄ v8) ∗ ((sp - 8#64) ↦₆₄ v9) ⊢
      stackAt sp stk := by
  rw [stackAt_dirPutStr_split sp hstk hmax]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans ?_ (Entails.sepExists_intro v0)
  refine Entails.trans ?_ (Entails.sepExists_intro v1)
  refine Entails.trans ?_ (Entails.sepExists_intro v2)
  refine Entails.trans ?_ (Entails.sepExists_intro v3)
  refine Entails.trans ?_ (Entails.sepExists_intro v4)
  refine Entails.trans ?_ (Entails.sepExists_intro v5)
  refine Entails.trans ?_ (Entails.sepExists_intro v6)
  refine Entails.trans ?_ (Entails.sepExists_intro v7)
  refine Entails.trans ?_ (Entails.sepExists_intro v8)
  refine Entails.trans ?_ (Entails.sepExists_intro v9)
  exact Entails.refl _

theorem pointsTo64_three_entails_memRegion24 (a v0 v1 v2 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ⊢ memRegion a 24 := by
  have h1 : memRegion a 24 = memRegion a 8 ∗ (memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8) := by
    rw [memRegion_split a 8 16 (by decide), memRegion_split (a + 8#64) 8 8 (by decide)]
    have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
    rw [h16]
  rw [h1]
  exact sepConj_mono (pointsTo64_entails_memRegion a v0)
    (sepConj_mono (pointsTo64_entails_memRegion _ v1) (pointsTo64_entails_memRegion _ v2))

theorem memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) := by
  set top : BitVec 64 := a + 48#64
  have h := ProofLib.memRegion_cells (top - 48#64) 6 (by decide)
  change memRegion (top - 48#64) 48 = cells (top - 48#64) 6 at h
  have hc6 : cells (top - 48#64) 6 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((top - 48#64) ↦₆₄ v0) ∗ ((top - 40#64) ↦₆₄ v1) ∗ ((top - 32#64) ↦₆₄ v2) ∗
        ((top - 24#64) ↦₆₄ v3) ∗ ((top - 16#64) ↦₆₄ v4) ∗ ((top - 8#64) ↦₆₄ v5)) := by
    cells_unfold
  rw [hc6] at h
  have o0 : top - 48#64 = a := by dsimp [top]; bv_omega
  have o1 : top - 40#64 = a + 8#64 := by dsimp [top]; bv_omega
  have o2 : top - 32#64 = a + 16#64 := by dsimp [top]; bv_omega
  have o3 : top - 24#64 = a + 24#64 := by dsimp [top]; bv_omega
  have o4 : top - 16#64 = a + 32#64 := by dsimp [top]; bv_omega
  have o5 : top - 8#64 = a + 40#64 := by dsimp [top]; bv_omega
  simpa only [o0, o1, o2, o3, o4, o5] using h

/-! ## 4. Pure `DirGhost` / `setOrPush` / Bit-Vector Lemmas -/

theorem allocFailedIn_of_append {s0 sf : State}
    (htr : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], htr.symm⟩⟩
  unfold allocFailedIn
  rw [htr, List.drop_left]
  exact List.Mem.head _

theorem allocFailedIn_panicked {s0 s : State}
    (h : allocFailedIn s0 s ∧ s0.trace <+: s.trace) :
    allocFailedIn s0 (Rust.panicked s) ∧ s0.trace <+: (Rust.panicked s).trace :=
  h

theorem allocFailedIn_of_trace_eq {s0 s sf : State}
    (htr : s.trace = s0.trace)
    (h : allocFailedIn s sf ∧ s.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢
  rw [← htr]
  exact h

theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.weaken_pre hent h

theorem panic_callee_wpp {A : RustAlloc} {img : Obj.Image} {x : DirPutStrGhost}
    {s0 s sf : State} {stk : Nat} {R F : SepProp}
    (htr : s.trace = s0.trace) :
    DirPutStrPanic A img x s0 stk R sf
      ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro hm
  have hm' : sf.mem ⊨ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ (anyHeap ∗ F ∗ R) := by
    simpa only [sepConj_assoc] using hm
  rw [satisfies_pure_sepConj] at hm'
  exact allowPanic_panicked (allocFailedIn_of_trace_eq htr hm'.1) hm

theorem setOrPush_append_of_forall_ne (name bs : List (BitVec 8)) :
    ∀ (pre suf : List (List (BitVec 8) × List (BitVec 8))),
      (∀ e ∈ pre, e.1 ≠ name) →
      DirGhost.setOrPush name bs (pre ++ suf) = pre ++ DirGhost.setOrPush name bs suf
  | [], suf, _ => rfl
  | e :: es, suf, hne => by
    have he : e.1 ≠ name := hne e (.head _)
    have hes : ∀ e' ∈ es, e'.1 ≠ name := fun e' hm => hne e' (.tail _ hm)
    simp only [List.cons_append, DirGhost.setOrPush, he, ↓reduceIte,
      setOrPush_append_of_forall_ne name bs es suf hes]

theorem setOrPush_eq_append_singleton_of_forall_ne (name bs : List (BitVec 8))
    (xs : List (List (BitVec 8) × List (BitVec 8)))
    (hne : ∀ e ∈ xs, e.1 ≠ name) :
    DirGhost.setOrPush name bs xs = xs ++ [(name, bs)] := by
  simpa only [List.append_nil, DirGhost.setOrPush] using
    setOrPush_append_of_forall_ne name bs xs [] hne

theorem ofNat_eq_of_toNat_eq {w : BitVec 64} {n : Nat} (h : w.toNat = n) :
    w = BitVec.ofNat 64 n := by
  subst h
  exact (BitVec.ofNat_toNat 64 w).symm

theorem ofNat_toNat_of_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false :=
  beq_false_of_ne (ofNat_ne_zero_of_pos hpos hlt)

theorem layoutOk_u8_of_lt {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    LayoutOk n 1 :=
  ⟨hpos, ⟨0, rfl⟩, by omega⟩

theorem bv64_eq_of_lt {m n : Nat} (hm : m < 2 ^ 64) (hn : n < 2 ^ 64)
    (h : BitVec.ofNat 64 m = BitVec.ofNat 64 n) : m = n := by
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at ht
  exact ht

theorem preheader_mul48 (n : Nat) :
    ((BitVec.ofNat 64 n + (BitVec.ofNat 64 n) <<< 1) <<< 4) =
      BitVec.ofNat 64 (n * 48) := by
  have h1 : (BitVec.ofNat 64 n) <<< 1 = BitVec.ofNat 64 n * 2#64 := by bv_omega
  have h2 : ∀ w : BitVec 64, w <<< 4 = w * 16#64 := fun _ => by bv_omega
  rw [h1, h2]
  have h3 : (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64) * 16#64 =
      BitVec.ofNat 64 n * 48#64 := by bv_omega
  rw [h3, BitVec.ofNat_mul]

theorem madd_slot_eq (ptr : BitVec 64) (n : Nat) :
    ptr + BitVec.ofNat 64 n * 48#64 = ptr + BitVec.ofNat 64 (n * 48) := by
  rw [BitVec.ofNat_mul]

theorem growOne_cap_gt {cap : BitVec 64} {len : Nat}
    (heq : len = cap.toNat) (hlt : len < 2 ^ 32) :
    len < (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat := by
  rw [ofNat_toNat_of_lt (by omega)]
  omega

/-! ## 5. `nameBuf`, `vecU8`, `arrayAt`, and `dirAt` Representation Lemmas -/

/-- Owned buffer for `name.to_owned()`: empty if `name = []` (with non-null dangling `ptr`),
otherwise `A.live ptr name.length 1 ∗ (ptr ↦ₛ name)`. -/
def nameBuf (A : RustAlloc) (ptr : BitVec 64) (name : List (BitVec 8)) : SepProp :=
  ⌜ptr ≠ 0#64 ∧ name.length < 2 ^ 63⌝ ∗
    (if name = [] then emp else A.live ptr name.length 1 ∗ (ptr ↦ₛ name))

/-- Remainder of `nameBuf` when lending `(ptr ↦ₛ name)` to read-preserving callees (`bcmp`). -/
def nameBufRest (A : RustAlloc) (ptr : BitVec 64) (name : List (BitVec 8)) : SepProp :=
  ⌜ptr ≠ 0#64 ∧ name.length < 2 ^ 63⌝ ∗
    (if name = [] then emp else A.live ptr name.length 1)

theorem nameBuf_expose_bytes (A : RustAlloc) (ptr : BitVec 64) (name : List (BitVec 8)) :
    nameBuf A ptr name = (ptr ↦ₛ name) ∗ nameBufRest A ptr name := by
  cases name with
  | nil =>
    simp only [nameBuf, nameBufRest, ↓reduceIte, pointsToBytes_nil, emp_sepConj]
  | cons _ _ =>
    simp only [nameBuf, nameBufRest, reduceCtorEq, ↓reduceIte]
    ac_rfl

theorem nameBuf_of_nil (A : RustAlloc) :
    emp ⊢ nameBuf A 1#64 [] := by
  simp only [nameBuf, List.length_nil, ↓reduceIte]
  exact Entails.pure_right (φ := (1#64 : BitVec 64) ≠ 0#64 ∧ 0 < 2 ^ 63)
    ⟨by decide, by decide⟩ (Entails.refl emp)

theorem nameBuf_of_nonempty (A : RustAlloc) (ptr : BitVec 64) (name : List (BitVec 8))
    (hne : name ≠ []) (hp : ptr ≠ 0#64) (hlt : name.length < 2 ^ 63) :
    A.live ptr name.length 1 ∗ (ptr ↦ₛ name) ⊢ nameBuf A ptr name := by
  simp only [nameBuf, hne, ↓reduceIte]
  exact Entails.pure_right ⟨hp, hlt⟩ (Entails.refl _)

theorem nameBuf_drop_nil (A : RustAlloc) (ptr : BitVec 64) :
    nameBuf A ptr [] ⊢ emp := by
  simp only [nameBuf, ↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

theorem nameBuf_for_dealloc (A : RustAlloc) (ptr : BitVec 64) (name : List (BitVec 8))
    (hne : name ≠ []) :
    nameBuf A ptr name ⊢
      ⌜ptr ≠ 0#64 ∧ LayoutOk name.length 1⌝ ∗
        A.live ptr name.length 1 ∗ memRegion ptr name.length := by
  simp only [nameBuf, hne, ↓reduceIte]
  refine Entails.pure_left fun ⟨hp, hlt⟩ => ?_
  have hpos : 0 < name.length := List.length_pos_of_ne_nil hne
  refine Entails.pure_right ⟨hp, layoutOk_u8_of_lt hpos hlt⟩ ?_
  exact sepConj_mono_right (IsBlock.pointsToBytes ptr name).entails_memRegion

/-- Assemble a 24-byte `Vec<u8>` header with `cap = len = name.length` and `nameBuf` into `vecU8`. -/
theorem vecU8_of_nameBuf (A : RustAlloc) (v ptr : BitVec 64) (name : List (BitVec 8)) :
    (v ↦₆₄ BitVec.ofNat 64 name.length) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 name.length) ∗ nameBuf A ptr name ⊢
      vecU8 A v name := by
  unfold nameBuf
  rw [show (v ↦₆₄ BitVec.ofNat 64 name.length) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 name.length) ∗
        (⌜ptr ≠ 0#64 ∧ name.length < 2 ^ 63⌝ ∗
          if name = [] then emp else A.live ptr name.length 1 ∗ (ptr ↦ₛ name)) =
      ⌜ptr ≠ 0#64 ∧ name.length < 2 ^ 63⌝ ∗
        ((v ↦₆₄ BitVec.ofNat 64 name.length) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 name.length) ∗
          if name = [] then emp else A.live ptr name.length 1 ∗ (ptr ↦ₛ name)) by ac_rfl]
  refine Entails.pure_left fun ⟨hp, hlt⟩ => ?_
  have hp0 : ptr ≠ 0 := hp
  cases name with
  | nil =>
    simp only [↓reduceIte, sepConj_emp, List.length_nil]
    unfold vecU8 vecU8At vecHeader
    refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
      Nat.le_refl, true_and, ↓reduceIte, sepConj_emp, sepConj_assoc]
    rw [show (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
          ⌜(0 : Nat) < 2 ^ 63 ∧ ptr ≠ 0#64⌝ =
        ⌜(0 : Nat) < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64)) by ac_rfl]
    exact Entails.pure_right ⟨by decide, hp⟩ (Entails.refl _)
  | cons b bs =>
    simp only [reduceCtorEq, ↓reduceIte]
    have hpos : 0 < (b :: bs).length := by simp
    have hne0 : BitVec.ofNat 64 (b :: bs).length ≠ 0 :=
      ofNat_ne_zero_of_pos hpos (by omega)
    have htoNat : (BitVec.ofNat 64 (b :: bs).length).toNat = (b :: bs).length :=
      ofNat_toNat_of_lt (by omega)
    unfold vecU8 vecU8At vecHeader
    refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 (b :: bs).length))
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte,
      Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc]
    rw [show (v ↦₆₄ BitVec.ofNat 64 (b :: bs).length) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b :: bs).length) ∗
          ⌜True ∧ True ∧ ptr ≠ 0⌝ ∗
          A.live ptr (b :: bs).length 1 ∗ (ptr ↦ₛ (b :: bs)) =
        ⌜True ∧ True ∧ ptr ≠ 0⌝ ∗
          ((v ↦₆₄ BitVec.ofNat 64 (b :: bs).length) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
            ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b :: bs).length) ∗
            A.live ptr (b :: bs).length 1 ∗ (ptr ↦ₛ (b :: bs))) by ac_rfl]
    exact Entails.pure_right ⟨trivial, trivial, hp0⟩ (Entails.refl _)

/-- Heap payload of a `vecU8At` without its 24-byte header at `v` (so moving the 3 words moves ownership). -/
def vecU8Heap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_heap (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Heap A cap ptr bs := by
  unfold vecU8At vecHeader vecU8Heap
  ac_rfl

theorem vecU8_of_header_heap (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Heap A cap ptr bs ⊢ vecU8 A v bs := by
  rw [← vecU8At_eq_header_heap]
  unfold vecU8
  exact Entails.trans
    (Entails.sepExists_intro (P := fun p => vecU8At A v cap p bs) ptr)
    (Entails.sepExists_intro (P := fun c => ∃∗ p, vecU8At A v c p bs) cap)

/-- Heap remainder of a `vecU8At` when `(ptr ↦ₛ bs)` is temporarily lent out (e.g. to `bcmp`). -/
def vecU8Rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8Heap_expose_bytes (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Heap A cap ptr bs = (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs := by
  by_cases hcap : cap = 0
  · subst hcap
    cases bs with
    | nil =>
      simp only [vecU8Heap, vecU8Rest, ↓reduceIte, pointsToBytes_nil, emp_sepConj]
    | cons b bs' =>
      have hz : (0 : BitVec 64).toNat = 0 := rfl
      apply Entails.antisymm
      · simp only [vecU8Heap, hz, ↓reduceIte]
        exact Entails.pure_left fun h => False.elim (by have := h.1; simp at this)
      · simp only [vecU8Rest, hz, ↓reduceIte, sepConj_emp]
        rw [sepConj_comm]
        exact Entails.pure_left fun h => False.elim (by have := h.1; simp at this)
  · simp only [vecU8Heap, vecU8Rest, hcap, ↓reduceIte]
    ac_rfl

theorem vecU8Heap_drop_zero (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Heap A 0 ptr bs ⊢ emp := by
  simp only [vecU8Heap, ↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

theorem vecU8Heap_for_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap : cap ≠ 0) :
    vecU8Heap A cap ptr bs ⊢
      ⌜ptr ≠ 0#64 ∧ LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  have hpos : 0 < cap.toNat := by
    by_contra h0
    have hz : cap.toNat = 0 := by omega
    exact hcap (ofNat_eq_of_toNat_eq hz)
  simp only [vecU8Heap, hcap, ↓reduceIte]
  refine Entails.pure_left fun ⟨hlen, hlt, hp⟩ => ?_
  refine Entails.pure_right ⟨hp, layoutOk_u8_of_lt hpos hlt⟩ ?_
  refine sepConj_mono_right ?_
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) :=
    memRegion_split' (by omega) rfl (by omega)
  rw [hsplit]
  exact sepConj_mono_left (IsBlock.pointsToBytes ptr bs).entails_memRegion

theorem arrayAt_append {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) :
    ∀ (base : BitVec 64) (xs ys : List α),
      arrayAt elem stride base (xs ++ ys) =
        arrayAt elem stride base xs ∗
          arrayAt elem stride (base + BitVec.ofNat 64 (xs.length * stride)) ys
  | base, [], ys => by
    simp only [List.nil_append, List.length_nil, Nat.zero_mul, BitVec.add_zero, arrayAt, emp_sepConj]
  | base, x :: xs, ys => by
    simp only [List.cons_append, arrayAt, arrayAt_append elem stride _ xs ys,
      List.length_cons, sepConj_assoc]
    have hmul : (xs.length + 1) * stride = stride + xs.length * stride := by
      rw [Nat.succ_mul, Nat.add_comm]
    have haddr : base + BitVec.ofNat 64 stride + BitVec.ofNat 64 (xs.length * stride) =
        base + BitVec.ofNat 64 ((xs.length + 1) * stride) := by
      rw [hmul, BitVec.ofNat_add, ← BitVec.add_assoc]
    rw [haddr]

theorem arrayAt_singleton {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat)
    (base : BitVec 64) (x : α) :
    arrayAt elem stride base [x] = elem x base := by
  simp only [arrayAt, sepConj_emp]

/-- When `xs.length < cap.toNat`, unpack `vecBuf A 48 8 (dirEntryAt A) cap ptr xs` to expose the
6 cells of the next 48-byte slot `ptr + BitVec.ofNat 64 (xs.length * 48)`. -/
theorem vecBuf_dirEntry_expose_slot (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List (List (BitVec 8) × List (BitVec 8)))
    (hlt : xs.length < cap.toNat) :
    vecBuf A 48 8 (dirEntryAt A) cap ptr xs ⊢
      let slot := ptr + BitVec.ofNat 64 (xs.length * 48)
      ⌜xs.length + 1 ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0 ∧ cap ≠ 0⌝ ∗
      A.live ptr (cap.toNat * 48) 8 ∗
      arrayAt (dirEntryAt A) 48 ptr xs ∗
      memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 48))
        ((cap.toNat - (xs.length + 1)) * 48) ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        (slot ↦₆₄ s0) ∗ ((slot + 8#64) ↦₆₄ s1) ∗ ((slot + 16#64) ↦₆₄ s2) ∗
        ((slot + 24#64) ↦₆₄ s3) ∗ ((slot + 32#64) ↦₆₄ s4) ∗ ((slot + 40#64) ↦₆₄ s5)) := by
  have hcap_ne : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  unfold vecBuf
  simp only [hcap_ne, ↓reduceIte]
  refine Entails.pure_left fun ⟨_, hbound, hptr⟩ => ?_
  refine Entails.pure_right ⟨by omega, hbound, hptr, hcap_ne⟩ ?_
  have hsp : memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48) =
      memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) 48 ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 48))
          ((cap.toNat - (xs.length + 1)) * 48) := by
    refine memRegion_split' (by omega) ?_ (by omega)
    rw [show (xs.length + 1) * 48 = xs.length * 48 + 48 by omega,
      BitVec.ofNat_add, BitVec.add_assoc]
  rw [hsp, memRegion_48_cells (ptr + BitVec.ofNat 64 (xs.length * 48))]
  ac_nf
  exact Entails.refl _

/-- Assemble `vecOf A 48 8 (dirEntryAt A) self (xs ++ [(name, bs)])` from the updated header,
live buffer, `arrayAt ... xs`, newly written `name` + `bs` slots at `slot = ptr + 48 * xs.length`,
and remaining spare capacity. -/
theorem vecOf_dirEntry_push_assemble (A : RustAlloc)
    (self cap ptr namePtr bCap bPtr : BitVec 64)
    (xs : List (List (BitVec 8) × List (BitVec 8)))
    (name bs : List (BitVec 8))
    (hle1 : xs.length + 1 ≤ cap.toNat)
    (hbound : cap.toNat * 48 < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hcap : cap ≠ 0) :
    let slot := ptr + BitVec.ofNat 64 (xs.length * 48)
    (self ↦₆₄ cap) ∗ ((self + 8#64) ↦₆₄ ptr) ∗
      ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1)) ∗
      A.live ptr (cap.toNat * 48) 8 ∗
      arrayAt (dirEntryAt A) 48 ptr xs ∗
      memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 48))
        ((cap.toNat - (xs.length + 1)) * 48) ∗
      ((slot ↦₆₄ BitVec.ofNat 64 name.length) ∗ ((slot + 8#64) ↦₆₄ namePtr) ∗
        ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 name.length) ∗ nameBuf A namePtr name) ∗
      (((slot + 24#64) ↦₆₄ bCap) ∗ ((slot + 32#64) ↦₆₄ bPtr) ∗
        ((slot + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Heap A bCap bPtr bs) ⊢
      vecOf A 48 8 (dirEntryAt A) self (xs ++ [(name, bs)]) := by
  intro slot
  have hentry :
      ((slot ↦₆₄ BitVec.ofNat 64 name.length) ∗ ((slot + 8#64) ↦₆₄ namePtr) ∗
        ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 name.length) ∗ nameBuf A namePtr name) ∗
      (((slot + 24#64) ↦₆₄ bCap) ∗ ((slot + 32#64) ↦₆₄ bPtr) ∗
        ((slot + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Heap A bCap bPtr bs) ⊢
      dirEntryAt A (name, bs) slot := by
    have ha32 : slot + 24#64 + 8#64 = slot + 32#64 := by bv_omega
    have ha40 : slot + 24#64 + 16#64 = slot + 40#64 := by bv_omega
    unfold dirEntryAt
    change _ ⊢ vecU8 A slot name ∗ vecU8 A (slot + 24#64) bs
    rw [← ha32, ← ha40]
    exact sepConj_mono (vecU8_of_nameBuf A slot namePtr name)
      (vecU8_of_header_heap A (slot + 24#64) bCap bPtr bs)
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hentry)))))) ?_
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.trans ?_ (Entails.sepExists_intro cap)
  refine Entails.trans ?_ (Entails.sepExists_intro ptr)
  have hlen_app : (xs ++ [(name, bs)]).length = xs.length + 1 := by simp
  simp only [hlen_app, hcap, ↓reduceIte, arrayAt_append, arrayAt_singleton, sepConj_assoc]
  rw [show (self ↦₆₄ cap) ∗ ((self + 8#64) ↦₆₄ ptr) ∗
        ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1)) ∗
        ⌜xs.length + 1 ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr xs ∗
        dirEntryAt A (name, bs) slot ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 48))
          ((cap.toNat - (xs.length + 1)) * 48) =
      ⌜xs.length + 1 ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((self ↦₆₄ cap) ∗ ((self + 8#64) ↦₆₄ ptr) ∗
          ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1)) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr xs ∗
          memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 48))
            ((cap.toNat - (xs.length + 1)) * 48) ∗
          dirEntryAt A (name, bs) slot) by ac_rfl]
  exact Entails.pure_right ⟨hle1, hbound, hptr⟩ (Entails.refl _)

/-- Assemble `vecOf A 48 8 (dirEntryAt A) self (pre ++ (name, bs) :: rest)` on a hit at
`curBase = ptr + 48 * pre.length`. -/
theorem vecOf_dirEntry_hit_assemble (A : RustAlloc)
    (self cap ptr curBase bCap bPtr : BitVec 64)
    (pre rest : List (List (BitVec 8) × List (BitVec 8)))
    (name bs : List (BitVec 8))
    (hcur : curBase = ptr + BitVec.ofNat 64 (pre.length * 48))
    (hle : (pre ++ (name, bs) :: rest).length ≤ cap.toNat)
    (hbound : cap.toNat * 48 < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hcap : cap ≠ 0) :
    (self ↦₆₄ cap) ∗ ((self + 8#64) ↦₆₄ ptr) ∗
      ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (name, bs) :: rest).length) ∗
      A.live ptr (cap.toNat * 48) 8 ∗
      arrayAt (dirEntryAt A) 48 ptr pre ∗
      vecU8 A curBase name ∗
      (((curBase + 24#64) ↦₆₄ bCap) ∗ ((curBase + 32#64) ↦₆₄ bPtr) ∗
        ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Heap A bCap bPtr bs) ∗
      arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
      memRegion (ptr + BitVec.ofNat 64 ((pre ++ (name, bs) :: rest).length * 48))
        ((cap.toNat - (pre ++ (name, bs) :: rest).length) * 48) ⊢
      vecOf A 48 8 (dirEntryAt A) self (pre ++ (name, bs) :: rest) := by
  subst hcur
  set slot := ptr + BitVec.ofNat 64 (pre.length * 48)
  have hentry :
      vecU8 A slot name ∗
        (((slot + 24#64) ↦₆₄ bCap) ∗ ((slot + 32#64) ↦₆₄ bPtr) ∗
          ((slot + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Heap A bCap bPtr bs) ⊢
        dirEntryAt A (name, bs) slot := by
    have ha32 : slot + 24#64 + 8#64 = slot + 32#64 := by bv_omega
    have ha40 : slot + 24#64 + 16#64 = slot + 40#64 := by bv_omega
    unfold dirEntryAt
    change _ ⊢ vecU8 A slot name ∗ vecU8 A (slot + 24#64) bs
    rw [← ha32, ← ha40]
    exact sepConj_mono_right (vecU8_of_header_heap A (slot + 24#64) bCap bPtr bs)
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.trans ?_ (Entails.sepExists_intro cap)
  refine Entails.trans ?_ (Entails.sepExists_intro ptr)
  simp only [hcap, ↓reduceIte, arrayAt_append, arrayAt, sepConj_assoc]
  rw [show (self ↦₆₄ cap) ∗ ((self + 8#64) ↦₆₄ ptr) ∗
        ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (name, bs) :: rest).length) ∗
        ⌜(pre ++ (name, bs) :: rest).length ≤ cap.toNat ∧
          cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A) 48 ptr pre ∗
        dirEntryAt A (name, bs) slot ∗
        arrayAt (dirEntryAt A) 48 (slot + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (name, bs) :: rest).length * 48))
          ((cap.toNat - (pre ++ (name, bs) :: rest).length) * 48) =
      ⌜(pre ++ (name, bs) :: rest).length ≤ cap.toNat ∧
        cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((self ↦₆₄ cap) ∗ ((self + 8#64) ↦₆₄ ptr) ∗
          ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (name, bs) :: rest).length) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          dirEntryAt A (name, bs) slot ∗
          arrayAt (dirEntryAt A) 48 (slot + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 ((pre ++ (name, bs) :: rest).length * 48))
            ((cap.toNat - (pre ++ (name, bs) :: rest).length) * 48)) by ac_rfl]
  refine Entails.pure_right ⟨hle, hbound, hptr⟩ ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right ?_))))
  have heq : vecU8 A slot name ∗
        ((slot + 24#64) ↦₆₄ bCap) ∗
        ((slot + 32#64) ↦₆₄ bPtr) ∗
        ((slot + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Heap A bCap bPtr bs ∗
        arrayAt (dirEntryAt A) 48 (slot + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (name, bs) :: rest).length * 48))
          ((cap.toNat - (pre ++ (name, bs) :: rest).length) * 48) =
      (vecU8 A slot name ∗
        (((slot + 24#64) ↦₆₄ bCap) ∗
          ((slot + 32#64) ↦₆₄ bPtr) ∗
          ((slot + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8Heap A bCap bPtr bs)) ∗
      (arrayAt (dirEntryAt A) 48 (slot + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (name, bs) :: rest).length * 48))
          ((cap.toNat - (pre ++ (name, bs) :: rest).length) * 48)) := by
    ac_rfl
  rw [heq]
  exact sepConj_mono_left hentry

/-! ## 6. Saved-Register Frame Slots & High Callee-Saved Invariant -/

/-- Saved callee-saved GPRs and return address stored in `[s0.sp - 80 .. s0.sp - 8]`. -/
abbrev savedSlots (s0 : State) : SepProp :=
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem savedSlots_merge (s0 : State) {cal stk : Nat}
    (hstk : 80 + cal ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
      stackAt (s0.sp - 80#64) cal ∗
      savedSlots s0 ⊢
      stackAt s0.sp stk :=
  stackAt_dirPutStr_merge s0.sp
    (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23)
    (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)
    hstk hmax

/-- Callee-saved registers untouched by `Dir::put::<&str>` (`x27`, `x28`, `d8..d15`). -/
def PresHigh (s0 s : State) : Prop :=
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem PresHigh.refl (s0 : State) : PresHigh s0 s0 :=
  ⟨rfl, rfl, rfl⟩

theorem PresHigh.of_callee {s0 s sf : State}
    (hp : PresHigh s0 s) (hc : CalleeSavedPreserved s sf) : PresHigh s0 sf :=
  ⟨hc.2.2.2.2.2.2.2.2.1.trans hp.1,
   hc.2.2.2.2.2.2.2.2.2.1.trans hp.2.1,
   hc.2.2.2.2.2.2.2.2.2.2.2.trans hp.2.2⟩

theorem calleeSavedPreserved_of_restored {s0 sf : State}
    (h19 : sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5))
    (h20 : sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5))
    (h21 : sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5))
    (h22 : sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5))
    (h23 : sf.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5))
    (h24 : sf.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5))
    (h25 : sf.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5))
    (h26 : sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5))
    (hfp : sf.readReg64 Reg.fp = s0.readReg64 Reg.fp)
    (hp : PresHigh s0 sf) :
    CalleeSavedPreserved s0 sf :=
  ⟨h19, h20, h21, h22, h23, h24, h25, h26, hp.1, hp.2.1, hfp, hp.2.2⟩

theorem memcpyROOkExtX_of_withStack {img : Obj.Image}
    {ext : String → Option (State → State)} {roStk : Nat}
    (hro : roStk ≤ extHookStack)
    (hRO : HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk)) :
    SpqrV1.Alloc.MemcpyROOkExtX img ext :=
  SpqrV1.Alloc.memcpyROOkExtX_of_hookSat_withStack hro hRO

theorem memcpy_ro_ok_at_dirPutStr_roX (img : Obj.Image)
    (ext : String → Option (State → State))
    (hRO : SpqrV1.Alloc.MemcpyROOkExtX img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "memcpy"))
      ((withStack SpqrV1.Alloc.sessionMemcpyRegionROSpec extHookStack).inImage img) := by
  have hmc_ro := SpqrV1.Alloc.session_memcpy_region_ro_ok_at_x_of_roX hRO dirPutStrName
    (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "memcpy")
    (by rw [dirPutStr_fnOff, (ls_stub% "memcpy")])
  apply subroutine_ok_outcome_intro
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (SpqrV1.Alloc.sessionMemcpyRegionROSpecX.inImage img).pre (dst, src, bs) s0 ∗ R := by
    simpa only [Spec.inImage, withStack, SpqrV1.Alloc.sessionMemcpyRegionROSpec,
      SpqrV1.Alloc.sessionMemcpyRegionROSpecX, sepConj_assoc] using hpre
  refine (hmc_ro.to_outcome (dst, src, bs) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [Spec.inImage, withStack, SpqrV1.Alloc.sessionMemcpyRegionROSpec,
      SpqrV1.Alloc.sessionMemcpyRegionROSpecX, sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem memcpy_bytesAt_inImage_ok_at_roX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hC : AllocContractsX img A ext)
    (hRO : SpqrV1.Alloc.MemcpyROOkExtX img ext)
    (ro : Bool) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "memcpy"))
      ((withStack (SpqrV1.Alloc.sessionMemcpyBytesAtSpec ro) extHookStack).inImage img) := by
  cases ro
  · apply subroutine_ok_outcome_intro
    rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp
    have hmc := hC.session_memcpy_region_ok_at dirPutStrName
      (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "memcpy")
      extHookStack (by decide) (by decide)
      (by rw [dirPutStr_fnOff, (ls_stub% "memcpy")])
    have hpre' : s0.mem ⊨
        ((withStack sessionMemcpyRegionSpec extHookStack).inImage img).pre
          (dst, src, bs) s0 ∗ R := by
      simp only [Spec.inImage, withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionSpec, memcpyRegionSpec, SpqrV1.ChainProofs.bytesAt_false,
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      exact ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2.1, hpre.2.1.2.2.1⟩, hpre.2.2⟩
    exact (hmc.to_outcome (dst, src, bs) R s0 hpc hrun hpre' hsp).mono_outcome fun _ h => h
  · exact memcpy_ro_ok_at_dirPutStr_roX img ext hRO

theorem memcpy_bytesAt_inImage_ok_at_withStack (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) {roStk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk))
    (ro : Bool)
    (hro : roStk ≤ extHookStack := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "memcpy"))
      ((withStack (SpqrV1.Alloc.sessionMemcpyBytesAtSpec ro) extHookStack).inImage img) :=
  memcpy_bytesAt_inImage_ok_at_roX img A ext hC (memcpyROOkExtX_of_withStack hro hRO) ro

end CryptoVerification.SignalSession.Cli.PutStr.Helpers

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.Layout
public import CaseStudies.Hashbrown.Proofs.Externs
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WPFrozen

/-!
# Placement-Generic Rust Allocator Shims

Placement-generic verification of the Rust global allocator shims
(`___rust_no_alloc_shim_is_unstable_v2`, `___rust_alloc`, `___rdl_alloc`, `___rust_dealloc`,
`___rdl_dealloc`) against `HbAlloc.ofMallocng`, parameterized symbolically over `HbCliLayout`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Rust ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CaseStudies.Hashbrown.Proofs

/-! ## Instruction Lists and `HbShimsCode` -/

def rustAllocShimInstrs : List Instr :=
  [ .ret .lr ]

def rustAllocInstrs (C : HbCliLayout) : List Instr :=
  [ .b (C.rdlAllocAddr - C.rustAllocAddr) ]

/-- Fast-path instruction sequence for `___rdl_alloc`:
    `cmp x1, #0x10; mov x2, x0; b.hi +0x14; cmp x1, x2; b.hi +0x0c; mov x0, x2; b malloc`. -/
def rdlAllocFastInstrs (C : HbCliLayout) : List Instr :=
  [ .addSubImm .W64 .SUBS .xzr .x1 0x10#12 false,
    .logicalShift .W64 .ORR .x2 .xzr .x0 .LSL 0,
    .bCond .HI 0x14#64,
    .addSubShift .W64 .SUBS .xzr .x1 .x2 .LSL 0,
    .bCond .HI 0x0c#64,
    .logicalShift .W64 .ORR .x0 .xzr .x2 .LSL 0,
    .b (C.mallocng.mallocAddr - (C.rdlAllocAddr + 0x18#64)) ]

def rustDeallocInstrs (C : HbCliLayout) : List Instr :=
  [ .b (C.rdlDeallocAddr - C.rustDeallocAddr) ]

def rdlDeallocInstrs (C : HbCliLayout) : List Instr :=
  [ .b (C.mallocng.freeAddr - C.rdlDeallocAddr) ]

/-- Instruction-presence bundle for the Rust allocator shims on program `P`. -/
structure HbShimsCode (P : Program) (C : HbCliLayout) : Prop where
  allocShim  : hasInstrs P C.rustAllocShimAddr rustAllocShimInstrs
  alloc      : hasInstrs P C.rustAllocAddr (rustAllocInstrs C)
  rdlAlloc   : hasInstrs P C.rdlAllocAddr (rdlAllocFastInstrs C)
  dealloc    : hasInstrs P C.rustDeallocAddr (rustDeallocInstrs C)
  rdlDealloc : hasInstrs P C.rdlDeallocAddr (rdlDeallocInstrs C)

def checkHbShimsCode (C : HbCliLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  let offShim := (C.rustAllocShimAddr - base).toNat
  let offAlloc := (C.rustAllocAddr - base).toNat
  let offRdlAlloc := (C.rdlAllocAddr - base).toNat
  let offDealloc := (C.rustDeallocAddr - base).toNat
  let offRdlDealloc := (C.rdlDeallocAddr - base).toNat
  decide (base + BitVec.ofNat 64 offShim = C.rustAllocShimAddr ∧
    offShim + 4 * rustAllocShimInstrs.length < 2 ^ 64 ∧
    base + BitVec.ofNat 64 offAlloc = C.rustAllocAddr ∧
    offAlloc + 4 * (rustAllocInstrs C).length < 2 ^ 64 ∧
    base + BitVec.ofNat 64 offRdlAlloc = C.rdlAllocAddr ∧
    offRdlAlloc + 4 * (rdlAllocFastInstrs C).length < 2 ^ 64 ∧
    base + BitVec.ofNat 64 offDealloc = C.rustDeallocAddr ∧
    offDealloc + 4 * (rustDeallocInstrs C).length < 2 ^ 64 ∧
    base + BitVec.ofNat 64 offRdlDealloc = C.rdlDeallocAddr ∧
    offRdlDealloc + 4 * (rdlDeallocInstrs C).length < 2 ^ 64) &&
  checkInstrsAt t offShim rustAllocShimInstrs &&
  checkInstrsAt t offAlloc (rustAllocInstrs C) &&
  checkInstrsAt t offRdlAlloc (rdlAllocFastInstrs C) &&
  checkInstrsAt t offDealloc (rustDeallocInstrs C) &&
  checkInstrsAt t offRdlDealloc (rdlDeallocInstrs C)

theorem hbShimsCode_of_wordTree {P : Program} {C : HbCliLayout} {t : WordTree} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkHbShimsCode C P.base t = true) :
    HbShimsCode P C := by
  unfold checkHbShimsCode at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨⟨hb1, hbd1, hb2, hbd2, hb3, hbd3, hb4, hbd4, hb5, hbd5⟩, hc1⟩, hc2⟩, hc3⟩, hc4⟩, hc5⟩
  exact
    { allocShim  := hasInstrs_of_wordTree n hcode hwf hb1 hbd1 hext hovr hc1
      alloc      := hasInstrs_of_wordTree n hcode hwf hb2 hbd2 hext hovr hc2
      rdlAlloc   := hasInstrs_of_wordTree n hcode hwf hb3 hbd3 hext hovr hc3
      dealloc    := hasInstrs_of_wordTree n hcode hwf hb4 hbd4 hext hovr hc4
      rdlDealloc := hasInstrs_of_wordTree n hcode hwf hb5 hbd5 hext hovr hc5 }

private theorem shim_fetch_at {P : Program} {base off : BitVec 64} {ls : List Instr} {inst : Instr}
    (i : Nat) (h : hasInstrs P base ls)
    (hi : ls[i]? = some inst := by rfl)
    (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P.fetch (base + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have hf := h.fetch_off i off hlt hoff
  rw [List.getElem?_eq_getElem hlt] at hi
  cases hi
  exact hf

private theorem shim_fetch_at0 {P : Program} {base : BitVec 64} {ls : List Instr} {inst : Instr}
    (h : hasInstrs P base ls) (hi : ls[0]? = some inst := by rfl) :
    P.fetch base = some inst := by
  simpa using shim_fetch_at 0 h hi rfl

private theorem allocStatePreserved_of_mallocng {s0 s1 sf : State}
    (hfs : s1.fs = s0.fs) (htr : s1.trace = s0.trace)
    (hsig : s1.sigActions = s0.sigActions) (htp : s1.tpidrEl0 = s0.tpidrEl0)
    (hmem : s1.mem = s0.mem)
    (hm : MallocngStatePreserved s1 sf) :
    AllocStatePreserved s0 sf :=
  ⟨hm.1.trans hfs, hm.2.1.trans htr, hm.2.2.1.trans hsig, hm.2.2.2.1.trans htp,
   hmem ▸ hm.2.2.2.2⟩

/-! ## Subroutine Contracts -/

theorem rustAllocShim_ok {P : Program} {C : HbCliLayout} (hc : HbShimsCode P C) :
    subroutine_ok P C.rustAllocShimAddr hbAllocShimSpec := by
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre _hsp
  refine ⟨emp, hpre, ?_⟩
  have hf0 := shim_fetch_at0 hc.allocShim
  wp_step
  apply SepWP.done
  · rfl
  · exact hrun
  · refine ⟨fun hm => ?_, rfl, (CalleeSavedPreserved_setPC s0 s0 _).mpr (CalleeSavedPreserved.rfl s0)⟩
    dsimp only [hbAllocShimSpec]
    have hstd : StdStatePreserved s0 (s0.setPC (s0.readReg64 (.gpr 30#5))) := by
      cases s0; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    have hkf : s0.mem.KeepsFrozen (s0.setPC (s0.readReg64 (.gpr 30#5))).mem := by
      cases s0; exact Memory.KeepsFrozen.refl _
    exact Satisfies.mono (sepConj_mono_left (Entails.pure_right_only ⟨hstd, hkf⟩ (Entails.refl _))) hm

/-- Under `CanAlloc`, `align ≤ 16` and `align ≤ size` hold, so neither `b.hi` slow-path branch in
    `___rdl_alloc` is taken and `___rust_alloc` tail-calls `malloc(size)`. -/
theorem rustAlloc_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbShimsCode P C)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2) :
    subroutine_ok P C.rustAllocAddr (hbAllocSpec (HbAlloc.ofMallocng M γ CodeInv hCodeInv)) := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  apply subroutine_ok_of_sepWP_init
  rintro ⟨size, align, lc, blk⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbAllocSpec, A, HbAlloc.ofMallocng] at hpre ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, _hlay, hcan_imp⟩, hmem⟩
  have hcan := hcan_imp not_false
  rcases hcan with ⟨hal_pos, hal_dvd16, hal_le_sz, hsz_max, hlc_max, hblk_max⟩
  have hal_le16 : align.toNat ≤ 16 := Nat.le_of_dvd (by decide) hal_dvd16
  rw [sepConj_assoc, sepConj_comm (∃∗ e : BitVec 32, muslErrnoAddr s0 ↦₃₂ e),
      ← sepConj_assoc, sepExists_sepConj_right] at hmem
  rcases (satisfies_sepExists _ _).mp hmem with ⟨e0, hmem_e0⟩
  refine ⟨M.Heap γ lc blk s0 ∗ (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp MallocngStackBytes,
    Satisfies.mono (by sep_entail) hmem_e0, ?_⟩
  have hfa := shim_fetch_at0 hc.alloc
  have hf0 := shim_fetch_at0 hc.rdlAlloc
  have hf1 := shim_fetch_at 1 (off := 0x04#64) hc.rdlAlloc
  have hf2 := shim_fetch_at 2 (off := 0x08#64) hc.rdlAlloc
  have hf3 := shim_fetch_at 3 (off := 0x0c#64) hc.rdlAlloc
  have hf4 := shim_fetch_at 4 (off := 0x10#64) hc.rdlAlloc
  have hf5 := shim_fetch_at 5 (off := 0x14#64) hc.rdlAlloc
  have hf6 := shim_fetch_at 6 (off := 0x18#64) hc.rdlAlloc
  wp_step
  conv in State.setPC _ _ =>
    arg 2
    rw [show C.rustAllocAddr + (C.rdlAllocAddr - C.rustAllocAddr) = C.rdlAllocAddr by bv_omega]
  wp_steps 3
  wp_if hb1
  · exfalso
    simp [BitVec.ult] at hb1
    omega
  · wp_steps 2
    wp_if hb2
    · exfalso
      simp [BitVec.ult] at hb2
      omega
    · wp_steps 2
      apply SepWP.call_subroutine_frame (ret_pc := s0.readReg64 .lr)
        (M.malloc_ok γ) (x := (lc, blk, size.toNat, e0)) (F := emp)
      · change C.rdlAllocAddr + 0x18#64 + (C.mallocng.mallocAddr - (C.rdlAllocAddr + 0x18#64)) =
          C.mallocng.mallocAddr
        bv_omega
      · exact hrun
      · simpa [State.spAligned, wp_norm, arm64_norm] using hsp
      · simp [wp_norm, arm64_norm]
      · intro R' hm_mid
        rw [emp_sepConj]
        refine Satisfies.mono (sepConj_mono_left ?_) hm_mid
        dsimp only [muslErrnoAddr]
        simp only [arm64_norm]
        exact Entails.pure_right ⟨hsz_max, hlc_max, hblk_max⟩
          (sepConj_mono_left (M.heap_transport
            (by simp [arm64_norm]) (by simp [arm64_norm])
            (by simp [arm64_norm]) (fun _ => by simp [arm64_norm])))
      · exact fun _ _ _ h => not_satisfies_false_sepConj h
      · exact fun _ _ _ _ h => not_satisfies_false_sepConj h
      · intro sf hpc_f hrun_f hsp_f hcs_f
        rw [sepConj_emp]
        apply SepWP.pure_elim
        rintro ⟨hmsp, hret_ne, hret16, hret_lt⟩
        apply SepWP.done hpc_f hrun_f
        refine ⟨fun hpost_f => ?_, by simpa [arm64_norm] using hsp_f, ?_⟩
        · have hasp : AllocStatePreserved s0 sf :=
            allocStatePreserved_of_mallocng
              (by simp [arm64_norm])
              (by simp [arm64_norm])
              (by simp [arm64_norm])
              (by simp [arm64_norm])
              (by simp [arm64_norm]) hmsp
          have herr_sf : s0.tpidrEl0 - 0xa4#64 = sf.tpidrEl0 - 0xa4#64 := by
            rw [hasp.2.2.2.1]
          have hmod_al : (sf.readReg64 .x0).toNat % align.toNat = 0 :=
            Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hal_dvd16 hret16)
          dsimp only [muslErrnoAddr, State.writeReg64, State.setPState, State.setPC,
            Reg.x0, Reg.x2, Reg.sp] at hpost_f ⊢
          refine Satisfies.mono (sepConj_mono_left ?_) hpost_f
          simp only [hret_ne, ↓reduceIte, herr_sf]
          refine Entails.trans ?_
            (Entails.pure_right hasp
              (sepConj_mono_right
                (Entails.pure_right ⟨hmod_al, hret_lt⟩
                  (sepConj_mono_right
                    (sepConj_mono_left (Entails.pure_right ⟨hal_pos, hal_dvd16⟩ (Entails.refl _)))))))
          sep_entail
        · refine CalleeSavedPreserved.trans ?_ hcs_f
          simp [CalleeSavedPreserved.iff_regs, wp_norm, arm64_norm]

theorem rustDealloc_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbShimsCode P C)
    (M : MallocngCoreIface P C.mallocng lim) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2) :
    subroutine_ok P C.rustDeallocAddr (hbDeallocSpec (HbAlloc.ofMallocng M γ CodeInv hCodeInv)) := by
  let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, size, align, lc, blk⟩ R s0 hpc hrun hpre hsp
  dsimp only [hbDeallocSpec, A, HbAlloc.ofMallocng] at hpre ⊢
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, _hx1, _hx2, _hlay⟩, hmem⟩
  have hmem_p :
      s0.mem ⊨ ⌜p ≠ 0#64 ∧ p.toNat + size.toNat < 2 ^ 64⌝ ∗
        ((M.Heap γ lc blk s0 ∗ (∃∗ e : BitVec 32, muslErrnoAddr s0 ↦₃₂ e)) ∗
          M.Block γ p size.toNat ∗ memRegion p size.toNat ∗
          stackAt s0.sp MallocngStackBytes ∗ R) := by
    refine Satisfies.mono ?_ hmem
    have hblk := M.block_noWrap γ p size.toNat
    have hdrop_al : (⌜0 < align.toNat ∧ align.toNat ∣ 16⌝ ∗ M.Block γ p size.toNat) ⊢
        ⌜p ≠ 0#64 ∧ p.toNat + size.toNat < 2 ^ 64⌝ ∗ M.Block γ p size.toNat := by
      apply Entails.pure_left
      intro _
      exact hblk
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hdrop_al))) ?_
    sep_entail
  rw [satisfies_pure_sepConj] at hmem_p
  rcases hmem_p with ⟨⟨hp_ne, _⟩, hmem2⟩
  have hmem3 :
      s0.mem ⊨ (∃∗ e : BitVec 32, muslErrnoAddr s0 ↦₃₂ e) ∗
        (M.Heap γ lc blk s0 ∗ M.Block γ p size.toNat ∗ memRegion p size.toNat ∗
          stackAt s0.sp MallocngStackBytes ∗ R) := by
    refine Satisfies.mono (by sep_entail) hmem2
  rw [sepExists_sepConj_left] at hmem3
  rcases (satisfies_sepExists _ _).mp hmem3 with ⟨e0, hmem_e0⟩
  refine ⟨M.Heap γ lc blk s0 ∗ (⌜p ≠ 0#64⌝ ∗ M.Block γ p size.toNat ∗ memRegion p size.toNat) ∗
      (muslErrnoAddr s0 ↦₃₂ e0) ∗ stackAt s0.sp MallocngStackBytes, ?_, ?_⟩
  · refine Satisfies.mono ?_ hmem_e0
    refine Entails.trans (Entails.pure_right hp_ne (Entails.refl _)) ?_
    sep_entail
  · have hf0 := shim_fetch_at0 hc.dealloc
    have hf1 := shim_fetch_at0 hc.rdlDealloc
    wp_step
    conv in State.setPC _ _ =>
      arg 2
      rw [show C.rustDeallocAddr + (C.rdlDeallocAddr - C.rustDeallocAddr) = C.rdlDeallocAddr by bv_omega]
    wp_step
    apply SepWP.call_subroutine_frame (ret_pc := s0.readReg64 .lr)
      (M.free_ok γ) (x := (lc, blk, some size.toNat, e0)) (F := emp)
    · change C.rdlDeallocAddr + (C.mallocng.freeAddr - C.rdlDeallocAddr) = C.mallocng.freeAddr
      bv_omega
    · exact hrun
    · exact hsp
    · rfl
    · intro R' hm_mid
      rw [emp_sepConj]
      refine Satisfies.mono (sepConj_mono_left ?_) hm_mid
      dsimp only [muslErrnoAddr, State.setPC, State.readReg64]
      have hp_eq : s0.readReg64 (.gpr 0#5) = p := hx0
      dsimp only [State.readReg64] at hp_eq
      rw [hp_eq]
      exact sepConj_mono_left (M.heap_transport rfl rfl rfl (fun _ => rfl))
    · exact fun _ _ _ h => not_satisfies_false_sepConj h
    · exact fun _ _ _ _ h => not_satisfies_false_sepConj h
    · intro sf hpc_f hrun_f hsp_f hcs_f
      rw [sepConj_emp]
      apply SepWP.pure_elim
      intro hmsp
      apply SepWP.done hpc_f hrun_f
      refine ⟨fun hpost_f => ?_, hsp_f, hcs_f⟩
      have hasp : AllocStatePreserved s0 sf :=
        allocStatePreserved_of_mallocng rfl rfl rfl rfl rfl hmsp
      have herr_sf : muslErrnoAddr s0 = muslErrnoAddr sf := by
        simp [muslErrnoAddr, hmsp.2.2.2.1]
      dsimp only [muslErrnoAddr, State.setPC] at hpost_f herr_sf ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hpost_f
      rw [herr_sf]
      refine Entails.trans ?_ (Entails.pure_right hasp (Entails.refl _))
      sep_entail

/-! ## Cross-Segment `withCodeInv` Wrappers -/

theorem HbShimsCode.withSvc {P : Program} {C : HbCliLayout} (svc : State → State)
    (h : HbShimsCode P C) : HbShimsCode (P.withSvc svc) C :=
  { allocShim  := fun i hi => by simpa using h.allocShim i hi
    alloc      := fun i hi => by simpa using h.alloc i hi
    rdlAlloc   := fun i hi => by simpa using h.rdlAlloc i hi
    dealloc    := fun i hi => by simpa using h.dealloc i hi
    rdlDealloc := fun i hi => by simpa using h.rdlDealloc i hi }

/-- Lift a hook-free `subroutine_ok Q entry spec` (with `onPanic = ⌜False⌝` and `onExit = ⌜False⌝`)
    to `subroutine_ok P entry (withCodeInv A spec)` across segments whenever `A.CodeInv m` implies
    `Q.CodeLoaded m` and `P`, `Q` share hooks and `svc`. -/
theorem subroutine_ok_withCodeInv_of_other {α : Type} {P Q : Program} {entry : BitVec 64}
    {A : HbAlloc} {spec : Spec α}
    (hcall : subroutine_ok Q entry spec)
    (hext : ∀ pc, Q.externAt? pc = P.externAt? pc)
    (hsvc : Q.svc = P.svc)
    (hcode : ∀ m, A.CodeInv m → Q.CodeLoaded m)
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok P entry (withCodeInv A spec) := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withCodeInv] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre_inner⟩
  refine ⟨spec.pre x s0, hpre_inner, ?_⟩
  apply SepWP.call_subroutine_frame_other (ret_pc := s0.readReg64 .lr)
    hcall hext hsvc (hcode s0.mem hinv) hpc hrun hsp rfl (F := emp)
  · intro R' hm; rwa [emp_sepConj]
  · exact fun R' sf hpan => h_no_panic x R' s0 sf hpan
  · exact fun R' code sf hex => h_no_exit x code R' s0 sf hex
  · intro sf hpc_f hrun_f hsp_f hcs_f _hQL
    rw [sepConj_emp]
    exact SepWP.done hpc_f hrun_f ⟨id, hsp_f, hcs_f⟩

theorem rustAllocShim_withCodeInv_ok {P Q : Program} {C : HbCliLayout} {A : HbAlloc}
    (hc : HbShimsCode Q C)
    (hext : ∀ pc, Q.externAt? pc = P.externAt? pc) (hsvc : Q.svc = P.svc)
    (hcode : ∀ m, A.CodeInv m → Q.CodeLoaded m) :
    subroutine_ok P C.rustAllocShimAddr (withCodeInv A hbAllocShimSpec) :=
  subroutine_ok_withCodeInv_of_other (rustAllocShim_ok hc) hext hsvc hcode

theorem rustAlloc_withCodeInv_ok {P Q : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbShimsCode Q C)
    (M : MallocngCoreIface Q C.mallocng lim) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (hext : ∀ pc, Q.externAt? pc = P.externAt? pc) (hsvc : Q.svc = P.svc)
    (hcode : ∀ m, CodeInv m → Q.CodeLoaded m) :
    let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
    subroutine_ok P C.rustAllocAddr (withCodeInv A (hbAllocSpec A)) :=
  subroutine_ok_withCodeInv_of_other (rustAlloc_ok hc M γ CodeInv hCodeInv) hext hsvc hcode

theorem rustDealloc_withCodeInv_ok {P Q : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbShimsCode Q C)
    (M : MallocngCoreIface Q C.mallocng lim) (γ : GhostName)
    (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    (hext : ∀ pc, Q.externAt? pc = P.externAt? pc) (hsvc : Q.svc = P.svc)
    (hcode : ∀ m, CodeInv m → Q.CodeLoaded m) :
    let A := HbAlloc.ofMallocng M γ CodeInv hCodeInv
    subroutine_ok P C.rustDeallocAddr (withCodeInv A (hbDeallocSpec A)) :=
  subroutine_ok_withCodeInv_of_other (rustDealloc_ok hc M γ CodeInv hCodeInv) hext hsvc hcode

end CaseStudies.Hashbrown.Proofs.StdCli

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.Layout
import all Init.Data.Repr
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.AddressText.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
  (vecU8Buf vecU8BufRest vecU8At_eq_header_buf layoutOk_align1)
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Call-site `inImage` wrappers (`shim2`, `memcpy2`, `decimalInnerSpec`) -/

def decimalInnerSpec (A : RustAlloc) (stk : Nat) : Spec DecimalGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg32 .x1 = x.n⌝ ∗ memRegion x.ret 24 ∗
      stackAt s.sp stk ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecU8 A x.ret (decimalText x.n.toNat) ∗
      stackAt s0.sp stk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem at_shim2_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (session2ShimSpecX.inImage img) :=
  shim_ok_at2_ext_x hC (name := addressTextName)
    (k := ls_rel% "libsignal_cli::stores::address_text"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [(ls_lemma% fnOff "libsignal_cli::stores::address_text"),
            (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])

theorem at_memcpy2_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text" "memcpy"))
      (session2MemcpySpecX.inImage img) :=
  memcpy_ok_at2_ext_x hC (name := addressTextName)
    (k := ls_rel% "libsignal_cli::stores::address_text" "memcpy")
    (by rw [(ls_lemma% fnOff "libsignal_cli::stores::address_text"),
            (ls_stub% "memcpy")])

/-! ## 2. Offset definitions & arithmetic / `SepWPp` combinators -/

def frameOff : BitVec 64 := 4#64
def shimRetOff : BitVec 64 := 76#64
def allocRetOff : BitVec 64 := 92#64
def memcpy0RetOff : BitVec 64 := 112#64
def res0RetOff : BitVec 64 := 144#64
def decRetOff : BitVec 64 := 176#64
def res1RetOff : BitVec 64 := 332#64
def memcpy1RetOff : BitVec 64 := 224#64

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  frameOff shimRetOff allocRetOff memcpy0RetOff res0RetOff decRetOff res1RetOff memcpy1RetOff

def Same {α : Type _} (a b : α) : Prop := a = b

theorem same_eq {α : Type _} {a b : α} (h : Same a b) : a = b := h

theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl _

theorem step_entails {P T T' F Q : SepProp}
    (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : T' ∗ F ⊢ Q) : P ⊢ Q :=
  Entails.trans (hf ▸ sepConj_mono_left hent) h

theorem false_entails (Q : SepProp) : (⌜False⌝ : SepProp) ⊢ Q := by
  rw [← emp_sepConj ⌜False⌝, sepConj_comm]
  exact Entails.pure_left False.elim

theorem onPanic_trace_eq {s0 s sf : State} (htr : s.trace = s0.trace) :
    ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  dsimp only [allocFailedIn]
  rw [htr]
  exact Entails.refl _

theorem decimalText_device_pos :
    ∀ d : BitVec 8, 0 < (decimalText d.toNat).length := by
  decide +kernel

theorem dCap_ne_zero {dCap : BitVec 64} {decLen : Nat}
    (hpos : 0 < decLen) (hle : decLen ≤ dCap.toNat) :
    dCap ≠ 0#64 := by
  intro h
  subst h
  change decLen ≤ 0 at hle
  omega

theorem dCap_beq_zero_false {dCap : BitVec 64} {decLen : Nat}
    (hpos : 0 < decLen) (hle : decLen ≤ dCap.toNat) :
    (dCap == 0#64) = false :=
  beq_false_of_ne (dCap_ne_zero hpos hle)

theorem pure_true_emp {P : Prop} (h : P) : (⌜P⌝ : SepProp) = emp := by
  simp only [h, pure_true]

theorem vecU8Buf_close_slice (A : RustAlloc) (cap ptr : BitVec 64)
    (bs extra : List (BitVec 8))
    (hle : bs.length + extra.length ≤ cap.toNat)
    (hpos : 0 < bs.length + extra.length)
    (h63 : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ extra) ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + extra.length))
        (cap.toNat - (bs.length + extra.length)) ⊢
      vecU8Buf A cap ptr (bs ++ extra) := by
  have hne0 : cap ≠ 0 := by
    intro h; subst h; change bs.length + extra.length ≤ 0 at hle; omega
  have hlen : (bs ++ extra).length = bs.length + extra.length := List.length_append
  unfold vecU8Buf
  simp only [hne0, hlen, ↓reduceIte]
  rw [pure_true_emp ⟨hle, h63, hptr⟩, emp_sepConj, pointsToBytes_append]
  apply entails_of_eq
  ac_rfl

theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem sepWPp_fold {prog : Program} {ret : BitVec 64} {s : State}
    {P T T' F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : SepWPp prog ret s (T' ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_weaken_pre (hf ▸ sepConj_mono_left hent) h

theorem sepWPp_exists_elim {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {F : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a : α, SepWPp prog ret s (F a) Q Qp) :
    SepWPp prog ret s (∃∗ a : α, F a) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hm⟩
  exact h a R hm hL

theorem sepWPp_of_sepWP_inv {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P
      (fun sm Pm => img.FrozenLoaded sm → sm.symtab = img.symtab →
        SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  Prost.SepWPp.of_sepWP_cs
    (SepWP.mono h fun _ _ _ _ hcont hstep =>
      let ⟨hfz', hsym'⟩ := hstep img ⟨hfz, hsym⟩
      hcont hfz' hsym')

def preservedTailRegs (s : State) :=
  (s.readReg64 .x25, s.readReg64 .x26, s.readReg64 .x27, s.readReg64 .x28, calleeSavedVRegs s)

theorem preservedTailRegs_mk {s s0 : State}
    (h25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (h26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (h27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (h28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0) :
    preservedTailRegs s = preservedTailRegs s0 := by
  simp only [preservedTailRegs, h25, h26, h27, h28, hv]

theorem preservedTailRegs_of_cs {s0 s1 : State} (h : CalleeSavedPreserved s0 s1) :
    preservedTailRegs s1 = preservedTailRegs s0 :=
  preservedTailRegs_mk
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2

theorem preservedTailRegs_elim {s s0 : State} (h : preservedTailRegs s = preservedTailRegs s0) :
    s.readReg64 .x25 = s0.readReg64 .x25 ∧
    s.readReg64 .x26 = s0.readReg64 .x26 ∧
    s.readReg64 .x27 = s0.readReg64 .x27 ∧
    s.readReg64 .x28 = s0.readReg64 .x28 ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 := by
  simpa only [preservedTailRegs, Prod.mk.injEq] using h

theorem preservedTailRegs_step {s0 s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2)
    (h25 : s1.readReg64 .x25 = s0.readReg64 .x25)
    (h26 : s1.readReg64 .x26 = s0.readReg64 .x26)
    (h27 : s1.readReg64 .x27 = s0.readReg64 .x27)
    (h28 : s1.readReg64 .x28 = s0.readReg64 .x28)
    (hv : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    preservedTailRegs s2 = preservedTailRegs s0 :=
  (preservedTailRegs_of_cs hcs).trans (preservedTailRegs_mk h25 h26 h27 h28 hv)

theorem calleeSaved_vregs {s0 s1 : State} (h : CalleeSavedPreserved s0 s1) :
    calleeSavedVRegs s1 = calleeSavedVRegs s0 :=
  h.2.2.2.2.2.2.2.2.2.2.2

theorem calleeSaved_trans {s0 s1 s2 : State}
    (h1 : CalleeSavedPreserved s0 s1) (h2 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  rcases h1 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
  rcases h2 with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8, b9.trans a9, b10.trans a10, b11.trans a11, b12.trans a12⟩

theorem call_inImage_addr {α : Type} {img : Obj.Image} {A : RustAlloc} {stk : Nat}
    {prog : Program} {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α}
    {x0 : AddrTextGhost} {s0 s : State} {P T F R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre_eq : spec.pre x s = T)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).onPanic x0 s0 sf ∗ R)))
    (hP : P = T ∗ F := by
      (conv_lhs => simp (config := { failIfUnchanged := false }) only [arm64_norm, *]); sep_focus)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).onPanic x0 s0 sf ∗ R)) := by
  have hspec : spec.pre x s = ⌜True⌝ ∗ T := by
    rw [pure_true, emp_sepConj]; exact hpre_eq
  refine SepWPp.call_inImage_frame (x := x) (φ := True) (T := T) (F := F)
    hcall hfz hsym hpc hrun hsp hlr hspec trivial hP ?_ ?_ hnext ?_
  · intro sf code R' _ hm
    rw [hexit_eq] at hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    dsimp only [addrTextSpec, Spec.inImage]
    have hm' : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left (hpan sf))) hm
    exact allowPanic_frame id hm'
  · intro sf R' _ hm
    rw [hoom_eq] at hm
    exact (not_satisfies_false_sepConj hm).elim

/-! ## 3. Segment 1 (`4 .. 140`): register saves + `name.to_owned()` up to first `cliDoReserve` -/

theorem step_prologue_to_owned {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {subStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hext_le : extHookStack ≤ subStk) (hsub64 : subStk ≤ 2 ^ 64)
    {x : AddrTextGhost} {R Fr : SepProp} {s0 s : State} {sp' : BitVec 64}
    {Q : State → SepProp → Prop}
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName + frameOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp')
    (hsp_al : (sp' &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = x.ret)
    (hx1 : s.readReg64 .x1 = x.addr)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx21 : s.readReg64 .x21 = s0.readReg64 .x21)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx29 : s.readReg64 .x29 = s0.readReg64 .x29)
    (hx30 : s.readReg64 .x30 = s0.readReg64 .x30)
    (hvregs : preservedTailRegs s = preservedTailRegs s0)
    (hlen32 : x.g.name.bytes.length < 2 ^ 32)
    {w0 w1 w2 w19 w20 w21 w22 w23 w24 w30 w29 : BitVec 64}
    (hnext : ∀ (sm : State) (p0 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName +
        bv% (2 ^ 64 +
          (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") -
          (ls_off% "libsignal_cli::stores::address_text")) →
      sm.status = .Running →
      sm.sp = sp' →
      sm.trace = s0.trace →
      sm.readReg64 .lr =
        (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName + res0RetOff →
      sm.readReg64 .x0 = sp' →
      sm.readReg64 .x1 = BitVec.ofNat 64 x.g.name.bytes.length →
      sm.readReg64 .x2 = 1#64 →
      sm.readReg64 .x3 = 1#64 →
      sm.readReg64 .x4 = 1#64 →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = x.addr →
      preservedTailRegs sm = preservedTailRegs s0 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) sm
        (vecU8At A sp' (BitVec.ofNat 64 x.g.name.bytes.length) p0 x.g.name.bytes ∗
          addrCalleeSavedAt sp' s0 ∗
          ((x.addr + 8#64) ↦₆₄ x.g.name.ptr) ∗
          ((x.addr + 16#64) ↦₆₄ BitVec.ofNat 64 x.g.name.bytes.length) ∗
          (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗
          ((x.addr + 24#64) ↦₈ x.g.device) ∗
          stackAt sp' subStk ∗ A.pool ∗ Fr)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (((sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ w2)) ∗
        (((sp' + 48#64) ↦₆₄ w29) ∗ ((sp' + 56#64) ↦₆₄ w30) ∗
          ((sp' + 64#64) ↦₆₄ w24) ∗ ((sp' + 72#64) ↦₆₄ w23) ∗
          ((sp' + 80#64) ↦₆₄ w22) ∗ ((sp' + 88#64) ↦₆₄ w21) ∗
          ((sp' + 96#64) ↦₆₄ w20) ∗ ((sp' + 104#64) ↦₆₄ w19)) ∗
        ((x.addr + 8#64) ↦₆₄ x.g.name.ptr) ∗
        ((x.addr + 16#64) ↦₆₄ BitVec.ofNat 64 x.g.name.bytes.length) ∗
        (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗
        ((x.addr + 24#64) ↦₈ x.g.device) ∗
        stackAt sp' subStk ∗ A.pool ∗ Fr)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).onPanic x s0 sf ∗ R)) := by
  obtain ⟨hx25, hx26, hx27, hx28, hvregs0⟩ := preservedTailRegs_elim hvregs
  have hshim := at_shim2_ok hC
  have halloc := at_alloc_ok hC
  have hmemcpy := at_memcpy2_ok hC
  have hpan := at_handleError_panic (img := img) (ext := ext)
  code_fetches_range CryptoVerification.libsignalSessionCode addrTextBin
    img.base (Rust.withPanics ext) addressText_fnOff
    (ls_off% "libsignal_cli::stores::address_text") 4 140
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName = entry
  examples_hide_fetches
  have h63 : (BitVec.ofNat 64 x.g.name.bytes.length)[63] = false :=
    ofNat_getElem_63_false (by omega)
  have h63' : (BitVec.ofNat 64 x.g.name.bytes.length).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by omega)
  by_cases hzero : x.g.name.bytes.length = 0
  · have hbs0 : x.g.name.bytes = [] := List.eq_nil_of_length_eq_zero hzero
    rw [hbs0]
    refine sepWPp_of_sepWP_inv hfz hsym
      (mid := entry + bv% (2 ^ 64 +
        (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") -
        (ls_off% "libsignal_cli::stores::address_text"))) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
    intro hfz1 hsym1
    have hv : vecU8At A sp' 0#64 1#64 [] =
        vecU8At A sp' (BitVec.ofNat 64 x.g.name.bytes.length) 1#64 x.g.name.bytes := by
      rw [hbs0]; rfl
    refine sepWPp_weaken_pre ?_ (hnext _ 1#64
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by rw [hbs0]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (preservedTailRegs_mk
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *]))
      hfz1 hsym1)
    rw [← hv, hbs0]
    unfold addrCalleeSavedAt
    refine Entails.trans ?_
      (sepConj_mono_left (vecU8At_zero_init A sp'))
    simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
    apply entails_of_eq
    ac_rfl
  · have hpos : 0 < x.g.name.bytes.length := Nat.pos_of_ne_zero hzero
    have hne_beq : (BitVec.ofNat 64 x.g.name.bytes.length == 0#64) = false :=
      ofNat_beq_zero_false hpos (by omega)
    refine sepWPp_of_sepWP_inv hfz hsym
      (mid := entry + BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2")) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
    intro hfz1 hsym1
    rw [stackAt_sub_le sp' hext_le hsub64]
    refine call_inImage_addr (x := ()) hshim hfz1 hsym1
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := entry + shimRetOff)
      (by simp only [arm64_norm, *])
      (T := stackAt sp' extHookStack)
      (by dsimp [session2ShimSpecX]; simp only [arm64_norm, *])
      (fun _ => false_entails _) ?_
    intro s2 hpc2 hrun2 hsp2 hcs2 hfz2 hsym2
    dsimp only [session2ShimSpecX]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun htr2 => ?_
    have hsp2' : s2.sp = sp' := by rw [hsp2]; simp only [arm64_norm, *]
    have htr2' : s2.trace = s0.trace := by rw [htr2]; simp only [arm64_norm, *]
    have hx19_2 : s2.readReg64 .x19 = x.ret := by rw [hcs2.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = x.addr := by rw [hcs2.2.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 x.g.name.bytes.length := by
      rw [hcs2.2.2.1]; simp only [arm64_norm, *]
    have hx23_2 : s2.readReg64 .x23 = x.g.name.ptr := by
      rw [hcs2.2.2.2.2.1]; simp only [arm64_norm, *]
    obtain ⟨hx25_2, hx26_2, hx27_2, hx28_2, hvregs_2⟩ :=
      preservedTailRegs_elim (preservedTailRegs_step (s0 := s0) hcs2
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *]))
    refine sepWPp_of_sepWP_inv hfz2 hsym2
      (mid := entry + BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text"
        "__rustc::__rust_alloc")) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
    intro hfz3 hsym3
    have htoNat_len : (BitVec.ofNat 64 x.g.name.bytes.length).toNat = x.g.name.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlay_len : LayoutOk x.g.name.bytes.length 1 := layoutOk_align1 hpos (by omega)
    refine call_inImage_addr (x := (x.g.name.bytes.length, 1)) halloc hfz3 hsym3
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := entry + allocRetOff)
      (by simp only [arm64_norm, *])
      (T := A.pool ∗ stackAt sp' extHookStack)
      (by
        apply same_eq
        dsimp [rustAllocSpecWithStack]
        simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
        unfold Same
        ac_rfl)
      (fun _ => false_entails _) ?_
    intro s4 hpc4 hrun4 hsp4 hcs4 hfz4 hsym4
    have hsp4' : s4.sp = sp' := by rw [hsp4]; simp only [arm64_norm, *]
    have hx19_4 : s4.readReg64 .x19 = x.ret := by rw [hcs4.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = x.addr := by rw [hcs4.2.1]; simp only [arm64_norm, *]
    have hx21_4 : s4.readReg64 .x21 = BitVec.ofNat 64 x.g.name.bytes.length := by
      rw [hcs4.2.2.1]; simp only [arm64_norm, *]
    have hx23_4 : s4.readReg64 .x23 = x.g.name.ptr := by
      rw [hcs4.2.2.2.2.1]; simp only [arm64_norm, *]
    obtain ⟨hx25_4, hx26_4, hx27_4, hx28_4, hvregs_4⟩ :=
      preservedTailRegs_elim (preservedTailRegs_step (s0 := s0) hcs4
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *]))
    dsimp only [rustAllocSpecWithStack]
    by_cases hnull : s4.readReg64 .x0 = 0#64
    · simp only [↓reduceIte, arm64_norm, *]
      refine SepWPp.pure_left fun htr4 => ?_
      have hnull_beq : (s4.readReg64 .x0 == 0#64) = true := beq_iff_eq.mpr hnull
      refine sepWPp_of_sepWP_inv hfz4 hsym4
        (mid := entry + BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text"
          "alloc::raw_vec::handle_error")) ?_
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
      intro _ _
      refine SepWPp.panic (by simp only [arm64_norm, *]) ?_ ?_
      · simp only [arm64_norm, *]
      · intro hm_pan
        dsimp only [addrTextSpec, Spec.inImage]
        exact allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, *])) hm_pan
    · have hnull' : s4.readReg64 .x0 ≠ 0 := hnull
      have hnull_beq : (s4.readReg64 .x0 == 0#64) = false := beq_false_of_ne hnull
      simp only [↓reduceIte, arm64_norm, *]
      refine SepWPp.pure_left fun ⟨_, htr4'⟩ => ?_
      refine sepWPp_of_sepWP_inv hfz4 hsym4
        (mid := entry + BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text" "memcpy")) ?_
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
      intro hfz5 hsym5
      refine call_inImage_addr (x := (s4.readReg64 .x0, x.g.name.ptr, x.g.name.bytes))
        hmemcpy hfz5 hsym5
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, *])
        (ret_pc := entry + memcpy0RetOff)
        (by simp only [arm64_norm, *])
        (T := memRegion (s4.readReg64 .x0) x.g.name.bytes.length ∗
          (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗ stackAt sp' extHookStack)
        (by
          apply same_eq
          dsimp [session2MemcpySpecX]
          simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
          unfold Same
          ac_rfl)
        (fun _ => false_entails _) ?_
      intro s6 hpc6 hrun6 hsp6 hcs6 hfz6 hsym6
      dsimp only [session2MemcpySpecX]
      rw [sepConj_assoc]
      refine SepWPp.pure_left fun ⟨_, htr6⟩ => ?_
      have hsp6' : s6.sp = sp' := by rw [hsp6]; simp only [arm64_norm, *]
      have htr6' : s6.trace = s0.trace := by rw [htr6]; simp only [arm64_norm, *]
      have hx19_6 : s6.readReg64 .x19 = x.ret := by rw [hcs6.1]; simp only [arm64_norm, *]
      have hx20_6 : s6.readReg64 .x20 = x.addr := by rw [hcs6.2.1]; simp only [arm64_norm, *]
      have hx21_6 : s6.readReg64 .x21 = BitVec.ofNat 64 x.g.name.bytes.length := by
        rw [hcs6.2.2.1]; simp only [arm64_norm, *]
      have hx22_6 : s6.readReg64 .x22 = s4.readReg64 .x0 := by
        rw [hcs6.2.2.2.1]; simp only [arm64_norm, *]
      obtain ⟨hx25_6, hx26_6, hx27_6, hx28_6, hvregs_6⟩ :=
        preservedTailRegs_elim (preservedTailRegs_step (s0 := s0) hcs6
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [calleeSavedVRegs, arm64_norm, *]))
      refine sepWPp_of_sepWP_inv hfz6 hsym6
        (mid := entry + bv% (2 ^ 64 +
          (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") -
          (ls_off% "libsignal_cli::stores::address_text"))) ?_
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
      intro hfz7 hsym7
      refine sepWPp_weaken_pre ?_ (hnext _ (s4.readReg64 .x0)
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (preservedTailRegs_mk
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [calleeSavedVRegs, arm64_norm, *]))
        hfz7 hsym7)
      rw [stackAt_sub_le sp' hext_le hsub64]
      unfold addrCalleeSavedAt
      apply step_entails
        (vecU8At_pos_init A sp' (s4.readReg64 .x0) x.g.name.bytes hpos (by omega) hnull)
        (by (conv_lhs => simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
      simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
      apply entails_of_eq
      ac_rfl

/-! ## 4. Segment 2 (`140 .. 176`): `cliDoReserve` + `"."` + `decimal(device)` -/

theorem step_dot_and_decimal {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack decStk subStk stk : Nat}
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hres_le : resStack ≤ subStk) (hdec_le : decStk ≤ subStk) (hsub64 : subStk ≤ 2 ^ 64)
    {x : AddrTextGhost} {R Fr : SepProp} {s0 s : State} {sp' p0 : BitVec 64}
    {Q : State → SepProp → Prop}
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName +
      bv% (2 ^ 64 +
        (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") -
        (ls_off% "libsignal_cli::stores::address_text")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp')
    (hsp_al : (sp' &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr =
      (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName + res0RetOff)
    (hx0 : s.readReg64 .x0 = sp')
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 x.g.name.bytes.length)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.addr)
    (hvregs : preservedTailRegs s = preservedTailRegs s0)
    (hlen32 : x.g.name.bytes.length < 2 ^ 32)
    (hnext : ∀ (sm : State) (cap1 p1 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName + decRetOff →
      sm.status = .Running →
      sm.sp = sp' →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      preservedTailRegs sm = preservedTailRegs s0 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      cap1.toNat < 2 ^ 34 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) sm
        (vecU8At A sp' cap1 p1 (x.g.name.bytes ++ [0x2e#8]) ∗
          vecU8 A (sp' + 24#64) (decimalText (x.g.device.zeroExtend 32).toNat) ∗
          ((x.addr + 24#64) ↦₈ x.g.device) ∗
          stackAt sp' subStk ∗ A.pool ∗ Fr)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (vecU8At A sp' (BitVec.ofNat 64 x.g.name.bytes.length) p0 x.g.name.bytes ∗
        memRegion (sp' + 24#64) 24 ∗
        ((x.addr + 24#64) ↦₈ x.g.device) ∗
        stackAt sp' subStk ∗ A.pool ∗ Fr)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).onPanic x s0 sf ∗ R)) := by
  have hdoRes := at_doReserve_ok hRes
  have hdecCall : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName +
        BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text"
          "libsignal_cli::stores::decimal"))
      ((decimalInnerSpec A decStk).inImage img) :=
    at_decimal_ok hDec
  code_fetches_range CryptoVerification.libsignalSessionCode addrTextBin
    img.base (Rust.withPanics ext) addressText_fnOff
    (ls_off% "libsignal_cli::stores::address_text") 144 32
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName = entry
  examples_hide_fetches
  have htoNat_len : (BitVec.ofNat 64 x.g.name.bytes.length).toNat = x.g.name.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hcap1_lt34, hlen_lt_cap1, hres1_bound⟩ := reserveCap1_bounds hlen32
  have h1_toNat : (1#64).toNat = 1 := rfl
  have hres1_bound63 : reserveCap x.g.name.bytes.length x.g.name.bytes.length 1 + 1 ≤ 9223372036854775808 :=
    hres1_bound
  rw [stackAt_sub_le sp' hres_le hsub64]
  refine call_inImage_addr
    (x := DoReserveCall.mk sp' (BitVec.ofNat 64 x.g.name.bytes.length)
      p0 x.g.name.bytes 1)
    hdoRes hfz hsym hpc hrun
    (by simp only [State.spAligned, *])
    hlr
    (T := vecU8At A sp' (BitVec.ofNat 64 x.g.name.bytes.length) p0 x.g.name.bytes ∗
      A.pool ∗ stackAt sp' resStack)
    (by
      apply same_eq
      dsimp [SpqrV1.Varint.doReserveSpecOf]
      simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
      unfold Same
      ac_rfl)
    (fun _ => onPanic_trace_eq htr)
    ?_
  intro s1 hpc1 hrun1 hsp1 hcs1 hfz1 hsym1
  dsimp only [SpqrV1.Varint.doReserveSpecOf]
  rw [hsp, sepConj_assoc]
  refine SepWPp.pure_left fun htr1 => ?_
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hsp1' : s1.sp = sp' := by rw [hsp1, hsp]
  have hx19_1 : s1.readReg64 .x19 = x.ret := hcs1.1.trans hx19
  have hx20_1 : s1.readReg64 .x20 = x.addr := hcs1.2.1.trans hx20
  obtain ⟨hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ :=
    preservedTailRegs_elim ((preservedTailRegs_of_cs hcs1).trans hvregs)
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim fun p1 => ?_
  set cap1 : BitVec 64 := BitVec.ofNat 64 (reserveCap x.g.name.bytes.length x.g.name.bytes.length 1)
  have hcap1_eq : (BitVec.ofNat 64
      (reserveCap (BitVec.ofNat 64 x.g.name.bytes.length).toNat x.g.name.bytes.length 1)) = cap1 := by
    rw [htoNat_len]
  rw [hcap1_eq]
  have hcap1_toNat : cap1.toNat = reserveCap x.g.name.bytes.length x.g.name.bytes.length 1 := by
    dsimp [cap1]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt1 : x.g.name.bytes.length < cap1.toNat := by omega
  apply sepWPp_fold (vecU8At_open_one A sp' cap1 p1 x.g.name.bytes hlt1) (by sep_focus)
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨h63_1, hp1⟩ => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun b0 => ?_
  have hadd1 : BitVec.ofNat 64 x.g.name.bytes.length + 1#64 =
      BitVec.ofNat 64 (x.g.name.bytes.length + 1) := by
    rw [← BitVec.ofNat_add]
  refine sepWPp_of_sepWP_inv hfz1 hsym1
    (mid := entry + BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text"
      "libsignal_cli::stores::decimal")) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
  intro hfz2 hsym2
  refine sepWPp_weaken_pre (P' :=
      vecU8At A sp' cap1 p1 (x.g.name.bytes ++ [0x2e#8]) ∗
        memRegion (sp' + 24#64) 24 ∗
        ((x.addr + 24#64) ↦₈ x.g.device) ∗
        stackAt sp' subStk ∗ A.pool ∗ Fr) ?_ ?_
  · rw [stackAt_sub_le sp' hres_le hsub64]
    apply step_entails
      (vecU8At_close_one A sp' cap1 p1 x.g.name.bytes 0x2e#8 hlt1 h63_1 hp1)
      (by (conv_lhs => simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
    simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
    apply entails_of_eq
    ac_rfl
  rw [stackAt_sub_le sp' hdec_le hsub64]
  refine call_inImage_addr
    (x := DecimalGhost.mk (x.g.device.zeroExtend 32) (sp' + 24#64))
    hdecCall hfz2 hsym2
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, *])
    (ret_pc := entry + decRetOff)
    (by simp only [arm64_norm, *])
    (T := memRegion (sp' + 24#64) 24 ∗ stackAt sp' decStk ∗ A.pool)
    (by
      apply same_eq
      dsimp [decimalInnerSpec]
      simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
      unfold Same
      ac_rfl)
    (fun _ => onPanic_trace_eq (by simp only [arm64_norm, *]))
    ?_
  intro s3 hpc3 hrun3 hsp3 hcs3 hfz3 hsym3
  dsimp only [decimalInnerSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun htr3 => ?_
  have htr3' : s3.trace = s0.trace := by rw [htr3]; simp only [arm64_norm, *]
  have hsp3' : s3.sp = sp' := by rw [hsp3]; simp only [arm64_norm, *]
  have hx19_3 : s3.readReg64 .x19 = x.ret := by rw [hcs3.1]; simp only [arm64_norm, *]
  have hvregs_3 : preservedTailRegs s3 = preservedTailRegs s0 :=
    preservedTailRegs_step hcs3
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [calleeSavedVRegs, arm64_norm, *])
  refine sepWPp_weaken_pre ?_
    (hnext s3 cap1 p1 hpc3 hrun3 hsp3' htr3' hx19_3 hvregs_3 hfz3 hsym3 (by omega))
  rw [stackAt_sub_le sp' hdec_le hsub64]
  simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
  apply entails_of_eq
  ac_rfl

end CryptoVerification.SignalSession.Cli.AddressText.Helpers

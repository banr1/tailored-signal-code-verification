/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.Steps
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup

/-!
# Relocatable `[LibsignalPlacement]` `signal_session::stores::address_text` (Block `594`)
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.AddressText.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap hiding vecU8Buf
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.LibsignalTripleRatchet.Wire
  (vecU8Buf vecU8BufRest vecU8At_eq_header_buf layoutOk_align1)
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification CryptoVerification.LibsignalPublicApi CryptoVerification.SignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  frameOff shimRetOff allocRetOff memcpy0RetOff res0RetOff decRetOff res1RetOff memcpy1RetOff

/-! ## 1. `SepWPp` Call Helper for `StoreKit.withLsCodeRoLoaded` -/

private theorem call_lscro_addr [LibsignalPlacement] {α : Type} {A : RustAlloc} {stk : Nat}
    {prog : Program} {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α}
    {x0 : AddrTextGhost} {s0 s : State} {P T F R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre_eq : spec.pre x s = T)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (addrTextSpecPlaced A stk).onPanic x0 s0 sf ∗ R)))
    (hP : P = T ∗ F := by
      (conv_lhs => simp (config := { failIfUnchanged := false }) only [arm64_norm, *]); sep_focus)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (addrTextSpecPlaced A stk).onPanic x0 s0 sf ∗ R)) := by
  refine SepWPp.call_lscro (x := x) (F := F)
    hcall hcrl hpc hrun hsp hlr ?_ ?_ ?_ hnext ?_
  · intro R' hm
    rw [hP, ← hpre_eq, sepConj_assoc] at hm
    exact hm
  · intro sf code R' _ hm
    rw [hexit_eq] at hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    have hm' : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left (hpan sf))) hm
    exact allowPanic_frame id hm'
  · intro R' sf _ hm
    rw [hoom_eq] at hm
    exact (not_satisfies_false_sepConj hm).elim

/-! ## 2. Segment 1 (`4 .. 140`): register saves + `name.to_owned()` up to first `cliDoReserve` -/

private theorem step_prologue_to_owned_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {subStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hext_le : extHookStack ≤ subStk) (hsub64 : subStk ≤ 2 ^ 64)
    {x : AddrTextGhost} {R Fr : SepProp} {s0 s : State} {sp' : BitVec 64}
    {Q : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_594).base + frameOff)
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
      sm.pc = lsmpl.base 561 →
      sm.status = .Running →
      sm.sp = sp' →
      sm.trace = s0.trace →
      sm.readReg64 .lr = (blkPl_594).base + res0RetOff →
      sm.readReg64 .x0 = sp' →
      sm.readReg64 .x1 = BitVec.ofNat 64 x.g.name.bytes.length →
      sm.readReg64 .x2 = 1#64 →
      sm.readReg64 .x3 = 1#64 →
      sm.readReg64 .x4 = 1#64 →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = x.addr →
      preservedTailRegs sm = preservedTailRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_594 H) (s0.readReg64 .lr) sm
        (vecU8At A sp' (BitVec.ofNat 64 x.g.name.bytes.length) p0 x.g.name.bytes ∗
          addrCalleeSavedAt sp' s0 ∗
          ((x.addr + 8#64) ↦₆₄ x.g.name.ptr) ∗
          ((x.addr + 16#64) ↦₆₄ BitVec.ofNat 64 x.g.name.bytes.length) ∗
          (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗
          ((x.addr + 24#64) ↦₈ x.g.device) ∗
          stackAt sp' subStk ∗ A.pool ∗ Fr)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (addrTextSpecPlaced A stk).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_594 H) (s0.readReg64 .lr) s
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
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (addrTextSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  obtain ⟨hx25, hx26, hx27, hx28, hvregs0⟩ := preservedTailRegs_elim hvregs
  have hshim := shim_lscro_of_cli (callerProg := lsProg_594 H) (stk := extHookStack) hC
  have halloc := alloc_lscro_of_cli (callerProg := lsProg_594 H) hC
  have hmemcpy := session_memcpy_region_lscro_of_cli (callerProg := lsProg_594 H)
    (stk := extHookStack) hC
  have hpanic : (lsProg_594 H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked :=
    ls_panicAt_of_cliPanic hpan
  have h63 : (BitVec.ofNat 64 x.g.name.bytes.length)[63] = false :=
    ofNat_getElem_63_false (by omega)
  have h63' : (BitVec.ofNat 64 x.g.name.bytes.length).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by omega)
  by_cases hzero : x.g.name.bytes.length = 0
  · have hbs0 : x.g.name.bytes = [] := List.eq_nil_of_length_eq_zero hzero
    rw [hbs0]
    apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 561) hcrl
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
    intro hcrl1
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
      hcrl1)
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
    apply StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
    intro hcrl1
    rw [stackAt_sub_le sp' hext_le hsub64]
    refine call_lscro_addr (x := ()) hshim hcrl1
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := (blkPl_594).base + shimRetOff)
      (by simp only [arm64_norm, *])
      (T := stackAt sp' extHookStack)
      (by dsimp [withStack, sessionShimSpec]; simp only [emp_sepConj, arm64_norm, *])
      (fun _ => false_entails _) ?_
    intro s2 hpc2 hrun2 hsp2 hcs2 hcrl2
    dsimp only [withStack, sessionShimSpec]
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
    apply StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl2
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
    intro hcrl3
    have htoNat_len : (BitVec.ofNat 64 x.g.name.bytes.length).toNat = x.g.name.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlay_len : LayoutOk x.g.name.bytes.length 1 := layoutOk_align1 hpos (by omega)
    refine call_lscro_addr (x := (x.g.name.bytes.length, 1)) halloc hcrl3
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := (blkPl_594).base + allocRetOff)
      (by simp only [arm64_norm, *])
      (T := A.pool ∗ stackAt sp' extHookStack)
      (by
        apply same_eq
        dsimp [rustAllocSpecWithStack]
        simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
        unfold Same
        ac_rfl)
      (fun _ => false_entails _) ?_
    intro s4 hpc4 hrun4 hsp4 hcs4 hcrl4
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
      apply StoreKit.sepWPp_seq_lscro
        (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") hcrl4
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
      intro _
      refine SepWPp.panic (by simp only [arm64_norm, *]) ?_ ?_
      · simp only [arm64_norm, *]
      · intro hm_pan
        exact allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, *])) hm_pan
    · have hnull' : s4.readReg64 .x0 ≠ 0 := hnull
      have hnull_beq : (s4.readReg64 .x0 == 0#64) = false := beq_false_of_ne hnull
      simp only [↓reduceIte, arm64_norm, *]
      refine SepWPp.pure_left fun ⟨_, htr4'⟩ => ?_
      apply StoreKit.sepWPp_seq_lscro (mid := lsρ memcpyName) hcrl4
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
      intro hcrl5
      refine call_lscro_addr (x := (s4.readReg64 .x0, x.g.name.ptr, x.g.name.bytes))
        hmemcpy hcrl5
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, *])
        (ret_pc := (blkPl_594).base + memcpy0RetOff)
        (by simp only [arm64_norm, *])
        (T := memRegion (s4.readReg64 .x0) x.g.name.bytes.length ∗
          (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗ stackAt sp' extHookStack)
        (by
          apply same_eq
          dsimp [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
          simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
          unfold Same
          ac_rfl)
        (fun _ => false_entails _) ?_
      intro s6 hpc6 hrun6 hsp6 hcs6 hcrl6
      dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
      simp only [sepConj_assoc]
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
      apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 561) hcrl6
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
      intro hcrl7
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
        hcrl7)
      rw [stackAt_sub_le sp' hext_le hsub64]
      unfold addrCalleeSavedAt
      apply step_entails
        (vecU8At_pos_init A sp' (s4.readReg64 .x0) x.g.name.bytes hpos (by omega) hnull)
        (by (conv_lhs => simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
      simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
      apply entails_of_eq
      ac_rfl

/-! ## 3. Segment 2 (`140 .. 176`): `cliDoReserve` + `"."` + `decimal(device)` -/

private theorem step_dot_and_decimal_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack decStk subStk stk : Nat}
    (hdoRes : subroutine_ok (lsProg_594 H) (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hdecCall : subroutine_ok (lsProg_594 H) (lsmpl.base 597)
      (StoreKit.withLsCodeRoLoaded lsmpl (decimalInnerSpec A decStk)))
    (hres_le : resStack ≤ subStk) (hdec_le : decStk ≤ subStk) (hsub64 : subStk ≤ 2 ^ 64)
    {x : AddrTextGhost} {R Fr : SepProp} {s0 s : State} {sp' p0 : BitVec 64}
    {Q : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 561)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp')
    (hsp_al : (sp' &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = (blkPl_594).base + res0RetOff)
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
      sm.pc = (blkPl_594).base + decRetOff →
      sm.status = .Running →
      sm.sp = sp' →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      preservedTailRegs sm = preservedTailRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      cap1.toNat < 2 ^ 34 →
      SepWPp (lsProg_594 H) (s0.readReg64 .lr) sm
        (vecU8At A sp' cap1 p1 (x.g.name.bytes ++ [0x2e#8]) ∗
          vecU8 A (sp' + 24#64) (decimalText (x.g.device.zeroExtend 32).toNat) ∗
          ((x.addr + 24#64) ↦₈ x.g.device) ∗
          stackAt sp' subStk ∗ A.pool ∗ Fr)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (addrTextSpecPlaced A stk).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_594 H) (s0.readReg64 .lr) s
      (vecU8At A sp' (BitVec.ofNat 64 x.g.name.bytes.length) p0 x.g.name.bytes ∗
        memRegion (sp' + 24#64) 24 ∗
        ((x.addr + 24#64) ↦₈ x.g.device) ∗
        stackAt sp' subStk ∗ A.pool ∗ Fr)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (addrTextSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  have htoNat_len : (BitVec.ofNat 64 x.g.name.bytes.length).toNat = x.g.name.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hcap1_lt34, hlen_lt_cap1, hres1_bound⟩ := reserveCap1_bounds hlen32
  have h1_toNat : (1#64).toNat = 1 := rfl
  have hres1_bound63 : reserveCap x.g.name.bytes.length x.g.name.bytes.length 1 + 1 ≤
      9223372036854775808 :=
    hres1_bound
  rw [stackAt_sub_le sp' hres_le hsub64]
  refine call_lscro_addr
    (x := DoReserveCall.mk sp' (BitVec.ofNat 64 x.g.name.bytes.length)
      p0 x.g.name.bytes 1)
    hdoRes hcrl hpc hrun
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
  intro s1 hpc1 hrun1 hsp1 hcs1 hcrl1
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
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 597) hcrl1
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
  intro hcrl2
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
  refine call_lscro_addr
    (x := DecimalGhost.mk (x.g.device.zeroExtend 32) (sp' + 24#64))
    hdecCall hcrl2
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, *])
    (ret_pc := (blkPl_594).base + decRetOff)
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
  intro s3 hpc3 hrun3 hsp3 hcs3 hcrl3
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
    (hnext s3 cap1 p1 hpc3 hrun3 hsp3' htr3' hx19_3 hvregs_3 hcrl3 (by omega))
  rw [stackAt_sub_le sp' hdec_le hsub64]
  simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
  apply entails_of_eq
  ac_rfl

/-! ## 4. Segment 3 (`176 .. 224` & `308 .. 336`): optional reserve + `memcpy` of `dec` -/

private theorem step_append_dec_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack subStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hdoRes : subroutine_ok (lsProg_594 H) (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hres_le : resStack ≤ subStk) (hext_le : extHookStack ≤ subStk) (hsub64 : subStk ≤ 2 ^ 64)
    {x : AddrTextGhost} {R Fr : SepProp} {s0 s : State} {sp' cap1 p1 : BitVec 64}
    {Q : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_594).base + decRetOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp')
    (hsp_al : (sp' &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hvregs : preservedTailRegs s = preservedTailRegs s0)
    (hlen32 : x.g.name.bytes.length < 2 ^ 32)
    (hcap1_34 : cap1.toNat < 2 ^ 34)
    (hnext : ∀ (sm : State) (capF ptrF dCap dPtr : BitVec 64),
      sm.pc = (blkPl_594).base + memcpy1RetOff →
      sm.status = .Running →
      sm.sp = sp' →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = dPtr →
      sm.readReg64 .x21 =
        BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length →
      sm.readReg64 .x22 =
        BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length →
      preservedTailRegs sm = preservedTailRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      (decimalText (x.g.device.zeroExtend 32).toNat).length ≤ dCap.toNat →
      dCap.toNat < 2 ^ 63 →
      dPtr ≠ 0 →
      SepWPp (lsProg_594 H) (s0.readReg64 .lr) sm
        ((sp' ↦₆₄ capF) ∗ ((sp' + 8#64) ↦₆₄ ptrF) ∗
          ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length) ∗
          vecU8Buf A capF ptrF ((x.g.name.bytes ++ [0x2e#8]) ++
            decimalText (x.g.device.zeroExtend 32).toNat) ∗
          ((sp' + 24#64) ↦₆₄ dCap) ∗ ((sp' + 32#64) ↦₆₄ dPtr) ∗
          ((sp' + 40#64) ↦₆₄
            BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length) ∗
          (dPtr ↦ₛ decimalText (x.g.device.zeroExtend 32).toNat) ∗
          vecU8BufRest A dCap dPtr (decimalText (x.g.device.zeroExtend 32).toNat) ∗
          stackAt sp' subStk ∗ A.pool ∗ Fr)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (addrTextSpecPlaced A stk).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_594 H) (s0.readReg64 .lr) s
      (vecU8At A sp' cap1 p1 (x.g.name.bytes ++ [0x2e#8]) ∗
        vecU8 A (sp' + 24#64) (decimalText (x.g.device.zeroExtend 32).toNat) ∗
        stackAt sp' subStk ∗ A.pool ∗ Fr)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (addrTextSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  obtain ⟨hx25, hx26, hx27, hx28, hvregs0⟩ := preservedTailRegs_elim hvregs
  have hmemcpy := session_memcpy_region_lscro_of_cli (callerProg := lsProg_594 H)
    (stk := extHookStack) hC
  generalize hdec_def : decimalText (x.g.device.zeroExtend 32).toNat = dec at hnext ⊢
  generalize hpfx_def : x.g.name.bytes ++ [0x2e#8] = pfx at hnext ⊢
  have hpfx_bound : pfx.length ≤ 2 ^ 32 := by
    subst hpfx_def; rw [List.length_append, List.length_singleton]; omega
  have hdec_pos : 0 < dec.length := by
    subst hdec_def; rw [device_zeroExtend32_toNat]; exact decimalText_device_pos x.g.device
  have hdec_le3 : dec.length ≤ 3 := by
    subst hdec_def; rw [device_zeroExtend32_toNat]; exact decimalText_device_len_le_three x.g.device
  have hdec_nz_beq : (BitVec.ofNat 64 dec.length == 0#64) = false :=
    ofNat_beq_zero_false hdec_pos (by omega)
  have htoNat_pfx : (BitVec.ofNat 64 pfx.length).toNat = pfx.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htoNat_dec : (BitVec.ofNat 64 dec.length).toNat = dec.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1_toNat : (1#64).toNat = 1 := rfl
  apply sepWPp_fold (vecU8_dec_unpack A (sp' + 24#64) dec) (by sep_focus)
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim fun dCap => ?_
  refine sepWPp_exists_elim fun dPtr => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨hd_le, hd_63, hd_ptr⟩ => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  by_cases hgrow : cap1.toNat < pfx.length + dec.length
  · apply sepWPp_fold (vecU8At_header_unpack A sp' cap1 p1 pfx) (by sep_focus)
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hpfx_le1, hcap1_63, _⟩ => ?_
    have hbhi_ult :
        (cap1 - BitVec.ofNat 64 pfx.length).ult (BitVec.ofNat 64 dec.length) = true :=
      cmp_hi_ult_true hpfx_le1 hcap1_63 hdec_le3 hgrow
    apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 561) hcrl
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) ?_
    intro hcrl1
    obtain ⟨_, hfit2, hres2_bound⟩ :=
      reserveCap2_bounds (cap1 := cap1.toNat) (len := x.g.name.bytes.length) (decLen := dec.length)
        hcap1_34 hlen32 hdec_le3
    have hres2_bound' : reserveCap cap1.toNat pfx.length dec.length + 1 ≤ 9223372036854775808 := by
      subst hpfx_def; rw [List.length_append]; exact hres2_bound
    have hres2_le : reserveCap cap1.toNat pfx.length dec.length ≤ 9223372036854775807 := by
      omega
    refine sepWPp_weaken_pre (P' :=
        vecU8At A sp' cap1 p1 pfx ∗
          ((sp' + 24#64) ↦₆₄ dCap) ∗
          ((sp' + 32#64) ↦₆₄ dPtr) ∗
          ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 dec.length) ∗
          (dPtr ↦ₛ dec) ∗ vecU8BufRest A dCap dPtr dec ∗
          stackAt sp' subStk ∗ A.pool ∗ Fr)
      (by
        rw [vecU8At_eq_header_buf]
        unfold vecHeader
        simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
        apply entails_of_eq
        ac_rfl) ?_
    rw [stackAt_sub_le sp' hres_le hsub64]
    refine call_lscro_addr
      (x := DoReserveCall.mk sp' cap1 p1 pfx dec.length)
      hdoRes hcrl1
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := (blkPl_594).base + res1RetOff)
      (by simp only [arm64_norm, *])
      (T := vecU8At A sp' cap1 p1 pfx ∗ A.pool ∗ stackAt sp' resStack)
      (by
        apply same_eq
        dsimp [SpqrV1.Varint.doReserveSpecOf]
        simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
        unfold Same
        ac_rfl)
      (fun _ => onPanic_trace_eq (by simp only [arm64_norm, *]))
      ?_
    intro s2 hpc2 hrun2 hsp2 hcs2 hcrl2
    dsimp only [SpqrV1.Varint.doReserveSpecOf]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun htr2 => ?_
    have htr2' : s2.trace = s0.trace := by rw [htr2]; simp only [arm64_norm, *]
    have hsp2' : s2.sp = sp' := by rw [hsp2]; simp only [arm64_norm, *]
    have hx19_2 : s2.readReg64 .x19 = x.ret := by rw [hcs2.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = dPtr := by rw [hcs2.2.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 dec.length := by
      rw [hcs2.2.2.1]; simp only [arm64_norm, *]
    have hvregs_2 : preservedTailRegs s2 = preservedTailRegs s0 :=
      preservedTailRegs_step hcs2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *])
    obtain ⟨hx25_2, hx26_2, hx27_2, hx28_2, hvregs0_2⟩ := preservedTailRegs_elim hvregs_2
    simp only [sepExists_sepConj_left]
    refine sepWPp_exists_elim fun p2 => ?_
    set cap2 : BitVec 64 := BitVec.ofNat 64 (reserveCap cap1.toNat pfx.length dec.length)
    have hcap2_toNat : cap2.toNat = reserveCap cap1.toNat pfx.length dec.length := by
      dsimp [cap2]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hle2 : pfx.length + dec.length ≤ cap2.toNat := by
      subst hpfx_def; rw [hcap2_toNat, List.length_append]; exact hfit2
    apply sepWPp_fold (vecU8At_open_slice A sp' cap2 p2 pfx dec.length hle2 hdec_pos) (by sep_focus)
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hcap2_63, hp2_ne⟩ => ?_
    apply StoreKit.sepWPp_seq_lscro (mid := lsρ memcpyName) hcrl2
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) ?_
    intro hcrl3
    refine sepWPp_weaken_pre (P' :=
        memRegion (p2 + BitVec.ofNat 64 pfx.length) dec.length ∗
          (dPtr ↦ₛ dec) ∗
          (sp' ↦₆₄ cap2) ∗
          ((sp' + 8#64) ↦₆₄ p2) ∗
          ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 pfx.length) ∗
          A.live p2 cap2.toNat 1 ∗ (p2 ↦ₛ pfx) ∗
          memRegion (p2 + BitVec.ofNat 64 (pfx.length + dec.length))
            (cap2.toNat - (pfx.length + dec.length)) ∗
          ((sp' + 24#64) ↦₆₄ dCap) ∗
          ((sp' + 32#64) ↦₆₄ dPtr) ∗
          ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 dec.length) ∗
          vecU8BufRest A dCap dPtr dec ∗
          stackAt sp' subStk ∗ A.pool ∗ Fr)
      (by
        rw [stackAt_sub_le sp' hres_le hsub64]
        simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
        apply entails_of_eq
        ac_rfl) ?_
    rw [stackAt_sub_le sp' hext_le hsub64]
    refine call_lscro_addr (x := (p2 + BitVec.ofNat 64 pfx.length, dPtr, dec))
      hmemcpy hcrl3
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := (blkPl_594).base + memcpy1RetOff)
      (by simp only [arm64_norm, *])
      (T := memRegion (p2 + BitVec.ofNat 64 pfx.length) dec.length ∗
        (dPtr ↦ₛ dec) ∗ stackAt sp' extHookStack)
      (by
        apply same_eq
        dsimp [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
        simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
        unfold Same
        ac_rfl)
      (fun _ => false_entails _) ?_
    intro s4 hpc4 hrun4 hsp4 hcs4 hcrl4
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr4⟩ => ?_
    have htr4' : s4.trace = s0.trace := by rw [htr4]; simp only [arm64_norm, *]
    have hsp4' : s4.sp = sp' := by rw [hsp4]; simp only [arm64_norm, *]
    have hx19_4 : s4.readReg64 .x19 = x.ret := by rw [hcs4.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = dPtr := by rw [hcs4.2.1]; simp only [arm64_norm, *]
    have hx21_4 : s4.readReg64 .x21 = BitVec.ofNat 64 dec.length := by
      rw [hcs4.2.2.1]; simp only [arm64_norm, *]
    have hx22_4 : s4.readReg64 .x22 = BitVec.ofNat 64 pfx.length := by
      rw [hcs4.2.2.2.1]; simp only [arm64_norm, *]
    have hvregs_4 : preservedTailRegs s4 = preservedTailRegs s0 :=
      preservedTailRegs_step hcs4
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *])
    refine sepWPp_weaken_pre ?_
      (hnext s4 cap2 p2 dCap dPtr hpc4 hrun4 hsp4' htr4'
        hx19_4 hx20_4 hx21_4 hx22_4 hvregs_4 hcrl4 hd_le hd_63 hd_ptr)
    rw [stackAt_sub_le sp' hext_le hsub64, ← hcap2_toNat]
    apply step_entails (vecU8Buf_close_slice A cap2 p2 pfx dec hle2 (by omega) hcap2_63 hp2_ne)
      (by (conv_lhs => simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
    simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
    apply entails_of_eq
    ac_rfl
  · have hle1 : pfx.length + dec.length ≤ cap1.toNat := by omega
    apply sepWPp_fold (vecU8At_open_slice A sp' cap1 p1 pfx dec.length hle1 hdec_pos) (by sep_focus)
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hcap1_63, hp1_ne⟩ => ?_
    have hbhi_ult :
        (cap1 - BitVec.ofNat 64 pfx.length).ult (BitVec.ofNat 64 dec.length) = false :=
      cmp_hi_ult_false hcap1_63 hdec_le3 hle1
    apply StoreKit.sepWPp_seq_lscro (mid := lsρ memcpyName) hcrl
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) ?_
    intro hcrl1
    rw [stackAt_sub_le sp' hext_le hsub64]
    refine call_lscro_addr (x := (p1 + BitVec.ofNat 64 pfx.length, dPtr, dec))
      hmemcpy hcrl1
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := (blkPl_594).base + memcpy1RetOff)
      (by simp only [arm64_norm, *])
      (T := memRegion (p1 + BitVec.ofNat 64 pfx.length) dec.length ∗
        (dPtr ↦ₛ dec) ∗ stackAt sp' extHookStack)
      (by
        apply same_eq
        dsimp [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
        simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
        unfold Same
        ac_rfl)
      (fun _ => false_entails _) ?_
    intro s2 hpc2 hrun2 hsp2 hcs2 hcrl2
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr2⟩ => ?_
    have htr2' : s2.trace = s0.trace := by rw [htr2]; simp only [arm64_norm, *]
    have hsp2' : s2.sp = sp' := by rw [hsp2]; simp only [arm64_norm, *]
    have hx19_2 : s2.readReg64 .x19 = x.ret := by rw [hcs2.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = dPtr := by rw [hcs2.2.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 dec.length := by
      rw [hcs2.2.2.1]; simp only [arm64_norm, *]
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 pfx.length := by
      rw [hcs2.2.2.2.1]; simp only [arm64_norm, *]
    have hvregs_2 : preservedTailRegs s2 = preservedTailRegs s0 :=
      preservedTailRegs_step hcs2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *])
    refine sepWPp_weaken_pre ?_
      (hnext s2 cap1 p1 dCap dPtr hpc2 hrun2 hsp2' htr2'
        hx19_2 hx20_2 hx21_2 hx22_2 hvregs_2 hcrl2 hd_le hd_63 hd_ptr)
    rw [stackAt_sub_le sp' hext_le hsub64]
    apply step_entails (vecU8Buf_close_slice A cap1 p1 pfx dec hle1 (by omega) hcap1_63 hp1_ne)
      (by (conv_lhs => simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
    simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
    apply entails_of_eq
    ac_rfl

/-! ## 5. Segment 4 (`224 .. 280` + tailcall `b __rust_dealloc`) -/

private theorem step_epilogue_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {subStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hstk : 112 + subStk ≤ stk) (hext_stk : extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    {x : AddrTextGhost} {R : SepProp} {s0 s : State}
    {sp' capF ptrF dCap dPtr : BitVec 64}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_594).base + memcpy1RetOff)
    (hrun : s.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp : s.sp = sp')
    (hsp_def : s0.sp - 112#64 = sp')
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = dPtr)
    (hx21 : s.readReg64 .x21 =
      BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length)
    (hvregs : preservedTailRegs s = preservedTailRegs s0)
    (hd_le : (decimalText (x.g.device.zeroExtend 32).toNat).length ≤ dCap.toNat)
    (hd_63 : dCap.toNat < 2 ^ 63) :
    SepWPp (lsProg_594 H) (s0.readReg64 .lr) s
      ((sp' ↦₆₄ capF) ∗ ((sp' + 8#64) ↦₆₄ ptrF) ∗
        ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length) ∗
        vecU8Buf A capF ptrF ((x.g.name.bytes ++ [0x2e#8]) ++
          decimalText (x.g.device.zeroExtend 32).toNat) ∗
        ((sp' + 24#64) ↦₆₄ dCap) ∗ ((sp' + 32#64) ↦₆₄ dPtr) ∗
        ((sp' + 40#64) ↦₆₄
          BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length) ∗
        (dPtr ↦ₛ decimalText (x.g.device.zeroExtend 32).toNat) ∗
        vecU8BufRest A dCap dPtr (decimalText (x.g.device.zeroExtend 32).toNat) ∗
        addrCalleeSavedAt sp' s0 ∗
        protocolAddressAt A x.g x.addr ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
        stackAt sp' subStk ∗ A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpecPlaced A stk).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (addrTextSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
  obtain ⟨hx25, hx26, hx27, hx28, hvregs0⟩ := preservedTailRegs_elim hvregs
  generalize hdec_def : decimalText (x.g.device.zeroExtend 32).toNat = dec at hx21 hd_le ⊢
  generalize hpfx_def : x.g.name.bytes ++ [0x2e#8] = pfx at hx22 ⊢
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_594 H) hC
  have hdec_pos : 0 < dec.length := by
    subst hdec_def; rw [device_zeroExtend32_toNat]; exact decimalText_device_pos x.g.device
  have hdCap_nz : dCap ≠ 0#64 := dCap_ne_zero hdec_pos hd_le
  have hdCap_beq : (dCap == 0#64) = false := dCap_beq_zero_false hdec_pos hd_le
  have hdCap_pos : 0 < dCap.toNat := by omega
  have hlay_d : LayoutOk dCap.toNat 1 := layoutOk_align1 hdCap_pos (by omega)
  have hlen_sum : BitVec.ofNat 64 pfx.length + BitVec.ofNat 64 dec.length =
      BitVec.ofNat 64 (pfx ++ dec).length := by
    rw [← BitVec.ofNat_add, List.length_append]
  have hsp_pop : sp' + 112#64 = s0.sp := by
    rw [← hsp_def]; exact BitVec.sub_add_cancel s0.sp 112#64
  rw [memRegion24_cells x.ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun r2 => ?_
  refine sepWPp_exists_elim fun r1 => ?_
  refine sepWPp_exists_elim fun r0 => ?_
  unfold addrCalleeSavedAt
  have htail : ∀ (s1 : State),
      s1.pc = lsρ lsRustDeallocSymCli →
      s1.status = .Running →
      s1.sp = s0.sp →
      s1.trace = s0.trace →
      s1.readReg64 .lr = s0.readReg64 .lr →
      s1.readReg64 .x0 = dPtr →
      s1.readReg64 .x1 = dCap →
      s1.readReg64 .x2 = 1#64 →
      CalleeSavedPreserved s0 s1 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      SepWPp (lsProg_594 H) (s0.readReg64 .lr) s1
        ((A.pool ∗ A.live dPtr dCap.toNat 1 ∗ memRegion dPtr dCap.toNat ∗
          stackAt s0.sp extHookStack) ∗
        (vecU8 A x.ret (addressText x.g.val) ∗
          protocolAddressAt A x.g x.addr ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack)))
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpecPlaced A stk).post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpecPlaced A stk).onPanic x s0 sf ∗ R)) := by
    intro s1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hcs1 hcrl1
    refine SepWPp.tailcall
      (x := (dPtr, dCap.toNat, 1))
      (F := vecU8 A x.ret (addressText x.g.val) ∗
        protocolAddressAt A x.g x.addr ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack))
      hdealloc hpc1 hrun1
      (by rw [State.spAligned, hsp1]; exact hsp0)
      hlr1 ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      apply satisfies_lscro_pre hcrl1
      dsimp only [rustDeallocExternSpecWithStack]
      rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, by rw [hx1_1], by rw [hx2_1]; rfl, hlay_d⟩, ?_⟩
      simpa only [sepConj_assoc] using hm
    · intro sf code R' _ hm
      dsimp only [rustDeallocExternSpecWithStack] at hm
      exact not_satisfies_false_sepConj hm
    · intro sf _ hmR
      dsimp only [rustDeallocExternSpecWithStack] at hmR
      rw [sepConj_assoc, satisfies_pure_sepConj] at hmR
      exact False.elim hmR.1
    · intro sf _ _ hspf hcsf
      have hsp_sf : sf.sp = s0.sp := hspf.trans hsp1
      refine ⟨?_, hsp_sf, calleeSaved_trans hcs1 hcsf⟩
      intro hm_post
      dsimp only [rustDeallocExternSpecWithStack, addrTextSpecPlaced] at hm_post ⊢
      rw [hsp1, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm_post
      rcases hm_post with ⟨htr_sf, hm_post⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htr_sf.trans htr1, ?_⟩
      refine Satisfies.mono ?_ hm_post
      rw [stackAt_sub_le s0.sp hext_stk hstk64]
      apply entails_of_eq
      ac_rfl
    · intro sf R' _ hm
      dsimp only [rustDeallocExternSpecWithStack] at hm
      exact (not_satisfies_false_sepConj hm).elim
  apply StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
  wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) ?_
  intro hcrl1
  refine sepWPp_weaken_pre (P' :=
      (A.pool ∗ A.live dPtr dCap.toNat 1 ∗ memRegion dPtr dCap.toNat ∗
        stackAt s0.sp extHookStack) ∗
      (vecU8 A x.ret (addressText x.g.val) ∗
        protocolAddressAt A x.g x.addr ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack))) ?_
    (htail _
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [calleeSavedVRegs, arm64_norm, *]⟩
      hcrl1)
  have hret_vec :
      (x.ret ↦₆₄ capF) ∗ ((x.ret + 8#64) ↦₆₄ ptrF) ∗
        ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 (pfx ++ dec).length) ∗
        vecU8Buf A capF ptrF (pfx ++ dec) ⊢
      vecU8 A x.ret (addressText x.g.val) := by
    subst hpfx_def hdec_def
    rw [← addressText_val_eq x.g]
    exact vecU8_from_moved_header A x.ret capF ptrF (addressText x.g.val)
  have hsp0_cell := cells24_entails_memRegion sp' capF ptrF
    (BitVec.ofNat 64 (pfx ++ dec).length)
  have hsp24_cell := cells24_entails_memRegion (sp' + 24#64) dCap dPtr
    (BitVec.ofNat 64 dec.length)
  have hsp48_cell := addrCalleeSavedAt_entails_memRegion64 sp' s0
  unfold addrCalleeSavedAt at hsp48_cell
  have hdec_dealloc := dec_buf_to_dealloc A dCap dPtr dec hd_le hd_63 hdCap_nz
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsp24_cell
  have hstk_back :
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
        stackAt sp' subStk ∗
        memRegion sp' 24 ∗
        memRegion (sp' + 24#64) 24 ∗
        memRegion (sp' + 48#64) 64 =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
        stackAt s0.sp extHookStack := by
    rw [← hsp_def, ← stackAt_frame112_split s0.sp hstk hstk64,
        stackAt_sub_le s0.sp hext_stk hstk64]
  apply step_entails hdec_dealloc (by sep_focus)
  apply step_entails hret_vec (by sep_focus)
  apply step_entails hsp0_cell (by sep_focus)
  apply step_entails hsp24_cell (by sep_focus)
  apply step_entails hsp48_cell (by sep_focus)
  apply step_entails (entails_of_eq hstk_back) (by sep_focus)
  simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
  apply entails_of_eq
  ac_rfl

/-! ## 6. Top-Level Relocatable Theorems -/

/-- Relocatable `[LibsignalPlacement]` `address_text` contract on `lsProg_594 H`. -/
theorem addrText_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resProg decProg : Program} {resBlk decBlk : Nat}
    [IsLsBlockProg resProg resBlk H] [IsLsBlockProg decProg decBlk H]
    {resStack decStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRes : subroutine_ok resProg (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hDec : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hstk : 0x70 + max (max resStack extHookStack) decStk ≤ stk)
    (hresBlk : resBlk < 619 := by decide)
    (hresUnmut : (resBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hdecBlk : decBlk < 619 := by decide)
    (hdecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_594 H) (lsmpl.base 594) (addrTextSpecPlaced A stk) := by
  have hdoRes : subroutine_ok (lsProg_594 H) (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)) :=
    ls_transfer_lscro (callerProg := lsProg_594 H) hRes (by decide) hresBlk hresUnmut
  have hdecCall : subroutine_ok (lsProg_594 H) (lsmpl.base 597)
      (StoreKit.withLsCodeRoLoaded lsmpl (decimalInnerSpec A decStk)) :=
    ls_transfer_lscro (callerProg := lsProg_594 H) hDec (by decide) hdecBlk hdecUnmut
  change subroutine_ok (lsProg_594 H) (blkPl_594).base (addrTextSpecPlaced A stk)
  apply subroutine_ok_of_sepWPp_init
  intro x R s0 hpc hrun hpre hsp0
  obtain ⟨hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg64 .x1 = x.addr ∧ x.g.name.bytes.length < 2 ^ 32⌝ ∗
      protocolAddressAt A x.g x.addr ∗ memRegion x.ret 24 ∗ stackAt s0.sp stk ∗ A.pool) ∗ R
    at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hlen32⟩, hmem0⟩
  have hstk64 : stk ≤ 2 ^ 64 := by
    refine stk_le_two_pow_64 (m := s0.mem) (ret := x.ret) (sp := s0.sp) (stk := stk)
      (R := protocolAddressAt A x.g x.addr ∗ A.pool ∗ R) ?_
    simpa only [sepConj_assoc, sepConj_comm, sepConj_left_comm] using hmem0
  set subStk := max (max resStack extHookStack) decStk
  have hres_le : resStack ≤ subStk := le_trans (le_max_left _ _) (le_max_left _ _)
  have hext_le : extHookStack ≤ subStk := le_trans (le_max_right _ _) (le_max_left _ _)
  have hdec_le : decStk ≤ subStk := le_max_right _ _
  have hsub64 : subStk ≤ 2 ^ 64 := by omega
  have hext_stk : extHookStack ≤ stk := by omega
  have hsp_al0 : ((s0.sp - 112#64) &&& 15#64 == 0#64) = true := spAligned_sub112 hsp0
  refine ⟨protocolAddressAt A x.g x.addr ∗ memRegion x.ret 24 ∗ stackAt s0.sp stk ∗ A.pool,
    hmem0, ?_⟩
  rw [stackAt_frame112_split s0.sp hstk hstk64]
  generalize hsp_def : s0.sp - 112#64 = sp' at hsp_al0 ⊢
  apply sepWPp_fold (memRegion64_cells sp') (by sep_focus)
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim fun w19 => ?_
  refine sepWPp_exists_elim fun w20 => ?_
  refine sepWPp_exists_elim fun w21 => ?_
  refine sepWPp_exists_elim fun w22 => ?_
  refine sepWPp_exists_elim fun w23 => ?_
  refine sepWPp_exists_elim fun w24 => ?_
  refine sepWPp_exists_elim fun w30 => ?_
  refine sepWPp_exists_elim fun w29 => ?_
  rw [memRegion24_cells sp']
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun w2 => ?_
  refine sepWPp_exists_elim fun w1 => ?_
  refine sepWPp_exists_elim fun w0 => ?_
  apply sepWPp_fold (protocolAddressAt_open A x.g x.addr) (by sep_focus)
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨_, _, _⟩ => ?_
  refine sepWPp_weaken_pre (P' :=
      (((sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ w2)) ∗
      (((sp' + 48#64) ↦₆₄ w29) ∗ ((sp' + 56#64) ↦₆₄ w30) ∗
        ((sp' + 64#64) ↦₆₄ w24) ∗ ((sp' + 72#64) ↦₆₄ w23) ∗
        ((sp' + 80#64) ↦₆₄ w22) ∗ ((sp' + 88#64) ↦₆₄ w21) ∗
        ((sp' + 96#64) ↦₆₄ w20) ∗ ((sp' + 104#64) ↦₆₄ w19)) ∗
      ((x.addr + 8#64) ↦₆₄ x.g.name.ptr) ∗
      ((x.addr + 16#64) ↦₆₄ BitVec.ofNat 64 x.g.name.bytes.length) ∗
      (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗
      ((x.addr + 24#64) ↦₈ x.g.device) ∗
      stackAt sp' subStk ∗ A.pool ∗
      ((x.addr ↦₆₄ x.g.name.cap) ∗
        (vecU8BufRest A x.g.name.cap x.g.name.ptr x.g.name.bytes ∗ memRegion (x.addr + 25#64) 7) ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
        memRegion (sp' + 24#64) 24)))
    (by apply entails_of_eq; ac_rfl) ?_
  apply StoreKit.sepWPp_seq_lscro (mid := (blkPl_594).base + frameOff) hcrl0
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
  intro hcrl0'
  refine step_prologue_to_owned_p hC hpan hext_le hsub64 hcrl0'
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm])
    hsp_al0
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hx0])
    (by simp only [arm64_norm, hx1])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (preservedTailRegs_mk
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [calleeSavedVRegs, arm64_norm]))
    hlen32 ?_
  intro s1 p0 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx19_1 hx20_1 hvregs_1 hcrl1
  refine sepWPp_weaken_pre (P' :=
      vecU8At A sp' (BitVec.ofNat 64 x.g.name.bytes.length) p0 x.g.name.bytes ∗
      memRegion (sp' + 24#64) 24 ∗
      ((x.addr + 24#64) ↦₈ x.g.device) ∗
      stackAt sp' subStk ∗ A.pool ∗
      (addrCalleeSavedAt sp' s0 ∗
        (x.addr ↦₆₄ x.g.name.cap) ∗
        ((x.addr + 8#64) ↦₆₄ x.g.name.ptr) ∗
        ((x.addr + 16#64) ↦₆₄ BitVec.ofNat 64 x.g.name.bytes.length) ∗
        (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗
        (vecU8BufRest A x.g.name.cap x.g.name.ptr x.g.name.bytes ∗ memRegion (x.addr + 25#64) 7) ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine step_dot_and_decimal_p hdoRes hdecCall hres_le hdec_le hsub64
    hcrl1 hpc1 hrun1 hsp1 hsp_al0 htr1 hlr1
    hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx19_1 hx20_1 hvregs_1 hlen32 ?_
  intro s2 cap1 p1 hpc2 hrun2 hsp2 htr2 hx19_2 hvregs_2 hcrl2 hcap1_34
  refine sepWPp_weaken_pre (P' :=
      vecU8At A sp' cap1 p1 (x.g.name.bytes ++ [0x2e#8]) ∗
      vecU8 A (sp' + 24#64) (decimalText (x.g.device.zeroExtend 32).toNat) ∗
      stackAt sp' subStk ∗ A.pool ∗
      (addrCalleeSavedAt sp' s0 ∗
        protocolAddressAt A x.g x.addr ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)))) ?_ ?_
  · apply step_entails (protocolAddressAt_close A x.g x.addr) (by sep_focus)
    apply entails_of_eq
    ac_rfl
  refine step_append_dec_p hC hdoRes hres_le hext_le hsub64
    hcrl2 hpc2 hrun2 hsp2 hsp_al0 htr2 hx19_2 hvregs_2 hlen32 hcap1_34 ?_
  intro s3 capF ptrF dCap dPtr hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3
    hvregs_3 hcrl3 hd_le hd_63 _
  refine sepWPp_weaken_pre (P' :=
      (sp' ↦₆₄ capF) ∗ ((sp' + 8#64) ↦₆₄ ptrF) ∗
      ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length) ∗
      vecU8Buf A capF ptrF ((x.g.name.bytes ++ [0x2e#8]) ++
        decimalText (x.g.device.zeroExtend 32).toNat) ∗
      ((sp' + 24#64) ↦₆₄ dCap) ∗ ((sp' + 32#64) ↦₆₄ dPtr) ∗
      ((sp' + 40#64) ↦₆₄
        BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length) ∗
      (dPtr ↦ₛ decimalText (x.g.device.zeroExtend 32).toNat) ∗
      vecU8BufRest A dCap dPtr (decimalText (x.g.device.zeroExtend 32).toNat) ∗
      addrCalleeSavedAt sp' s0 ∗
      protocolAddressAt A x.g x.addr ∗
      memRegion x.ret 24 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
      stackAt sp' subStk ∗ A.pool)
    (by apply entails_of_eq; ac_rfl) ?_
  exact step_epilogue_p hC hstk hext_stk hstk64
    hcrl3 hpc3 hrun3 hsp0 hsp3 hsp_def htr3 hx19_3 hx20_3 hx21_3 hx22_3 hvregs_3 hd_le hd_63

/-- Caller-transferable `[LibsignalPlacement]` `address_text` contract for any block `< 619`. -/
theorem addrText_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg resProg decProg : Program} {i resBlk decBlk : Nat}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg resProg resBlk H]
    [IsLsBlockProg decProg decBlk H]
    {resStack decStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRes : subroutine_ok resProg (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hDec : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hstk : 0x70 + max (max resStack extHookStack) decStk ≤ stk)
    (hi : i < 619 := by decide)
    (hresBlk : resBlk < 619 := by decide)
    (hresUnmut : (resBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hdecBlk : decBlk < 619 := by decide)
    (hdecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 594) (addrTextSpecPlaced A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 594)
    (addrText_placed_ok_of_deps hC hpan hRes hDec hstk hresBlk hresUnmut hdecBlk hdecUnmut) hi

end CryptoVerification.SignalSession.Cli.AddressText.Helpers

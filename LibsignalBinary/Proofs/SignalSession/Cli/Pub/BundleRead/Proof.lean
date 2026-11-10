/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.ReadCall
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Layout
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.BundleRead.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit

/-!
# Proof of `bundleRead_ok_of_loads` for `read_bundle::{closure#0}`

Decomposes the 55-instruction body (`+0 .. +216`) of `signal_session::public::read_bundle::{closure#0}`
into per-branch weakest-precondition lemmas, isolating the `read_file` call in `BundleRead.ReadCall`.
-/

private theorem bind_sepWP_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : let st := s; SepWP prog ret st P Q) :
    SepWP prog ret s P Q := h

@[local simp, local arm64_norm, local wp_norm]
private theorem readReg64_setPState_local (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem readVReg128_setPState_local (s : State) (ps : PState) (v : BitVec 5) :
    (s.setPState ps).readVReg128 v = s.readVReg128 v := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).sp = s.sp := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem mem_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).mem = s.mem := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem status_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).status = s.status := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem trace_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem symtab_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setPState_local (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := rfl

private theorem sepWPp_mono_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

private theorem sepWPp_exists_pre {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (P a) Q Qp) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hm⟩ := hm
  exact h a R hm hL

private theorem allocFailedIn_of_prefix {s0 sm sf : State}
    (h0m : s0.trace <+: sm.trace) (hmf : allocFailedIn sm sf) :
    allocFailedIn s0 sf := by
  obtain ⟨t, ht⟩ := h0m
  unfold allocFailedIn at hmf ⊢
  rw [← ht, List.length_append, ← List.drop_drop] at hmf
  exact List.mem_of_mem_drop hmf

private theorem allocFailedIn_append_of_prefix {s0 s1 sf : State}
    (h01 : s0.trace <+: s1.trace) (htr : sf.trace = s1.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  obtain ⟨t, ht⟩ := h01
  refine ⟨?_, ⟨t ++ [allocFailedEvent], by rw [htr, ← ht, List.append_assoc]⟩⟩
  unfold allocFailedIn
  rw [htr, ← ht, List.append_assoc, List.drop_left]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

private theorem layoutOk_of_pos_lt63 {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    LayoutOk n 1 :=
  ⟨hpos, ⟨0, rfl⟩, by omega⟩

private theorem sp_pop_80_eq (sp0 : BitVec 64) : (sp0 - 80#64) + 80#64 = sp0 :=
  BitVec.sub_add_cancel sp0 80#64

private theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl _

private theorem satisfies_of_eq {m : Memory} {P Q : SepProp} (h : P = Q) (hm : m ⊨ P) :
    m ⊨ Q :=
  h ▸ hm

private theorem satisfies_mono_rev {m : Memory} {P Q : SepProp} (hm : m ⊨ P) (h : P ⊢ Q) :
    m ⊨ Q :=
  Satisfies.mono h hm

private theorem cs_hi_of_eq {s1 s2 : State}
    (h21 : s1.readReg64 .x21 = s2.readReg64 .x21)
    (h22 : s1.readReg64 .x22 = s2.readReg64 .x22)
    (h23 : s1.readReg64 .x23 = s2.readReg64 .x23)
    (h24 : s1.readReg64 .x24 = s2.readReg64 .x24)
    (h25 : s1.readReg64 .x25 = s2.readReg64 .x25)
    (h26 : s1.readReg64 .x26 = s2.readReg64 .x26)
    (h27 : s1.readReg64 .x27 = s2.readReg64 .x27)
    (h28 : s1.readReg64 .x28 = s2.readReg64 .x28) :
    ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s1.readReg64 (.gpr ⟨n, by omega⟩) = s2.readReg64 (.gpr ⟨n, by omega⟩) := by
  intro n hn
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 := by omega
  all_goals assumption

private theorem cs_hi_of_preserved {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s2.readReg64 (.gpr ⟨n, by omega⟩) = s1.readReg64 (.gpr ⟨n, by omega⟩) :=
  cs_hi_of_eq h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1

private theorem cs_hi_trans {s1 s2 s3 : State}
    (h12 : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s1.readReg64 (.gpr ⟨n, by omega⟩) = s2.readReg64 (.gpr ⟨n, by omega⟩))
    (h23 : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s2.readReg64 (.gpr ⟨n, by omega⟩) = s3.readReg64 (.gpr ⟨n, by omega⟩)) :
    ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s1.readReg64 (.gpr ⟨n, by omega⟩) = s3.readReg64 (.gpr ⟨n, by omega⟩) :=
  fun n hn => (h12 n hn).trans (h23 n hn)

/-- Non-zero-capacity epilogue (`+84 .. +104`): restores callee-saved registers, pops the frame, and tail-calls `__rust_dealloc` on `path`. -/
theorem tail_dealloc_step {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 0x50 + extHookStack ≤ stk)
    (hstk_le : stk ≤ 2 ^ 64)
    {x : BundleReadGhost} {s0 s : State}
    {pathCap pathPtr : BitVec 64} {r : Except Unit (List (BitVec 8))}
    {F : SepProp}
    (hPC : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName + bv% (84))
    (hRun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hAl0 : s0.spAligned = true)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx19_s : s.readReg64 .x19 = pathPtr)
    (hx1_s : s.readReg64 .x1 = pathCap)
    (hcap_pos : 0 < pathCap.toNat)
    (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hcs_hi : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hr_out : r = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ s.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (((getResultAt A x.ret r ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ F))
      (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ F)
      (fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ F) := by
  have hdealloc := dealloc_ok_at_bundleRead hC
  code_fetches_range libsignalSessionCode bundleReadBin img.base (Rust.withPanics ext)
    bundleRead_fnOff (num% (ls_off% bundleReadName)) 84 28
  dsimp only [tripleRatchetProgAtExt] at hdealloc hPC ⊢
  generalize hfnBase : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    bundleReadName = fnBase at *
  have hAl_frame : (s0.sp - 80#64) &&& 15#64 = 0#64 := by
    have hal : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hAl0
    bv_bits
  have hsplit_hk : stackAt (s0.sp - 80#64) (stk - 80) =
      memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
        stackAt (s0.sp - 80#64) extHookStack :=
    stackAt_split_sub (s0.sp - 80#64) (stk - 80) extHookStack (by omega) (by omega)
  apply SepWPp.seq_frozen
    (mid := fnBase + bv% (ls_rel% bundleReadName "__rustc::__rust_dealloc"))
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial
  wp_steps
  apply bind_sepWP_state; intro s1
  refine SepWP.done ?_ ?_ ?_
  · simp [s1, arm64_norm]
  · simp [s1, arm64_norm, hRun]
  · intro _ R hm1 hL1
    have hsp1 : s1.sp = s0.sp - 80#64 := by simp [s1, arm64_norm, hsp]
    have htr_s1 : s1.trace = s.trace := by simp [s1, arm64_norm]
    let restDealloc : SepProp :=
      getResultAt A x.ret r ∗
        SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
        memRegion (s0.sp - 80#64) 24 ∗
        (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
        (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
        (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
        (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
        (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
        (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗ F
    have hm1_d : s1.mem ⊨
        (A.pool ∗ A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          stackAt s1.sp extHookStack) ∗ restDealloc ∗ R := by
      rw [hsp1]
      have hm1' := hm1
      rw [hsplit_hk] at hm1'
      refine satisfies_of_eq ?_ hm1'
      dsimp only [restDealloc]
      simp only [List.length_append, List.length_cons, List.length_nil]
      ac_rfl
    obtain ⟨sd, hsteps_d, hout_d, -⟩ :=
      subroutine_ok.no_fault_before_outcome hdealloc
        (pathPtr, pathCap.toNat, 1) (restDealloc ∗ R) s1
        (by simp [s1, arm64_norm])
        (by simp [s1, arm64_norm, hRun])
        (by
          dsimp only [rustDeallocExternSpecWithStack, Spec.inImage]
          rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨by simpa [s1, arm64_norm] using hF, by simpa [s1, arm64_norm] using hsym⟩,
            ⟨by simp [s1, arm64_norm, hx19_s],
             by simp [s1, arm64_norm, hx1_s],
             rfl,
             layoutOk_of_pos_lt63 hcap_pos hcap_lt⟩,
            by simpa [sepConj_assoc] using hm1_d⟩)
        (by simpa [State.spAligned, hsp1] using hAl_frame)
        hL1
    rcases hout_d with ⟨⟨hpcsd, hsp_d0, hrunsd⟩, ⟨hspsd, hcssd⟩, hpost_d⟩ | ⟨_, hpost_d⟩ |
        ⟨_, _, hpost_d⟩ | ⟨_, hpost_d⟩
    · dsimp only [rustDeallocExternSpecWithStack, Spec.inImage] at hpost_d
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_d
      obtain ⟨htr_sd, hmem_sd⟩ := hpost_d
      replace hpcsd : sd.pc = fnBase + bv% (96) :=
        hpcsd.trans (by simp [s1, arm64_norm])
      have hspd : sd.sp = s0.sp - 80#64 := hspsd.trans hsp1
      clear hsp_d0 hspsd
      have hLd := hsteps_d.codeLoaded hL1
      have hmd_ep : sd.mem ⊨
          (((getResultAt A x.ret r ∗
            SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            stackAt (s0.sp - 80#64) (stk - 80) ∗
            memRegion (s0.sp - 80#64) 24 ∗
            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
            (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗ A.pool) ∗ F) ∗ R) := by
        rw [hsp1] at hmem_sd
        rw [hsplit_hk]
        refine satisfies_of_eq ?_ hmem_sd
        dsimp only [restDealloc]
        simp only [List.length_append, List.length_cons, List.length_nil]
        ac_rfl
      have hwp_ep :
          SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (s0.readReg64 .lr) sd
            (((getResultAt A x.ret r ∗
              SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
              SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
              stackAt (s0.sp - 80#64) (stk - 80) ∗
              memRegion (s0.sp - 80#64) 24 ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
              (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗ A.pool) ∗ F))
            (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
              Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ F)
            (fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ F) := by
        apply SepWPp.seq_frozen
          (mid := s0.readReg64 .lr)
          (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial
        wp_conv_pre => rw [← hspd]
        wp_steps
        apply bind_sepWP_state; intro sf
        refine SepWP.done ?_ ?_ ?_
        · simp [sf, arm64_norm]
        · simp [sf, arm64_norm, hrunsd]
        · intro _ R_ep hm_ep _hL_ep
          rw [hspd] at hm_ep
          have hpack80 := frame_80_pack (s0.sp - 80#64) pathCap pathPtr
            (BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length)
            (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x20) (s0.readReg64 .x19)
          have hstk80 : stackAt s0.sp stk =
              stackAt (s0.sp - 80#64) (stk - 80) ∗ memRegion (s0.sp - 80#64) 80 :=
            stackAt_frame_80_eq s0.sp stk (by omega) hstk_le
          have htr_sf : sf.trace = sd.trace := by simp [sf, arm64_norm]
          have hr_final :
              r = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ sf.trace = s0.trace :=
            ⟨hr_out.1, htr_sf.trans (htr_sd.trans (htr_s1.trans hr_out.2))⟩
          refine ⟨sf, Steps.refl sf,
            Or.inl ⟨by simp [sf, arm64_norm], by simp [sf, arm64_norm, hrunsd], _, ?_,
              by simp [sf, arm64_norm, hspd, sp_pop_80_eq], ?_, rfl⟩⟩
          · have hm_ep' : sf.mem ⊨
                (((getResultAt A x.ret r ∗
                  SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  (stackAt (s0.sp - 80#64) (stk - 80) ∗
                    (memRegion (s0.sp - 80#64) 24 ∗
                      (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                      (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                      (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                      (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                      (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                      (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                      (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19))) ∗ A.pool) ∗ F) ∗ R_ep) := by
              refine satisfies_of_eq ?_ hm_ep
              simp only [List.length_append, List.length_cons, List.length_nil]
              ac_rfl
            have h1 :
                (stackAt (s0.sp - 80#64) (stk - 80) ∗
                  (memRegion (s0.sp - 80#64) 24 ∗
                    (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                    (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                    (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                    (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                    (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                    (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                    (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19))) ⊢
                stackAt s0.sp stk := by
              rw [hstk80]
              exact sepConj_mono_right hpack80
            have hpost_ent :
                ((getResultAt A x.ret r ∗
                  SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  (stackAt (s0.sp - 80#64) (stk - 80) ∗
                    (memRegion (s0.sp - 80#64) 24 ∗
                      (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                      (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                      (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                      (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                      (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                      (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                      (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19))) ∗ A.pool) ∗ F) ⊢
                (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ F := by
              dsimp only [bundleReadSpec, Spec.inImage]
              refine Entails.trans
                (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_left h1))))) ?_
              refine Entails.trans ?_
                (sepConj_mono_left (sepConj_mono_left
                  (Entails.sepExists_right r (Entails.pure_right hr_final (Entails.refl _)))))
              have hre :
                  ((getResultAt A x.ret r ∗
                    SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                    SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                    stackAt s0.sp stk ∗ A.pool) ∗ F) =
                  (getResultAt A x.ret r ∗
                    (SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                      SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                      stackAt s0.sp stk ∗ A.pool)) ∗ F := by
                ac_rfl
              rw [hre]
              exact Entails.refl _
            exact Satisfies.mono (sepConj_mono_left hpost_ent) hm_ep'
          · have hcs_sf_s0 :=
              cs_hi_trans
                (cs_hi_of_eq (s1 := sf) (s2 := sd)
                  (by simp [sf, arm64_norm]) (by simp [sf, arm64_norm])
                  (by simp [sf, arm64_norm]) (by simp [sf, arm64_norm])
                  (by simp [sf, arm64_norm]) (by simp [sf, arm64_norm])
                  (by simp [sf, arm64_norm]) (by simp [sf, arm64_norm]))
                (cs_hi_trans (cs_hi_of_preserved hcssd)
                  (cs_hi_trans
                    (cs_hi_of_eq (s1 := s1) (s2 := s)
                      (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm])
                      (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm])
                      (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm])
                      (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm]))
                    hcs_hi))
            unfold CalleeSavedPreserved at hcssd ⊢
            refine ⟨by simp [sf, arm64_norm],
              by simp [sf, arm64_norm],
              hcs_sf_s0 21 ⟨by omega, by omega⟩,
              hcs_sf_s0 22 ⟨by omega, by omega⟩,
              hcs_sf_s0 23 ⟨by omega, by omega⟩,
              hcs_sf_s0 24 ⟨by omega, by omega⟩,
              hcs_sf_s0 25 ⟨by omega, by omega⟩,
              hcs_sf_s0 26 ⟨by omega, by omega⟩,
              hcs_sf_s0 27 ⟨by omega, by omega⟩,
              hcs_sf_s0 28 ⟨by omega, by omega⟩,
              by simp [sf, arm64_norm],
              ((by simp [sf, calleeSavedVRegs, arm64_norm] :
                calleeSavedVRegs sf = calleeSavedVRegs sd).trans
                (hcssd.2.2.2.2.2.2.2.2.2.2.2.trans
                  ((by simp [s1, calleeSavedVRegs, arm64_norm] :
                    calleeSavedVRegs s1 = calleeSavedVRegs s).trans hvregs)))⟩
      obtain ⟨sf, hsteps_ep, hout_ep⟩ := hwp_ep R hmd_ep hLd
      exact ⟨sf, hsteps_d.trans hsteps_ep, hout_ep⟩
    · exact (not_satisfies_false_sepConj hpost_d).elim
    · exact (not_satisfies_false_sepConj hpost_d).elim
    · exact (not_satisfies_false_sepConj hpost_d).elim

set_option maxHeartbeats 800000 in
/-- `Ok(bs)` branch (`+44 .. +84`): stores `(okTagVec, cap, ptr, len)` at `x.ret` and enters `tail_dealloc_step`. -/
theorem ok_branch_step {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 0x50 + extHookStack ≤ stk)
    (hstk_le : stk ≤ 2 ^ 64)
    {x : BundleReadGhost} {s0 s : State}
    {pathCap pathPtr : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp}
    (hPC : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName + bv% (44))
    (hRun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hAl0 : s0.spAligned = true)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx19_s : s.readReg64 .x19 = pathPtr)
    (hx20_s : s.readReg64 .x20 = x.ret)
    (hcap_pos : 0 < pathCap.toNat)
    (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hcs_hi : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hr_out : Except.ok bs = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ s.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (((vecU8 A (s0.sp - 80#64) bs ∗
          memRegion x.ret 48 ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ F))
      (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ F)
      (fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ F) := by
  code_fetches_range libsignalSessionCode bundleReadBin img.base (Rust.withPanics ext)
    bundleRead_fnOff (num% (ls_off% bundleReadName)) 44 40
  dsimp only [tripleRatchetProgAtExt] at hPC ⊢
  generalize hfnBase : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    bundleReadName = fnBase at *
  generalize hprog : libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
  dsimp only [vecU8, vecU8At, vecHeader]
  simp only [sepExists_sepConj_left]
  apply sepWPp_exists_pre; intro vecCap
  apply sepWPp_exists_pre; intro vecPtr
  apply sepWPp_mono_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (sret_32_unpack x.ret))))
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWPp_exists_pre; intro w3
  apply sepWPp_exists_pre; intro w2
  apply sepWPp_exists_pre; intro w1
  apply sepWPp_exists_pre; intro w0 R hm hL
  have hpure_vec :
      bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0 := by
    have hm' : s.mem ⊨ ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
        ((((s0.sp - 80#64) ↦₆₄ vecCap) ∗ (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
          (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if vecCap = 0 then emp
           else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
             memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length)) ∗
          ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
            ((x.ret + 24#64) ↦₆₄ w3) ∗ memRegion (x.ret + 32#64) 16) ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool ∗ F) ∗ R) := by
      refine satisfies_of_eq ?_ hm
      ac_rfl
    rw [satisfies_pure_sepConj] at hm'
    exact hm'.1
  have hnot_err : (vecCap + 1#64 == 0#64) = false := by
    apply beq_false_of_ne
    intro heq
    have hnat := congrArg BitVec.toNat heq
    simp [BitVec.toNat_add] at hnat
    omega
  have heq_cond : ConditionHolds CondCode.EQ (AddWithCarry64 vecCap 1#64 false).2 = false := by
    have _ : vecCap.toNat < 2 ^ 63 := hpure_vec.2.1
    simp only [ConditionHolds, AddWithCarry64]
    bv_bits
  have hcap_ne : pathCap ≠ 0#64 := by intro heq; subst heq; simp at hcap_pos
  have hcap_ne0 : (pathCap == 0#64) = false := beq_false_of_ne hcap_ne
  have _ := And.intro heq_cond (And.intro hnot_err (And.intro hcap_ne hcap_ne0))
  have hm_flat : s.mem ⊨
      (((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
        ((x.ret + 24#64) ↦₆₄ w3) ∗ memRegion (x.ret + 32#64) 16 ∗
        ((s0.sp - 80#64) ↦₆₄ vecCap) ∗
        (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
        (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
        (if vecCap = 0 then emp
         else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
           memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length)) ∗
        SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 80#64) (stk - 80) ∗
        (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
        (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
        (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
        (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
        (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
        (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool ∗ F) ∗ R) := by
    refine satisfies_of_eq ?_ hm
    simp only [List.length_append, List.length_cons, List.length_nil]
    ac_rfl
  simp only [arm64_norm] at hx20_s
  refine (?_ : SepWPp prog
    (s0.readReg64 .lr) s _ _ _) R hm_flat hL
  apply SepWPp.seq_frozen
    (mid := fnBase + bv% (84))
    (Φ := fun m' => s.mem.KeepsFrozen m')
    (fun _ _ h12 h23 => Memory.KeepsFrozen.trans h12 h23)
    (Memory.KeepsFrozen.refl s.mem)
  wp_steps
  apply bind_sepWP_state; intro s_mid
  refine SepWP.done ?_ ?_ ?_
  · simp [s_mid, arm64_norm, hnot_err, heq_cond, hcap_ne0]
  · simp [s_mid, arm64_norm, hRun]
  · intro hkf_mid R' hm_mid hL_mid
    have hF_mid : img.FrozenLoaded s_mid := hF.of_keepsFrozen hkf_mid
    subst hprog
    subst hfnBase
    have hs_mid_sp : s_mid.sp = s0.sp - 80#64 := by simp [s_mid, arm64_norm, hsp]
    have hs_mid_x1 : s_mid.readReg64 .x1 = pathCap := by simp [s_mid, arm64_norm]
    have hs_mid_x19 : s_mid.readReg64 .x19 = pathPtr := by simp [s_mid, arm64_norm, hx19_s]
    have hs_mid_tr : s_mid.trace = s.trace := by simp [s_mid, arm64_norm]
    have hpack_ok :
        ((((s0.sp - 80#64) ↦₆₄ vecCap) ∗
          (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
          (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
          (if vecCap = 0 then emp
           else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
             memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
          ((x.ret ↦₆₄ okTagVec) ∗ ((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
            ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ memRegion (x.ret + 32#64) 16) ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ⊢
        (getResultAt A x.ret (.ok bs) ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) := by
      have hre1 :
          ((((s0.sp - 80#64) ↦₆₄ vecCap) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
            (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
            (if vecCap = 0 then emp
             else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
               memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
            ((x.ret ↦₆₄ okTagVec) ∗ ((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
              ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ memRegion (x.ret + 32#64) 16)) =
          ((x.ret ↦₆₄ okTagVec) ∗
            (((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
              ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
              ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
              (if vecCap = 0 then emp
               else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
                 memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
            memRegion (x.ret + 32#64) 16) ∗
          (((s0.sp - 80#64) ↦₆₄ vecCap) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
            (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) := by
        ac_rfl
      have hboth := sepConj_mono (ok_result_intro A x.ret vecCap vecPtr bs)
        (slot24_pack (s0.sp - 80#64) vecCap vecPtr (BitVec.ofNat 64 bs.length))
      rw [← hre1] at hboth
      have hall := sepConj_mono_left
        (Q := SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) hboth
      have hre2 :
          (getResultAt A x.ret (.ok bs) ∗ memRegion (s0.sp - 80#64) 24) ∗
            (SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
              SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
              stackAt (s0.sp - 80#64) (stk - 80) ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
              (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
              A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) =
          getResultAt A x.ret (.ok bs) ∗
            SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            stackAt (s0.sp - 80#64) (stk - 80) ∗
            memRegion (s0.sp - 80#64) 24 ∗
            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
            (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
            A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool := by
        ac_rfl
      rw [hre2] at hall
      simpa [sepConj_assoc] using hall
    have hm_mid_orig : s_mid.mem ⊨
        ((((((s0.sp - 80#64) ↦₆₄ vecCap) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
            (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
            (if vecCap = 0 then emp
             else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
               memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
          ((x.ret ↦₆₄ okTagVec) ∗ ((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
            ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ memRegion (x.ret + 32#64) 16) ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ F) ∗ R') := by
      refine satisfies_of_eq ?_ hm_mid
      simp only [List.length_append, List.length_cons, List.length_nil]
      ac_rfl
    have hm_norm : s_mid.mem ⊨
        ((getResultAt A x.ret (.ok bs) ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ F) ∗ R' :=
      satisfies_mono_rev hm_mid_orig
        (sepConj_mono_left (Q := R') (sepConj_mono_left (Q := F) hpack_ok))
    exact
      (tail_dealloc_step hC hstk hstk_le
        (by simp [s_mid, tripleRatchetProgAtExt, arm64_norm, Program.fnAddr_rebase,
          hnot_err, heq_cond, hcap_ne0])
        (by simp [s_mid, arm64_norm, hRun])
        hs_mid_sp hAl0
        hF_mid
        (by simpa [s_mid, arm64_norm] using hsym)
        hs_mid_x19 hs_mid_x1 hcap_pos hcap_lt
        (cs_hi_trans
          (cs_hi_of_eq
            (by simp [s_mid, arm64_norm]) (by simp [s_mid, arm64_norm])
            (by simp [s_mid, arm64_norm]) (by simp [s_mid, arm64_norm])
            (by simp [s_mid, arm64_norm]) (by simp [s_mid, arm64_norm])
            (by simp [s_mid, arm64_norm]) (by simp [s_mid, arm64_norm]))
          hcs_hi)
        ((by simp [s_mid, calleeSavedVRegs, arm64_norm] :
          calleeSavedVRegs s_mid = calleeSavedVRegs s).trans hvregs)
        ⟨hr_out.1, hs_mid_tr.trans hr_out.2⟩)
      R' hm_norm hL_mid

private theorem rebase_fetch_of_fnAddr {b : BitVec 64} {H : String → Option (State → State)}
    {k off : BitVec 64} {inst : Instr}
    (hk : BitVec.ofNat 64 (num% (ls_off% bundleReadName)) + k = off)
    (h : (libsignalSessionCode.rebase b H).fetch (b + off) = some inst) :
    (libsignalSessionCode.rebase b H).fetch
      ((libsignalSessionCode.rebase b H).fnAddr bundleReadName + k) = some inst := by
  have heq :
      (libsignalSessionCode.rebase b H).fnAddr bundleReadName + k = b + off := by
    rw [Program.fnAddr_rebase, bundleRead_fnOff, BitVec.add_assoc, hk]
  rw [heq]
  exact h

private theorem err_panic_core {prog : Program} {fnBase : BitVec 64}
    {img : Obj.Image} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {stk : Nat}
    {x : BundleReadGhost} {s0 s : State} {P F : SepProp}
    (hf200 : prog.fetch (fnBase + bv% (200)) =
      some (.moveWide .W32 .MOVZ (.gpr 0#5) 1#16 0))
    (hf204 : prog.fetch (fnBase + bv% (204)) =
      some (.moveWide .W32 .MOVZ (.gpr 1#5) 22#16 0))
    (hf208 : prog.fetch (fnBase + bv% (208)) =
      some (.bl (bv% (ls_rel% bundleReadName "alloc::raw_vec::handle_error" - 208))))
    (hext : prog.externAt? (fnBase + bv% (ls_rel% bundleReadName "alloc::raw_vec::handle_error")) =
      some Rust.panicked)
    (hPC : s.pc = fnBase + bv% (200))
    (hRun : s.status = .Running)
    (haf : allocFailedIn s0 s)
    (hpref : s0.trace <+: s.trace) :
    SepWPp prog (s0.readReg64 .lr) s (P ∗ F)
      (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ F)
      (fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ F) := by
  apply SepWPp.seq_frozen
    (mid := fnBase + bv% (ls_rel% bundleReadName "alloc::raw_vec::handle_error"))
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial
  wp_steps
  apply bind_sepWP_state; intro s1
  refine SepWP.done ?_ ?_ ?_
  · simp [s1, arm64_norm]
  · simp [s1, arm64_norm, hRun]
  · intro _ R hm1 _hL
    have hpc1 : s1.pc = fnBase + bv% (ls_rel% bundleReadName "alloc::raw_vec::handle_error") := by
      simp [s1, arm64_norm]
    have hrun1 : s1.status = .Running := by simp [s1, arm64_norm, hRun]
    have hext1 : prog.externAt? s1.pc = some Rust.panicked := by
      rw [hpc1]; exact hext
    have htr1 : (Rust.panicked s1).trace = s.trace := by simp [Rust.panicked, s1, arm64_norm]
    refine ⟨Rust.panicked s1,
      Steps.step (Step.extern hrun1 hext1 (Memory.KeepsFrozen.refl _)) (Steps.refl _),
      Or.inr (Or.inl ⟨rfl, _, ?_, rfl⟩)⟩
    dsimp only [bundleReadSpec, Spec.inImage]
    have hpure : allocFailedIn s0 (Rust.panicked s1) ∧ s0.trace <+: (Rust.panicked s1).trace := by
      refine ⟨?_, htr1 ▸ hpref⟩
      unfold allocFailedIn at haf ⊢
      rwa [htr1]
    have hent : (P ∗ F) ⊢ (⌜allocFailedIn s0 (Rust.panicked s1) ∧
        s0.trace <+: (Rust.panicked s1).trace⌝ ∗ anyHeap) ∗ F :=
      sepConj_mono_left (Entails.pure_right hpure (entails_anyHeap _))
    exact Satisfies.mono (sepConj_mono_left hent) hm1

/-- OOM panic block (`+208 .. +216`): calls `alloc::raw_vec::handle_error(1, 22)`. -/
theorem err_panic_step {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {stk : Nat}
    {x : BundleReadGhost} {s0 s : State} {P F : SepProp}
    (hPC : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName + bv% (200))
    (hRun : s.status = .Running)
    (haf : allocFailedIn s0 s)
    (hpref : s0.trace <+: s.trace) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s (P ∗ F)
      (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ F)
      (fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ F) :=
  err_panic_core
    (rebase_fetch_of_fnAddr rfl ((ls_rebase_fetch% bundleRead (ls_off% bundleReadName + 200)) img.base (Rust.withPanics ext)))
    (rebase_fetch_of_fnAddr rfl ((ls_rebase_fetch% bundleRead (ls_off% bundleReadName + 204)) img.base (Rust.withPanics ext)))
    (rebase_fetch_of_fnAddr rfl ((ls_rebase_fetch% bundleRead (ls_off% bundleReadName + 208)) img.base (Rust.withPanics ext)))
    (panic_at_handle_error_bundleRead img.base ext)
    hPC hRun haf hpref

private theorem buf22_reassoc_14_8 (buf d0 d1 : BitVec 64) :
    ((buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6) ⊢
      ∃∗ d2 : BitVec 64, memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) := by
  have h16 : memRegion buf 8 ∗ memRegion (buf + 8#64) 8 = memRegion buf 16 :=
    (memRegion_split buf 8 8 (by decide)).symm
  have h22 : memRegion buf 16 ∗ memRegion (buf + 16#64) 6 = memRegion buf 22 :=
    (memRegion_split buf 16 6 (by decide)).symm
  have h14_8 : memRegion buf 22 = memRegion buf 14 ∗ memRegion (buf + 14#64) 8 :=
    memRegion_split buf 14 8 (by decide)
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion buf d0)
      (sepConj_mono_left (pointsTo64_entails_memRegion (buf + 8#64) d1))) ?_
  rw [← sepConj_assoc, h16, h22, h14_8, ProofLib.memRegion_eight (buf + 14#64), sepExists_sepConj_right]
  exact Entails.refl _

private theorem buf22_reassoc_14_8_rest (buf d0 d1 : BitVec 64) (Q : SepProp) :
    ((buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6 ∗ Q) ⊢
    ((∃∗ d2 : BitVec 64, memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2)) ∗ Q) := by
  simpa [sepConj_assoc] using sepConj_mono_left (Q := Q) (buf22_reassoc_14_8 buf d0 d1)

private theorem buf22_merge_14_8 (buf d2 : BitVec 64) :
    (memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2)) ⊢ memRegion buf 22 := by
  rw [show (22 : Nat) = 14 + 8 from rfl, memRegion_split buf 14 8 (by decide)]
  exact sepConj_mono_right (pointsTo64_entails_memRegion (buf + 14#64) d2)

set_option maxHeartbeats 800000 in
/-- Non-null `Err` copy block (`+124 .. +188`): copies `"file could not be read"` into `buf`, writes `speAt` into `x.ret`, and jumps to `tail_dealloc_step`. -/
theorem err_copy_step {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : AllocContractsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hstk : 0x50 + extHookStack ≤ stk)
    (hstk_le : stk ≤ 2 ^ 64)
    {x : BundleReadGhost} {s0 s : State}
    {pathCap pathPtr buf : BitVec 64}
    {F : SepProp}
    (hPC : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName + bv% (128))
    (hRun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hAl0 : s0.spAligned = true)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx0_s : s.readReg64 .x0 = buf)
    (hbuf_ne : buf ≠ 0#64)
    (hx19_s : s.readReg64 .x19 = pathPtr)
    (hx20_s : s.readReg64 .x20 = x.ret)
    (hcap_pos : 0 < pathCap.toNat)
    (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hcs_hi : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hr_out : Except.error () = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ s.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (((A.live buf 22 1 ∗ memRegion buf 22 ∗
          memRegion x.ret 48 ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ F))
      (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ F)
      (fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ F) := by
  let ptrUnr := img.base + bv% (ls_xref% (ls_off% bundleReadName + 132) (ls_off% bundleReadName + 136))
  let ptrRead := img.base + bv% (ls_xref% (ls_off% bundleReadName + 176) (ls_off% bundleReadName + 180))
  have hadp1 :
      (((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr bundleReadName + bv% (132)) &&&
        0xfffffffffffff000#64) =
      img.base + bv% (page% (ls_off% bundleReadName + 132)) :=
    adrp_unreadable_page (H := Rust.withPanics ext) hb
  have hadp2 :
      (((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr bundleReadName + bv% (176)) &&&
        0xfffffffffffff000#64) =
      img.base + bv% (page% (ls_off% bundleReadName + 176)) :=
    adrp_read_page (H := Rust.withPanics ext) hb
  code_fetches_range libsignalSessionCode bundleReadBin img.base (Rust.withPanics ext)
    bundleRead_fnOff (num% (ls_off% bundleReadName)) 128 68
  dsimp only [tripleRatchetProgAtExt] at hPC ⊢
  generalize hfnBase : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    bundleReadName = fnBase at *
  generalize hprog : libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
  have hbuf22 : memRegion buf 22 =
      (∃∗ d1 : BitVec 64, ∃∗ d0 : BitVec 64,
        (buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6) := by
    have h16 : memRegion buf 16 = memRegion buf 8 ∗ memRegion (buf + 8#64) 8 :=
      memRegion_split buf 8 8 (by decide)
    rw [show (22 : Nat) = 16 + 6 from rfl, memRegion_split buf 16 6 (by decide),
        h16, ProofLib.memRegion_eight buf, ProofLib.memRegion_eight (buf + 8#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  rw [hbuf22]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWPp_exists_pre; intro d1
  apply sepWPp_exists_pre; intro d0
  apply sepWPp_mono_pre (by
    simpa [sepConj_assoc] using
      sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (sret_48_unpack x.ret))))))
  apply sepWPp_exists_pre; intro w5
  apply sepWPp_exists_pre; intro w4
  apply sepWPp_exists_pre; intro w3
  apply sepWPp_exists_pre; intro w2
  apply sepWPp_exists_pre; intro w1
  apply sepWPp_exists_pre; intro w0 R hm hL
  have hro : img.RoDataLoaded s.mem := (Obj.Image.frozenLoaded_iff.mp hF).2.1
  have hm_ro := rodata_unreadable_intro himg hro (rodata_read_intro himg hro hm)
  have hm_init : s.mem ⊨
      (((ptrUnr ↦ᵣ utf8 "file could not be read") ∗
        ((ptrRead ↦ᵣ utf8 "read") ∗
          A.live buf 22 1 ∗
          (buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6 ∗
          ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
            ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5)) ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool ∗ F)) ∗ R) := by
    refine satisfies_of_eq ?_ hm_ro
    dsimp only [ptrUnr, ptrRead]
    simp only [List.length_append, List.length_cons, List.length_nil]
    ac_rfl
  have hbuf_be : (buf == 0#64) = false := beq_false_of_ne hbuf_ne
  have hcap_ne : pathCap ≠ 0#64 := by intro heq; subst heq; simp at hcap_pos
  have hcap_be : (pathCap == 0#64) = false := beq_false_of_ne hcap_ne
  have _ := And.intro hadp1 (And.intro hadp2 (And.intro hbuf_ne (And.intro hbuf_be (And.intro hcap_ne hcap_be))))
  simp only [arm64_norm] at hx0_s hx20_s
  refine (?_ : SepWPp prog
    (s0.readReg64 .lr) s _ _ _) R hm_init hL
  apply SepWPp.seq_frozen
    (mid := fnBase + bv% (156))
    (Φ := fun m' => s.mem.KeepsFrozen m')
    (fun _ _ h12 h23 => Memory.KeepsFrozen.trans h12 h23)
    (Memory.KeepsFrozen.refl s.mem)
  wp_steps
  apply SepWP.step_ldrSimd128 rfl (by simp [arm64_norm, hRun]) (by assumption)
    rfl (by simp [ptrUnr, arm64_norm] : evalAddrMode _ _ = (ptrUnr, none)) rfl
    (SepLoad64.of_pointsToBytesRO rfl (off := 0) (by decide +kernel) (by simp))
    (SepLoad64.of_pointsToBytesRO rfl (off := 8) (by decide +kernel) rfl)
    rfl
  apply SepWP.step_ldur64 (by simp [arm64_norm] : _ = fnBase + 148#64)
    (by simp [arm64_norm, hRun]) (by assumption)
    rfl (by simp [ptrUnr, arm64_norm] : evalAddrMode _ _ = (ptrUnr + 14#64, none))
    (SepLoad64.of_pointsToBytesRO rfl (off := 14) (by decide +kernel) rfl)
    rfl
  simp (config := { zeta := false }) only [applyWriteback, State.pc_setPC,
    State.setPC_setPC, BitVec.add_assoc,
    show (144#64 : BitVec 64) + 4#64 = 148#64 from rfl,
    show (148#64 : BitVec 64) + 4#64 = 152#64 from rfl]
  wp_steps
  apply bind_sepWP_state; intro s_mid1
  refine SepWP.done ?_ ?_ ?_
  · simp [s_mid1, arm64_norm]
  · simp [s_mid1, arm64_norm, hRun]
  · intro hkf_mid1 R1 hm_mid1 hL_mid1
    have hF_mid1 : img.FrozenLoaded s_mid1 := hF.of_keepsFrozen hkf_mid1
    have hs_mid1_sp : s_mid1.sp = s0.sp - 80#64 := by simp [s_mid1, arm64_norm, hsp]
    have hs_mid1_x0 : s_mid1.readReg64 .x0 = buf := by simp [s_mid1, arm64_norm, hx0_s]
    have hs_mid1_x9 : s_mid1.readReg64 .x9 = 9223372036854775809#64 := by simp [s_mid1, arm64_norm]
    have hs_mid1_x19 : s_mid1.readReg64 .x19 = pathPtr := by simp [s_mid1, arm64_norm, hx19_s]
    have hs_mid1_x20 : s_mid1.readReg64 .x20 = x.ret := by simp [s_mid1, arm64_norm, hx20_s]
    have hs_mid1_tr : s_mid1.trace = s.trace := by simp [s_mid1, arm64_norm]
    have hs_mid1_run : s_mid1.status = .Running := by simp [s_mid1, arm64_norm, hRun]
    have hs_mid1_pc : s_mid1.pc = fnBase + bv% (156) := by simp [s_mid1, arm64_norm]
    have hm_mid1_re : s_mid1.mem ⊨
        (((ptrUnr ↦ᵣ utf8 "file could not be read") ∗
          (ptrRead ↦ᵣ utf8 "read") ∗
          A.live buf 22 1 ∗
          (∃∗ d2 : BitVec 64, memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2)) ∗
          ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
            ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5)) ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool ∗ F)) ∗ R1 := by
      refine satisfies_mono_rev hm_mid1 ?_
      simp only [sepConj_assoc]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (buf22_reassoc_14_8_rest buf _ _ _)))
    simp only [arm64_norm] at hs_mid1_x0 hs_mid1_x9 hs_mid1_x20
    refine (?_ : SepWPp prog
      (s0.readReg64 .lr) s_mid1 _ _ _) R1 hm_mid1_re hL_mid1
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWPp_exists_pre; intro d2
    apply SepWPp.seq_frozen
      (mid := fnBase + bv% (84))
      (Φ := fun m' => s_mid1.mem.KeepsFrozen m')
      (fun _ _ h12 h23 => Memory.KeepsFrozen.trans h12 h23)
      (Memory.KeepsFrozen.refl s_mid1.mem)
    wp_steps
    apply bind_sepWP_state; intro s_mid
    refine SepWP.done ?_ ?_ ?_
    · simp [s_mid, arm64_norm, hcap_be]
    · simp [s_mid, arm64_norm, hs_mid1_run]
    · intro hkf_mid R' hm_mid hL_mid
      have hF_mid : img.FrozenLoaded s_mid := hF_mid1.of_keepsFrozen hkf_mid
      subst hprog
      subst hfnBase
      have herr_pack_d2 : ∀ (v2 : BitVec 64),
          ((ptrUnr ↦ᵣ utf8 "file could not be read") ∗
            (ptrRead ↦ᵣ utf8 "read") ∗
            A.live buf 22 1 ∗
            memRegion buf 14 ∗
            ((buf + 14#64) ↦₆₄ v2) ∗
            (x.ret ↦₆₄ speWord 1) ∗ ((x.ret + 8#64) ↦₆₄ 22#64) ∗ ((x.ret + 16#64) ↦₆₄ buf) ∗
            ((x.ret + 24#64) ↦₆₄ 22#64) ∗ ((x.ret + 32#64) ↦₆₄ ptrRead) ∗
            ((x.ret + 40#64) ↦₆₄ 4#64)) ⊢
          (ptrUnr ↦ᵣ utf8 "file could not be read") ∗ getResultAt A x.ret (.error ()) := by
        intro v2
        have hre :
            ((ptrUnr ↦ᵣ utf8 "file could not be read") ∗
              (ptrRead ↦ᵣ utf8 "read") ∗
              A.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ v2) ∗
              (x.ret ↦₆₄ speWord 1) ∗ ((x.ret + 8#64) ↦₆₄ 22#64) ∗ ((x.ret + 16#64) ↦₆₄ buf) ∗
              ((x.ret + 24#64) ↦₆₄ 22#64) ∗ ((x.ret + 32#64) ↦₆₄ ptrRead) ∗
              ((x.ret + 40#64) ↦₆₄ 4#64)) =
            (ptrUnr ↦ᵣ utf8 "file could not be read") ∗
              ((x.ret ↦₆₄ speWord 1) ∗
                (((x.ret + 8#64) ↦₆₄ 22#64) ∗ ((x.ret + 16#64) ↦₆₄ buf) ∗
                  ((x.ret + 24#64) ↦₆₄ 22#64) ∗ A.live buf 22 1 ∗
                  (memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ v2))) ∗
                (((x.ret + 32#64) ↦₆₄ ptrRead) ∗ ((x.ret + 40#64) ↦₆₄ 4#64) ∗
                  (ptrRead ↦ᵣ utf8 "read"))) := by
          ac_rfl
        rw [hre]
        exact sepConj_mono_right (Entails.trans
          (sepConj_mono_right (sepConj_mono_left
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (buf22_merge_14_8 buf v2)))))))
          (err_result_intro A x.ret buf ptrRead hbuf_ne))
      have hm_dropped : s_mid.mem ⊨
          ((getResultAt A x.ret (.error ()) ∗
            SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            stackAt (s0.sp - 80#64) (stk - 80) ∗
            memRegion (s0.sp - 80#64) 24 ∗
            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
            (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
            A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ F) ∗ R' := by
        have hm_step : s_mid.mem ⊨ (ptrUnr ↦ᵣ utf8 "file could not be read") ∗
            (((getResultAt A x.ret (.error ()) ∗
              SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
              SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
              stackAt (s0.sp - 80#64) (stk - 80) ∗
              memRegion (s0.sp - 80#64) 24 ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
              (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
              A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ F) ∗ R') :=
          satisfies_mono_rev hm_mid (by
            dsimp only [ptrUnr, ptrRead] at *
            simpa [arm64_norm, speWord, sepConj_assoc] using
              sepConj_mono_left (Q := (SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                stackAt (s0.sp - 80#64) (stk - 80) ∗
                memRegion (s0.sp - 80#64) 24 ∗
                (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool ∗ F) ∗ R')
                (herr_pack_d2 _))
        exact Satisfies.of_sep_right hm_step
      have htr_mid : s_mid.trace = s.trace :=
        (by simp [s_mid, arm64_norm] : s_mid.trace = s_mid1.trace).trans hs_mid1_tr
      exact
        (tail_dealloc_step hC hstk hstk_le
          (by simp [s_mid, s_mid1, tripleRatchetProgAtExt, arm64_norm, Program.fnAddr_rebase,
            hcap_be, hcap_ne])
          (by simp [s_mid, arm64_norm, hs_mid1_run])
          (by simp [s_mid, arm64_norm, hs_mid1_sp])
          hAl0
          hF_mid
          (by simpa [s_mid, s_mid1, arm64_norm] using hsym)
          (by simp [s_mid, arm64_norm, hs_mid1_x19])
          (by simp [s_mid, arm64_norm])
          hcap_pos hcap_lt
          (cs_hi_trans
            (cs_hi_of_eq
              (by simp [s_mid, s_mid1, arm64_norm]) (by simp [s_mid, s_mid1, arm64_norm])
              (by simp [s_mid, s_mid1, arm64_norm]) (by simp [s_mid, s_mid1, arm64_norm])
              (by simp [s_mid, s_mid1, arm64_norm]) (by simp [s_mid, s_mid1, arm64_norm])
              (by simp [s_mid, s_mid1, arm64_norm]) (by simp [s_mid, s_mid1, arm64_norm]))
            hcs_hi)
          ((by simp [s_mid, s_mid1, calleeSavedVRegs, arm64_norm] :
            calleeSavedVRegs s_mid = calleeSavedVRegs s).trans hvregs)
          ⟨hr_out.1, htr_mid.trans hr_out.2⟩)
        R' hm_dropped hL_mid

/-- `Err(())` branch from `+44`: allocates the 22-byte error buffer (panicking on null) and delegates to `err_copy_step`. -/
theorem err_branch_step {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : AllocContractsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hstk : 0x50 + extHookStack ≤ stk)
    (hstk_le : stk ≤ 2 ^ 64)
    {x : BundleReadGhost} {s0 s : State}
    {pathCap pathPtr : BitVec 64}
    {F : SepProp}
    (hPC : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName + bv% (44))
    (hRun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hAl0 : s0.spAligned = true)
    (hAl : s.spAligned = true)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx19_s : s.readReg64 .x19 = pathPtr)
    (hx20_s : s.readReg64 .x20 = x.ret)
    (hcap_pos : 0 < pathCap.toNat)
    (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hcs_hi : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hpref_s : s0.trace <+: s.trace)
    (hr_out : Except.error () = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ s.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (((ioVecAt A (s0.sp - 80#64) (.error ()) ∗
          memRegion x.ret 48 ∗
          SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ F))
      (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ F)
      (fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ F) := by
  have hshim := shim_ok_at_bundleRead hC extHookStack (Nat.le_refl _) (by decide)
  have halloc := alloc_ok_at_bundleRead hC
  code_fetches_range libsignalSessionCode bundleReadBin img.base (Rust.withPanics ext)
    bundleRead_fnOff (num% (ls_off% bundleReadName)) 44 12
  code_fetches_range libsignalSessionCode bundleReadBin img.base (Rust.withPanics ext)
    bundleRead_fnOff (num% (ls_off% bundleReadName)) 112 20
  dsimp only [tripleRatchetProgAtExt, ioVecAt] at hshim halloc hPC ⊢
  generalize hfnBase : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    bundleReadName = fnBase at *
  have hsplit_hk : stackAt (s0.sp - 80#64) (stk - 80) =
      memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
        stackAt (s0.sp - 80#64) extHookStack :=
    stackAt_split_sub (s0.sp - 80#64) (stk - 80) extHookStack (by omega) (by omega)
  apply SepWPp.seq_frozen
    (mid := fnBase + bv% (ls_rel% bundleReadName "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial
  wp_conv_pre => rw [← hsp]
  wp_steps
  apply bind_sepWP_state; intro s1
  refine SepWP.done ?_ ?_ ?_
  · simp [s1, arm64_norm]
  · simp [s1, arm64_norm, hRun]
  · intro _ R hm1 hL1
    rw [hsp] at hm1
    have hsp1 : s1.sp = s0.sp - 80#64 := by simp [s1, arm64_norm, hsp]
    have htr1 : s1.trace = s.trace := by simp [s1, arm64_norm]
    let frameShim : SepProp :=
      memRegion (s0.sp - 80#64) 24 ∗
        memRegion x.ret 48 ∗
        SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
        (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
        (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
        (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
        (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
        (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
        (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool ∗ F
    have hm1_shim : s1.mem ⊨ stackAt s1.sp extHookStack ∗ frameShim ∗ R := by
      rw [hsp1]
      have hpack24 := err_slot24_pack (s0.sp - 80#64)
      have hm1' : s1.mem ⊨
          (((s0.sp - 80#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion ((s0.sp - 80#64) + 8#64) 16) ∗
            (stackAt (s0.sp - 80#64) (stk - 80) ∗
              (memRegion x.ret 48 ∗
                SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool ∗ F ∗ R)) := by
        refine satisfies_of_eq ?_ hm1
        ac_rfl
      have hm1'' := Satisfies.mono (sepConj_mono_left hpack24) hm1'
      rw [hsplit_hk] at hm1''
      refine satisfies_of_eq ?_ hm1''
      dsimp only [frameShim]
      ac_rfl
    obtain ⟨s2, hsteps_shim, hout_shim, -⟩ :=
      subroutine_ok.no_fault_before_outcome hshim () (frameShim ∗ R) s1
        (by simp [s1, arm64_norm])
        (by simp [s1, arm64_norm, hRun])
        (by
          dsimp only [withStack, sessionShimSpec, Spec.inImage]
          rw [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
          exact ⟨⟨by simpa [s1, arm64_norm] using hF, by simpa [s1, arm64_norm] using hsym⟩,
            by simpa [sepConj_assoc] using hm1_shim⟩)
        (by simpa [State.spAligned, hsp1, ← hsp] using hAl)
        hL1
    rcases hout_shim with ⟨⟨hpcs2, _, hruns2⟩, ⟨hsps2, hcss2⟩, hpost_shim⟩ | ⟨_, hpost_shim⟩ |
        ⟨_, _, hpost_shim⟩ | ⟨_, hpost_shim⟩
    · dsimp only [withStack, sessionShimSpec, Spec.inImage] at hpost_shim
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_shim
      obtain ⟨htr2, hm2⟩ := hpost_shim
      have hsp2 : s2.sp = s0.sp - 80#64 := hsps2.trans hsp1
      have hF2 : img.FrozenLoaded s2 :=
        (by simpa [s1, arm64_norm] using hF : img.FrozenLoaded s1).of_keepsFrozen
          hsteps_shim.keepsFrozen
      have hsym2 : s2.symtab = img.symtab :=
        hsteps_shim.symtab_eq.trans (by simpa [s1, arm64_norm] using hsym)
      have hL2 := hsteps_shim.codeLoaded hL1
      have hpcs2' : s2.pc = fnBase + bv% (116) :=
        hpcs2.trans (by simp [s1, arm64_norm])
      have hwp_alloc :
          SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (s0.readReg64 .lr) s2
            ((stackAt (s0.sp - 80#64) extHookStack ∗ A.pool) ∗
              (memRegion (s0.sp - 80#64) 24 ∗
                memRegion x.ret 48 ∗
                SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
                (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ F))
            (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
              Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ F)
            (fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ F) := by
        apply SepWPp.seq_frozen
          (mid := fnBase + bv% (ls_rel% bundleReadName "__rustc::__rust_alloc"))
          (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial
        wp_steps
        apply bind_sepWP_state; intro s3
        refine SepWP.done ?_ ?_ ?_
        · simp [s3, arm64_norm]
        · simp [s3, arm64_norm, hruns2]
        · intro _ R3 hm3 hL3
          let restAlloc : SepProp :=
            memRegion (s0.sp - 80#64) 24 ∗
              memRegion x.ret 48 ∗
              SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
              SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
              memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
              (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
              A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ F
          have hsp3 : s3.sp = s0.sp - 80#64 := by simp [s3, arm64_norm, hsp2]
          obtain ⟨s4, hsteps_al, hout_al, -⟩ :=
            subroutine_ok.no_fault_before_outcome halloc (22, 1) (restAlloc ∗ R3) s3
              (by simp [s3, arm64_norm])
              (by simp [s3, arm64_norm, hruns2])
              (by
                dsimp only [rustAllocSpecWithStack, Spec.inImage]
                rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
                refine ⟨⟨by simpa [s3, arm64_norm] using hF2, by simpa [s3, arm64_norm] using hsym2⟩,
                  ⟨rfl, rfl, ⟨by omega, ⟨0, rfl⟩, by omega⟩⟩,
                  ?_⟩
                rw [hsp3]
                refine satisfies_of_eq ?_ hm3
                dsimp only [restAlloc]
                ac_rfl)
              (by simpa [State.spAligned, hsp3, ← hsp] using hAl)
              hL3
          rcases hout_al with ⟨⟨hpcs4, _, hruns4⟩, ⟨hsps4, hcss4⟩, hpost_al⟩ | ⟨_, hpost_al⟩ |
              ⟨_, _, hpost_al⟩ | ⟨_, hpost_al⟩
          · dsimp only [rustAllocSpecWithStack, Spec.inImage] at hpost_al
            have hpcs4' : s4.pc = fnBase + bv% (128) :=
              hpcs4.trans (by simp [s3, arm64_norm])
            have hsp4 : s4.sp = s0.sp - 80#64 := hsps4.trans hsp3
            have hF4 : img.FrozenLoaded s4 :=
              (by simpa [s3, arm64_norm] using hF2 : img.FrozenLoaded s3).of_keepsFrozen
                hsteps_al.keepsFrozen
            have hsym4 : s4.symtab = img.symtab :=
              hsteps_al.symtab_eq.trans (by simpa [s3, arm64_norm] using hsym2)
            have hL4 := hsteps_al.codeLoaded hL3
            have hx19_4 : s4.readReg64 .x19 = pathPtr :=
              hcss4.1.trans ((by simp [s3, arm64_norm] : s3.readReg64 .x19 = s2.readReg64 .x19).trans
                (hcss2.1.trans ((by simp [s1, arm64_norm] : s1.readReg64 .x19 = s.readReg64 .x19).trans hx19_s)))
            have hx20_4 : s4.readReg64 .x20 = x.ret :=
              hcss4.2.1.trans ((by simp [s3, arm64_norm] : s3.readReg64 .x20 = s2.readReg64 .x20).trans
                (hcss2.2.1.trans ((by simp [s1, arm64_norm] : s1.readReg64 .x20 = s.readReg64 .x20).trans hx20_s)))
            have hcs_hi4 : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
                s4.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩) :=
              cs_hi_trans (cs_hi_of_preserved hcss4)
                (cs_hi_trans
                  (cs_hi_of_eq
                    (by simp [s3, arm64_norm]) (by simp [s3, arm64_norm])
                    (by simp [s3, arm64_norm]) (by simp [s3, arm64_norm])
                    (by simp [s3, arm64_norm]) (by simp [s3, arm64_norm])
                    (by simp [s3, arm64_norm]) (by simp [s3, arm64_norm]))
                  (cs_hi_trans (cs_hi_of_preserved hcss2)
                    (cs_hi_trans
                      (cs_hi_of_eq
                        (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm])
                        (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm])
                        (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm])
                        (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm]))
                      hcs_hi)))
            have hv4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
              unfold CalleeSavedPreserved at hcss4 hcss2
              exact hcss4.2.2.2.2.2.2.2.2.2.2.2.trans
                ((by simp [s3, calleeSavedVRegs, arm64_norm] :
                  calleeSavedVRegs s3 = calleeSavedVRegs s2).trans
                  (hcss2.2.2.2.2.2.2.2.2.2.2.2.trans
                    ((by simp [s1, calleeSavedVRegs, arm64_norm] :
                      calleeSavedVRegs s1 = calleeSavedVRegs s).trans hvregs)))
            have htr3_eq : s3.trace = s.trace :=
              (by simp [s3, arm64_norm] : s3.trace = s2.trace).trans (htr2.trans htr1)
            by_cases hnull : s4.readReg64 .x0 = 0
            · simp only [hnull, ↓reduceIte, sepConj_assoc] at hpost_al
              have htr4_pure : s4.trace = s3.trace ++ [allocFailedEvent] := by
                have hm_p : s4.mem ⊨ ⌜s4.trace = s3.trace ++ [allocFailedEvent]⌝ ∗
                    (A.pool ∗ stackAt s3.sp extHookStack ∗ restAlloc ∗ R3) := by
                  refine satisfies_of_eq ?_ hpost_al
                  ac_rfl
                rw [satisfies_pure_sepConj] at hm_p
                exact hm_p.1
              have ⟨haf4, hpref4⟩ :=
                allocFailedIn_append_of_prefix (htr3_eq ▸ hpref_s) htr4_pure
              let restNoF : SepProp :=
                memRegion (s0.sp - 80#64) 24 ∗
                  memRegion x.ret 48 ∗
                  SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
                  (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                  (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                  (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                  (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                  (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                  (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                  (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                  A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat
              have hwp_null :
                  SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (s0.readReg64 .lr) s4
                    ((A.pool ∗ stackAt s3.sp extHookStack ∗
                        ⌜s4.trace = s3.trace ++ [allocFailedEvent]⌝ ∗ restNoF) ∗ F)
                    (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
                      Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ F)
                    (fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ F) := by
                have hz : (s4.readReg64 .x0 == 0#64) = true := beq_iff_eq.mpr hnull
                have hnull64 : s4.readReg64 .x0 = 0#64 := hnull
                have _ := And.intro hz hnull64
                apply SepWPp.seq_frozen
                  (mid := fnBase + bv% (200))
                  (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial
                wp_steps
                apply bind_sepWP_state; intro s5
                refine SepWP.done ?_ ?_ ?_
                · simp [s5, arm64_norm]
                · simp [s5, arm64_norm, hruns4]
                · intro _ R5 hm5 hL5
                  subst hfnBase
                  exact
                    (err_panic_step
                      (P := A.pool ∗ stackAt s3.sp extHookStack ∗
                        ⌜s4.trace = s3.trace ++ [allocFailedEvent]⌝ ∗ restNoF)
                      (F := F)
                      (by simp [s5, tripleRatchetProgAtExt, arm64_norm, Program.fnAddr_rebase])
                      (by simp [s5, arm64_norm, hruns4])
                      (by simpa [allocFailedIn, s5, arm64_norm] using haf4)
                      (by simpa [s5, arm64_norm] using hpref4))
                    R5 hm5 hL5
              have hm4_null : s4.mem ⊨
                  ((A.pool ∗ stackAt s3.sp extHookStack ∗
                      ⌜s4.trace = s3.trace ++ [allocFailedEvent]⌝ ∗ restNoF) ∗ F) ∗ R3 := by
                refine satisfies_of_eq ?_ hpost_al
                dsimp only [restAlloc, restNoF]
                ac_rfl
              obtain ⟨sf, hsteps_rest, hout_rest⟩ := hwp_null R3 hm4_null hL4
              exact ⟨sf, hsteps_al.trans hsteps_rest, hout_rest⟩
            · simp only [hnull, ↓reduceIte, sepConj_assoc] at hpost_al
              have htr4_pure : s4.trace = s3.trace := by
                have hm_p : s4.mem ⊨
                    ⌜(s4.readReg64 .x0).toNat % 1 = 0 ∧ s4.trace = s3.trace⌝ ∗
                    (A.pool ∗ stackAt s3.sp extHookStack ∗
                      A.live (s4.readReg64 .x0) 22 1 ∗ memRegion (s4.readReg64 .x0) 22 ∗
                      restAlloc ∗ R3) := by
                  refine satisfies_of_eq ?_ hpost_al
                  ac_rfl
                rw [satisfies_pure_sepConj] at hm_p
                exact hm_p.1.2
              have htr4_s : s4.trace = s.trace := htr4_pure.trans htr3_eq
              have hm4_packed : s4.mem ⊨
                  (((A.live (s4.readReg64 .x0) 22 1 ∗ memRegion (s4.readReg64 .x0) 22 ∗
                    memRegion x.ret 48 ∗
                    SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                    SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                    stackAt (s0.sp - 80#64) (stk - 80) ∗
                    memRegion (s0.sp - 80#64) 24 ∗
                    (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                    (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                    (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                    (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                    (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                    (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                    (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                    A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ F) ∗
                    R3) := by
                rw [hsp3] at hpost_al
                have hm_drop_p : s4.mem ⊨
                    ⌜(s4.readReg64 .x0).toNat % 1 = 0 ∧ s4.trace = s3.trace⌝ ∗
                    (((A.live (s4.readReg64 .x0) 22 1 ∗ memRegion (s4.readReg64 .x0) 22 ∗
                      memRegion x.ret 48 ∗
                      SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                      SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                      (memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
                        stackAt (s0.sp - 80#64) extHookStack) ∗
                      memRegion (s0.sp - 80#64) 24 ∗
                      (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                      (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                      (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                      (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                      (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                      (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                      (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                      A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ F) ∗ R3) := by
                  refine satisfies_of_eq ?_ hpost_al
                  dsimp only [restAlloc]
                  ac_rfl
                rw [← hsplit_hk] at hm_drop_p
                rw [satisfies_pure_sepConj] at hm_drop_p
                exact hm_drop_p.2
              subst hfnBase
              obtain ⟨sf, hsteps_cp, hout_cp⟩ :=
                (err_copy_step himg hC hb hstk hstk_le hpcs4' hruns4 hsp4 hAl0 hF4 hsym4
                  rfl hnull hx19_4 hx20_4 hcap_pos hcap_lt hcs_hi4 hv4
                  ⟨hr_out.1, htr4_s.trans hr_out.2⟩)
                  R3 hm4_packed hL4
              exact ⟨sf, hsteps_al.trans hsteps_cp, hout_cp⟩
          · exact (not_satisfies_false_sepConj hpost_al).elim
          · exact (not_satisfies_false_sepConj hpost_al).elim
          · exact (not_satisfies_false_sepConj hpost_al).elim
      have hm2_for_alloc : s2.mem ⊨
          ((stackAt (s0.sp - 80#64) extHookStack ∗ A.pool) ∗
            (memRegion (s0.sp - 80#64) 24 ∗
              memRegion x.ret 48 ∗
              SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
              SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
              memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
              (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
              A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ F)) ∗ R := by
        rw [hsp1] at hm2
        refine satisfies_of_eq ?_ hm2
        dsimp only [frameShim]
        ac_rfl
      obtain ⟨sf, hsteps_rest, hout_rest⟩ := hwp_alloc R hm2_for_alloc hL2
      exact ⟨sf, hsteps_shim.trans hsteps_rest, hout_rest⟩
    · exact (not_satisfies_false_sepConj hpost_shim).elim
    · exact (not_satisfies_false_sepConj hpost_shim).elim
    · exact (not_satisfies_false_sepConj hpost_shim).elim

private theorem satisfies_vecU8_unpack {A : RustAlloc} {m : Memory} {a : BitVec 64}
    {p : List (BitVec 8)} {Q : SepProp}
    (hp : 0 < p.length)
    (hm : m ⊨ vecU8 A a p ∗ Q) :
    ∃ cap ptr : BitVec 64,
      0 < cap.toNat ∧ p.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 ∧
      (m ⊨ (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 p.length)) ∗
        (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ p) ∗
          memRegion (ptr + BitVec.ofNat 64 p.length) (cap.toNat - p.length))) ∗ Q) := by
  dsimp only [vecU8, vecU8At, vecHeader] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨cap, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨ptr, hm⟩ := hm
  have hpure : p.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 := by
    have hm' : m ⊨ ⌜p.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 p.length)) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ p) ∗
             memRegion (ptr + BitVec.ofNat 64 p.length) (cap.toNat - p.length))) ∗ Q) := by
      refine satisfies_of_eq ?_ hm
      ac_rfl
    rw [satisfies_pure_sepConj] at hm'
    exact hm'.1
  have hpos : 0 < cap.toNat := Nat.lt_of_lt_of_le hp hpure.1
  have hne : cap ≠ 0 := by intro h0; subst h0; simp at hpos
  simp only [hne, ↓reduceIte] at hm
  refine ⟨cap, ptr, hpos, hpure.1, hpure.2.1, hpure.2.2, ?_⟩
  have hm'' : m ⊨ ⌜p.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 p.length)) ∗
        (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ p) ∗
          memRegion (ptr + BitVec.ofNat 64 p.length) (cap.toNat - p.length))) ∗ Q) := by
    refine satisfies_of_eq ?_ hm
    ac_rfl
  rw [satisfies_pure_sepConj] at hm''
  exact hm''.2

/-- `read_bundle::{closure#0}` satisfies `bundleReadSpec` given `Obj.Loads libsignalSessionImage img` and 32-bit joined-path length bounds. -/
theorem bundleRead_ok_of_loads {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {pathStk readStk stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hC : AllocContractsX img A ext)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hRead : ReadCallHyp img A ext rd pathOk readStk)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x50 + max (max pathStk readStk) extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName)
      (bundleReadSpec rd pathOk A img stk) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc0 hrun0 hpre0 hAl0 hL0 => ?_
  have hpath_le : pathStk ≤ stk - 80 := by omega
  have hread_le : readStk ≤ stk - 80 := by omega
  have hext_le : 0x50 + extHookStack ≤ stk := by omega
  dsimp only [bundleReadSpec, Spec.inImage] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hF0, hsym0⟩,
    ⟨hx0_0, hx1_0, hx2_0, hx3_0, hx4_0, hdir_lt, hname_lt, hpOk⟩, hm0⟩
  have hstk_le : stk ≤ 2 ^ 64 := stk_le_two_pow_64 (by
    have hre : ((SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ A.pool) ∗ R) =
      memRegion x.ret 48 ∗ stackAt s0.sp stk ∗
        (SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ A.pool ∗ R) := by
      ac_rfl
    rwa [hre] at hm0)
  have hAl_frame : (s0.sp - 80#64) &&& 15#64 = 0#64 := by
    have hal : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hAl0
    bv_bits
  code_fetches_range libsignalSessionCode bundleReadBin img.base (Rust.withPanics ext)
    bundleRead_fnOff (num% (ls_off% bundleReadName)) 0 28
  code_fetches_range libsignalSessionCode bundleReadBin img.base (Rust.withPanics ext)
    bundleRead_fnOff (num% (ls_off% bundleReadName)) 28 12
  dsimp only [tripleRatchetProgAtExt] at hpc0 hPath hFs ⊢
  generalize hfnBase : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    bundleReadName = fnBase at *
  have hstk80 : stackAt s0.sp stk =
      stackAt (s0.sp - 80#64) (stk - 80) ∗ memRegion (s0.sp - 80#64) 80 :=
    stackAt_frame_80_eq s0.sp stk (by omega) hstk_le
  have hsplit_path : stackAt (s0.sp - 80#64) (stk - 80) =
      memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - pathStk) ∗
        stackAt (s0.sp - 80#64) pathStk :=
    stackAt_split_sub (s0.sp - 80#64) (stk - 80) pathStk hpath_le (by omega)
  have hwp_all :
      SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (s0.readReg64 .lr) s0
        ((SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ A.pool) ∗ emp)
        (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ emp)
        (fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ emp) := by
    rw [hstk80, hsplit_path]
    simp only [sepConj_assoc]
    apply sepWPp_mono_pre (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (frame_80_unpack (s0.sp - 80#64))))))))
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply sepWPp_exists_pre; intro v19
    apply sepWPp_exists_pre; intro v20
    apply sepWPp_exists_pre; intro v30
    apply sepWPp_exists_pre; intro v29
    have _ := And.intro hx0_0 (And.intro hx1_0 hx3_0)
    apply SepWPp.seq_frozen
      (mid := (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr pathName)
      (Φ := fun m' => s0.mem.KeepsFrozen m')
      (fun _ _ h12 h23 => Memory.KeepsFrozen.trans h12 h23)
      (Memory.KeepsFrozen.refl s0.mem)
    wp_steps
    apply bind_sepWP_state; intro s1
    refine SepWP.done ?_ ?_ ?_
    · simp only [s1, arm64_norm]
      rw [← hfnBase]
      simp only [Program.fnAddr_rebase, bundleRead_fnOff, path_fnOff]
      bv_bits
    · simp [s1, arm64_norm, hrun0]
    · intro hkf1 R1 hm1 hL1
      have hF1 : img.FrozenLoaded s1 := hF0.of_keepsFrozen hkf1
      let gPath : PathGhost :=
        { dirA := x.dirA, dir := x.dir, dirRo := x.dirRo,
          nameA := x.nameA, name := x.name, nameRo := x.nameRo,
          ret := (s0.sp - 80#64) + 24#64 }
      let framePath : SepProp :=
        memRegion x.ret 48 ∗
          memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - pathStk) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19)
      have hsp1 : s1.sp = s0.sp - 80#64 := by simp [s1, arm64_norm]
      have htr1 : s1.trace = s0.trace := by simp [s1, arm64_norm]
      have hLiftPath := subroutine_ok_withFsInv hFs hPath s0.fs.files s0.trace
      obtain ⟨s2, hsteps_path, hout_path, -⟩ :=
        subroutine_ok.no_fault_before_outcome hLiftPath gPath (framePath ∗ R1) s1
          (by
            simp only [s1, arm64_norm]
            rw [← hfnBase]
            simp only [Program.fnAddr_rebase, bundleRead_fnOff, path_fnOff]
            bv_bits)
          (by simp [s1, arm64_norm, hrun0])
          (withFsInv_pre_intro
            ⟨[], by simp [htr1], fun _ => by simp [s1, arm64_norm]⟩
            (by
              dsimp only [pathSpec, Spec.inImage]
              rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
              refine ⟨⟨hF1, by simpa [s1, arm64_norm] using hsym0⟩,
                ⟨by simp [s1, gPath, arm64_norm]; bv_bits,
                 by simp [s1, gPath, arm64_norm, hx1_0],
                 by simpa [s1, gPath, arm64_norm] using hx2_0,
                 by simp [s1, gPath, arm64_norm, hx3_0],
                 by simpa [s1, gPath, arm64_norm] using hx4_0,
                 hdir_lt, hname_lt⟩,
                ?_⟩
              rw [hsp1]
              have hm1_clean : s1.mem ⊨
                  SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  memRegion x.ret 48 ∗
                  memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - pathStk) ∗
                  stackAt (s0.sp - 80#64) pathStk ∗
                  memRegion (s0.sp - 80#64) 24 ∗
                  memRegion ((s0.sp - 80#64) + 24#64) 24 ∗
                  (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                  (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                  (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                  (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                  A.pool ∗ R1 := by
                simpa [arm64_norm, sepConj_emp, sepConj_assoc] using hm1
              refine satisfies_of_eq ?_ hm1_clean
              dsimp only [gPath, framePath]
              ac_rfl))
          (by simpa [State.spAligned, hsp1] using hAl_frame)
          hL1
      rcases hout_path with ⟨⟨hpcs2, _, hruns2⟩, ⟨hsps2, hcss2⟩, hpost_path⟩ |
          ⟨hpan2, hpost_path⟩ | ⟨_, _, hpost_path⟩ | ⟨_, hpost_path⟩
      · obtain ⟨hinv2, hpost_p⟩ := withFsInv_post_elim hpost_path
        dsimp only [pathSpec, Spec.inImage] at hpost_p
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_p
        obtain ⟨htr2_eq, hm2⟩ := hpost_p
        have htr2 : s2.trace = s0.trace := htr2_eq.trans htr1
        have hsp2 : s2.sp = s0.sp - 80#64 := hsps2.trans hsp1
        have hpcs2' : s2.pc = fnBase + bv% (28) :=
          hpcs2.trans (by simp [s1, arm64_norm])
        clear hpcs2
        have hF2 : img.FrozenLoaded s2 := hF1.of_keepsFrozen hsteps_path.keepsFrozen
        have hsym2 : s2.symtab = img.symtab :=
          hsteps_path.symtab_eq.trans (by simpa [s1, arm64_norm] using hsym0)
        have hL2 := hsteps_path.codeLoaded hL1
        let p := x.dir ++ [0x2f#8] ++ x.name
        have hp_len_pos : 0 < p.length := by simp [p]
        have hp_len_lt32 : p.length < 2 ^ 32 := hpLen p hpOk
        obtain ⟨pathCap, pathPtr, hcap_pos, hp_le_cap, hcap_lt63, _hptr_ne, hm2_unp⟩ :=
          satisfies_vecU8_unpack (p := p) hp_len_pos (by
            dsimp only [gPath, p] at hm2 ⊢
            rw [sepConj_assoc] at hm2
            exact hm2)
        have hsplit_read : stackAt (s0.sp - 80#64) (stk - 80) =
            memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - readStk) ∗
              stackAt (s0.sp - 80#64) readStk :=
          stackAt_split_sub (s0.sp - 80#64) (stk - 80) readStk hread_le (by omega)
        let frameRead : SepProp :=
          memRegion x.ret 48 ∗
            SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - readStk) ∗
            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
            (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 p.length) ∗
            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
            A.live pathPtr pathCap.toNat 1 ∗
            memRegion (pathPtr + BitVec.ofNat 64 p.length) (pathCap.toNat - p.length)
        have hm2_read : s2.mem ⊨
            (((pathPtr ↦ₛ p) ∗ memRegion (s0.sp - 80#64) 24 ∗
              stackAt (s0.sp - 80#64) readStk ∗ A.pool) ∗ frameRead) ∗ R1 := by
          rw [hsp1] at hm2_unp
          have hm2_stk : s2.mem ⊨
              (memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - pathStk) ∗
                stackAt (s0.sp - 80#64) pathStk) ∗
                ((pathPtr ↦ₛ p) ∗ memRegion (s0.sp - 80#64) 24 ∗ A.pool ∗
                  memRegion x.ret 48 ∗
                  SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                  (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                  (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 p.length) ∗
                  (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                  (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                  (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                  (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                  A.live pathPtr pathCap.toNat 1 ∗
                  memRegion (pathPtr + BitVec.ofNat 64 p.length) (pathCap.toNat - p.length) ∗ R1) := by
            dsimp only [framePath, p] at hm2_unp ⊢
            refine satisfies_of_eq ?_ hm2_unp
            rw [BitVec.add_assoc (s0.sp - 80#64) 24#64 8#64,
                BitVec.add_assoc (s0.sp - 80#64) 24#64 16#64,
                show (24#64 : BitVec 64) + 8#64 = 32#64 from rfl,
                show (24#64 : BitVec 64) + 16#64 = 40#64 from rfl]
            ac_rfl
          rw [← hsplit_path, hsplit_read] at hm2_stk
          refine satisfies_of_eq ?_ hm2_stk
          dsimp only [frameRead]
          ac_rfl
        have hwp_after_path :
            SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (s0.readReg64 .lr) s2
              ((((pathPtr ↦ₛ p) ∗ memRegion (s0.sp - 80#64) 24 ∗
                  stackAt (s0.sp - 80#64) readStk ∗ A.pool) ∗ frameRead) ∗ emp)
              (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
                Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ emp)
              (fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ emp) := by
          apply SepWPp.seq_frozen
            (mid := fnBase + bv% (40))
            (Φ := fun m' => s2.mem.KeepsFrozen m')
            (fun _ _ h12 h23 => Memory.KeepsFrozen.trans h12 h23)
            (Memory.KeepsFrozen.refl s2.mem)
          wp_conv_pre => dsimp only [frameRead]; rw [← hsp2]
          wp_steps
          apply bind_sepWP_state; intro s3
          refine SepWP.done ?_ ?_ ?_
          · simp [s3, arm64_norm]
          · simp [s3, arm64_norm, hruns2]
          · intro hkf3 R3 hm3 hL3
            have hF3 : img.FrozenLoaded s3 := hF2.of_keepsFrozen hkf3
            subst hfnBase
            have hsp3 : s3.sp = s0.sp - 80#64 := by simp [s3, arm64_norm, hsp2]
            have htr3 : s3.trace = s0.trace :=
              (by simp [s3, arm64_norm] : s3.trace = s2.trace).trans htr2
            have hx1_3 : (s3.readReg64 .x1).toNat = p.length := by
              have hlt64 : p.length < 18446744073709551616 := by omega
              simp [s3, arm64_norm, Nat.mod_eq_of_lt hlt64]
            have hm3_norm : s3.mem ⊨
                (((pathPtr ↦ₛ p) ∗ memRegion (s0.sp - 80#64) 24 ∗
                  stackAt s3.sp readStk ∗ A.pool) ∗ (frameRead ∗ emp)) ∗ R3 := by
              rw [hsp3]
              rw [hsp2] at hm3
              refine satisfies_of_eq ?_ hm3
              dsimp only [frameRead]
              ac_rfl
            exact
              (readCall_step hRead hFs s0.fs.files s0.trace
                (ret := s0.readReg64 .lr)
                (F := frameRead ∗ emp)
                (Q := fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
                  Q = (bundleReadSpec rd pathOk A img stk).post x s0 sf ∗ emp)
                (Qp := fun sf Qp => Qp = (bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ emp)
                (s0 := s0) (s := s3)
                (by simp [s3, tripleRatchetProgAtExt, arm64_norm, Program.fnAddr_rebase])
                (by simp [s3, arm64_norm, hruns2])
                (by simpa [State.spAligned, hsp3] using hAl_frame)
                hF3
                (by simpa [s3, arm64_norm] using hsym2)
                (by
                  obtain ⟨w, hw1, hw2⟩ := hinv2
                  exact ⟨w, by simpa [s3, arm64_norm] using hw1,
                    by simpa [s3, arm64_norm] using hw2⟩)
                htr3 rfl
                (by simp [s3, arm64_norm])
                hx1_3
                (by simp [s3, arm64_norm, hsp2])
                hp_len_lt32 hpOk
                (fun s4 hpcs4 hruns4 hsps4 hAls4 hcss4 hF4 hsym4 _hinv4 r hr4 => by
                  have hsp4 : s4.sp = s0.sp - 80#64 := hsps4.trans hsp3
                  have hx19_4 : s4.readReg64 .x19 = pathPtr :=
                    hcss4.1.trans (by simp [s3, arm64_norm])
                  have hx20_4 : s4.readReg64 .x20 = x.ret :=
                    hcss4.2.1.trans ((by simp [s3, arm64_norm] : s3.readReg64 .x20 = s2.readReg64 .x20).trans
                      (hcss2.2.1.trans (by simp [s1, arm64_norm, hx0_0])))
                  have hcs_hi4 : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
                      s4.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩) :=
                    cs_hi_trans (cs_hi_of_preserved hcss4)
                      (cs_hi_trans
                        (cs_hi_of_eq
                          (by simp [s3, arm64_norm]) (by simp [s3, arm64_norm])
                          (by simp [s3, arm64_norm]) (by simp [s3, arm64_norm])
                          (by simp [s3, arm64_norm]) (by simp [s3, arm64_norm])
                          (by simp [s3, arm64_norm]) (by simp [s3, arm64_norm]))
                        (cs_hi_trans (cs_hi_of_preserved hcss2)
                          (cs_hi_of_eq
                            (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm])
                            (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm])
                            (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm])
                            (by simp [s1, arm64_norm]) (by simp [s1, arm64_norm]))))
                  have hv4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
                    unfold CalleeSavedPreserved at hcss4 hcss2
                    exact hcss4.2.2.2.2.2.2.2.2.2.2.2.trans
                      ((by simp [s3, calleeSavedVRegs, arm64_norm] :
                        calleeSavedVRegs s3 = calleeSavedVRegs s2).trans
                        (hcss2.2.2.2.2.2.2.2.2.2.2.2.trans
                          (by simp [s1, calleeSavedVRegs, arm64_norm] :
                            calleeSavedVRegs s1 = calleeSavedVRegs s0)))
                  have hpack_buf := path_buf_dealloc_pack pathPtr pathCap.toNat p hp_le_cap hcap_lt63
                  have hent_after_read :
                      (ioVecAt A (s0.sp - 80#64) r ∗ (pathPtr ↦ₛ p) ∗
                        stackAt s3.sp readStk ∗ A.pool ∗ (frameRead ∗ emp)) ⊢
                      ((ioVecAt A (s0.sp - 80#64) r ∗
                        memRegion x.ret 48 ∗
                        SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                        stackAt (s0.sp - 80#64) (stk - 80) ∗
                        (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                        (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                        (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                        (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                        (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                        (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                        (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                        A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ emp) := by
                    rw [hsp3]
                    have hre1 :
                        (ioVecAt A (s0.sp - 80#64) r ∗ (pathPtr ↦ₛ p) ∗
                          stackAt (s0.sp - 80#64) readStk ∗ A.pool ∗ (frameRead ∗ emp)) =
                        ((pathPtr ↦ₛ p) ∗
                          memRegion (pathPtr + BitVec.ofNat 64 p.length) (pathCap.toNat - p.length)) ∗
                        ((memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - readStk) ∗
                          stackAt (s0.sp - 80#64) readStk) ∗
                          (ioVecAt A (s0.sp - 80#64) r ∗
                            memRegion x.ret 48 ∗
                            SpqrV1.ChainProofs.bytesAt x.dirRo x.dirA x.dir ∗
                            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                            (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
                            A.live pathPtr pathCap.toNat 1 ∗ A.pool)) := by
                      dsimp only [frameRead, p]
                      simp only [sepConj_emp]
                      ac_rfl
                    rw [hre1, ← hsplit_read]
                    refine Entails.trans (sepConj_mono_left hpack_buf) (entails_of_eq ?_)
                    simp only [sepConj_emp]
                    ac_rfl
                  apply sepWPp_mono_pre hent_after_read
                  cases r with
                  | ok bs =>
                    exact ok_branch_step hC hext_le hstk_le hpcs4 hruns4 hsp4 hAl0 hF4 hsym4
                      hx19_4 hx20_4 hcap_pos hcap_lt63 hcs_hi4 hv4 hr4
                  | error u =>
                    cases u
                    have hpref4 : s0.trace <+: s4.trace := hr4.2 ▸ List.prefix_refl _
                    exact err_branch_step himg hC hb hext_le hstk_le hpcs4 hruns4 hsp4 hAl0 hAls4
                      hF4 hsym4 hx19_4 hx20_4 hcap_pos hcap_lt63 hcs_hi4 hv4 hpref4 hr4)
                (fun sf _ haf hpfx =>
                  ⟨(bundleReadSpec rd pathOk A img stk).onPanic x s0 sf ∗ emp, by
                    dsimp only [bundleReadSpec, Spec.inImage]
                    simp only [sepConj_emp]
                    exact Entails.pure_right ⟨haf, hpfx⟩ (entails_anyHeap _), rfl⟩))
                R3 hm3_norm hL3
        obtain ⟨sf, hsteps_rest, hout_rest⟩ :=
          hwp_after_path R1 (by simpa [sepConj_emp, sepConj_assoc] using hm2_read) hL2
        exact ⟨sf, hsteps_path.trans hsteps_rest, hout_rest⟩
      ·
        dsimp only [withFsInv, pathSpec, Spec.inImage] at hpost_path
        rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost_path
        obtain ⟨_hinv_p, ⟨haf_p, hpref_p⟩, hm_p⟩ := hpost_path
        refine ⟨s2, hsteps_path, Or.inr (Or.inl ⟨hpan2, _, ?_, rfl⟩)⟩
        dsimp only [bundleReadSpec, Spec.inImage]
        have hpure_pan : allocFailedIn s0 s2 ∧ s0.trace <+: s2.trace := by
          refine ⟨?_, htr1 ▸ hpref_p⟩
          unfold allocFailedIn at haf_p ⊢
          rwa [htr1] at haf_p
        have hent_pan : (anyHeap ∗ framePath) ⊢
            (⌜allocFailedIn s0 s2 ∧ s0.trace <+: s2.trace⌝ ∗ anyHeap) ∗ emp := by
          rw [sepConj_emp]
          exact Entails.pure_right hpure_pan (entails_anyHeap _)
        rw [← sepConj_assoc] at hm_p
        exact Satisfies.mono (sepConj_mono_left hent_pan) hm_p
      · dsimp only [withFsInv, pathSpec, Spec.inImage] at hpost_path
        rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost_path
        exact hpost_path.2.1.elim
      · dsimp only [withFsInv, pathSpec, Spec.inImage] at hpost_path
        rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost_path
        exact hpost_path.2.1.elim
  obtain ⟨sf, hsteps_all, hout_all⟩ :=
    hwp_all R (by simpa [sepConj_emp, sepConj_assoc] using hm0) hL0
  refine reaches_outcome_steps hsteps_all (reaches_outcome.of_outcome ?_)
  rcases hout_all with ⟨hpcf, hrunf, _, hmf, hsp_f, hcs_f, rfl⟩ | ⟨hp1, _, hmf, rfl⟩ | ⟨_, hmo⟩
  · exact Or.inl ⟨⟨hpcf, hsp_f, hrunf⟩, ⟨hsp_f, hcs_f⟩,
      by simpa [sepConj_emp, sepConj_assoc] using hmf⟩
  · exact Or.inr (Or.inl ⟨hp1,
      by simpa [sepConj_emp, sepConj_assoc] using hmf⟩)
  · exact (not_satisfies_false_sepConj hmo).elim

end CryptoVerification.SignalSession.Cli.BundleRead.Helpers

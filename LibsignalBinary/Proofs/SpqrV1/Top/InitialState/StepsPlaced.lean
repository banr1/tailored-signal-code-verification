/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Steps
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# Relocatable V1 Path Step Lemmas for `spqr::initial_state`

Segment steppers and full `.v1` body composition (`initial_state_v1_body_placed`) for
`spqr::initial_state` (Block `327`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.InitialState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.Placed
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local wp_norm] csel_maxJump_eq csel_maxOoo_eq
attribute [local arm64_norm] bv_sub_add_lit

theorem h61s_stackAt_initialState_split (sp : BitVec 64) :
    stackAt sp initialStateStack =
      stackAt (sp - 496#64) initInnerStack ∗ memRegion (sp - 496#64) 40 ∗
      memRegion (sp - 456#64) 352 ∗ memRegion (sp - 104#64) 8 ∗ cells (sp - 96#64) 12 :=
  h61s_stackAt_split_gen sp initInnerStack

theorem h61s_stack_restore_initialState (s0 : State) :
    stackAt (s0.sp - 496#64) initInnerStack ∗ memRegion (s0.sp - 496#64) 40 ∗
    memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
    h61s_initialStateSavedCells s0 ⊢ stackAt s0.sp initialStateStack :=
  h61s_stack_restore_gen s0 initInnerStack

theorem stackAt_initInner_split_allocHook (sp : BitVec 64) :
    stackAt sp initInnerStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 17680#64) 13584 :=
  stackAt_callee_split sp initInnerStack allocHookStack

theorem stackAt_initInner_split_encodeToVec (sp : BitVec 64) :
    stackAt sp initInnerStack =
      stackAt sp encodeToVecStackX ∗ memRegion (sp - 17680#64) (initInnerStack - encodeToVecStackX) :=
  stackAt_callee_split sp initInnerStack encodeToVecStackX

theorem stackAt_initInner_split_dropStack96 (sp : BitVec 64) :
    stackAt sp initInnerStack =
      stackAt sp dropStack96 ∗ memRegion (sp - 17680#64) 13488 :=
  stackAt_callee_split sp initInnerStack dropStack96

/-! ## 1. Prologue (`+0 -> +232`) and Epilogue (`+396 -> +424 -> ret`) on `Block 327` -/

theorem initial_state_prologue_v1_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 : State) (x : InitialStateGhost) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = initialStatePlacedEntry)
    (hrun : s0.status = .Running) (hx0 : s0.readReg64 .x0 = x.pA) (hx8 : s0.readReg64 .x8 = x.ret)
    (hv : x.p.version = .v1) (hlen : x.p.authKey.length < 2 ^ 32) :
    SepWP (initialStatePlacedProg ext)
      (initialStatePlacedEntry + 232#64) s0
      (cells (s0.sp - 96#64) 12 ∗ paramsAt x.pA x.akPtr x.p ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ h61s_initialStateSavedCells s0 ∗ paramsAt x.pA x.akPtr x.p ∗
              (lsLogFilterAddr ↦₆₄ 0#64) ∗ Rest) ∧
        s1.sp = s0.sp - 496#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x19 = x.ret ∧ s1.readReg64 .x20 = x.pA ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
        s1.readReg64 .x22 = x.akPtr ∧ s1.readReg32 .x25 = 1#32 ∧ s1.trace = s0.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0) := by
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have htbz := testBit63_ofNat_of_lt hlen
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, paramsAt, lsLogFilterAddr,
    State.readReg32, Reg.x0, Reg.x8, Reg.x25, BitVec.ofNat_eq_ofNat]
    at hpc hx0 hx8 ⊢
  simp only [hv, Version.toI32]
  cells_unfold; wp_pull_exists
  dsimp only [h61s_initialStateSavedCells]
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

theorem initial_state_epilogue_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = initialStatePlacedEntry + 396#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64) (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 496#64) initInnerStack ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       h61s_initialStateSavedCells s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp initialStateStack ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrestore :
      (stackAt (s0.sp - 496#64) initInnerStack ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       h61s_initialStateSavedCells s0) ∗ Rest ⊢ stackAt s0.sp initialStateStack ∗ Rest :=
    sepConj_mono_left (h61s_stack_restore_initialState s0)
  refine SepWP.strengthen_entails_const hrestore ?_
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, h61s_initialStateSavedCells,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-! ## 2. `auth_key.to_vec()` (`+232 -> +284`) and OOM Panic (`+196 -> +204`) on `Block 327` -/

theorem initial_state_to_vec_empty_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (Rest : SepProp)
    (hpc : s.pc = initialStatePlacedEntry + 232#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.pA) (hx21 : s.readReg64 .x21 = 0#64)
    (hx22 : s.readReg64 .x22 = x.akPtr) (hw25 : s.readReg32 .x25 = 1#32)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext)
      (initialStatePlacedEntry + 284#64) s Rest
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
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry,
    State.readReg32, Reg.x25, BitVec.ofNat_eq_ofNat] at hpc hw25 ⊢
  wp_steps; wp_done

theorem initial_state_panic_196_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = initialStatePlacedEntry + 196#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (InitInnerPanic s0 R) := by
  have hpanic : (initialStatePlacedProg ext).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (ls_externAt?_of_mem (prog := initialStatePlacedProg ext) (i := 327)
      (H := Rust.withPanics ext) (sym := spqrHandleErrorSym)).trans h_panic
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, lsρ, spqrHandleErrorSym,
    BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  apply SepWPp.of_sepWP
    (mid := (blkPl_327).ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
  wp_steps
  apply ProofLib.SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [InitInnerPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem initial_state_to_vec_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym) framelessMemcpySpec)
    (s0 s : State) (x : InitialStateGhost) (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hlt : x.p.authKey.length < 2 ^ 63)
    (hpc : s.pc = initialStatePlacedEntry + 232#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.pA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length)
    (hx22 : s.readReg64 .x22 = x.akPtr) (hw25 : s.readReg32 .x25 = 1#32)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      sm.pc = initialStatePlacedEntry + 284#64 →
      sm.status = .Running → (LsCallInv lsmpl s.mem → LsCallInv lsmpl sm.mem) →
      sm.sp = s0.sp - 496#64 → sm.readReg64 .x29 = s0.sp - 96#64 →
      sm.readReg64 .x19 = x.ret → sm.readReg64 .x20 = x.pA →
      sm.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length →
      sm.readReg64 .x22 = x.akPtr → sm.readReg64 .x23 = ptr →
      sm.readReg32 .x25 = 1#32 → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) sm
        (RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
         (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) allocHookStack ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) allocHookStack ∗ Frame)
      Q (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  by_cases hlen_zero : x.p.authKey.length = 0
  · have hnil : x.p.authKey = [] := List.eq_nil_of_length_eq_zero hlen_zero
    have hx21_0 : s.readReg64 .x21 = 0#64 := by rw [hx21, hlen_zero]
    refine initInner_seq_sepWP_lsInv
      (initial_state_to_vec_empty_placed (A := A) s0 s x
        ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) allocHookStack ∗ Frame)
        hpc hrun hsp hx29 hx19 hx20 hx21_0 hx22 hw25 htrace hvregs) ?_
    intro sm hpcm hrunm _ hinvm ⟨hspm, hx29m, hx19m, hx20m, hx21m, hx22m, hx23m, hw25m, htrm, hvregsm⟩
    have hbuf_eq : RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) 1#64 x.p.authKey =
        RustHeap.vecU8Buf A 0#64 1#64 [] := by
      conv => lhs; rw [hnil]; dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
    have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length := by rw [hx21m, hlen_zero]
    rw [← hbuf_eq]
    exact hnext sm 1#64 hpcm hrunm hinvm hspm hx29m hx19m hx20m hx21m' hx22m hx23m hw25m htrm hvregsm
  · have hpos : 0 < x.p.authKey.length := Nat.pos_of_ne_zero hlen_zero
    have htoNat_len : (BitVec.ofNat 64 x.p.authKey.length).toNat = x.p.authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hne_bv0 : BitVec.ofNat 64 x.p.authKey.length ≠ 0#64 := by
      intro h; have h1 := congrArg BitVec.toNat h; rw [htoNat_len] at h1
      change x.p.authKey.length = 0 at h1; omega
    have hbeq0 : (BitVec.ofNat 64 x.p.authKey.length == 0#64) = false := beq_eq_false_iff_ne.mpr hne_bv0
    have hne0 : (BitVec.ofNat 64 x.p.authKey.length != 0#64) = true := bne_iff_ne.mpr hne_bv0
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk x.p.authKey.length 1 := ⟨hpos, hpow2, by omega⟩
    have hpanic : ∀ (sm : State) (P_mid : SepProp),
        sm.pc = initialStatePlacedEntry + 196#64 →
        sm.status = .Running → sm.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) sm P_mid Q
          (InitInnerPanic s0 R) :=
      fun sm P_mid hpcm hrunm htrm =>
        initial_state_panic_196_placed h_panic s0 sm P_mid R hpcm hrunm htrm
    simp only [noAllocShimSpec] at hshim
    simp only [rustAllocSpec] at halloc
    simp only [framelessMemcpySpec] at hmemcpy
    dsimp only [initialStatePlacedProg, initialStatePlacedEntry, lsρ, spqrRustNoAllocShimSym,
      spqrRustAllocSym, lsMemcpySym,
      State.readReg32, Reg.x25, BitVec.ofNat_eq_ofNat]
      at hpc hw25 hshim halloc hmemcpy hpanic ⊢
    refine sepWPp_of_sepWP_keepLsInv (mid := (blkPl_327).base + 256#64) ?_
    wp_steps; wp_apply; wp_steps; wp_apply
    apply ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _ hinv_sf1
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte]
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.sepWPp_pure_mid fun htr_oom => ?_
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.SepWPp.seq_clean (mid := (blkPl_327).base + 196#64)
        (P_mid := A.pool ∗ stackAt sf.sp allocHookStack ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent]) ?_ ?_
      · wp_steps; wp_done
      · intro sm hpcm hrunm htrm; exact hpanic sm _ hpcm hrunm htrm
    · have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      have hoom_bne : (sf_1.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len]; simp only [sepConj_assoc]
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine initInner_seq_sepWP_lsInv (mid := (blkPl_327).base + 284#64)
        (P' := RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr_c x.p.authKey ∗
          (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) allocHookStack ∗ Frame)
        (Post := fun sm => sm.sp = s0.sp - 496#64 ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = x.ret ∧ sm.readReg64 .x20 = x.pA ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length ∧
          sm.readReg64 .x22 = x.akPtr ∧ sm.readReg64 .x23 = ptr_c ∧
          sm.readReg32 .x25 = 1#32 ∧ sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0) ?_ ?_
      · wp_steps; wp_apply; wp_steps
        have hbuf := vecU8Buf_nonempty A ptr_c x.p.authKey hpos hlt hoom
        have hent :
            (ptr_c ↦ₛ x.p.authKey) ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
            A.pool ∗ stackAt sf.sp allocHookStack ∗
            A.live ptr_c x.p.authKey.length 1 ∗ Frame ⊢
            RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr_c x.p.authKey ∗
            (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) allocHookStack ∗ Frame := by
          rw [‹sf.sp = s.sp›, hsp]
          refine Entails.trans (Entails.of_eq (show _ =
            (A.live ptr_c x.p.authKey.length 1 ∗ (ptr_c ↦ₛ x.p.authKey)) ∗
            ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) allocHookStack ∗ Frame)
            by ac_rfl)) ?_
          exact sepConj_mono_left hbuf
        exact SepWP.weaken_pre hent (by wp_done)
      · intro sm hpcm hrunm _ hinvm ⟨hspm, hx29m, hx19m, hx20m, hx21m, hx22m, hx23m, hw25m, htrm, hvregsm⟩
        exact hnext sm ptr_c hpcm hrunm (fun hinv => hinvm (hinv_sf1 hinv))
          hspm hx29m hx19m hx20m hx21m hx22m hx23m hw25m htrm hvregsm

/-! ## 3. Callee Bridges and `spqr::init_inner` Call (`+284 -> +340`) on `Block 327` -/

theorem sepWPp_call_lsCallInv [LibsignalPlacement] {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {α : Type} {entry ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry spec) (hinv : LsCallInv lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LsCallInv lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hcall_wpp : SepWPp prog ret_pc s P
      (fun sm Pm => Pm = spec.post x s sm ∗ F ∧ sm.sp = s.sp ∧ CalleeSavedPreserved s sm) Qp := by
    refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr hpre hexit hpanic
      (fun sm hpcm hrunm hspm hcsm R' hm' _ =>
        ⟨sm, Steps.refl sm, Or.inl ⟨hpcm, hrunm, _, hm', rfl, hspm, hcsm⟩⟩) ?_
    intro sf R' _ hoom
    rw [hoom_eq] at hoom
    exact (not_satisfies_false_sepConj hoom).elim
  intro R hm hL
  rcases hcall_wpp R hm hL with
    ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, rfl, hspm, hcsm⟩ | hpan | hoom⟩
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hinv.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem initialState_initInner_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX A F))) :
    subroutine_ok (initialStatePlacedProg ext) (lsmpl.base 324)
      (withLsCallInv lsmpl (initInnerPlacedSpecX A F)) := by
  apply subroutine_ok_withLsCallInv_of_withLsCodeLoaded
  exact subroutine_ok_mono
    (ls_subroutine_ok_cl_of_block (callerProg := initialStatePlacedProg ext) hinit)
    (fun _ _ _ h => h)
    (fun _ _ _ _ h => by
      dsimp only [withLsCl, withLsCodeLoaded] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.2)

theorem initialState_encodeToVec_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (henc : PqRatchetStateEncodeToVecPlacedOkExt A ext) :
    subroutine_ok (initialStatePlacedProg ext) (lsmpl.base 426)
      (withLsCallInv lsmpl (pqRatchetStateEncodeToVecSpecX A)) := by
  have henc_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base (withLsCallInv lsmpl (pqRatchetStateEncodeToVecSpecX A)) := by
    refine subroutine_ok_mono henc (fun x s0 R hpre => ?_) (fun _ _ _ _ hq => hq)
    dsimp only [withLsCallInv] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hro, hcl⟩, hpre⟩ := hpre
    dsimp only [withLsRoLoaded, withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre⟩
  exact ls_subroutine_ok_callInv_of_block (callerProg := initialStatePlacedProg ext) henc_call

theorem initialState_dropPqRatchetState_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A))) :
    subroutine_ok (initialStatePlacedProg ext) (lsmpl.base 270)
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A)) :=
  subroutine_ok_mono
    (ls_subroutine_ok_cl_of_block (callerProg := initialStatePlacedProg ext) hdrop)
    (fun _ _ _ h => h)
    (fun _ _ _ _ h => by
      dsimp only [withLsCl, withLsCodeLoaded] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.2)

theorem initial_state_pre_init_inner_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (ptr : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = initialStatePlacedEntry + 284#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.pA) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length)
    (hx22 : s.readReg64 .x22 = x.akPtr) (hx23 : s.readReg64 .x23 = ptr)
    (hw25 : s.readReg32 .x25 = 1#32) (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (lsmpl.base 324) s
      (paramsAt x.pA x.akPtr x.p ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ paramsAt x.pA x.akPtr x.p ∗ Rest) ∧
        s2.sp = s0.sp - 496#64 ∧
        s2.readReg64 .x30 = initialStatePlacedEntry + 344#64 ∧
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
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, paramsAt, Version.toI32,
    State.readReg32, Reg.x1, Reg.x2, Reg.x20, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
    BitVec.ofNat_eq_ofNat] at hpc hw25 ⊢
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

theorem call_initInner_placed_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX A F)))
    {Q : State → SepProp → Prop}
    (s0 s : State) (x : InitialStateGhost) (Frame R : SepProp)
    (hinv : LsCallInv lsmpl s.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hak_ne : x.akPtr ≠ 0#64) (hlt : 32 + x.p.authKey.length < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 324)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hlr : s.readReg64 .x30 = initialStatePlacedEntry + 344#64)
    (hx0 : s.readReg64 .x0 = (s0.sp - 456#64) + 0x80#64)
    (hw1 : s.readReg32 .x1 = Version.v1.toI32) (hw2 : s.readReg32 .x2 = x.p.direction.toI32)
    (hx3 : s.readReg64 .x3 = x.akPtr) (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 x.p.authKey.length)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = initialStatePlacedEntry + 344#64 →
      sf.status = .Running → LsCallInv lsmpl sf.mem → sf.sp = s0.sp - 496#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) sf
        ((initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey ∗
          (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      ((memRegion ((s0.sp - 456#64) + 0x80#64) optProtoInnerStateSize ∗
        (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
        A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack) ∗ Frame)
      Q (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hcall := initialState_initInner_placed_ok hinit
  let gx : InitInnerGhost := ⟨(s0.sp - 456#64) + 0x80#64, .v1, x.p.direction, x.akPtr, x.p.authKey⟩
  refine sepWPp_call_lsCallInv hcall (x := gx) (F := Frame) hinv
    hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr ?_
    (fun _ _ _ _ h => ProofLib.allowPanic_not_exited h) (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerStackX, gx]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨hinv, ⟨hx0, hw1, hw2, hx3, hx4, hak_ne, hlt⟩, hm⟩
  · change (sf.mem ⊨ ((withLsCallInv lsmpl (initInnerPlacedSpecX A F)).onPanic gx s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem
    dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerOnPanic] at hmem
    rw [← sepConj_assoc]
    have hpan := ProofLib.allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by
        unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerStackX, gx]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hnext' := hnext sf hpc_sf hrun_sf hinv_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hnext'

/-! ## 4. `PqRatchetState` Stores (`+344 -> +380`) and `encode_to_vec` Call on `Block 327` -/

theorem initial_state_pre_encode_to_vec_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
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
    (hpc : s.pc = initialStatePlacedEntry + 344#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (hw20 : s.readReg32 .x20 = x.p.minVersion.toI32)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.p.authKey.length) (hx23 : s.readReg64 .x23 = ptr)
    (hw24 : s.readReg32 .x24 = x.p.direction.toI32) (hw25 : s.readReg32 .x25 = 1#32)
    (hw26 : s.readReg32 .x26 = x.p.chainParams.intoPb.maxJump)
    (hw27 : s.readReg32 .x27 = x.p.chainParams.intoPb.maxOooKeys) (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (lsmpl.base 426) s
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
        s2.readReg64 .x30 = initialStatePlacedEntry + 384#64 ∧
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
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, noneCap,
    State.readReg32, Reg.x20, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
    BitVec.ofNat_eq_ofNat] at hpc hw20 hw24 hw25 hw26 hw27 ⊢
  cells_unfold; wp_pull_exists; wp_steps
  refine Drop.align_pre (by simp only [arm64_norm]; ac_rfl) ?_
  wp_done

theorem call_encodeToVec_placed_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (henc : PqRatchetStateEncodeToVecPlacedOkExt A ext)
    {Q : State → SepProp → Prop}
    (s0 s : State) (x : InitialStateGhost) (Frame R : SepProp)
    (hinv : LsCallInv lsmpl s.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen_pb : (PqRatchetState.encodeRaw (initialStatePB F x.p)).length < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 426)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hlr : s.readReg64 .x30 = initialStatePlacedEntry + 384#64)
    (hx0 : s.readReg64 .x0 = x.ret + 8#64) (hx1 : s.readReg64 .x1 = s0.sp - 456#64)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = initialStatePlacedEntry + 384#64 →
      sf.status = .Running → LsCallInv lsmpl sf.mem → sf.sp = s0.sp - 496#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) sf
        ((vecU8 A (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p)) ∗
          pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
          A.pool ∗ stackAt (s0.sp - 496#64) encodeToVecStackX) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      ((memRegion (x.ret + 8#64) 24 ∗
        pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
        A.pool ∗ stackAt (s0.sp - 496#64) encodeToVecStackX) ∗ Frame)
      Q (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hcall := initialState_encodeToVec_placed_ok henc
  let gx : PqRatchetStateEncodeToVecGhost := ⟨x.ret + 8#64, s0.sp - 456#64, initialStatePB F x.p⟩
  refine sepWPp_call_lsCallInv hcall (x := gx) (F := Frame) hinv
    hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr ?_
    (fun _ _ _ _ h => ProofLib.allowPanic_not_exited h) (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    dsimp only [withLsCallInv, pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf, gx]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨hinv, ⟨hx0, hx1, hlen_pb⟩, hm⟩
  · change (sf.mem ⊨ ((withLsCallInv lsmpl (pqRatchetStateEncodeToVecSpecX A)).onPanic gx s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem
    dsimp only [withLsCallInv, pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf] at hmem
    rw [← sepConj_assoc]
    have hpan := ProofLib.allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by
        unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [withLsCallInv, pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf, gx]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hnext' := hnext sf hpc_sf hrun_sf hinv_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hnext'

/-! ## 5. `Ok` Tag Store (`+384 -> +392`) and `drop_glue::<PqRatchetState>` Call on `Block 327` -/

theorem initial_state_pre_drop_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (x : InitialStateGhost) (r0 : BitVec 64) (Rest : SepProp)
    (hv : x.p.version = .v1) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = initialStatePlacedEntry + 384#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = x.ret)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (initialStatePlacedProg ext) (lsmpl.base 270) s
      ((x.ret ↦₆₄ r0) ∗
       vecU8 A (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p)) ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ initialStateResultAt A x.ret (initialStateValue F x.p) ∗ Rest) ∧
        s2.sp = s0.sp - 496#64 ∧
        s2.readReg64 .x30 = initialStatePlacedEntry + 396#64 ∧
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
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

theorem call_dropPqRatchetState_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A)))
    {Q : State → SepProp → Prop}
    (s0 s : State) (x : InitialStateGhost) (Frame R : SepProp)
    (hinv : LsCallInv lsmpl s.mem)
    (hproto_eq : protoPqRatchetStateAt A (s0.sp - 456#64) (initialStatePB F x.p) =
      pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 270)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hlr : s.readReg64 .x30 = initialStatePlacedEntry + 396#64)
    (hx0 : s.readReg64 .x0 = s0.sp - 456#64) (htrace : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = initialStatePlacedEntry + 396#64 →
      sf.status = .Running → sf.sp = s0.sp - 496#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) sf
        ((memRegion (s0.sp - 456#64) 352 ∗ optProtoInnerStateJumpTablePlacedAt ∗
          A.pool ∗ stackAt (s0.sp - 496#64) dropStack96) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      ((pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
        optProtoInnerStateJumpTablePlacedAt ∗
        A.pool ∗ stackAt (s0.sp - 496#64) dropStack96) ∗ Frame)
      Q (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  rw [← hproto_eq]
  have hcall := subroutine_ok_withLsCallInv_of_withLsCodeLoaded
    (initialState_dropPqRatchetState_placed_ok hdrop)
  let gx : DropProtoPqRatchetStateGhost := ⟨s0.sp - 456#64, initialStatePB F x.p⟩
  refine sepWPp_call_lsCallInv hcall (x := gx) (F := Frame) hinv
    hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [withLsCallInv, dropProtoPqRatchetStatePlacedSpec, gx] at h
      rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf _ => ?_)
  · intro R' hm
    dsimp only [withLsCallInv, dropProtoPqRatchetStatePlacedSpec, gx]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨hinv, hx0, hm⟩
  · dsimp only [withLsCallInv, dropProtoPqRatchetStatePlacedSpec, gx] at hmem
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1
  · dsimp only [withLsCallInv, dropProtoPqRatchetStatePlacedSpec, protoPqRatchetStateSize, gx]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hnext' := hnext sf hpc_sf hrun_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hnext'

/-! ## 6. Full V1 Path Composition (`+0 -> ret`) on `Block 327` -/

def InitialStateV1PlacedPost [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (s0 : State) (x : InitialStateGhost) : State → SepProp → Prop :=
  fun sf Pf =>
    (Pf ⊢
      statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
      paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp initialStateStack) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace

theorem sepWPp_of_initialState_v1_placed_wpp [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 : State) (x : InitialStateGhost) (P R : SepProp)
    (hwpp : SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s0 P
      (InitialStateV1PlacedPost A F s0 x) (InitInnerPanic s0 R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s0 P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initialStatePlacedSpec A F).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initialStatePlacedSpec A F).onPanic x s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hent, hspf, hcsf, htrf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR; dsimp only [initialStatePlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrf, ?_⟩
    have hm1 := Satisfies.mono (sepConj_mono_left hent) hmR
    have hm2 : sf.mem ⊨
        (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt) ∗
        ((paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
          initialStateResultAt A x.ret (initialStateValue F x.p) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp initialStateStack) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hm1
    exact Satisfies.of_sep_right hm2
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, ?_⟩)⟩
    intro hmR; dsimp only [initialStatePlacedSpec, initialStateOnPanic]
    simpa [sepConj_assoc] using hqp hmR
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem initial_state_v1_body_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym) framelessMemcpySpec)
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX A F)))
    (henc : PqRatchetStateEncodeToVecPlacedOkExt A ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A)))
    (s0 : State) (x : InitialStateGhost) (R : SepProp) (hinv0 : LsCallInv lsmpl s0.mem)
    (hpc : s0.pc = initialStatePlacedEntry)
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
      pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s0
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp initialStateStack)
      (InitialStateV1PlacedPost A F s0 x)
      (InitInnerPanic s0 R) := by
  have hlt63 : x.p.authKey.length < 2 ^ 63 := by omega
  have hlt32_63 : 32 + x.p.authKey.length < 2 ^ 63 := by omega
  refine SepWPp.weaken_pre (P' :=
      cells (s0.sp - 96#64) 12 ∗ paramsAt x.pA x.akPtr x.p ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [h61s_stackAt_initialState_split s0.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_prologue_v1_placed s0 x _ hsp0_align hpc hrun hx0 hx8 hv hlen) ?_
  intro s1 hpc1 hrun1 _ hinv1 ⟨hsp1, hx29_1, hx19_1, hx20_1, hx21_1, hx22_1, hw25_1, htr1, hvregs1⟩
  refine SepWPp.weaken_pre (P' :=
      (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) allocHookStack ∗
      (memRegion ((s0.sp - 496#64) - 17680#64) 13584 ∗ paramsAt x.pA x.akPtr x.p ∗
       h61s_initialStateSavedCells s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_allocHook (s0.sp - 496#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  refine initial_state_to_vec_placed h_panic hshim halloc hmemcpy s0 s1 x _ R hsp0_align hlt63
    hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx21_1 hx22_1 hw25_1 htr1 hvregs1 ?_
  intro s2 ptr hpc2 hrun2 hinv2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hw25_2 htr2 hvregs2
  refine SepWPp.weaken_pre (P' :=
      paramsAt x.pA x.akPtr x.p ∗
      (memRegion (s0.sp - 456#64) 352 ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
       h61s_initialStateSavedCells s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_allocHook (s0.sp - 496#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_init_inner_placed s0 s2 x ptr _ hsp0_align
      hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hw25_2 htr2 hvregs2) ?_
  intro s3 hpc3 hrun3 _ hinv3
    ⟨hsp3, hlr3, hx0_3, hw1_3, hw2_3, hx3_3, hx4_3, hx29_3, hx19_3, hw20_3, hx21_3, hx23_3,
     hw24_3, hw25_3, hw26_3, hw27_3, htr3, hvregs3⟩
  refine SepWPp.weaken_pre (P' :=
      (memRegion ((s0.sp - 456#64) + 0x80#64) optProtoInnerStateSize ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
       A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack) ∗
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
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ memRegion x.ret 32 ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [memRegion_pqState_split (s0.sp - 456#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  have hinv_s3 : LsCallInv lsmpl s3.mem := hinv3 (hinv2 (hinv1 hinv0))
  refine call_initInner_placed_x hinit s0 s3 x _ R hinv_s3 hsp0_align hak_ne hlt32_63
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
      (memRegion x.ret 32 ∗ A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt ∗
       optProtoInnerStateJumpTablePlacedAt))
    (Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_encode_to_vec_placed s0 s4 x ptr _ (hpbAt ptr) hsp0_align
      hpc4 hrun4 hsp4
      (hx29_4.1.trans hx29_3) (hx19_4.trans hx19_3)
      ((readReg32_of_eq hx20_4).trans hw20_3)
      (hx21_4.trans hx21_3) (hx23_4.trans hx23_3)
      ((readReg32_of_eq hx24_4).trans hw24_3)
      ((readReg32_of_eq hx25_4).trans hw25_3)
      ((readReg32_of_eq hx26_4).trans hw26_3)
      ((readReg32_of_eq hx27_4).trans hw27_3) htr4 (hx29_4.2.trans hvregs3)) ?_
  intro s5 hpc5 hrun5 _ hinv5 ⟨hsp5, hlr5, hx0_5, hx1_5, hx29_5, hx19_5, htr5, hvregs5⟩
  refine SepWPp.weaken_pre (P' :=
      ∃∗ r0 : BitVec 64,
        (memRegion (x.ret + 8#64) 24 ∗
         pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
         A.pool ∗ stackAt (s0.sp - 496#64) encodeToVecStackX) ∗
        ((x.ret ↦₆₄ r0) ∗
         memRegion ((s0.sp - 496#64) - 17680#64) (initInnerStack - encodeToVecStackX) ∗
         (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
         memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt ∗
         optProtoInnerStateJumpTablePlacedAt))
    (by
      rw [memRegion_ret_32_split x.ret, stackAt_initInner_split_encodeToVec (s0.sp - 496#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro r0
      exact Entails.sepExists_right r0 (Entails.of_eq (by ac_rfl))) ?_
  refine SepWPp.exists_elim fun r0 => ?_
  have hinv_s5 : LsCallInv lsmpl s5.mem := hinv5 hinv4
  refine call_encodeToVec_placed_x henc s0 s5 x _ R hinv_s5 hsp0_align hlen_pb
    hpc5 hrun5 hsp5 hlr5 hx0_5 hx1_5 htr5 ?_
  intro s6 hpc6 hrun6 hinv6 hsp6 hcs6 htr6
  obtain ⟨hx19_6, _, _, _, _, _, _, _, _, _, hx29_6⟩ := hcs6
  refine SepWPp.weaken_pre (P' :=
      (x.ret ↦₆₄ r0) ∗ vecU8 A (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p)) ∗
      (pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
       optProtoInnerStateJumpTablePlacedAt ∗ A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_encodeToVec (s0.sp - 496#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_drop_placed s0 s6 x r0 _ hv hsp0_align
      hpc6 hrun6 hsp6 (hx29_6.1.trans hx29_5) (hx19_6.trans hx19_5) htr6 (hx29_6.2.trans hvregs5)) ?_
  intro s7 hpc7 hrun7 _ hinv7 ⟨hsp7, hlr7, hx0_7, hx29_7, htr7, hvregs7⟩
  refine SepWPp.weaken_pre (P' :=
      (pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
       optProtoInnerStateJumpTablePlacedAt ∗ A.pool ∗ stackAt (s0.sp - 496#64) dropStack96) ∗
      (memRegion ((s0.sp - 496#64) - 17680#64) 13488 ∗
       initialStateResultAt A x.ret (initialStateValue F x.p) ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_dropStack96 (s0.sp - 496#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  have hinv_s7 : LsCallInv lsmpl s7.mem := hinv7 hinv6
  refine call_dropPqRatchetState_placed hdrop s0 s7 x _ R hinv_s7 hproto_eq hsp0_align
    hpc7 hrun7 hsp7 hlr7 hx0_7 htr7 ?_
  intro s8 hpc8 hrun8 hsp8 hcs8 htr8
  refine SepWPp.weaken_pre (P' :=
      stackAt (s0.sp - 496#64) initInnerStack ∗ memRegion (s0.sp - 496#64) 40 ∗
      memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
      h61s_initialStateSavedCells s0 ∗
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       initialStateResultAt A x.ret (initialStateValue F x.p) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool))
    (by rw [stackAt_initInner_split_dropStack96 (s0.sp - 496#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_epilogue_placed s0 s8 _ hsp0_align hpc8 hrun8 hsp8 htr8
      (hcs8.2.2.2.2.2.2.2.2.2.2.2.trans hvregs7)) ?_
  intro sf hpcf hrunf _ _ ⟨hspf, hcsf, htrf⟩
  exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), hspf, hcsf, htrf⟩

end CryptoVerification.SpqrV1.Top.InitialState

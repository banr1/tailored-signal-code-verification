/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.AllocBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Proof for `<PolyEncoder as Encoder>::encode_bytes`

Proves `encode_bytes_placed_ok_ext` and `encode_bytes_placed_ok_x` on Block `417` under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_417 blkPl_417)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalSpqrV1
  (CHUNK_SIZE NUM_POLYS Point)
open CryptoVerification.SpqrV1.Alloc
  (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderSize resultPolyEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncodeBytes
  (bv_add_add_lit bytesAt distributeMsgChunksTotal distributeMsgChunksTotal_value_length_le
   distributeMsgChunks_eq_ok encodeBytesResult encodeBytesStack memRegion_464_split savedCells
   sepWPp_cells_succ sepWPp_cells_zero stackAt_96_split_464)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv EncodeBytesPlacedOkExt EncodeBytesPlacedOkX
   encodeBytesAllocEvents encodeBytesSpec encodeBytesSpecOfEnv
   encodeBytesSpecX_of_encodeBytesSpec
   encode_bytes_err_odd_placed encode_bytes_err_too_long_placed)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.AllocBudget
  (encodeBytesAllocChunkEvents encode_bytes_alloc_0_3_placed encode_bytes_alloc_12_15_placed
   encode_bytes_alloc_4_7_placed encode_bytes_alloc_8_11_placed
   fitsEvents_encodeBytesAllocEvents_chunks)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.LoopBudget
  (encode_bytes_dist_entry_placed)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudgetAux
  (encode_bytes_dispatch_empty_placed encode_bytes_dispatch_nonempty_placed
   encode_bytes_dispatch_odd_placed encode_bytes_dispatch_too_long_placed
   encode_bytes_empty_body_placed encode_bytes_finish_ok_placed
   encode_bytes_prologue_placed encode_bytes_store_headers_nonempty_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved

private theorem sepWPp_seq_vm_clean {P : Program} {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (h1 : SepWP P mid s Pre (fun sm Pm => (Pm ⊢ P_mid) ∧ VmPreserved s sm ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWPp P target sm P_mid post onPanic) :
    SepWPp P target s Pre post onPanic :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hent, hvm, hQ⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hvm hQ))

private theorem pool_encodeBytesEnv_intro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st0 : M.σ) {msgLen : Nat} {evs0 : List AllocEvent}
    {s sf : State} (hvm : VmPreserved s sf) (hevs : evs0 = encodeBytesAllocEvents msgLen) :
    A.pool lim (M.stepEvents evs0 st0) s ⊢
      ∃∗ evs : List AllocEvent, ⌜EncodeBytesEnv msgLen evs⌝ ∗
        A.pool lim (M.stepEvents evs st0) sf := by
  refine Entails.trans ?_ (Entails.sepExists_intro (P := fun evs =>
    ⌜EncodeBytesEnv msgLen evs⌝ ∗ A.pool lim (M.stepEvents evs st0) sf) evs0)
  rw [A.pool_of_vmPreserved hvm]
  exact Entails.pure_right hevs (Entails.refl _)

section Placed
variable [LibsignalPlacement]

set_option maxHeartbeats 800000 in
theorem encode_bytes_nonempty_body_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyBudgetSpec)
    (msg : List (BitVec 8))
    (s0 s : State) (st0 : M.σ) (fsp out msgA : BitVec 64) (hfsp : fsp = s0.sp - 560#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (msgRO : Bool)
    (heven : msg.length % 2 = 0) (hpos : 2 ≤ msg.length) (hle : msg.length ≤ 1048576)
    (hfits : FitsEvents M lim st0 (encodeBytesAllocEvents msg.length))
    (R : SepProp) (hpc : s.pc = (blkPl_417).base + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msg.length)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hout : out = s0.readReg64 .x8) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
        savedCells s0 ∗ stackAt fsp allocHookStack ∗ memRegion out polyEncoderSize ∗
        bytesAt msgRO msgA msg ∗ A.pool lim st0 s)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (⌜sf.trace = s0.trace⌝ ∗
              resultPolyEncoderAt A.repAlloc out
                (.ok { idx := 0#32, s := .points (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] })) }) ∗
              bytesAt msgRO msgA msg ∗
              (∃∗ evs : List AllocEvent, ⌜EncodeBytesEnv msg.length evs⌝ ∗
                A.pool lim (M.stepEvents evs st0) sf) ∗
              stackAt s0.sp encodeBytesStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R)) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]; exact ProofLib.spAligned_sub s0.sp 560#64 hsp0_align
  obtain ⟨hf0, hf1, hf2, hf3, hstep_all⟩ :=
    fitsEvents_encodeBytesAllocEvents_chunks hle heven (by omega) hfits
  let c := encodeBytesAllocChunkEvents msg.length
  let st1 := M.stepEvents c st0
  let st2 := M.stepEvents c st1
  let st3 := M.stepEvents c st2
  iterate 9 (apply sepWPp_cells_succ; intro)
  apply sepWPp_cells_zero
  rename_i v0 v1 v2 v3 v4 v5 v6 v7 v8
  conv => arg 4; simp only [bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (encode_bytes_alloc_0_3_placed hshim_sat halloc_sat s0 s st0 fsp hfsp_align msg.length hpos hle hf0 v5 v6 v7 v8
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      hpc hrun hsp hx21 htrace hvregs ?_)
  intro s1 p0 p1 p2 p3 hp0 hp1 hp2 hp3 hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 htr1 hvr1
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (encode_bytes_alloc_4_7_placed hshim_sat halloc_sat s0 s1 st1 fsp hfsp_align msg.length hpos hle hf1 v1 v2 v3 v4
      ((fsp ↦₆₄ v0) ∗ ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗ ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
       (A.live p0 msg.length 2 ∗ memRegion p0 msg.length) ∗ (A.live p1 msg.length 2 ∗ memRegion p1 msg.length) ∗
       (A.live p2 msg.length 2 ∗ memRegion p2 msg.length) ∗ (A.live p3 msg.length 2 ∗ memRegion p3 msg.length) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      hpc1 hrun1 hsp1 hx21_1 htr1 hvr1 ?_)
  intro s2 p4 p5 p6 p7 hp4 hp5 hp6 hp7 hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 htr2 hvr2
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (encode_bytes_alloc_8_11_placed hshim_sat halloc_sat s0 s2 st2 fsp hfsp_align msg.length hpos hle hf2
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗ ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
       ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗ ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
       (A.live p0 msg.length 2 ∗ memRegion p0 msg.length) ∗ (A.live p1 msg.length 2 ∗ memRegion p1 msg.length) ∗
       (A.live p2 msg.length 2 ∗ memRegion p2 msg.length) ∗ (A.live p3 msg.length 2 ∗ memRegion p3 msg.length) ∗
       (A.live p4 msg.length 2 ∗ memRegion p4 msg.length) ∗ (A.live p5 msg.length 2 ∗ memRegion p5 msg.length) ∗
       (A.live p6 msg.length 2 ∗ memRegion p6 msg.length) ∗ (A.live p7 msg.length 2 ∗ memRegion p7 msg.length) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      hpc2 hrun2 hsp2 hx21_2 htr2 hvr2 ?_)
  intro s3 p8 p9 p10 p11 hp8 hp9 hp10 hp11 hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx23_3 hx24_3 hx25_3 hx26_3 htr3 hvr3
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (encode_bytes_alloc_12_15_placed hshim_sat halloc_sat s0 s3 st3 fsp hfsp_align msg.length hpos hle hf3
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗ ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
       ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗ ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
       (A.live p0 msg.length 2 ∗ memRegion p0 msg.length) ∗ (A.live p1 msg.length 2 ∗ memRegion p1 msg.length) ∗
       (A.live p2 msg.length 2 ∗ memRegion p2 msg.length) ∗ (A.live p3 msg.length 2 ∗ memRegion p3 msg.length) ∗
       (A.live p4 msg.length 2 ∗ memRegion p4 msg.length) ∗ (A.live p5 msg.length 2 ∗ memRegion p5 msg.length) ∗
       (A.live p6 msg.length 2 ∗ memRegion p6 msg.length) ∗ (A.live p7 msg.length 2 ∗ memRegion p7 msg.length) ∗
       (A.live p8 msg.length 2 ∗ memRegion p8 msg.length) ∗ (A.live p9 msg.length 2 ∗ memRegion p9 msg.length) ∗
       (A.live p10 msg.length 2 ∗ memRegion p10 msg.length) ∗ (A.live p11 msg.length 2 ∗ memRegion p11 msg.length) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      hpc3 hrun3 hsp3 hx21_3 htr3 hvr3 ?_)
  intro s4 p12 p13 p14 p15 hp12 hp13 hp14 hp15 hpc4 hrun4 hsp4
    hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx22_4 hx0_4 htr4 hvr4
  rw [show M.stepEvents c st3 = M.stepEvents (encodeBytesAllocEvents msg.length) st0 from hstep_all]
  let cap := BitVec.ofNat 64 (msg.length / 2)
  let pins : List VecPin :=
    [⟨cap, p0⟩, ⟨cap, p1⟩, ⟨cap, p2⟩, ⟨cap, p3⟩, ⟨cap, p4⟩, ⟨cap, p5⟩, ⟨cap, p6⟩, ⟨cap, p7⟩,
     ⟨cap, p8⟩, ⟨cap, p9⟩, ⟨cap, p10⟩, ⟨cap, p11⟩, ⟨cap, p12⟩, ⟨cap, p13⟩, ⟨cap, p14⟩, ⟨cap, p15⟩]
  have hpins_len : pins.length = 16 := rfl
  have hpins_cap : ∀ pin ∈ pins, pin.cap = cap := by
    intro pin hpin; simp only [pins, List.mem_cons, List.not_mem_nil, or_false] at hpin
    rcases hpin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hhdr := encode_bytes_store_headers_nonempty_placed (A := A.repAlloc) (ext := ext) s0 s4 fsp hfsp_align
    msg.length heven hpos hle v0 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
    hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15
    (memRegion (fsp + 456#64) 8 ∗ savedCells s0 ∗ stackAt fsp allocHookStack ∗
      memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗
      A.pool lim (M.stepEvents (encodeBytesAllocEvents msg.length) st0) s4)
    hpc4 hrun4 hsp4 hx21_4
    (by rw [hx23_4, hx23_3]) (by rw [hx24_4, hx24_3]) (by rw [hx25_4, hx25_3]) (by rw [hx26_4, hx26_3])
    hx27_4 hx28_4 hx22_4 hx0_4 htr4 hvr4
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (sepWPp_seq_vm_clean hhdr ?_)
  intro s5 hpc5 hrun5 hvm45 ⟨hsp5, hx8_5, hx19_5, hx20_5, htr5, hvr5⟩
  have hx19_s5 : s5.readReg64 .x19 = s0.readReg64 .x8 := by
    rw [hx19_5, hx19_4, hx19_3, hx19_2, hx19_1, hx19, hout]
  have hx20_s5 : s5.readReg64 .x20 = msgA := by
    rw [hx20_5, hx20_4, hx20_3, hx20_2, hx20_1, hx20]
  have hinit_len : (List.replicate 16 ({ value := [] } : Point)).length = 16 := by simp
  have hinit_bound : ∀ pt ∈ (List.replicate 16 ({ value := [] } : Point)), pt.value.length ≤ 0 := by
    intro pt hpt; rw [List.mem_replicate] at hpt; rcases hpt with ⟨_, rfl⟩; simp
  have hloop := encode_bytes_dist_entry_placed (A := A.repAlloc) (ext := ext) msg s0 s5 fsp msgA hfsp_align msgRO
    heven (by omega) (by omega) pins (List.replicate 16 { value := [] })
    hpins_len hinit_len hpins_cap hinit_bound
    (cells fsp 9 ∗ memRegion (fsp + 456#64) 8 ∗ savedCells s0 ∗ stackAt fsp allocHookStack ∗
      memRegion out polyEncoderSize ∗
      A.pool lim (M.stepEvents (encodeBytesAllocEvents msg.length) st0) s4)
    hpc5 hrun5 hsp5 hx8_5 hx19_s5 hx20_s5 htr5 hvr5
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (sepWPp_seq_vm_clean hloop ?_)
  intro s6 hpc6 hrun6 hvm56 ⟨hsp6, hx19_6, htr6, hvr6⟩
  have hpts_len : (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] })).length = 16 :=
    (distributeMsgChunks_eq_ok msg 0 (List.replicate 16 { value := [] }) heven hinit_len).2
  have hpts_bound : ∀ pt ∈ distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] }),
      pt.value.length ≤ 0x0555555555555555 := by
    intro pt hpt
    have h1 := distributeMsgChunksTotal_value_length_le msg 0
      (List.replicate 16 { value := [] }) heven hinit_len hinit_bound pt hpt
    omega
  have hfin := encode_bytes_finish_ok_placed (A := A.repAlloc) hmemcpy_sat s0 s6 fsp out hfsp
    pins (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] }))
    hpins_len hpts_len hpts_bound
    (bytesAt msgRO msgA msg ∗ A.pool lim (M.stepEvents (encodeBytesAllocEvents msg.length) st0) s4)
    hsp0_align hpc6 hrun6 hsp6 (by rw [hx19_6, hout]) htr6 hvr6
  refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hfin)
    fun sf Pf hpcf hrunf ⟨hPf, hvm6f, hcs, hspf, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
  have hvm4f : VmPreserved s4 sf := hvm45.trans (hvm56.trans hvm6f)
  have hpool := pool_encodeBytesEnv_intro A lim st0 hvm4f (msgLen := msg.length) rfl
  refine Entails.trans hPf (Entails.pure_right htrf ?_)
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right hpool))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

theorem encode_bytes_placed_ok_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyBudgetSpec) :
    EncodeBytesPlacedOkExt A lim ext := by
  unfold EncodeBytesPlacedOkExt
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, msgRO, msgA, msg⟩, st0⟩ R s0 hpc hrun hpre hsp0
  simp only [encodeBytesSpec, encodeBytesSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hlen_lt, hFit⟩, hmem⟩
  refine ⟨stackAt s0.sp encodeBytesStack ∗
      (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool lim st0 s0),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  dsimp only [encodeBytesSpec, encodeBytesSpecOfEnv]
  have hpro := encode_bytes_prologue_placed (ext := ext) s0
    (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool lim st0 s0)
    hsp0 hpc hrun
  refine sepWPp_seq_vm_clean hpro ?_
  intro s1 hpc1 hrun1 hvm01 ⟨hsp1, hx0_1, hx19_1, hx21_1, htr1, hvr1⟩
  have hx19_s1 : s1.readReg64 .x19 = out := by rw [hx19_1, hx8]
  have hx0_s1 : s1.readReg64 .x0 = msgA := by rw [hx0_1, hx0]
  have hx21_s1 : s1.readReg64 .x21 = BitVec.ofNat 64 msg.length := by rw [hx21_1, hx1]
  by_cases hodd : (msg.length % 2 != 0) = true
  · have hres : encodeBytesResult msg = .error (.polynomialError .messageLengthEven) := by
      simp [encodeBytesResult, hodd]
    have hevs_nil : ([] : List AllocEvent) = encodeBytesAllocEvents msg.length := by
      have hne : msg.length % 2 ≠ 0 := bne_iff_ne.mp hodd
      simp [encodeBytesAllocEvents, hne]
    rw [hres]
    have hdisp := encode_bytes_dispatch_odd_placed (ext := ext) s1 msg.length hodd
      (savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗
        (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool lim st0 s0))
      hpc1 hrun1 hx21_s1
    refine sepWPp_seq_vm_clean hdisp ?_
    intro s2 hpc2 hrun2 hvm12 ⟨hsp2, hx19_2, htr2, hvr2⟩
    have herr := encode_bytes_err_odd_placed (A := A.repAlloc) (ext := ext) s0 s2 out
      (bytesAt msgRO msgA msg ∗ A.pool lim st0 s0)
      hsp0 hpc2 hrun2 (by rw [hsp2, hsp1]) (by rw [hx19_2, hx19_s1]) (by rw [htr2, htr1]) (by rw [hvr2, hvr1])
    refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) herr)
      fun sf Pf hpcf hrunf ⟨hPf, hvm2f, hcs, hspf, htrf⟩ => ?_)
    refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
    have hpool := pool_encodeBytesEnv_intro A lim st0 (hvm01.trans (hvm12.trans hvm2f)) hevs_nil
    refine Entails.trans hPf (Entails.pure_right htrf ?_)
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right hpool))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · have heven : msg.length % 2 = 0 := by
      simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hodd; exact hodd
    have hodd_false : (msg.length % 2 != 0) = false := bne_eq_false_iff_eq.mpr heven
    by_cases hlong : msg.length > 1048576
    · have hres : encodeBytesResult msg = .error (.polynomialError .messageLengthTooLong) := by
        simp [encodeBytesResult, hodd_false, NUM_POLYS, CHUNK_SIZE]; omega
      have hevs_nil : ([] : List AllocEvent) = encodeBytesAllocEvents msg.length := by
        have hnotle : ¬ msg.length ≤ 1048576 := by omega
        simp [encodeBytesAllocEvents, hnotle]
      rw [hres]
      have hdisp := encode_bytes_dispatch_too_long_placed (ext := ext) s1 msg.length heven hlong hlen_lt
        (savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗
          (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool lim st0 s0))
        hpc1 hrun1 hx21_s1
      refine sepWPp_seq_vm_clean hdisp ?_
      intro s2 hpc2 hrun2 hvm12 ⟨hsp2, hx19_2, htr2, hvr2⟩
      have herr := encode_bytes_err_too_long_placed (A := A.repAlloc) (ext := ext) s0 s2 out
        (bytesAt msgRO msgA msg ∗ A.pool lim st0 s0)
        hsp0 hpc2 hrun2 (by rw [hsp2, hsp1]) (by rw [hx19_2, hx19_s1]) (by rw [htr2, htr1]) (by rw [hvr2, hvr1])
      refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) herr)
        fun sf Pf hpcf hrunf ⟨hPf, hvm2f, hcs, hspf, htrf⟩ => ?_)
      refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
      have hpool := pool_encodeBytesEnv_intro A lim st0 (hvm01.trans (hvm12.trans hvm2f)) hevs_nil
      refine Entails.trans hPf (Entails.pure_right htrf ?_)
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right hpool))) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    · have hle : msg.length ≤ 1048576 := by omega
      have hres : encodeBytesResult msg =
          .ok { idx := 0#32, s := .points (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] })) } := by
        simp [encodeBytesResult, hodd_false, NUM_POLYS, CHUNK_SIZE, hle]
      rw [hres]
      let fsp := s0.sp - 560#64
      have hfsp : fsp = s0.sp - 560#64 := rfl
      have hstk : stackAt (s0.sp - 96#64) (allocHookStack + 464) =
          stackAt fsp allocHookStack ∗ cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 := by
        rw [stackAt_96_split_464 s0.sp, ← hfsp, memRegion_464_split fsp]
      rw [hstk]
      by_cases hemp : msg.length = 0
      · have hmsg_nil : msg = [] := List.eq_nil_of_length_eq_zero hemp
        subst hmsg_nil
        simp only [distributeMsgChunksTotal]
        have hevs_nil : ([] : List AllocEvent) = encodeBytesAllocEvents ([] : List (BitVec 8)).length := by
          simp [encodeBytesAllocEvents]
        have hx21_zero : s1.readReg64 .x21 = 0#64 := by simpa using hx21_s1
        have hdisp := encode_bytes_dispatch_empty_placed (ext := ext) s1
          (savedCells s0 ∗
            (stackAt fsp allocHookStack ∗ cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8) ∗
            (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA [] ∗ A.pool lim st0 s0))
          hpc1 hrun1 hx21_zero
        refine sepWPp_seq_vm_clean hdisp ?_
        intro s2 hpc2 hrun2 hvm12 ⟨hsp2, hx19_2, hx21_2, htr2, hvr2⟩
        have hbody := encode_bytes_empty_body_placed (A := A.repAlloc) hmemcpy_sat s0 s2 fsp out hfsp hsp0
          (bytesAt msgRO msgA [] ∗ A.pool lim st0 s0)
          hpc2 hrun2 (by rw [hsp2, hsp1]) (by rw [hx19_2, hx19_s1]) hx21_2 (by rw [htr2, htr1]) (by rw [hvr2, hvr1])
        refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hbody)
          fun sf Pf hpcf hrunf ⟨hPf, hvm2f, hcs, hspf, htrf⟩ => ?_)
        refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
        have hpool := pool_encodeBytesEnv_intro A lim st0 (hvm01.trans (hvm12.trans hvm2f)) hevs_nil
        refine Entails.trans hPf (Entails.pure_right htrf ?_)
        refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right hpool))) ?_
        exact Entails.of_eq (by sep_ac_rfl)
      · have hpos : 2 ≤ msg.length := by omega
        have hdisp := encode_bytes_dispatch_nonempty_placed (ext := ext) s1 msg.length heven hpos hle
          (savedCells s0 ∗
            (stackAt fsp allocHookStack ∗ cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8) ∗
            (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool lim st0 s0))
          hpc1 hrun1 hx21_s1
        refine sepWPp_seq_vm_clean hdisp ?_
        intro s2 hpc2 hrun2 hvm12 ⟨hsp2, hx19_2, hx20_2, hx21_2, htr2, hvr2⟩
        rw [← A.pool_of_vmPreserved (hvm01.trans hvm12)]
        have hfits_ev : FitsEvents M lim st0 (encodeBytesAllocEvents msg.length) := hFit _ rfl
        have hbody := encode_bytes_nonempty_body_placed hshim_sat halloc_sat hmemcpy_sat
          msg s0 s2 st0 fsp out msgA hfsp hsp0 msgRO
          heven hpos hle hfits_ev R hpc2 hrun2 (by rw [hsp2, hsp1])
          (by rw [hx19_2, hx19_s1]) (by rw [hx20_2, hx0_s1]) hx21_2
          (by rw [htr2, htr1]) (by rw [hvr2, hvr1]) hx8.symm
        exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hbody

theorem encode_bytes_placed_ok_x {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyBudgetSpec) :
    EncodeBytesPlacedOkX A lim ext := by
  unfold EncodeBytesPlacedOkX
  exact encodeBytesSpecX_of_encodeBytesSpec
    (encode_bytes_placed_ok_ext hshim_sat halloc_sat hmemcpy_sat)

end Placed

end LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget

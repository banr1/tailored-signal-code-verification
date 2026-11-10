/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.FindIndexCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.Core
import LibsignalBinary.Proofs.ConsumeMessageKey.PanicPathsProofs.Fetch
import ProofLib.CoreLemmas
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Panic Paths of `RatchetState::consume_message_key`

Symbolic execution of the `consume_message_key` panic branches (Block 24):
- `loopNoChainPanic_ok`: store-loop iteration at `cmkLoopPC` (`+0x334`) when `find_receiver_chain_index`
  returns `None`, panicking via `expect_failed` (`+0x974`) or allocator `handle_error` (`+0x9b4`).
- `epiloguePanic_ok`: epilogue at `cmkEpiloguePC` (`+0x4dc`) when `counter = u32::MAX`
  (`panic_const_add_overflow` at `+0x9c0`) or `find_receiver_chain_index` returns `None`
  (`expect_failed` at `+0x99c`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- Store-loop missing-chain panic contract (`LoopNoChainPanicSpec`). -/
theorem loopNoChainPanic_ok (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) :
    LoopNoChainPanicSpec F A alloc img := by
  exact PanicPaths.loopNoChainPanic_ok' F A alloc img

/-- Epilogue overflow and missing-chain panic contract (`EpiloguePanicSpec`). -/
theorem epiloguePanic_ok (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) :
    EpiloguePanicSpec F A alloc img := by
  exact PanicPaths.epiloguePanic_ok' F A alloc img

/-- Placed store-loop missing-chain panic contract. -/
theorem loopNoChainPanic_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    LoopNoChainPanicPlacedSpec F A H := by
  exact PanicPaths.loopNoChainPanic_placed_ok' F A H

/-- Placed epilogue panic contract. -/
theorem epiloguePanic_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    EpiloguePanicPlacedSpec F A H := by
  exact PanicPaths.epiloguePanic_placed_ok' F A H

namespace PanicPaths

open CryptoVerification.SessionModel ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWPp_seq_lscro_pp {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem) (hro : LibsignalRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → LibsignalRoLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen
    (Φ := fun m => LibsignalCodeLoaded pl m ∧ LibsignalRoLoaded pl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen hr hkf⟩)
    ⟨hcl, hro⟩
    (SepWP.mono h fun _ _ _ _ hnext ⟨hc, hr⟩ => hnext hc hr)

private theorem call_hmac_placed_ro [LibsignalPlacement] {prog : Program}
    {F : ShaState → List (BitVec 8) → ShaState}
    {ret entry : BitVec 64} (ret_pc out ka : BitVec 64) (key : List (BitVec 8))
    (ia : BitVec 64) (inp : List (BitVec 8)) (sp0 : BitVec 64)
    {s : State} {P Fr : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        { hmacSpec F with pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp0) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hro : LibsignalRoLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = ka)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hx3 : s.readReg64 .x3 = ia)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hklen : key.length = 32) (hilen : inp.length = 1)
    (hframe : SepFrame (memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt sp0 4096) P Fr)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp0 → sf.spAligned = true → sf.trace = s.trace →
      LibsignalCodeLoaded lsmpl sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf
        ((out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt sp0 4096 ∗ Fr) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have h_stk := stackAt_split_bottom sp0 2048 2048 (by decide)
  change stackAt sp0 4096 = memRegion (sp0 - 4096#64) 2048 ∗ stackAt sp0 2048 at h_stk
  refine SepWPp.seq_frozen (mid := ret_pc) (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl ?_
  refine SepWP.call_subroutine_frame hcall (x := (out, ka, key, ia, inp))
    (F := memRegion (sp0 - 4096#64) 2048 ∗ Fr) hpc hrun hsp_align hlr
    (fun R hm => ?_)
    (fun _ _ _ hpost => by simp only [hmacSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun _ _ _ _ hpost => by simp only [hmacSpec] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm hpcm hrunm hspm hcsm => SepWP.done hpcm hrunm fun hcl_sm R hpost => ?_)
    (fun _ _ _ hpost => by simp only [hmacSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim)
  · refine introduce_withLsCodeLoaded hcl ?_
    dsimp only
    rw [sepConj_assoc, sepConj_left_comm ((hmacSpec F).pre (out, ka, key, ia, inp) s), satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    simp only [hmacSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by simp [hx2, hklen], hx3, by simp [hx4, hilen], hklen, hilen⟩, ?_⟩
    have hm' := hm
    rw [hframe.eq, h_stk] at hm'
    exact Satisfies.of_eq hm'
  · have hsp_sm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_align
    rw [hsp] at hspm
    simp only [hmacSpec, hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    have hpost' : sm.mem ⊨
        ((out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt sp0 4096 ∗ Fr) ∗ R := by
      rw [h_stk]
      exact Satisfies.of_eq hpost
    exact hnext sm hpcm hrunm hspm hsp_sm htrm hcl_sm hcsm R hpost'

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1600000 in
theorem epiloguePanic_placed_ro_ok' [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    EpiloguePanicPlacedRoSpec F A H := by
  intro hexp hovf hfind hhmac x Gc stc ckc R s0 s hidx hcond hpan hstate hro
  obtain ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, _⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, _, hmem⟩ := hstate
  rw [cmkLoopHeap_placed_eq_at] at hmem
  obtain ⟨b0, u1, u2, u3, R_unused, hlen_chains, hxs_lt, hm⟩ := cmkLoopHeapAt_decompose_panicPaths hmem
  have hpan_ovf : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkPanicAddOverflowSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hovf
  have hpan_exp : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkExpectFailedSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hexp
  change s.pc = (blkPl_24).base + 1244#64 at hpc
  refine reaches_outcome_panic_of_sepWPp (ret := 0#64) hm ?_
  simp only [cmkPlacedSpec_onPanic_eq]
  unfold cmkPanicPathsUsedAt
  apply sepWPp_seq_lscro_pp hcl hro (mid := lsmpl.base 73)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
  intro hcl1 hro1
  rw [pointsTo8_eq_pointsToBytes (s0.sp - 320#64) 2#8]
  refine call_hmac_placed_ro ((blkPl_24).base + bv% (1276)) (s0.sp - 224#64) x.ckA (keyToBytes32 ckc.key)
    (s0.sp - 320#64) [2#8] (s0.sp - 480#64) hhmac
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp [hsp, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp_align)
    hcl1 hro1 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (keyToBytes32_length ckc.key) rfl (by wp_sep_access) ?_
  intro s1 hpc1 hrun1 hsp1 hsp1_align htr1 hcl2 hcs1
  have hx23_1 : s1.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23, arm64_norm] using hcs1.2.2.2.2.1
  have hx26_1 : s1.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : s1.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1
  have hx28_1 : s1.readReg64 .x28 = BitVec.zeroExtend 64 ckc.index := by
    simpa [CalleeSavedPreserved, hx28, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.2.1
  by_cases hc : x.counter = BitVec.allOnes 32
  · have hckc_max : ckc.index = 0xffffffff#32 := hidx.trans hc
    rw [hckc_max] at hx28_1
    apply sepWPp_seq_lscl hcl2 (mid := lsρ cmkPanicAddOverflowSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    intro _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun1, arm64_norm]) hpan_ovf hpan
      (by simp [htr1, htrace, arm64_norm])
  · have hnone : stc.findReceiverChainIndex x.their = none := hcond.resolve_left hc
    have hz2 : (x.counter + 1#32 == 0#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; apply hc; apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := x.counter.isLt
      rw [BitVec.toNat_add] at h1
      change (x.counter.toNat + 1) % 4294967296 = 0 at h1
      change x.counter.toNat = 4294967295
      omega
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (hmacWith_length F (keyToBytes32 ckc.key) [2#8])
    rw [hw32 (s0.sp - 224#64)]
    refine SepWPp.fold_cell64_320 (by wp_sep_access) fun u0 => ?_
    apply sepWPp_seq_lscl hcl2 (mid := lsmpl.base 26)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    intro hcl3
    refine SepWPp.call_findIndex_none_placed ((blkPl_24).base + bv% (1312)) Gc.chainsPtr x.theirA (s0.sp - 480#64)
      Gc stc x.their hfind
      (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
      (by simp [hsp1, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp1_align)
      hcl3 (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      hlen_chains hxs_lt hnone (by wp_sep_access) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hcl4 _ hx0_2
    apply sepWPp_seq_lscl hcl4 (mid := lsρ cmkExpectFailedSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    intro _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) hpan_exp hpan
      (by simp [htr2, htr1, htrace, arm64_norm])

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1600000 in
theorem loopNoChainPanic_placed_ro_ok' [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    LoopNoChainPanicPlacedRoSpec F A H := by
  intro hA hfind hhmac x R s0 s _ hnone hpan hstate hro
  obtain ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, _⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, hloop_x19, hmem⟩ := hstate
  have hx19 : s.readReg64 .x19 = 1#64 := hloop_x19 rfl
  rw [cmkLoopHeap_placed_eq_at] at hmem
  obtain ⟨b0, u1, u2, u3, R_unused, hlen_chains, hxs_lt, hm⟩ := cmkLoopHeapAt_decompose_panicPaths hmem
  have halloc' : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustAllocSym) (rustAllocSpec A) :=
    cmk_hook_ok_of_mem hA.1
  have hshim' : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hA.2.2.1
  have hpan_oom : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkHandleErrorSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hA.2.2.2.1
  have hpan_exp : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkExpectFailedSym) =
      some Rust.panicked := (cmk_externAt?_of_mem).trans hA.2.2.2.2.1
  change s.pc = (blkPl_24).base + 820#64 at hpc
  refine reaches_outcome_panic_of_sepWPp (ret := 0#64) hm ?_
  simp only [cmkPlacedSpec_onPanic_eq]
  unfold cmkPanicPathsUsedAt
  apply sepWPp_seq_lscro_pp hcl hro (mid := lsmpl.base 73)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
  intro hcl1 hro1
  rw [pointsTo8_eq_pointsToBytes (s0.sp - 320#64) 1#8]
  refine call_hmac_placed_ro ((blkPl_24).base + bv% (848)) (s0.sp - 224#64) x.ckA (keyToBytes32 x.ck.key)
    (s0.sp - 320#64) [1#8] (s0.sp - 480#64) hhmac
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp [hsp, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp_align)
    hcl1 hro1 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (keyToBytes32_length x.ck.key) rfl (by wp_sep_access) ?_
  intro s1 hpc1 hrun1 hsp1 hsp1_align htr1 hcl2 hcs1
  have hx23_1 : s1.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23, arm64_norm] using hcs1.2.2.2.2.1
  have hx26_1 : s1.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hx27_1 : s1.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1
  apply sepWPp_seq_lscl hcl2 (mid := lsρ cmkRustNoAllocShimSym)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
  intro hcl3
  refine SepWPp.call_shim_placed ((blkPl_24).base + bv% (852)) (s0.sp - 480#64) hshim'
    (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    (by simp [hsp1, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp1_align)
    hcl3 (by simp [arm64_norm]) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hcl4 hcs2
  have hx23_2 : s2.readReg64 .x23 = x.self := by
    simpa [CalleeSavedPreserved, hx23_1, arm64_norm] using hcs2.2.2.2.2.1
  have hx26_2 : s2.readReg64 .x26 = x.theirA := by
    simpa [CalleeSavedPreserved, hx26_1, arm64_norm] using hcs2.2.2.2.2.2.2.2.1
  have hx27_2 : s2.readReg64 .x27 = s0.sp - 224#64 := by
    simpa [CalleeSavedPreserved, hx27_1, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1
  apply sepWPp_seq_lscl hcl4 (mid := lsρ cmkRustAllocSym)
  wp_steps
  apply SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
  intro hcl5
  refine SepWPp.call_alloc_32_placed ((blkPl_24).base + bv% (864)) (s0.sp - 480#64) halloc'
    (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    (by simp [hsp2, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp2_align)
    hcl5 (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (by wp_sep_access) ?_ ?_
  · intro s3 hpc3 hrun3 hsp3 hsp3_align htr3 hcl6 _ hx0_3
    apply sepWPp_seq_lscl hcl6 (mid := lsρ cmkHandleErrorSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
    intro _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun3, arm64_norm]) hpan_oom hpan
      (by simp [htr3, htr2, htr1, htrace, arm64_norm])
  · intro s3 a0 a1 a2 a3 hpc3 hrun3 hsp3 hsp3_align htr3 hcl6 hcs3 hx0_3
    have hx23_3 : s3.readReg64 .x23 = x.self := by
      simpa [CalleeSavedPreserved, hx23_2, arm64_norm] using hcs3.2.2.2.2.1
    have hx26_3 : s3.readReg64 .x26 = x.theirA := by
      simpa [CalleeSavedPreserved, hx26_2, arm64_norm] using hcs3.2.2.2.2.2.2.2.1
    have hx27_3 : s3.readReg64 .x27 = s0.sp - 224#64 := by
      simpa [CalleeSavedPreserved, hx27_2, arm64_norm] using hcs3.2.2.2.2.2.2.2.2.1
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (hmacWith_length F (keyToBytes32 x.ck.key) [1#8])
    rw [hw32 (s0.sp - 224#64)]
    apply sepWPp_seq_lscl hcl6 (mid := lsmpl.base 26)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
    intro hcl7
    refine SepWPp.call_findIndex_none_placed ((blkPl_24).base + bv% (900)) x.G.chainsPtr x.theirA (s0.sp - 480#64)
      x.G x.st x.their hfind
      (by simp [arm64_norm]) (by simp [hrun3, arm64_norm])
      (by simp [hsp3, arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp3_align)
      hcl7 (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      hlen_chains hxs_lt hnone (by wp_sep_access) ?_
    intro s4 hpc4 hrun4 hsp4 hsp4_align htr4 hcl8 _ hx0_4
    apply sepWPp_seq_lscl hcl8 (mid := lsρ cmkExpectFailedSym)
    wp_steps
    apply SepWP.done (by simp [arm64_norm]) (by simp [hrun4, arm64_norm])
    intro _
    exact SepWPp.panic_cmk (by simp [arm64_norm]) (by simp [hrun4, arm64_norm]) hpan_exp hpan
      (by simp [htr4, htr3, htr2, htr1, htrace, arm64_norm])

end PanicPaths

/-- `.rodata`-backed placed store-loop missing-chain panic contract. -/
theorem loopNoChainPanic_placed_ro_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    LoopNoChainPanicPlacedRoSpec F A H :=
  PanicPaths.loopNoChainPanic_placed_ro_ok' F A H

/-- `.rodata`-backed placed epilogue panic contract. -/
theorem epiloguePanic_placed_ro_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    EpiloguePanicPlacedRoSpec F A H :=
  PanicPaths.epiloguePanic_placed_ro_ok' F A H

end CryptoVerification.LibsignalSession


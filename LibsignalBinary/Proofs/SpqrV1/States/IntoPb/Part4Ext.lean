/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 4 (`AllocContracts4K` `memcpy` Relocation)

Lifts `sub_ok_memcpy_raw` and `call_memcpy_keep_relocate` from stackless
`sessionMemcpyRegionSpec` to 4-KiB stack-framed `SpqrV1.Alloc.AllocContracts4K`
(`withStack sessionMemcpyRegionSpec stk` for `allocHookStack ≤ stk ≤ 2 ^ 64`).
-/

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4Ext

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (tripleRatchetProgAtExt withStack sessionMemcpyRegionSpec)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (statesIntoPbName statesIntoPb_fnOff libsignalSessionCode_fnOff_memcpy fnAddr_fwd_eq
   Relocatable relocatedHeap memcpy_keep_relocate_split memcpy_keep_relocate_recombine
   TraceCalleeSaved StatesIntoPbPanic)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem sub_ok_memcpy_4k_raw {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (stk : Nat := encoderIntoPbStack)
    (hlo : allocHookStack ≤ stk := by decide)
    (hhi : stk ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
      (withStack sessionMemcpyRegionSpec stk) := by
  rw [fnAddr_fwd_eq
      (d := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
      (b := b) (X := Rust.withPanics ext)
      statesIntoPb_fnOff libsignalSessionCode_fnOff_memcpy (by decide)]
  exact hA.session_memcpy_region stk hlo hhi

/-- Call `memcpy` inside `SepWPp` under `withStack sessionMemcpyRegionSpec stk`,
keeping `F src` (`k` bytes) at `src` and relocating `G (src + off)` (`m` bytes) to `dst + off`. -/
theorem call_memcpy_keep_relocate_4k {b memcpy_pc : BitVec 64}
    {ext : String → Option (State → State)} {stk : Nat}
    (hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      memcpy_pc
      (withStack sessionMemcpyRegionSpec stk))
    {k m n : Nat} {off : BitVec 64}
    {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 k)
    (hkm : k + m = n)
    (hF : Relocatable k F)
    (hG : Relocatable m G)
    (dst src : BitVec 64)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = memcpy_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (F src ∗ G (src + off))) ∗
      (stackAt (s0.sp - 1520#64) stk ∗ Frame))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m)) ∗
          (stackAt (s0.sp - 1520#64) stk ∗ Frame))
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      Q (StatesIntoPbPanic s0 R) := by
  have hpre_split :
      P ⊢ ∃∗ bs1 : List (BitVec 8), ∃∗ bs2 : List (BitVec 8),
        ⌜bs1.length = k ∧ bs2.length = m ∧ (bs1 ++ bs2).length = n⌝ ∗
        (memRegion dst n ∗ (src ↦ₛ (bs1 ++ bs2)) ∗ stackAt s.sp stk) ∗
        (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame) := by
    rw [hsplit, ← hsp]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right
      (memcpy_keep_relocate_split hoff hkm hF hG dst src))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs1
    apply Entails.sepExists_elim; intro bs2
    rw [sepConj_left_comm (memRegion dst n), sepConj_assoc (⌜_⌝)]
    apply Entails.pure_left; intro hpure
    refine Entails.sepExists_right bs1 (Entails.sepExists_right bs2 ?_)
    refine Entails.pure_right hpure ?_
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine SepWPp.exists_elim fun bs1 => SepWPp.exists_elim fun bs2 => ?_
  refine SepWPp.pure_left fun ⟨hlen1, hlen2, hlen12⟩ => ?_
  refine SepWPp.call hmemcpy_raw (x := (dst, src, bs1 ++ bs2))
    (F := relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at h
      simp only [satisfies_pure_sepConj] at h
      exact h.1.elim)
    (fun _ _ h => by
      dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at h
      simp only [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.1.elim)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen12]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, hm⟩
  · dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr⟩ => ?_
    rw [hsp]
    have hrec := memcpy_keep_relocate_recombine (F := F) (G := G) hoff hlen1 hlen2 dst src
    have hpost_ent :
        ((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
          stackAt (s0.sp - 1520#64) stk ∗
          relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame) ⊢
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m)) ∗
          (stackAt (s0.sp - 1520#64) stk ∗ Frame)) := by
      have hreord :
          ((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
            stackAt (s0.sp - 1520#64) stk ∗
            relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame) =
          ((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
            relocatedHeap F bs1 ∗ relocatedHeap G bs2) ∗
          (stackAt (s0.sp - 1520#64) stk ∗ Frame) := by sep_ac_rfl
      rw [hreord]
      exact sepConj_mono_left hrec
    refine SepWPp.weaken_pre hpost_ent ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4Ext

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.States.IntoPb
export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4Ext
  (sub_ok_memcpy_4k_raw call_memcpy_keep_relocate_4k)
end CryptoVerification.SpqrV1.States.IntoPb
-- AUTO-BRIDGE END

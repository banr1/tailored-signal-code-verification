/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ErrK2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ConstsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.PrevBridgePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Version-Mismatch Epilogue over One Archived Session

Relocatable (`[LibsignalPlacement]`) proof of `overK2Seg_cli_placed`
(`(blkPl_518).base + 0x359c → retAddr`) on `lsProg_518` for a 1-element `previous_sessions`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches SepProp
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.CliHandshake.RespClosurePlaced

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Relocatable `[LibsignalPlacement]` K2 per-site epilogue
(`(blkPl_518).base + 0x359c → retAddr`) on `lsProg_518 ext` for a 1-element `previous_sessions`
(`prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc]`), preserving `calleeSavedVRegs`. -/
def OverK2SegCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State)),
    ∀ (s : State) (coroPtr outPtr errTag prevCap prevPtr
        w_370 w_378 w_380 w_388
        u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
        savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
        savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
      (w_22 w_390 u_ret08 u_ret2c : BitVec 32)
      (b_2c0 : BitVec 8) (enc : List (BitVec 8)),
      s.pc = (blkPl_518).base + 0x359c#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x22 = w_22.zeroExtend 64 →
      s.readReg64 .x25 = s.sp + 0x210#64 →
      s.readReg64 .x26 = outPtr →
      s.readReg64 .x28 = errTag →
      SepWP (lsProg_518 ext) retAddr s
        (prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
         A.pool ∗
         stackAt s.sp allocHookStack ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
         ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗
         ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
         ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗
         ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
         ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗
         ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
         ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
         ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
         ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
         ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
         ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
         ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
         ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
         ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
         ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
         ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
         ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
         ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
         ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
         ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
         ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
         ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
         ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
         ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
        (fun s1 P_f =>
          (P_f ⊢
            HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
            A.pool ∗ stackAt s.sp allocHookStack ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
            ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
            ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
            ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
            ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
            ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
            ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
            ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
            ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
            ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
            ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
            ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
            ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
            ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
            ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
            ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
            ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
            ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
            ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
            ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
            ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
            ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
            ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
            ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
          s1.sp = s.sp + 0xcd0#64 ∧
          s1.trace = s.trace ∧
          s1.readReg64 .x19 = savedX19 ∧
          s1.readReg64 .x20 = savedX20 ∧
          s1.readReg64 .x21 = savedX21 ∧
          s1.readReg64 .x22 = savedX22 ∧
          s1.readReg64 .x23 = savedX23 ∧
          s1.readReg64 .x24 = savedX24 ∧
          s1.readReg64 .x25 = savedX25 ∧
          s1.readReg64 .x26 = savedX26 ∧
          s1.readReg64 .x27 = savedX27 ∧
          s1.readReg64 .x28 = savedX28 ∧
          s1.readReg64 .x29 = savedX29 ∧
          s1.readReg64 .x30 = retAddr ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)

/-! ## Spatial helpers -/

private theorem entails_replace_sub_k2_pl {P A A' F Q : SepProp}
    (hA : A ⊢ A') (hP : P = A ∗ F) (hQ : Q = A' ∗ F) : P ⊢ Q := by
  rw [hP, hQ]; exact sepConj_mono_left hA

private theorem prevVecAt_one_drop_split_k2_pl (A : RustAlloc) (r cap q : BitVec 64)
    (enc : List (BitVec 8)) (hcap : cap ≠ 0#64) :
    prevVecAt A r cap q [enc] ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64,
        ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        ⌜c.toNat < 2 ^ 63⌝ ∗
        HdrP r cap q 1#64 ∗
        A.live q (cap.toNat * 24) 8 ∗
        (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
        (if c = 0#64 then emp else A.live p c.toNat 1 ∗ memRegion p c.toNat) ∗
        memRegion (q + 24#64) ((cap.toNat - 1) * 24) := by
  have h0 : prevVecAt A r cap q [enc] ⊢
      HdrP r cap q 1#64 ∗ ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
      A.live q (cap.toNat * 24) 8 ∗
      (∃∗ c : BitVec 64, ∃∗ p : BitVec 64, (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
        ⌜c.toNat < 2 ^ 63⌝ ∗ (if c = 0#64 then emp else A.live p c.toNat 1 ∗ memRegion p c.toNat)) ∗
      memRegion (q + 24#64) ((cap.toNat - 1) * 24) := by
    rw [prevVecAt_one_eq A r cap q enc hcap]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
    unfold vecU8
    refine Entails.sepExists_elim fun c => Entails.sepExists_right c ?_
    refine Entails.sepExists_elim fun p => Entails.sepExists_right p ?_
    refine Entails.trans (vecU8At_entails_dealloc A q c p enc) ?_
    unfold vecHeader
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right ?_)
    refine sepConj_mono (pointsTo64_entails_memRegion (q + 16#64) _) ?_
    exact Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.refl _)
  refine Entails.trans h0 ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun c => Entails.sepExists_right c ?_
  refine Entails.sepExists_elim fun p => Entails.sepExists_right p ?_
  exact Entails.of_eq (by ac_rfl)

private theorem prevVec1_outer_merge_k2_pl (q c p : BitVec 64) (cap : Nat)
    (h : 1 ≤ cap ∧ cap * 24 < 2 ^ 63) :
    (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗ memRegion (q + 24#64) ((cap - 1) * 24) ⊢
      memRegion q (cap * 24) := by
  have h24 : (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
      memRegion (q + 24#64) ((cap - 1) * 24) ⊢
      memRegion q 24 ∗ memRegion (q + 24#64) ((cap - 1) * 24) := by
    rw [ProofLib.memRegion_split' (b := q) (b' := q + 8#64) (N := 24) (n := 8) (k := 16)
          rfl rfl (by decide),
        ProofLib.memRegion_split' (b := q + 8#64) (b' := q + 16#64) (N := 16) (n := 8) (k := 8)
          rfl (by bv_omega) (by decide)]
    simp only [sepConj_assoc]
    exact sepConj_mono (pointsTo64_entails_memRegion q c)
      (sepConj_mono (pointsTo64_entails_memRegion (q + 8#64) p) (Entails.refl _))
  refine Entails.trans h24 ?_
  rw [ProofLib.memRegion_split' (b := q) (b' := q + 24#64) (N := cap * 24) (n := 24)
        (k := (cap - 1) * 24) (by omega) rfl (by omega)]
  exact Entails.refl _

private theorem prevVecAt_one_cap0_false_k2_pl (A : RustAlloc) (r q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A r 0#64 q [enc] ⊢ ⌜False⌝ := by
  rw [prevVecAt_eq]
  unfold RustHeap.vecBuf
  rw [sepConj_left_comm]
  refine Entails.pure_left fun ⟨hlen, _, _⟩ => ?_
  nomatch hlen

private theorem sepWP_exists_elim_k2_pl {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {P : α → SepProp} {post : State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) :
    SepWP prog pc s (∃∗ a, P a) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm
  exact h a R ha

private theorem sepWP_pure_elim_k2_pl {prog : Program} {pc : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog pc s P post) :
    SepWP prog pc s (⌜φ⌝ ∗ P) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

/-! ## Case split (`c = 0` vs `c ≠ 0`) and main theorem -/

set_option maxHeartbeats 1200000 in
private theorem p3_err_tail_b_prev1_c0_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr outPtr errTag prevCap prevPtr p
      w_370 w_378 w_380 w_388
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8)
    (hcap : prevCap ≠ 0#64)
    (hcapb : 1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x359c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (lsProg_518 ext) retAddr s
      (HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
       A.live prevPtr (prevCap.toNat * 24) 8 ∗
       (prevPtr ↦₆₄ 0#64) ∗
       ((prevPtr + 8#64) ↦₆₄ p) ∗
       memRegion (prevPtr + 16#64) 8 ∗
       memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24) ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗
       ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗
       ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗
       ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
       ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
       ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
       ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
       ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
       ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
       ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
          ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
          ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
          ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
          ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
          ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
          ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
          ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧
        s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧
        s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧
        s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧
        s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧
        s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
  have hlay_q : LayoutOk (prevCap.toNat * 24) 8 := ⟨by omega, ⟨3, rfl⟩, by omega⟩
  obtain ⟨hlay_q1, hlay_q2, hlay_q3⟩ := hlay_q
  have hmul24' : (prevCap + (prevCap <<< 1)) <<< 3 = prevCap * 24#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    omega
  have hmul24 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = prevCap * 24#64 := hmul24'
  have hx1_de2 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24]; bv_omega
  have hx1_de2' : (prevCap + (prevCap <<< 1)) <<< 3 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24']; bv_omega
  have hx1_de2_nat : ((prevCap + (prevCap <<< 1#64)) <<< 3#64).toNat = prevCap.toNat * 24 := by
    rw [hmul24]; bv_omega
  have hx1_de2_nat' : ((prevCap + (prevCap <<< 1)) <<< 3).toNat = prevCap.toNat * 24 := by
    rw [hmul24']; bv_omega
  rw [hdrP_coro_eq]
  simp only [sepConj_assoc]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  wp_steps
  refine SepWP.weaken_pre
    (entails_replace_sub_k2_pl
      (prevVec1_outer_merge_k2_pl prevPtr 0#64 p prevCap.toNat hcapb)
      (by sep_focus) rfl) ?_
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  simp_all only [BitVec.add_zero, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
private theorem p3_err_tail_b_prev1_cnz_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr outPtr errTag prevCap prevPtr c p
      w_370 w_378 w_380 w_388
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8)
    (hcap : prevCap ≠ 0#64)
    (hcapb : 1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63)
    (hc0 : c ≠ 0#64)
    (hc : c.toNat < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x359c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (lsProg_518 ext) retAddr s
      (HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
       A.live prevPtr (prevCap.toNat * 24) 8 ∗
       (prevPtr ↦₆₄ c) ∗
       ((prevPtr + 8#64) ↦₆₄ p) ∗
       memRegion (prevPtr + 16#64) 8 ∗
       A.live p c.toNat 1 ∗
       memRegion p c.toNat ∗
       memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24) ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗
       ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗
       ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗
       ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
       ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
       ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
       ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
       ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
       ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
       ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
          ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
          ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
          ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
          ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
          ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
          ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
          ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧
        s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧
        s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧
        s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧
        s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧
        s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
  have hc_beq : (c == 0#64) = false := beq_eq_false_iff_ne.mpr hc0
  have hc_pos : 0 < c.toNat := by
    rcases Nat.eq_zero_or_pos c.toNat with h0 | hpos
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hc0
    · exact hpos
  have hlay_c : LayoutOk c.toNat 1 := ⟨hc_pos, ⟨0, rfl⟩, by omega⟩
  obtain ⟨hlay_c1, hlay_c2, hlay_c3⟩ := hlay_c
  have hlay_q : LayoutOk (prevCap.toNat * 24) 8 := ⟨by omega, ⟨3, rfl⟩, by omega⟩
  obtain ⟨hlay_q1, hlay_q2, hlay_q3⟩ := hlay_q
  have hmul24' : (prevCap + (prevCap <<< 1)) <<< 3 = prevCap * 24#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    omega
  have hmul24 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = prevCap * 24#64 := hmul24'
  have hx1_de2 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24]; bv_omega
  have hx1_de2' : (prevCap + (prevCap <<< 1)) <<< 3 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24']; bv_omega
  have hx1_de2_nat : ((prevCap + (prevCap <<< 1#64)) <<< 3#64).toNat = prevCap.toNat * 24 := by
    rw [hmul24]; bv_omega
  have hx1_de2_nat' : ((prevCap + (prevCap <<< 1)) <<< 3).toNat = prevCap.toNat * 24 := by
    rw [hmul24']; bv_omega
  rw [hdrP_coro_eq]
  simp only [sepConj_assoc]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  wp_steps
  wp_call hdealloc (p, c.toNat, 1)
  wp_steps
  refine SepWP.weaken_pre
    (entails_replace_sub_k2_pl
      (prevVec1_outer_merge_k2_pl prevPtr c p prevCap.toNat hcapb)
      (by sep_focus) rfl) ?_
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  simp_all only [BitVec.add_zero, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

/-- Proves `OverK2SegCliPlacedStmt` from `__rust_dealloc` on `lsProg_518`. -/
theorem overK2Seg_cli_placed [LibsignalPlacement]
    (hdealloc : ∀ {A : RustAlloc} ext,
      subroutine_ok (lsProg_518 ext)
        (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    OverK2SegCliPlacedStmt := by
  intro A ext s coroPtr outPtr errTag prevCap prevPtr
    w_370 w_378 w_380 w_388
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
    w_22 w_390 u_ret08 u_ret2c b_2c0 enc
    hpc hrun hsp_align hx19 hx22 hx25 hx26 hx28
  by_cases hcap : prevCap = 0#64
  · subst hcap
    refine SepWP.weaken_pre
      (sepConj_mono_left (prevVecAt_one_cap0_false_k2_pl A (coroPtr + 0xe0#64) prevPtr enc)) ?_
    exact sepWP_pure_elim_k2_pl fun h => False.elim h
  · refine SepWP.weaken_pre
      (sepConj_mono_left (prevVecAt_one_drop_split_k2_pl A (coroPtr + 0xe0#64) prevCap prevPtr enc hcap)) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine sepWP_exists_elim_k2_pl fun c => sepWP_exists_elim_k2_pl fun p => ?_
    refine sepWP_pure_elim_k2_pl fun ⟨hcap1, hcap2, _⟩ => ?_
    refine sepWP_pure_elim_k2_pl fun hc => ?_
    by_cases hc0 : c = 0#64
    · subst hc0
      simp only [↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (p3_err_tail_b_prev1_c0_placed_wp ext (hdealloc (A := A) ext)
          s coroPtr outPtr errTag prevCap prevPtr p
          w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
          savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
          savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
          w_22 w_390 u_ret08 u_ret2c b_2c0
          hcap ⟨hcap1, hcap2⟩ hpc hrun hsp_align hx19 hx22 hx25 hx26 hx28)
    · simp only [hc0, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (p3_err_tail_b_prev1_cnz_placed_wp ext (hdealloc (A := A) ext)
          s coroPtr outPtr errTag prevCap prevPtr c p
          w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
          savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
          savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
          w_22 w_390 u_ret08 u_ret2c b_2c0
          hcap ⟨hcap1, hcap2⟩ hc0 hc hpc hrun hsp_align hx19 hx22 hx25 hx26 hx28)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

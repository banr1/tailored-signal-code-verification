/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Top
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.PostPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneGen
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePack
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop

/-!
# Relocatable Top-Level Version-Mismatch Closure Composition

Relocatable (`[LibsignalPlacement]` / `[LibsignalFullPlacement]`) top-level compositions for the
version-mismatch path at `(blkPl_518).base + 0x1e04` on `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (prostSSGQAt ssgqOf)

open ProofLib.GenPlacedFetches

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Spatial bridge helpers between `PrevDec` and `VerNe` -/

private theorem overDecScratchPre_eq_prevDec_pl (sp : BitVec 64) :
    overDecScratchPre sp = PrevDec.overDecScratchPre sp := by
  have h920 :
      memRegion (sp + 0x920#64) 112 =
        memRegion (sp + 0x920#64) 16 ∗ memRegion (sp + 0x930#64) 96 :=
    ProofLib.memRegion_split' (b := sp + 0x920#64) (n := 16) (k := 96) (b' := sp + 0x930#64)
      rfl (by bv_omega) (by decide)
  have h930 :
      memRegion (sp + 0x930#64) 344 =
        memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 248 :=
    ProofLib.memRegion_split' (b := sp + 0x930#64) (n := 96) (k := 248) (b' := sp + 0x990#64)
      rfl (by bv_omega) (by decide)
  have h990 :
      memRegion (sp + 0x990#64) 256 =
        memRegion (sp + 0x990#64) 248 ∗ memRegion (sp + 0xa88#64) 8 :=
    ProofLib.memRegion_split' (b := sp + 0x990#64) (n := 248) (k := 8) (b' := sp + 0xa88#64)
      rfl (by bv_omega) (by decide)
  unfold overDecScratchPre PrevDec.overDecScratchPre
  rw [h920, h930, h990]
  ac_rfl

private theorem prevDec_scratchPost_eq_pl (sp : BitVec 64)
    (v : Symbolic.Swarm.TRREF.B3DeserQ.SSGQ) :
    PrevDec.overDecScratchPost sp v =
      Symbolic.Swarm.TRREF.B3DeserQ.prostSSGQAt A0 (sp + 0x930#64) v ∗
        overDecScratchPost sp := by
  unfold PrevDec.overDecScratchPost PrevDec.overDecScratchPostExt overDecScratchPost
  ac_rfl

private theorem overPrevElemAt_eq_exists_prevDec_pl (prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) :
    overPrevElemAt A0 prevCap prevPtr enc =
      ∃∗ encCap : BitVec 64, ∃∗ encPtr : BitVec 64,
        PrevDec.overPrevElemAt prevCap prevPtr encCap encPtr enc := by
  unfold overPrevElemAt PrevDec.overPrevElemAt PrevDec.overPrevElemAtExt vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem prevDec_elemAt_entails_overPrevElemAt_pl
    (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8)) :
    PrevDec.overPrevElemAt prevCap prevPtr encCap encPtr enc ⊢
      overPrevElemAt A0 prevCap prevPtr enc := by
  rw [overPrevElemAt_eq_exists_prevDec_pl]
  exact Entails.sepExists_right encCap (Entails.sepExists_right encPtr (Entails.refl _))

/-! ## `LibsignalCodeRoLoaded`-threaded `VerNe` composition -/

private theorem entails_replace_sub_top_pl {P A A' F Q : SepProp}
    (hA : A ⊢ A') (hP : P = A ∗ F) (hQ : Q = A' ∗ F) : P ⊢ Q := by
  rw [hP, hQ]; exact sepConj_mono_left hA

private theorem prevVecAt_one_drop_split_top_pl (A : RustAlloc) (r cap q : BitVec 64)
    (enc : List (BitVec 8)) (hcap : cap ≠ 0#64) :
    prevVecAt A r cap q [enc] ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64,
        ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        ⌜c.toNat < 2 ^ 63⌝ ∗ HdrP r cap q 1#64 ∗ A.live q (cap.toNat * 24) 8 ∗
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
    unfold vecHeader; simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right ?_)
    refine sepConj_mono (pointsTo64_entails_memRegion (q + 16#64) _) ?_
    exact Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.refl _)
  refine Entails.trans h0 ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun c => Entails.sepExists_right c ?_
  refine Entails.sepExists_elim fun p => Entails.sepExists_right p ?_
  exact Entails.of_eq (by ac_rfl)

private theorem prevVec1_outer_merge_top_pl (q c p : BitVec 64) (cap : Nat)
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

private theorem prevVecAt_one_cap0_false_top_pl (A : RustAlloc) (r q : BitVec 64)
    (enc : List (BitVec 8)) :
    prevVecAt A r 0#64 q [enc] ⊢ ⌜False⌝ := by
  rw [prevVecAt_eq]; unfold RustHeap.vecBuf; rw [sepConj_left_comm]
  exact Entails.pure_left fun ⟨hlen, _, _⟩ => nomatch hlen

private theorem sepWP_exists_elim_top_pl {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {P : α → SepProp} {post : State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) :
    SepWP prog pc s (∃∗ a, P a) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm; exact h a R ha

private theorem sepWP_pure_elim_top_pl {prog : Program} {pc : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog pc s P post) :
    SepWP prog pc s (⌜φ⌝ ∗ P) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

set_option maxHeartbeats 1200000 in
private theorem p3_err_tail_b_prev1_c0_top_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr outPtr errTag prevCap prevPtr p
      w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap : prevCap ≠ 0#64) (hcapb : 1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x359c#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (lsProg_518 ext) retAddr s
      (HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
       (prevPtr ↦₆₄ 0#64) ∗ ((prevPtr + 8#64) ↦₆₄ p) ∗ memRegion (prevPtr + 16#64) 8 ∗
       memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24) ∗ A.pool ∗
       stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗ ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ w_378) ∗ ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ w_388) ∗ ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗ ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
          ((outPtr + 0x14#64) ↦₆₄ w_378) ∗ ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗ ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗ ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗ ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
          ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗ ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
          ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗ ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗ ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
          ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗ ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
          ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧ s1.readReg64 .x19 = savedX19 ∧
        s1.readReg64 .x20 = savedX20 ∧ s1.readReg64 .x21 = savedX21 ∧
        s1.readReg64 .x22 = savedX22 ∧ s1.readReg64 .x23 = savedX23 ∧
        s1.readReg64 .x24 = savedX24 ∧ s1.readReg64 .x25 = savedX25 ∧
        s1.readReg64 .x26 = savedX26 ∧ s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x28 = savedX28 ∧ s1.readReg64 .x29 = savedX29 ∧
        s1.readReg64 .x30 = retAddr ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
  have hlay_q : LayoutOk (prevCap.toNat * 24) 8 := ⟨by omega, ⟨3, rfl⟩, by omega⟩
  obtain ⟨hlay_q1, hlay_q2, hlay_q3⟩ := hlay_q
  have hmul24' : (prevCap + (prevCap <<< 1)) <<< 3 = prevCap * 24#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]; omega
  have hmul24 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = prevCap * 24#64 := hmul24'
  have hx1_de2 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24]; bv_omega
  have hx1_de2' : (prevCap + (prevCap <<< 1)) <<< 3 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24']; bv_omega
  have hx1_de2_nat : ((prevCap + (prevCap <<< 1#64)) <<< 3#64).toNat = prevCap.toNat * 24 := by
    rw [hmul24]; bv_omega
  have hx1_de2_nat' : ((prevCap + (prevCap <<< 1)) <<< 3).toNat = prevCap.toNat * 24 := by
    rw [hmul24']; bv_omega
  rw [hdrP_coro_eq]; simp only [sepConj_assoc]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  wp_steps
  refine SepWP.weaken_pre
    (entails_replace_sub_top_pl
      (prevVec1_outer_merge_top_pl prevPtr 0#64 p prevCap.toNat hcapb)
      (by sep_focus) rfl) ?_
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  simp_all only [BitVec.add_zero, sepConj_assoc]; exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
private theorem p3_err_tail_b_prev1_cnz_top_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr outPtr errTag prevCap prevPtr c p
      w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap : prevCap ≠ 0#64) (hcapb : 1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63)
    (hc0 : c ≠ 0#64) (hc : c.toNat < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x359c#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (lsProg_518 ext) retAddr s
      (HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
       (prevPtr ↦₆₄ c) ∗ ((prevPtr + 8#64) ↦₆₄ p) ∗ memRegion (prevPtr + 16#64) 8 ∗
       A.live p c.toNat 1 ∗ memRegion p c.toNat ∗
       memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24) ∗ A.pool ∗
       stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗ ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ w_378) ∗ ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ w_388) ∗ ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗ ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
          ((outPtr + 0x14#64) ↦₆₄ w_378) ∗ ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗ ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗ ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗ ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
          ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗ ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
          ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗ ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗ ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
          ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗ ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
          ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧ s1.readReg64 .x19 = savedX19 ∧
        s1.readReg64 .x20 = savedX20 ∧ s1.readReg64 .x21 = savedX21 ∧
        s1.readReg64 .x22 = savedX22 ∧ s1.readReg64 .x23 = savedX23 ∧
        s1.readReg64 .x24 = savedX24 ∧ s1.readReg64 .x25 = savedX25 ∧
        s1.readReg64 .x26 = savedX26 ∧ s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x28 = savedX28 ∧ s1.readReg64 .x29 = savedX29 ∧
        s1.readReg64 .x30 = retAddr ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
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
      Nat.shiftLeft_eq]; omega
  have hmul24 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = prevCap * 24#64 := hmul24'
  have hx1_de2 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24]; bv_omega
  have hx1_de2' : (prevCap + (prevCap <<< 1)) <<< 3 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24']; bv_omega
  have hx1_de2_nat : ((prevCap + (prevCap <<< 1#64)) <<< 3#64).toNat = prevCap.toNat * 24 := by
    rw [hmul24]; bv_omega
  have hx1_de2_nat' : ((prevCap + (prevCap <<< 1)) <<< 3).toNat = prevCap.toNat * 24 := by
    rw [hmul24']; bv_omega
  rw [hdrP_coro_eq]; simp only [sepConj_assoc]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  wp_steps
  wp_call hdealloc (p, c.toNat, 1)
  wp_steps
  refine SepWP.weaken_pre
    (entails_replace_sub_top_pl
      (prevVec1_outer_merge_top_pl prevPtr c p prevCap.toNat hcapb)
      (by sep_focus) rfl) ?_
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  simp_all only [BitVec.add_zero, sepConj_assoc]; exact Entails.of_eq (by ac_rfl)

/-- Pointwise (`A`, `ext`) K2 per-site segment (`(blkPl_518).base + 0x359c → retAddr`). -/
theorem overK2Seg_cli_placed_at [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    OverK2SegCliPlacedAt A ext := by
  intro s coroPtr outPtr errTag prevCap prevPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
    w_22 w_390 u_ret08 u_ret2c b_2c0 enc
    hpc hrun hsp_align hx19 hx22 hx25 hx26 hx28
  by_cases hcap : prevCap = 0#64
  · subst hcap
    refine SepWP.weaken_pre
      (sepConj_mono_left (prevVecAt_one_cap0_false_top_pl A (coroPtr + 0xe0#64) prevPtr enc)) ?_
    exact sepWP_pure_elim_top_pl fun h => False.elim h
  · refine SepWP.weaken_pre
      (sepConj_mono_left (prevVecAt_one_drop_split_top_pl A (coroPtr + 0xe0#64) prevCap prevPtr enc hcap)) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine sepWP_exists_elim_top_pl fun c => sepWP_exists_elim_top_pl fun p => ?_
    refine sepWP_pure_elim_top_pl fun ⟨hcap1, hcap2, _⟩ => ?_
    refine sepWP_pure_elim_top_pl fun hc => ?_
    by_cases hc0 : c = 0#64
    · subst hc0
      simp only [↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (p3_err_tail_b_prev1_c0_top_wp ext hdealloc
          s coroPtr outPtr errTag prevCap prevPtr p
          w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
          savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
          savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
          w_22 w_390 u_ret08 u_ret2c b_2c0
          hcap ⟨hcap1, hcap2⟩ hpc hrun hsp_align hx19 hx22 hx25 hx26 hx28)
    · simp only [hc0, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (p3_err_tail_b_prev1_cnz_top_wp ext hdealloc
          s coroPtr outPtr errTag prevCap prevPtr c p
          w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
          savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
          savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
          w_22 w_390 u_ret08 u_ret2c b_2c0
          hcap ⟨hcap1, hcap2⟩ hc0 hc hpc hrun hsp_align hx19 hx22 hx25 hx26 hx28)

private theorem bind_sepWP_cro_frame_top_pl [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hCL : prog.CodeLoaded s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → prog.CodeLoaded sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q (P3P4.PanicOomProp s0)) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  intro R hm hL; rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim hoom | exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hcrom : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
    hcro.of_keepsFrozen hsteps.keepsFrozen
  have hCLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hCL
  obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hcrom hCLm hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem bind_sepWPp_frame_top_pl {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop} {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (P3P4.PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ F) Q (P3P4.PanicOomProp s0)) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  intro R hm hL; rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ F) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem stackAt_sub_eq_top_pl (sp : BitVec 64) (big small : Nat)
    (h1 : small ≤ big := by decide) (h2 : big ≤ 2 ^ 64 := by decide) :
    stackAt sp big = memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le h1] at h

private theorem prevVecAt_open_eq_top_pl (coroPtr prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (hcap : prevCap ≠ 0#64) :
    prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] =
      ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗ overPrevElemAt A0 prevCap prevPtr enc := by
  rw [prevVecAt_one_eq_elemAt A0 (coroPtr + 0xe0#64) prevCap prevPtr enc hcap, hdrP_coro_eq]
  ac_rfl

private theorem loopScratch_to_decPre_top_pl (sp : BitVec 64) :
    memRegion (sp + 0x538#64) 1016 ∗ memRegion (sp + 0x930#64) 48 ∗
    memRegion (sp + 0x960#64) 48 ∗ memRegion (sp + 0x990#64) 256 ∗
    memRegion (sp + 0xa90#64) 344 ∗ memRegion (sp + 0xbe8#64) 136 =
      memRegion (sp + 0x538#64) 40 ∗ memRegion (sp + 0x560#64) 320 ∗
      memRegion (sp + 0x6a0#64) 320 ∗ memRegion (sp + 0x7e0#64) 320 ∗
      overDecScratchPre sp := by
  have h538 :
      memRegion (sp + 0x538#64) 1016 =
        memRegion (sp + 0x538#64) 40 ∗ memRegion (sp + 0x560#64) 320 ∗
        memRegion (sp + 0x6a0#64) 320 ∗ memRegion (sp + 0x7e0#64) 320 ∗
        memRegion (sp + 0x920#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x538#64) (n := 40) (k := 976) (b' := sp + 0x560#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x560#64) (n := 320) (k := 656) (b' := sp + 0x6a0#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x6a0#64) (n := 320) (k := 336) (b' := sp + 0x7e0#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x7e0#64) (n := 320) (k := 16) (b' := sp + 0x920#64)
          rfl (by bv_omega) (by decide)]
  have h990 :
      memRegion (sp + 0x990#64) 256 =
        memRegion (sp + 0x990#64) 248 ∗ memRegion (sp + 0xa88#64) 8 :=
    ProofLib.memRegion_split' (b := sp + 0x990#64) (n := 248) (k := 8) (b' := sp + 0xa88#64)
      rfl (by bv_omega) (by decide)
  have h930 :
      memRegion (sp + 0x930#64) 344 =
        memRegion (sp + 0x930#64) 48 ∗ memRegion (sp + 0x960#64) 48 ∗
        memRegion (sp + 0x990#64) 248 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x930#64) (n := 48) (k := 296) (b' := sp + 0x960#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x960#64) (n := 48) (k := 248) (b' := sp + 0x990#64)
          rfl (by bv_omega) (by decide)]
  unfold overDecScratchPre; rw [h538, h990, h930]; ac_rfl

private theorem decScratchPost_join_930_top_pl (sp : BitVec 64) :
    overDecScratchPost sp ∗ memRegion (sp + 0x930#64) 344 = overDecScratchPre sp := by
  unfold overDecScratchPost overDecScratchPre; ac_rfl

private theorem mem920_16_split_top_pl (sp : BitVec 64) :
    memRegion (sp + 0x920#64) 16 =
      ∃∗ u920 : BitVec 64, ((sp + 0x920#64) ↦₆₄ u920) ∗ memRegion (sp + 0x928#64) 8 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x920#64) (n := 8) (k := 8) (b' := sp + 0x928#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x920#64), sepExists_sepConj_left]

private theorem mem920_16_fold_top_pl (sp w : BitVec 64) :
    ((sp + 0x920#64) ↦₆₄ w) ∗ memRegion (sp + 0x928#64) 8 ⊢ memRegion (sp + 0x920#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x920#64) (n := 8) (k := 8) (b' := sp + 0x928#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)

private theorem slot3e0_344_fold_top_pl (sp w : BitVec 64) :
    ((sp + 0x3e0#64) ↦₆₄ w) ∗ memRegion (sp + 0x3e8#64) 336 ⊢ memRegion (sp + 0x3e0#64) 344 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 336) (b' := sp + 0x3e8#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)

private theorem stack_bottom_join_top_pl (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - overDecStackX) ∗
    memRegion (sp - BitVec.ofNat 64 overDecStackX) (overDecStackX - growOneSpeStack) =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) :=
  (ProofLib.memRegion_split'
    (b := sp - BitVec.ofNat 64 rootStack)
    (n := rootStack - overDecStackX)
    (k := overDecStackX - growOneSpeStack)
    (b' := sp - BitVec.ofNat 64 overDecStackX)
    (by decide) (by dsimp only [rootStack, overDecStackX]; bv_omega) (by decide)).symm

set_option maxHeartbeats 400000 in
private theorem overPrevDecode_cro_placed_of_prevDec [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hPrevDec : PrevDec.OverPrevDecodeCroPlacedAt ext)
    (s0 s : State) (prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (sess : Session (List (BitVec 8)))
    (henc : enc = CryptoVerification.E2E.Record.encSession sess)
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩)
    (hver4 : sess.state.sessionVersion = 4#32)
    (hpp : sess.pendingPreKey = none)
    (hkpk : sess.pendingKyberPreKey = none)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hCL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1ee8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = s.sp + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64) (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 .x27 = prevPtr) (hx29 : s.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overPrevElemAt A0 prevCap prevPtr enc ∗ overDecScratchPre s.sp ∗
       A0.pool ∗ stackAt s.sp overDecStackX)
      (fun sf P_f =>
        (P_f ⊢
          prostSSGQAt A0 (s.sp + 0x930#64) (ssgqOf sess) ∗
          overDecScratchPost s.sp ∗ overPrevElemAt A0 prevCap prevPtr enc ∗
          A0.pool ∗ stackAt s.sp overDecStackX ∗ anyHeap) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.sp + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x27 = prevPtr ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ (lsProg_518 ext).CodeLoaded sf.mem)
      (P3P4.PanicOomProp s0) := by
  conv =>
    arg 4
    rw [overPrevElemAt_eq_exists_prevDec_pl, overDecScratchPre_eq_prevDec_pl]
    simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun encCap => SepWPp.exists_elim fun encPtr => ?_
  have hpre_eq :
      PrevDec.overPrevElemAt prevCap prevPtr encCap encPtr enc ∗
        PrevDec.overDecScratchPre s.sp ∗ A0.pool ∗ stackAt s.sp overDecStackX =
      PrevDec.overPrevElemAt prevCap prevPtr encCap encPtr enc ∗
        PrevDec.overDecScratchPre s.sp ∗ stackAt s.sp PrevDec.overDecStackX ∗ A0.pool := by
    dsimp only [overDecStackX, PrevDec.overDecStackX]; ac_rfl
  rw [hpre_eq]
  have hwp := hPrevDec s0 s prevCap prevPtr encCap encPtr
    enc sess ⟨henc, hQ, hver4, hpp, hkpk⟩ hcro hCL hpc hrun hsp_align htr hx21 hx24 hx25 hx27 hx29
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', P_f, hmf, hent_f, hsp', htr', hcrof, hCLf,
    hx19', hx20', hx21', hx24', hx25', _hx26', hx27', hx29_c70, hvregs'⟩ | hpan⟩ := hwp R hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc', hrun', P_f, hmf, ?_,
      hsp', htr', hx19', hx20', hx21', hx24', hx25', hx27',
      hx29_c70.trans hx29.symm, hvregs', hcrof, hCLf⟩⟩
    refine Entails.trans hent_f ?_
    rw [prevDec_scratchPost_eq_pl]
    refine Entails.trans (sepConj_mono_left (prevDec_elemAt_entails_overPrevElemAt_pl
      prevCap prevPtr encCap encPtr enc)) ?_
    dsimp only [overDecStackX, PrevDec.overDecStackX]
    exact Entails.of_eq (by ac_rfl)
  · exact ⟨sf, hsteps, Or.inr hpan⟩

set_option maxHeartbeats 800000 in
private theorem overPrevLoop_part1_cro_placed_ok [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hPrevDec : PrevDec.OverPrevDecodeCroPlacedAt ext)
    (s0 s : State) (coroPtr prevCap prevPtr wd0 u3e0 : BitVec 64)
    (enc : List (BitVec 8)) (sess : Session (List (BitVec 8)))
    (hcap : prevCap ≠ 0#64)
    (henc : enc = CryptoVerification.E2E.Record.encSession sess)
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩)
    (hver4 : sess.state.sessionVersion = 4#32)
    (hpp : sess.pendingPreKey = none)
    (hkpk : sess.pendingKyberPreKey = none)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hCL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1e78#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx29 : s.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗
       memRegion (s.sp + 0x538#64) 1016 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ memRegion (s.sp + 0x990#64) 256 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (s.sp + 0xbe8#64) 136 ∗
       A0.pool ∗ stackAt s.sp overDecStackX)
      (fun s2 P_f =>
        (P_f ⊢
          prostSSGQAt A0 (s.sp + 0x930#64) (ssgqOf sess) ∗ overDecScratchPost s.sp ∗
          memRegion (s.sp + 0x538#64) 40 ∗ memRegion (s.sp + 0x560#64) 320 ∗
          memRegion (s.sp + 0x6a0#64) 320 ∗ memRegion (s.sp + 0x7e0#64) 320 ∗
          prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
          ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          A0.pool ∗ stackAt s.sp overDecStackX ∗ anyHeap) ∧
        s2.sp = s.sp ∧ s2.trace = s0.trace ∧
        s2.readReg64 .x19 = coroPtr ∧ s2.readReg64 .x21 = s.sp + 0x930#64 ∧
        s2.readReg64 .x27 = prevPtr ∧ s2.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem ∧ (lsProg_518 ext).CodeLoaded s2.mem)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (prevVecAt_open_eq_top_pl coroPtr prevCap prevPtr enc hcap))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (loopScratch_to_decPre_top_pl s.sp)) (by sep_focus) ?_
  refine bind_sepWP_cro_frame_top_pl hcro hCL
    (overPrevLoop_head_cli_placed_wp ext s coroPtr prevCap prevPtr u3e0 wd0 hpc hrun hsp_align hx19)
    (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 hCL1
      ⟨hsp1, htr1, hx19_1, _, hx21_1, hx24_1, hx25_1, _, hx27_1, hx29_1, hvregs1⟩ => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  have htr1_0 : s1.trace = s0.trace := htr1.trans htr
  have hx21_1' : s1.readReg64 .x21 = s1.sp + 0x930#64 := by rw [hx21_1, hsp1]
  have hx29_1' : s1.readReg64 .x29 = s1.sp + 0xc70#64 := by rw [hx29_1, hx29, hsp1]
  have hdec := overPrevDecode_cro_placed_of_prevDec hPrevDec s0 s1 prevCap prevPtr enc sess
    henc hQ hver4 hpp hkpk hcro1 hCL1 hpc1 hrun1 hsp1_align htr1_0 hx21_1' hx24_1 hx25_1 hx27_1 hx29_1'
  rw [hsp1] at hdec
  refine bind_sepWPp_frame_top_pl hdec (by sep_focus)
    fun s2 hpc2 hrun2
      ⟨hsp2_1, htr2, hx19_2, _, hx21_2, _, _, hx27_2, hx29_2, hvregs_2_1, hcro2, hCL2⟩ => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (prevVecAt_open_eq_top_pl coroPtr prevCap prevPtr enc hcap).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpc2 hrun2
    ⟨Entails.of_eq (by ac_rfl),
     hsp2_1, htr2, hx19_2.trans hx19_1, hx21_2, hx27_2,
     hx29_2.trans (hx29_1.trans hx29), hvregs_2_1.trans hvregs1, hcro2, hCL2⟩

set_option maxHeartbeats 800000 in
private theorem overPrevLoop_part2_cro_placed_ok [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A0)))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (sessionMemcpySpec allocHookStack))
    (s0 s s2 : State) (coroPtr prevPtr errsPtr : BitVec 64)
    (msgVer : BitVec 32) (sess : Session (List (BitVec 8)))
    (hver_ne : msgVer ≠ 4#32)
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩)
    (hver4 : sess.state.sessionVersion = 4#32)
    (hkpk : sess.pendingKyberPreKey = none)
    (hcro2 : StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
    (hCL2 : (lsProg_518 ext).CodeLoaded s2.mem)
    (hpc2 : s2.pc = (blkPl_518).base + 0x2620#64) (hrun2 : s2.status = .Running)
    (hs2_sp : s2.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr2 : s2.trace = s0.trace)
    (hx19_2 : s2.readReg64 .x19 = coroPtr) (hx21_2 : s2.readReg64 .x21 = s.sp + 0x930#64)
    (hx27_2 : s2.readReg64 .x27 = prevPtr) (hx29_2 : s2.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s2
      (prostSSGQAt A0 (s.sp + 0x930#64) (ssgqOf sess) ∗ overDecScratchPost s.sp ∗
       memRegion (s.sp + 0x538#64) 40 ∗ memRegion (s.sp + 0x560#64) 320 ∗
       memRegion (s.sp + 0x6a0#64) 320 ∗ memRegion (s.sp + 0x7e0#64) 320 ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ memRegion (errsPtr + 48#64) 144 ∗
       pqLogLevelCellPlaced ∗ A0.pool ∗ stackAt s.sp overDecStackX)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((errsPtr + 56#64) ↦₃₂ msgVer) ∗ memRegion (errsPtr + 60#64) 36 ∗
          memRegion (errsPtr + 96#64) 96 ∗ memRegion (s.sp + 0x538#64) 1016 ∗
          memRegion (s.sp + 0x930#64) 48 ∗ memRegion (s.sp + 0x960#64) 48 ∗
          memRegion (s.sp + 0x990#64) 256 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
          memRegion (s.sp + 0xbe8#64) 136 ∗ pqLogLevelCellPlaced ∗
          A0.pool ∗ stackAt s.sp overDecStackX) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s2 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ (lsProg_518 ext).CodeLoaded sf.mem)
      (P3P4.PanicOomProp s0) := by
  dsimp only [overDecScratchPost]
  refine P3P4.SepWPp.weaken_frame (overPrevPeel_ok sess hQ hver4 hkpk (s.sp + 0x930#64))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun r1 =>
    SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun H => ?_
  refine SepWPp.pure_elim fun ⟨hw0, hr1, hr2, hdropFromMoves⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (mem920_16_split_top_pl s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u920 => ?_
  have hstk_alloc := stackAt_sub_eq_top_pl s.sp overDecStackX allocHookStack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
  have hx21_2' : s2.readReg64 .x21 = s2.sp + 0x930#64 := by rw [hx21_2, hs2_sp]
  have hmv := overPrevMoves_cli_placed_ok ext hmemcpy s2 w0 w1 w2 u920 r1 r2
    hw0 hr1 hr2 hpc2 hrun2 hsp2_align hx21_2'
  rw [hs2_sp] at hmv
  refine bind_sepWP_cro_frame_top_pl hcro2 hCL2 hmv (by sep_focus)
    fun s3 hpc3 hrun3 hcro3 hCL3
      ⟨hsp3_2, htr3_2, hx8_3, hx19_3, _, hx27_3, hx29_3, hvregs3⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (mem920_16_fold_top_pl s.sp (s2.readReg64 .x26)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame hdropFromMoves (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun G => SepWPp.exists_elim fun st => ?_
  refine SepWPp.pure_elim fun _ => ?_
  have hstk_grow := stackAt_sub_eq_top_pl s.sp overDecStackX growOneSpeStack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have hsp3 : s3.sp = s.sp := hsp3_2
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
  have htr3 : s3.trace = s0.trace := htr3_2.trans htr2
  have hx19_3' : s3.readReg64 .x19 = coroPtr := hx19_3.trans hx19_2
  have hx27_3' : s3.readReg64 .x27 = prevPtr := hx27_3.trans hx27_2
  have hx29_3' : s3.readReg64 .x29 = s.sp + 0xc70#64 := hx29_3.trans hx29_2
  have herr := overPrevErr_cro_placed_at ext hLogClosure hDropSS3 s0 s3 prevPtr errsPtr msgVer G st
    hver_ne hcro3 hCL3 hpc3 hrun3 hsp3_align htr3 hx8_3 hx27_3'
  rw [hsp3] at herr
  refine bind_sepWPp_frame_top_pl herr (by sep_focus)
    fun sf hpcf hrunf ⟨hspf_3, htrf, hx19_f, _, hx29_f, hvregsf, hcrof, hCLf⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow.symm) (by sep_focus) ?_
  have hfold_post :
      memRegion (s.sp + 0x920#64) 16 ∗ memRegion (s.sp + 0xa88#64) 8 ∗
      memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (s.sp + 0xbe8#64) 136 ∗
      memRegion (s.sp + 0x930#64) 344 = overDecScratchPre s.sp := by
    simpa only [overDecScratchPost, sepConj_assoc] using decScratchPost_join_930_top_pl s.sp
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hfold_post) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (loopScratch_to_decPre_top_pl s.sp).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf
    ⟨Entails.of_eq (by ac_rfl),
     hspf_3, htrf, hx19_f.trans hx19_3', hx29_f.trans hx29_3',
     hvregsf.trans hvregs3, hcrof, hCLf⟩

set_option maxHeartbeats 600000 in
/-- Pointwise (`ext`) `StoreKit.LibsignalCodeRoLoaded lsmpl`-threaded 1-element `previous_sessions`
loop (`(blkPl_518).base + 0x1e78 → (blkPl_518).base + 0x2cfc`) on `lsProg_518 ext`. -/
theorem overPrevLoop_cro_placed_at [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hPrevDec : PrevDec.OverPrevDecodeCroPlacedAt ext)
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A0)))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (sessionMemcpySpec allocHookStack))
    (s0 s : State) (coroPtr prevCap prevPtr errsPtr wd0 u3e0 : BitVec 64)
    (err0_w0 : BitVec 64) (msgVer : BitVec 32) (enc : List (BitVec 8))
    (hcap : prevCap ≠ 0#64) (hver_ne : msgVer ≠ 4#32) (hEnc : OverPrevEncOK enc)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hCL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1e78#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx29 : s.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s
      (prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗
       (errsPtr ↦₆₄ err0_w0) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 12#64) 36 ∗ memRegion (errsPtr + 48#64) 144 ∗
       memRegion (s.sp + 0x538#64) 1016 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ memRegion (s.sp + 0x990#64) 256 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (s.sp + 0xbe8#64) 136 ∗
       pqLogLevelCellPlaced ∗ A0.pool ∗ stackAt s.sp overDecStackX)
      (fun sf P_f =>
        (P_f ⊢
          prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          (errsPtr ↦₆₄ err0_w0) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 12#64) 36 ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((errsPtr + 56#64) ↦₃₂ msgVer) ∗ memRegion (errsPtr + 60#64) 36 ∗
          memRegion (errsPtr + 96#64) 96 ∗ memRegion (s.sp + 0x538#64) 1016 ∗
          memRegion (s.sp + 0x930#64) 48 ∗ memRegion (s.sp + 0x960#64) 48 ∗
          memRegion (s.sp + 0x990#64) 256 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
          memRegion (s.sp + 0xbe8#64) 136 ∗ pqLogLevelCellPlaced ∗
          A0.pool ∗ stackAt s.sp overDecStackX ∗ anyHeap) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ (lsProg_518 ext).CodeLoaded sf.mem)
      (P3P4.PanicOomProp s0) := by
  obtain ⟨sess, henc, hQ, hver4, hpp, hkpk⟩ := hEnc
  have hpart1 := overPrevLoop_part1_cro_placed_ok hPrevDec
    s0 s coroPtr prevCap prevPtr wd0 u3e0 enc sess
    hcap henc hQ hver4 hpp hkpk hcro hCL hpc hrun hsp_align htr hx19 hx29
  refine bind_sepWPp_frame_top_pl hpart1 (by sep_focus)
    fun s2 hpc2 hrun2
      ⟨hs2_sp, htr2, hx19_2, hx21_2, hx27_2, hx29_2, hvregs2, hcro2, hCL2⟩ => ?_
  have hpart2 := overPrevLoop_part2_cro_placed_ok ext hLogClosure hDropSS3 hmemcpy
    s0 s s2 coroPtr prevPtr errsPtr msgVer sess
    hver_ne hQ hver4 hkpk hcro2 hCL2 hpc2 hrun2 hs2_sp hsp_align htr2
    hx19_2 hx21_2 hx27_2 hx29_2
  refine bind_sepWPp_frame_top_pl hpart2 (by sep_focus)
    fun sf hpcf hrunf ⟨hspf, htrf, hx19f, hx29f, hvregsf, hcrof, hCLf⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    hspf, htrf, hx19f, hx29f, hvregsf.trans hvregs2, hcrof, hCLf⟩

set_option maxHeartbeats 800000 in
private theorem overVerNe_1e04_cro_a0_placed_at_cl [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A0)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A0)))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A0))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A0))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (sessionMemcpySpec allocHookStack))
    (hPrevDec : PrevDec.OverPrevDecodeCroPlacedAt ext)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap : prevCap ≠ 0#64)
    (msgVer : BitVec 32) (hver_ne : msgVer ≠ 4#32)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8)) (hEnc : OverPrevEncOK enc)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hF1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64) (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64) (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
       sessionStateAt A0 (s.sp + 0xa90#64) G₁ st ∗ sessionStateAt A0 (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       pqLogLevelCellPlaced ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A0.pool ∗ stackAt s.sp rootStack)
      (fun sf P_f =>
        (∃ wd0 : BitVec 64, P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
            memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
            stageP3ErrPostPrevEmptyPlaced A0 s0 s coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed) ∗ anyHeap) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (P3P4.PanicOomProp s0) := by
  have hstk_dec := stackAt_sub_eq_top_pl s.sp rootStack overDecStackX
  have hstk_grow := stackAt_sub_eq_top_pl s.sp overDecStackX growOneSpeStack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_dec) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have hs1 := overVerNe_1e04_to_1e78_cro_placed_at ext hLogClosure hGrow hDropSS3
    s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
    hcro1 hF1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1
  refine SepWPp.bind_sepWPp_frame_raw hs1 (by sep_focus)
    fun s6b P_6b hpc6b hrun6b
      ⟨⟨errsPtr, hP6b⟩, hs6b_sp, htr6b, hx19_6b, hx29_6b, hvregs_6b, hcro6b, hF6b⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP6b) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow.symm) (by sep_focus) ?_
  dsimp only [overScratch]
  have hsp6b_align : (s6b.sp &&& 15#64 == 0#64) = true := by rw [hs6b_sp]; exact hsp_align
  have hx29_6b' : s6b.readReg64 .x29 = s6b.sp + 0xc70#64 := by rw [hx29_6b, hs6b_sp]
  have hloop := overPrevLoop_cro_placed_at ext hPrevDec hLogClosure hDropSS3 hmemcpy
    s0 s6b coroPtr prevCap prevPtr errsPtr ud0
    0x8000000000000006#64 0x8000000000000006#64 msgVer enc hcap hver_ne hEnc
    hcro6b hF6b hpc6b hrun6b hsp6b_align htr6b hx19_6b hx29_6b'
  rw [hs6b_sp] at hloop
  refine SepWPp.bind_sepWPp_frame_raw hloop (by sep_focus)
    fun s7 P_7 hpc7 hrun7
      ⟨hP7, hs7_sp, htr7, hx19_7, _, hvregs_7_6b, hcro7, hF7⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP7) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have htail := over_ver_ne_tail_2cfc_cro_placed_at ext hshim halloc hdealloc hpanic hDropSS3
    (overK2Seg_cli_placed_at ext hdealloc)
    s0 s s7 coroPtr ctxPtr outPtr errsPtr prevCap prevPtr msgVer msgVer b_2c0 enc recG st
    hcro7 hF7 hpc7 hrun7 hs7_sp hsp_align htr7 hx19_7
  refine SepWPp.bind_sepWPp_frame_raw htail (by sep_focus)
    fun sf P_f hpcf hrunf ⟨hPf, hspf, htrf, hcc, hcrof, _hFf, hvregs_f_7⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hPf) ?_
  refine P3P4.SepWPp.weaken_frame
    (slot3e0_344_fold_top_pl s.sp 0xffffffffffffffff#64) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_bottom_join_top_pl s.sp)) (by sep_focus) ?_
  have herrs_ex :
      ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ⊢
      ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
        ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
        ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
    Entails.sepExists_right 4#64
      (Entails.sepExists_right errsPtr (Entails.sepExists_right 2#64 (Entails.refl _)))
  refine P3P4.SepWPp.weaken_frame herrs_ex (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨prevPtr + 24#64, ?_⟩, hspf, htrf, hcc, hcrof,
    hvregs_f_7.trans (hvregs_7_6b.trans hvregs_6b)⟩
  dsimp only [stageP3ErrPostPrevEmptyPlaced, overScratch, SessionState.recordError]
  exact Entails.of_eq (by ac_rfl)

/-- Pointwise (`ext`) `StoreKit.LibsignalCodeRoLoaded lsmpl`-threaded Stage P3/P4 `VerNe`
at `(blkPl_518).base + 0x1e04` (`A = Record.A0`) on `lsProg_518 ext`. -/
theorem overVerNe_1e04_cro_a0_placed_at [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A0)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A0)))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A0))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A0))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (sessionMemcpySpec allocHookStack))
    (hPrevDec : PrevDec.OverPrevDecodeCroPlacedAt ext)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap : prevCap ≠ 0#64)
    (msgVer : BitVec 32) (hver_ne : msgVer ≠ 4#32)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8)) (hEnc : OverPrevEncOK enc)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (_hver4 : st.version = 4#32) (_hsp_root : rootStack ≤ s.sp.toNat)
    (hcro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64) (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64) (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
       sessionStateAt A0 (s.sp + 0xa90#64) G₁ st ∗ sessionStateAt A0 (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       pqLogLevelCellPlaced ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A0.pool ∗ stackAt s.sp rootStack)
      (fun sf P_f =>
        (∃ wd0 : BitVec 64, P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
            memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
            stageP3ErrPostPrevEmptyPlaced A0 s0 s coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed) ∗ anyHeap) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (P3P4.PanicOomProp s0) :=
  fun R hm hF1 =>
    overVerNe_1e04_cro_a0_placed_at_cl ext hLogClosure hGrow hDropSS3
      hshim halloc hdealloc hpanic hmemcpy hPrevDec
      s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
      hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc G₁ recG st
      hcro1 hF1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 R hm hF1

private theorem hookSat_sessionMemcpy_of_frameless_top_pl {H : String → Option (State → State)}
    {sym : String} (hookStack : Nat) (h : HookSat H sym framelessMemcpySpec) :
    HookSat H sym (sessionMemcpySpec hookStack) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpySpec, libcMemcpySpec, framelessMemcpySpec, memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [sessionMemcpySpec, framelessMemcpySpec] at hpost ⊢
    ac_nf at hpost ⊢

/-- Hook-discharged `LibsignalCodeRoLoaded`-threaded Stage P3/P4 `VerNe` at
`(blkPl_518).base + 0x1e04` (`A = Record.A0`) on `lsProg_518 ext`. -/
theorem overVerNe_1e04_cro_a0_placed_of_hooks [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A0)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A0)))
    (hshim_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
      noAllocShimSpec)
    (halloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" (rustAllocSpec A0))
    (hrealloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"
      (rustReallocSpec A0))
    (hdealloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustDeallocSpec A0))
    (hmc_sat : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : ext CryptoVerification.LibsignalTripleRatchet.Prost.lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap : prevCap ≠ 0#64)
    (msgVer : BitVec 32) (hver_ne : msgVer ≠ 4#32)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8)) (hEnc : OverPrevEncOK enc)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hver4 : st.version = 4#32) (hsp_root : rootStack ≤ s.sp.toNat)
    (hcro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64) (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64) (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
       sessionStateAt A0 (s.sp + 0xa90#64) G₁ st ∗ sessionStateAt A0 (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       pqLogLevelCellPlaced ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A0.pool ∗ stackAt s.sp rootStack)
      (fun sf P_f =>
        (∃ wd0 : BitVec 64, P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
            memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
            stageP3ErrPostPrevEmptyPlaced A0 s0 s coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed) ∗ anyHeap) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (P3P4.PanicOomProp s0) :=
  overVerNe_1e04_cro_a0_placed_at ext hLogClosure hGrow hDropSS3
    (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518) hshim_sat)
    (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518) halloc_sat)
    (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518) hdealloc_sat)
    hpanic_raw
    (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518)
      (hookSat_sessionMemcpy_of_frameless_top_pl allocHookStack hmc_sat))
    (PrevDec.overPrevDecode_cro_placed_of_hooks hshim_sat halloc_sat hrealloc_sat hdealloc_sat
      hmc_sat hpanic_alloc hpanic_raw)
    s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
    hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc G₁ recG st
    hver4 hsp_root hcro1 hpc1 hrun1 hs1_sp hsp_align htr1
    hx9_1 hx19_1 hx24_1 hx27_1 hx29_1

/-! ## `LibsignalFrozen` / `[LibsignalFullPlacement]` corollaries -/

private theorem bind_sepWPp_fr_frame_top_pl [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s0 s : State} {P P_stage P_stage_post F : SepProp}
    {Q_regs : State → Prop} {Q : State → SepProp → Prop}
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hstage : SepWPp prog mid s P_stage (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (P3P4.PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalFrozen lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ F) Q (P3P4.PanicOomProp s0)) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  intro R hm hL; rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ F) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm (libsignalFrozen_of_keepsFrozen hfr hsteps.keepsFrozen)
        hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 800000 in
private theorem overPrevLoop_part2_frozen_placed_ok [LibsignalFullPlacement]
    (ext : String → Option (State → State))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A0)))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (sessionMemcpySpec allocHookStack))
    (s0 s s2 : State) (coroPtr prevPtr errsPtr : BitVec 64)
    (msgVer : BitVec 32) (sess : Session (List (BitVec 8)))
    (hver_ne : msgVer ≠ 4#32)
    (hQ : DeserializeScopeP_Q NonEmptyV1Q ⟨some sess⟩)
    (hver4 : sess.state.sessionVersion = 4#32)
    (hkpk : sess.pendingKyberPreKey = none)
    (hfr2 : LibsignalFrozen lsmpl s2.mem)
    (hCL2 : (lsProg_518 ext).CodeLoaded s2.mem)
    (hpc2 : s2.pc = (blkPl_518).base + 0x2620#64) (hrun2 : s2.status = .Running)
    (hs2_sp : s2.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr2 : s2.trace = s0.trace)
    (hx19_2 : s2.readReg64 .x19 = coroPtr) (hx21_2 : s2.readReg64 .x21 = s.sp + 0x930#64)
    (hx27_2 : s2.readReg64 .x27 = prevPtr) (hx29_2 : s2.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s2
      (prostSSGQAt A0 (s.sp + 0x930#64) (ssgqOf sess) ∗ overDecScratchPost s.sp ∗
       memRegion (s.sp + 0x538#64) 40 ∗ memRegion (s.sp + 0x560#64) 320 ∗
       memRegion (s.sp + 0x6a0#64) 320 ∗ memRegion (s.sp + 0x7e0#64) 320 ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ memRegion (errsPtr + 48#64) 144 ∗
       pqLogLevelCellPlaced ∗ A0.pool ∗ stackAt s.sp overDecStackX)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((errsPtr + 56#64) ↦₃₂ msgVer) ∗ memRegion (errsPtr + 60#64) 36 ∗
          memRegion (errsPtr + 96#64) 96 ∗ memRegion (s.sp + 0x538#64) 1016 ∗
          memRegion (s.sp + 0x930#64) 48 ∗ memRegion (s.sp + 0x960#64) 48 ∗
          memRegion (s.sp + 0x990#64) 256 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
          memRegion (s.sp + 0xbe8#64) 136 ∗ pqLogLevelCellPlaced ∗
          A0.pool ∗ stackAt s.sp overDecStackX) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s2 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ (lsProg_518 ext).CodeLoaded sf.mem)
      (P3P4.PanicOomProp s0) := by
  dsimp only [overDecScratchPost]
  refine P3P4.SepWPp.weaken_frame (overPrevPeel_ok sess hQ hver4 hkpk (s.sp + 0x930#64))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun r1 =>
    SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun H => ?_
  refine SepWPp.pure_elim fun ⟨hw0, hr1, hr2, hdropFromMoves⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (mem920_16_split_top_pl s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u920 => ?_
  have hstk_alloc := stackAt_sub_eq_top_pl s.sp overDecStackX allocHookStack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
  have hx21_2' : s2.readReg64 .x21 = s2.sp + 0x930#64 := by rw [hx21_2, hs2_sp]
  have hmv := overPrevMoves_cli_placed_ok ext hmemcpy s2 w0 w1 w2 u920 r1 r2
    hw0 hr1 hr2 hpc2 hrun2 hsp2_align hx21_2'
  rw [hs2_sp] at hmv
  refine bind_sepWP_fr_frame hCL2 hfr2 hmv (by sep_focus)
    fun s3 hpc3 hrun3 hCL3 hfr3
      ⟨hsp3_2, htr3_2, hx8_3, hx19_3, _, hx27_3, hx29_3, hvregs3⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (mem920_16_fold_top_pl s.sp (s2.readReg64 .x26)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame hdropFromMoves (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun G => SepWPp.exists_elim fun st => ?_
  refine SepWPp.pure_elim fun _ => ?_
  have hstk_grow := stackAt_sub_eq_top_pl s.sp overDecStackX growOneSpeStack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have hsp3 : s3.sp = s.sp := hsp3_2
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
  have htr3 : s3.trace = s0.trace := htr3_2.trans htr2
  have hx19_3' : s3.readReg64 .x19 = coroPtr := hx19_3.trans hx19_2
  have hx27_3' : s3.readReg64 .x27 = prevPtr := hx27_3.trans hx27_2
  have hx29_3' : s3.readReg64 .x29 = s.sp + 0xc70#64 := hx29_3.trans hx29_2
  have herr := overPrevErr_frozen_placed_at ext hDropSS3 s0 s3 prevPtr errsPtr msgVer G st
    hver_ne hfr3 hCL3 hpc3 hrun3 hsp3_align htr3 hx8_3 hx27_3'
  rw [hsp3] at herr
  refine bind_sepWPp_frame_top_pl herr (by sep_focus)
    fun sf hpcf hrunf ⟨hspf_3, htrf, hx19_f, _, hx29_f, hvregsf, hcrof, hCLf⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow.symm) (by sep_focus) ?_
  have hfold_post :
      memRegion (s.sp + 0x920#64) 16 ∗ memRegion (s.sp + 0xa88#64) 8 ∗
      memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (s.sp + 0xbe8#64) 136 ∗
      memRegion (s.sp + 0x930#64) 344 = overDecScratchPre s.sp := by
    simpa only [overDecScratchPost, sepConj_assoc] using decScratchPost_join_930_top_pl s.sp
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hfold_post) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (loopScratch_to_decPre_top_pl s.sp).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf
    ⟨Entails.of_eq (by ac_rfl),
     hspf_3, htrf, hx19_f.trans hx19_3', hx29_f.trans hx29_3',
     hvregsf.trans hvregs3, hcrof, hCLf⟩

set_option maxHeartbeats 600000 in
/-- Pointwise (`ext`) `LibsignalFrozen lsmpl`-discharged 1-element `previous_sessions`
loop (`(blkPl_518).base + 0x1e78 → (blkPl_518).base + 0x2cfc`) on `lsProg_518 ext`. -/
theorem overPrevLoop_frozen_placed_at [LibsignalFullPlacement]
    (ext : String → Option (State → State))
    (hPrevDec : PrevDec.OverPrevDecodeCroPlacedAt ext)
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A0)))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (sessionMemcpySpec allocHookStack))
    (s0 s : State) (coroPtr prevCap prevPtr errsPtr wd0 u3e0 : BitVec 64)
    (err0_w0 : BitVec 64) (msgVer : BitVec 32) (enc : List (BitVec 8))
    (hcap : prevCap ≠ 0#64) (hver_ne : msgVer ≠ 4#32) (hEnc : OverPrevEncOK enc)
    (hfr : LibsignalFrozen lsmpl s.mem)
    (hCL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1e78#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx29 : s.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2cfc#64) s
      (prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗
       (errsPtr ↦₆₄ err0_w0) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 12#64) 36 ∗ memRegion (errsPtr + 48#64) 144 ∗
       memRegion (s.sp + 0x538#64) 1016 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ memRegion (s.sp + 0x990#64) 256 ∗
       memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (s.sp + 0xbe8#64) 136 ∗
       pqLogLevelCellPlaced ∗ A0.pool ∗ stackAt s.sp overDecStackX)
      (fun sf P_f =>
        (P_f ⊢
          prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          (errsPtr ↦₆₄ err0_w0) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 12#64) 36 ∗ ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((errsPtr + 56#64) ↦₃₂ msgVer) ∗ memRegion (errsPtr + 60#64) 36 ∗
          memRegion (errsPtr + 96#64) 96 ∗ memRegion (s.sp + 0x538#64) 1016 ∗
          memRegion (s.sp + 0x930#64) 48 ∗ memRegion (s.sp + 0x960#64) 48 ∗
          memRegion (s.sp + 0x990#64) 256 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
          memRegion (s.sp + 0xbe8#64) 136 ∗ pqLogLevelCellPlaced ∗
          A0.pool ∗ stackAt s.sp overDecStackX ∗ anyHeap) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ (lsProg_518 ext).CodeLoaded sf.mem)
      (P3P4.PanicOomProp s0) := by
  obtain ⟨sess, henc, hQ, hver4, hpp, hkpk⟩ := hEnc
  have hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem := Matched.lscro_of_frozen hfr
  have hpart1 := overPrevLoop_part1_cro_placed_ok hPrevDec
    s0 s coroPtr prevCap prevPtr wd0 u3e0 enc sess
    hcap henc hQ hver4 hpp hkpk hcro hCL hpc hrun hsp_align htr hx19 hx29
  refine bind_sepWPp_fr_frame_top_pl hfr hpart1 (by sep_focus)
    fun s2 hpc2 hrun2 hfr2
      ⟨hs2_sp, htr2, hx19_2, hx21_2, hx27_2, hx29_2, hvregs2, _hcro2, hCL2⟩ => ?_
  have hpart2 := overPrevLoop_part2_frozen_placed_ok ext hDropSS3 hmemcpy
    s0 s s2 coroPtr prevPtr errsPtr msgVer sess
    hver_ne hQ hver4 hkpk hfr2 hCL2 hpc2 hrun2 hs2_sp hsp_align htr2
    hx19_2 hx21_2 hx27_2 hx29_2
  refine bind_sepWPp_frame_top_pl hpart2 (by sep_focus)
    fun sf hpcf hrunf ⟨hspf, htrf, hx19f, hx29f, hvregsf, hcrof, hCLf⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    hspf, htrf, hx19f, hx29f, hvregsf.trans hvregs2, hcrof, hCLf⟩

set_option maxHeartbeats 800000 in
private theorem overVerNe_1e04_frozen_a0_placed_at_cl [LibsignalFullPlacement]
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A0)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A0)))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A0))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A0))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (sessionMemcpySpec allocHookStack))
    (hPrevDec : PrevDec.OverPrevDecodeCroPlacedAt ext)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap : prevCap ≠ 0#64)
    (msgVer : BitVec 32) (hver_ne : msgVer ≠ 4#32)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8)) (hEnc : OverPrevEncOK enc)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hF1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64) (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64) (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
       sessionStateAt A0 (s.sp + 0xa90#64) G₁ st ∗ sessionStateAt A0 (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       pqLogLevelCellPlaced ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A0.pool ∗ stackAt s.sp rootStack)
      (fun sf P_f =>
        (∃ wd0 : BitVec 64, P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
            memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
            stageP3ErrPostPrevEmptyPlaced A0 s0 s coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed) ∗ anyHeap) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (P3P4.PanicOomProp s0) := by
  have hstk_dec := stackAt_sub_eq_top_pl s.sp rootStack overDecStackX
  have hstk_grow := stackAt_sub_eq_top_pl s.sp overDecStackX growOneSpeStack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_dec) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have hs1 := overVerNe_1e04_to_1e78_frozen_placed_at ext hGrow hDropSS3
    s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
    hfr1 hF1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1
  refine SepWPp.bind_sepWPp_frame_raw hs1 (by sep_focus)
    fun s6b P_6b hpc6b hrun6b
      ⟨⟨⟨errsPtr, hP6b⟩, hs6b_sp, htr6b, hx19_6b, hx29_6b, hvregs_6b, _hcro6b, hF6b⟩, hfr6b⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP6b) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow.symm) (by sep_focus) ?_
  dsimp only [overScratch]
  have hsp6b_align : (s6b.sp &&& 15#64 == 0#64) = true := by rw [hs6b_sp]; exact hsp_align
  have hx29_6b' : s6b.readReg64 .x29 = s6b.sp + 0xc70#64 := by rw [hx29_6b, hs6b_sp]
  have hloop := overPrevLoop_frozen_placed_at ext hPrevDec hDropSS3 hmemcpy
    s0 s6b coroPtr prevCap prevPtr errsPtr ud0
    0x8000000000000006#64 0x8000000000000006#64 msgVer enc hcap hver_ne hEnc
    hfr6b hF6b hpc6b hrun6b hsp6b_align htr6b hx19_6b hx29_6b'
  rw [hs6b_sp] at hloop
  refine SepWPp.bind_sepWPp_frame_raw hloop (by sep_focus)
    fun s7 P_7 hpc7 hrun7
      ⟨hP7, hs7_sp, htr7, hx19_7, _, hvregs_7_6b, hcro7, hF7⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP7) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have htail := over_ver_ne_tail_2cfc_cro_placed_at ext hshim halloc hdealloc hpanic hDropSS3
    (overK2Seg_cli_placed_at ext hdealloc)
    s0 s s7 coroPtr ctxPtr outPtr errsPtr prevCap prevPtr msgVer msgVer b_2c0 enc recG st
    hcro7 hF7 hpc7 hrun7 hs7_sp hsp_align htr7 hx19_7
  refine SepWPp.bind_sepWPp_frame_raw htail (by sep_focus)
    fun sf P_f hpcf hrunf ⟨hPf, hspf, htrf, hcc, hcrof, _hFf, hvregs_f_7⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hPf) ?_
  refine P3P4.SepWPp.weaken_frame
    (slot3e0_344_fold_top_pl s.sp 0xffffffffffffffff#64) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_bottom_join_top_pl s.sp)) (by sep_focus) ?_
  have herrs_ex :
      ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ⊢
      ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
        ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
        ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
    Entails.sepExists_right 4#64
      (Entails.sepExists_right errsPtr (Entails.sepExists_right 2#64 (Entails.refl _)))
  refine P3P4.SepWPp.weaken_frame herrs_ex (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨prevPtr + 24#64, ?_⟩, hspf, htrf, hcc, hcrof,
    hvregs_f_7.trans (hvregs_7_6b.trans hvregs_6b)⟩
  dsimp only [stageP3ErrPostPrevEmptyPlaced, overScratch, SessionState.recordError]
  exact Entails.of_eq (by ac_rfl)

/-- Pointwise (`ext`) `LibsignalFrozen lsmpl`-discharged Stage P3/P4 `VerNe`
at `(blkPl_518).base + 0x1e04` (`A = Record.A0`) on `lsProg_518 ext`. -/
theorem overVerNe_1e04_frozen_a0_placed_at [LibsignalFullPlacement]
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A0)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A0)))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A0))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A0))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (sessionMemcpySpec allocHookStack))
    (hPrevDec : PrevDec.OverPrevDecodeCroPlacedAt ext)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap : prevCap ≠ 0#64)
    (msgVer : BitVec 32) (hver_ne : msgVer ≠ 4#32)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8)) (hEnc : OverPrevEncOK enc)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (_hver4 : st.version = 4#32) (_hsp_root : rootStack ≤ s.sp.toNat)
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64) (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64) (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
       sessionStateAt A0 (s.sp + 0xa90#64) G₁ st ∗ sessionStateAt A0 (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       pqLogLevelCellPlaced ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A0.pool ∗ stackAt s.sp rootStack)
      (fun sf P_f =>
        (∃ wd0 : BitVec 64, P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
            memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
            stageP3ErrPostPrevEmptyPlaced A0 s0 s coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed) ∗ anyHeap) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (P3P4.PanicOomProp s0) :=
  fun R hm hF1 =>
    overVerNe_1e04_frozen_a0_placed_at_cl ext hGrow hDropSS3
      hshim halloc hdealloc hpanic hmemcpy hPrevDec
      s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
      hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc G₁ recG st
      hfr1 hF1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 R hm hF1

/-- Hook-discharged `LibsignalFrozen`-threaded Stage P3/P4 `VerNe` at
`(blkPl_518).base + 0x1e04` (`A = Record.A0`) on `lsProg_518 ext` under `[LibsignalFullPlacement]`. -/
theorem overVerNe_1e04_frozen_a0_placed_of_hooks [LibsignalFullPlacement]
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A0)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A0)))
    (hshim_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
      noAllocShimSpec)
    (halloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" (rustAllocSpec A0))
    (hrealloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"
      (rustReallocSpec A0))
    (hdealloc_sat : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustDeallocSpec A0))
    (hmc_sat : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : ext CryptoVerification.LibsignalTripleRatchet.Prost.lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap : prevCap ≠ 0#64)
    (msgVer : BitVec 32) (hver_ne : msgVer ≠ 4#32)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8)) (hEnc : OverPrevEncOK enc)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hver4 : st.version = 4#32) (hsp_root : rootStack ≤ s.sp.toNat)
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64) (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64) (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
       sessionStateAt A0 (s.sp + 0xa90#64) G₁ st ∗ sessionStateAt A0 (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A0 (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       pqLogLevelCellPlaced ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A0.pool ∗ stackAt s.sp rootStack)
      (fun sf P_f =>
        (∃ wd0 : BitVec 64, P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
            memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
            stageP3ErrPostPrevEmptyPlaced A0 s0 s coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed) ∗ anyHeap) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      (P3P4.PanicOomProp s0) :=
  overVerNe_1e04_frozen_a0_placed_at ext hGrow hDropSS3
    (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518) hshim_sat)
    (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518) halloc_sat)
    (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518) hdealloc_sat)
    hpanic_raw
    (ls_hook_ok_ultra_of_mem (prog := lsProg_518 ext) (i := 518)
      (hookSat_sessionMemcpy_of_frameless_top_pl allocHookStack hmc_sat))
    (PrevDec.overPrevDecode_cro_placed_of_hooks hshim_sat halloc_sat hrealloc_sat hdealloc_sat
      hmc_sat hpanic_alloc hpanic_raw)
    s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
    hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc G₁ recG st
    hver4 hsp_root hfr1 hpc1 hrun1 hs1_sp hsp_align htr1
    hx9_1 hx19_1 hx24_1 hx27_1 hx29_1

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

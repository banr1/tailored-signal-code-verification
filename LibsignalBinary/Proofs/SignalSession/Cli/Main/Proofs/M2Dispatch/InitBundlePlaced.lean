/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.Pure
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops.Proofs

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.MainHops

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem cells3_to_memRegion_24 (a : BitVec 64) (v0 v1 v2 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ⊢ memRegion a 24 := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
    ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion a v0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) v1)
      (pointsTo64_entails_memRegion (a + 16#64) v2))

private theorem cells32_64_to_memRegion_32 (a : BitVec 64) (u0 u1 : BitVec 32)
    (v1 v2 v3 : BitVec 64) :
    (a ↦₃₂ u0) ∗ ((a + 4#64) ↦₃₂ u1) ∗ ((a + 8#64) ↦₆₄ v1) ∗
      ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢ memRegion a 32 := by
  rw [show (32 : Nat) = 8 + 24 by rfl, ProofLib.memRegion_split a 8 24 (by decide)]
  refine Entails.trans (Entails.of_eq (show
    (a ↦₃₂ u0) ∗ ((a + 4#64) ↦₃₂ u1) ∗ ((a + 8#64) ↦₆₄ v1) ∗
      ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) =
    ((a ↦₃₂ u0) ∗ ((a + 4#64) ↦₃₂ u1)) ∗
      (((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3))
    by ac_rfl)) (sepConj_mono (pointsTo32_pair_entails_memRegion8 a u0 u1) ?_)
  have hc3 := cells3_to_memRegion_24 (a + 8#64) v1 v2 v3
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hc3

private theorem ownedBytes_exact (A : RustAlloc) {p' : BitVec 64} {bs : List (BitVec 8)}
    (hpos : 0 < bs.length) (hle : bs.length ≤ 16384) (hp' : p' ≠ 0#64) :
    A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      ownedBytes A (BitVec.ofNat 64 bs.length) p' (BitVec.ofNat 64 bs.length) bs := by
  have htn : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0; have h := congrArg BitVec.toNat h0; rw [htn] at h
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz] at h; omega
  dsimp only [ownedBytes]
  simp only [hne0, ↓reduceIte, htn, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  exact pure_intro_entails ⟨trivial, Nat.le_refl _, by omega, hp'⟩ (Entails.refl _)

theorem step_init_bundle_274_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 w3 w4 w1 devw : BitVec 64}
    {peer : AddrV} {g : AddrGhost} {bs1 bs2 bs3 : List (BitVec 8)}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hbs3_pos : 0 < bs3.length) (hbs3_le : bs3.length ≤ 16384)
    (hparse_ok : parseArgs uuidParse (i.argv.map bytesOfString) = some (.init peer bs3))
    (hs : InMainPlaced CodeOk s0 s 0x274)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : s.readReg64 (.gpr 25#5) = g.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 bs3.length)
    (hx27 : s.readReg64 (.gpr 27#5) = p3)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hnext : ∀ (s' : State) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) ret s'
        (callHeap A w c ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
          argvAtP (s0.readReg64 .x1)
            ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ Statics)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) ret s
      (((fsp + 0x1b8#64) ↦₆₄ g.name.cap) ∗ ((fsp + 0x1c0#64) ↦₆₄ g.name.ptr) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 peer.name.length) ∗ ((fsp + 0x1d0#64) ↦₆₄ devw) ∗
        addrWords A peer g.name.cap g.name.ptr (BitVec.ofNat 64 peer.name.length) devw ∗
        argsBuf A vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        argvAtP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        m2LocalsRest fsp ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ Statics)
      Q Qp oom := by
  dsimp only
  have htry : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 588)
      (withLsRoCl lsmpl (tryAllocateInSpecOf resStack A).keepsFs) := hc.tryAllocateIn3
  have hmemcpy := memcpy_keepsFs_placed_ok hc
  have hres_le : resStack ≤ stk - mainFrameSize := by omega
  have hext_le : extHookStack ≤ stk - mainFrameSize := by
    dsimp only [mainFrameSize, extHookStack] at hstk ⊢; omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  have htn3 : (BitVec.ofNat 64 bs3.length).toNat = bs3.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne3 : (BitVec.ofNat 64 bs3.length == 0#64) = false := by
    apply beq_false_of_ne; intro h0; have h := congrArg BitVec.toNat h0
    rw [htn3] at h
    have hz : (0#64).toNat = 0 := rfl
    rw [hz] at h; omega
  rw [stackAt_split_ge (s0.sp - BitVec.ofNat 64 mainFrameSize) hres_le hsub64]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  have hfsp_align0 := fsp_align_of_spAligned hsp0
  generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp hfsp_align0 ⊢
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsmpl.base 588) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine main_call_keepsFs_placed (CodeOk := CodeOk)
    (x := ⟨fsp + 0x1b8#64, BitVec.ofNat 64 bs3.length, 1#64, 1#64⟩) (k_ret := 0x290)
    (F := ((fsp + 0x1d0#64) ↦₆₄ devw) ∗
      addrWords A peer g.name.cap g.name.ptr (BitVec.ofNat 64 peer.name.length) devw ∗
      argsBuf A vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
      argsBuf A (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
      argvAtP (s0.readReg64 .x1)
        ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗
      mainSaved s0 ∗
      ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
      m2LocalsRest fsp ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
        (stk - mainFrameSize - resStack) ∗ Statics)
    htry hinv1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [calleeSavedVRegs, arm64_norm, *]) hsp0
    (by simp only [arm64_norm, *])
    (hP := ?_) (hnext := ?_)
  · dsimp only [tryAllocateInSpecOf]
    simp only [arm64_norm, hsp]
    have hc3 : ((fsp + 440#64) ↦₆₄ g.name.cap) ∗ ((fsp + 448#64) ↦₆₄ g.name.ptr) ∗
        ((fsp + 456#64) ↦₆₄ BitVec.ofNat 64 peer.name.length) ⊢
        memRegion (fsp + 440#64) 24 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        cells3_to_memRegion_24 (fsp + 0x1b8#64) g.name.cap g.name.ptr
          (BitVec.ofNat 64 peer.name.length)
    have hlay3 : LayoutOk ((BitVec.ofNat 64 bs3.length).toNat * 1) 1 := by
      rw [htn3]; exact ⟨by omega, ⟨0, rfl⟩, by omega⟩
    have hn3_pos : 0 < (BitVec.ofNat 64 bs3.length).toNat := by rw [htn3]; exact hbs3_pos
    refine Entails.trans ?_
      (pure_intro_entails ⟨hn3_pos, hlay3⟩ (sepConj_mono_left hc3))
    exact Entails.of_eq (by ac_rfl)
  intro sm1 hin1 hcs1 hfs1
  dsimp only [tryAllocateInSpecOf]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun tag => SepWPp.exists_elim fun p' => ?_
  have hx19_1 : sm1.readReg64 (.gpr 19#5) = buf := hcs1.1.trans (by simp only [arm64_norm, *])
  have hx20_1 : sm1.readReg64 (.gpr 20#5) = vptr := hcs1.2.1.trans (by simp only [arm64_norm, *])
  have hx21_1 : sm1.readReg64 (.gpr 21#5) = g.name.ptr := hcs1.2.2.1.trans (by simp only [arm64_norm, *])
  have hx22_1 : sm1.readReg64 (.gpr 22#5) = BitVec.ofNat 64 peer.name.length :=
    hcs1.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx23_1 : sm1.readReg64 (.gpr 23#5) = vcap := hcs1.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx24_1 : sm1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
    hcs1.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx25_1 : sm1.readReg64 (.gpr 25#5) = g.name.cap :=
    hcs1.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx26_1 : sm1.readReg64 (.gpr 26#5) = BitVec.ofNat 64 bs3.length :=
    hcs1.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx27_1 : sm1.readReg64 (.gpr 27#5) = p3 :=
    hcs1.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx28_1 : sm1.readReg64 (.gpr 28#5) = devw :=
    hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  obtain ⟨hpc1, hrun1, hsp1, hfp1, hinv1', hvregs1, _⟩ := hin1
  rw [hfsp] at hsp1
  rw [mPcPlaced_eq] at hpc1
  simp only [arm64_norm, hsp]
  by_cases htag : tag = 1#64
  · subst htag
    simp only [↓reduceIte]
    rw [pointsTo64_one_split32 (fsp + 0x1b8#64)]
    have hpure1 : ∀ (A0 P0 B0 C0 R2 : SepProp),
        A0 ∗ (P0 ∗ B0 ∗ C0) ∗ R2 = P0 ∗ (A0 ∗ B0 ∗ C0 ∗ R2) :=
      fun _ _ _ _ _ => by ac_rfl
    rw [hpure1]
    refine SepWPp.pure_elim fun ⟨_, htr_oom⟩ => ?_
    have htr_oom' : sm1.trace = s0.trace ++ [allocFailedEvent] := by
      simpa only [arm64_norm, htr] using htr_oom
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0xfb8#64) hinv1'
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    have hin2 : InMainPlaced CodeOk s0 _ 0xfb8 := {
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, *]
      sp := by simp only [arm64_norm, *]
      fp := by simp only [arm64_norm, *]
      inv := hinv2
      vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
      spAligned := hsp0 }
    have hpan_perm : ∀ (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 W4 R0 : SepProp),
        (X0 ∗ X1 ∗ X2 ∗ X3 ∗ X4 ∗ X5 ∗ X6 ∗ X7 ∗ X8 ∗ X9 ∗ X10 ∗ X11 ∗ W4 ∗ R0) ⊢
          (W4 ∗ X2) ∗ (X0 ∗ X1 ∗ X3 ∗ X4 ∗ X5 ∗ X6 ∗ X7 ∗ X8 ∗ X9 ∗ X10 ∗ X11 ∗ R0) :=
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre (hpan_perm _ _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
    rw [← hfsp, ← mProgPlaced_eq]
    exact step_panic_f84_placed hc hin2 (by simp only [arm64_norm, *]) hpanic
  · simp only [htag, ↓reduceIte]
    have hpure2 : ∀ (A0 P0 R1 R2 : SepProp),
        A0 ∗ (P0 ∗ R1) ∗ R2 = P0 ∗ (A0 ∗ R1 ∗ R2) :=
      fun _ _ _ _ => by ac_rfl
    rw [hpure2]
    refine SepWPp.pure_elim fun ⟨htag0, hp'_ne, _, htr1⟩ => ?_
    rw [htag0]
    have htr1' : sm1.trace = s0.trace :=
      (by simpa only [arm64_norm] using htr1 : sm1.trace = s.trace).trans htr
    have hfs1' : sm1.fs = s0.fs :=
      (by simpa only [arm64_norm] using hfs1 : sm1.fs = s.fs).trans hfs
    have hmul1 : (BitVec.ofNat 64 bs3.length).toNat * 1 = bs3.length := by
      rw [htn3, Nat.mul_one]
    have hstk_perm : ∀ (A0 A1 PL S0 D AW AB1 AB2 AV MS W3 W4 W1 M2 STX ST : SepProp),
        A0 ∗ A1 ∗ PL ∗ S0 ∗ D ∗ AW ∗ AB1 ∗ AB2 ∗ AV ∗ MS ∗ W3 ∗ W4 ∗ W1 ∗ M2 ∗ STX ∗ ST =
          A0 ∗ A1 ∗ PL ∗ (STX ∗ S0) ∗ D ∗ AW ∗ AB1 ∗ AB2 ∗ AV ∗ MS ∗ W3 ∗ W4 ∗ W1 ∗ M2 ∗ ST :=
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by ac_rfl
    rw [hstk_perm, hmul1, ← stackAt_split_ge fsp hres_le hsub64, stackAt_split_ge fsp hext_le hsub64,
      pointsTo64_zero_split32 (fsp + 0x1b8#64)]
    dsimp only [argvAtP]
    rw [cStrAt_split p3 bs3]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ memcpyName) hinv1'
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv2
    refine main_call_keepsFs_placed (CodeOk := CodeOk) (x := (p', p3, bs3)) (k_ret := 0x2c0)
      (F := ((fsp + 0x1b8#64) ↦₃₂ 0#32) ∗ (((fsp + 0x1b8#64) + 4#64) ↦₃₂ 0#32) ∗
        ((fsp + 0x1c0#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗ ((fsp + 0x1c8#64) ↦₆₄ p') ∗
        ((fsp + 0x1d0#64) ↦₆₄ devw) ∗ A.live p' bs3.length 1 ∗
        addrWords A peer g.name.cap g.name.ptr (BitVec.ofNat 64 peer.name.length) devw ∗
        argsBuf A vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        ((s0.readReg64 .x1) ↦₆₄ p0) ∗ cStrAt p0 (bytesOfString "libsignal-cli") ∗
        ((s0.readReg64 .x1 + 8#64) ↦₆₄ p1) ∗ cStrAt p1 bs1 ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ p2) ∗ cStrAt p2 bs2 ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ p3) ∗
        ((p3 + BitVec.ofNat 64 bs3.length) ↦₈ 0#8) ∗
        ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ 0#64) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ devw) ∗ ((fsp + 0x48#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        ((fsp + 0x58#64) ↦₆₄ g.name.ptr) ∗ m2LocalsRest fsp ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - extHookStack) ∗ A.pool ∗ Statics)
      hmemcpy hinv2
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [calleeSavedVRegs, arm64_norm, *]) hsp0
      (by simp only [arm64_norm, *])
      (hP := ?_) (hnext := ?_)
    · dsimp only [session2MemcpySpecX]
      refine Entails.trans (Entails.of_eq (by simp only [arm64_norm, hsp1]; ac_rfl))
        (sepConj_mono_left (pure_intro_entails
          ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
            by simp only [arm64_norm, *]⟩ (Entails.refl _)))
    intro sm2 hin2 hcs2 hfs2
    dsimp only [session2MemcpySpecX]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
    have hx19_2 : sm2.readReg64 (.gpr 19#5) = buf := hcs2.1.trans (by simp only [arm64_norm, *])
    have hx20_2 : sm2.readReg64 (.gpr 20#5) = vptr := hcs2.2.1.trans (by simp only [arm64_norm, *])
    have hx21_2 : sm2.readReg64 (.gpr 21#5) = p' := hcs2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22_2 : sm2.readReg64 (.gpr 22#5) = BitVec.ofNat 64 peer.name.length :=
      hcs2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23_2 : sm2.readReg64 (.gpr 23#5) = vcap := hcs2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx24_2 : sm2.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
      hcs2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx25_2 : sm2.readReg64 (.gpr 25#5) = g.name.cap :=
      hcs2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hx26_2 : sm2.readReg64 (.gpr 26#5) = BitVec.ofNat 64 bs3.length :=
      hcs2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    have htr2' : sm2.trace = s0.trace :=
      htr2.trans ((by simp only [arm64_norm, *] : _ = sm1.trace).trans htr1')
    have hfs2' : sm2.fs = s0.fs :=
      hfs2.trans ((by simp only [arm64_norm, *] : _ = sm1.fs).trans hfs1')
    obtain ⟨hpc2, hrun2, hsp2, hfp2, hinv2', hvregs2, _⟩ := hin2
    rw [hfsp] at hsp2
    rw [mPcPlaced_eq] at hpc2
    simp only [arm64_norm, hsp1]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x550#64) hinv2'
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv3
    have hin3 : InMainPlaced CodeOk s0 _ 0x550 := {
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, *]
      sp := by simp only [arm64_norm, *]
      fp := by simp only [arm64_norm, *]
      inv := hinv3
      vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
      spAligned := hsp0 }
    let w : CallW := ⟨g.name.cap, g.name.ptr, BitVec.ofNat 64 peer.name.length, devw,
      BitVec.ofNat 64 bs3.length, p', BitVec.ofNat 64 bs3.length⟩
    rw [← mProgPlaced_eq]
    refine SepWPp.weaken_pre ?_
      (step_ok_tail_548_placed (buf := buf) (vcap := vcap) (vptr := vptr) (p0 := p0) (w := w)
        (c := .init peer bs3) (ps := [(p1, bs1), (p2, bs2), (p3, bs3)]) (Statics := Statics)
        hc hstk hstk64 hparse_ok hin3
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, w, *]) (by simp only [arm64_norm, w, *])
        (by simp only [arm64_norm, w, *]) (by simp only [arm64_norm, w, *]; exact hi32_or_lo32 p')
        hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hnext)
    dsimp only [w, callHeap, argvAtP]
    rw [cStrAt_split p3 bs3, hfsp, stackAt_split_ge fsp hext_le hsub64]
    have hown := ownedBytes_exact A hbs3_pos hbs3_le hp'_ne
    have h32 := cells32_64_to_memRegion_32 (fsp + 0x1b8#64) 0#32 0#32
      (BitVec.ofNat 64 bs3.length) p' devw
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32 ⊢
    refine Entails.trans (Entails.of_eq (show
      (p' ↦ₛ bs3) ∗ (p3 ↦ₛ bs3) ∗ stackAt fsp extHookStack ∗
        (((fsp + 0x1b8#64) ↦₃₂ 0#32) ∗ ((fsp + 0x1bc#64) ↦₃₂ 0#32) ∗
          ((fsp + 0x1c0#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗ ((fsp + 0x1c8#64) ↦₆₄ p') ∗
          ((fsp + 0x1d0#64) ↦₆₄ devw) ∗ A.live p' bs3.length 1 ∗
          addrWords A peer g.name.cap g.name.ptr (BitVec.ofNat 64 peer.name.length) devw ∗
          argsBuf A vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
          ((s0.readReg64 .x1) ↦₆₄ p0) ∗ cStrAt p0 (bytesOfString "libsignal-cli") ∗
          ((s0.readReg64 .x1 + 8#64) ↦₆₄ p1) ∗ cStrAt p1 bs1 ∗
          ((s0.readReg64 .x1 + 16#64) ↦₆₄ p2) ∗ cStrAt p2 bs2 ∗
          ((s0.readReg64 .x1 + 24#64) ↦₆₄ p3) ∗
          ((p3 + BitVec.ofNat 64 bs3.length) ↦₈ 0#8) ∗
          ((s0.readReg64 .x1 + 32#64) ↦₆₄ 0#64) ∗
          mainSaved s0 ∗
          ((fsp + 0x40#64) ↦₆₄ devw) ∗ ((fsp + 0x48#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
          ((fsp + 0x58#64) ↦₆₄ g.name.ptr) ∗ m2LocalsRest fsp ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - extHookStack) ∗ A.pool ∗ Statics) =
      (((fsp + 0x1b8#64) ↦₃₂ 0#32) ∗ ((fsp + 0x1bc#64) ↦₃₂ 0#32) ∗
        ((fsp + 0x1c0#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗ ((fsp + 0x1c8#64) ↦₆₄ p') ∗
        ((fsp + 0x1d0#64) ↦₆₄ devw)) ∗
      (A.live p' bs3.length 1 ∗ (p' ↦ₛ bs3)) ∗
      (argsBuf A vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        addrWords A peer g.name.cap g.name.ptr (BitVec.ofNat 64 peer.name.length) devw ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        ((s0.readReg64 .x1) ↦₆₄ p0) ∗ cStrAt p0 (bytesOfString "libsignal-cli") ∗
        ((s0.readReg64 .x1 + 8#64) ↦₆₄ p1) ∗ cStrAt p1 bs1 ∗
        ((s0.readReg64 .x1 + 16#64) ↦₆₄ p2) ∗ cStrAt p2 bs2 ∗
        ((s0.readReg64 .x1 + 24#64) ↦₆₄ p3) ∗
        ((p3 ↦ₛ bs3) ∗ ((p3 + BitVec.ofNat 64 bs3.length) ↦₈ 0#8)) ∗
        ((s0.readReg64 .x1 + 32#64) ↦₆₄ 0#64) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ devw) ∗ ((fsp + 0x48#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        ((fsp + 0x58#64) ↦₆₄ g.name.ptr) ∗ m2LocalsRest fsp ∗
        (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - extHookStack) ∗ stackAt fsp extHookStack) ∗ A.pool ∗ Statics)
      by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono h32 (sepConj_mono_left hown)) (Entails.of_eq (by ac_rfl))

end CryptoVerification.SignalSession.Cli.MainHops.Proofs

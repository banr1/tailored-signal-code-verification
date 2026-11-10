/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymA
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.MainCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStores
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Pure

/-!
# Relocatable Drop Glue Proofs for `Stores` and `IdentityFiles`

Proves `[LibsignalPlacement]` drop contracts for `IdentityFiles` (block `549`) and `Stores`
(block `550`), and transfers `cliDropStores_placed_ok` to caller blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617 instIsLsBlockProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunProofs.Helpers

/-- Relocatable `[LibsignalPlacement]` specification for `drop_glue::<Stores>` (block `550`). -/
def dropStoresSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) :
    Spec DropStoresGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropStoresSpec A stk)

/-- Relocatable `[LibsignalPlacement]` specification for `drop_glue::<IdentityFiles>` (block `549`). -/
def dropDirPairSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) :
    Spec DropDirPairGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropDirPairSpec A stk)

section DropStoresPlacedHelpers

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] exists_two_pow_one exists_two_pow_eight
attribute [local wp_norm, local arm64_norm]
  sub_32_of_add_32 sub_24_of_add_32 sub_8_of_add_32
  add_32_sub_32 add_32_sub_32_assoc add_32_sub_24 add_32_sub_24_assoc
  add_32_sub_8 add_32_sub_8_assoc
  add_32_neg_32 add_32_neg_32_assoc add_32_neg_24 add_32_neg_24_assoc
  add_32_neg_8 add_32_neg_8_assoc add_one_sub_one
attribute [local simp, local wp_norm, local arm64_norm]
  reg_x0_eq reg_x1_eq reg_x2_eq reg_x19_eq reg_x20_eq reg_x21_eq reg_x22_eq
  reg_x23_eq reg_x24_eq reg_x25_eq reg_x26_eq reg_x27_eq reg_x28_eq
  reg_fp_eq reg_lr_eq

private theorem seq_cleanX_placed [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P P_mid : SepProp}
    {Q : State → Prop} {post : State → SepProp → Prop}
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post := by
  refine LibsignalPublicApi.StoreKit.sepWP_seq_lscro hcrl (SepWP.mono h1 ?_)
  intro sm Pm hpc hrun ⟨hent, hQ⟩ hcrl_m
  exact SepWP.weaken_pre hent (h2 sm hpc hrun hcrl_m hQ)

set_option hygiene false in
local macro "prove_dir_loop_placed" bodyId:ident loopId:ident
    blkProgId:ident blkPlId:ident blkLibId:ident
    bLoopIdx:num bCondIdx:num blDeallocIdx:num bExitIdx:num : command => `(
  set_option maxHeartbeats 1600000 in
  private theorem $bodyId [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
      (hdealloc : subroutine_ok ($blkProgId H) (lsρ lsRustDeallocSymCli)
        (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack)))
      (s0 : State) (fsp p0 ptr : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
      ∀ (cur cnt : BitVec 64) (e : List (BitVec 8) × List (BitVec 8))
        (s : State) (Frame : SepProp),
        s.pc = ($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b.cond" $bCondIdx + 4#64) →
        s.status = .Running →
        LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
        Saved48Preserved s0 s fsp →
        s.readReg64 (Reg.gpr 19#5) = p0 →
        s.readReg64 (Reg.gpr 20#5) = ptr →
        s.readReg64 (Reg.gpr 21#5) = cnt →
        s.readReg64 (Reg.gpr 22#5) = cur + 32#64 →
        SepWP ($blkProgId H)
          (($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b" $bLoopIdx + 4#64))
          s
          (dirEntryAt A e cur ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 48 ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 (Reg.gpr 19#5) = p0 ∧
            sm.readReg64 (Reg.gpr 20#5) = ptr ∧
            sm.readReg64 (Reg.gpr 21#5) = cnt ∧
            sm.readReg64 (Reg.gpr 22#5) = cur + 32#64) := by
    dsimp only [$blkProgId:ident, ite_true, withLsRoCl, rustDeallocExternSpecWithStack, LayoutOk]
      at hdealloc ⊢
    intro cur cnt e s Frame hpc hrun hcrl hpres hx19 hx20 hx21 hx22
    rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
    refine SepWP.weaken_pre (sepConj_mono_left (dirEntryAt_expose A e cur)) ?_
    wp_pull_exists
    rename_i nc np bc bp
    refine seq_cleanX_placed
      (mid := ($blkPlId).base + (words_insn_off% ($blkLibId).text.code "bl" $blDeallocIdx + 4#64))
      (P_mid := (entryHeadersAt cur nc np bc bp ∗ vecPinDeallocX A bc bp) ∗
        A.pool ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr ∧
        sm.readReg64 (Reg.gpr 21#5) = cnt ∧ sm.readReg64 (Reg.gpr 22#5) = cur + 32#64)
      hcrl ?_ ?_
    · nth_rw 1 [show vecPinDeallocX A nc np =
          if (nc == 0#64) = true then emp
          else ⌜0 < nc.toNat ∧ nc.toNat < 2 ^ 63⌝ ∗ A.live np nc.toNat 1 ∗ memRegion np nc.toNat
          from rfl]
      dsimp only [entryHeadersAt]
      by_cases hnc : (nc == 0#64) = true <;>
        simp only [hnc, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        try wp_done
      · refine SepWP.weaken_pre (Entails.of_eq (show _ =
          ⌜0 < nc.toNat ∧ nc.toNat < 2 ^ 63⌝ ∗
            ((cur ↦₆₄ nc) ∗ ((cur + 8#64) ↦₆₄ np) ∗ memRegion (cur + 16#64) 8 ∗
              ((cur + 24#64) ↦₆₄ bc) ∗ ((cur + 32#64) ↦₆₄ bp) ∗ memRegion (cur + 40#64) 8 ∗
              A.live np nc.toNat 1 ∗ memRegion np nc.toNat ∗ vecPinDeallocX A bc bp ∗
              A.pool ∗ stackAt fsp extHookStack ∗ Frame) by ac_rfl)) ?_
        refine SepWP.pure_elim ?_
        rintro ⟨hpos, hlt⟩
        apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        rintro ⟨hcl_c1, hro_c1⟩
        wp_call hdealloc (np, nc.toNat, 1)
        try rw [hsp]
        try wp_done
    · intro s1 hpc1 hrun1 hcrl1
        ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩,
          hx19_1, hx20_1, hx21_1, hx22_1⟩
      have hstep2 : SepWP ($blkProgId H)
          (($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b" $bLoopIdx + 4#64)) s1
          ((entryHeadersAt cur nc np bc bp ∗ vecPinDeallocX A bc bp) ∗
            A.pool ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ entryHeadersAt cur nc np bc bp ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 (Reg.gpr 19#5) = p0 ∧
            sm.readReg64 (Reg.gpr 20#5) = ptr ∧
            sm.readReg64 (Reg.gpr 21#5) = cnt ∧
            sm.readReg64 (Reg.gpr 22#5) = cur + 32#64) := by
        dsimp only [$blkProgId:ident, ite_true, entryHeadersAt, vecPinDeallocX]
        by_cases hbc : (bc == 0#64) = true <;>
          simp only [hbc, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          try wp_done
        · refine SepWP.weaken_pre (Entails.of_eq (show _ =
            ⌜0 < bc.toNat ∧ bc.toNat < 2 ^ 63⌝ ∗
              ((cur ↦₆₄ nc) ∗ ((cur + 8#64) ↦₆₄ np) ∗ memRegion (cur + 16#64) 8 ∗
                ((cur + 24#64) ↦₆₄ bc) ∗ ((cur + 32#64) ↦₆₄ bp) ∗ memRegion (cur + 40#64) 8 ∗
                A.live bp bc.toNat 1 ∗ memRegion bp bc.toNat ∗
                A.pool ∗ stackAt fsp extHookStack ∗ Frame) by ac_rfl)) ?_
          refine SepWP.pure_elim ?_
          rintro ⟨hpos, hlt⟩
          apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl1
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl_c2, hro_c2⟩
          wp_call hdealloc (bp, bc.toNat, 1)
          try wp_steps
          try rw [hsp_1]
          try wp_done
      exact SepWP.mono hstep2 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (entryHeadersAt_entails_memRegion_48 cur nc np bc bp)),
          h.2⟩)

  set_option maxHeartbeats 1600000 in
  private theorem $loopId [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
      (hdealloc : subroutine_ok ($blkProgId H) (lsρ lsRustDeallocSymCli)
        (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack)))
      (s0 : State) (fsp p0 ptr : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
      ∀ (rest : List (List (BitVec 8) × List (BitVec 8))) (cur : BitVec 64)
        (s : State) (Frame : SepProp),
        rest ≠ [] →
        rest.length * 48 < 2 ^ 63 →
        s.pc = ($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b.cond" $bCondIdx + 4#64) →
        s.status = .Running →
        LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
        Saved48Preserved s0 s fsp →
        s.readReg64 (Reg.gpr 19#5) = p0 →
        s.readReg64 (Reg.gpr 20#5) = ptr →
        s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 rest.length →
        s.readReg64 (Reg.gpr 22#5) = cur + 32#64 →
        SepWP ($blkProgId H)
          (($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b" $bExitIdx + 4#64))
          s
          (arrayAt (dirEntryAt A) 48 cur rest ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur (rest.length * 48) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 (Reg.gpr 19#5) = p0 ∧
            sm.readReg64 (Reg.gpr 20#5) = ptr) := by
    have hbody := @$bodyId _ A H hdealloc s0 fsp p0 ptr hfsp_align
    dsimp only [$blkProgId:ident, ite_true, BitVec.ofNat_eq_ofNat] at hbody ⊢
    intro rest
    induction rest with
    | nil =>
      intro _ _ _ hne
      exact absurd rfl hne
    | cons hd tl ih =>
      intro cur s Frame _ hlen hpc hrun hcrl hpres hx19 hx20 hx21 hx22
      rw [show arrayAt (dirEntryAt A) 48 cur (hd :: tl) =
            dirEntryAt A hd cur ∗ arrayAt (dirEntryAt A) 48 (cur + 48#64) tl from rfl,
          sep_pull_entry]
      refine seq_cleanX_placed
        (mid := ($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b" $bLoopIdx + 4#64))
        (P_mid := memRegion cur 48 ∗ A.pool ∗ stackAt fsp extHookStack ∗
          (arrayAt (dirEntryAt A) 48 (cur + 48#64) tl ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr ∧
          sm.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (hd :: tl).length ∧
          sm.readReg64 (Reg.gpr 22#5) = cur + 32#64)
        hcrl
        (hbody cur (BitVec.ofNat 64 (hd :: tl).length) hd s
          (arrayAt (dirEntryAt A) 48 (cur + 48#64) tl ∗ Frame)
          hpc hrun hcrl hpres hx19 hx20 hx21 hx22) ?_
      intro s4 hpc4 hrun4 hcrl4 ⟨hpres4, hx19_4, hx20_4, hx21_4, hx22_4⟩
      cases tl with
      | nil =>
        rcases hpres4 with ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
        simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
          BitVec.ofNat_eq_ofNat, arrayAt, emp_sepConj] at hx21_4 ⊢
        wp_steps
        try wp_done
      | cons hd2 tl2 =>
        have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
        have htl_len := tail_len_mul_48_lt hlen
        rw [show (hd :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
            ofNat_succ_eq_add_one] at hx21_4
        have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
        refine seq_cleanX_placed
          (mid := ($blkPlId).base + (words_insn_off% ($blkLibId).text.code "b.cond" $bCondIdx + 4#64))
          (P_mid := arrayAt (dirEntryAt A) 48 (cur + 48#64) (hd2 :: tl2) ∗
            A.pool ∗ stackAt fsp extHookStack ∗ (memRegion cur 48 ∗ Frame))
          (Q := fun sm => Saved48Preserved s0 sm fsp ∧
            sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr ∧
            sm.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (hd2 :: tl2).length ∧
            sm.readReg64 (Reg.gpr 22#5) = (cur + 48#64) + 32#64)
          hcrl4 ?_ ?_
        · rcases hpres4 with ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          rw [sep_push_entry]
          wp_steps
          rw [add_32_add_48]
          try wp_done
        · intro s5 hpc5 hrun5 hcrl5 ⟨hpres5, hx19_5, hx20_5, hx21_5, hx22_5⟩
          refine SepWP.mono
            (ih (cur + 48#64) s5 (memRegion cur 48 ∗ Frame)
              htl_ne htl_len hpc5 hrun5 hcrl5 hpres5 hx19_5 hx20_5 hx21_5 hx22_5) ?_
          intro sf Pf _ _ h
          refine ⟨Entails.trans h.1 ?_, h.2⟩
          have hsplit := cons_len_mul_48 hd (hd2 :: tl2)
          have hbound : 48 + (hd2 :: tl2).length * 48 ≤ 2 ^ 64 := by
            rw [hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
          rw [sep_rejoin_entries, ← hsplit,
              ProofLib.memRegion_split cur 48 ((hd2 :: tl2).length * 48) hbound]
          exact Entails.refl _
)

prove_dir_loop_placed id_loop0_body_placed id_loop0_placed
  lsProg_549 blkPl_549 blkLib_549 0 0 0 1

prove_dir_loop_placed id_loop1_body_placed id_loop1_placed
  lsProg_549 blkPl_549 blkLib_549 2 1 3 3

prove_dir_loop_placed stores_loop0_body_placed stores_loop0_placed
  lsProg_550 blkPl_550 blkLib_550 0 0 1 1

prove_dir_loop_placed stores_loop1_body_placed stores_loop1_placed
  lsProg_550 blkPl_550 blkLib_550 2 1 5 3

prove_dir_loop_placed stores_loop2_body_placed stores_loop2_placed
  lsProg_550 blkPl_550 blkLib_550 4 2 8 5

prove_dir_loop_placed stores_loop3_body_placed stores_loop3_placed
  lsProg_550 blkPl_550 blkLib_550 6 3 11 7

set_option hygiene false in
local macro "prove_dir_nontail_placed" blockId:ident loopId:ident
    off:term:max off8:term:max off16:term:max off24:term:max
    blStartIdx:num bCondIdx:num bExitIdx:num blEndIdx:num : command => `(
  set_option maxHeartbeats 1600000 in
  private theorem $blockId [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
      (hdealloc : subroutine_ok (lsProg_550 H) (lsρ lsRustDeallocSymCli)
        (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack)))
      (s0 : State) (fsp p0 : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
      ∀ (xs : List (List (BitVec 8) × List (BitVec 8))) (s : State) (Frame : SepProp),
        s.pc = (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" $blStartIdx + 4#64) →
        s.status = .Running →
        LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
        Saved48Preserved s0 s fsp →
        s.readReg64 (Reg.gpr 19#5) = p0 →
        SepWP (lsProg_550 H)
          ((blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" $blEndIdx + 4#64))
          s
          (dirRawAt A (p0 + $off) xs ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion (p0 + $off) 40 ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 (Reg.gpr 19#5) = p0) := by
    have hloop := @$loopId _ A H hdealloc
    dsimp only [lsProg_550, ite_true, withLsRoCl, rustDeallocExternSpecWithStack, LayoutOk,
      BitVec.ofNat_eq_ofNat] at hdealloc hloop ⊢
    intro xs s Frame hpc hrun hcrl hpres hx19
    rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
    have ho8 : (p0 + $off) + 8#64 = p0 + $off8 := by bv_omega
    have ho16 : (p0 + $off) + 16#64 = p0 + $off16 := by bv_omega
    have ho24 : (p0 + $off) + 24#64 = p0 + $off24 := by bv_omega
    refine SepWP.weaken_pre
      (sepConj_mono_left
        (dirRawAt_expose_off A p0 $off $off8 $off16 $off24 ho8 ho16 ho24 xs)) ?_
    wp_pull_exists
    rename_i cap ptr
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ xs.length * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((p0 + $off) ↦₆₄ cap) ∗
          ((p0 + $off8) ↦₆₄ ptr) ∗
          ((p0 + $off16) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
          arrayAt (dirEntryAt A) 48 ptr xs ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 48) 8 ∗
             memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48)) ∗
          memRegion (p0 + $off24) 16 ∗
          A.pool ∗ stackAt fsp extHookStack ∗ Frame) by ac_rfl)) ?_
    refine SepWP.pure_elim ?_
    rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
    refine seq_cleanX_placed
      (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "b" $bExitIdx + 4#64))
      (P_mid :=
        ((p0 + $off) ↦₆₄ cap) ∗
        ((p0 + $off8) ↦₆₄ ptr) ∗
        ((p0 + $off16) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        memRegion ptr (xs.length * 48) ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48)) ∗
        memRegion (p0 + $off24) 16 ∗
        A.pool ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := fun sm =>
        Saved48Preserved s0 sm fsp ∧
        sm.readReg64 (Reg.gpr 19#5) = p0 ∧
        sm.readReg64 (Reg.gpr 20#5) = ptr)
      hcrl ?_ ?_
    · cases xs with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
        wp_steps
        try wp_done
      | cons hd tl =>
        have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) (by omega)
        apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro
          (mid := (blkPl_550).base +
            (words_insn_off% (blkLib_550).text.code "b.cond" $bCondIdx + 4#64)) hcrl
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_p
        have hpre_eq :
            (((p0 + $off) ↦₆₄ cap) ∗
              ((p0 + $off8) ↦₆₄ ptr) ∗
              ((p0 + $off16) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
              arrayAt (dirEntryAt A) 48 ptr (hd :: tl) ∗
              (if cap = 0 then emp
               else A.live ptr (cap.toNat * 48) 8 ∗
                 memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 48))
                   ((cap.toNat - (hd :: tl).length) * 48)) ∗
              memRegion (p0 + $off24) 16 ∗
              A.pool ∗ stackAt fsp extHookStack ∗ Frame) =
            (arrayAt (dirEntryAt A) 48 ptr (hd :: tl) ∗
              A.pool ∗ stackAt fsp extHookStack ∗
              (((p0 + $off) ↦₆₄ cap) ∗
                ((p0 + $off8) ↦₆₄ ptr) ∗
                ((p0 + $off16) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                (if cap = 0 then emp
                 else A.live ptr (cap.toNat * 48) 8 ∗
                   memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 48))
                     ((cap.toNat - (hd :: tl).length) * 48)) ∗
                memRegion (p0 + $off24) 16 ∗ Frame)) := by
          ac_rfl
        rw [hpre_eq]
        refine SepWP.mono
          (hloop s0 fsp p0 ptr hfsp_align (hd :: tl) ptr _ _
            (List.cons_ne_nil _ _) hlen_lt (by wp_norm_goal) (by wp_norm_lhs) hcrl_p
            ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
            hx19 rfl rfl rfl) ?_
        intro sm Pm _ _ h
        exact ⟨Entails.trans h.1 (Entails.of_eq (by ac_rfl)), h.2⟩
    · intro sm hpcm hrunm hcrlm
        ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx19_m, hx20_m⟩
      refine SepWP.weaken_pre
        (post_dir_loop_weaken_off A p0 $off $off8 $off16 $off24
          cap ptr ho8 ho16 ho24 xs.length hlen_le hcap_lt _) ?_
      by_cases hcap : (cap == 0#64) = true <;>
        simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre
          (weaken_perm
            (word_and_32_rest_entails_40_off p0 $off $off8 cap ho8
              (A.pool ∗ stackAt fsp extHookStack ∗ Frame))
            (by ac_rfl)) ?_
        try wp_done
      · have hcap_pos := pos_of_beq_zero_false hcap
        have hsz_pos : 0 < cap.toNat * 48 := Nat.mul_pos hcap_pos (by decide)
        apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrlm
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        rintro ⟨hcl_cm, hro_cm⟩
        rw [mul_48_reg hcap_lt]
        wp_call hdealloc (ptr, cap.toNat * 48, 8)
        refine SepWP.weaken_pre
          (weaken_perm
            (word_and_32_rest_entails_40_off p0 $off $off8 cap ho8
              (A.pool ∗ stackAt fsp extHookStack ∗ Frame))
            (by rw [hsp_m]; ac_rfl)) ?_
        try wp_done
)

prove_dir_nontail_placed stores_dir_signed_placed stores_loop0_placed (80#64) (88#64) (96#64) (104#64) 0 0 1 3
prove_dir_nontail_placed stores_dir_onetime_placed stores_loop1_placed (200#64) (208#64) (216#64) (224#64) 4 1 3 7
prove_dir_nontail_placed stores_dir_sessions_placed stores_loop2_placed (240#64) (248#64) (256#64) (264#64) 7 2 5 10

private def dropDirPairRawSpecPlaced [LibsignalPlacement] (A : RustAlloc) :
    Spec DropDirPairGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl {
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.a⌝ ∗ dirRawAt A x.a x.d0.changed ∗
        dirRawAt A (x.a + 40#64) x.d1.changed ∗ A.pool ∗ stackAt s.sp idExactStk
    post := fun x s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 80 ∗ A.pool ∗ stackAt s0.sp idExactStk
  }

private def dropStoresRawSpecPlaced [LibsignalPlacement] (A : RustAlloc) :
    Spec DropStoresGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl {
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.a⌝ ∗
        dirAt A x.a x.g.identity.own ∗ dirAt A (x.a + 40#64) x.g.identity.peers ∗
        dirRawAt A (x.a + 80#64) x.g.signed.changed ∗
        dirAt A (x.a + 120#64) x.g.kyber.oneTime ∗ dirAt A (x.a + 160#64) x.g.kyber.lastResort ∗
        dirRawAt A (x.a + 200#64) x.g.oneTime.changed ∗
        dirRawAt A (x.a + 240#64) x.g.sessions.changed ∗
        dirRawAt A (x.a + 280#64) x.g.pub.changed ∗
        A.pool ∗ stackAt s.sp storesExactStk
    post := fun x s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 320 ∗ A.pool ∗ stackAt s0.sp storesExactStk
  }

set_option maxHeartbeats 1600000 in
private theorem cliDropIdentityFiles_placed_ok_exact [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_549 H) (blkPl_549).base (dropDirPairRawSpecPlaced A) := by
  unfold dropDirPairRawSpecPlaced LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  have hdealloc_raw : subroutine_ok (lsProg_549 H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
    @ls_subroutine_ok_rocl_of_block _ _ (lsProg_549 H) (lsProg_617 H) 549 617 H
      (instIsLsBlockProg_549 H) (instIsLsBlockProg_617 H) (lsρ lsRustDeallocSymCli) _
      hA.dealloc _ _ _ _ (by decide) (by decide) (by decide)
  clear hA
  have hdealloc := hdealloc_raw
  have hloop0 := id_loop0_placed hdealloc_raw
  have hloop1 := id_loop1_placed hdealloc_raw
  dsimp only [lsProg_549, ite_true, withLsRoCl, rustDeallocExternSpecWithStack, LayoutOk,
    BitVec.ofNat_eq_ofNat] at hdealloc hloop0 hloop1 ⊢
  wp_init x s0
  obtain ⟨a, d0, d1⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  subst ‹s0.readReg64 _ = a›
  set p0 := s0.readReg64 (Reg.gpr 0#5)
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_id_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre (sepConj_mono_left (dirRawAt_expose A p0 d0.changed)) ?_
  wp_pull_exists
  rename_i cap0 ptr0
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜d0.changed.length ≤ cap0.toNat ∧ cap0.toNat * 48 < 2 ^ 63 ∧
      d0.changed.length * 48 < 2 ^ 63 ∧ ptr0 ≠ 0⌝ ∗
    ((p0 ↦₆₄ cap0) ∗ ((p0 + 8#64) ↦₆₄ ptr0) ∗
      ((p0 + 16#64) ↦₆₄ BitVec.ofNat 64 d0.changed.length) ∗
      arrayAt (dirEntryAt A) 48 ptr0 d0.changed ∗
      (if cap0 = 0 then emp
       else A.live ptr0 (cap0.toNat * 48) 8 ∗
         memRegion (ptr0 + BitVec.ofNat 64 (d0.changed.length * 48))
           ((cap0.toNat - d0.changed.length) * 48)) ∗
      memRegion (p0 + 24#64) 16 ∗ dirRawAt A (p0 + 40#64) d1.changed ∗
      A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
      ((s0.sp - 48#64) ↦₆₄ _) ∗ ((s0.sp - 40#64) ↦₆₄ _) ∗
      ((s0.sp - 32#64) ↦₆₄ _) ∗ ((s0.sp - 24#64) ↦₆₄ _) ∗
      ((s0.sp - 16#64) ↦₆₄ _) ∗ ((s0.sp - 8#64) ↦₆₄ _)) by ac_rfl)) ?_
  refine SepWP.pure_elim ?_
  rintro ⟨hlen0_le, hcap0_lt, hlen0_lt, hptr0_ne⟩
  refine seq_cleanX_placed
    (mid := (blkPl_549).base + (words_insn_off% (blkLib_549).text.code "bl" 2 + 4#64))
    (P_mid := memRegion p0 40 ∗ dirRawAt A (p0 + 40#64) d1.changed ∗
      A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
    hcrl0 ?_ ?_
  · refine seq_cleanX_placed
      (mid := (blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b" 1 + 4#64))
      (P_mid := (p0 ↦₆₄ cap0) ∗ ((p0 + 8#64) ↦₆₄ ptr0) ∗
        ((p0 + 16#64) ↦₆₄ BitVec.ofNat 64 d0.changed.length) ∗
        memRegion ptr0 (d0.changed.length * 48) ∗
        (if cap0 = 0 then emp
         else A.live ptr0 (cap0.toNat * 48) 8 ∗
           memRegion (ptr0 + BitVec.ofNat 64 (d0.changed.length * 48))
             ((cap0.toNat - d0.changed.length) * 48)) ∗
        memRegion (p0 + 24#64) 16 ∗ dirRawAt A (p0 + 40#64) d1.changed ∗
        A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr0)
      hcrl0 ?_ ?_
    · cases hc0 : d0.changed with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
        wp_steps
        try wp_done
      | cons hd tl =>
        rw [hc0] at hlen0_lt
        have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) (by omega)
        apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro
          (mid := (blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b.cond" 0 + 4#64))
          hcrl0
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_p
        have hpre_eq :
            ((p0 ↦₆₄ cap0) ∗ ((p0 + 8#64) ↦₆₄ ptr0) ∗
              ((p0 + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
              arrayAt (dirEntryAt A) 48 ptr0 (hd :: tl) ∗
              (if cap0 = 0 then emp
               else A.live ptr0 (cap0.toNat * 48) 8 ∗
                 memRegion (ptr0 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                   ((cap0.toNat - (hd :: tl).length) * 48)) ∗
              memRegion (p0 + 24#64) 16 ∗ dirRawAt A (p0 + 40#64) d1.changed ∗
              A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
            (arrayAt (dirEntryAt A) 48 ptr0 (hd :: tl) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
              ((p0 ↦₆₄ cap0) ∗ ((p0 + 8#64) ↦₆₄ ptr0) ∗
                ((p0 + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                (if cap0 = 0 then emp
                 else A.live ptr0 (cap0.toNat * 48) 8 ∗
                   memRegion (ptr0 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                     ((cap0.toNat - (hd :: tl).length) * 48)) ∗
                memRegion (p0 + 24#64) 16 ∗ dirRawAt A (p0 + 40#64) d1.changed ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) := by
          ac_rfl
        rw [hpre_eq]
        refine SepWP.mono
          (hloop0 s0 (s0.sp - 48#64) p0 ptr0 hfsp_align (hd :: tl) ptr0 _ _
            (List.cons_ne_nil _ _) hlen0_lt (by wp_norm_goal) (by wp_norm_lhs) hcrl_p
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            rfl rfl rfl rfl) ?_
        intro sm Pm _ _ hh
        exact ⟨Entails.trans hh.1 (Entails.of_eq (by ac_rfl)), hh.2⟩
    · intro sm hpcm hrunm hcrlm
        ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx19_m, hx20_m⟩
      refine SepWP.weaken_pre
        (post_dir_loop_weaken A p0 cap0 ptr0 d0.changed.length hlen0_le hcap0_lt _) ?_
      by_cases hcap0 : (cap0 == 0#64) = true <;>
        simp only [hcap0, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre
          (weaken_perm
            (word_and_32_rest_entails_40 p0 cap0
              (dirRawAt A (p0 + 40#64) d1.changed ∗ A.pool ∗
                stackAt (s0.sp - 48#64) extHookStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
            (by ac_rfl)) ?_
        try wp_done
      · have hcap_pos := pos_of_beq_zero_false hcap0
        have hsz_pos : 0 < cap0.toNat * 48 := Nat.mul_pos hcap_pos (by decide)
        apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrlm
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        rintro ⟨hcl_cm, hro_cm⟩
        rw [mul_48_reg hcap0_lt]
        wp_call hdealloc (ptr0, cap0.toNat * 48, 8)
        refine SepWP.weaken_pre
          (weaken_perm
            (word_and_32_rest_entails_40 p0 cap0
              (dirRawAt A (p0 + 40#64) d1.changed ∗ A.pool ∗
                stackAt (s0.sp - 48#64) extHookStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
            (by try rw [hsp_m]; ac_rfl)) ?_
        try wp_done
  ·
    intro s1 hpc1 hrun1 hcrl1
      ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    have ho1_8 : (p0 + 40#64) + 8#64 = p0 + 48#64 := by bv_omega
    have ho1_16 : (p0 + 40#64) + 16#64 = p0 + 56#64 := by bv_omega
    have ho1_24 : (p0 + 40#64) + 24#64 = p0 + 64#64 := by bv_omega
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_left
        (dirRawAt_expose_off A p0 40#64 48#64 56#64 64#64
          ho1_8 ho1_16 ho1_24 d1.changed))) ?_
    wp_pull_exists
    rename_i cap1 ptr1
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜d1.changed.length ≤ cap1.toNat ∧ cap1.toNat * 48 < 2 ^ 63 ∧
        d1.changed.length * 48 < 2 ^ 63 ∧ ptr1 ≠ 0⌝ ∗
      (((p0 + 40#64) ↦₆₄ cap1) ∗ ((p0 + 48#64) ↦₆₄ ptr1) ∗
        ((p0 + 56#64) ↦₆₄ BitVec.ofNat 64 d1.changed.length) ∗
        arrayAt (dirEntryAt A) 48 ptr1 d1.changed ∗
        (if cap1 = 0 then emp
         else A.live ptr1 (cap1.toNat * 48) 8 ∗
           memRegion (ptr1 + BitVec.ofNat 64 (d1.changed.length * 48))
             ((cap1.toNat - d1.changed.length) * 48)) ∗
        memRegion (p0 + 64#64) 16 ∗ memRegion p0 40 ∗
        A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
    refine SepWP.pure_elim ?_
    rintro ⟨hlen1_le, hcap1_lt, hlen1_lt, hptr1_ne⟩
    refine seq_cleanX_placed
      (mid := (blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b" 3 + 4#64))
      (P_mid := ((p0 + 40#64) ↦₆₄ cap1) ∗ ((p0 + 48#64) ↦₆₄ ptr1) ∗
        ((p0 + 56#64) ↦₆₄ BitVec.ofNat 64 d1.changed.length) ∗
        memRegion ptr1 (d1.changed.length * 48) ∗
        (if cap1 = 0 then emp
         else A.live ptr1 (cap1.toNat * 48) 8 ∗
           memRegion (ptr1 + BitVec.ofNat 64 (d1.changed.length * 48))
             ((cap1.toNat - d1.changed.length) * 48)) ∗
        memRegion (p0 + 64#64) 16 ∗ memRegion p0 40 ∗
        A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr1)
      hcrl1 ?_ ?_
    · cases hc1 : d1.changed with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
        wp_steps
        try wp_done
      | cons hd tl =>
        rw [hc1] at hlen1_lt
        have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) (by omega)
        apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro
          (mid := (blkPl_549).base + (words_insn_off% (blkLib_549).text.code "b.cond" 1 + 4#64))
          hcrl1
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_p
        have hpre_eq :
            (((p0 + 40#64) ↦₆₄ cap1) ∗ ((p0 + 48#64) ↦₆₄ ptr1) ∗
              ((p0 + 56#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
              arrayAt (dirEntryAt A) 48 ptr1 (hd :: tl) ∗
              (if cap1 = 0 then emp
               else A.live ptr1 (cap1.toNat * 48) 8 ∗
                 memRegion (ptr1 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                   ((cap1.toNat - (hd :: tl).length) * 48)) ∗
              memRegion (p0 + 64#64) 16 ∗ memRegion p0 40 ∗
              A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
            (arrayAt (dirEntryAt A) 48 ptr1 (hd :: tl) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
              (((p0 + 40#64) ↦₆₄ cap1) ∗ ((p0 + 48#64) ↦₆₄ ptr1) ∗
                ((p0 + 56#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                (if cap1 = 0 then emp
                 else A.live ptr1 (cap1.toNat * 48) 8 ∗
                   memRegion (ptr1 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                     ((cap1.toNat - (hd :: tl).length) * 48)) ∗
                memRegion (p0 + 64#64) 16 ∗ memRegion p0 40 ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) := by
          ac_rfl
        rw [hpre_eq]
        refine SepWP.mono
          (hloop1 s0 (s0.sp - 48#64) p0 ptr1 hfsp_align (hd :: tl) ptr1 _ _
            (List.cons_ne_nil _ _) hlen1_lt (by wp_norm_goal) (by wp_norm_lhs) hcrl_p
            ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
            hx19_1 rfl rfl rfl) ?_
        intro sm Pm _ _ hh
        exact ⟨Entails.trans hh.1 (Entails.of_eq (by ac_rfl)), hh.2⟩
    · intro sm hpcm hrunm hcrlm
        ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx19_m, hx20_m⟩
      refine SepWP.weaken_pre
        (post_dir_loop_weaken_off A p0 40#64 48#64 56#64 64#64 cap1 ptr1
          ho1_8 ho1_16 ho1_24 d1.changed.length hlen1_le hcap1_lt _) ?_
      by_cases hcap1 : (cap1 == 0#64) = true <;>
        simp only [hcap1, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre
          (weaken_perm
            (id_cap0_ret_weaken p0 cap1 A.pool s0.sp
              (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
              (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
              (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
            (by ac_rfl)) ?_
        try wp_done
      · have hcap_pos := pos_of_beq_zero_false hcap1
        have hsz_pos : 0 < cap1.toNat * 48 := Nat.mul_pos hcap_pos (by decide)
        apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrlm
        wp_steps
        refine SepWP.weaken_pre
          (weaken_perm
            (id_tail_dealloc_pre_weaken p0 cap1
              (A.live ptr1 (cap1.toNat * 48) 8 ∗ memRegion ptr1 (cap1.toNat * 48))
              A.pool s0.sp
              (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
              (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
              (s0.readReg64 (Reg.gpr 20#5))
              (s0.readReg64 (Reg.gpr 19#5)))
            (by ac_rfl)) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        rintro ⟨hcl_ct, hro_ct⟩
        rw [mul_48_reg hcap1_lt]
        wp_call hdealloc (ptr1, cap1.toNat * 48, 8)
        refine SepWP.weaken_pre (weaken_perm (id_tail_dealloc_post p0 A.pool s0.sp) (by ac_rfl)) ?_
        try wp_done

end DropStoresPlacedHelpers

/-- Proves `dropDirPairSpecPlaced` for `drop_glue::<IdentityFiles>` (block `549`) at stack budgets `48 + extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem cliDropIdentityFiles_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    (stk : Nat) (hstk : 48 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_549 H) (blkPl_549).base (dropDirPairSpecPlaced A stk) := by
  have hexact := cliDropIdentityFiles_placed_ok_exact hA
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - idExactStk)
  have hsplit : stackAt s0.sp stk = stackAt s0.sp idExactStk ∗ F :=
    Put.Helpers.stackAt_sub_split hstk hstk64 s0.sp
  have hpre1 : s0.mem ⊨
      (dropDirPairRawSpecPlaced A).pre x s0 ∗
        ((roPathAt x.d0.path ∗ roPathAt x.d1.path) ∗ (F ∗ R)) := by
    simp only [dropDirPairSpecPlaced, dropDirPairRawSpecPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropDirPairSpec] at hpre ⊢
    rw [hsplit] at hpre
    refine Satisfies.mono ?_ hpre
    refine Entails.trans (Entails.of_eq (show _ =
        (dirAt A x.a x.d0 ∗ dirAt A (x.a + 0x28#64) x.d1) ∗
          (⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            ⌜s0.readReg64 .x0 = x.a⌝ ∗
            A.pool ∗ stackAt s0.sp idExactStk ∗ F ∗ R) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (id_entry_raw_ro A x.a x.d0 x.d1)) ?_
    exact Entails.of_eq (by ac_rfl)
  have hpre2 : s0.mem ⊨ (dropDirPairRawSpecPlaced A).pre x s0 ∗ (F ∗ R) :=
    Satisfies.drop_mid hpre1
  refine reaches_pc_mono
    (subroutine_ok_apply_full hexact x (F ∗ R) hpc hrun hpre2 hsp) ?_
  intro sf _ _ ⟨hpost, hcc⟩
  refine ⟨?_, hcc⟩
  simp only [dropDirPairSpecPlaced, dropDirPairRawSpecPlaced,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropDirPairSpec] at hpost ⊢
  rw [hsplit]
  convert hpost using 1
  ac_rfl

section DropStoresMainPlaced

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] exists_two_pow_one exists_two_pow_eight
attribute [local wp_norm, local arm64_norm]
  sub_32_of_add_32 sub_24_of_add_32 sub_8_of_add_32
  add_32_sub_32 add_32_sub_32_assoc add_32_sub_24 add_32_sub_24_assoc
  add_32_sub_8 add_32_sub_8_assoc
  add_32_neg_32 add_32_neg_32_assoc add_32_neg_24 add_32_neg_24_assoc
  add_32_neg_8 add_32_neg_8_assoc add_one_sub_one
attribute [local simp, local wp_norm, local arm64_norm]
  reg_x0_eq reg_x1_eq reg_x2_eq reg_x19_eq reg_x20_eq reg_x21_eq reg_x22_eq
  reg_x23_eq reg_x24_eq reg_x25_eq reg_x26_eq reg_x27_eq reg_x28_eq
  reg_fp_eq reg_lr_eq

set_option maxHeartbeats 1600000 in
private theorem cliDropStores_placed_ok_exact [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_550 H) (blkPl_550).base (dropStoresRawSpecPlaced A) := by
  unfold dropStoresRawSpecPlaced LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  have hdealloc_raw : subroutine_ok (lsProg_550 H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
    @ls_subroutine_ok_rocl_of_block _ _ (lsProg_550 H) (lsProg_617 H) 550 617 H
      (instIsLsBlockProg_550 H) (instIsLsBlockProg_617 H) (lsρ lsRustDeallocSymCli) _
      hA.dealloc _ _ _ _ (by decide) (by decide) (by decide)
  have hid : subroutine_ok (lsProg_550 H) (lsmpl.base 549)
      (withLsRoCl lsmpl (dropDirPairSpec A idExactStk)) :=
    @ls_subroutine_ok_rocl_of_block _ _ (lsProg_550 H) (lsProg_549 H) 550 549 H
      (instIsLsBlockProg_550 H) (instIsLsBlockProg_549 H) (lsmpl.base 549)
      (dropDirPairSpec A idExactStk)
      (cliDropIdentityFiles_placed_ok hA idExactStk (le_refl _) (by decide))
      _ _ _ _ (by decide) (by decide) (by decide)
  clear hA
  have hdealloc := hdealloc_raw
  have hsigned := stores_dir_signed_placed hdealloc_raw
  have honetime := stores_dir_onetime_placed hdealloc_raw
  have hsessions := stores_dir_sessions_placed hdealloc_raw
  have hloop3 := stores_loop3_placed hdealloc_raw
  dsimp only [lsProg_550, ite_true, withLsRoCl, rustDeallocExternSpecWithStack, LayoutOk,
    dropDirPairSpec, BitVec.ofNat_eq_ofNat]
    at hdealloc hid hsigned honetime hsessions hloop3 ⊢
  wp_init x s0
  obtain ⟨a, g⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  subst ‹s0.readReg64 _ = a›
  set p0 := s0.readReg64 (Reg.gpr 0#5)
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_stores_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine seq_cleanX_placed
    (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" 0 + 4#64))
    (P_mid := memRegion p0 80 ∗
      dirRawAt A (p0 + 80#64) g.signed.changed ∗
      dirAt A (p0 + 120#64) g.kyber.oneTime ∗ dirAt A (p0 + 160#64) g.kyber.lastResort ∗
      dirRawAt A (p0 + 200#64) g.oneTime.changed ∗
      dirRawAt A (p0 + 240#64) g.sessions.changed ∗
      dirRawAt A (p0 + 280#64) g.pub.changed ∗
      A.pool ∗ stackAt (s0.sp - 48#64) idExactStk ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
    hcrl0 ?_ ?_
  · apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsmpl.base 549) hcrl0
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hcl_c0, hro_c0⟩
    wp_call hid (DropDirPairGhost.mk p0 g.identity.own g.identity.peers)
    try wp_done
  ·
    intro s1 hpc1 hrun1 hcrl1 hq1
    rw [stackAt_id_split_bottom (s0.sp - 48#64)]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      dirRawAt A (p0 + 80#64) g.signed.changed ∗ A.pool ∗
      stackAt (s0.sp - 48#64) extHookStack ∗
      (memRegion p0 80 ∗
        dirAt A (p0 + 120#64) g.kyber.oneTime ∗ dirAt A (p0 + 160#64) g.kyber.lastResort ∗
        dirRawAt A (p0 + 200#64) g.oneTime.changed ∗
        dirRawAt A (p0 + 240#64) g.sessions.changed ∗
        dirRawAt A (p0 + 280#64) g.pub.changed ∗
        memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
    refine seq_cleanX_placed
      (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" 3 + 4#64))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
      hcrl1
      (hsigned s0 (s0.sp - 48#64) p0 hfsp_align g.signed.changed s1 _
        hpc1 hrun1 hcrl1 hq1.1 hq1.2) ?_
    intro s2 hpc2 hrun2 hcrl2
      ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
    have hp0_160 : p0 + 160#64 = (p0 + 120#64) + 40#64 := by bv_omega
    rw [hp0_160]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      dirAt A (p0 + 120#64) g.kyber.oneTime ∗
      dirAt A ((p0 + 120#64) + 40#64) g.kyber.lastResort ∗
      A.pool ∗ (memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗ stackAt (s0.sp - 48#64) extHookStack) ∗
      (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗
        dirRawAt A (p0 + 200#64) g.oneTime.changed ∗
        dirRawAt A (p0 + 240#64) g.sessions.changed ∗
        dirRawAt A (p0 + 280#64) g.pub.changed ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
    rw [← stackAt_id_split_bottom (s0.sp - 48#64)]
    refine seq_cleanX_placed
      (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" 4 + 4#64))
      (P_mid := memRegion (p0 + 120#64) 80 ∗ A.pool ∗ stackAt (s0.sp - 48#64) idExactStk ∗
        (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗
          dirRawAt A (p0 + 200#64) g.oneTime.changed ∗
          dirRawAt A (p0 + 240#64) g.sessions.changed ∗
          dirRawAt A (p0 + 280#64) g.pub.changed ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
      hcrl2 ?_ ?_
    · apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsmpl.base 549) hcrl2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hcl_c2, hro_c2⟩
      wp_call hid (DropDirPairGhost.mk (p0 + 120#64) g.kyber.oneTime g.kyber.lastResort)
      try rw [hsp_2]
      try wp_done
    ·
      intro s3 hpc3 hrun3 hcrl3 hq3
      rw [stackAt_id_split_bottom (s0.sp - 48#64)]
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        dirRawAt A (p0 + 200#64) g.oneTime.changed ∗ A.pool ∗
        stackAt (s0.sp - 48#64) extHookStack ∗
        (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
          dirRawAt A (p0 + 240#64) g.sessions.changed ∗
          dirRawAt A (p0 + 280#64) g.pub.changed ∗
          memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
      refine seq_cleanX_placed
        (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" 7 + 4#64))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
        hcrl3
        (honetime s0 (s0.sp - 48#64) p0 hfsp_align g.oneTime.changed s3 _
          hpc3 hrun3 hcrl3 hq3.1 hq3.2) ?_
      intro s4 hpc4 hrun4 hcrl4 hq4
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        dirRawAt A (p0 + 240#64) g.sessions.changed ∗ A.pool ∗
        stackAt (s0.sp - 48#64) extHookStack ∗
        (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
          memRegion (p0 + 200#64) 40 ∗
          dirRawAt A (p0 + 280#64) g.pub.changed ∗
          memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
      refine seq_cleanX_placed
        (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" 10 + 4#64))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
        hcrl4
        (hsessions s0 (s0.sp - 48#64) p0 hfsp_align g.sessions.changed s4 _
          hpc4 hrun4 hcrl4 hq4.1 hq4.2) ?_
      intro s5 hpc5 hrun5 hcrl5
        ⟨⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
      have ho7_8 : (p0 + 280#64) + 8#64 = p0 + 288#64 := by bv_omega
      have ho7_16 : (p0 + 280#64) + 16#64 = p0 + 296#64 := by bv_omega
      have ho7_24 : (p0 + 280#64) + 24#64 = p0 + 304#64 := by bv_omega
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        dirRawAt A (p0 + 280#64) g.pub.changed ∗
        (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
          memRegion (p0 + 200#64) 40 ∗ memRegion (p0 + 240#64) 40 ∗
          A.pool ∗ memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
          stackAt (s0.sp - 48#64) extHookStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
      refine SepWP.weaken_pre
        (sepConj_mono_left
          (dirRawAt_expose_off A p0 280#64 288#64 296#64 304#64
            ho7_8 ho7_16 ho7_24 g.pub.changed)) ?_
      wp_pull_exists
      rename_i cap7 ptr7
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        ⌜g.pub.changed.length ≤ cap7.toNat ∧ cap7.toNat * 48 < 2 ^ 63 ∧
          g.pub.changed.length * 48 < 2 ^ 63 ∧ ptr7 ≠ 0⌝ ∗
        (((p0 + 280#64) ↦₆₄ cap7) ∗ ((p0 + 288#64) ↦₆₄ ptr7) ∗
          ((p0 + 296#64) ↦₆₄ BitVec.ofNat 64 g.pub.changed.length) ∗
          arrayAt (dirEntryAt A) 48 ptr7 g.pub.changed ∗
          (if cap7 = 0 then emp
           else A.live ptr7 (cap7.toNat * 48) 8 ∗
             memRegion (ptr7 + BitVec.ofNat 64 (g.pub.changed.length * 48))
               ((cap7.toNat - g.pub.changed.length) * 48)) ∗
          memRegion (p0 + 304#64) 16 ∗
          (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
            memRegion (p0 + 200#64) 40 ∗ memRegion (p0 + 240#64) 40 ∗
            A.pool ∗ memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
            stackAt (s0.sp - 48#64) extHookStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) by ac_rfl)) ?_
      refine SepWP.pure_elim ?_
      rintro ⟨hlen7_le, hcap7_lt, hlen7_lt, hptr7_ne⟩
      refine seq_cleanX_placed
        (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "b" 7 + 4#64))
        (P_mid := ((p0 + 280#64) ↦₆₄ cap7) ∗ ((p0 + 288#64) ↦₆₄ ptr7) ∗
          ((p0 + 296#64) ↦₆₄ BitVec.ofNat 64 g.pub.changed.length) ∗
          memRegion ptr7 (g.pub.changed.length * 48) ∗
          (if cap7 = 0 then emp
           else A.live ptr7 (cap7.toNat * 48) 8 ∗
             memRegion (ptr7 + BitVec.ofNat 64 (g.pub.changed.length * 48))
               ((cap7.toNat - g.pub.changed.length) * 48)) ∗
          memRegion (p0 + 304#64) 16 ∗
          (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
            memRegion (p0 + 200#64) 40 ∗ memRegion (p0 + 240#64) 40 ∗
            A.pool ∗ memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
            stackAt (s0.sp - 48#64) extHookStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr7)
        hcrl5 ?_ ?_
      · cases hc7 : g.pub.changed with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
          wp_steps
          try wp_done
        | cons hd tl =>
          rw [hc7] at hlen7_lt
          have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) (by omega)
          apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro
            (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "b.cond" 3 + 4#64))
            hcrl5
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcrl_p
          have hpre_eq :
              (((p0 + 280#64) ↦₆₄ cap7) ∗ ((p0 + 288#64) ↦₆₄ ptr7) ∗
                ((p0 + 296#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                arrayAt (dirEntryAt A) 48 ptr7 (hd :: tl) ∗
                (if cap7 = 0 then emp
                 else A.live ptr7 (cap7.toNat * 48) 8 ∗
                   memRegion (ptr7 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                     ((cap7.toNat - (hd :: tl).length) * 48)) ∗
                memRegion (p0 + 304#64) 16 ∗
                (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
                  memRegion (p0 + 200#64) 40 ∗ memRegion (p0 + 240#64) 40 ∗
                  A.pool ∗ memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
                  stackAt (s0.sp - 48#64) extHookStack ∗
                  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
                  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
                  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
                  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) =
              (arrayAt (dirEntryAt A) 48 ptr7 (hd :: tl) ∗
                A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
                (((p0 + 280#64) ↦₆₄ cap7) ∗ ((p0 + 288#64) ↦₆₄ ptr7) ∗
                  ((p0 + 296#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                  (if cap7 = 0 then emp
                   else A.live ptr7 (cap7.toNat * 48) 8 ∗
                     memRegion (ptr7 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                       ((cap7.toNat - (hd :: tl).length) * 48)) ∗
                  memRegion (p0 + 304#64) 16 ∗
                  (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
                    memRegion (p0 + 200#64) 40 ∗ memRegion (p0 + 240#64) 40 ∗
                    memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
                    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
                    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
                    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
                    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))) := by
            ac_rfl
          rw [hpre_eq]
          refine SepWP.mono
            (hloop3 s0 (s0.sp - 48#64) p0 ptr7 hfsp_align (hd :: tl) ptr7 _ _
              (List.cons_ne_nil _ _) hlen7_lt (by wp_norm_goal) (by wp_norm_lhs) hcrl_p
              ⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩
              hx19_5 rfl rfl rfl) ?_
          intro sm Pm _ _ hh
          exact ⟨Entails.trans hh.1 (Entails.of_eq (by ac_rfl)), hh.2⟩
      · intro sm hpcm hrunm hcrlm
          ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
            hx19_m, hx20_m⟩
        refine SepWP.weaken_pre
          (post_dir_loop_weaken_off A p0 280#64 288#64 296#64 304#64 cap7 ptr7
            ho7_8 ho7_16 ho7_24 g.pub.changed.length hlen7_le hcap7_lt _) ?_
        by_cases hcap7 : (cap7 == 0#64) = true <;>
          simp only [hcap7, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre
            (weaken_perm
              (stores_cap0_ret_weaken p0 cap7 A.pool s0.sp
                (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
                (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
                (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
              (by ac_rfl)) ?_
          try wp_done
        · have hcap_pos := pos_of_beq_zero_false hcap7
          have hsz_pos : 0 < cap7.toNat * 48 := Nat.mul_pos hcap_pos (by decide)
          apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrlm
          wp_steps
          refine SepWP.weaken_pre
            (weaken_perm
              (stores_tail_dealloc_pre_weaken p0 cap7
                (A.live ptr7 (cap7.toNat * 48) 8 ∗ memRegion ptr7 (cap7.toNat * 48))
                A.pool s0.sp
                (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
                (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
                (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
              (by ac_rfl)) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨hcl_ct, hro_ct⟩
          rw [mul_48_reg hcap7_lt]
          wp_call hdealloc (ptr7, cap7.toNat * 48, 8)
          refine SepWP.weaken_pre
            (weaken_perm (stores_tail_dealloc_post p0 A.pool s0.sp) (by ac_rfl)) ?_
          try wp_done

end DropStoresMainPlaced

/-- Proves `dropStoresSpecPlaced` for `drop_glue::<Stores>` (block `550`) at stack budgets `96 + extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem cliDropStores_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_550 H) (blkPl_550).base (dropStoresSpecPlaced A stk) := by
  have hexact := cliDropStores_placed_ok_exact hA
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - storesExactStk)
  have hsplit : stackAt s0.sp stk = stackAt s0.sp storesExactStk ∗ F :=
    Put.Helpers.stackAt_sub_split hstk hstk64 s0.sp
  have hpre1 : s0.mem ⊨
      (dropStoresRawSpecPlaced A).pre x s0 ∗
        ((roPathAt x.g.signed.path ∗ roPathAt x.g.oneTime.path ∗
          roPathAt x.g.sessions.path ∗ roPathAt x.g.pub.path) ∗ (F ∗ R)) := by
    simp only [dropStoresSpecPlaced, dropStoresRawSpecPlaced,
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropStoresSpec] at hpre ⊢
    rw [hsplit] at hpre
    refine Satisfies.mono ?_ hpre
    refine Entails.trans (Entails.of_eq (show _ =
        storesAt A x.a x.g ∗
          (⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            ⌜s0.readReg64 .x0 = x.a⌝ ∗
            A.pool ∗ stackAt s0.sp storesExactStk ∗ F ∗ R) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (stores_entry_raw_ro A x.a x.g)) ?_
    exact Entails.of_eq (by ac_rfl)
  have hpre2 : s0.mem ⊨ (dropStoresRawSpecPlaced A).pre x s0 ∗ (F ∗ R) :=
    Satisfies.drop_mid hpre1
  refine reaches_pc_mono
    (subroutine_ok_apply_full hexact x (F ∗ R) hpc hrun hpre2 hsp) ?_
  intro sf _ _ ⟨hpost, hcc⟩
  refine ⟨?_, hcc⟩
  simp only [dropStoresSpecPlaced, dropStoresRawSpecPlaced,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dropStoresSpec] at hpost ⊢
  rw [hsplit]
  convert hpost using 1
  ac_rfl

/-- Transfers `cliDropStores_placed_ok` to any caller block `i < 619`. -/
theorem cliDropStores_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A H)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_550).base (dropStoresSpecPlaced A stk) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_550 H) i 550 H
    hcaller (instIsLsBlockProg_550 H) (blkPl_550).base _
    (cliDropStores_placed_ok hA stk hstk hstk64)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

end CryptoVerification.SignalSession.Cli.RunProofs

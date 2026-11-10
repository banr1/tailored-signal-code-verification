/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSessionStructure3Placed
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Common
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Contract for `drop_glue::<SessionStructure> [local#4]` (Block `512`)

Proves `drop_session_structure4_placed_ok` (`dropSessionStructureLocal2Spec A`) on Block `512`,
calling Block `513` (`drop_glue::<Chain>`) and `__rust_dealloc`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSession
open DropsCommon DropGlueFacts
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.Cli.LibsignalE2E.Pqxdh.Reloc

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_ss4_split (sp : BitVec 64) :
    stackAt sp dropSessionStructureLocal2Stack =
      stackAt (sp - 48#64) dropChainStack ∗ cells (sp - 48#64) 6 := by
  exact ProofLib.stackAt_split_cells sp dropChainStack 6 (by decide)

private theorem stackAt_dropChain_split_alloc_ss4 (fsp : BitVec 64) :
    stackAt fsp dropChainStack =
      memRegion (fsp - 4144#64) 48 ∗ stackAt fsp allocHookStack := by
  rw [show dropChainStack = allocHookStack + 48 from rfl,
      DropsCommon.stackAt_split_bottom' fsp allocHookStack 48 (by decide)]

private theorem tail_stack_ss4_96_from_bottom (sp : BitVec 64) :
    memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack =
      stackAt (sp - 48#64) dropChainStack ∗ cells (sp - 48#64) 6 := by
  rw [← DropsCommon.stackAt_split_bottom' sp allocHookStack 96 (by decide),
      show allocHookStack + 96 = dropSessionStructureLocal2Stack from rfl,
      ← stackAt_ss4_split sp]

private theorem tail_dealloc_ss4_pre_weaken (ss cap ptr : BitVec 64)
    (live rest pool : SepProp) (sp : BitVec 64) (fp lr x22 x21 x20 x19 : BitVec 64) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
      live ∗ rest ∗ pool ∗
      stackAt (sp - 48#64) dropChainStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (ss + 120#64) 24 ∗ rest ∗ pool ∗
      memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack ∗ live := by
  have h1 : ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ⊢
      memRegion (ss + 120#64) 24 := by
    have ha1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
    have ha2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
    rw [← ha1, ← ha2]
    exact DropsCommon.header_cells_entails_memRegion_24 (ss + 120#64) cap ptr
  have h2 :
      stackAt (sp - 48#64) dropChainStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
      memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack := by
    rw [tail_stack_ss4_96_from_bottom sp]
    cells_unfold
    refine Entails.sepExists_right fp (Entails.sepExists_right lr
      (Entails.sepExists_right x22 (Entails.sepExists_right x21
        (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))))
  have hreord :
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
        live ∗ rest ∗ pool ∗
        stackAt (sp - 48#64) dropChainStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8) ∗
        (live ∗ rest ∗ pool ∗
         (stackAt (sp - 48#64) dropChainStack ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by ac_rfl)

private theorem vecAt_expose_loop_at_72_ss4 {α : Type} (A : RustAlloc) (sz align : Nat)
    (elem : α → BitVec 64 → SepProp) (ss cap ptr : BitVec 64) (xs : List α) :
    vecAt A sz align elem (ss + 72#64) cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * sz < 2 ^ 63 ∧ xs.length * sz < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((ss + 72#64) ↦₆₄ cap) ∗ ((ss + 80#64) ↦₆₄ ptr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        arrayAt elem sz ptr xs ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * sz) align ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * sz)) ((cap.toNat - xs.length) * sz))) := by
  unfold vecAt vecHeader
  refine Entails.trans (sepConj_mono_right (vecBuf_expose_arrayAt A sz align elem cap ptr xs)) ?_
  have h1 : (ss + 72#64) + 8#64 = ss + 80#64 := by bv_omega
  have h2 : (ss + 72#64) + 16#64 = ss + 88#64 := by bv_omega
  rw [h1, h2]
  exact Entails.of_eq (by ac_rfl)

private theorem seq_clean_lscl_ss4 [LibsignalPlacement] {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post := by
  apply sepWP_seq_lscl hcl (mid := mid)
  refine SepWP.mono h1 ?_
  rintro sm Pm hpcm hrunm ⟨hent, hQ⟩ hclm
  exact SepWP.weaken_pre hent (h2 sm hpcm hrunm hclm hQ)

private theorem drop_ss4_placed_first3 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (blkPl_512).base + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP ((blkPC_512).rebase (blkPl_512).base H)
        ((blkPl_512).base + 80#64)
        s
        ((ssFirst3HeadersAt_shared_lb ss G ∗
          DropsCommon.vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          DropsCommon.vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          DropsCommon.vecPinDealloc A G.root) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustDeallocSpec] at hdealloc
  intro G s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine DropsCommon.SepWP.seq_clean (mid := (blkPl_512).base + 40#64) (P_mid :=
    (ssFirst3HeadersAt_shared_lb ss G ∗
      DropsCommon.vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      DropsCommon.vecPinDealloc A G.root) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssFirst3HeadersAt_shared_lb, DropsCommon.vecPinDealloc]
    by_cases hcap : (G.localIk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply
      refine DropsCommon.SepWP.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine DropsCommon.SepWP.seq_clean (mid := (blkPl_512).base + 60#64) (P_mid :=
      (ssFirst3HeadersAt_shared_lb ss G ∗ DropsCommon.vecPinDealloc A G.root) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssFirst3HeadersAt_shared_lb, DropsCommon.vecPinDealloc]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply
        refine DropsCommon.SepWP.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_512).rebase (blkPl_512).base H) ((blkPl_512).base + 80#64) s2
          ((ssFirst3HeadersAt_shared_lb ss G ∗ DropsCommon.vecPinDealloc A G.root) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt_shared_lb ss G ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssFirst3HeadersAt_shared_lb, DropsCommon.vecPinDealloc]
        by_cases hcap : (G.root.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp]
        · wp_steps; wp_done
        · wp_steps; wp_apply
          refine DropsCommon.SepWP.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (DropsCommon.ssFirst3HeadersAt_entails_memRegions ss G)), h.2⟩)

private theorem drop_ss4_placed_sender [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdrop_chain : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsmpl.base 513) (withLsCodeLoaded lsmpl (dropProtoChainSpec A)))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_512).base + 80#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP ((blkPC_512).rebase (blkPl_512).base H)
        ((blkPl_512).base + 100#64)
        s
        (optSenderChainAt A (ss + 144#64) senderG senderSt ∗
          A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [withLsCodeLoaded, dropProtoChainSpec] at hdrop_chain
  intro senderG senderSt s Frame hpc hrun hcl hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      unfold optSenderChainAt
      have hstep : SepWP ((blkPC_512).rebase (blkPl_512).base H) ((blkPl_512).base + 100#64) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
            A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
              A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [noneCap]
        wp_steps; wp_done
      exact SepWP.mono hstep (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (sender_none_entails_memRegion_104_shared_lb (ss + 144#64))), h.2⟩)
    | some _ => simp only [optSenderChainAt]; exact DropsCommon.SepWP.false_elim_left
  | some sg =>
    cases senderSt with
    | none => simp only [optSenderChainAt]; exact DropsCommon.SepWP.false_elim_left
    | some sc =>
      refine SepWP.weaken_pre (sepConj_mono_left (optSenderChainAt_some_expose_shared_lb A (ss + 144#64) sg sc)) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨hpk, hlen, hcap_lt, hptr_ne, hcmn⟩
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      wp_steps
      refine SepWP.weaken_pre
        (sepConj_mono_left (chainAt_of_exposed_sender_shared_lb A (ss + 144#64) sg sc hpk hlen hcap_lt hptr_ne)) ?_
      wp_apply
      refine DropsCommon.SepWP.align_pre (by rw [hsp]) ?_
      wp_done

private theorem drop_ss4_placed_receiver_loop [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdrop_chain : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsmpl.base 513) (withLsCodeLoaded lsmpl (dropChainSpec A)))
    (s0 : State) (fsp ss ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (blkPl_512).base + 112#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      s.readReg64 .x20 = ptr →
      s.readReg64 .x21 = cur →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP ((blkPC_512).rebase (blkPl_512).base H)
        ((blkPl_512).base + 132#64)
        s
        (arrayAt (chainAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss ∧
          sm.readReg64 .x20 = ptr) := by
  simp only [withLsCodeLoaded, dropChainSpec] at hdrop_chain
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur s Frame _ hlen hpc hrun hcl hpres hx19 hx20 hx21 hx22
    rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
    rw [show arrayAt (chainAt A) 104 cur ((g, c) :: tl) =
          chainAt A (g, c) cur ∗ arrayAt (chainAt A) 104 (cur + 104#64) tl from rfl,
        DropGlueFacts.sep_pull_body]
    refine seq_clean_lscl_ss4 hcl (mid := (blkPl_512).base + 120#64)
      (P_mid := memRegion cur 104 ∗ A.pool ∗ stackAt fsp dropChainStack ∗
        (arrayAt (chainAt A) 104 (cur + 104#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ss ∧ sm.readReg64 .x20 = ptr ∧
        sm.readReg64 .x21 = cur ∧ sm.readReg64 .x22 = BitVec.ofNat 64 ((g, c) :: tl).length)
      ?_ ?_
    · wp_steps; wp_apply
      refine DropsCommon.SepWP.align_pre (by rw [hsp]) ?_
      wp_done
    · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
      cases tl with
      | nil =>
        simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
          arrayAt, emp_sepConj] at hx22_1 ⊢
        wp_steps; wp_done
      | cons hd2 tl2 =>
        have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
        have htl_len := DropGlueFacts.tail_len_mul_lt hlen
        rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
            DropGlueFacts.ofNat_succ_eq_add_one] at hx22_1
        have hne1 := DropGlueFacts.ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
        wp_steps
        have hpc_next : (BitVec.ofNat 64 (hd2 :: tl2).length + 1#64 != 1#64) = true := by
          rw [bne_iff_ne]; intro h; exact hne1 (beq_iff_eq.mpr h)
        rw [DropGlueFacts.sep_push_body]
        refine SepWP.mono
          (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
            htl_ne htl_len (by simp only [State.setPC, hpc_next, ↓reduceIte]) (by assumption) hcl1
            ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
            hx19_1 hx20_1 rfl rfl) ?_
        intro sf Pf _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        have hsplit := DropGlueFacts.cons_len_mul (g, c) (hd2 :: tl2) 104
        have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [DropGlueFacts.sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
        exact Entails.refl _

private theorem drop_ss4_placed_tail3 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (blkPl_512).base + 160#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP ((blkPC_512).rebase (blkPl_512).base H)
        ((blkPl_512).base + 228#64)
        s
        ((ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
          DropsCommon.sgnPinDealloc A pCap pPtr ∗
          DropsCommon.sgnPinDealloc A kCap kPtr ∗
          DropsCommon.vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustDeallocSpec] at hdealloc
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine DropsCommon.SepWP.seq_clean (mid := (blkPl_512).base + 184#64) (P_mid :=
    (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
      DropsCommon.sgnPinDealloc A kCap kPtr ∗
      DropsCommon.vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssTail3HeadersAt_shared_lb, DropsCommon.sgnPinDealloc, DropsCommon.vecPinDealloc]
    by_cases hcap : pCap.slt 1#64 = true <;>
      simp only [hcap, ↓reduceIte, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply
      refine DropsCommon.SepWP.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine DropsCommon.SepWP.seq_clean (mid := (blkPl_512).base + 208#64) (P_mid :=
      (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
        DropsCommon.vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssTail3HeadersAt_shared_lb, DropsCommon.sgnPinDealloc, DropsCommon.vecPinDealloc]
      by_cases hcap : kCap.slt 1#64 = true <;>
        simp only [hcap, ↓reduceIte, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply
        refine DropsCommon.SepWP.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_512).rebase (blkPl_512).base H) ((blkPl_512).base + 228#64) s2
          ((ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
            DropsCommon.vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssTail3HeadersAt_shared_lb, DropsCommon.vecPinDealloc]
        by_cases hcap : (G.alice.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp]
        · wp_steps; wp_done
        · wp_steps; wp_apply
          refine DropsCommon.SepWP.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (DropsCommon.ssTail3HeadersAt_entails_memRegions ss pCap pPtr kCap kPtr G)), h.2⟩)

/-- Block `512` (`core::ptr::drop_glue::<SessionStructure> [local#4]`) meets
`withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)` under `[LibsignalPlacement]`,
given `subroutine_ok` for `__rust_dealloc` and Block `513` (`dropProtoChainSpec` and `dropChainSpec`). -/
theorem drop_session_structure4_placed_ok_of_dealloc_and_chain [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hdrop_proto_chain_raw : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsmpl.base 513) (withLsCodeLoaded lsmpl (dropProtoChainSpec A)))
    (hdrop_chain_raw : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H)
      (lsmpl.base 513) (withLsCodeLoaded lsmpl (dropChainSpec A))) :
    subroutine_ok ((blkPC_512).rebase (blkPl_512).base H) (blkPl_512).base
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) := by
  simp only [withLsCodeLoaded, dropSessionStructureLocal2Spec]
  wp_init x s0
  obtain ⟨ss, G, st⟩ := x
  dsimp only at *
  have hdealloc := hdealloc_raw
  have hfirst3 := drop_ss4_placed_first3 hdealloc_raw
  have hsender := drop_ss4_placed_sender hdrop_proto_chain_raw
  have hloop := drop_ss4_placed_receiver_loop hdrop_chain_raw
  have htail3 := drop_ss4_placed_tail3 hdealloc_raw
  clear hdealloc_raw hdrop_chain_raw hdrop_proto_chain_raw
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst ss
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  rw [stackAt_ss4_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v0 v1 v2 v3 v4 v5
  refine drop6_strengthen_post_shared_lb (session_memRegions_entails_344_shared_lb (s0.readReg64 (Reg.gpr 0#5))) ?_
  refine SepWP.weaken_pre
    (sepConj_mono_left (DropsCommon.sessionStateAt_entails_dealloc A (s0.readReg64 (Reg.gpr 0#5)) G st)) ?_
  wp_pull_exists
  rename_i pCap pPtr kCap kPtr
  refine seq_clean_lscl_ss4 hcl0 (mid := (blkPl_512).base + 16#64)
    (P_mid :=
      (ssFirst3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G ∗
        DropsCommon.vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        DropsCommon.vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        DropsCommon.vecPinDealloc A G.root) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          DropsCommon.sgnPinDealloc A pCap pPtr ∗ DropsCommon.sgnPinDealloc A kCap kPtr ∗
          DropsCommon.vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ DropsCommon.vecPinDealloc A G.pq) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗ memRegion (s0.sp - 4192#64) 48 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropChain_split_alloc_ss4 (s0.sp - 48#64)]
    have hsp_sub : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
    rw [hsp_sub]
    wp_steps
    refine DropsCommon.SepWP.align_pre (by dsimp only [ssFirst3HeadersAt_shared_lb, ssTail3HeadersAt_shared_lb, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨hpres1, hx0_1⟩
    refine seq_clean_lscl_ss4 hcl1 (mid := (blkPl_512).base + 80#64)
      (P_mid :=
        optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
        (vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          DropsCommon.sgnPinDealloc A pCap pPtr ∗ DropsCommon.sgnPinDealloc A kCap kPtr ∗
          DropsCommon.vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ DropsCommon.vecPinDealloc A G.pq) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · refine SepWP.mono
        (hfirst3 s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G s1 _
          hpc1 hrun1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [stackAt_dropChain_split_alloc_ss4 (s0.sp - 48#64)]
      have hsp_sub1 : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
      rw [hsp_sub1]
      exact Entails.of_eq (by ac_rfl)
    · intro s2 hpc2 hrun2 hcl2 ⟨hpres2, hx19_2⟩
      refine seq_clean_lscl_ss4 hcl2 (mid := (blkPl_512).base + 100#64)
        (P_mid :=
          vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains) ∗
          (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
            DropsCommon.sgnPinDealloc A pCap pPtr ∗ DropsCommon.sgnPinDealloc A kCap kPtr ∗
            DropsCommon.vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
          (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ DropsCommon.vecPinDealloc A G.pq) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
          A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G.sender st.senderChain s2 _
            hpc2 hrun2 hcl2 hpres2 hx19_2) ?_
        intro sm Pm _ _ h
        exact ⟨Entails.trans h.1 (Entails.of_eq (by ac_rfl)), h.2⟩
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine SepWP.weaken_pre
          (sepConj_mono_left (vecAt_expose_loop_at_72_ss4 A 104 8 (chainAt A)
            (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains))) ?_
        rw [sepConj_assoc]
        refine SepWP.pure_elim ?_
        rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
        generalize G.chains.zip st.receiverChains = cs at hlen_le hlen_lt ⊢
        refine seq_clean_lscl_ss4 hcl3 (mid := (blkPl_512).base + 132#64)
          (P_mid :=
            ((s0.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ G.chainsCap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ G.chainsPtr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            memRegion G.chainsPtr (cs.length * 104) ∗
            (if G.chainsCap = 0 then emp
             else A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
               memRegion (G.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((G.chainsCap.toNat - cs.length) * 104)) ∗
            (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
              DropsCommon.sgnPinDealloc A pCap pPtr ∗ DropsCommon.sgnPinDealloc A kCap kPtr ∗
              DropsCommon.vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
            (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ DropsCommon.vecPinDealloc A G.pq) ∗
            (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
            A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
            sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5) ∧ sm.readReg64 .x20 = G.chainsPtr)
          ?_ ?_
        · cases cs with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
            wp_steps
            refine DropsCommon.SepWP.align_pre (by dsimp only [ssTail3HeadersAt_shared_lb]; ac_rfl) ?_
            wp_done
          | cons hd tl =>
            have hne0 := DropGlueFacts.ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
            wp_steps_lscl ((blkPl_512).base + 112#64)
            refine SepWP.weaken_pre (P' :=
              arrayAt (chainAt A) 104 G.chainsPtr (hd :: tl) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
              (((s0.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ G.chainsCap) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ G.chainsPtr) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                (if G.chainsCap = 0 then emp
                 else A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
                   memRegion (G.chainsPtr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((G.chainsCap.toNat - (hd :: tl).length) * 104)) ∗
                (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
                  DropsCommon.sgnPinDealloc A pCap pPtr ∗ DropsCommon.sgnPinDealloc A kCap kPtr ∗
                  DropsCommon.vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
                (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ DropsCommon.vecPinDealloc A G.pq) ∗
                (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (Entails.of_eq (by dsimp only [ssTail3HeadersAt_shared_lb]; ac_rfl)) ?_
            refine SepWP.mono
              (hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) G.chainsPtr hfsp_align
                (hd :: tl) G.chainsPtr _ _
                (List.cons_ne_nil _ _) hlen_lt rfl (by assumption) hcl3
                ⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩
                hx19_3 rfl rfl rfl) ?_
            intro sm Pm _ _ h
            exact ⟨Entails.trans h.1 (Entails.of_eq (by dsimp only [ssTail3HeadersAt_shared_lb]; ac_rfl)), h.2⟩
        · intro sm hpcm hrunm hclm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩, hx19_m, hx20_m⟩
          refine SepWP.weaken_pre
            (post_loop_weaken_at_72_shared_lb A (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr
              cs.length hlen_le hcap_lt _) ?_
          refine seq_clean_lscl_ss4 hclm (mid := (blkPl_512).base + 160#64)
            (P_mid :=
              (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
                DropsCommon.sgnPinDealloc A pCap pPtr ∗ DropsCommon.sgnPinDealloc A kCap kPtr ∗
                DropsCommon.vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              ((((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ DropsCommon.vecPinDealloc A G.pq) ∗
              (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗ memRegion (s0.sp - 4192#64) 48 ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
            ?_ ?_
          · rw [stackAt_dropChain_split_alloc_ss4 (s0.sp - 48#64)]
            have hsp_subm : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
            rw [hsp_subm]
            by_cases hcap : (G.chainsCap == 0#64) = true <;>
              simp only [hcap, ↓reduceIte, emp_sepConj]
            · wp_steps
              refine SepWP.weaken_pre
                (chains_header24_weaken_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr _) ?_
              refine DropsCommon.SepWP.align_pre (by dsimp only [ssTail3HeadersAt_shared_lb]; ac_rfl) ?_
              wp_done
            · wp_steps
              have hmul : 104#64 * G.chainsCap = BitVec.ofNat 64 (G.chainsCap.toNat * 104) := by bv_omega
              have hmul2 : G.chainsCap * 104#64 = BitVec.ofNat 64 (G.chainsCap.toNat * 104) := by bv_omega
              wp_apply
              refine SepWP.weaken_pre
                (sepConj_mono_right (sepConj_mono_right
                  (chains_header24_weaken_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr _))) ?_
              refine DropsCommon.SepWP.align_pre (by rw [hsp_m]; dsimp only [ssTail3HeadersAt_shared_lb]; ac_rfl) ?_
              wp_done
          · intro s4 hpc4 hrun4 hcl4 ⟨hpres4, hx19_4⟩
            refine seq_clean_lscl_ss4 hcl4 (mid := (blkPl_512).base + 228#64)
              (P_mid :=
                ((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ DropsCommon.vecPinDealloc A G.pq ∗
                (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 96#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 248#64) 48 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 296#64) 32 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
                A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
              (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
              ?_ ?_
            · refine SepWP.mono
                (htail3 s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align pCap pPtr kCap kPtr G s4 _
                  hpc4 hrun4 hpres4 hx19_4) ?_
              intro sm Pm _ _ h
              refine ⟨Entails.trans h.1 ?_, h.2⟩
              rw [stackAt_dropChain_split_alloc_ss4 (s0.sp - 48#64)]
              have hsp_sub4 : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
              rw [hsp_sub4]
              exact Entails.of_eq (by ac_rfl)
            · intro s5 hpc5 hrun5 _ ⟨⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
              dsimp only [DropsCommon.vecPinDealloc]
              by_cases hcap : (G.pq.cap == 0#64) = true <;>
                simp only [hcap, ↓reduceIte, emp_sepConj]
              · wp_steps
                refine SepWP.weaken_pre (pq_header24_weaken_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr _) ?_
                wp_done
              · wp_steps
                refine SepWP.weaken_pre
                  (tail_dealloc_ss4_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                    _ _ _ s0.sp _ _ _ _ _ _) ?_
                wp_apply
                refine SepWP.weaken_pre (P' :=
                  (memRegion (s0.readReg64 (Reg.gpr 0#5) + 120#64) 24 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 96#64) 24 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 248#64) 48 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 296#64) 32 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
                  A.pool ∗
                  (stackAt (s0.sp - 48#64) dropChainStack ∗ cells (s0.sp - 48#64) 6))
                  (by rw [← tail_stack_ss4_96_from_bottom s0.sp]; exact Entails.of_eq (by ac_rfl)) ?_
                cells_unfold
                wp_pull_exists
                wp_done

private theorem withLsCodeLoaded_of_raw [LibsignalPlacement] {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec) := by
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact h x R s0 hpc hrun hpre.2 hsp

/-- Block `512` (`core::ptr::drop_glue::<SessionStructure> [local#4]`) meets
`withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)` under `[LibsignalPlacement]`. -/
theorem drop_session_structure4_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_512).rebase (blkPl_512).base H) (blkPl_512).base
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) := by
  have hp : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H) (lsmpl.base 513)
      (withLsCodeLoaded lsmpl (dropProtoChainSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_512).rebase (blkPl_512).base H)
      (withLsCodeLoaded_of_raw (drop_proto_chain_placed_ok h_dealloc)) (by decide)
  have hc : subroutine_ok ((blkPC_512).rebase (blkPl_512).base H) (lsmpl.base 513)
      (withLsCodeLoaded lsmpl (dropChainSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_512).rebase (blkPl_512).base H)
      (withLsCodeLoaded_of_raw (drop_chain_placed_ok h_dealloc)) (by decide)
  exact drop_session_structure4_placed_ok_of_dealloc_and_chain
    (ls_hook_ok_rustDealloc h_dealloc) hp hc

/-- Caller-lifted `dropSessionStructureLocal2Spec A` (`withLsCodeLoaded`) at `lsmpl.base 512`. -/
theorem drop_session_structure4_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (drop_session_structure4_placed_ok h_dealloc) hi

/-- Caller-lifted `dropSessionStructureLocal2Spec A` (`withLsCl`) at `lsmpl.base 512`. -/
theorem drop_session_structure4_placed_cl_ok_at [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCl lsmpl (dropSessionStructureLocal2Spec A)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (drop_session_structure4_placed_ok h_dealloc) hi

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

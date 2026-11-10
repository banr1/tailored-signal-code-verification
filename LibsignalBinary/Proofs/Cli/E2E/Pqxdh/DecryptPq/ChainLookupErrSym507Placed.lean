/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2Placed
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSym

/-!
# Relocatable `ErrTail` Symbolic Execution for CLI `try_decrypt_with_state::<Coins>`

Relocatable `[LibsignalPlacement]` symbolic execution and tight-panic epilogue lemmas for the
shared `ErrTail` cleanup block of `try_decrypt_with_state::<signal_session_handshake::Coins>`
(Block `507`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet hiding memRegion_eight
open CryptoVerification.LibsignalTripleRatchet.Getters hiding drop_chain_placed_ok
open CryptoVerification.LibsignalTripleRatchet.Decrypt hiding
  ErrTailStatePlaced ErrTailStateXPlaced LoadRatchetStatePlaced FindChainStatePlaced
  DhStepStatePlaced ConsumeMsgKeyStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  VerifyMacStatePlaced AesDecryptStatePlaced ApplyRatchetStatePlaced
  ErrTailSeamPlaced S0SeamPlaced S1SeamPlaced S2SeamPlaced S3SeamPlaced S4SeamPlaced
  S5SeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup hiding arrayAt_nil arrayAt_cons
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt
open CryptoVerification.CliHandshake.TryDecPlaced

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem tryDecrypt_epilogue_394_507_wp_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (s0 s : State) (hpc : s.pc = retEpiloguePC_at (blkPl_508).base) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1504#64) (hs0_align : s0.spAligned = true)
    (_hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
        memRegion (s0.sp - 1504#64) 1408 ∗ tryDecryptSavedRegs s0.sp s0)
      (fun sf P_f => sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
        CalleeSavedPreserved s0 sf ∧ (P_f ⊢ stackAt s0.sp rootStack)) := by
  unfold tryDecryptSavedRegs
  dsimp only [retEpiloguePC_at] at hpc
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, ?_⟩
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]
  · exact tryDecryptStack_recombine s0.sp s0

theorem errTail_copy_spe_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {ret tag chainsPtr chainsLen : BitVec 64}
    {w0 w1 w2 w3 w4 r0 r1 r2 r3 r4 r5 t0 t1 t2 : BitVec 64}
    {s0 s : State}
    (hpc : s.pc = errTailPC_at (blkPl_508).base)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx26 : s.readReg64 .x26 = tag) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_508).base + 820#64) s
      (((sp + 64#64) ↦₆₄ chainsPtr) ∗ ((sp + 72#64) ↦₆₄ chainsLen) ∗
       ((sp + 320#64) ↦₆₄ t0) ∗ ((sp + 328#64) ↦₆₄ t1) ∗ ((sp + 336#64) ↦₆₄ t2) ∗
       words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5)
      (fun sf P =>
        P = (((sp + 64#64) ↦₆₄ chainsPtr) ∗ ((sp + 72#64) ↦₆₄ chainsLen) ∗
             ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗ ((sp + 336#64) ↦₆₄ w2) ∗
             words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x20 = chainsPtr ∧ sf.readReg64 .x21 = chainsLen) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errTailPC_at] at hpc
  unfold words5At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem errTail_drop_one_507_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {p chainsPtr rem : BitVec 64} (gc : ChainGhost × ReceiverChain) {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = errDropChainLoopPC_at (blkPl_508).base)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_508).base + 836#64) s
      (chainAt A gc p ∗ A.pool ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (memRegion p 104 ∗ A.pool ∗ stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p ∧ sf.readReg64 .x20 = chainsPtr ∧ sf.readReg64 .x21 = rem) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdrop := ls_subroutine_ok_of_block (callerProg := (blkPC_508).rebase (blkPl_508).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (CryptoVerification.Cli.LibsignalE2E.Pqxdh.Reloc.drop_chain_placed_ok hdealloc))
  rw [show CliHandshake.Placed.blkPl_513.base = lsmpl.base 513 from rfl] at hdrop
  simp only [withLsCodeLoaded, dropChainSpec] at hdrop
  dsimp only [errDropChainLoopPC_at] at hpc
  refine SepWP.rw_pre (by rw [← hsp]) ?_
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 513); wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
  wp_call hdrop ⟨p, gc⟩
  wp_finish
  refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  rw [hsp]

theorem errTail_drop_exit_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 836#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 1#64) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 848#64) s emp
      (fun sf P => P = emp ∧ tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps; wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm]⟩

theorem errTail_drop_cont_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {p chainsPtr rem : BitVec 64} {s0 s : State}
    (hne : (rem != 1#64) = true)
    (hpc : s.pc = (blkPl_508).base + 836#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) (errDropChainLoopPC_at (blkPl_508).base) s emp
      (fun sf P =>
        P = emp ∧ tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = p + 104#64 ∧ sf.readReg64 .x20 = chainsPtr ∧
        sf.readReg64 .x21 = rem - 1#64) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errDropChainLoopPC_at]
  wp_steps
  try rw [hne, if_pos rfl]
  wp_finish
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem errTail_drop_loop_507_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    {chainsPtr : BitVec 64} {s0 : State}
    (rest : List (ChainGhost × ReceiverChain)) :
    ∀ (gc : ChainGhost × ReceiverChain) (p : BitVec 64) (s : State),
      (rest.length + 1) * 104 < 2 ^ 63 →
      s.pc = errDropChainLoopPC_at (blkPl_508).base →
      tryDecryptWPInv s0 s →
      LibsignalCodeLoaded lsmpl s.mem →
      s.readReg64 .x19 = p →
      s.readReg64 .x20 = chainsPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 (rest.length + 1) →
      SepWP ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 848#64) s
        (arrayAt (chainAt A) 104 p (gc :: rest) ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack)
        (fun sf P =>
          P = (memRegion p ((rest.length + 1) * 104) ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) ∧
          tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  induction rest with
  | nil =>
    intro gc p s hlt hpc hmeta hcl hx19 hx20 hx21
    rw [List.length_nil, Nat.zero_add] at hx21
    have hone := errTail_drop_one_507_wp_placed (H := H) gc hdealloc hcl hpc hmeta hx19 hx20 hx21
    refine SepWP.bind_framed (F := emp) hone ?_ ?_
    · rw [arrayAt_cons, arrayAt_nil, sepConj_emp, sepConj_emp]
    intro s1 P1 ⟨hP1, hmeta1, _, hx20_1, hx21_1⟩ hpc1
    subst hP1
    have hexit := errTail_drop_exit_507_wp_placed (H := H) hpc1 hmeta1 hx20_1 hx21_1
    refine SepWP.bind_framed (F := memRegion p 104 ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) hexit ?_ ?_
    · rw [emp_sepConj, sepConj_emp]
    intro sf Pf ⟨hPf, hmeta_f, hx20_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    rw [emp_sepConj, List.length_nil, Nat.zero_add, Nat.one_mul]
  | cons gc' rest' ih =>
    intro gc p s hlt hpc hmeta hcl hx19 hx20 hx21
    rw [List.length_cons] at hlt hx21
    have hone := errTail_drop_one_507_wp_placed (H := H) gc hdealloc hcl hpc hmeta hx19 hx20 hx21
    refine SepWP.bind_framed_lscl (F := arrayAt (chainAt A) 104 (p + 104#64) (gc' :: rest')) hcl hone ?_ ?_
    · rw [arrayAt_cons]; sep_ac_rfl
    intro s1 P1 ⟨hP1, hmeta1, hx19_1, hx20_1, hx21_1⟩ hpc1 hcl1
    subst hP1
    have hstep := errTail_drop_cont_507_wp_placed (H := H)
      (bv_ofNat_succ_succ_bne_one hlt) hpc1 hmeta1 hx19_1 hx20_1 hx21_1
    refine SepWP.bind_framed_lscl
      (F := (memRegion p 104 ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) ∗
            arrayAt (chainAt A) 104 (p + 104#64) (gc' :: rest')) hcl1 hstep ?_ ?_
    · rw [emp_sepConj]
    intro s2 P2 ⟨hP2, hmeta2, hx19_2, hx20_2, hx21_2⟩ hpc2 hcl2
    subst hP2
    have hx21_2' : s2.readReg64 .x21 = BitVec.ofNat 64 (rest'.length + 1) := by
      rw [hx21_2, bv_ofNat_succ_sub_one (rest'.length + 1)]
    have hlt' : (rest'.length + 1) * 104 < 2 ^ 63 :=
      Nat.lt_trans (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (by decide)) hlt
    have hih := ih gc' (p + 104#64) s2 hlt' hpc2 hmeta2 hcl2 hx19_2 hx20_2 hx21_2'
    refine SepWP.bind_framed (F := memRegion p 104) hih ?_ ?_
    · sep_ac_rfl
    intro sf Pf ⟨hPf, hmeta_f, hx20_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    have hcomb : memRegion p ((rest'.length + 1 + 1) * 104) =
        memRegion p 104 ∗ memRegion (p + 104#64) ((rest'.length + 1) * 104) := by
      rw [show (rest'.length + 1 + 1) * 104 = 104 + (rest'.length + 1) * 104 by omega]
      exact memRegion_split p 104 ((rest'.length + 1) * 104) (by omega)
    rw [List.length_cons, hcomb]; sep_ac_rfl

theorem errTail_drop_nil_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = 0#64) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 848#64) s emp
      (fun sf P => P = emp ∧ tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps; wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm]⟩

theorem errTail_drop_init_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {chainsPtr rem : BitVec 64} {s0 s : State}
    (hne : (rem == 0#64) = false)
    (hpc : s.pc = (blkPl_508).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = rem) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) (errDropChainLoopPC_at (blkPl_508).base) s emp
      (fun s1 P1 =>
        P1 = emp ∧ tryDecryptWPInv s0 s1 ∧
        s1.readReg64 .x19 = chainsPtr ∧ s1.readReg64 .x20 = chainsPtr ∧ s1.readReg64 .x21 = rem) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [errDropChainLoopPC_at]
  wp_steps; wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem errTail_drop_chains_507_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {chainsPtr : BitVec 64} {cs : List (ChainGhost × ReceiverChain)} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hlt : cs.length * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_508).base + 820#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx20 : s.readReg64 .x20 = chainsPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 cs.length) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 848#64) s
      (arrayAt (chainAt A) 104 chainsPtr cs ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack)
      (fun sf P =>
        P = (memRegion chainsPtr (cs.length * 104) ∗ A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x20 = chainsPtr) := by
  cases cs with
  | nil =>
    rw [List.length_nil] at hx21
    have hstep := errTail_drop_nil_507_wp_placed (H := H) hpc hmeta hx20 hx21
    refine SepWP.bind_framed (F := A.pool ∗ stackAt (s0.sp - 1504#64) dropChainStack) hstep ?_ ?_
    · rw [arrayAt_nil]
    intro sf Pf ⟨hPf, hmeta_f, hx20_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f, hx20_f⟩
    rw [List.length_nil, Nat.zero_mul, memRegion_zero]
  | cons gc rest =>
    rw [List.length_cons] at hlt hx21 ⊢
    have hstep := errTail_drop_init_507_wp_placed (H := H) (bv_ofNat_succ_beq_zero hlt) hpc hmeta hx20 hx21
    refine SepWP.bind_framed_lscl
      (F := arrayAt (chainAt A) 104 chainsPtr (gc :: rest) ∗ A.pool ∗
            stackAt (s0.sp - 1504#64) dropChainStack) hcl hstep ?_ ?_
    · rw [emp_sepConj]
    intro s1 P1 ⟨hP1, hmeta1, hx19_1, hx20_1, hx21_1⟩ hpc1 hcl1
    subst hP1
    refine SepWP.rw_pre (emp_sepConj _) ?_
    exact errTail_drop_loop_507_wp_placed (A := A) (H := H)
      (chainsPtr := chainsPtr) (s0 := s0)
      hdealloc rest gc chainsPtr s1 hlt hpc1 hmeta1 hcl1 hx19_1 hx20_1 hx21_1

theorem errTail_dealloc_chains_507_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {chainsCap chainsPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hlt : chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_508).base + 848#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = chainsPtr) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 876#64) s
      (((s0.sp - 1504#64 + 56#64) ↦₆₄ chainsCap) ∗
       (if chainsCap = 0#64 then emp
        else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          memRegion chainsPtr (chainsCap.toNat * 104)) ∗
       A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 56#64) ↦₆₄ chainsCap) ∗ A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdealloc_ok := Getters.ls_hook_ok_rustDealloc (prog := (blkPC_508).rebase (blkPl_508).base H) hdealloc
  by_cases hcap : chainsCap = 0#64
  · subst hcap
    refine SepWP.rw_pre (by simp only [ite_true, emp_sepConj, ← hsp]; exact rfl) ?_
    wp_steps; wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp]
  · refine SepWP.rw_pre (by simp only [hcap, ite_false, ← hsp]; exact rfl) ?_
    have hcap_beq : (chainsCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hmul : (chainsCap * 104#64).toNat = chainsCap.toNat * 104 := by
      rw [BitVec.toNat_mul, show (104#64 : BitVec 64).toNat = 104 from rfl,
          Nat.mod_eq_of_lt (by omega)]
    wp_steps; wp_apply; wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp, show s0.sp - 1448#64 = s0.sp - 1504#64 + 56#64 by bv_omega]; sep_ac_rfl

theorem errTail_dealloc_pq_507_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {pqCap pqPtr : BitVec 64} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hpc : s.pc = (blkPl_508).base + 876#64)
    (hmeta : tryDecryptWPInv s0 s) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H) (retEpiloguePC_at (blkPl_508).base) s
      (((s0.sp - 1504#64 + 232#64) ↦₆₄ pqCap) ∗
       ((s0.sp - 1504#64 + 240#64) ↦₆₄ pqPtr) ∗
       (if pqCap = 0#64 then emp
        else A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) ∗
       A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack)
      (fun sf P =>
        P = (((s0.sp - 1504#64 + 232#64) ↦₆₄ pqCap) ∗
             ((s0.sp - 1504#64 + 240#64) ↦₆₄ pqPtr) ∗
             A.pool ∗ stackAt (s0.sp - 1504#64) allocHookStack) ∧
        tryDecryptWPInv s0 sf) := by
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hdealloc_ok := Getters.ls_hook_ok_rustDealloc (prog := (blkPC_508).rebase (blkPl_508).base H) hdealloc
  dsimp only [retEpiloguePC_at]
  by_cases hcap : pqCap = 0#64
  · subst hcap
    refine SepWP.rw_pre (by simp only [ite_true, emp_sepConj, ← hsp]; exact rfl) ?_
    wp_steps; wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp]
  · refine SepWP.rw_pre (by simp only [hcap, ite_false, ← hsp]; exact rfl) ?_
    have hcap_beq : (pqCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    wp_steps; wp_apply; wp_steps; wp_finish
    refine ⟨?_, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩
    rw [hsp,
        show s0.sp - 1272#64 = s0.sp - 1504#64 + 232#64 by bv_omega,
        show s0.sp - 1264#64 = s0.sp - 1504#64 + 240#64 by bv_omega]
    sep_ac_rfl

theorem errTail_all_steps_507_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    {ret tag : BitVec 64} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {w0 w1 w2 w3 w4 r0 r1 r2 r3 r4 r5 t0 t1 t2 : BitVec 64} {s0 s : State}
    (hcs_le : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat)
    (hcs_lt : trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = errTailPC_at (blkPl_508).base)
    (hmeta : tryDecryptWPInv s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx26 : s.readReg64 .x26 = tag) :
    let sp := s0.sp - 1504#64
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    SepWP ((blkPC_508).rebase (blkPl_508).base H) (retEpiloguePC_at (blkPl_508).base) s
      (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
       ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ t0) ∗ ((sp + 328#64) ↦₆₄ t1) ∗
       ((sp + 336#64) ↦₆₄ t2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
       A.pool ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
             ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
             ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
             ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗ A.pool ∗ stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only; let sp := s0.sp - 1504#64; set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hcopy := errTail_copy_spe_507_wp_placed (H := H)
    (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2) hpc hmeta hx19 hx20 hx26
  refine SepWP.bind_framed_lscl
    (F := ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
          A.pool ∗ stackAt sp dropChainStack) hcl hcopy ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s1 P1 ⟨hP1, hmeta1, hx20_1, hx21_1⟩ hpc1 hcl1; subst hP1
  have hcs_lt' : cs.length * 104 < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 hcs_le) hcs_lt
  have hdrop_cs := errTail_drop_chains_507_wp_placed (A := A) (H := H)
    hdealloc hcs_lt' hpc1 hmeta1 hcl1 hx20_1 hx21_1
  refine SepWP.bind_framed
    (F := ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
          ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)) hdrop_cs ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s2 P2 ⟨hP2, hmeta2, hx20_2⟩ hpc2; subst hP2
  let sp0 := s0.sp - 1504#64
  let R_rest : SepProp :=
    A.pool ∗ stackAt sp0 allocHookStack ∗ memRegion (sp0 - 4144#64) 48 ∗
    ((sp0 + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp0 + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
    ((sp0 + 232#64) ↦₆₄ trG.pq.cap) ∗ ((sp0 + 240#64) ↦₆₄ trG.pq.ptr) ∗
    ((sp0 + 320#64) ↦₆₄ w0) ∗ ((sp0 + 328#64) ↦₆₄ w1) ∗ ((sp0 + 336#64) ↦₆₄ w2) ∗
    words5At (sp0 + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗ words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
    (if trG.pq.cap = 0#64 then emp
     else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)
  have hent_cs :
      ((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗ stackAt sp dropChainStack) ∗
       (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
        ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
        ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
        ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.ratchet.chainsCap = 0#64 then emp
         else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
           memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
             ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) ⊢
      ((((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
        (if trG.ratchet.chainsCap = 0#64 then emp
         else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
           memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
        A.pool ∗ stackAt sp allocHookStack) ∗
       (memRegion (sp - 4144#64) 48 ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
        ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
        ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
        ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by
    dsimp only [sp]; rw [stackAt_dropChainStack_sub sp0]
    have hcomm1 :
        ((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗
          (stackAt sp0 allocHookStack ∗ memRegion (sp0 - 4144#64) 48)) ∗
         (((sp0 + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp0 + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp0 + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp0 + 232#64) ↦₆₄ trG.pq.cap) ∗
          ((sp0 + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp0 + 320#64) ↦₆₄ w0) ∗ ((sp0 + 328#64) ↦₆₄ w1) ∗
          ((sp0 + 336#64) ↦₆₄ w2) ∗ words5At (sp0 + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
               ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) =
        (((sp0 + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         (memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
               ((trG.ratchet.chainsCap.toNat - cs.length) * 104))) ∗ R_rest) := by
      dsimp only [R_rest, sp0]; sep_ac_rfl
    have hcomm2 :
        ((((sp0 + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
          A.pool ∗ stackAt sp0 allocHookStack) ∗
         (memRegion (sp0 - 4144#64) 48 ∗ ((sp0 + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp0 + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp0 + 232#64) ↦₆₄ trG.pq.cap) ∗
          ((sp0 + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp0 + 320#64) ↦₆₄ w0) ∗ ((sp0 + 328#64) ↦₆₄ w1) ∗
          ((sp0 + 336#64) ↦₆₄ w2) ∗ words5At (sp0 + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) =
        (((sp0 + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗ R_rest) := by
      dsimp only [R_rest, sp0]; sep_ac_rfl
    rw [hcomm1, hcomm2]
    exact sepConj_mono_right (sepConj_mono_left (chains_recombine_entails hcs_le hcs_lt))
  refine SepWP.mono_pre hent_cs ?_
  have hdealloc_cs := errTail_dealloc_chains_507_wp_placed (A := A) (H := H)
    hdealloc hcs_lt hpc2 hmeta2 hx20_2
  refine SepWP.bind_framed
    (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗
          ((sp + 336#64) ↦₆₄ w2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)) hdealloc_cs ?_ ?_
  · dsimp only [sp]
  intro s3 P3 ⟨hP3, hmeta3⟩ hpc3; subst hP3
  have hdealloc_pq := errTail_dealloc_pq_507_wp_placed (A := A) (H := H)
    (pqCap := trG.pq.cap) (pqPtr := trG.pq.ptr) hdealloc hpc3 hmeta3
  refine SepWP.bind_framed
    (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗ ((sp + 336#64) ↦₆₄ w2) ∗
          words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4) hdealloc_pq ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro sf Pf ⟨hPf, hmeta_f⟩ hpcf; subst hPf
  refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
  rw [stackAt_dropChainStack_sub sp]; dsimp only [sp]; sep_ac_rfl

theorem reaches_epilogue_to_outcome_tight_507_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {H : String → Option (State → State)}
    (x : TryDecryptGhost) (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.model C S parse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.model C S parse).1.toBool G')
    (hreach : reaches_pc ((blkPC_508).rebase (blkPl_508).base H) (retEpiloguePC_at (blkPl_508).base) s
      (fun s1 =>
        tryDecryptMidMeta_placed s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt A x.ss G' (x.model C S parse).2 ∗
          vecResultAt A x.ret (x.model C S parse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          cliTryDecryptCommonHeapPlaced A ctl x (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 ∗ R))) :
    reaches_outcome ((blkPC_508).rebase (blkPl_508).base H)
      (cliTryDecryptTightSpecPlaced C A ctl parse S) x R s0 s := by
  have hcomb : reaches_pc ((blkPC_508).rebase (blkPl_508).base H) (s0.readReg64 .x30) s
      (fun sf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.mem ⊨ (cliTryDecryptTightSpecPlaced C A ctl parse S).post x s0 sf ∗ R)) := by
    refine reaches_pc_seq hreach ?_
    intro s1 hpc1 _ ⟨⟨hrun1, hsp1, hs0_align, hsp_align1, _, htrace1, _, hvregs1⟩, hm1⟩
    unfold cliTryDecryptCommonHeapPlaced at hm1
    have hm1_re : s1.mem ⊨
        (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
          memRegion (s0.sp - 1504#64) 1408 ∗ tryDecryptSavedRegs s0.sp s0) ∗
        (sessionStateAt A x.ss G' (x.model C S parse).2 ∗
         vecResultAt A x.ret (x.model C S parse).1 ∗
         protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         FromRecordCallees.lsLogOff ∗ A.pool ∗ R) := by
      convert hm1 using 1; ac_rfl
    refine reaches_pc_mono
      (sepWP_to_reaches_pc
        (tryDecrypt_epilogue_394_507_wp_placed s0 s1 hpc1 hrun1 hsp1 hs0_align hsp_align1 htrace1 hvregs1) hm1_re) ?_
    intro sf _ _ ⟨P_f, hm_sf, hsp_sf, htrace_sf, hcc_sf, hP_f⟩
    refine ⟨hsp_sf, hcc_sf, ?_⟩
    have hm2 := Satisfies.mono (sepConj_mono_left hP_f) hm_sf
    dsimp only [cliTryDecryptTightSpecPlaced, withLsCodeRoLoaded,
      CryptoVerification.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedTightSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec]
    have hm3 : sf.mem ⊨
        sessionStateAt A x.ss G' (x.model C S parse).2 ∗
        (vecResultAt A x.ret (x.model C S parse).1 ∗
         protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         FromRecordCallees.lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool ∗ R) := by
      convert hm2 using 1; ac_rfl
    have hent :
        sessionStateAt A x.ss G' (x.model C S parse).2 ⊢
          ⌜(x.model C S parse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
            (∃∗ G'' : SessionGhost, ⌜x.G.AfterTryDecrypt (x.model C S parse).1.toBool G''⌝ ∗
              sessionStateAt A x.ss G'' (x.model C S parse).2) :=
      Entails.pure_right ⟨hnpan, htrace_sf⟩
        (Entails.trans (Entails.pure_right hG' (Entails.refl _))
          (Entails.sepExists_intro
            (P := fun G'' => ⌜x.G.AfterTryDecrypt (x.model C S parse).1.toBool G''⌝ ∗
              sessionStateAt A x.ss G'' (x.model C S parse).2) G'))
    have hm4 := Satisfies.mono (sepConj_mono_left hent) hm3
    convert hm4 using 1; ac_rfl
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, hsp_sf, hcc_sf, hpost_sf⟩ | ⟨_, hfalse⟩⟩ := hcomb hL
  · exact P3kR1bc.reaches_outcome_steps hsteps
      (reaches_outcome.of_outcome (Or.inl ⟨⟨hpc_sf, hsp_sf, hrun_sf⟩, ⟨hsp_sf, hcc_sf⟩, hpost_sf⟩))
  · exact hfalse.elim

end CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup

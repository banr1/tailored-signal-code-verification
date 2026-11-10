/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeys -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.Getters.SameAccount
import ProofLib.RegChain
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep

/-!
# `HookSat`-backed `black_box` Sibling of `TripleRatchet/Decrypt/ChainLookup/IdentityKeys`

Weakens `h_bb : H lsBlackBoxU8Sym = some blackBoxHook` to
`h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat` across Block `17` (`is_same_account`) and
Block `130` Segment S0 (`identityKeys_placed_ok_sat`, `identityKeys_placed_ok_x_sat`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSat

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_212 blkPl_212 lsBlackBoxU8Sym
   ls_subroutine_ok_of_block lsmpl sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.LibsignalSessionRepr (chainAt msgTypeByte vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel TryDecryptGhost logOff rootStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (tryDecryptCommonHeap tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (LoadRatchetState_placed blkPC_131 blkPl_131 bytes9_64_8_eq_8_64 exists_remoteGroupC_of_length_32
   exists_remoteGroupC_of_memRegion_32 identityKeys_step1_reaches_placed
   identityKeys_step2_reaches_placed identityKeys_step3_reaches_placed
   identityKeys_step4_reaches_placed identityKeys_step4_to_memRegion_1352
   identityKeys_step5_none_reaches_placed identityKeys_step5_some_extract
   identityKeys_step5_some_recombine reaches_pc_lscl reaches_pc_seq_lscl remoteGroupC
   remoteGroupC_eq_remoteGroupD remoteGroupD remote_identity_key_placed_ok segLoadRatchetPC_placed
   sepWP_to_reaches_pc stackAt_tryDecryptSubStack_sub tryDecryptDummyImg tryDecryptEntry_placed
   tryDecryptFnPlacedSpec tryDecryptPlacedSpec tryDecryptRawSpec)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (IsSameAccountGhost blkPC_17 blkPl_17 localIdentityOkAt remoteIdentityOkAt)
open CryptoVerification.LibsignalTripleRatchetRepr
  (optSenderChainAt optTailVecAt protocolAddressAt sessionStateAt signalMessageAt tapeAfter
   tapeAt uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc vecAt vecU8At)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat publicKeyEqMemSpec16 publicKey_eq_mem_placed_ok_16_sat)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `160`-byte (`144` B frames + `16` B `black_box` stack) stack requirement for `is_same_account`. -/
abbrev isSameAccountStack16 : Nat := 160

/-- `160`-byte counterpart of `isSameAccountSpec` (Block `17`). -/
@[expose] def isSameAccountSpec16 : Spec IsSameAccountGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.localIkA ∧ s.readReg64 .x2 = x.remoteIkA ∧ x.localIk ≠ x.remoteIk⌝ ∗
      (x.localIkA ↦ₛ x.localIk.publicKey.bytes.toList) ∗
      (x.remoteIkA ↦ₛ x.remoteIk.publicKey.bytes.toList) ∗
      stackAt s.sp isSameAccountStack16
  post := fun x s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
      (x.localIkA ↦ₛ x.localIk.publicKey.bytes.toList) ∗
      (x.remoteIkA ↦ₛ x.remoteIk.publicKey.bytes.toList) ∗
      stackAt s0.sp isSameAccountStack16

private theorem publicKey_beq_false_of_ne_ik {ik1 ik2 : IdentityKey} (h : ik1 ≠ ik2) :
    (ik1.publicKey == ik2.publicKey) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  apply h
  cases ik1
  cases ik2
  cases heq
  rfl

private theorem stackAt_isSameAccount16_split_placed (sp : BitVec 64) :
    stackAt sp isSameAccountStack16 =
      memRegion (sp - 80#64 - 80#64) 80 ∗
      memRegion (sp - 80#64) 32 ∗ cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountStack16]
  rw [show sp - 80#64 - 80#64 = sp - 160#64 by bv_omega,
      show BitVec.ofNat 64 160 = 160#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 80) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 32) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      (memRegion_cells (sp - 48#64) 6 (by decide) : memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]

/-- Block `17` (`<IdentityKey>::is_same_account`) meets `isSameAccountSpec16` (`160` B) under
`HookSat H lsBlackBoxU8Sym blackBoxSpecSat`. -/
theorem is_same_account_placed_ok_16_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl isSameAccountSpec16) := by
  simp only [withLsCodeLoaded, isSameAccountSpec16]
  have heq0 : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H)
      (lsmpl.base 212) (withLsCodeLoaded lsmpl publicKeyEqMemSpec16) :=
    publicKey_eq_mem_placed_ok_16_sat h_bb
  have heq := ls_subroutine_ok_of_block (callerProg := (blkPC_17).rebase (blkPl_17).base H) heq0
  simp only [withLsCodeLoaded, publicKeyEqMemSpec16] at heq
  wp_init x s0
  obtain ⟨localIkA, localIk, remoteIkA, remoteIk⟩ := x
  dsimp only at *
  subst h_2 h_3
  rw [stackAt_isSameAccount16_split_placed s0.sp]
  cells_unfold
  wp_pull_exists
  have hne := publicKey_beq_false_of_ne_ik h_1
  apply sepWP_seq_lscl h (mid := lsmpl.base 212)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_call
  wp_apply
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at *
  wp_steps
  wp_done

/-- `160`-byte `isSameAccountSpec16` counterpart of `identityKeys_remote_some_wp_placed`. -/
theorem identityKeys_remote_some_wp_placed_16 [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hsame : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl isSameAccountSpec16))
    (x : TryDecryptGhost) (remIk : IdentityKey) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8) (u400 : BitVec 64) (u408 : BitVec 8)
    (dw0 : BitVec 32) (db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 : BitVec 8)
    (dw3 : BitVec 64) (db31 : BitVec 8)
    (h_pc : s.pc = (blkPl_131).base + 384#64) (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s.readReg64 .x11 = 1#64) (hx20 : s.readReg64 .x20 = s.sp + 320#64)
    (hx25 : s.readReg64 .x25 = x.locA) (hx29 : s.readReg64 .x29 = s.sp + 1408#64)
    (hrem_eq : ∀ a : BitVec 64, (a ↦ₛ remIk.publicKey.bytes.toList) =
      remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s
      (((s.sp + 48#64) ↦₆₄ x.remA) ∗ ((s.sp + 400#64) ↦₆₄ u400) ∗ ((s.sp + 408#64) ↦₈ u408) ∗
       ((s.sp + 352#64) ↦₆₄ w3) ∗ ((s.sp + 360#64) ↦₈ b31) ∗ ((s.sp + 976#64) ↦₃₂ w0) ∗
       ((s.sp + 980#64) ↦₈ b4) ∗ ((s.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ stackAt s.sp isSameAccountStack16)
      (fun sf P_f =>
        sf.sp = s.sp ∧ sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (sf.readReg64 .x1).setWidth 32 = 0#32 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.sp + 320#64 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = x.locA ∧
        sf.readReg64 .x29 = s.sp + 1408#64 ∧
        (P_f ⊢ ((s.sp + 48#64) ↦₆₄ x.remA) ∗ ((s.sp + 400#64) ↦₈ b6) ∗
          ((s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
          ((s.sp + 352#64) ↦₆₄ w3) ∗ ((s.sp + 360#64) ↦₈ b31) ∗ ((s.sp + 976#64) ↦₃₂ w0) ∗
          ((s.sp + 980#64) ↦₈ b4) ∗ ((s.sp + 981#64) ↦₈ b5) ∗
          ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
          ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          stackAt s.sp isSameAccountStack16)) := by
  simp only [withLsCodeLoaded, isSameAccountSpec16] at hsame
  unfold remoteGroupD
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_seq_lscl hcl (mid := (blkPl_131).base + 404#64)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl1
  have hb14 : BitVec.zeroExtend 8 (pack64 b14 b15 b16 b17 b18 b19 b20 b21) = b14 := by
    unfold pack64; bv_kernel
  have h400 :
      ((s.sp + 400#64) ↦₆₄ pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∗ (s.sp + 408#64) ↦₈ b14) =
      ((s.sp + 400#64) ↦₈ b6 ∗ (s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      bytes9_64_8_eq_8_64 (s.sp + 400#64) b6 b7 b8 b9 b10 b11 b12 b13 b14
  rw [hb14, ← sepConj_assoc ((s.sp + 400#64) ↦₆₄ _), h400, sepConj_assoc]
  apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 17)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_call
  have hb4 : BitVec.zeroExtend 8 (b5 ++ b4) = b4 := by bv_kernel
  have hb5 : BitVec.extractLsb' 8 8 (BitVec.zeroExtend 32 (b5 ++ b4)) = b5 := by bv_kernel
  have hb6 : BitVec.zeroExtend 8 (pack64 b6 b7 b8 b9 b10 b11 b12 b13) = b6 := by
    unfold pack64; bv_kernel
  have hb15_22 :
      BitVec.truncate 64 ((BitVec.zeroExtend 64 b22 ++ pack64 b14 b15 b16 b17 b18 b19 b20 b21) >>> 8) =
        pack64 b15 b16 b17 b18 b19 b20 b21 b22 := by
    unfold pack64; bv_kernel
  have hrem56 :
      ((s.sp + 56#64) ↦₃₂ w0 ∗ (s.sp + 60#64) ↦₈ b4 ∗ (s.sp + 61#64) ↦₈ b5 ∗
       (s.sp + 62#64) ↦₈ b6 ∗ (s.sp + 63#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14 ∗
       (s.sp + 71#64) ↦₆₄ pack64 b15 b16 b17 b18 b19 b20 b21 b22 ∗
       (s.sp + 79#64) ↦₆₄ w3 ∗ (s.sp + 87#64) ↦₈ b31) =
      ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) := by
    simpa only [remoteGroupD, BitVec.add_assoc, BitVec.reduceAdd] using (hrem_eq (s.sp + 56#64)).symm
  rw [hb4, hb5, hb6, hb15_22, hrem56]
  wp_apply
  wp_steps
  wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    Entails.of_eq (by sep_ac_rfl)⟩

private theorem tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest ⊢ tapeAfter ctl cur rest 0 := by
  unfold tapeAt tapeAfter
  have hcur : cur + BitVec.ofNat 64 0 = cur := by bv_omega
  have hlen : rest.length - 0 = rest.length := Nat.sub_zero _
  rw [hcur, hlen]
  exact Entails.pure_left (fun _ => Entails.refl _)

/-- `HookSat`-backed counterpart of `identityKeys_step5_some_reaches_placed`. -/
theorem identityKeys_step5_some_reaches_placed_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (x : TryDecryptGhost) (remIk : IdentityKey) (F : SepProp) (s0 s4 : State)
    (hcl : LibsignalCodeLoaded lsmpl s4.mem)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s4.pc = (blkPl_131).base + 384#64) (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64) (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx8 : s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s4.readReg64 .x10 = BitVec.zeroExtend 64 b22) (hx11 : s4.readReg64 .x11 = 1#64)
    (hx19 : s4.readReg64 .x19 = x.ret) (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s4.readReg64 .x21 = x.ss) (hx22 : s4.readReg64 .x22 = x.msgA)
    (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA) (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hrem_eq : ∀ a : BitVec 64, (a ↦ₛ remIk.publicKey.bytes.toList) =
      remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk)
    (hm : s4.mem ⊨ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗ memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      ((s0.sp - 1504#64 + 352#64) ↦₆₄ w3) ∗ ((s0.sp - 1504#64 + 360#64) ↦₈ b31) ∗
      ((s0.sp - 1504#64 + 976#64) ↦₃₂ w0) ∗ ((s0.sp - 1504#64 + 980#64) ↦₈ b4) ∗
      ((s0.sp - 1504#64 + 981#64) ↦₈ b5) ∗ memRegion ((s0.sp - 1504#64) + 56#64) 296 ∗
      memRegion ((s0.sp - 1504#64) + 361#64) 39 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 542 ∗
      memRegion ((s0.sp - 1504#64) + 982#64) 298 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s4
      (fun s5 => s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp isSameAccountStack16 (by decide)] at hm
  have hm_sub : s4.mem ⊨ (memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 296) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗ stackAt sp isSameAccountStack16 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountStack16) ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u400, u408, dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15, db16, db17, db18, db19, db20, db21, db22, dw3, db31, hm_ext⟩ :=
    identityKeys_step5_some_extract hm_sub
  have hm_pre : s4.mem ⊨
      (((s4.sp + 48#64) ↦₆₄ x.remA) ∗ ((s4.sp + 400#64) ↦₆₄ u400) ∗ ((s4.sp + 408#64) ↦₈ u408) ∗
       ((s4.sp + 352#64) ↦₆₄ w3) ∗ ((s4.sp + 360#64) ↦₈ b31) ∗ ((s4.sp + 976#64) ↦₃₂ w0) ∗
       ((s4.sp + 980#64) ↦₈ b4) ∗ ((s4.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s4.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s4.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ stackAt s4.sp isSameAccountStack16) ∗
      (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ memRegion (sp + 1312#64) 96 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountStack16) ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s4.readReg64 .x20 = s4.sp + 320#64 := by rw [h_sp]; exact hx20
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by rw [hx29, h_sp]; bv_omega
  have hsame := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H)
    (is_same_account_placed_ok_16_sat h_bb)
  have hwp := identityKeys_remote_some_wp_placed_16 hsame x remIk s4 hcl w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
    w3 b31 u400 u408 dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31
    h_pc h_run h_sp_align hx8 hx9 hx10 hx11 hx20' hx25 hx29' hrem_eq hdiff
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨by reg_chain, halign5, by reg_chain, hx1_5, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, hx25_5, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s5
  rw [h_sp] at hm2
  have hm3 : s5.mem ⊨
      (((sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗ memRegion (sp + 88#64) 264 ∗
       ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗ memRegion (sp + 361#64) 39 ∗
       ((sp + 400#64) ↦₈ b6) ∗ ((sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
       memRegion (sp + 409#64) 25 ∗ memRegion (sp + 434#64) 542 ∗ ((sp + 976#64) ↦₃₂ w0) ∗
       ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗ memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ memRegion (sp + 1312#64) 96) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗
       (stackAt sp isSameAccountStack16 ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountStack16)) ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp isSameAccountStack16 (by decide)] at hm3
  have hm4 := Satisfies.mono
    (sepConj_mono_left (identityKeys_step5_some_recombine sp x.st.localIdentity remIk w0 b4 b5 b6
      (pack64 b7 b8 b9 b10 b11 b12 b13 b14) w3 b31)) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

/-- `HookSat`-backed counterpart of `identityKeys_step45_reaches_placed`. -/
theorem identityKeys_step45_reaches_placed_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State) (hcl : LibsignalCodeLoaded lsmpl s3.mem)
    (h_pc : s3.pc = (blkPl_131).base + 160#64) (h_run : s3.status = .Running)
    (h_sp : s3.sp = s0.sp - 1504#64) (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret) (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss) (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA) (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hnot_self : x.st.remoteIdentity ≠ some x.st.localIdentity)
    (hm : s3.mem ⊨ remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff tryDecryptDummyImg ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s3
      (fun s5 => s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗
          logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hrem_opt : x.st.remoteIdentity with _ | remIk
  · rw [hrem_opt] at hm
    dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega,
        show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    have hm_402 : s3.mem ⊨ memRegion (sp + 402#64) 32 ∗
        (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 0#8) ∗ memRegion (sp + 56#64) 344 ∗
         memRegion (sp + 434#64) 846 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F) := by
      dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, w3, b31, hent_402, hm_402⟩ :=
      exists_remoteGroupC_of_memRegion_32 hm_402
    have hm_s4 : s3.mem ⊨
        ((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 0#8) ∗
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
        memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
        (((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F) := by
      dsimp only [sp] at hm_402 ⊢; convert hm_402 using 1; sep_ac_rfl
    refine reaches_pc_seq
      (identityKeys_step4_reaches_placed (H := H) x _ s0 s3 0#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 (hent_402 (sp + 402#64)) hm_s4) ?_
    intro s4 hpc4 hrun4 ⟨hsp4, halign4, htr4, _, _, _, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩
    have hm4_re : s4.mem ⊨
        (memRegion (sp + 56#64) 296 ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
         memRegion (sp + 361#64) 39 ∗ memRegion (sp + 400#64) 34 ∗ memRegion (sp + 434#64) 542 ∗
         ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
         memRegion (sp + 982#64) 298 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96) ∗
        (logOff tryDecryptDummyImg ∗ (((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
      dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
    have hm4_1352 := Satisfies.mono (sepConj_mono_left (identityKeys_step4_to_memRegion_1352 sp x.st.localIdentity w0 b4 b5 w3 b31)) hm4_re
    refine reaches_pc_mono
      (identityKeys_step5_none_reaches_placed (H := H) x (((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗ F)
        s0 s4 hpc4 hrun4 hsp4 halign4 htr4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx29_4 hm4_1352) ?_
    intro s5 _ _ ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩
    refine ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, ?_⟩
    dsimp only [sp] at hm5; convert hm5 using 1; sep_ac_rfl
  · rw [hrem_opt] at hm
    dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega,
        show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, w3, b31, hrem_c⟩ :=
      exists_remoteGroupC_of_length_32 (List.Vector.toList_length remIk.publicKey.bytes)
    have hent_402 : remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ⊢
        memRegion (sp + 402#64) 32 := by
      rw [← hrem_c (sp + 402#64)]
      have hlen : remIk.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
      have h := pointsToBytes_entails_memRegion (sp + 402#64) remIk.publicKey.bytes.toList
      rwa [hlen] at h
    rw [hrem_c (sp + 402#64)] at hm
    have hm_s4 : s3.mem ⊨
        ((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 1#8) ∗
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
        memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
        (((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F) := by
      dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
    refine reaches_pc_seq_lscl hcl
      (identityKeys_step4_reaches_placed (H := H) x _ s0 s3 1#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hent_402 hm_s4) ?_
    intro s4 hpc4 hrun4 ⟨hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩ hcl4
    have hrem_d : ∀ a : BitVec 64, (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 :=
      fun a => (hrem_c a).trans (remoteGroupC_eq_remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    have hdiff : x.st.localIdentity ≠ remIk := by intro heq; apply hnot_self; rw [hrem_opt, heq]
    have hm4_re : s4.mem ⊨
        ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 400#64) 34 ∗
        ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗ ((sp + 976#64) ↦₃₂ w0) ∗
        ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗ memRegion (sp + 56#64) 296 ∗
        memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
        ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
        memRegion (sp + 1312#64) 96 ∗ stackAt sp tryDecryptSubStack ∗ (logOff tryDecryptDummyImg ∗ F) := by
      dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
    refine reaches_pc_mono
      (identityKeys_step5_some_reaches_placed_sat h_bb x remIk (logOff tryDecryptDummyImg ∗ F) s0 s4 hcl4
        w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31
        hpc4 hrun4 hsp4 halign4 htr4 hx8_4 hx9_4 hx10_4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx29_4
        hrem_d hdiff hm4_re) ?_
    intro s5 _ _ ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩
    refine ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, ?_⟩
    convert hm5 using 1; sep_ac_rfl

/-- `HookSat`-backed Block `130` Segment S0 (`+0x000..+0x1d8`) under `[LibsignalPlacement]`:
conclusion is token-identical to `IdentityKeys.identityKeys_placed_ok`. -/
theorem identityKeys_placed_ok_sat [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (x : TryDecryptGhost) (R : SepProp) (s0 : State)
    (h_pc : s0.pc = tryDecryptEntry_placed) (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨ (tryDecryptPlacedSpec C A ctl uuidTryParse S).pre x s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segLoadRatchetPC_placed s0
      (LoadRatchetState_placed A ctl x R s0) := by
  dsimp only [tryDecryptPlacedSpec, withLsCodeLoaded, tryDecryptRawSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hnot_self, _, _, _⟩, hm0⟩
  unfold sessionStateAt at hm0
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm0
  rcases hm0 with ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, hm0⟩
  have hm_s1 : s0.mem ⊨ stackAt s0.sp rootStack ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗
      (vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗ optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm0 using 1; sep_ac_rfl
  refine reaches_pc_seq_lscl hcl0
    (identityKeys_step1_reaches_placed (H := H) x _ s0 hcl0 h_pc h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc hm_s1) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, halign1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx29_1, hm1⟩ hcl1
  have hm_s2 : s1.mem ⊨ localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗
      (vecGhostAt A x.G.localIk x.ss ∗ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗
       (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗ optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗ logOff tryDecryptDummyImg ∗ memRegion x.ret 48 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  refine reaches_pc_seq_lscl hcl1
    (identityKeys_step2_reaches_placed (H := H) x _ s0 s1 hpc1 hrun1 hsp1 halign1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hm_s2) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx29_2, hm2⟩ hcl2
  have hm_s3 : s2.mem ⊨ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗ logOff tryDecryptDummyImg ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
       ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ vecGhostAt A x.G.localIk x.ss ∗
       memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗ optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
        ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  have hrem := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H)
    (remote_identity_key_placed_ok A H)
  refine reaches_pc_seq_lscl hcl2
    (identityKeys_step3_reaches_placed hrem x _ s0 s2 hcl2 hpc2 hrun2 hsp2 halign2 htr2 hx0_2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx29_2 hdeser_rem hm_s3) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx29_3, hm3⟩ hcl3
  have hm_s45 : s3.mem ⊨ remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff tryDecryptDummyImg ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (vecGhostAt A x.G.localIk x.ss ∗ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s0.sp - 1504#64) 48 ∗ tryDecryptSavedRegs s0.sp s0 ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗ optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm3 using 1; sep_ac_rfl
  refine reaches_pc_mono
    (reaches_pc_lscl hcl3
      (identityKeys_step45_reaches_placed_sat h_bb x _ s0 s3 hcl3 hpc3 hrun3 hsp3 halign3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx29_3 hnot_self hm_s45)) ?_
  intro s5 hpc5 hrun5 ⟨⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩, hcl5⟩
  refine ⟨hpc5, ⟨hrun5, hsp5, h_sp_align, halign5, hx29_5, htr5.1, hcl5, htr5.2⟩,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx1_5, ?_⟩
  unfold sessionStateAt tryDecryptCommonHeap
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, ?_⟩
  have hm5_tape : s5.mem ⊨
      tapeAt ctl x.cur x.rest ∗ (((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       memRegion (s0.sp - 1504#64 + 56#64) 1352 ∗ logOff tryDecryptDummyImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ vecGhostAt A x.G.localIk x.ss ∗
       vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s0.sp - 1504#64) 48 ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A (x.ss + 0x90#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗ optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗
       ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗ A.pool ∗ R) := by
    convert hm5 using 1; sep_ac_rfl
  have hm5_after := Satisfies.mono (sepConj_mono_left (tapeAfter_zero ctl x.cur x.rest)) hm5_tape
  convert hm5_after using 1; sep_ac_rfl

/-- `HookSat`-backed `tryDecryptFnPlacedSpec` variant of `identityKeys_placed_ok_x`. -/
theorem identityKeys_placed_ok_x_sat [LibsignalPlacement] {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (x : TryDecryptGhost) (R : SepProp) (s0 : State)
    (h_pc : s0.pc = tryDecryptEntry_placed) (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨ (tryDecryptFnPlacedSpec C decFn A ctl uuidTryParse S).pre x s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segLoadRatchetPC_placed s0
      (LoadRatchetState_placed A ctl x R s0) :=
  @identityKeys_placed_ok_sat _ C A ctl S H h_bb x R s0 h_pc h_run h_sp_align hpre

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSat

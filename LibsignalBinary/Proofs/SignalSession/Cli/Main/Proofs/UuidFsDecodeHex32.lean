/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
public import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.DecodeHex32
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `.keepsFs` Contract for `uuid::parser::decode_hex32`

Lifts `decodeHex32_ok` to `decodeHex32Spec.keepsFs` on `libsignalSessionCode` for arbitrary image
base and hook table.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops.UuidFs

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem fs_writeReg_local (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by
  cases s; cases w <;> cases r <;> rfl

structure DecodeLoopInvFs (entry : BitVec 64) (s0 s : State)
    (out src sp' acc : BitVec 64) (i : Nat) : Prop where
  inv : DecodeLoopInv entry s0 s out src sp' acc i
  hfs : s.fs = s0.fs

structure DecodeLoopPostFs (entry : BitVec 64) (s0 s : State)
    (out src sp' acc : BitVec 64) : Prop where
  post : DecodeLoopPost entry s0 s out src sp' acc
  hfs : s.fs = s0.fs

theorem decode_hex32_iter_step_fs (b : BitVec 64)
    (hooks : String → Option (State → State))
    (target_pc : BitVec 64) (s0 s : State) (out src sp' acc : BitVec 64) (i : Nat)
    (c old_b : BitVec 8) (Frame : SepProp) (post : State → SepProp → Prop)
    (hinv : DecodeLoopInvFs ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name)
      s0 s out src sp' acc i)
    (hnext : ∀ s' : State,
      s'.pc = (if (BitVec.ofNat 64 i + 1#64 != 32#64) = true
               then (libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name + bv% (20)
               else (libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name + bv% (88)) →
      s'.status = .Running →
      s'.sp = sp' →
      s'.readReg64 (Reg.gpr 0#5) = out →
      s'.readReg64 (Reg.gpr 1#5) = src →
      s'.readReg64 (Reg.gpr 8#5) = stepAcc acc c →
      s'.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 (i + 1) →
      s'.readReg64 (Reg.gpr 10#5) = sp' →
      s'.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) →
      s'.trace = s0.trace →
      s'.fs = s0.fs →
      CalleeSavedPreserved s0 s' →
      SepWP (libsignalSessionCode.rebase b hooks) target_pc s'
        (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b hooks) target_pc s
      (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ old_b) ∗ Frame) post := by
  rcases hinv with ⟨⟨hpc, hrun, hsp, hsp_align, hx0, hx1, hx8, hx9, hx10, hx30, htrace, hcs⟩, hfs⟩
  have hsp' : s.sp &&& 15#64 = 0#64 := hsp ▸ hsp_align
  code_fetches CryptoVerification.libsignalSessionCode decodeHex32Bin
    b hooks
    (ls_lemma% fnOff "uuid::parser::decode_hex32") (num% (ls_off% "uuid::parser::decode_hex32")) 380
  dsimp only [decodeHex32Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::decode_hex32" = entry
  examples_hide_fetches
  wp_steps
  apply hnext
  · rfl
  · simp only [arm64_norm, hrun]
  · simp only [arm64_norm, hsp]
  · simp only [arm64_norm, hx0]
  · simp only [arm64_norm, hx1]
  · rfl
  · simp only [arm64_norm, BitVec.ofNat_add]
  · simp only [arm64_norm, hx10]
  · simp only [arm64_norm, hx30]
  · simp only [arm64_norm, htrace]
  · simp only [arm64_norm, hfs]
  · simp (config := { decide := true }) only [arm64_norm, hcs]

theorem decode_hex32_loop_fs (b : BitVec 64)
    (hooks : String → Option (State → State))
    (target_pc : BitVec 64) (s0 : State) (out src sp' : BitVec 64)
    (post : State → SepProp → Prop) :
    ∀ (rem_src rem_sp : List (BitVec 8)) (i : Nat) (acc : BitVec 64)
      (s : State) (Frame : SepProp),
      rem_src ≠ [] →
      rem_sp.length = rem_src.length →
      i + rem_src.length = 32 →
      DecodeLoopInvFs ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name)
        s0 s out src sp' acc i →
      (∀ sf : State,
        DecodeLoopPostFs ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name)
          s0 sf out src sp' (rem_src.foldl stepAcc acc) →
        SepWP (libsignalSessionCode.rebase b hooks) target_pc sf
          (((src + BitVec.ofNat 64 i) ↦ₛ rem_src) ∗
           ((sp' + BitVec.ofNat 64 i) ↦ₛ (rem_src.map rawNibble)) ∗ Frame) post) →
      SepWP (libsignalSessionCode.rebase b hooks) target_pc s
        (((src + BitVec.ofNat 64 i) ↦ₛ rem_src) ∗
         ((sp' + BitVec.ofNat 64 i) ↦ₛ rem_sp) ∗ Frame) post
  | [], _, _, _, _, _, hne, _, _, _, _ => absurd rfl hne
  | c :: rest_src, rem_sp, i, acc, s, Frame, _, hlen_sp, hi_sum, hinv, hcont => by
    rcases rem_sp with _ | ⟨old_b, rest_sp⟩
    · simp at hlen_sp
    have hsplit_pre :
        (((src + BitVec.ofNat 64 i) ↦ₛ (c :: rest_src)) ∗
         ((sp' + BitVec.ofNat 64 i) ↦ₛ (old_b :: rest_sp)) ∗ Frame) =
        (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ old_b) ∗
         (((src + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_src) ∗
          ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗ Frame)) := by
      rw [pointsToBytes_cons_off src i c rest_src, pointsToBytes_cons_off sp' i old_b rest_sp]
      ac_rfl
    rw [hsplit_pre]
    refine decode_hex32_iter_step_fs b hooks target_pc s0 s out src sp' acc i c old_b
      (((src + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_src) ∗
       ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗ Frame) post hinv ?_
    intro s' hpc' hrun' hsp' hx0' hx1' hx8' hx9' hx10' hx30' htrace' hfs' hcs'
    rcases rest_src with _ | ⟨c2, rest_src'⟩
    · have hi31 : i = 31 := by simp at hi_sum; omega
      subst hi31
      have hpc_done : s'.pc = (libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name + bv% (88) := by
        simpa using hpc'
      have hpost_inv : DecodeLoopPostFs ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name)
          s0 s' out src sp' ([c].foldl stepAcc acc) :=
        ⟨⟨hpc_done, hrun', hsp', hinv.inv.hsp_align, hx0', hx1', hx8', hx30', htrace', hcs'⟩, hfs'⟩
      have hrest_sp : rest_sp = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen_sp)
      subst hrest_sp
      have hrecomb :
          (((src + BitVec.ofNat 64 31) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 31) ↦₈ rawNibble c) ∗
           (((src + BitVec.ofNat 64 (31 + 1)) ↦ₛ []) ∗
            ((sp' + BitVec.ofNat 64 (31 + 1)) ↦ₛ []) ∗ Frame)) =
          (((src + BitVec.ofNat 64 31) ↦ₛ [c]) ∗
           ((sp' + BitVec.ofNat 64 31) ↦ₛ ([c].map rawNibble)) ∗ Frame) := by
        simp only [List.map_cons, List.map_nil, pointsToBytes_singleton, pointsToBytes_nil,
          emp_sepConj]
      rw [hrecomb]
      exact hcont s' hpost_inv
    · have hi_lt : i + 1 < 32 := by simp at hi_sum; omega
      have hbne : (BitVec.ofNat 64 i + 1#64 != 32#64) = true := bne_32_of_lt hi_lt
      simp only [hbne, ↓reduceIte] at hpc'
      have hnext_inv : DecodeLoopInvFs ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name)
          s0 s' out src sp' (stepAcc acc c) (i + 1) :=
        ⟨⟨hpc', hrun', hsp', hinv.inv.hsp_align, hx0', hx1', hx8', hx9', hx10', hx30', htrace', hcs'⟩,
         hfs'⟩
      have hrearr1 :
          (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗
           (((src + BitVec.ofNat 64 (i + 1)) ↦ₛ (c2 :: rest_src')) ∗
            ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗ Frame)) =
          (((src + BitVec.ofNat 64 (i + 1)) ↦ₛ (c2 :: rest_src')) ∗
           ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗
           (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame)) := by
        ac_rfl
      rw [hrearr1]
      refine decode_hex32_loop_fs b hooks target_pc s0 out src sp' post
        (c2 :: rest_src') rest_sp (i + 1) (stepAcc acc c) s'
        (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame)
        (List.cons_ne_nil _ _) (by simp at hlen_sp; omega) (by simp at hi_sum ⊢; omega)
        hnext_inv ?_
      intro sf hpost_sf
      have hrearr2 :
          (((src + BitVec.ofNat 64 (i + 1)) ↦ₛ (c2 :: rest_src')) ∗
           ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ ((c2 :: rest_src').map rawNibble)) ∗
           (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame)) =
          (((src + BitVec.ofNat 64 i) ↦ₛ (c :: c2 :: rest_src')) ∗
           ((sp' + BitVec.ofNat 64 i) ↦ₛ ((c :: c2 :: rest_src').map rawNibble)) ∗ Frame) := by
        simp only [List.map_cons]
        rw [pointsToBytes_cons_off src i c (c2 :: rest_src'),
            pointsToBytes_cons_off sp' i (rawNibble c) (rawNibble c2 :: List.map rawNibble rest_src')]
        ac_rfl
      rw [hrearr2]
      exact hcont sf hpost_sf

theorem decode_hex32_post_err_fs (b : BitVec 64)
    (hooks : String → Option (State → State))
    (s0 sf : State) (out src : BitVec 64) (hex : List (BitVec 8)) (R : SepProp)
    (hlen : hex.length = 32)
    (hall : hex.all isHexByte = false)
    (hpost : DecodeLoopPostFs ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name)
      s0 sf out src (s0.sp - 32#64) (hex.foldl stepAcc 0#64)) :
    SepWP (libsignalSessionCode.rebase b hooks) (s0.readReg64 (Reg.gpr 30#5)) sf
      ((src ↦ₛ hex) ∗ ((s0.sp - 32#64) ↦ₛ (hex.map rawNibble)) ∗ memRegion out 17 ∗ R)
      (fun s' Q =>
        s'.status = .Running ∧
        s'.sp = s0.sp ∧
        CalleeSavedPreserved s0 s' ∧
        (Q ⊢ decodeHex32Spec.keepsFs.post (out, src, hex) s0 s' ∗ R)) := by
  rcases hpost with ⟨⟨hpc, hrun, hsp, hsp_align, hx0, hx1, hx8_0, hx30, htrace, hcs⟩, hfs⟩
  have hx8 : sf.readReg64 (Reg.gpr 8#5) = 1#64 := by
    rw [hx8_0, foldl_stepAcc_zero, hall]; rfl
  clear hx8_0
  have hsp' : sf.sp &&& 15#64 = 0#64 := hsp ▸ hsp_align
  have hmem17 : memRegion out 17 = (∃∗ b0 : BitVec 8, out ↦₈ b0) ∗ memRegion (out + 1#64) 16 := by
    rw [show (17 : Nat) = 1 + 16 from rfl, memRegion_split out 1 16 (by decide), memRegion_one]
  rw [hmem17]
  wp_pull_exists
  code_fetches CryptoVerification.libsignalSessionCode decodeHex32Bin
    b hooks
    (ls_lemma% fnOff "uuid::parser::decode_hex32") (num% (ls_off% "uuid::parser::decode_hex32")) 380
  dsimp only [decodeHex32Name] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::decode_hex32" = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done
  · rfl
  · simp only [arm64_norm, hrun]
  refine ⟨by simp only [arm64_norm, hrun], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hcs], ?_⟩
  have hdec : decodeHex32 hex = none := by
    rw [decodeHex32_of_length_32 hlen, hall]; rfl
  dsimp only [Spec.keepsFs, decodeHex32Spec]
  rw [hdec]
  dsimp only [decodeHex32ResultAt]
  simp only [arm64_norm, hfs, htrace, pure_true, emp_sepConj, sepConj_assoc]
  have hcells := pointsToBytes_entails_stackAt_32 s0.sp (hex.map rawNibble) (by simp [hlen])
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hcells)) ?_
  apply entails_of_eq
  ac_rfl

theorem decode_hex32_post_ok_fs (b : BitVec 64)
    (hooks : String → Option (State → State))
    (s0 sf : State) (out src : BitVec 64) (hex : List (BitVec 8)) (R : SepProp)
    (hlen : hex.length = 32)
    (hall : hex.all isHexByte = true)
    (hpost : DecodeLoopPostFs ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name)
      s0 sf out src (s0.sp - 32#64) (hex.foldl stepAcc 0#64)) :
    SepWP (libsignalSessionCode.rebase b hooks) (s0.readReg64 (Reg.gpr 30#5)) sf
      ((src ↦ₛ hex) ∗ ((s0.sp - 32#64) ↦ₛ (hex.map rawNibble)) ∗ memRegion out 17 ∗ R)
      (fun s' Q =>
        s'.status = .Running ∧
        s'.sp = s0.sp ∧
        CalleeSavedPreserved s0 s' ∧
        (Q ⊢ decodeHex32Spec.keepsFs.post (out, src, hex) s0 s' ∗ R)) := by
  rcases hpost with ⟨⟨hpc, hrun, hsp, hsp_align, hx0, hx1, hx8_0, hx30, htrace, hcs⟩, hfs⟩
  have hx8 : sf.readReg64 (Reg.gpr 8#5) = 0#64 := by
    rw [hx8_0, foldl_stepAcc_zero, hall]; rfl
  clear hx8_0
  have hsp' : sf.sp &&& 15#64 = 0#64 := hsp ▸ hsp_align
  have hns_len : (hex.map rawNibble).length = 32 := by simp [hlen]
  rcases list_length_32_elim (hex.map rawNibble) hns_len with
    ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
     n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, hns⟩
  have hdec_len :
      (decodeNibbles [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
                      n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31]).length = 16 := rfl
  have hdec : decodeHex32 hex =
      some ⟨decodeNibbles [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
                           n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31],
            hdec_len⟩ := by
    rw [decodeHex32_of_length_32 hlen]
    simp only [hall, ↓reduceIte]
    congr 1
    exact Subtype.ext (congrArg decodeNibbles hns)
  have hdec_res : decodeHex32ResultAt out (decodeHex32 hex) =
      (out ↦₈ 1#8) ∗
      ((out + 1#64) ↦ₛ
        [rawCombine n0 n1, rawCombine n2 n3, rawCombine n4 n5, rawCombine n6 n7,
         rawCombine n8 n9, rawCombine n10 n11, rawCombine n12 n13, rawCombine n14 n15,
         rawCombine n16 n17, rawCombine n18 n19, rawCombine n20 n21, rawCombine n22 n23,
         rawCombine n24 n25, rawCombine n26 n27, rawCombine n28 n29, rawCombine n30 n31]) := by
    rw [hdec]; rfl
  rw [hns, ← hsp, pointsToBytes_32_expand sf.sp]
  rw [memRegion_eq_exists_bytes out 17 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro os
  wp_focus_pure; intro hos_len
  rcases list_length_17_elim os hos_len with
    ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, hos⟩
  rw [hos, pointsToBytes_17_expand out]
  code_fetches CryptoVerification.libsignalSessionCode decodeHex32Bin
    b hooks
    (ls_lemma% fnOff "uuid::parser::decode_hex32") (num% (ls_off% "uuid::parser::decode_hex32")) 380
  dsimp only [decodeHex32Name] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::decode_hex32" = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done
  · rfl
  · simp only [arm64_norm, hrun]
  refine ⟨by simp only [arm64_norm, hrun], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hcs], ?_⟩
  dsimp only [Spec.keepsFs, decodeHex32Spec]
  simp only [arm64_norm, hfs, htrace, pure_true, emp_sepConj, sepConj_assoc, rawCombine_step_eq]
  rw [hdec_res, ← pointsToBytes_32_sub32_expand s0.sp, ← pointsToBytes_16_tail_expand out]
  have hcells := pointsToBytes_entails_stackAt_32 s0.sp
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
     n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31] rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hcells)) ?_
  apply entails_of_eq
  ac_rfl

theorem decodeHex32_okFs (b : BitVec 64)
    (hooks : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name)
      decodeHex32Spec.keepsFs := by
  apply subroutine_ok_of_sepWP_entails
  intro ⟨out, src, hex⟩ R s0 hpc hrun hsp_align
  conv => arg 4; simp only [Spec.keepsFs, decodeHex32Spec, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hx0, hx1, hlen⟩
  conv => arg 4; rw [stackAt_32_split s0.sp]
  wp_pull_exists
  have hloop := decode_hex32_loop_fs b hooks (s0.readReg64 (Reg.gpr 30#5)) s0 out src (s0.sp - 32#64)
  have herr := fun sf => decode_hex32_post_err_fs b hooks s0 sf out src hex R hlen
  have hok := fun sf => decode_hex32_post_ok_fs b hooks s0 sf out src hex R hlen
  code_fetches CryptoVerification.libsignalSessionCode decodeHex32Bin
    b hooks
    (ls_lemma% fnOff "uuid::parser::decode_hex32") (num% (ls_off% "uuid::parser::decode_hex32")) 380
  dsimp only [decodeHex32Name] at hpc hloop herr hok ⊢
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::decode_hex32" = entry
  examples_hide_fetches
  wp_steps 5
  have hgroup :
      ((src ↦ₛ hex) ∗ memRegion out 17 ∗
       ((s0.sp - 32#64) ↦₆₄ 0#64) ∗ ((s0.sp - 24#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 16#64) ↦₆₄ 0#64) ∗ ((s0.sp - 8#64) ↦₆₄ 0#64) ∗ R) =
      (((src + BitVec.ofNat 64 0) ↦ₛ hex) ∗
       (((s0.sp - 32#64) + BitVec.ofNat 64 0) ↦ₛ List.replicate 32 0#8) ∗
       (memRegion out 17 ∗ R)) := by
    have h0a : src + BitVec.ofNat 64 0 = src := by bv_arith
    have h0b : s0.sp - 32#64 + BitVec.ofNat 64 0 = s0.sp - 32#64 := by bv_arith
    rw [h0a, h0b, ← stack32_zero_eq_replicate s0.sp]
    ac_rfl
  rw [hgroup]
  have hsp32_align : (s0.sp - 32#64) &&& 15#64 = 0#64 := by
    unfold State.spAligned at hsp_align
    have h : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
    have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
      simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
    have h' := congrArg BitVec.toNat h
    apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
    have hlt := s0.sp.isLt; omega
  have hhex_ne : hex ≠ [] := by intro h; simp [h] at hlen
  refine hloop _ hex (List.replicate 32 0#8) 0 0#64 _ (memRegion out 17 ∗ R)
    hhex_ne (by simp [hlen]) (by omega)
    ⟨⟨rfl, by simp only [arm64_norm, hrun], by simp only [arm64_norm],
      hsp32_align, by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm],
      by simp (config := { decide := true }) only [arm64_norm, CalleeSavedPreserved.rfl]⟩,
     by simp only [arm64_norm]⟩
    ?_
  intro sf hpost_sf
  have h0a : src + BitVec.ofNat 64 0 = src := by bv_arith
  have h0b : s0.sp - 32#64 + BitVec.ofNat 64 0 = s0.sp - 32#64 := by bv_arith
  rw [h0a, h0b]
  cases hall : hex.all isHexByte
  · exact herr sf hall hpost_sf
  · exact hok sf hall hpost_sf

end CryptoVerification.SignalSession.Cli.MainHops.UuidFs

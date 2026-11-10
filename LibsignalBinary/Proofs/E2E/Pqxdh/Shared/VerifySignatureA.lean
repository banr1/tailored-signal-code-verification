/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignatureDecode
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.RoDataReloc -- shake: keep
/-!
# `<PublicKey>::verify_signature` (`0x3dd4c`) and `verify_signature_for_multipart_message` (`0x3dd74`)

Proves `verifySignatureMultipart_sepWP` (`verifySignatureMultipart_base_ok`) and
`verifySignature_sepWP` (`verifySignature_base_ok`) on `tripleRatchetProgAt` and
`tripleRatchetProgAtExt`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
namespace CryptoVerification.E2E.Pqxdh.Shared
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
open SignalPqxdh SignalPqxdh.Model
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
private theorem calleeSavedVRegs_setPC_pre_trap (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := calleeSavedVRegs_setPC s pc
private theorem calleeSavedVRegs_setMem_setPC_pre_trap (s : State) (m : Memory) (pc : BitVec 64) :
    calleeSavedVRegs ((s.setMem m).setPC pc) = calleeSavedVRegs s := by
  rw [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem]
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  calleeSavedVRegs_setPC_pre_trap calleeSavedVRegs_setMem_setPC_pre_trap
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  libsignalSessionCode_fnOff_0x3dd44 libsignalSessionCode_fnOff_0x3de30
  libsignalSessionCode_fnOff_0x3de58 libsignalSessionCode_fnOff_0x3eda8
  (ls_stub% "memset") (ls_stub% "memcpy")
  (ls_stub% "sha2::sha512::compress512") (ls_stub% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide")
  (ls_stub% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order") (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint>::compress")
  (ls_stub% "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards") (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free")
  (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg") (ls_stub% "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint")
  (ls_hook% "memset") (ls_hook% "memcpy")
  (ls_hook% "sha2::sha512::compress512") (ls_hook% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide")
  (ls_hook% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order") (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint>::compress")
  (ls_hook% "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards") (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free")
  (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg") (ls_hook% "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint")
/-! ## Read-Only Data, Unpack64, and Stub Helpers -/
structure RoQuad64 (m : Memory) (ea v1 v2 v3 v4 : BitVec 64) : Prop where
  read0 : m.read64 ea = v1
  read8 : m.read64 (ea + 8#64) = v2
  read16 : m.read64 (ea + 16#64) = v3
  read24 : m.read64 (ea + 24#64) = v4
  canRead0 : m.canRead ea 8 = true
  canRead8 : m.canRead (ea + 8#64) 8 = true
  canRead16 : m.canRead (ea + 16#64) 8 = true
  canRead24 : m.canRead (ea + 24#64) 8 = true
theorem RoQuad64.of_holdsBytes {m : Memory} {ea v1 v2 v3 v4 : BitVec 64} {bs : List (BitVec 8)}
    (h : Obj.HoldsBytes m ea bs (fun _ => Perm.ro))
    (hbs : bs = unpack64 v1 ++ unpack64 v2 ++ unpack64 v3 ++ unpack64 v4) :
    RoQuad64 m ea v1 v2 v3 v4 := by
  rw [hbs, List.append_assoc, List.append_assoc] at h; obtain ⟨h1, hrest1⟩ := holdsBytes_append h
  obtain ⟨h2, hrest2⟩ := holdsBytes_append hrest1; obtain ⟨h3, h4⟩ := holdsBytes_append hrest2
  simp only [unpack64_length, BitVec.add_assoc] at h2 h3 h4
  obtain ⟨hc1, hr1⟩ := memSlice_of_holdsBytes_ro h1
  obtain ⟨hc2, hr2⟩ := memSlice_of_holdsBytes_ro h2
  obtain ⟨hc3, hr3⟩ := memSlice_of_holdsBytes_ro h3
  obtain ⟨hc4, hr4⟩ := memSlice_of_holdsBytes_ro h4
  exact ⟨Memory.read64_of_readBytes_eq_unpack64 m _ _ hr1,
    Memory.read64_of_readBytes_eq_unpack64 m _ _ hr2,
    Memory.read64_of_readBytes_eq_unpack64 m _ _ hr3,
    Memory.read64_of_readBytes_eq_unpack64 m _ _ hr4, hc1, hc2, hc3, hc4⟩
@[irreducible] def roStop (pc : BitVec 64) : BitVec 64 := pc
theorem reaches_pc_keepsFrozen {prog : Program} {target_pc : BitVec 64} {s : State}
    {Q : State → Prop} (h : reaches_pc prog target_pc s Q) :
    reaches_pc prog target_pc s (fun sf => s.mem.KeepsFrozen sf.mem ∧ Q sf) := by
  intro hL; obtain ⟨sf, hsteps, ⟨hpc, hrun, hQ⟩ | hoom⟩ := h hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hsteps.keepsFrozen, hQ⟩⟩
  · exact ⟨sf, hsteps, Or.inr hoom⟩
theorem SepWP.done_ro {prog : Program} {mid : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} (hpc : s.pc = mid)
    (hrun : s.status = .Running) (hpost : post s P) : SepWP prog (roStop mid) s P post := by
  unfold roStop; exact SepWP.done hpc hrun hpost
theorem SepWP.step_ldpSimd128_ro {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea' ea2 ea3 ea4 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 v3 v4 : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .Q128 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hea3 : ea + 16#64 = ea3) (hea4 : ea3 + 8#64 = ea4)
    (hro : RoQuad64 s.mem ea' v1 v2 v3 v4) (hea : ea' = ea)
    (hexec : (((applyWriteback s wb).writeVReg128 vt1 (v2 ++ v1)).writeVReg128 vt2 (v4 ++
      v3)).setPC (pc + 4#64) = s') (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  subst hea
  have hs_pc : s.setPC pc = s := by
    cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
  have hread1 : s.mem.read64 ea' = v1 := hro.read0
  have hread2 : s.mem.read64 ea2 = v2 := hea2 ▸ hro.read8
  have hread3 : s.mem.read64 ea3 = v3 := hea3 ▸ hro.read16
  have hread4 : s.mem.read64 ea4 = v4 := by
    have h24 : ea' + 24#64 = ea4 := by rw [← hea4, ← hea3, BitVec.add_assoc]; rfl
    exact h24 ▸ hro.read24
  have hcan1 : s.mem.canRead ea' 8 = true := hro.canRead0
  have hcan2 : s.mem.canRead ea2 8 = true := hea2 ▸ hro.canRead8
  have hcan3 : s.mem.canRead ea3 8 = true := hea3 ▸ hro.canRead16
  have hcan4 : s.mem.canRead ea4 8 = true := by
    have h24 : ea' + 24#64 = ea4 := by rw [← hea4, ← hea3, BitVec.add_assoc]; rfl
    exact h24 ▸ hro.canRead24
  have hcan_lo : s.mem.canRead ea' 16 = true := Memory.canRead_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  have hcan_hi : s.mem.canRead ea3 16 = true := Memory.canRead_16_of_8_8 hcan3 (hea4.symm ▸ hcan4)
  have hstep : execInst (.ldpSimd .Q128 vt1 vt2 addr) (s.setPC pc) = s' := by
    rw [hs_pc, ← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, Memory.readSimdSized, Memory.read128, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hea2, hea3, hea4,
      hread1, hread2, hread3, hread4, hcan_lo, hcan_hi, SimdMemSize.bytes, hpc]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]; cases wb <;> rfl
  exact SepWP.step_pure hpc hrun hfetch hstep hmem hnext
macro "wp_step_ldp_ro " hquad:term:max : tactic =>
  `(tactic| (
    apply SepWP.step_ldpSimd128_ro
    wp_focus_close wp_norm_lhs
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_assumption | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close wp_norm_lhs
    wp_focus_close wp_norm_lhs
    wp_focus_close wp_norm_lhs
    wp_focus_close wp_norm_lhs
    wp_focus_close (exact $hquad)
    wp_focus_close (first | rfl | wp_assumption | (simp only [*, BitVec.add_assoc,
                                                   BitVec.reduceAdd]; done) | (bv_omega; done))
    wp_focus_close wp_norm_lhs
  ))
macro "wp_ldp_ro " f:term:max : tactic =>
  `(tactic| (
    apply SepWP.done_ro (by wp_norm_lhs) (by wp_norm_lhs)
    intro _hro_ldp
    wp_step_ldp_ro ($f _hro_ldp)))
theorem and_pageMask_eq_sub_and_fff (x : BitVec 64) :
    x &&& 0xfffffffffffff000#64 = x - (x &&& 0xfff#64) := by bv_bits
theorem aligned_and_fff {b : BitVec 64} (hb : b.toNat % Arm64.Obj.pageSize = 0) :
    b &&& 0xfff#64 = 0#64 := by
  simp only [Arm64.Obj.pageSize] at hb; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.and_two_pow_sub_one_eq_mod _ 12, hb]
theorem bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
macro "cells_pre_unfold_fast" : tactic =>
  `(tactic| (
    conv => arg 4; simp (config := { maxSteps := 1000000 }) only [
      cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit',
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]))
macro "wp_simp_pre_fast " "[" rules:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (conv => arg 4; simp only [$rules,*]))
macro "wp_extract_exists" : tactic =>
  `(tactic| (
    (conv =>
      arg 4
      simp (config := { maxSteps := 1000000 }) only [
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    repeat' (apply SepWP.exists_elim; intro _)
    try (apply SepWP.pure_elim; intro _)))
theorem bytesToBv8_append (xs ys : Bytes) :
    bytesToBv8 (xs ++ ys) = bytesToBv8 xs ++ bytesToBv8 ys := by simp [bytesToBv8]
theorem bytesToBv8_inj {xs ys : Bytes} (h : bytesToBv8 xs = bytesToBv8 ys) : xs = ys := by
  have h1 := congrArg (List.map (fun b : BitVec 8 => UInt8.ofBitVec b)) h
  simpa [bytesToBv8, List.map_map, Function.comp_def] using h1
theorem exists_unpack64_of_length_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
            ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗
            ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : (bs.drop 32).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => ?_⟩
  have hsplit : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0, hp1]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem cells_10_merge (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ⊢ cells a 10 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <| Entails.refl _
def pqxdhCtEqSliceSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec
    64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ cells (sp - 48#64) 6
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ cells (sp - 48#64) 6
theorem cells_6_eq_stackFrameFor_ct_eq (sp : BitVec 64) : cells (sp - 48#64) 6 =
      stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp := by
  cells_unfold
  simp only [stackFrameFor, libsignalSessionCode_frameBytes_0x3eda8, reduceStackFrameAt]
theorem pqxdhCtEqSliceSpec_eq :
    pqxdhCtEqSliceSpec = CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec :=
      by
  unfold pqxdhCtEqSliceSpec CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec
  simp only [cells_6_eq_stackFrameFor_ct_eq]
def sha512IVBytesLE : List (BitVec 8) := bytesToBv8 (revWords64 sha512InitState)
theorem sha512IVBytesLE_eq_unpack64 : sha512IVBytesLE =
      (unpack64 0x6a09e667f3bcc908#64 ++ unpack64 0xbb67ae8584caa73b#64 ++
       unpack64 0x3c6ef372fe94f82b#64 ++ unpack64 0xa54ff53a5f1d36f1#64) ++
      (unpack64 0x510e527fade682d1#64 ++ unpack64 0x9b05688c2b3e6c1f#64 ++
       unpack64 0x1f83d9abfb41bd6b#64 ++ unpack64 0x5be0cd19137e2179#64) := by decide
open ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux CryptoProofLib.RoDataReloc in
theorem img_dataLen : libsignalSessionImage.data.length = num% (ls_field% dataLen) := by rfl_kernel
set_option maxRecDepth 200000 in
open ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux CryptoProofLib.RoDataReloc in
theorem sha512IV_rodata_check : (decide (libsignalSessionImage.dataOff ≤ num% (ls_xref% 0x3df5c 0x3df60)) &&
      decide ((num% (ls_xref% 0x3df5c 0x3df60) - libsignalSessionImage.dataOff) + 64 ≤ num% (ls_field% dataLen)) &&
      noRelocInRange libsignalSessionImage.relocs (num% (ls_field% dataLen) + libsignalSessionImage.bss)
        (num% (ls_xref% 0x3df5c 0x3df60) - libsignalSessionImage.dataOff) 64 && inLiRoData libsignalSessionImage (num% (ls_xref% 0x3df5c 0x3df60)) 64 &&
      decide ((libsignalSessionImage.data.drop (num% (ls_xref% 0x3df5c 0x3df60) - libsignalSessionImage.dataOff)).take 64 =
        sha512IVBytesLE)) = true := by
  rfl_kernel
open ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux CryptoProofLib.RoDataReloc in
theorem sha512IV_holdsBytes {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    Obj.HoldsBytes s.mem (img.base + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro) := by
  have h := sha512IV_rodata_check; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hk : (num% (ls_xref% 0x3df5c 0x3df60) - libsignalSessionImage.dataOff) + 64 ≤ libsignalSessionImage.data.length := by
    rw [img_dataLen]; exact h.1.1.1.2
  have hno : noRelocInRange libsignalSessionImage.relocs
      (libsignalSessionImage.data.length + libsignalSessionImage.bss)
      (num% (ls_xref% 0x3df5c 0x3df60) - libsignalSessionImage.dataOff) 64 = true := by
    rw [img_dataLen]; exact h.1.1.2
  have hlen : sha512IVBytesLE.length = 64 := rfl
  exact loads_rodata_holdsBytes himg hF h.1.1.1.1 hk hno h.1.2 hlen h.2
theorem sha512IV_quad0 {b : BitVec 64} {m : Memory}
    (h : Obj.HoldsBytes m (b + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro)) :
    RoQuad64 m (b + bv% (ls_xref% 0x3df5c 0x3df60)) 0x6a09e667f3bcc908#64 0xbb67ae8584caa73b#64
      0x3c6ef372fe94f82b#64 0xa54ff53a5f1d36f1#64 := by
  rw [sha512IVBytesLE_eq_unpack64] at h; exact RoQuad64.of_holdsBytes (holdsBytes_append h).1 rfl
theorem sha512IV_quad1 {b : BitVec 64} {m : Memory}
    (h : Obj.HoldsBytes m (b + bv% (ls_xref% 0x3df5c 0x3df60)) sha512IVBytesLE (fun _ => Perm.ro)) :
    RoQuad64 m (b + bv% (ls_xref% 0x3df5c 0x3df60 + 32)) 0x510e527fade682d1#64 0x9b05688c2b3e6c1f#64
      0x1f83d9abfb41bd6b#64 0x5be0cd19137e2179#64 := by
  rw [sha512IVBytesLE_eq_unpack64] at h; have h2 := (holdsBytes_append h).2
  have hadd : b + bv% (ls_xref% 0x3df5c 0x3df60) + BitVec.ofNat 64 (unpack64 0x6a09e667f3bcc908#64 ++
    unpack64 0xbb67ae8584caa73b#64 ++
       unpack64 0x3c6ef372fe94f82b#64 ++ unpack64 0xa54ff53a5f1d36f1#64).length = b + bv% (ls_xref% 0x3df5c 0x3df60 + 32) :=
       by
    have hlen : (unpack64 0x6a09e667f3bcc908#64 ++ unpack64 0xbb67ae8584caa73b#64 ++
       unpack64 0x3c6ef372fe94f82b#64 ++ unpack64 0xa54ff53a5f1d36f1#64).length = 32 := rfl
    rw [hlen]; bv_omega
  rw [hadd] at h2; exact RoQuad64.of_holdsBytes h2 rfl
def xeddsaVerifyBinRef (P : Primitives) (pk m sig : Bytes) : Bool :=
  if pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0) then
    let signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
    match P.montToEd pk signBit with
    | none => false
    | some edPk =>
      let capA := P.compress edPk; let minusCapA := P.edNeg edPk; let capR := sig.take 32
      let sRaw := sig.drop 32; let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
      let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
      let sScalar := P.scalarFromBytesModOrder sClamped
      let capRCheck := P.compress (P.doubleScalarMulBasepoint h minusCapA sScalar)
      capRCheck == capR
  else false
theorem uint8_ubfm7_eq_signBit (b : UInt8) :
    BitVec.zeroExtend 64 ((BitVec.zeroExtend 32 b.toBitVec).extractLsb 31 7) =
      BitVec.ofNat 64 (((b &&& 0x80) >>> 7).toNat) := by
  rcases b with ⟨bv⟩; revert bv; decide
theorem uint8_and7f_ult32_iff (b : UInt8) :
    (BitVec.zeroExtend 32 b.toBitVec &&& 0x7f#32).ult 32#32 = ((b &&& 0x60) == 0) := by
  rcases b with ⟨bv⟩; revert bv; decide
theorem verifySig_adrp (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64) :
    ((b + 0x3de58#64 + 260#64) &&& 0xfffffffffffff000#64) + bv% (page% (ls_xref% 0x3df5c 0x3df60) - 0x3d000) + bv% ((ls_xref% 0x3df5c 0x3df60) % 4096) =
      b + bv% (ls_xref% 0x3df5c 0x3df60) := by
  revert hb; bv_bits
theorem fitBytes_eq_fitBytesRef (n : Nat) (bs : Bytes) : fitBytes n bs = fitBytesRef n bs := rfl
theorem revWords64_length {bs : Bytes} (h : bs.length = 64) : (revWords64 bs).length = 64 := by
  simp [revWords64, h]
theorem list_split8_64 {α : Type} (bs : List α) (h : bs.length = 64) :
    bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ ((bs.drop 24).take 8 ++
      ((bs.drop 32).take 8 ++ ((bs.drop 40).take 8 ++ ((bs.drop 48).take 8 ++
        (bs.drop 56).take 8)))))) := by
  have h56 : (bs.drop 56).take 8 = bs.drop 56 := List.take_of_length_le (by simp [h])
  have s7 : bs.drop 48 = (bs.drop 48).take 8 ++ bs.drop 56 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 48)).symm
  have s6 : bs.drop 40 = (bs.drop 40).take 8 ++ bs.drop 48 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 40)).symm
  have s5 : bs.drop 32 = (bs.drop 32).take 8 ++ bs.drop 40 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 32)).symm
  have s4 : bs.drop 24 = (bs.drop 24).take 8 ++ bs.drop 32 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 24)).symm
  have s3 : bs.drop 16 = (bs.drop 16).take 8 ++ bs.drop 24 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 16)).symm
  have s2 : bs.drop 8 = (bs.drop 8).take 8 ++ bs.drop 16 := by
    simpa [List.drop_drop] using (List.take_append_drop 8 (bs.drop 8)).symm
  have s1 : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  rw [h56, ← s7, ← s6, ← s5, ← s4, ← s3, ← s2, ← s1]
theorem revWords64_of_append8 {w0 w1 w2 w3 w4 w5 w6 w7 : Bytes}
    (h0 : w0.length = 8) (h1 : w1.length = 8) (h2 : w2.length = 8) (h3 : w3.length = 8)
    (h4 : w4.length = 8) (h5 : w5.length = 8) (h6 : w6.length = 8) (h7 : w7.length = 8) :
    revWords64 (w0 ++ (w1 ++ (w2 ++ (w3 ++ (w4 ++ (w5 ++ (w6 ++ w7))))))) =
      w0.reverse ++ (w1.reverse ++ (w2.reverse ++ (w3.reverse ++
        (w4.reverse ++ (w5.reverse ++ (w6.reverse ++ w7.reverse)))))) := by
  unfold revWords64; simp only [List.take_left' h0, List.drop_left' h0,
    show (16 : Nat) = 8 + 8 from rfl, ← List.drop_drop, List.take_left' h1, List.drop_left' h1,
    show (24 : Nat) = 8 + (8 + 8) from rfl, List.take_left' h2, List.drop_left' h2,
    show (32 : Nat) = 8 + (8 + (8 + 8)) from rfl, List.take_left' h3, List.drop_left' h3,
    show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) from rfl, List.take_left' h4, List.drop_left' h4,
    show (48 : Nat) = 8 + (8 + (8 + (8 + (8 + 8)))) from rfl,
    List.take_left' h5, List.drop_left' h5,
    show (56 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + 8))))) from rfl,
    List.take_left' h6, List.drop_left' h6,
    List.take_of_length_le (Nat.le_of_eq h7), List.append_assoc]
theorem revWords64_involutive {bs : Bytes} (h : bs.length = 64) :
    revWords64 (revWords64 bs) = bs := by
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h3 : ((bs.drop 24).take 8).length = 8 := by simp [h]
  have h4 : ((bs.drop 32).take 8).length = 8 := by simp [h]
  have h5 : ((bs.drop 40).take 8).length = 8 := by simp [h]
  have h6 : ((bs.drop 48).take 8).length = 8 := by simp [h]
  have h7 : ((bs.drop 56).take 8).length = 8 := by simp [h]
  conv => lhs; arg 1; rw [list_split8_64 bs h]
  rw [revWords64_of_append8 h0 h1 h2 h3 h4 h5 h6 h7,
    revWords64_of_append8 (by simp [h0]) (by simp [h1]) (by simp [h2]) (by simp [h3])
      (by simp [h4]) (by simp [h5]) (by simp [h6]) (by simp [h7])]
  simp only [List.reverse_reverse]; exact (list_split8_64 bs h).symm
theorem sha512CompressOutBytes_length (P : Primitives) (st blk : Bytes) :
    (sha512CompressOutBytes P st blk).length = 64 := by
  apply revWords64_length; exact fitBytes_length 64 _
theorem sha512Step_length (P : Primitives) (st blk : Bytes) : (sha512Step P st blk).length = 64 :=
  fitBytesRef_length 64 _
theorem foldl_sha512Step_length (P : Primitives) (blks : List Bytes) (st : Bytes)
    (hst : st.length = 64) : (blks.foldl (sha512Step P) st).length = 64 := by
  induction blks generalizing st with
  | nil => exact hst
  | cons b rest ih => exact ih (sha512Step P st b) (sha512Step_length P st b)
theorem revWords64_sha512CompressOutBytes_of_len (P : Primitives) {st blk : Bytes}
    (hst : st.length = 64) : revWords64 (sha512CompressOutBytes P st blk) =
      (chunkBlocks 128 blk).foldl (sha512Step P) (revWords64 st) := by
  unfold sha512CompressOutBytes
  rw [revWords64_involutive (fitBytes_length 64 _), fitBytes_eq_fitBytesRef,
    fitBytesRef_of_length_eq (foldl_sha512Step_length P _ _ (revWords64_length hst))]
theorem sha512Ref_of_length_97 (P : Primitives) {msg : Bytes} (h : msg.length = 97) :
    sha512Ref P msg = revWords64 (sha512CompressOutBytes P (revWords64 sha512InitState)
        (msg ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 97)) := by
  have hpad_eq : sha512Pad msg = msg ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 97 := by
    unfold sha512Pad; rw [h]; rfl
  have hinit_len : sha512InitState.length = 64 := rfl
  rw [revWords64_sha512CompressOutBytes_of_len P (revWords64_length hinit_len),
    revWords64_involutive hinit_len, ← hpad_eq]
  unfold sha512Ref; rw [fitBytesRef_of_length_eq (foldl_sha512Step_length P _ _ hinit_len)]
theorem list_range_add (m n : Nat) :
    List.range (m + n) = List.range m ++ (List.range n).map (m + ·) := by
  induction n with
  | zero => simp
  | succ n ih => rw [← Nat.add_assoc, List.range_succ, List.range_succ, ih]; simp
theorem chunkBlocks_128_append {a b : Bytes} (k m : Nat)
    (ha : a.length = k * 128) (hb : b.length = m * 128) :
    chunkBlocks 128 (a ++ b) = chunkBlocks 128 a ++ chunkBlocks 128 b := by
  unfold chunkBlocks; dsimp only
  have hab : (a ++ b).length / 128 = k + m := by rw [List.length_append, ha, hb]; omega
  have ha_div : a.length / 128 = k := by rw [ha]; omega
  have hb_div : b.length / 128 = m := by rw [hb]; omega
  rw [hab, ha_div, hb_div, list_range_add k m, List.map_append, List.map_map]; congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi; have hle : i * 128 + 128 ≤ a.length := by rw [ha]; omega
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · apply List.map_congr_left
    intro i _
    have hmul : (k + i) * 128 = a.length + i * 128 := by rw [ha, Nat.add_mul]
    simp only [Function.comp_apply, hmul, ← List.drop_drop, List.drop_left]
theorem sha512Ref_of_length_1633 (P : Primitives) {blk0 blks1_11 tail97 : Bytes}
    (h0 : blk0.length = 128) (h11 : blks1_11.length = 1408) (ht : tail97.length = 97) :
    sha512Ref P (blk0 ++ blks1_11 ++ tail97) =
      let st0 := revWords64 sha512InitState
      let st1 := sha512CompressOutBytes P st0 blk0; let st2 := sha512CompressOutBytes P st1 blks1_11
      let padBlk := tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 1633
      revWords64 (sha512CompressOutBytes P st2 padBlk) := by
  dsimp only; have hinit_len : sha512InitState.length = 64 := rfl
  have hst0_len : (revWords64 sha512InitState).length = 64 := revWords64_length hinit_len
  have hst1_len : (sha512CompressOutBytes P (revWords64 sha512InitState) blk0).length = 64 :=
    sha512CompressOutBytes_length P _ _
  have hst2_len : (sha512CompressOutBytes P (sha512CompressOutBytes P (revWords64 sha512InitState)
    blk0) blks1_11).length = 64 := sha512CompressOutBytes_length P _ _
  rw [revWords64_sha512CompressOutBytes_of_len P hst2_len,
    revWords64_sha512CompressOutBytes_of_len P hst1_len,
    revWords64_sha512CompressOutBytes_of_len P hst0_len,
    revWords64_involutive hinit_len, ← List.foldl_append, ← List.foldl_append]
  have hpad_len : (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 1633).length =
    1 * 128 := by
    simp [encodeBitLen128BE, encodeBitLen64BE, ht]
  have h011_len : (blk0 ++ blks1_11).length = 12 * 128 := by simp [h0, h11]
  rw [← List.append_assoc (chunkBlocks 128 blk0),
    ← chunkBlocks_128_append (a := blk0) (b := blks1_11) 1 11 (by omega) (by omega),
    ← chunkBlocks_128_append 12 1 h011_len hpad_len]
  have htot_len : (blk0 ++ blks1_11 ++ tail97).length = 1633 := by simp [h0, h11, ht]
  have hpad_eq : sha512Pad (blk0 ++ blks1_11 ++ tail97) =
      (blk0 ++ blks1_11) ++ (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 1633) :=
        by
    unfold sha512Pad; rw [htot_len]; simp [List.append_assoc]
  rw [← hpad_eq]; unfold sha512Ref
  rw [fitBytesRef_of_length_eq (foldl_sha512Step_length P _ _ hinit_len)]
theorem unpack64_rev64_eq_reverse (w : BitVec 64) : unpack64 (rev64 w) = (unpack64 w).reverse := by
  simp only [unpack64, rev64, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.cons.injEq, and_true]
  generalize w.extractLsb' 0 8 = b0
  generalize w.extractLsb' 8 8 = b1
  generalize w.extractLsb' 16 8 = b2
  generalize w.extractLsb' 24 8 = b3
  generalize w.extractLsb' 32 8 = b4
  generalize w.extractLsb' 40 8 = b5
  generalize w.extractLsb' 48 8 = b6
  generalize w.extractLsb' 56 8 = b7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits
theorem bytesToBv8_reverse (bs : Bytes) : bytesToBv8 bs.reverse = (bytesToBv8 bs).reverse := by
  simp [bytesToBv8, List.map_reverse]
def unpackL (ws : List (BitVec 64)) : List (BitVec 8) := ws.flatMap unpack64
theorem pointsToBytes_unpack8 (a w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    (a ↦ₛ unpackL [w0, w1, w2, w3, w4, w5, w6, w7]) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
        ((a + 56#64) ↦₆₄ w7)) := by
  simp only [unpackL, List.flatMap_cons, List.flatMap_nil, List.append_nil, pointsToBytes_append,
    unpack64_length, ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]
theorem exists_unpackL8_revWords64 {bs : Bytes} (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64,
      bytesToBv8 bs = unpackL [w0, w1, w2, w3, w4, w5, w6, w7] ∧ bytesToBv8 (revWords64 bs) =
        unpackL [rev64 w0, rev64 w1, rev64 w2, rev64 w3, rev64 w4, rev64 w5, rev64 w6, rev64 w7] :=
        by
  have h0 : (bytesToBv8 (bs.take 8)).length = 8 := by simp [bytesToBv8, h]
  have h1 : (bytesToBv8 ((bs.drop 8).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h2 : (bytesToBv8 ((bs.drop 16).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h3 : (bytesToBv8 ((bs.drop 24).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h4 : (bytesToBv8 ((bs.drop 32).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h5 : (bytesToBv8 ((bs.drop 40).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h6 : (bytesToBv8 ((bs.drop 48).take 8)).length = 8 := by simp [bytesToBv8, h]
  have h7 : (bytesToBv8 ((bs.drop 56).take 8)).length = 8 := by simp [bytesToBv8, h]
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 h0
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 h1
  obtain ⟨w2, hw2⟩ := exists_unpack64_of_length_8 h2
  obtain ⟨w3, hw3⟩ := exists_unpack64_of_length_8 h3
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 h4
  obtain ⟨w5, hw5⟩ := exists_unpack64_of_length_8 h5
  obtain ⟨w6, hw6⟩ := exists_unpack64_of_length_8 h6
  obtain ⟨w7, hw7⟩ := exists_unpack64_of_length_8 h7
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, ?_, ?_⟩
  · conv => lhs; arg 1; rw [list_split8_64 bs h]
    simp only [bytesToBv8_append, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      unpackL, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · unfold revWords64
    simp only [bytesToBv8_append, bytesToBv8_reverse, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      ← unpack64_rev64_eq_reverse,
      unpackL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
theorem exists_unpack64_revWords64_of_length_64 {bs : Bytes} (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64, (∀ a : BitVec 64, (a ↦ₛ bytesToBv8 bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
            ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
            ((a + 56#64) ↦₆₄ w7))) ∧ (∀ b : BitVec 64, (b ↦ₛ bytesToBv8 (revWords64 bs)) =
          ((b ↦₆₄ rev64 w0) ∗ ((b + 8#64) ↦₆₄ rev64 w1) ∗ ((b + 16#64) ↦₆₄ rev64 w2) ∗
            ((b + 24#64) ↦₆₄ rev64 w3) ∗ ((b + 32#64) ↦₆₄ rev64 w4) ∗ ((b + 40#64) ↦₆₄ rev64 w5) ∗
            ((b + 48#64) ↦₆₄ rev64 w6) ∗ ((b + 56#64) ↦₆₄ rev64 w7))) := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hbs, hrev⟩ := exists_unpackL8_revWords64 h
  exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => by rw [hbs, pointsToBytes_unpack8],
    fun b => by rw [hrev, pointsToBytes_unpack8]⟩
def first7 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8]
def last7 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]
theorem cell_split7 (a v : BitVec 64) :
    (a ↦₆₄ v) = ((a ↦ₛ first7 v) ∗ ((a + 7#64) ↦₈ v.extractLsb' 56 8)) := by
  rw [pointsTo64_eq_pointsToBytes, show unpack64 v = first7 v ++ [v.extractLsb' 56 8] from rfl,
    pointsToBytes_append, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  rfl
theorem cell_split1 (a v : BitVec 64) :
    (a ↦₆₄ v) = ((a ↦₈ v.extractLsb' 0 8) ∗ ((a + 1#64) ↦ₛ last7 v)) := by
  rw [pointsTo64_eq_pointsToBytes, show unpack64 v = v.extractLsb' 0 8 :: last7 v from rfl,
    pointsToBytes_cons]
theorem cell_pack1 (a : BitVec 64) (b0 : BitVec 8) : (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64, ⌜w.extractLsb' 0 8 = b0⌝ ∗ (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes (a + 1#64) 7 (by decide)]
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine Entails.sepExists_elim fun junk => Entails.pure_left fun hj => ?_
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := b0 :: junk) (by simp [hj])
  have hext : w.extractLsb' 0 8 = b0 := by
    have h := congrArg (fun l => l.getD 0 0#8) hw; simp [unpack64] at h; exact h.symm
  refine Entails.sepExists_right w (Entails.pure_right hext ?_)
  rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_cons]; exact Entails.refl _
theorem cell_pack7 (a : BitVec 64) (b7 : BitVec 8) : memRegion a 7 ∗ ((a + 7#64) ↦₈ b7) ⊢
      ∃∗ w : BitVec 64, ⌜w.extractLsb' 56 8 = b7⌝ ∗ (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes a 7 (by decide)]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Entails.sepExists_elim fun junk => Entails.pure_left fun hj => ?_
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := junk ++ [b7]) (by simp [hj])
  have hext : w.extractLsb' 56 8 = b7 := by
    have h := congrArg (fun l => l.drop 7) hw; rw [List.drop_left' hj] at h; simp [unpack64] at h
    exact h.symm
  refine Entails.sepExists_right w (Entails.pure_right hext ?_)
  rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_append, hj, pointsToBytes_cons,
    pointsToBytes_nil, sepConj_emp]
  exact Entails.refl _
theorem list_capS_split {sig : Bytes} (hsig : sig.length = 64) :
    (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F] =
      (sig.drop 32).take 15 ++ ((sig.drop 47).take 16 ++ [sig.getD 63 0 &&& 0x7F]) := by
  rcases sig with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | ⟨b32, _ | ⟨b33, _ | ⟨b34, _ | ⟨b35, _ | ⟨b36, _ | ⟨b37, _ | ⟨b38, _ | ⟨b39,
    _ | ⟨b40, _ | ⟨b41, _ | ⟨b42, _ | ⟨b43, _ | ⟨b44, _ | ⟨b45, _ | ⟨b46, _ | ⟨b47,
    _ | ⟨b48, _ | ⟨b49, _ | ⟨b50, _ | ⟨b51, _ | ⟨b52, _ | ⟨b53, _ | ⟨b54, _ | ⟨b55,
    _ | ⟨b56, _ | ⟨b57, _ | ⟨b58, _ | ⟨b59, _ | ⟨b60, _ | ⟨b61, _ | ⟨b62, _ | ⟨b63, _ |
      _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at hsig)
  rfl
theorem uint8_and7f_bv8 (u : UInt8) :
    (BitVec.ofNat 8 u.toNat) &&& 0x7f#8 = BitVec.ofNat 8 (u &&& 0x7F).toNat := by
  rcases u with ⟨bv⟩; revert bv; decide
theorem bytesToBv8_getD_eq (bs : Bytes) (i : Nat) :
    (bytesToBv8 bs).getD i 0#8 = BitVec.ofNat 8 (bs.getD i 0).toNat := by
  induction bs generalizing i with
  | nil => simp [bytesToBv8]
  | cons b rest ih =>
    cases i with
    | zero => simp [bytesToBv8]
    | succ j => exact ih j
theorem exists_sig_capS_cells {sig : Bytes} (hsig : sig.length = 64) :
    ∃ q0_lo q0_hi q1_lo q1_hi : BitVec 64, (∀ p : BitVec 64, (p ↦ₛ bytesToBv8 sig) =
          ((p ↦ₛ bytesToBv8 (sig.take 32)) ∗ ((p + 32#64) ↦₆₄ q0_lo) ∗ ((p + 40#64) ↦₆₄ q0_hi) ∗
           ((p + 48#64) ↦ₛ bytesToBv8 (sig.drop 48)))) ∧ (∀ p : BitVec 64, (p ↦ₛ bytesToBv8 sig) =
          ((p ↦ₛ bytesToBv8 (sig.take 47)) ∗ ((p + 47#64) ↦₆₄ q1_lo) ∗ ((p + 55#64) ↦₆₄ q1_hi) ∗
           ((p + 63#64) ↦ₛ bytesToBv8 (sig.drop 63)))) ∧ (∀ a : BitVec 64,
        ((a ↦₆₄ q0_lo) ∗ ((a + 8#64) ↦₆₄ q0_hi)) ∗ memRegion (a + 16#64) 15 ⊢
          (a ↦ₛ bytesToBv8 ((sig.drop 32).take 15)) ∗
          (∃∗ v0, (a + 15#64) ↦₆₄ v0) ∗ (∃∗ v1, (a + 23#64) ↦₆₄ v1)) ∧ (∀ a : BitVec 64,
        (a ↦ₛ bytesToBv8 ((sig.drop 32).take 15)) ∗
          ((a + 15#64) ↦₆₄ q1_lo) ∗ ((a + 23#64) ↦₆₄ q1_hi) ∗
          ((a + 31#64) ↦₈ ((bytesToBv8 sig).getD 63 0#8 &&& 0x7f#8)) =
          (a ↦ₛ bytesToBv8 ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]))) := by
  have h16a : (bytesToBv8 ((sig.drop 32).take 16)).length = 16 := by simp [bytesToBv8, hsig]
  have h16b : (bytesToBv8 ((sig.drop 47).take 16)).length = 16 := by simp [bytesToBv8, hsig]
  obtain ⟨q0_lo, q0_hi, hq0_eq, hq0_pts⟩ := exists_unpack64_of_length_16 h16a
  obtain ⟨q1_lo, q1_hi, hq1_eq, hq1_pts⟩ := exists_unpack64_of_length_16 h16b
  refine ⟨q0_lo, q0_hi, q1_lo, q1_hi, fun p => ?_, fun p => ?_, fun a => ?_, fun a => ?_⟩
  · have hsp : sig = sig.take 32 ++ ((sig.drop 32).take 16 ++ sig.drop 48) := by
      rw [show (48 : Nat) = 32 + 16 from rfl, ←
        List.drop_drop, List.take_append_drop, List.take_append_drop]
    conv => lhs; arg 2; arg 1; rw [hsp]
    have ht32 : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
    simp only [bytesToBv8_append, pointsToBytes_append, ht32, h16a, hq0_pts,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · have hsp : sig = sig.take 47 ++ ((sig.drop 47).take 16 ++ sig.drop 63) := by
      rw [show (63 : Nat) = 47 + 16 from rfl, ←
        List.drop_drop, List.take_append_drop, List.take_append_drop]
    conv => lhs; arg 2; arg 1; rw [hsp]
    have ht47 : (bytesToBv8 (sig.take 47)).length = 47 := by simp [bytesToBv8, hsig]
    simp only [bytesToBv8_append, pointsToBytes_append, ht47, h16b, hq1_pts,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · rw [← hq0_pts a]
    have hsp16 : (sig.drop 32).take 16 = (sig.drop 32).take 15 ++ ((sig.drop 32).drop 15).take 1 :=
      by
      rw [show (16 : Nat) = 15 + 1 from rfl, List.take_add]
    have ht15 : (bytesToBv8 ((sig.drop 32).take 15)).length = 15 := by simp [bytesToBv8, hsig]
    have hd1 : (bytesToBv8 (((sig.drop 32).drop 15).take 1)).length = 1 := by
      simp [bytesToBv8, hsig]
    rw [hsp16, bytesToBv8_append, pointsToBytes_append, ht15, sepConj_assoc]
    refine sepConj_mono_right ?_
    refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion _ _)) ?_
    rw [hd1, ← ProofLib.memRegion_split' (b := a + 15#64) (n := 1) (k := 15) (b' :=
      a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 15#64) (n := 8) (k := 8) (b' :=
        a + 23#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    exact Entails.refl _
  · symm
    rw [list_capS_split hsig]
    have ht15 : (bytesToBv8 ((sig.drop 32).take 15)).length = 15 := by simp [bytesToBv8, hsig]
    have hq1_at : ((a + 15#64) ↦ₛ bytesToBv8 ((sig.drop 47).take 16)) =
        (((a + 15#64) ↦₆₄ q1_lo) ∗ ((a + 23#64) ↦₆₄ q1_hi)) := by
      have := hq1_pts (a + 15#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at this
      exact this
    rw [bytesToBv8_append, bytesToBv8_append,
      pointsToBytes_append, pointsToBytes_append, ht15, h16b, hq1_at,
      bytesToBv8_getD_eq, uint8_and7f_bv8]
    simp only [bytesToBv8, List.map_cons, List.map_nil, pointsToBytes_cons, pointsToBytes_nil,
      sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem blockBuf_tail32_pack (q : BitVec 64) (b0 b7 : BitVec 8) :
    (q ↦₈ b0) ∗ memRegion (q + 1#64) 30 ∗ ((q + 31#64) ↦₈ b7) ⊢ ∃∗ b12, ∃∗ b13, ∃∗ b14, ∃∗ b15,
        ⌜b12.extractLsb' 0 8 = b0 ∧ b15.extractLsb' 56 8 = b7⌝ ∗
        ((q ↦₆₄ b12) ∗ ((q + 8#64) ↦₆₄ b13) ∗ ((q + 16#64) ↦₆₄ b14) ∗ ((q + 24#64) ↦₆₄ b15)) := by
  rw [ProofLib.memRegion_eq_exists_bytes (q + 1#64) 30 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun junk => ?_; rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hj => ?_; have h31 : (b0 :: junk).length = 31 := by simp [hj]
  obtain ⟨b12, b13, b14, b15, hw, hp⟩ := exists_unpack64_of_length_32
    (bs := (b0 :: junk) ++ [b7]) (by simp [hj])
  have hb12 : b12.extractLsb' 0 8 = b0 := by
    have h := congrArg (fun l => l.getD 0 0#8) hw; simp [unpack64] at h; exact h.symm
  have hb15 : b15.extractLsb' 56 8 = b7 := by
    have h := congrArg (fun l => l.drop 31) hw; rw [List.drop_left' h31] at h; simp [unpack64] at h
    exact h.symm
  refine Entails.sepExists_right b12 (Entails.sepExists_right b13
    (Entails.sepExists_right b14 (Entails.sepExists_right b15 (Entails.pure_right ⟨hb12,
      hb15⟩ ?_))))
  have hpq := hp q; simp only [pointsToBytes_append, h31, pointsToBytes_cons,
    pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, sepConj_assoc] at hpq
  rw [← hpq]
  exact Entails.refl _
theorem blockBuf_tail32_unpack (q b12 b13 b14 b15 : BitVec 64) (b0 b7 : BitVec 8)
    (hb12 : b12.extractLsb' 0 8 = b0) : (q ↦₆₄ b12) ∗ ((q + 8#64) ↦₆₄ b13) ∗ ((q + 16#64) ↦₆₄ b14) ∗
      ((q + 24#64) ↦ₛ first7 b15) ∗ ((q + 31#64) ↦₈ b7) ⊢
      (q ↦₈ b0) ∗ (∃∗ c, (q + 1#64) ↦₈ c) ∗ memRegion (q + 2#64) 30 := by
  rw [cell_split1 q b12, hb12, sepConj_assoc]
  refine sepConj_mono_right ?_
  have hl7 : (last7 b12).length = 7 := rfl
  have hf7 : (first7 b15).length = 7 := rfl
  have hm12 : ((q + 1#64) ↦ₛ last7 b12) ⊢ memRegion (q + 1#64) 7 := by
    rw [← hl7]; exact pointsToBytes_entails_memRegion _ _
  have hm15 : ((q + 24#64) ↦ₛ first7 b15) ⊢ memRegion (q + 24#64) 7 := by
    rw [← hf7]; exact pointsToBytes_entails_memRegion _ _
  have hm31 : ((q + 31#64) ↦₈ b7) ⊢ memRegion (q + 31#64) 1 := by
    rw [ProofLib.memRegion_one]; exact Entails.sepExists_intro b7
  refine Entails.trans (sepConj_mono hm12 (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono hm15 hm31)))) ?_
  rw [← ProofLib.memRegion_split' (b := q + 24#64) (n := 7) (k := 1) (b' :=
    q + 31#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := q + 16#64) (n := 8) (k := 8) (b' :=
      q + 24#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := q + 8#64) (n := 8) (k := 16) (b' :=
      q + 16#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := q + 1#64) (n := 7) (k := 24) (b' :=
      q + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := q + 1#64) (n := 1) (k := 30) (b' :=
      q + 2#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
  exact Entails.refl _
theorem unpack64_encodeBitLen128BE {L : Nat} (hL : L = 97 ∨ L = 1633) (r : BitVec 64) :
    ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ rev64 (BitVec.ofNat 64 (8 * L)))) =
      (r ↦ₛ bytesToBv8 (encodeBitLen128BE L)) := by
  have heq : unpack64 0#64 ++ unpack64 (rev64 (BitVec.ofNat 64 (8 * L))) =
      bytesToBv8 (encodeBitLen128BE L) := by
    rcases hL with rfl | rfl <;> decide
  rw [← heq, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes]
theorem exists_pad97_cells {tail97 : Bytes} (ht : tail97.length = 97) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 p12 p13 : BitVec 64, (∀ p : BitVec 64,
        (p ↦ₛ bytesToBv8 tail97) =
          ((p ↦₆₄ b0) ∗ ((p + 8#64) ↦₆₄ b1) ∗ ((p + 16#64) ↦₆₄ b2) ∗ ((p + 24#64) ↦₆₄ b3) ∗
           ((p + 32#64) ↦₆₄ b4) ∗ ((p + 40#64) ↦₆₄ b5) ∗ ((p + 48#64) ↦₆₄ b6) ∗ ((p +
           56#64) ↦₆₄ b7) ∗
           ((p + 64#64) ↦₆₄ b8) ∗ ((p + 72#64) ↦₆₄ b9) ∗ ((p + 80#64) ↦₆₄ b10) ∗ ((p +
           88#64) ↦₆₄ b11) ∗ ((p + 96#64) ↦₈ (bytesToBv8 tail97).getD 96 0#8))) ∧ (∀ q : BitVec 64,
        (q ↦₈ (bytesToBv8 tail97).getD 96 0#8) ∗ ((q + 1#64) ↦₈ 128#8) ∗
          ((q + 2#64) ↦ₛ List.replicate 30 0#8) =
          ((q ↦₆₄ p12) ∗ ((q + 8#64) ↦₆₄ p13) ∗ ((q + 16#64) ↦₆₄ 0#64) ∗ ((q + 24#64) ↦₆₄ 0#64))) ∧
      (∀ (r : BitVec 64) {L : Nat}, (L = 97 ∨ L = 1633) →
        ((r ↦₆₄ b0) ∗ ((r + 8#64) ↦₆₄ b1) ∗ ((r + 16#64) ↦₆₄ b2) ∗ ((r + 24#64) ↦₆₄ b3) ∗
         ((r + 32#64) ↦₆₄ b4) ∗ ((r + 40#64) ↦₆₄ b5) ∗ ((r + 48#64) ↦₆₄ b6) ∗ ((r + 56#64) ↦₆₄ b7) ∗
         ((r + 64#64) ↦₆₄ b8) ∗ ((r + 72#64) ↦₆₄ b9) ∗ ((r + 80#64) ↦₆₄ b10) ∗ ((r +
         88#64) ↦₆₄ b11) ∗ ((r + 96#64) ↦₆₄ p12) ∗ ((r + 104#64) ↦₆₄ p13) ∗
         ((r + 112#64) ↦₆₄ 0#64) ∗ ((r + 120#64) ↦₆₄ rev64 (BitVec.ofNat 64 (8 * L)))) =
          (r ↦ₛ bytesToBv8 (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L))) := by
  have h64 : (bytesToBv8 (tail97.take 64)).length = 64 := by simp [bytesToBv8, ht]
  have h32 : (bytesToBv8 ((tail97.drop 64).take 32)).length = 32 := by simp [bytesToBv8, ht]
  have h16 : (bytesToBv8 ([tail97.getD 96 0, 0x80] ++ List.replicate 14 0)).length = 16 := by
    simp [bytesToBv8]
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb07⟩ := exists_unpack64_of_length_64 h64
  obtain ⟨b8, b9, b10, b11, _, hb811⟩ := exists_unpack64_of_length_32 h32
  obtain ⟨p12, p13, _, hp1213⟩ := exists_unpack64_of_length_16 h16
  have ht96_drop : tail97.drop 96 = [tail97.getD 96 0] := by
    rcases hp : tail97.drop 96 with _ | ⟨x, _ | ⟨y, _⟩⟩
    · have := congrArg List.length hp; simp [ht] at this
    · have hget : (tail97.drop 96).getD 0 0 = tail97.getD 96 0 := by
        simp [List.getD_eq_getElem?_getD]
      rw [hp] at hget; simp at hget; rw [hget]; rfl
    · have := congrArg List.length hp; simp [ht] at this
  have hsp97 : tail97 = tail97.take 64 ++ ((tail97.drop 64).take 32 ++ [tail97.getD 96 0]) := by
    rw [← ht96_drop, show (96 : Nat) = 64 + 32 from rfl, ← List.drop_drop,
      List.take_append_drop, List.take_append_drop]
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, p12, p13, fun p => ?_, fun q =>
    ?_, fun r L hL => ?_⟩
  · conv => lhs; arg 2; arg 1; rw [hsp97]
    simp only [bytesToBv8_append, pointsToBytes_append, h64, h32, hb07, hb811,
      bytesToBv8_getD_eq, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    simp only [bytesToBv8, List.map_cons, List.map_nil, pointsToBytes_cons, pointsToBytes_nil,
      sepConj_emp]
  · have hrep30 : List.replicate 30 (0#8 : BitVec 8) = List.replicate 14 0#8 ++ (unpack64 0#64 ++
      unpack64 0#64) := by decide
    have hp1213_q : (q ↦₈ (bytesToBv8 tail97).getD 96 0#8) ∗ ((q + 1#64) ↦₈ 128#8) ∗
        ((q + 2#64) ↦ₛ List.replicate 14 0#8) = ((q ↦₆₄ p12) ∗ ((q + 8#64) ↦₆₄ p13)) := by
      rw [← hp1213 q, bytesToBv8_getD_eq]
      have hmap14 : bytesToBv8 (List.replicate 14 0) = List.replicate 14 0#8 := by decide
      simp only [bytesToBv8_append, hmap14]
      simp only [bytesToBv8, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        pointsToBytes_cons, BitVec.add_assoc, BitVec.reduceAdd]; rfl
    rw [hrep30, pointsToBytes_append, show (List.replicate 14 (0#8 : BitVec 8)).length = 14 from
      rfl, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes, ←
        pointsTo64_eq_pointsToBytes]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
    rw [sepConj_assoc (q ↦₈ _), hp1213_q]
  · symm
    have hsp_pad : tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L =
        tail97.take 64 ++ ((tail97.drop 64).take 32 ++
          (([tail97.getD 96 0, 0x80] ++ List.replicate 14 0) ++ encodeBitLen128BE L)) := by
      conv => lhs; arg 1; arg 1; arg 1; rw [hsp97]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hsp_pad, bytesToBv8_append, bytesToBv8_append, bytesToBv8_append,
      pointsToBytes_append, h64, pointsToBytes_append, h32, pointsToBytes_append, h16,
      hb07, hb811, hp1213, ← unpack64_encodeBitLen128BE hL]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  libsignalSessionCode_fnOff_0x3de58
theorem cells_16_merge (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗
      ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ∗ ((a + 96#64) ↦₆₄ v12) ∗
      ((a + 104#64) ↦₆₄ v13) ∗ ((a + 112#64) ↦₆₄ v14) ∗ ((a + 120#64) ↦₆₄ v15) ⊢ cells a 16 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <|
    Entails.sepExists_right v2 <| Entails.sepExists_right v3 <|
    Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <|
    Entails.sepExists_right v8 <| Entails.sepExists_right v9 <|
    Entails.sepExists_right v10 <| Entails.sepExists_right v11 <|
    Entails.sepExists_right v12 <| Entails.sepExists_right v13 <|
    Entails.sepExists_right v14 <| Entails.sepExists_right v15 <| Entails.refl _
theorem first7_pack (a v : BitVec 64) (b7 : BitVec 8) :
    ((a ↦ₛ first7 v) ∗ ((a + 7#64) ↦₈ b7)) ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) := by
  have hf7 : (first7 v).length = 7 := rfl
  have hm : (a ↦ₛ first7 v) ⊢ memRegion a 7 := by
    rw [← hf7]; exact pointsToBytes_entails_memRegion a (first7 v)
  refine Entails.trans (sepConj_mono_left hm) (Entails.trans (cell_pack7 a b7) ?_)
  exact Entails.sepExists_elim fun w => Entails.pure_left fun _ => Entails.sepExists_intro w
theorem fitBv8_64_sha512CompressOutBytes (P : Primitives) (st blk : Bytes) :
    fitBv8 64 (sha512CompressOutBytes P st blk) = bytesToBv8 (sha512CompressOutBytes P st blk) := by
  have hlen : (bytesToBv8 (sha512CompressOutBytes P st blk)).length = 64 := by
    simp [bytesToBv8, sha512CompressOutBytes_length]
  simp [fitBv8, hlen, List.take_of_length_le (Nat.le_of_eq hlen)]
theorem fitBv8_of_length_eq {n : Nat} {bs : Bytes} (h : bs.length = n) :
    fitBv8 n bs = bytesToBv8 bs := by
  have hlen : (bytesToBv8 bs).length = n := by simp [bytesToBv8, h]
  simp [fitBv8, hlen, List.take_of_length_le (Nat.le_of_eq hlen)]
theorem sClamped_buf_pre (a v0 v1 v2 v3 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢
      (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ memRegion (a + 16#64) 15 ∗
      (∃∗ b31 : BitVec 8, (a + 31#64) ↦₈ b31) := by
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (pointsTo64_entails_memRegion _ _)) ?_
  rw [← ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' :=
    a + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 16#64) (n := 15) (k := 1) (b' :=
      a + 31#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
  exact Entails.refl _
theorem stackAt_hook_split_48 (sp : BitVec 64) : stackAt sp pqxdhHookStack =
      memRegion (sp - 4096#64) 4048 ∗ cells (sp - 48#64) 6 := by
  simp only [stackAt, pqxdhHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 4096) (n := 4048) (k := 48)
      (b' := sp - 48#64) rfl (by bv_omega) (by decide),
    (memRegion_cells (sp - 48#64) 6 (by decide) : memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]
theorem pointsToBytes_32_merge_128 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) ∗ memRegion (a + 32#64) 128 ⊢ memRegion a 160 := by
  have hm : (a ↦ₛ bs) ⊢ memRegion a 32 := by rw [← h]; exact pointsToBytes_entails_memRegion a bs
  refine Entails.trans (sepConj_mono_left hm) ?_
  rw [← ProofLib.memRegion_split' (b := a) (n := 32) (k := 128) (b' :=
    a + 32#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _
theorem sig_split_32 (p : BitVec 64) {sig : Bytes} (hsig : sig.length = 64) :
    (p ↦ₛ bytesToBv8 sig) =
      ((p ↦ₛ bytesToBv8 (sig.take 32)) ∗ ((p + 32#64) ↦ₛ bytesToBv8 (sig.drop 32))) := by
  conv => lhs; arg 2; arg 1; rw [← List.take_append_drop 32 sig]
  have ht32 : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
  rw [bytesToBv8_append, pointsToBytes_append, ht32]
@[local simp, local wp_norm, local arm64_norm]
theorem and64_mask255_ite_1_0 (p : Prop) [Decidable p] :
    ((if p then 1#64 else 0#64) &&& 4294967551#64) = if p then 1#64 else 0#64 := by
  by_cases hp : p <;> simp [hp]
@[local simp, local wp_norm, local arm64_norm]
theorem csinc_eq_zero32_ite_1_0 (p : Prop) [Decidable p] :
    (if (BitVec.setWidth 32 (if p then 1#64 else 0#64) == 0#32) = true then 0#64 else 1#64) =
      if p then 1#64 else 0#64 := by
  by_cases hp : p <;> simp [hp]
theorem truncate8_zeroExtend32_and7f (b : BitVec 8) :
    BitVec.truncate 8 (BitVec.zeroExtend 32 b &&& 0x7f#32) = b &&& 0x7f#8 := by revert b; decide
theorem pointsToBytes_entails_memRegion_n (a : BitVec 64) (bs : List (BitVec 8)) {n : Nat}
    (h : bs.length = n) : (a ↦ₛ bs) ⊢ memRegion a n := by
  subst h; exact pointsToBytes_entails_memRegion a bs
theorem x0_cteq_simplify (xs ys : Bytes) : (if (BitVec.truncate 32 ((if bytesToBv8 xs =
      bytesToBv8 ys then 1#64 else 0#64) &&& 1095216660735#64) == 0#32) = true
     then 0#64 else 1#64) = (if (xs == ys) = true then 1#64 else 0#64) := by
  by_cases h : xs = ys
  · subst h; simp
  · have hne : ¬ (bytesToBv8 xs = bytesToBv8 ys) := fun heq => h (bytesToBv8_inj heq)
    have hbeq : ¬ ((xs == ys) = true) := by rw [beq_iff_eq]; exact h
    simp only [hne, hbeq, ↓reduceIte]; decide

section WithProgramTrap
variable {C : Crypto}
local notation "PP" b:arg absHooks:arg => trTrapProgAt b C absHooks

theorem dalekCompressStub_ok_at_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekCompressStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafStubSpec P.compress 160 32) := hook_ok_at (hname := dalekCompressStub) rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [dalekCompressStub, dalekDoubleMulStub, dalekEdNegStub, dalekScalarModStub, dalekScalarWideStub, sha512CompressStub, Rust.isPanicSymbol])
    (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.dalekCompress)
theorem dalekEdNegStub_ok_at_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekEdNegStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafStubSpec P.edNeg 160 160) := hook_ok_at (hname := dalekEdNegStub) rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [dalekCompressStub, dalekDoubleMulStub, dalekEdNegStub, dalekScalarModStub, dalekScalarWideStub, sha512CompressStub, Rust.isPanicSymbol])
    (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.dalekEdNeg)
theorem sha512CompressStub_ok_at_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff sha512CompressStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (compressInPlaceStubSpec (sha512CompressOutBytes P) 64 128 img) :=
  hook_ok_at (hname := sha512CompressStub) rfl hk (by fnoff_eq) (by fnoff_eq) (by simp [dalekCompressStub, dalekDoubleMulStub, dalekEdNegStub, dalekScalarModStub, dalekScalarWideStub, sha512CompressStub, Rust.isPanicSymbol])
    (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.sha512Compress)
theorem dalekScalarWideStub_ok_at_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekScalarWideStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafStubSpec P.scalarFromWide 64 32) :=
  hook_ok_at (hname := dalekScalarWideStub) rfl hk (by fnoff_eq) (by fnoff_eq) (by simp [dalekCompressStub, dalekDoubleMulStub, dalekEdNegStub, dalekScalarModStub, dalekScalarWideStub, sha512CompressStub, Rust.isPanicSymbol])
    (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.dalekScalarWide)
theorem dalekScalarModStub_ok_at_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekScalarModStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafStubSpec P.scalarFromBytesModOrder 32 32) :=
  hook_ok_at (hname := dalekScalarModStub) rfl hk (by fnoff_eq) (by fnoff_eq) (by simp [dalekCompressStub, dalekDoubleMulStub, dalekEdNegStub, dalekScalarModStub, dalekScalarWideStub, sha512CompressStub, Rust.isPanicSymbol])
    (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.dalekScalarMod)
theorem dalekDoubleMulStub_ok_at_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekDoubleMulStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (dalekDoubleMulStubSpec P img) := hook_ok_at (hname := dalekDoubleMulStub) rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [dalekCompressStub, dalekDoubleMulStub, dalekEdNegStub, dalekScalarModStub, dalekScalarWideStub, sha512CompressStub, Rust.isPanicSymbol])
    (hookSat_tripleRatchetExterns'_trap C absHooks rfl hH.dalekDoubleMul)
theorem memcpy_region_ok_at_trap {b : BitVec 64} {absHooks : String → Option (State → State)}
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff memcpyName := by fnoff_eq) :
    subroutine_ok (PP b absHooks) ((PP b absHooks).fnAddr name + BitVec.ofNat 64 k)
      sessionMemcpyRegionSpec := session_memcpy_region_ok_at_trap b C absHooks name k hk
theorem memset_region_ok_at_trap {b : BitVec 64} {absHooks : String → Option (State → State)}
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff memsetName := by fnoff_eq) :
    subroutine_ok (PP b absHooks) ((PP b absHooks).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemsetSpec pqxdhHookStack) :=
  session_memset_ok_at_trap b C absHooks name k pqxdhHookStack (by decide) hk
theorem pqxdh_ct_eq_slice_ok_trap (b : BitVec 64) (absHooks : String → Option (State → State)) :
    subroutine_ok (PP b absHooks) ((PP b absHooks).fnAddr ConsumeMessageKeyTransfer.ctEqName)
      pqxdhCtEqSliceSpec := by
  rw [pqxdhCtEqSliceSpec_eq]; exact ctEq_ok_trap b C absHooks
theorem subroutine_ok_rel_pqxdh_trap {α : Type} {b : BitVec 64}
    {absHooks : String → Option (State → State)}
    {spec : Spec α} {callee name : String} {offc off k : Nat}
    (h : subroutine_ok (PP b absHooks) ((PP b absHooks).fnAddr callee) spec)
    (hc : libsignalSessionCode.fnOff callee = offc) (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = offc) : subroutine_ok (PP b absHooks)
      ((PP b absHooks).fnAddr name + BitVec.ofNat 64 k) spec := by
  have hrel : (PP b absHooks).fnAddr callee = (PP b absHooks).fnAddr name + BitVec.ofNat 64 k := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hc, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, hk, ← hk, Nat.mod_mod]
  rwa [hrel] at h
theorem verifySig_seg2_1569_trap (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 1569) (hst0 : st0.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 320#64)
    (hsp : s.sp = fsp) (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = 1#64) : SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame) (fun sm Pm => (Pm ⊢
          (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (m.drop 1472)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8
            (sha512CompressOutBytes P (sha512CompressOutBytes P st0 (pre64 ++
            m.take 64)) ((m.drop 64).take 1408))) ∗ ((fsp + 752#64) ↦₆₄ 12#64) ∗
          ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym = 0x3de58 :=
    libsignalSessionCode_fnOff_0x3de58
  have hmemcpy := memcpy_region_ok_at_trap (b := img.base) (absHooks := absHooks)
    (name := verifySignatureMultipartSym) (C := C) (k := num% (ls_off% "memcpy" - 0x3de58))
  have hsha := sha512CompressStub_ok_at_trap hH
    (name := verifySignatureMultipartSym) (C := C) (k := num% (ls_off% "sha2::sha512::compress512" - 0x3de58))
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    320) hfn (by decide) verifySignatureMultipart_decode_0x3df98
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    324) hfn (by decide) verifySignatureMultipart_decode_0x3df9c
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    328) hfn (by decide) verifySignatureMultipart_decode_0x3dfa0
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    332) hfn (by decide) verifySignatureMultipart_decode_0x3dfa4
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    336) hfn (by decide) verifySignatureMultipart_decode_0x3dfa8
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    340) hfn (by decide) verifySignatureMultipart_decode_0x3dfac
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    344) hfn (by decide) verifySignatureMultipart_decode_0x3dfb0
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    348) hfn (by decide) verifySignatureMultipart_decode_0x3dfb4
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    352) hfn (by decide) verifySignatureMultipart_decode_0x3dfb8
  have f9 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    356) hfn (by decide) verifySignatureMultipart_decode_0x3dfbc
  have f10 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    360) hfn (by decide) verifySignatureMultipart_decode_0x3dfc0
  have f11 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    364) hfn (by decide) verifySignatureMultipart_decode_0x3dfc4
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    368) hfn (by decide) verifySignatureMultipart_decode_0x3dfc8
  have f13 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    372) hfn (by decide) verifySignatureMultipart_decode_0x3dfcc
  have f14 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    376) hfn (by decide) verifySignatureMultipart_decode_0x3dfd0
  have f15 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    380) hfn (by decide) verifySignatureMultipart_decode_0x3dfd4
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    384) hfn (by decide) verifySignatureMultipart_decode_0x3dfd8
  have f17 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    388) hfn (by decide) verifySignatureMultipart_decode_0x3dfdc
  have f18 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    392) hfn (by decide) verifySignatureMultipart_decode_0x3dfe0
  have f19 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    396) hfn (by decide) verifySignatureMultipart_decode_0x3dfe4
  have f20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    400) hfn (by decide) verifySignatureMultipart_decode_0x3dfe8
  have f21 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    404) hfn (by decide) verifySignatureMultipart_decode_0x3dfec
  have f22 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    408) hfn (by decide) verifySignatureMultipart_decode_0x3dff0
  have f23 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    412) hfn (by decide) verifySignatureMultipart_decode_0x3dff4
  have f24 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    416) hfn (by decide) verifySignatureMultipart_decode_0x3dff8
  have f25 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    420) hfn (by decide) verifySignatureMultipart_decode_0x3dffc
  have f26 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    424) hfn (by decide) verifySignatureMultipart_decode_0x3e000
  have f27 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    428) hfn (by decide) verifySignatureMultipart_decode_0x3e004
  have f28 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    432) hfn (by decide) verifySignatureMultipart_decode_0x3e008
  have f29 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    436) hfn (by decide) verifySignatureMultipart_decode_0x3e00c
  have f30 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    440) hfn (by decide) verifySignatureMultipart_decode_0x3e010
  have f31 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    444) hfn (by decide) verifySignatureMultipart_decode_0x3e014
  have f32 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    448) hfn (by decide) verifySignatureMultipart_decode_0x3e018
  have f33 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    452) hfn (by decide) verifySignatureMultipart_decode_0x3e01c
  have f34 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    456) hfn (by decide) verifySignatureMultipart_decode_0x3e020
  have f35 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    460) hfn (by decide) verifySignatureMultipart_decode_0x3e024
  have f36 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    464) hfn (by decide) verifySignatureMultipart_decode_0x3e028
  have f37 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    468) hfn (by decide) verifySignatureMultipart_decode_0x3e02c
  have f38 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    472) hfn (by decide) verifySignatureMultipart_decode_0x3e030
  have f39 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    476) hfn (by decide) verifySignatureMultipart_decode_0x3e034
  have f40 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    480) hfn (by decide) verifySignatureMultipart_decode_0x3e038
  have f41 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    484) hfn (by decide) verifySignatureMultipart_decode_0x3e03c
  have f42 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    488) hfn (by decide) verifySignatureMultipart_decode_0x3e040
  have f43 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    492) hfn (by decide) verifySignatureMultipart_decode_0x3e044
  have f44 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    496) hfn (by decide) verifySignatureMultipart_decode_0x3e048
  have f45 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    500) hfn (by decide) verifySignatureMultipart_decode_0x3e04c
  have f46 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    504) hfn (by decide) verifySignatureMultipart_decode_0x3e050
  have f47 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    508) hfn (by decide) verifySignatureMultipart_decode_0x3e054
  have f48 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    512) hfn (by decide) verifySignatureMultipart_decode_0x3e058
  have f49 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    516) hfn (by decide) verifySignatureMultipart_decode_0x3e05c
  have f50 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    520) hfn (by decide) verifySignatureMultipart_decode_0x3e060
  have f51 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    524) hfn (by decide) verifySignatureMultipart_decode_0x3e064
  have f52 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    528) hfn (by decide) verifySignatureMultipart_decode_0x3e068
  have f53 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    532) hfn (by decide) verifySignatureMultipart_decode_0x3e06c
  have f54 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    536) hfn (by decide) verifySignatureMultipart_decode_0x3e070
  have f55 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    540) hfn (by decide) verifySignatureMultipart_decode_0x3e074
  have f56 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    544) hfn (by decide) verifySignatureMultipart_decode_0x3e078
  dsimp only [trTrapProgAt] at hmemcpy hsha hpc ⊢
  clear hfn hH
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureMultipartSym =
      entry
  examples_hide_fetches
  have hlen_m64_bv : (bytesToBv8 (m.take 64)).length = 64 := by simp [bytesToBv8, hm]
  have hlen_m1408 : ((m.drop 64).take 1408).length = 128 * 11 := by simp [hm]
  have hlen_m1408_bv : (bytesToBv8 ((m.drop 64).take 1408)).length = 1408 := by
    simp [bytesToBv8, hm]
  have hlen_m97_bv : (bytesToBv8 (m.drop 1472)).length = 97 := by simp [bytesToBv8, hm]
  have hlen_pre_bv : (bytesToBv8 pre64).length = 64 := by simp [bytesToBv8, hpre64]
  have hlen_blk0 : (pre64 ++ m.take 64).length = 128 * 1 := by simp [hpre64, hm]
  have hlen_blk0_bv : (bytesToBv8 (pre64 ++ m.take 64)).length = 128 := by
    simp [bytesToBv8, hpre64, hm]
  have hst1_len : (sha512CompressOutBytes P st0 (pre64 ++ m.take 64)).length = 64 :=
    sha512CompressOutBytes_length P _ _
  have hm_split : msgPtr ↦ₛ bytesToBv8 m = ((msgPtr ↦ₛ bytesToBv8 (m.take 64)) ∗
       ((msgPtr + 64#64) ↦ₛ bytesToBv8 ((m.drop 64).take 1408)) ∗
       ((msgPtr + 1472#64) ↦ₛ bytesToBv8 (m.drop 1472))) := by
    have h1 : m = m.take 64 ++ ((m.drop 64).take 1408 ++ m.drop 1472) := by
      have ha : (m.drop 64).take 1408 ++ m.drop 1472 = m.drop 64 := by
        rw [show (1472 : Nat) = 64 + 1408 from rfl, ← List.drop_drop, List.take_append_drop]
      rw [ha, List.take_append_drop]
    conv => lhs; rw [h1, bytesToBv8_append, bytesToBv8_append]
    rw [pointsToBytes_append, pointsToBytes_append, hlen_m64_bv, hlen_m1408_bv]
    have h64 : BitVec.ofNat 64 64 = 64#64 := rfl
    have h1408 : 64#64 + BitVec.ofNat 64 1408 = 1472#64 := rfl
    rw [h64, BitVec.add_assoc, h1408]
  have hbuf64_in : memRegion (fsp + 624#64) 63 ∗ ((fsp + 687#64) ↦₈ 64#8) ⊢
      memRegion (fsp + 624#64) (bytesToBv8 (m.take 64)).length := by
    rw [hlen_m64_bv, ProofLib.memRegion_split' (b := fsp + 624#64) (n := 63) (k := 1) (b' :=
      fsp + 687#64)
      rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
    exact sepConj_mono_right (Entails.sepExists_intro 64#8)
  have hbuf128_weaken : ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m.take 64)) ⊢
      memRegion (fsp + 560#64) (bytesToBv8 (m.drop 1472)).length ∗ memRegion (fsp + 657#64) 30 ∗
      (∃∗ b687 : BitVec 8, (fsp + 687#64) ↦₈ b687) := by
    refine Entails.trans (Q := memRegion (fsp + 560#64) 128) ?_ (Entails.of_eq ?_)
    · rw [← hlen_blk0_bv]; exact pointsToBytes_entails_memRegion _ _
    · rw [hlen_m97_bv, ProofLib.memRegion_split' (b := fsp + 560#64) (n := 97) (k := 31) (b' :=
        fsp + 657#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 657#64) (n := 30) (k := 1) (b' :=
        fsp + 687#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hm_split) (by sep_focus)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf64_in) (by sep_focus)
  wp_call hmemcpy ⟨fsp + 624#64, msgPtr, bytesToBv8 (m.take 64)⟩
  have hmerge128 : ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ ((fsp +
    624#64) ↦ₛ bytesToBv8 (m.take 64)) = ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m.take 64)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hlen_pre_bv, BitVec.add_assoc]
    rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge128) (by sep_focus)
  wp_steps
  wp_call hsha ⟨fsp + 688#64, st0, fsp + 560#64, pre64 ++ m.take 64, 1⟩
  rw [fitBv8_64_sha512CompressOutBytes]
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf128_weaken) (by sep_focus)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  wp_steps
  wp_call hsha ⟨fsp + 688#64, sha512CompressOutBytes P st0 (pre64 ++ m.take 64), msgPtr + 64#64,
    (m.drop 64).take 1408, 11⟩
  rw [fitBv8_64_sha512CompressOutBytes]
  wp_steps
  wp_call hmemcpy ⟨fsp + 560#64, msgPtr + 1472#64, bytesToBv8 (m.drop 1472)⟩
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hm_split.symm) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by rw [hsp_sf_1, hsp_sf, hsp]; ac_rfl), by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
theorem verifySig_seg3a_trap (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp : BitVec 64) (tail97 st : Bytes) (blkCnt : BitVec 64) (L : Nat)
    (Frame : SepProp) (htail97 : tail97.length = 97) (hst : st.length = 64)
    (hblkL : (blkCnt = 0#64 ∧ L = 97) ∨ (blkCnt = 12#64 ∧ L = 1633))
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) : SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 992#64) s
      (((fsp + 560#64) ↦ₛ bytesToBv8 tail97) ∗ memRegion (fsp + 657#64) 30 ∗
       ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st) ∗ ((fsp + 752#64) ↦₆₄ blkCnt) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ memRegion (fsp + 768#64) 32 ∗ cells (fsp + 800#64) 16 ∗
       cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm => (Pm ⊢ cells (fsp + 560#64) 16 ∗ cells (fsp + 688#64) 10 ∗
          ((fsp + 768#64) ↦ₛ fitBv8 32 (P.scalarFromWide (revWords64 (sha512CompressOutBytes P st
              (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L))))) ∗
          cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 992#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = fsp + 800#64 ∧ sm.readReg64 (.gpr 29#5) = fsp + 1152#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym = 0x3de58 :=
    libsignalSessionCode_fnOff_0x3de58
  have hmemset := memset_region_ok_at_trap (b := img.base) (absHooks := absHooks)
    (name := verifySignatureMultipartSym) (C := C) (k := num% (ls_off% "memset" - 0x3de58))
  have hsha := sha512CompressStub_ok_at_trap hH
    (name := verifySignatureMultipartSym) (C := C) (k := num% (ls_off% "sha2::sha512::compress512" - 0x3de58))
  have hwide := dalekScalarWideStub_ok_at_trap hH
    (name := verifySignatureMultipartSym) (C := C) (k := num% (ls_off% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide" - 0x3de58))
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    548) hfn (by decide) verifySignatureMultipart_decode_0x3e07c
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    552) hfn (by decide) verifySignatureMultipart_decode_0x3e080
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    556) hfn (by decide) verifySignatureMultipart_decode_0x3e084
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    560) hfn (by decide) verifySignatureMultipart_decode_0x3e088
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    564) hfn (by decide) verifySignatureMultipart_decode_0x3e08c
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    568) hfn (by decide) verifySignatureMultipart_decode_0x3e090
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    572) hfn (by decide) verifySignatureMultipart_decode_0x3e094
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    576) hfn (by decide) verifySignatureMultipart_decode_0x3e098
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    580) hfn (by decide) verifySignatureMultipart_decode_0x3e09c
  have f9 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    584) hfn (by decide) verifySignatureMultipart_decode_0x3e0a0
  have f10 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    588) hfn (by decide) verifySignatureMultipart_decode_0x3e0a4
  have f11 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    592) hfn (by decide) verifySignatureMultipart_decode_0x3e0a8
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    596) hfn (by decide) verifySignatureMultipart_decode_0x3e0ac
  have f13 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    600) hfn (by decide) verifySignatureMultipart_decode_0x3e0b0
  have f14 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    604) hfn (by decide) verifySignatureMultipart_decode_0x3e0b4
  have f15 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    608) hfn (by decide) verifySignatureMultipart_decode_0x3e0b8
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    612) hfn (by decide) verifySignatureMultipart_decode_0x3e0bc
  have f17 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    616) hfn (by decide) verifySignatureMultipart_decode_0x3e0c0
  have f18 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    620) hfn (by decide) verifySignatureMultipart_decode_0x3e0c4
  have f19 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    624) hfn (by decide) verifySignatureMultipart_decode_0x3e0c8
  have f20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    628) hfn (by decide) verifySignatureMultipart_decode_0x3e0cc
  have f21 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    632) hfn (by decide) verifySignatureMultipart_decode_0x3e0d0
  have f22 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    636) hfn (by decide) verifySignatureMultipart_decode_0x3e0d4
  have f23 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    640) hfn (by decide) verifySignatureMultipart_decode_0x3e0d8
  have f24 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    644) hfn (by decide) verifySignatureMultipart_decode_0x3e0dc
  have f25 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    648) hfn (by decide) verifySignatureMultipart_decode_0x3e0e0
  have f26 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    652) hfn (by decide) verifySignatureMultipart_decode_0x3e0e4
  have f27 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    656) hfn (by decide) verifySignatureMultipart_decode_0x3e0e8
  have f28 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    660) hfn (by decide) verifySignatureMultipart_decode_0x3e0ec
  have f29 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    664) hfn (by decide) verifySignatureMultipart_decode_0x3e0f0
  have f30 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    668) hfn (by decide) verifySignatureMultipart_decode_0x3e0f4
  have f31 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    672) hfn (by decide) verifySignatureMultipart_decode_0x3e0f8
  have f32 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    676) hfn (by decide) verifySignatureMultipart_decode_0x3e0fc
  have f33 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    680) hfn (by decide) verifySignatureMultipart_decode_0x3e100
  have f34 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    684) hfn (by decide) verifySignatureMultipart_decode_0x3e104
  have f35 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    688) hfn (by decide) verifySignatureMultipart_decode_0x3e108
  have f36 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    692) hfn (by decide) verifySignatureMultipart_decode_0x3e10c
  have f37 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    696) hfn (by decide) verifySignatureMultipart_decode_0x3e110
  have f38 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    700) hfn (by decide) verifySignatureMultipart_decode_0x3e114
  have f39 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    704) hfn (by decide) verifySignatureMultipart_decode_0x3e118
  have f40 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    708) hfn (by decide) verifySignatureMultipart_decode_0x3e11c
  have f41 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    712) hfn (by decide) verifySignatureMultipart_decode_0x3e120
  have f42 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    716) hfn (by decide) verifySignatureMultipart_decode_0x3e124
  have f43 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    720) hfn (by decide) verifySignatureMultipart_decode_0x3e128
  have f44 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    724) hfn (by decide) verifySignatureMultipart_decode_0x3e12c
  have f45 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    728) hfn (by decide) verifySignatureMultipart_decode_0x3e130
  have f46 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    732) hfn (by decide) verifySignatureMultipart_decode_0x3e134
  have f47 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    736) hfn (by decide) verifySignatureMultipart_decode_0x3e138
  have f48 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    740) hfn (by decide) verifySignatureMultipart_decode_0x3e13c
  have f49 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    744) hfn (by decide) verifySignatureMultipart_decode_0x3e140
  have f50 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    748) hfn (by decide) verifySignatureMultipart_decode_0x3e144
  have f51 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    752) hfn (by decide) verifySignatureMultipart_decode_0x3e148
  have f52 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    756) hfn (by decide) verifySignatureMultipart_decode_0x3e14c
  have f53 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    760) hfn (by decide) verifySignatureMultipart_decode_0x3e150
  have f54 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    764) hfn (by decide) verifySignatureMultipart_decode_0x3e154
  have f55 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    768) hfn (by decide) verifySignatureMultipart_decode_0x3e158
  have f56 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    772) hfn (by decide) verifySignatureMultipart_decode_0x3e15c
  have f57 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    776) hfn (by decide) verifySignatureMultipart_decode_0x3e160
  have f58 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    780) hfn (by decide) verifySignatureMultipart_decode_0x3e164
  have f59 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    784) hfn (by decide) verifySignatureMultipart_decode_0x3e168
  have f60 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    788) hfn (by decide) verifySignatureMultipart_decode_0x3e16c
  have f61 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    792) hfn (by decide) verifySignatureMultipart_decode_0x3e170
  have f62 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    796) hfn (by decide) verifySignatureMultipart_decode_0x3e174
  have f63 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    800) hfn (by decide) verifySignatureMultipart_decode_0x3e178
  have f64 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    804) hfn (by decide) verifySignatureMultipart_decode_0x3e17c
  have f65 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    808) hfn (by decide) verifySignatureMultipart_decode_0x3e180
  have f66 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    812) hfn (by decide) verifySignatureMultipart_decode_0x3e184
  have f67 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    816) hfn (by decide) verifySignatureMultipart_decode_0x3e188
  have f68 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    820) hfn (by decide) verifySignatureMultipart_decode_0x3e18c
  have f69 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    824) hfn (by decide) verifySignatureMultipart_decode_0x3e190
  have f70 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    828) hfn (by decide) verifySignatureMultipart_decode_0x3e194
  have f71 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    832) hfn (by decide) verifySignatureMultipart_decode_0x3e198
  have f72 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    836) hfn (by decide) verifySignatureMultipart_decode_0x3e19c
  have f73 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    840) hfn (by decide) verifySignatureMultipart_decode_0x3e1a0
  have f74 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    844) hfn (by decide) verifySignatureMultipart_decode_0x3e1a4
  have f75 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    848) hfn (by decide) verifySignatureMultipart_decode_0x3e1a8
  have f76 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    852) hfn (by decide) verifySignatureMultipart_decode_0x3e1ac
  have f77 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    856) hfn (by decide) verifySignatureMultipart_decode_0x3e1b0
  have f78 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    860) hfn (by decide) verifySignatureMultipart_decode_0x3e1b4
  have f79 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    864) hfn (by decide) verifySignatureMultipart_decode_0x3e1b8
  have f80 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    868) hfn (by decide) verifySignatureMultipart_decode_0x3e1bc
  have f81 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    872) hfn (by decide) verifySignatureMultipart_decode_0x3e1c0
  have f82 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    876) hfn (by decide) verifySignatureMultipart_decode_0x3e1c4
  have f83 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    880) hfn (by decide) verifySignatureMultipart_decode_0x3e1c8
  have f84 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    884) hfn (by decide) verifySignatureMultipart_decode_0x3e1cc
  have f85 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    888) hfn (by decide) verifySignatureMultipart_decode_0x3e1d0
  have f86 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    892) hfn (by decide) verifySignatureMultipart_decode_0x3e1d4
  have f87 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    896) hfn (by decide) verifySignatureMultipart_decode_0x3e1d8
  have f88 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    900) hfn (by decide) verifySignatureMultipart_decode_0x3e1dc
  have f89 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    904) hfn (by decide) verifySignatureMultipart_decode_0x3e1e0
  have f90 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    908) hfn (by decide) verifySignatureMultipart_decode_0x3e1e4
  have f91 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    912) hfn (by decide) verifySignatureMultipart_decode_0x3e1e8
  have f92 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    916) hfn (by decide) verifySignatureMultipart_decode_0x3e1ec
  have f93 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    920) hfn (by decide) verifySignatureMultipart_decode_0x3e1f0
  have f94 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    924) hfn (by decide) verifySignatureMultipart_decode_0x3e1f4
  have f95 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    928) hfn (by decide) verifySignatureMultipart_decode_0x3e1f8
  have f96 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    932) hfn (by decide) verifySignatureMultipart_decode_0x3e1fc
  have f97 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    936) hfn (by decide) verifySignatureMultipart_decode_0x3e200
  have f98 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    940) hfn (by decide) verifySignatureMultipart_decode_0x3e204
  have f99 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    944) hfn (by decide) verifySignatureMultipart_decode_0x3e208
  have f100 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    948) hfn (by decide) verifySignatureMultipart_decode_0x3e20c
  have f101 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    952) hfn (by decide) verifySignatureMultipart_decode_0x3e210
  have f102 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    956) hfn (by decide) verifySignatureMultipart_decode_0x3e214
  have f103 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    960) hfn (by decide) verifySignatureMultipart_decode_0x3e218
  have f104 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    964) hfn (by decide) verifySignatureMultipart_decode_0x3e21c
  have f105 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    968) hfn (by decide) verifySignatureMultipart_decode_0x3e220
  have f106 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    972) hfn (by decide) verifySignatureMultipart_decode_0x3e224
  have f107 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    976) hfn (by decide) verifySignatureMultipart_decode_0x3e228
  have f108 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    980) hfn (by decide) verifySignatureMultipart_decode_0x3e22c
  have f109 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    984) hfn (by decide) verifySignatureMultipart_decode_0x3e230
  have f110 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    988) hfn (by decide) verifySignatureMultipart_decode_0x3e234
  dsimp only [trTrapProgAt] at hmemset hsha hwide hpc ⊢
  clear hfn hH
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureMultipartSym =
      entry
  examples_hide_fetches
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, p12, p13, hp1, hp2, hp3⟩ :=
    exists_pad97_cells htail97
  have hst_bv : (bytesToBv8 st).length = 64 := by simp [bytesToBv8, hst]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hw_st⟩ := exists_unpack64_of_length_64 hst_bv
  cells_pre_unfold_fast
  wp_extract_exists
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hp1 (fsp + 560#64))) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hw_st (fsp + 688#64))) (by sep_focus)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply ProofLib.SepWP.replace_pre
    (hPQ := blockBuf_tail32_pack (fsp + 656#64) ((bytesToBv8 tail97).getD 96 0#8) 97#8)
    (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_left; intro b12
  apply SepWP.exists_left; intro b13
  apply SepWP.exists_left; intro b14
  apply SepWP.exists_left; intro b15
  apply SepWP.pure_elim; rintro ⟨hb12, hb15⟩
  wp_steps
  have hsp7 : ((fsp + 920#64) ↦₆₄ b15) =
      (((fsp + 920#64) ↦ₛ first7 b15) ∗ ((fsp + 927#64) ↦₈ 97#8)) := by
    rw [cell_split7 (fsp + 920#64) b15, hb15, BitVec.add_assoc]; rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsp7) (by sep_focus)
  wp_steps
  have hunpack32 := blockBuf_tail32_unpack (fsp + 896#64) b12 b13 b14 b15
    ((bytesToBv8 tail97).getD 96 0#8) 97#8 hb12
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hunpack32
  apply ProofLib.SepWP.replace_pre (hPQ := hunpack32) (by sep_focus)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  wp_steps
  wp_call hmemset (fsp + 898#64, 0#8, 30)
  have hp2_896 := hp2 (fsp + 896#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp2_896
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp2_896) (by sep_focus)
  wp_steps
  have hbithi : rev64 (BitVec.truncate 64 ((0#64 ++ blkCnt) >>> 54)) = 0#64 := by
    rcases hblkL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hbitlo : rev64 (blkCnt <<< 10 ||| 776#64) = rev64 (BitVec.ofNat 64 (8 * L)) := by
    rcases hblkL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hL_or : L = 97 ∨ L = 1633 := hblkL.imp And.right And.right
  have hp3_1008 := hp3 (fsp + 1008#64) hL_or
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp3_1008
  have hw_st_928 := (hw_st (fsp + 928#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hw_st_928
  wp_simp_pre_fast [hbithi, hbitlo]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp3_1008) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hw_st_928) (by sep_focus)
  have hpad_len : (tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L)).length = 128 := by
    simp [encodeBitLen128BE, encodeBitLen64BE, htail97]
  wp_call hsha ⟨fsp + 928#64, st, fsp + 1008#64, tail97 ++ [0x80] ++ List.replicate 14 0 ++
    encodeBitLen128BE L, 1⟩
  have hpad_norm : tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L) =
      tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L := by
    simp [List.append_assoc]
  wp_simp_pre_fast [fitBv8_64_sha512CompressOutBytes, hpad_norm]
  have hst_out_len : (sha512CompressOutBytes P st (tail97 ++ [0x80] ++ List.replicate 14 0 ++
    encodeBitLen128BE L)).length = 64 := sha512CompressOutBytes_length P _ _
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, hu_st, hu_rev⟩ :=
    exists_unpack64_revWords64_of_length_64 hst_out_len
  have hu_st_928 := hu_st (fsp + 928#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu_st_928
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_st_928) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp3_1008.symm) (by sep_focus)
  have hsp7_920 := cell_split7 (fsp + 920#64) (rev64 (BitVec.ofNat 64 (8 * L)))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsp7_920
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsp7_920) (by sep_focus)
  wp_steps
  have hpk7_920 := first7_pack (fsp + 920#64) (rev64 (BitVec.ofNat 64 (8 * L))) 0#8
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpk7_920
  apply ProofLib.SepWP.replace_pre (hPQ := hpk7_920) (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro _
  wp_steps
  have hu_rev_1008 := (hu_rev (fsp + 1008#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu_rev_1008
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_rev_1008) (by sep_focus)
  have hrev_len : (revWords64 (sha512CompressOutBytes P st (tail97 ++ 128 :: (List.replicate 14 0 ++
    encodeBitLen128BE L)))).length = 64 := revWords64_length (sha512CompressOutBytes_length P _ _)
  wp_call hwide ⟨fsp + 1008#64, revWords64 (sha512CompressOutBytes P st (tail97 ++ [0x80] ++
    List.replicate 14 0 ++ encodeBitLen128BE L)), fsp + 768#64⟩
  wp_simp_pre_fast [hpad_norm]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_rev_1008.symm) (by sep_focus)
  have hm560 := cells_16_merge (fsp + 560#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm560
  apply ProofLib.SepWP.replace_pre (hPQ := hm560) (by sep_focus)
  have hm688 := cells_10_merge (fsp + 688#64) w0 w1 w2 w3 w4 w5 w6 w7 blkCnt 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm688
  apply ProofLib.SepWP.replace_pre (hPQ := hm688) (by sep_focus)
  have hm800 := cells_16_merge (fsp +
    800#64) 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm800
  apply ProofLib.SepWP.replace_pre (hPQ := hm800) (by sep_focus)
  have hm928 := cells_10_merge (fsp + 928#64) u0 u1 u2 u3 u4 u5 u6 u7 blkCnt 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm928
  apply ProofLib.SepWP.replace_pre (hPQ := hm928) (by sep_focus)
  have hm1008 := cells_16_merge (fsp +
    1008#64) (rev64 u0) (rev64 u1) (rev64 u2) (rev64 u3) (rev64 u4) (rev64 u5) (rev64 u6) (rev64 u7)
    0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1008
  apply ProofLib.SepWP.replace_pre (hPQ := hm1008) (by sep_focus)
  wp_simp_pre_fast [hsp_sf_1, hsp_sf, hsp]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
set_option maxHeartbeats 8000000 in
theorem verifySig_seg2_33_trap (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 33) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 320#64)
    (hsp : s.sp = fsp) (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = 1#64) : SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame) (fun sm Pm => (Pm ⊢
          (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗
          ((fsp + 752#64) ↦₆₄ 0#64) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗
          Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym = 0x3de58 :=
    libsignalSessionCode_fnOff_0x3de58
  have hmemcpy := memcpy_region_ok_at_trap (b := img.base) (absHooks := absHooks)
    (name := verifySignatureMultipartSym) (C := C) (k := num% (ls_off% "memcpy" - 0x3de58))
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    320) hfn (by decide) verifySignatureMultipart_decode_0x3df98
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    324) hfn (by decide) verifySignatureMultipart_decode_0x3df9c
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    328) hfn (by decide) verifySignatureMultipart_decode_0x3dfa0
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    332) hfn (by decide) verifySignatureMultipart_decode_0x3dfa4
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    336) hfn (by decide) verifySignatureMultipart_decode_0x3dfa8
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    340) hfn (by decide) verifySignatureMultipart_decode_0x3dfac
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    344) hfn (by decide) verifySignatureMultipart_decode_0x3dfb0
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    348) hfn (by decide) verifySignatureMultipart_decode_0x3dfb4
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    352) hfn (by decide) verifySignatureMultipart_decode_0x3dfb8
  have f9 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    356) hfn (by decide) verifySignatureMultipart_decode_0x3dfbc
  have f10 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    360) hfn (by decide) verifySignatureMultipart_decode_0x3dfc0
  have f11 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    364) hfn (by decide) verifySignatureMultipart_decode_0x3dfc4
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    368) hfn (by decide) verifySignatureMultipart_decode_0x3dfc8
  have f13 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    372) hfn (by decide) verifySignatureMultipart_decode_0x3dfcc
  have f14 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    376) hfn (by decide) verifySignatureMultipart_decode_0x3dfd0
  have f15 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    380) hfn (by decide) verifySignatureMultipart_decode_0x3dfd4
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    384) hfn (by decide) verifySignatureMultipart_decode_0x3dfd8
  have f17 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    388) hfn (by decide) verifySignatureMultipart_decode_0x3dfdc
  have f18 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    392) hfn (by decide) verifySignatureMultipart_decode_0x3dfe0
  dsimp only [trTrapProgAt] at hmemcpy hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureMultipartSym =
      entry
  examples_hide_fetches
  have hlen_pre_bv : (bytesToBv8 pre64).length = 64 := by simp [bytesToBv8, hpre64]
  have hlen_m_bv : (bytesToBv8 m).length = 33 := by simp [bytesToBv8, hm]
  have hbuf63_split : memRegion (fsp + 624#64) 63 =
      memRegion (fsp + 624#64) (bytesToBv8 m).length ∗ memRegion (fsp + 657#64) 30 := by
    rw [hlen_m_bv]
    exact ProofLib.memRegion_split' (b := fsp + 624#64) (n := 33) (k := 30) (b' := fsp + 657#64)
      rfl (by bv_omega) (by decide)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hbuf63_split) (by sep_focus)
  wp_steps
  wp_call hmemcpy ⟨fsp + 624#64, msgPtr, bytesToBv8 m⟩
  have hmerge97 : ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ ((fsp + 624#64) ↦ₛ bytesToBv8 m) =
      ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hlen_pre_bv, BitVec.add_assoc]
    rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge97) (by sep_focus)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
theorem verifySig_seg3b_trap (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks) (s : State) (fsp sigPtr : BitVec 64)
    (sig minusCapA hScalar : Bytes) (Frame : SepProp) (hsig : sig.length = 64)
    (hnegA : minusCapA.length = 160) (hh : hScalar.length = 32) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 992#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) : SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1100#64) s
      (((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
       ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
       ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗ ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗
       cells (fsp + 800#64) 4 ∗ memRegion (fsp + 832#64) 128 ∗ memRegion (fsp + 1008#64) 32 ∗
       stackAt fsp pqxdhHookStack ∗ Frame) (fun sm Pm => (Pm ⊢
          ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
          ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
          ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗ ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗
          memRegion (fsp + 800#64) 160 ∗ memRegion (fsp + 1008#64) 32 ∗ stackAt fsp pqxdhHookStack ∗
          Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1100#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 0#5) =
          (let sClamped := (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]
           let sScalar := P.scalarFromBytesModOrder sClamped
           let capRCheck := P.compress (P.doubleScalarMulBasepoint hScalar minusCapA sScalar)
           if (capRCheck == sig.take 32) = true then 1#64 else 0#64) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym = 0x3de58 :=
    libsignalSessionCode_fnOff_0x3de58
  have hmod := dalekScalarModStub_ok_at_trap hH
    (name := verifySignatureMultipartSym) (C := C) (k := num% (ls_off% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order" - 0x3de58))
  have hdmul := dalekDoubleMulStub_ok_at_trap hH
    (name := verifySignatureMultipartSym) (C := C) (k := num% (ls_off% "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint" - 0x3de58))
  have hcomp := dalekCompressStub_ok_at_trap hH
    (name := verifySignatureMultipartSym) (C := C) (k := num% (ls_off% "<curve25519_dalek::edwards::EdwardsPoint>::compress" - 0x3de58))
  have hcteq := subroutine_ok_rel_pqxdh_trap (pqxdh_ct_eq_slice_ok_trap (C := C) img.base absHooks)
    libsignalSessionCode_fnOff_0x3eda8 hfn (k := 3920) (by decide)
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    992) hfn (by decide) verifySignatureMultipart_decode_0x3e238
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    996) hfn (by decide) verifySignatureMultipart_decode_0x3e23c
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1000) hfn (by decide) verifySignatureMultipart_decode_0x3e240
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1004) hfn (by decide) verifySignatureMultipart_decode_0x3e244
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1008) hfn (by decide) verifySignatureMultipart_decode_0x3e248
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1012) hfn (by decide) verifySignatureMultipart_decode_0x3e24c
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1016) hfn (by decide) verifySignatureMultipart_decode_0x3e250
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1020) hfn (by decide) verifySignatureMultipart_decode_0x3e254
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1024) hfn (by decide) verifySignatureMultipart_decode_0x3e258
  have f9 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1028) hfn (by decide) verifySignatureMultipart_decode_0x3e25c
  have f10 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1032) hfn (by decide) verifySignatureMultipart_decode_0x3e260
  have f11 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1036) hfn (by decide) verifySignatureMultipart_decode_0x3e264
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1040) hfn (by decide) verifySignatureMultipart_decode_0x3e268
  have f13 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1044) hfn (by decide) verifySignatureMultipart_decode_0x3e26c
  have f14 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1048) hfn (by decide) verifySignatureMultipart_decode_0x3e270
  have f15 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1052) hfn (by decide) verifySignatureMultipart_decode_0x3e274
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1056) hfn (by decide) verifySignatureMultipart_decode_0x3e278
  have f17 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1060) hfn (by decide) verifySignatureMultipart_decode_0x3e27c
  have f18 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1064) hfn (by decide) verifySignatureMultipart_decode_0x3e280
  have f19 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1068) hfn (by decide) verifySignatureMultipart_decode_0x3e284
  have f20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1072) hfn (by decide) verifySignatureMultipart_decode_0x3e288
  have f21 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1076) hfn (by decide) verifySignatureMultipart_decode_0x3e28c
  have f22 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1080) hfn (by decide) verifySignatureMultipart_decode_0x3e290
  have f23 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H :=
    Rust.withPanics (trTrapExterns C absHooks)) (k :=
    1084) hfn (by decide) verifySignatureMultipart_decode_0x3e294
  dsimp only [trTrapProgAt] at hmod hdmul hcomp hcteq hpc ⊢
  clear hfn hH
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr verifySignatureMultipartSym =
      entry
  examples_hide_fetches
  obtain ⟨q0_lo, q0_hi, q1_lo, q1_hi, hsig_q0, hsig_q1, hbuf_q0, hbuf_q1⟩ :=
    exists_sig_capS_cells hsig
  cells_pre_unfold_fast
  wp_extract_exists
  rename_i v0 v1 v2 v3
  have hsbuf := sClamped_buf_pre (fsp + 800#64) v0 v1 v2 v3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsbuf
  apply ProofLib.SepWP.replace_pre (hPQ := hsbuf) (by sep_focus)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig_q0 sigPtr)) (by sep_focus)
  wp_steps
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq ((hsig_q0 sigPtr).symm.trans (hsig_q1 sigPtr))) (by sep_focus)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig_q1 sigPtr).symm) (by sep_focus)
  have hbuf0 := hbuf_q0 (fsp + 800#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbuf0
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf0) (by sep_focus)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  apply SepWP.exists_left; intro _
  wp_steps
  wp_simp_pre_fast [truncate8_zeroExtend32_and7f]
  have hbuf1 := hbuf_q1 (fsp + 800#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbuf1
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hbuf1) (by sep_focus)
  have hsClamped_len : ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]).length = 32 :=
    by simp [hsig]
  wp_call hmod ⟨fsp + 800#64, (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F], fsp +
    1008#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.scalarFromBytesModOrder_len _)]
  wp_steps
  have hsClamped_bv_len : (bytesToBv8 (List.take 31 (List.drop 32 sig) ++
    [(List.drop 32 sig).getD 31 0 &&& 127])).length = 32 := by
    simp [bytesToBv8, hsig]
  have hm160 := pointsToBytes_32_merge_128 (fsp + 800#64) _ hsClamped_bv_len
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm160
  apply ProofLib.SepWP.replace_pre (hPQ := hm160) (by sep_focus)
  have hsScalar_len : (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
    [(List.drop 32 sig).getD 31 0 &&& 127])).length = 32 := hWF.scalarFromBytesModOrder_len _
  wp_call hdmul ⟨hScalar, minusCapA, P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
    [(List.drop 32 sig).getD 31 0 &&& 127]), fsp + 768#64, fsp + 400#64, fsp + 1008#64, fsp +
    800#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.doubleScalarMulBasepoint_len _ _ _)]
  wp_steps
  have hsScalar_bv_len : (bytesToBv8 (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
    [(List.drop 32 sig).getD 31 0 &&& 127]))).length = 32 := by
    simp [bytesToBv8, hWF.scalarFromBytesModOrder_len]
  have hm32_1008 := pointsToBytes_entails_memRegion_n (fsp + 1008#64) _ hsScalar_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm32_1008) (by sep_focus)
  have hdmul_len : (P.doubleScalarMulBasepoint hScalar minusCapA (P.scalarFromBytesModOrder
    (List.take 31 (List.drop 32 sig) ++ [(List.drop 32 sig).getD 31 0 &&& 127]))).length = 160 :=
    hWF.doubleScalarMulBasepoint_len _ _ _
  wp_call hcomp ⟨fsp + 800#64,
    P.doubleScalarMulBasepoint hScalar minusCapA (P.scalarFromBytesModOrder (List.take 31 (List.drop
    32 sig) ++ [(List.drop 32 sig).getD 31 0 &&& 127])), fsp + 1008#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.compress_len _)]
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig)) (by sep_focus)
  wp_simp_pre_fast [hsp_sf_1, hsp_sf, hsp, stackAt_hook_split_48]
  have hcapR_bv_len : (bytesToBv8 (P.compress (P.doubleScalarMulBasepoint hScalar minusCapA
    (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
    [(List.drop 32 sig).getD 31 0 &&& 127]))))).length = 32 := by
    simp [bytesToBv8, hWF.compress_len]
  have hsig32_bv_len : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
  wp_call hcteq (fsp + 1008#64,
    bytesToBv8 (P.compress (P.doubleScalarMulBasepoint hScalar minusCapA (P.scalarFromBytesModOrder
    (List.take 31 (List.drop 32 sig) ++ [(List.drop 32 sig).getD 31 0 &&& 127])))), sigPtr,
    bytesToBv8 (sig.take 32), fsp)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (sig_split_32 sigPtr hsig).symm) (by sep_focus)
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (stackAt_hook_split_48 fsp).symm) (by sep_focus)
  have hdmul_bv_len : (bytesToBv8 (P.doubleScalarMulBasepoint hScalar minusCapA
    (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
    [(List.drop 32 sig).getD 31 0 &&& 127])))).length = 160 := by
    simp [bytesToBv8, hWF.doubleScalarMulBasepoint_len]
  have hm160_800 := pointsToBytes_entails_memRegion_n (fsp + 800#64) _ hdmul_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm160_800) (by sep_focus)
  have hm32_capR := pointsToBytes_entails_memRegion_n (fsp + 1008#64) _ hcapR_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm32_capR) (by sep_focus)
  wp_simp_pre_fast [hsp_sf_3, hsp_sf_2, hsp_sf_1, hsp_sf, hsp]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_,
    by wp_norm_goal, by wp_norm_goal⟩
  wp_norm_goal
  exact x0_cteq_simplify _ _
end WithProgramTrap

section WithProgram
variable {C : Crypto} {ctl : BitVec 64}
local notation "PP" b:arg absHooks:arg => tripleRatchetProgAt b C ctl absHooks

theorem dalekCompressStub_ok_at {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekCompressStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafStubSpec P.compress 160 32) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (dalekCompressStub_ok_at_trap hH hk)

theorem dalekEdNegStub_ok_at {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekEdNegStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafStubSpec P.edNeg 160 160) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (dalekEdNegStub_ok_at_trap hH hk)

theorem sha512CompressStub_ok_at {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff sha512CompressStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (compressInPlaceStubSpec (sha512CompressOutBytes P) 64 128 img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (sha512CompressStub_ok_at_trap hH hk)

theorem dalekScalarWideStub_ok_at {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekScalarWideStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafStubSpec P.scalarFromWide 64 32) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (dalekScalarWideStub_ok_at_trap hH hk)

theorem dalekScalarModStub_ok_at {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekScalarModStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafStubSpec P.scalarFromBytesModOrder 32 32) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (dalekScalarModStub_ok_at_trap hH hk)

theorem dalekDoubleMulStub_ok_at {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContracts P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekDoubleMulStub := by fnoff_eq) :
    subroutine_ok (PP img.base absHooks) ((PP img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (dalekDoubleMulStubSpec P img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (dalekDoubleMulStub_ok_at_trap hH hk)

theorem memcpy_region_ok_at {b : BitVec 64} {absHooks : String → Option (State → State)}
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff memcpyName := by fnoff_eq) :
    subroutine_ok (PP b absHooks) ((PP b absHooks).fnAddr name + BitVec.ofNat 64 k)
      sessionMemcpyRegionSpec := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (memcpy_region_ok_at_trap hk)

theorem memset_region_ok_at {b : BitVec 64} {absHooks : String → Option (State → State)}
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff memsetName := by fnoff_eq) :
    subroutine_ok (PP b absHooks) ((PP b absHooks).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemsetSpec pqxdhHookStack) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (memset_region_ok_at_trap hk)

theorem pqxdh_ct_eq_slice_ok (b : BitVec 64) (absHooks : String → Option (State → State)) :
    subroutine_ok (PP b absHooks) ((PP b absHooks).fnAddr ConsumeMessageKeyTransfer.ctEqName)
      pqxdhCtEqSliceSpec := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdh_ct_eq_slice_ok_trap b absHooks)

theorem subroutine_ok_rel_pqxdh {α : Type} {b : BitVec 64}
    {absHooks : String → Option (State → State)}
    {spec : Spec α} {callee name : String} {offc off k : Nat}
    (h : subroutine_ok (PP b absHooks) ((PP b absHooks).fnAddr callee) spec)
    (hc : libsignalSessionCode.fnOff callee = offc) (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = offc) : subroutine_ok (PP b absHooks)
      ((PP b absHooks).fnAddr name + BitVec.ofNat 64 k) spec := by
  have hrel : (PP b absHooks).fnAddr callee = (PP b absHooks).fnAddr name + BitVec.ofNat 64 k := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hc, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, hk, ← hk, Nat.mod_mod]
  rwa [hrel] at h

theorem verifySig_seg2_1569 (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 1569) (hst0 : st0.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 320#64)
    (hsp : s.sp = fsp) (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = 1#64) : SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame) (fun sm Pm => (Pm ⊢
          (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (m.drop 1472)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8
            (sha512CompressOutBytes P (sha512CompressOutBytes P st0 (pre64 ++
            m.take 64)) ((m.drop 64).take 1408))) ∗ ((fsp + 752#64) ↦₆₄ 12#64) ∗
          ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧ sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_seg2_1569_trap P A img absHooks hH s fsp slicesPtr msgPtr pre64 m st0 Frame hpre64 hm hst0 hfsp_align hrun hpc hsp hx20 hx21).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, _, htr⟩ => ⟨hPm, h1, h2, h3, h4, h5, htr⟩)

theorem verifySig_seg3a (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hH : PqxdhHookContracts P A img absHooks)
    (s : State) (fsp : BitVec 64) (tail97 st : Bytes) (blkCnt : BitVec 64) (L : Nat)
    (Frame : SepProp) (htail97 : tail97.length = 97) (hst : st.length = 64)
    (hblkL : (blkCnt = 0#64 ∧ L = 97) ∨ (blkCnt = 12#64 ∧ L = 1633))
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) : SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 992#64) s
      (((fsp + 560#64) ↦ₛ bytesToBv8 tail97) ∗ memRegion (fsp + 657#64) 30 ∗
       ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st) ∗ ((fsp + 752#64) ↦₆₄ blkCnt) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ memRegion (fsp + 768#64) 32 ∗ cells (fsp + 800#64) 16 ∗
       cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm => (Pm ⊢ cells (fsp + 560#64) 16 ∗ cells (fsp + 688#64) 10 ∗
          ((fsp + 768#64) ↦ₛ fitBv8 32 (P.scalarFromWide (revWords64 (sha512CompressOutBytes P st
              (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L))))) ∗
          cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 992#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = fsp + 800#64 ∧ sm.readReg64 (.gpr 29#5) = fsp + 1152#64 ∧
        sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_seg3a_trap P A img absHooks hH s fsp tail97 st blkCnt L Frame htail97 hst hblkL hfsp_align hrun hpc hsp hx23 hx29).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, _, htr⟩ => ⟨hPm, h1, h2, h3, h4, h5, htr⟩)

set_option maxHeartbeats 8000000 in
theorem verifySig_seg2_33 (img : Obj.Image) (absHooks : String → Option (State → State))
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 33) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 320#64)
    (hsp : s.sp = fsp) (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = 1#64) : SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame) (fun sm Pm => (Pm ⊢
          (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗
          ((fsp + 752#64) ↦₆₄ 0#64) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗
          Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧ sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_seg2_33_trap img absHooks s fsp slicesPtr msgPtr pre64 m st0 Frame hpre64 hm hfsp_align hrun hpc hsp hx20 hx21).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, h5, _, htr⟩ => ⟨hPm, h1, h2, h3, h4, h5, htr⟩)

theorem verifySig_seg3b (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hWF : StructuralPrims P)
    (hH : PqxdhHookContracts P A img absHooks) (s : State) (fsp sigPtr : BitVec 64)
    (sig minusCapA hScalar : Bytes) (Frame : SepProp) (hsig : sig.length = 64)
    (hnegA : minusCapA.length = 160) (hh : hScalar.length = 32) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 992#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) : SepWP (PP img.base absHooks)
      ((PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1100#64) s
      (((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
       ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
       ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗ ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗
       cells (fsp + 800#64) 4 ∗ memRegion (fsp + 832#64) 128 ∗ memRegion (fsp + 1008#64) 32 ∗
       stackAt fsp pqxdhHookStack ∗ Frame) (fun sm Pm => (Pm ⊢
          ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
          ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
          ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗ ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗
          memRegion (fsp + 800#64) 160 ∗ memRegion (fsp + 1008#64) 32 ∗ stackAt fsp pqxdhHookStack ∗
          Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PP img.base absHooks).fnAddr verifySignatureMultipartSym + 1100#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 0#5) =
          (let sClamped := (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]
           let sScalar := P.scalarFromBytesModOrder sClamped
           let capRCheck := P.compress (P.doubleScalarMulBasepoint hScalar minusCapA sScalar)
           if (capRCheck == sig.take 32) = true then 1#64 else 0#64) ∧ sm.trace = s.trace) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact SepWP.mono
    ((verifySig_seg3b_trap P A img absHooks hWF hH s fsp sigPtr sig minusCapA hScalar Frame hsig hnegA hh hfsp_align hrun hpc hsp hx23 hx29).of_trapsOnly (trapsOnly_trTrap_kit _ C ctl _))
    (fun _ _ _ _ ⟨hPm, h1, h2, h3, h4, _, htr⟩ => ⟨hPm, h1, h2, h3, h4, htr⟩)

end WithProgram

/-! ## Contract-Backed Generalization on `tripleRatchetProgAtExt` -/

section WithProgramExt
local notation "PPX" b:arg absHooks:arg => tripleRatchetProgAtExt b absHooks

def pqxdhCtEqSliceSpecExt :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ cells (sp - 48#64) 6 ∗ stackAt (sp - 48#64) pqxdhHookStackExt
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = (if k1 = k2 then 1#8 else 0#8) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ cells (sp - 48#64) 6 ∗ stackAt (sp - 48#64) pqxdhHookStackExt

theorem stackAt_verifySigHook_split_48_ext (sp : BitVec 64) :
    stackAt sp verifySigHookStackExt =
      cells (sp - 48#64) 6 ∗ stackAt (sp - 48#64) pqxdhHookStackExt := by
  simpa only [sepConj_comm] using
    ProofLib.stackAt_split_cells sp pqxdhHookStackExt 6 (by decide)

private theorem truncate32_and_mask_eq_zext32_setWidth8_ext (v : BitVec 64) :
    BitVec.truncate 32 (v &&& 1095216660735#64) = BitVec.zeroExtend 32 (v.setWidth 8) := by
  bv_bits

theorem x0_cteq_simplify_ext {v : BitVec 64} (xs ys : Bytes)
    (hv : v.setWidth 8 = (if bytesToBv8 xs = bytesToBv8 ys then 1#8 else 0#8)) :
    (if (BitVec.truncate 32 (v &&& 1095216660735#64) == 0#32) = true
     then 0#64 else 1#64) = (if (xs == ys) = true then 1#64 else 0#64) := by
  rw [truncate32_and_mask_eq_zext32_setWidth8_ext, hv]
  by_cases h : xs = ys
  · subst h; simp
  · have hne : ¬ (bytesToBv8 xs = bytesToBv8 ys) := fun heq => h (bytesToBv8_inj heq)
    have hbeq : ¬ ((xs == ys) = true) := by rw [beq_iff_eq]; exact h
    simp only [hne, hbeq, ↓reduceIte]; decide

theorem dalekCompressStub_ok_at_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContractsExt P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekCompressStub := by fnoff_eq) :
    subroutine_ok (PPX img.base absHooks) ((PPX img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafRefStubSpecExt P.compress 160 32) :=
  hook_ok_at (hname := dalekCompressStub) rfl hk (by fnoff_eq) (by fnoff_eq)
    (by simp [Rust.isPanicSymbol, dalekCompressStub]) hH.dalekCompress

theorem dalekEdNegStub_ok_at_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContractsExt P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekEdNegStub := by fnoff_eq) :
    subroutine_ok (PPX img.base absHooks) ((PPX img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafByValStubSpecExt P.edNeg 160 160) :=
  hook_ok_at (hname := dalekEdNegStub) rfl hk (by fnoff_eq) (by fnoff_eq)
    (by simp [Rust.isPanicSymbol, dalekEdNegStub]) hH.dalekEdNeg

theorem sha512CompressStub_ok_at_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContractsExt P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff sha512CompressStub := by fnoff_eq) :
    subroutine_ok (PPX img.base absHooks) ((PPX img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (compressInPlaceStubSpecExt (sha512CompressOutBytes P) 64 128 img) :=
  hook_ok_at (hname := sha512CompressStub) rfl hk (by fnoff_eq) (by fnoff_eq)
    (by simp [Rust.isPanicSymbol, sha512CompressStub]) hH.sha512Compress

theorem dalekScalarWideStub_ok_at_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContractsExt P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekScalarWideStub := by fnoff_eq) :
    subroutine_ok (PPX img.base absHooks) ((PPX img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafRefStubSpecExt P.scalarFromWide 64 32) :=
  hook_ok_at (hname := dalekScalarWideStub) rfl hk (by fnoff_eq) (by fnoff_eq)
    (by simp [Rust.isPanicSymbol, dalekScalarWideStub]) hH.dalekScalarWide

theorem dalekScalarModStub_ok_at_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContractsExt P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekScalarModStub := by fnoff_eq) :
    subroutine_ok (PPX img.base absHooks) ((PPX img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafByValStubSpecExt P.scalarFromBytesModOrder 32 32) :=
  hook_ok_at (hname := dalekScalarModStub) rfl hk (by fnoff_eq) (by fnoff_eq)
    (by simp [Rust.isPanicSymbol, dalekScalarModStub]) hH.dalekScalarMod

theorem dalekDoubleMulStub_ok_at_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {absHooks : String → Option (State → State)} (hH : PqxdhHookContractsExt P A img absHooks)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dalekDoubleMulStub := by fnoff_eq) :
    subroutine_ok (PPX img.base absHooks) ((PPX img.base absHooks).fnAddr name + BitVec.ofNat 64 k)
      (dalekDoubleMulStubSpecExt P img) :=
  hook_ok_at (hname := dalekDoubleMulStub) rfl hk (by fnoff_eq) (by fnoff_eq)
    (by simp [Rust.isPanicSymbol, dalekDoubleMulStub]) hH.dalekDoubleMul

private theorem hookSat_sessionMemcpy_ext {absHooks : String → Option (State → State)}
    (h : HookSat absHooks memcpyName SignalSession.CliExt.memcpySpec) :
    HookSat absHooks memcpyName (sessionMemcpySpec pqxdhHookStackExt) := by
  obtain ⟨fn, hfn, hok⟩ := h
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases x with ⟨dst, src, bs⟩
  have hsplit : stackAt s0.sp pqxdhHookStackExt =
      stackAt s0.sp SignalSession.CliExt.memHookStack ∗ memRegion (s0.sp - 16384#64) 12288 :=
    (ProofLib.stackAt_split_bottom s0.sp 4096 12288 (by decide)).trans (sepConj_comm _ _)
  dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpre
  rw [hsplit] at hpre
  have hpre0 : s0.mem ⊨ SignalSession.CliExt.memcpySpec.pre (dst, src, bs) s0 ∗
      (memRegion (s0.sp - 16384#64) 12288 ∗ R) := by
    dsimp only [SignalSession.CliExt.memcpySpec, libcMemcpySpec]
    convert hpre using 1; ac_rfl
  rcases hok (dst, src, bs) (memRegion (s0.sp - 16384#64) 12288 ∗ R) s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [SignalSession.CliExt.memcpySpec] at hpost
    dsimp only [sessionMemcpySpec]
    rw [hsplit]
    convert hpost using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem hookSat_sessionMemset_ext {absHooks : String → Option (State → State)}
    (h : HookSat absHooks memsetName SignalSession.CliExt.memsetSpec) :
    HookSat absHooks memsetName (sessionMemsetSpec pqxdhHookStackExt) := by
  obtain ⟨fn, hfn, hok⟩ := h
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases x with ⟨ptr, c, len⟩
  have hsplit : stackAt s0.sp pqxdhHookStackExt =
      stackAt s0.sp SignalSession.CliExt.memHookStack ∗ memRegion (s0.sp - 16384#64) 12288 :=
    (ProofLib.stackAt_split_bottom s0.sp 4096 12288 (by decide)).trans (sepConj_comm _ _)
  dsimp only [sessionMemsetSpec, libcMemsetSpec] at hpre
  rw [hsplit] at hpre
  have hpre0 : s0.mem ⊨ SignalSession.CliExt.memsetSpec.pre (ptr, c, len) s0 ∗
      (memRegion (s0.sp - 16384#64) 12288 ∗ R) := by
    dsimp only [SignalSession.CliExt.memsetSpec, libcMemsetSpec]
    convert hpre using 1; ac_rfl
  rcases hok (ptr, c, len) (memRegion (s0.sp - 16384#64) 12288 ∗ R) s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [SignalSession.CliExt.memsetSpec] at hpost
    dsimp only [sessionMemsetSpec]
    rw [hsplit]
    convert hpost using 1; ac_rfl
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem memcpy_region_ok_at_ext {b : BitVec 64} {absHooks : String → Option (State → State)}
    (hmemcpy : HookSat absHooks memcpyName SignalSession.CliExt.memcpySpec)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff memcpyName := by fnoff_eq) :
    subroutine_ok (PPX b absHooks) ((PPX b absHooks).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpySpec pqxdhHookStackExt) :=
  hook_ok_at (hname := memcpyName) rfl hk (by fnoff_eq) (by fnoff_eq)
    (by simp [Rust.isPanicSymbol, memcpyName]) (hookSat_sessionMemcpy_ext hmemcpy)

theorem memset_region_ok_at_ext {b : BitVec 64} {absHooks : String → Option (State → State)}
    (hmemset : HookSat absHooks memsetName SignalSession.CliExt.memsetSpec)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff memsetName := by fnoff_eq) :
    subroutine_ok (PPX b absHooks) ((PPX b absHooks).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemsetSpec pqxdhHookStackExt) :=
  hook_ok_at (hname := memsetName) rfl hk (by fnoff_eq) (by fnoff_eq)
    (by simp [Rust.isPanicSymbol, memsetName]) (hookSat_sessionMemset_ext hmemset)

theorem subroutine_ok_rel_pqxdh_ext {α : Type} {b : BitVec 64}
    {absHooks : String → Option (State → State)}
    {spec : Spec α} {callee name : String} {offc off k : Nat}
    (h : subroutine_ok (PPX b absHooks) ((PPX b absHooks).fnAddr callee) spec)
    (hc : libsignalSessionCode.fnOff callee = offc) (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = offc) : subroutine_ok (PPX b absHooks)
      ((PPX b absHooks).fnAddr name + BitVec.ofNat 64 k) spec := by
  have hrel : (PPX b absHooks).fnAddr callee = (PPX b absHooks).fnAddr name + BitVec.ofNat 64 k := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hc, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, hk, ← hk, Nat.mod_mod]
  rwa [hrel] at h

private def blackBoxU8SpecExt : Spec (BitVec 64) where
  pre := fun v s => ⌜s.readReg64 .x0 = v⌝ ∗ stackAt s.sp pqxdhHookStackExt
  post := fun v s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = v.setWidth 8 ∧ sf.trace = s0.trace⌝ ∗
      stackAt s0.sp pqxdhHookStackExt

private theorem setWidth8_of_setWidth32_zext8_ext {a b : BitVec 64}
    (h : a.setWidth 32 = (b.setWidth 8).zeroExtend 32) :
    a.setWidth 8 = b.setWidth 8 := by
  have h8 := congrArg (BitVec.setWidth 8) h
  revert h8; bv_bits

private theorem hookSat_blackBoxU8_ext {absHooks : String → Option (State → State)}
    (h : HookSat absHooks "subtle::black_box::<u8>" SignalSession.CliExt.blackBoxSpec) :
    HookSat absHooks "subtle::black_box::<u8>" blackBoxU8SpecExt := by
  obtain ⟨fn, hfn, hok⟩ := h
  refine ⟨fn, hfn, fun v R s0 hrun hpre hsp => ?_⟩
  dsimp only [blackBoxU8SpecExt, pqxdhHookStackExt] at hpre
  have hpre0 : s0.mem ⊨ SignalSession.CliExt.blackBoxSpec.pre v s0 ∗ R := by
    simpa only [SignalSession.CliExt.blackBoxSpec, SignalSession.CliExt.withStack] using hpre
  rcases hok v R s0 hrun hpre0 hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [SignalSession.CliExt.blackBoxSpec, SignalSession.CliExt.withStack] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨h32, htr⟩, hmem⟩
    dsimp only [blackBoxU8SpecExt, pqxdhHookStackExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨setWidth8_of_setWidth32_zext8_ext h32, htr⟩, hmem⟩
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem blackBox_u8_ok_at_ext {b : BitVec 64} {absHooks : String → Option (State → State)}
    (hbb : HookSat absHooks "subtle::black_box::<u8>" SignalSession.CliExt.blackBoxSpec)
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "subtle::black_box::<u8>" := by fnoff_eq) :
    subroutine_ok (PPX b absHooks) ((PPX b absHooks).fnAddr name + BitVec.ofNat 64 k)
      blackBoxU8SpecExt :=
  hook_ok_at (hname := "subtle::black_box::<u8>") rfl hk (by fnoff_eq) (by fnoff_eq)
    (by simp [Rust.isPanicSymbol]) (hookSat_blackBoxU8_ext hbb)

@[local simp, local wp_norm, local arm64_norm]
private theorem byte_bne_zext32_ext (a b : BitVec 8) :
    (BitVec.setWidth 32 a != BitVec.setWidth 32 b) = (a != b) :=
  FindReceiverChainIndex.byte_bne_zext32 a b

@[local simp, local wp_norm, local arm64_norm]
private theorem ite_bne_byte_0_1_ext (a b : BitVec 8) :
    (if (a != b) = true then 0#64 else 1#64) = if (a == b) = true then 1#64 else 0#64 :=
  FindReceiverChainIndex.ite_bne_byte_0_1 a b

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_1_0_ext (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#64 else 0#64) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_prop_1_0_ext (P : Prop) [Decidable P] :
    BitVec.setWidth 8 (if P then 1#64 else 0#64) = if P then 1#8 else 0#8 := by
  split <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_1_0_32_ext (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#32 else 0#32) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_zext64_32_ext (x : BitVec 32) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 x) = BitVec.setWidth 8 x := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_setWidth32_ext (x : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x) = BitVec.setWidth 8 x := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_and64_ext (x y : BitVec 64) :
    BitVec.setWidth 8 (x &&& y) = BitVec.setWidth 8 x &&& BitVec.setWidth 8 y :=
  BitVec.setWidth_and

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_and32_ext (x y : BitVec 32) :
    BitVec.setWidth 8 (x &&& y) = BitVec.setWidth 8 x &&& BitVec.setWidth 8 y :=
  BitVec.setWidth_and

@[local simp, local wp_norm, local arm64_norm]
private theorem ite_one_zero_and_8_ext (b1 b2 : Bool) :
    ((if b1 = true then 1#8 else 0#8) &&& (if b2 = true then 1#8 else 0#8)) =
      if (b1 && b2) = true then 1#8 else 0#8 := by
  cases b1 <;> cases b2 <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_and_4294967297_ext (x : BitVec 64) :
    BitVec.setWidth 32 (x &&& 4294967297#64) =
      BitVec.zeroExtend 32 (BitVec.setWidth 8 x &&& 1#8) := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem ite_one_zero_and_one_8_ext (b : Bool) :
    ((if b = true then 1#8 else 0#8) &&& 1#8) =
      if b = true then 1#8 else 0#8 := by
  cases b <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem zeroExtend32_ite_one_zero_8_ext (b : Bool) :
    BitVec.zeroExtend 32 (if b = true then 1#8 else 0#8) =
      if b = true then 1#32 else 0#32 := by
  cases b <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_32_ext (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#32 else 0#32) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

attribute [local simp, local wp_norm, local arm64_norm] Bool.and_assoc

private theorem ct_eq_bool_32_u8_ext {k1 k2 : List (BitVec 8)} (h1 : k1.length = 32) (h2 : k2.length = 32) :
    (if (k1.getD 0 0#8 == k2.getD 0 0#8 &&
        (k1.getD 1 0#8 == k2.getD 1 0#8 &&
        (k1.getD 2 0#8 == k2.getD 2 0#8 &&
        (k1.getD 3 0#8 == k2.getD 3 0#8 &&
        (k1.getD 4 0#8 == k2.getD 4 0#8 &&
        (k1.getD 5 0#8 == k2.getD 5 0#8 &&
        (k1.getD 6 0#8 == k2.getD 6 0#8 &&
        (k1.getD 7 0#8 == k2.getD 7 0#8 &&
        (k1.getD 8 0#8 == k2.getD 8 0#8 &&
        (k1.getD 9 0#8 == k2.getD 9 0#8 &&
        (k1.getD 10 0#8 == k2.getD 10 0#8 &&
        (k1.getD 11 0#8 == k2.getD 11 0#8 &&
        (k1.getD 12 0#8 == k2.getD 12 0#8 &&
        (k1.getD 13 0#8 == k2.getD 13 0#8 &&
        (k1.getD 14 0#8 == k2.getD 14 0#8 &&
        (k1.getD 15 0#8 == k2.getD 15 0#8 &&
        (k1.getD 16 0#8 == k2.getD 16 0#8 &&
        (k1.getD 17 0#8 == k2.getD 17 0#8 &&
        (k1.getD 18 0#8 == k2.getD 18 0#8 &&
        (k1.getD 19 0#8 == k2.getD 19 0#8 &&
        (k1.getD 20 0#8 == k2.getD 20 0#8 &&
        (k1.getD 21 0#8 == k2.getD 21 0#8 &&
        (k1.getD 22 0#8 == k2.getD 22 0#8 &&
        (k1.getD 23 0#8 == k2.getD 23 0#8 &&
        (k1.getD 24 0#8 == k2.getD 24 0#8 &&
        (k1.getD 25 0#8 == k2.getD 25 0#8 &&
        (k1.getD 26 0#8 == k2.getD 26 0#8 &&
        (k1.getD 27 0#8 == k2.getD 27 0#8 &&
        (k1.getD 28 0#8 == k2.getD 28 0#8 &&
        (k1.getD 29 0#8 == k2.getD 29 0#8 &&
        (k1.getD 30 0#8 == k2.getD 30 0#8 &&
        (k1.getD 31 0#8 == k2.getD 31 0#8)))))))))))))))))))))))))))))))) = true then 1#8 else 0#8) =
      (if k1 = k2 then 1#8 else 0#8) := by
  have h64 := FindReceiverChainIndex.ct_eq_bool_32 h1 h2
  have h8 := congrArg (BitVec.setWidth 8) h64
  simpa only [setWidth8_ite_1_0_ext, setWidth8_ite_prop_1_0_ext] using h8

private theorem ctEqCells_entails_ext (sp : BitVec 64) (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    (((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
     ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) ⊢
      cells (sp - 48#64) 6 := by
  refine cells_sub_succ_entails 48 6 ?_
  refine cells_sub_succ_entails 40 5 ?_
  refine cells_sub_succ_entails 32 4 ?_
  refine cells_sub_succ_entails 24 3 ?_
  refine cells_sub_succ_entails 16 2 ?_
  have h1 : (((sp - 8#64) ↦₆₄ v5) ∗ emp) ⊢ cells (sp - BitVec.ofNat 64 8) 1 :=
    cells_sub_succ_entails 8 1 (Entails.refl _)
  rwa [sepConj_emp] at h1

theorem ctEqCells_sepConj_stackAt_ext (sp : BitVec 64) :
    cells (sp - 48#64) 6 ∗ stackAt (sp - 48#64) pqxdhHookStackExt =
      stackAt sp pqxdhHookStackExt ∗ memRegion (sp - 16432#64) 48 := by
  rw [← stackAt_verifySigHook_split_48_ext sp]
  exact (ProofLib.stackAt_split_bottom sp 16384 48 (by decide)).trans (sepConj_comm _ _)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 800000 in
private theorem step_blackBox_ext
    {prog : Program} {target_pc entry_bb ret_pc : BitVec 64}
    {s0 s : State} {sp_cur x19_v x20_v : BitVec 64}
    {x0_v x19_8_v x21_8_v x22_8_v : BitVec 8}
    {R_rest : SepProp} {post : State → SepProp → Prop}
    (hbb : subroutine_ok prog entry_bb blackBoxU8SpecExt)
    (hal_cur : (sp_cur &&& 15#64 == 0#64) = true)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hlr : s.readReg64 (Reg.gpr 30#5) = ret_pc)
    (hx0 : (s.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x19_v)
    (hx19_8 : (s.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x20_v)
    (hx21_8 : (s.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v)
    (hx22_8 : (s.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5))
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hx28 : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5))
    (hx29 : s.readReg64 (Reg.gpr 29#5) = sp_cur)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = sp_cur →
      (sf.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v →
      sf.readReg64 (Reg.gpr 19#5) = x19_v →
      (sf.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v →
      sf.readReg64 (Reg.gpr 20#5) = x20_v →
      (sf.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v →
      (sf.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v →
      sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) →
      sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) →
      sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) →
      sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) →
      sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) →
      sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) →
      sf.readReg64 (Reg.gpr 29#5) = sp_cur →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.trace = s0.trace →
      SepWP prog target_pc sf (stackAt sp_cur pqxdhHookStackExt ∗ R_rest) post) :
    SepWP prog target_pc s (stackAt sp_cur pqxdhHookStackExt ∗ R_rest) post := by
  have hal : s.spAligned = true := by
    unfold State.spAligned
    rwa [hsp]
  refine SepWP.call_subroutine_frame hbb (x := s.readReg64 .x0) (F := R_rest)
    hpc hrun hal hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hret_pc hret_run hsp_sf0 hcs => ?_)
  · intro R hm
    rw [sepConj_assoc] at hm
    simp only [blackBoxU8SpecExt, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨trivial, hm⟩
  · dsimp only [blackBoxU8SpecExt]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hx0_sf, htr_sf⟩ => ?_
    have hsp_sf : sf.sp = sp_cur := hsp_sf0.trans hsp
    have hx19_sf : sf.readReg64 (Reg.gpr 19#5) = x19_v := hcs.1.trans hx19
    have hx19_8_sf : (sf.readReg64 (Reg.gpr 19#5)).setWidth 8 = x19_8_v := by
      change (sf.readReg64 .x19).setWidth 8 = x19_8_v
      rw [hcs.1]; exact hx19_8
    have hx20_sf : sf.readReg64 (Reg.gpr 20#5) = x20_v := hcs.2.1.trans hx20
    have hx21_8_sf : (sf.readReg64 (Reg.gpr 21#5)).setWidth 8 = x21_8_v := by
      change (sf.readReg64 .x21).setWidth 8 = x21_8_v
      rw [hcs.2.2.1]; exact hx21_8
    have hx22_8_sf : (sf.readReg64 (Reg.gpr 22#5)).setWidth 8 = x22_8_v := by
      change (sf.readReg64 .x22).setWidth 8 = x22_8_v
      rw [hcs.2.2.2.1]; exact hx22_8
    have hx23_sf : sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) := hcs.2.2.2.2.1.trans hx23
    have hx24_sf : sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) := hcs.2.2.2.2.2.1.trans hx24
    have hx25_sf : sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := hcs.2.2.2.2.2.2.1.trans hx25
    have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := hcs.2.2.2.2.2.2.2.1.trans hx26
    have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := hcs.2.2.2.2.2.2.2.2.1.trans hx27
    have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := hcs.2.2.2.2.2.2.2.2.2.1.trans hx28
    have hx29_sf : sf.readReg64 (Reg.gpr 29#5) = sp_cur := hcs.2.2.2.2.2.2.2.2.2.2.1.trans hx29
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := hcs.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
    exact hnext sf hret_pc hret_run hsp_sf
      (hx0_sf.trans hx0) hx19_sf hx19_8_sf hx20_sf hx21_8_sf hx22_8_sf
      hx23_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf hvregs_sf
      (htr_sf.trans htr)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 800000 in
private theorem step_blackBox_tail_ext
    {prog : Program} {entry_bb : BitVec 64}
    {s0 s : State} {x0_v x0_target : BitVec 8}
    {v0 v1 v2 v3 v4 v5 : BitVec 64}
    {R_slices S1 S2 R0 : SepProp}
    (hbb : subroutine_ok prog entry_bb blackBoxU8SpecExt)
    (hal_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hlr : s.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5))
    (hx0 : (s.readReg64 (Reg.gpr 0#5)).setWidth 8 = x0_v)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5))
    (hx20 : s.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5))
    (hx21 : s.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5))
    (hx22 : s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5))
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hx28 : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5))
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hx0_eq : x0_v = x0_target)
    (h_slices : R_slices = S1 ∗ S2) :
    SepWP prog (s0.readReg64 .lr) s
      (stackAt (s0.sp - 48#64) pqxdhHookStackExt ∗
        ((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
        ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5) ∗
        R_slices)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R0 →
          sf.mem ⊨
            (⌜(sf.readReg64 .x0).setWidth 8 = x0_target ∧ sf.trace = s0.trace⌝ ∗
              S1 ∗ S2 ∗
              cells (s0.sp - 48#64) 6 ∗
              stackAt (s0.sp - 48#64) pqxdhHookStackExt) ∗ R0) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hal : s.spAligned = true := by
    unfold State.spAligned
    rwa [hsp]
  refine SepWP.call_subroutine_frame hbb (x := s.readReg64 .x0)
    (F := memRegion (s0.sp - 16432#64) 48 ∗ R_slices)
    hpc hrun hal hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hret_pc hret_run hsp_sf0 hcs => ?_)
  · intro R hm
    have hm1 : s.mem ⊨
        (cells (s0.sp - 48#64) 6 ∗
          stackAt (s0.sp - 48#64) pqxdhHookStackExt) ∗ (R_slices ∗ R) := by
      have hrearr :
          (stackAt (s0.sp - 48#64) pqxdhHookStackExt ∗
            ((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
            ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5) ∗
            R_slices) ∗ R =
          (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗ ((s0.sp - 32#64) ↦₆₄ v2) ∗
            ((s0.sp - 24#64) ↦₆₄ v3) ∗ ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗
          (stackAt (s0.sp - 48#64) pqxdhHookStackExt ∗ (R_slices ∗ R)) := by ac_rfl
      rw [hrearr] at hm
      have hm' := Satisfies.mono (sepConj_mono_left (ctEqCells_entails_ext s0.sp v0 v1 v2 v3 v4 v5)) hm
      rwa [← sepConj_assoc] at hm'
    rw [ctEqCells_sepConj_stackAt_ext s0.sp, sepConj_assoc] at hm1
    simp only [blackBoxU8SpecExt, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨trivial, by simpa only [sepConj_assoc] using hm1⟩
  · dsimp only [blackBoxU8SpecExt]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hx0_sf, htr_sf⟩ => ?_
    have hrearr_post :
        stackAt s0.sp pqxdhHookStackExt ∗ (memRegion (s0.sp - 16432#64) 48 ∗ R_slices) =
        S1 ∗ S2 ∗ cells (s0.sp - 48#64) 6 ∗ stackAt (s0.sp - 48#64) pqxdhHookStackExt := by
      rw [← sepConj_assoc, ← ctEqCells_sepConj_stackAt_ext s0.sp, h_slices]
      ac_rfl
    rw [hrearr_post]
    apply SepWP.done hret_pc hret_run
    refine ⟨?_, hsp_sf0.trans hsp,
      ⟨hcs.1.trans hx19, hcs.2.1.trans hx20, hcs.2.2.1.trans hx21, hcs.2.2.2.1.trans hx22,
       hcs.2.2.2.2.1.trans hx23, hcs.2.2.2.2.2.1.trans hx24, hcs.2.2.2.2.2.2.1.trans hx25,
       hcs.2.2.2.2.2.2.2.1.trans hx26, hcs.2.2.2.2.2.2.2.2.1.trans hx27,
       hcs.2.2.2.2.2.2.2.2.2.1.trans hx28, hcs.2.2.2.2.2.2.2.2.2.2.1.trans hx29,
       hcs.2.2.2.2.2.2.2.2.2.2.2.trans hvregs⟩⟩
    intro hm_R0
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm_R0 ⊢
    exact ⟨⟨(hx0_sf.trans hx0).trans hx0_eq, htr_sf.trans htr⟩, hm_R0⟩

private theorem ctEq_pre_rearrange_ext (S1 S2 C0 C1 C2 C3 C4 C5 Stk : SepProp) :
    S1 ∗ S2 ∗ C0 ∗ C1 ∗ C2 ∗ C3 ∗ C4 ∗ C5 ∗ Stk =
      Stk ∗ C0 ∗ C1 ∗ C2 ∗ C3 ∗ C4 ∗ C5 ∗ (S1 ∗ S2) := by
  ac_rfl

private theorem sp_sub48_aligned_ext {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 48#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_bits

set_option hygiene false in
local macro "wp_black_box_ext " hbb:ident hal:ident : tactic =>
  `(tactic| (
    refine step_blackBox_ext $hbb $hal
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) ?_
    try clear hpc_bb hrun_bb hsp_bb hx0_bb hx19_bb hx19_8_bb hx20_bb hx21_8_bb hx22_8_bb hx23_bb hx24_bb hx25_bb hx26_bb hx27_bb hx28_bb hx29_bb hvregs_bb htr_bb s_bb
    intro s_bb hpc_bb hrun_bb hsp_bb hx0_bb hx19_bb hx19_8_bb hx20_bb hx21_8_bb hx22_8_bb hx23_bb hx24_bb hx25_bb hx26_bb hx27_bb hx28_bb hx29_bb hvregs_bb htr_bb
  ))

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
theorem pqxdh_ct_eq_slice_ok_ext (b : BitVec 64) {absHooks : String → Option (State → State)}
    (hbb_hook : HookSat absHooks "subtle::black_box::<u8>" SignalSession.CliExt.blackBoxSpec) :
    subroutine_ok (PPX b absHooks) ((PPX b absHooks).fnAddr ConsumeMessageKeyTransfer.ctEqName)
      pqxdhCtEqSliceSpecExt := by
  have hbb := blackBox_u8_ok_at_ext (b := b) hbb_hook
    (name := ConsumeMessageKeyTransfer.ctEqName)
    (k := num% (ls_off% "subtle::black_box::<u8>" - ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq"))
  clear hbb_hook
  dsimp only [tripleRatchetProgAtExt, ConsumeMessageKeyTransfer.ctEqName] at hbb ⊢
  simp only [pqxdhCtEqSliceSpecExt]
  code_fetches libsignalSessionCode libsignalSessionBin b (Rust.withPanics absHooks)
    (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq")
    (num% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq")) 840
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  cells_pre_unfold_fast
  wp_extract_exists
  dsimp only at *
  subst h_1 h_2 h_3
  have hal_sub48 : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    sp_sub48_aligned_ext hsp_align
  have h_slices :
      FindReceiverChainIndex.pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) k1 ∗
        FindReceiverChainIndex.pointsToBytes32 (s0.readReg64 (Reg.gpr 1#5)) k2 =
      ((s0.readReg64 (Reg.gpr 0#5)) ↦ₛ k1) ∗ ((s0.readReg64 (Reg.gpr 1#5)) ↦ₛ k2) := by
    rw [FindReceiverChainIndex.pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) h_4,
        FindReceiverChainIndex.pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 1#5)) h]
  rw [ctEq_pre_rearrange_ext]
  conv =>
    arg 4
    rw [← h_slices]
    unfold FindReceiverChainIndex.pointsToBytes32
    simp only [sepConj_assoc]
  wp_steps
  iterate 31 (wp_black_box_ext hbb hal_sub48; wp_steps)
  wp_black_box_ext hbb hal_sub48
  clear hx19_bb
  wp_steps
  refine step_blackBox_tail_ext hbb hsp_align
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (ct_eq_bool_32_u8_ext h_4 h) ?_
  rw [← h_slices]
  unfold FindReceiverChainIndex.pointsToBytes32
  simp only [sepConj_assoc]

set_option maxHeartbeats 4000000 in
theorem verifySig_seg2_1569_ext (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hH : PqxdhHookContractsExt P A img absHooks)
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 1569) (hst0 : st0.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 320#64)
    (hsp : s.sp = fsp) (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = 1#64) : SepWP (PPX img.base absHooks)
      ((PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStackExt ∗ Frame) (fun sm Pm => (Pm ⊢
          (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (m.drop 1472)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8
            (sha512CompressOutBytes P (sha512CompressOutBytes P st0 (pre64 ++
            m.take 64)) ((m.drop 64).take 1408))) ∗ ((fsp + 752#64) ↦₆₄ 12#64) ∗
          ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStackExt ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym =
      (num% (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")) :=
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")
  have hmemcpy := memcpy_region_ok_at_ext (b := img.base) hH.memcpy
    (name := verifySignatureMultipartSym)
    (k := num% (ls_off% "memcpy" - (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")))
  have hsha := sha512CompressStub_ok_at_ext hH
    (name := verifySignatureMultipartSym)
    (k := num% (ls_off% "sha2::sha512::compress512" - (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")))
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 320) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 320))
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 324) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 324))
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 328) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 328))
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 332) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 332))
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 336) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 336))
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 340) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 340))
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 344) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 344))
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 348) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 348))
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 352) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 352))
  have f9 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 356) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 356))
  have f10 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 360) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 360))
  have f11 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 364) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 364))
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 368) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 368))
  have f13 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 372) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 372))
  have f14 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 376) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 376))
  have f15 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 380) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 380))
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 384) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 384))
  have f17 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 388) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 388))
  have f18 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 392) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 392))
  have f19 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 396) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 396))
  have f20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 400) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 400))
  have f21 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 404) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 404))
  have f22 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 408) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 408))
  have f23 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 412) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 412))
  have f24 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 416) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 416))
  have f25 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 420) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 420))
  have f26 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 424) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 424))
  have f27 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 428) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 428))
  have f28 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 432) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 432))
  have f29 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 436) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 436))
  have f30 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 440) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 440))
  have f31 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 444) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 444))
  have f32 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 448) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 448))
  have f33 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 452) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 452))
  have f34 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 456) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 456))
  have f35 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 460) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 460))
  have f36 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 464) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 464))
  have f37 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 468) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 468))
  have f38 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 472) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 472))
  have f39 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 476) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 476))
  have f40 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 480) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 480))
  have f41 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 484) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 484))
  have f42 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 488) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 488))
  have f43 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 492) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 492))
  have f44 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 496) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 496))
  have f45 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 500) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 500))
  have f46 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 504) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 504))
  have f47 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 508) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 508))
  have f48 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 512) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 512))
  have f49 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 516) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 516))
  have f50 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 520) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 520))
  have f51 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 524) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 524))
  have f52 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 528) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 528))
  have f53 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 532) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 532))
  have f54 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 536) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 536))
  have f55 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 540) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 540))
  have f56 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 544) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 544))
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hsha hpc ⊢
  clear hfn hH
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics absHooks)).fnAddr verifySignatureMultipartSym = entry
  examples_hide_fetches
  have hlen_m64_bv : (bytesToBv8 (m.take 64)).length = 64 := by simp [bytesToBv8, hm]
  have hlen_m1408 : ((m.drop 64).take 1408).length = 128 * 11 := by simp [hm]
  have hlen_m1408_bv : (bytesToBv8 ((m.drop 64).take 1408)).length = 1408 := by simp [bytesToBv8, hm]
  have hlen_m97_bv : (bytesToBv8 (m.drop 1472)).length = 97 := by simp [bytesToBv8, hm]
  have hlen_pre_bv : (bytesToBv8 pre64).length = 64 := by simp [bytesToBv8, hpre64]
  have hlen_blk0 : (pre64 ++ m.take 64).length = 128 * 1 := by simp [hpre64, hm]
  have hlen_blk0_bv : (bytesToBv8 (pre64 ++ m.take 64)).length = 128 := by simp [bytesToBv8, hpre64, hm]
  have hst1_len : (sha512CompressOutBytes P st0 (pre64 ++ m.take 64)).length = 64 :=
    sha512CompressOutBytes_length P _ _
  have hm_split : msgPtr ↦ₛ bytesToBv8 m = ((msgPtr ↦ₛ bytesToBv8 (m.take 64)) ∗
       ((msgPtr + 64#64) ↦ₛ bytesToBv8 ((m.drop 64).take 1408)) ∗
       ((msgPtr + 1472#64) ↦ₛ bytesToBv8 (m.drop 1472))) := by
    have h1 : m = m.take 64 ++ ((m.drop 64).take 1408 ++ m.drop 1472) := by
      have ha : (m.drop 64).take 1408 ++ m.drop 1472 = m.drop 64 := by
        rw [show (1472 : Nat) = 64 + 1408 from rfl, ← List.drop_drop, List.take_append_drop]
      rw [ha, List.take_append_drop]
    conv => lhs; rw [h1, bytesToBv8_append, bytesToBv8_append]
    rw [pointsToBytes_append, pointsToBytes_append, hlen_m64_bv, hlen_m1408_bv]
    have h64 : BitVec.ofNat 64 64 = 64#64 := rfl
    have h1408 : 64#64 + BitVec.ofNat 64 1408 = 1472#64 := rfl
    rw [h64, BitVec.add_assoc, h1408]
  have hbuf64_in : memRegion (fsp + 624#64) 63 ∗ ((fsp + 687#64) ↦₈ 64#8) ⊢
      memRegion (fsp + 624#64) (bytesToBv8 (m.take 64)).length := by
    rw [hlen_m64_bv, ProofLib.memRegion_split' (b := fsp + 624#64) (n := 63) (k := 1) (b' :=
      fsp + 687#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
    exact sepConj_mono_right (Entails.sepExists_intro 64#8)
  have hbuf128_weaken : ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m.take 64)) ⊢
      memRegion (fsp + 560#64) (bytesToBv8 (m.drop 1472)).length ∗ memRegion (fsp + 657#64) 30 ∗
      (∃∗ b687 : BitVec 8, (fsp + 687#64) ↦₈ b687) := by
    refine Entails.trans (Q := memRegion (fsp + 560#64) 128) ?_ (Entails.of_eq ?_)
    · rw [← hlen_blk0_bv]; exact pointsToBytes_entails_memRegion _ _
    · rw [hlen_m97_bv, ProofLib.memRegion_split' (b := fsp + 560#64) (n := 97) (k := 31) (b' :=
        fsp + 657#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 657#64) (n := 30) (k := 1) (b' :=
        fsp + 687#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hm_split) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf64_in) (by sep_frame)
  wp_call hmemcpy ⟨fsp + 624#64, msgPtr, bytesToBv8 (m.take 64)⟩
  have hmerge128 : ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ ((fsp +
    624#64) ↦ₛ bytesToBv8 (m.take 64)) = ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m.take 64)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hlen_pre_bv, BitVec.add_assoc]
    rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge128) (by sep_frame)
  wp_steps
  wp_call hsha ⟨fsp + 688#64, st0, fsp + 560#64, pre64 ++ m.take 64, 1⟩
  rw [fitBv8_64_sha512CompressOutBytes]
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf128_weaken) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  wp_steps
  wp_call hsha ⟨fsp + 688#64, sha512CompressOutBytes P st0 (pre64 ++ m.take 64), msgPtr + 64#64,
    (m.drop 64).take 1408, 11⟩
  rw [fitBv8_64_sha512CompressOutBytes]
  wp_steps
  wp_call hmemcpy ⟨fsp + 560#64, msgPtr + 1472#64, bytesToBv8 (m.drop 1472)⟩
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hm_split.symm) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_2, hsp_sf_1, hsp_sf, hsp]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 4000000 in
theorem verifySig_seg3a_ext (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hH : PqxdhHookContractsExt P A img absHooks)
    (s : State) (fsp : BitVec 64) (tail97 st : Bytes) (blkCnt : BitVec 64) (L : Nat)
    (Frame : SepProp) (htail97 : tail97.length = 97) (hst : st.length = 64)
    (hblkL : (blkCnt = 0#64 ∧ L = 97) ∨ (blkCnt = 12#64 ∧ L = 1633))
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) : SepWP (PPX img.base absHooks)
      ((PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 992#64) s
      (((fsp + 560#64) ↦ₛ bytesToBv8 tail97) ∗ memRegion (fsp + 657#64) 30 ∗
       ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st) ∗ ((fsp + 752#64) ↦₆₄ blkCnt) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ memRegion (fsp + 768#64) 32 ∗ cells (fsp + 800#64) 16 ∗
       cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗ stackAt fsp pqxdhHookStackExt ∗ Frame)
      (fun sm Pm => (Pm ⊢ cells (fsp + 560#64) 16 ∗ cells (fsp + 688#64) 10 ∗
          ((fsp + 768#64) ↦ₛ fitBv8 32 (P.scalarFromWide (revWords64 (sha512CompressOutBytes P st
              (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L))))) ∗
          cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗
          stackAt fsp pqxdhHookStackExt ∗ Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 992#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = fsp + 800#64 ∧ sm.readReg64 (.gpr 29#5) = fsp + 1152#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym =
      (num% (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")) :=
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")
  have hmemset := memset_region_ok_at_ext (b := img.base) hH.memset
    (name := verifySignatureMultipartSym)
    (k := num% (ls_off% "memset" - (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")))
  have hsha := sha512CompressStub_ok_at_ext hH
    (name := verifySignatureMultipartSym)
    (k := num% (ls_off% "sha2::sha512::compress512" - (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")))
  have hwide := dalekScalarWideStub_ok_at_ext hH
    (name := verifySignatureMultipartSym)
    (k := num% (ls_off% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide" - (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")))
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 548) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 548))
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 552) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 552))
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 556) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 556))
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 560) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 560))
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 564) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 564))
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 568) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 568))
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 572) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 572))
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 576) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 576))
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 580) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 580))
  have f9 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 584) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 584))
  have f10 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 588) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 588))
  have f11 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 592) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 592))
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 596) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 596))
  have f13 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 600) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 600))
  have f14 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 604) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 604))
  have f15 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 608) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 608))
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 612) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 612))
  have f17 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 616) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 616))
  have f18 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 620) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 620))
  have f19 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 624) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 624))
  have f20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 628) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 628))
  have f21 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 632) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 632))
  have f22 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 636) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 636))
  have f23 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 640) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 640))
  have f24 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 644) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 644))
  have f25 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 648) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 648))
  have f26 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 652) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 652))
  have f27 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 656) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 656))
  have f28 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 660) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 660))
  have f29 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 664) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 664))
  have f30 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 668) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 668))
  have f31 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 672) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 672))
  have f32 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 676) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 676))
  have f33 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 680) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 680))
  have f34 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 684) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 684))
  have f35 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 688) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 688))
  have f36 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 692) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 692))
  have f37 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 696) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 696))
  have f38 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 700) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 700))
  have f39 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 704) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 704))
  have f40 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 708) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 708))
  have f41 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 712) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 712))
  have f42 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 716) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 716))
  have f43 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 720) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 720))
  have f44 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 724) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 724))
  have f45 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 728) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 728))
  have f46 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 732) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 732))
  have f47 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 736) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 736))
  have f48 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 740) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 740))
  have f49 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 744) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 744))
  have f50 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 748) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 748))
  have f51 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 752) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 752))
  have f52 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 756) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 756))
  have f53 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 760) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 760))
  have f54 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 764) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 764))
  have f55 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 768) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 768))
  have f56 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 772) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 772))
  have f57 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 776) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 776))
  have f58 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 780) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 780))
  have f59 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 784) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 784))
  have f60 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 788) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 788))
  have f61 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 792) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 792))
  have f62 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 796) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 796))
  have f63 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 800) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 800))
  have f64 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 804) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 804))
  have f65 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 808) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 808))
  have f66 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 812) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 812))
  have f67 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 816) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 816))
  have f68 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 820) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 820))
  have f69 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 824) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 824))
  have f70 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 828) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 828))
  have f71 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 832) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 832))
  have f72 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 836) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 836))
  have f73 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 840) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 840))
  have f74 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 844) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 844))
  have f75 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 848) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 848))
  have f76 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 852) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 852))
  have f77 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 856) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 856))
  have f78 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 860) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 860))
  have f79 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 864) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 864))
  have f80 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 868) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 868))
  have f81 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 872) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 872))
  have f82 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 876) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 876))
  have f83 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 880) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 880))
  have f84 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 884) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 884))
  have f85 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 888) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 888))
  have f86 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 892) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 892))
  have f87 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 896) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 896))
  have f88 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 900) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 900))
  have f89 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 904) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 904))
  have f90 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 908) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 908))
  have f91 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 912) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 912))
  have f92 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 916) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 916))
  have f93 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 920) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 920))
  have f94 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 924) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 924))
  have f95 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 928) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 928))
  have f96 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 932) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 932))
  have f97 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 936) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 936))
  have f98 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 940) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 940))
  have f99 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 944) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 944))
  have f100 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 948) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 948))
  have f101 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 952) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 952))
  have f102 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 956) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 956))
  have f103 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 960) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 960))
  have f104 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 964) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 964))
  have f105 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 968) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 968))
  have f106 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 972) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 972))
  have f107 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 976) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 976))
  have f108 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 980) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 980))
  have f109 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 984) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 984))
  have f110 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 988) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 988))
  dsimp only [tripleRatchetProgAtExt] at hmemset hsha hwide hpc ⊢
  clear hfn hH
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics absHooks)).fnAddr verifySignatureMultipartSym = entry
  examples_hide_fetches
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, p12, p13, hp1, hp2, hp3⟩ :=
    exists_pad97_cells htail97
  have hst_bv : (bytesToBv8 st).length = 64 := by simp [bytesToBv8, hst]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hw_st⟩ := exists_unpack64_of_length_64 hst_bv
  cells_pre_unfold_fast
  wp_extract_exists
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hp1 (fsp + 560#64))) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hw_st (fsp + 688#64))) (by sep_frame)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply ProofLib.SepWP.replace_pre
    (hPQ := blockBuf_tail32_pack (fsp + 656#64) ((bytesToBv8 tail97).getD 96 0#8) 97#8)
    (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_left; intro b12
  apply SepWP.exists_left; intro b13
  apply SepWP.exists_left; intro b14
  apply SepWP.exists_left; intro b15
  apply SepWP.pure_elim; rintro ⟨hb12, hb15⟩
  wp_steps
  have hsp7 : ((fsp + 920#64) ↦₆₄ b15) =
      (((fsp + 920#64) ↦ₛ first7 b15) ∗ ((fsp + 927#64) ↦₈ 97#8)) := by
    rw [cell_split7 (fsp + 920#64) b15, hb15, BitVec.add_assoc]; rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsp7) (by sep_frame)
  wp_steps
  have hunpack32 := blockBuf_tail32_unpack (fsp + 896#64) b12 b13 b14 b15
    ((bytesToBv8 tail97).getD 96 0#8) 97#8 hb12
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hunpack32
  apply ProofLib.SepWP.replace_pre (hPQ := hunpack32) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  wp_steps
  wp_call hmemset (fsp + 898#64, 0#8, 30)
  have hp2_896 := hp2 (fsp + 896#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp2_896
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp2_896) (by sep_frame)
  wp_steps
  have hbithi : rev64 (BitVec.truncate 64 ((0#64 ++ blkCnt) >>> 54)) = 0#64 := by
    rcases hblkL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hbitlo : rev64 (blkCnt <<< 10 ||| 776#64) = rev64 (BitVec.ofNat 64 (8 * L)) := by
    rcases hblkL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hL_or : L = 97 ∨ L = 1633 := hblkL.imp And.right And.right
  have hp3_1008 := hp3 (fsp + 1008#64) hL_or
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp3_1008
  have hw_st_928 := (hw_st (fsp + 928#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hw_st_928
  wp_simp_pre_fast [hbithi, hbitlo]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp3_1008) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hw_st_928) (by sep_frame)
  have hpad_len : (tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L)).length = 128 := by
    simp [encodeBitLen128BE, encodeBitLen64BE, htail97]
  wp_call hsha ⟨fsp + 928#64, st, fsp + 1008#64, tail97 ++ [0x80] ++ List.replicate 14 0 ++
    encodeBitLen128BE L, 1⟩
  have hpad_norm : tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L) =
      tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L := by
    simp [List.append_assoc]
  wp_simp_pre_fast [fitBv8_64_sha512CompressOutBytes, hpad_norm]
  have hst_out_len : (sha512CompressOutBytes P st (tail97 ++ [0x80] ++ List.replicate 14 0 ++
    encodeBitLen128BE L)).length = 64 := sha512CompressOutBytes_length P _ _
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, hu_st, hu_rev⟩ :=
    exists_unpack64_revWords64_of_length_64 hst_out_len
  have hu_st_928 := hu_st (fsp + 928#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu_st_928
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_st_928) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp3_1008.symm) (by sep_frame)
  have hsp7_920 := cell_split7 (fsp + 920#64) (rev64 (BitVec.ofNat 64 (8 * L)))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsp7_920
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsp7_920) (by sep_frame)
  wp_steps
  have hpk7_920 := first7_pack (fsp + 920#64) (rev64 (BitVec.ofNat 64 (8 * L))) 0#8
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpk7_920
  apply ProofLib.SepWP.replace_pre (hPQ := hpk7_920) (by sep_frame)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro _
  wp_steps
  have hu_rev_1008 := (hu_rev (fsp + 1008#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu_rev_1008
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_rev_1008) (by sep_frame)
  have hrev_len : (revWords64 (sha512CompressOutBytes P st (tail97 ++ 128 :: (List.replicate 14 0 ++
    encodeBitLen128BE L)))).length = 64 := revWords64_length (sha512CompressOutBytes_length P _ _)
  wp_call hwide ⟨fsp + 1008#64, revWords64 (sha512CompressOutBytes P st (tail97 ++ [0x80] ++
    List.replicate 14 0 ++ encodeBitLen128BE L)), fsp + 768#64⟩
  wp_simp_pre_fast [hpad_norm]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_rev_1008.symm) (by sep_frame)
  have hm560 := cells_16_merge (fsp + 560#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm560
  apply ProofLib.SepWP.replace_pre (hPQ := hm560) (by sep_frame)
  have hm688 := cells_10_merge (fsp + 688#64) w0 w1 w2 w3 w4 w5 w6 w7 blkCnt 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm688
  apply ProofLib.SepWP.replace_pre (hPQ := hm688) (by sep_frame)
  have hm800 := cells_16_merge (fsp +
    800#64) 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm800
  apply ProofLib.SepWP.replace_pre (hPQ := hm800) (by sep_frame)
  have hm928 := cells_10_merge (fsp + 928#64) u0 u1 u2 u3 u4 u5 u6 u7 blkCnt 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm928
  apply ProofLib.SepWP.replace_pre (hPQ := hm928) (by sep_frame)
  have hm1008 := cells_16_merge (fsp +
    1008#64) (rev64 u0) (rev64 u1) (rev64 u2) (rev64 u3) (rev64 u4) (rev64 u5) (rev64 u6) (rev64 u7)
    0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1008
  apply ProofLib.SepWP.replace_pre (hPQ := hm1008) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_1, hsp_sf, hsp]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 8000000 in
theorem verifySig_seg2_33_ext (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hH : PqxdhHookContractsExt P A img absHooks)
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 33) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 320#64)
    (hsp : s.sp = fsp) (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = 1#64) : SepWP (PPX img.base absHooks)
      ((PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStackExt ∗ Frame) (fun sm Pm => (Pm ⊢
          (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗
          ((fsp + 752#64) ↦₆₄ 0#64) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStackExt ∗
          Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym =
      (num% (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")) :=
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")
  have hmemcpy := memcpy_region_ok_at_ext (b := img.base) hH.memcpy
    (name := verifySignatureMultipartSym)
    (k := num% (ls_off% "memcpy" - (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")))
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 320) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 320))
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 324) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 324))
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 328) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 328))
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 332) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 332))
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 336) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 336))
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 340) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 340))
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 344) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 344))
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 348) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 348))
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 352) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 352))
  have f9 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 356) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 356))
  have f10 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 360) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 360))
  have f11 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 364) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 364))
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 368) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 368))
  have f13 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 372) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 372))
  have f14 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 376) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 376))
  have f15 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 380) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 380))
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 384) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 384))
  have f17 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 388) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 388))
  have f18 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 392) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 392))
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  clear hfn hH
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics absHooks)).fnAddr verifySignatureMultipartSym = entry
  examples_hide_fetches
  have hlen_pre_bv : (bytesToBv8 pre64).length = 64 := by simp [bytesToBv8, hpre64]
  have hlen_m_bv : (bytesToBv8 m).length = 33 := by simp [bytesToBv8, hm]
  have hbuf63_split : memRegion (fsp + 624#64) 63 =
      memRegion (fsp + 624#64) (bytesToBv8 m).length ∗ memRegion (fsp + 657#64) 30 := by
    rw [hlen_m_bv]
    exact ProofLib.memRegion_split' (b := fsp + 624#64) (n := 33) (k := 30) (b' := fsp + 657#64)
      rfl (by bv_omega) (by decide)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hbuf63_split) (by sep_frame)
  wp_steps
  wp_call hmemcpy ⟨fsp + 624#64, msgPtr, bytesToBv8 m⟩
  have hmerge97 : ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ ((fsp + 624#64) ↦ₛ bytesToBv8 m) =
      ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hlen_pre_bv, BitVec.add_assoc]
    rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge97) (by sep_frame)
  wp_steps
  wp_simp_pre_fast [hsp]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 4000000 in
theorem verifySig_seg3b_ext (P : Primitives) (A : RustAlloc) (img : Obj.Image)
    (absHooks : String → Option (State → State)) (hWF : StructuralPrims P)
    (hH : PqxdhHookContractsExt P A img absHooks) (s : State) (fsp sigPtr : BitVec 64)
    (sig minusCapA hScalar : Bytes) (Frame : SepProp) (hsig : sig.length = 64)
    (hnegA : minusCapA.length = 160) (hh : hScalar.length = 32) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 992#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) : SepWP (PPX img.base absHooks)
      ((PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 1100#64) s
      (((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
       ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
       ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗ ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗
       cells (fsp + 800#64) 4 ∗ memRegion (fsp + 832#64) 128 ∗ memRegion (fsp + 1008#64) 32 ∗
       stackAt fsp verifySigHookStackExt ∗ Frame) (fun sm Pm => (Pm ⊢
          ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
          ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
          ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗ ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗
          memRegion (fsp + 800#64) 160 ∗ memRegion (fsp + 1008#64) 32 ∗
          stackAt fsp verifySigHookStackExt ∗ Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (PPX img.base absHooks).fnAddr verifySignatureMultipartSym + 1100#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 0#5) =
          (let sClamped := (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]
           let sScalar := P.scalarFromBytesModOrder sClamped
           let capRCheck := P.compress (P.doubleScalarMulBasepoint hScalar minusCapA sScalar)
           if (capRCheck == sig.take 32) = true then 1#64 else 0#64) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hfn : libsignalSessionCode.fnOff verifySignatureMultipartSym =
      (num% (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")) :=
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")
  have hmod := dalekScalarModStub_ok_at_ext hH
    (name := verifySignatureMultipartSym)
    (k := num% (ls_off% "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order" - (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")))
  have hdmul := dalekDoubleMulStub_ok_at_ext hH
    (name := verifySignatureMultipartSym)
    (k := num% (ls_off% "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint" - (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")))
  have hcomp := dalekCompressStub_ok_at_ext hH
    (name := verifySignatureMultipartSym)
    (k := num% (ls_off% "<curve25519_dalek::edwards::EdwardsPoint>::compress" - (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")))
  have hcteq := subroutine_ok_rel_pqxdh_ext (pqxdh_ct_eq_slice_ok_ext img.base hH.blackBox)
    (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq") hfn
    (k := num% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" - (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message")))
    (by decide)
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 992) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 992))
  have f1 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 996) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 996))
  have f2 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1000) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1000))
  have f3 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1004) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1004))
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1008) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1008))
  have f5 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1012) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1012))
  have f6 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1016) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1016))
  have f7 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1020) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1020))
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1024) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1024))
  have f9 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1028) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1028))
  have f10 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1032) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1032))
  have f11 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1036) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1036))
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1040) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1040))
  have f13 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1044) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1044))
  have f14 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1048) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1048))
  have f15 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1052) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1052))
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1056) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1056))
  have f17 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1060) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1060))
  have f18 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1064) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1064))
  have f19 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1068) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1068))
  have f20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1072) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1072))
  have f21 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1076) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1076))
  have f22 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1080) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1080))
  have f23 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics absHooks) (k := 1084) hfn (by decide) (ls_decode% verifySignatureMultipart (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 1084))
  dsimp only [tripleRatchetProgAtExt] at hmod hdmul hcomp hcteq hpc ⊢
  clear hfn hH
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics absHooks)).fnAddr verifySignatureMultipartSym = entry
  examples_hide_fetches
  have hstk_split48 : stackAt fsp verifySigHookStackExt =
      stackAt fsp pqxdhHookStackExt ∗ memRegion (fsp - 16432#64) 48 := by
    rw [stackAt_verifySigHook_split_48_ext fsp, ctEqCells_sepConj_stackAt_ext fsp]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hstk_split48) (by sep_frame)
  obtain ⟨q0_lo, q0_hi, q1_lo, q1_hi, hsig_q0, hsig_q1, hbuf_q0, hbuf_q1⟩ :=
    exists_sig_capS_cells hsig
  cells_pre_unfold_fast
  wp_extract_exists
  rename_i v0 v1 v2 v3
  have hsbuf := sClamped_buf_pre (fsp + 800#64) v0 v1 v2 v3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsbuf
  apply ProofLib.SepWP.replace_pre (hPQ := hsbuf) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig_q0 sigPtr)) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq ((hsig_q0 sigPtr).symm.trans (hsig_q1 sigPtr))) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig_q1 sigPtr).symm) (by sep_frame)
  have hbuf0 := hbuf_q0 (fsp + 800#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbuf0
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf0) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  apply SepWP.exists_left; intro _
  wp_steps
  wp_simp_pre_fast [truncate8_zeroExtend32_and7f]
  have hbuf1 := hbuf_q1 (fsp + 800#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbuf1
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hbuf1) (by sep_frame)
  have hsClamped_len : ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]).length = 32 :=
    by simp [hsig]
  wp_call hmod ⟨fsp + 800#64, (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F], fsp +
    1008#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.scalarFromBytesModOrder_len _)]
  wp_steps
  have hm160 : memRegion (fsp + 800#64) 32 ∗ memRegion (fsp + 832#64) 128 =
      memRegion (fsp + 800#64) 160 :=
    (ProofLib.memRegion_split' (b := fsp + 800#64) (n := 32) (k := 128) (b' := fsp + 832#64)
      rfl (by bv_omega) (by decide)).symm
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hm160) (by sep_frame)
  have hsScalar_len : (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
    [(List.drop 32 sig).getD 31 0 &&& 127])).length = 32 := hWF.scalarFromBytesModOrder_len _
  wp_call hdmul ⟨hScalar, minusCapA, P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
    [(List.drop 32 sig).getD 31 0 &&& 127]), fsp + 768#64, fsp + 400#64, fsp + 1008#64, fsp +
    800#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.doubleScalarMulBasepoint_len _ _ _)]
  wp_steps
  have hsScalar_bv_len : (bytesToBv8 (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
    [(List.drop 32 sig).getD 31 0 &&& 127]))).length = 32 := by
    simp [bytesToBv8, hWF.scalarFromBytesModOrder_len]
  have hm32_1008 := pointsToBytes_entails_memRegion_n (fsp + 1008#64) _ hsScalar_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm32_1008) (by sep_frame)
  have hdmul_len : (P.doubleScalarMulBasepoint hScalar minusCapA (P.scalarFromBytesModOrder
    (List.take 31 (List.drop 32 sig) ++ [(List.drop 32 sig).getD 31 0 &&& 127]))).length = 160 :=
    hWF.doubleScalarMulBasepoint_len _ _ _
  wp_call hcomp ⟨fsp + 800#64,
    P.doubleScalarMulBasepoint hScalar minusCapA (P.scalarFromBytesModOrder (List.take 31 (List.drop
    32 sig) ++ [(List.drop 32 sig).getD 31 0 &&& 127])), fsp + 1008#64⟩
  wp_simp_pre_fast [fitBv8_of_length_eq (hWF.compress_len _)]
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig)) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_1, hsp_sf, hsp]
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq (ctEqCells_sepConj_stackAt_ext fsp).symm) (by sep_frame)
  have hcapR_bv_len : (bytesToBv8 (P.compress (P.doubleScalarMulBasepoint hScalar minusCapA
    (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
    [(List.drop 32 sig).getD 31 0 &&& 127]))))).length = 32 := by
    simp [bytesToBv8, hWF.compress_len]
  have hsig32_bv_len : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
  wp_call hcteq (fsp + 1008#64,
    bytesToBv8 (P.compress (P.doubleScalarMulBasepoint hScalar minusCapA (P.scalarFromBytesModOrder
    (List.take 31 (List.drop 32 sig) ++ [(List.drop 32 sig).getD 31 0 &&& 127])))), sigPtr,
    bytesToBv8 (sig.take 32), fsp)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (sig_split_32 sigPtr hsig).symm) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ :=
    Entails.of_eq (stackAt_verifySigHook_split_48_ext fsp).symm) (by sep_frame)
  have hdmul_bv_len : (bytesToBv8 (P.doubleScalarMulBasepoint hScalar minusCapA
    (P.scalarFromBytesModOrder (List.take 31 (List.drop 32 sig) ++
    [(List.drop 32 sig).getD 31 0 &&& 127])))).length = 160 := by
    simp [bytesToBv8, hWF.doubleScalarMulBasepoint_len]
  have hm160_800 := pointsToBytes_entails_memRegion_n (fsp + 800#64) _ hdmul_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm160_800) (by sep_frame)
  have hm32_capR := pointsToBytes_entails_memRegion_n (fsp + 1008#64) _ hcapR_bv_len
  apply ProofLib.SepWP.replace_pre (hPQ := hm32_capR) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_3, hsp_sf_2, hsp_sf_1, hsp_sf, hsp]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_,
    by wp_norm_goal, by wp_norm_goal⟩
  wp_norm_goal
  refine x0_cteq_simplify_ext _ _ ?_
  rw [show ∀ u : BitVec 64,
      BitVec.setWidth 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 u)) = BitVec.setWidth 8 u by
    intro u
    change BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 u)) = BitVec.setWidth 8 u
    rw [BitVec.setWidth_setWidth_of_le (BitVec.setWidth 32 u) (by decide),
      BitVec.setWidth_setWidth_of_le u (by decide)]]
  assumption

end WithProgramExt
end CryptoVerification.E2E.Pqxdh.Shared

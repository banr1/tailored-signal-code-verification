/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Stmts
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysBase
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontSteps
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Segment 1: Keys & Sender Chain

Proves `cloneKeysFront_ok : CloneKeysFrontStmt` (`+0x1778 → +0x19b0`, `genP3Pre → genP3J1`),
cloning `local_identity_public`, `remote_identity_public`, `root_key`, and `sender_chain`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName

/-! ## 1. Modular Substage Composition for Front (`+0x1778 → +0x19b0`) -/

/- Clone `local_identity_public` (`+0x1778 → +0x18e0`, non-empty `localIk`, OOM `+0x3774`). -/
set_option maxHeartbeats 400000 in
theorem seg_locId_4k_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K img.base A ext)
    (s0 s : State) (coroPtr u_d0 : BitVec 64) (sessionVer u_7c : BitVec 32)
    (locIk : VecGhost) (hpos : 0 < locIk.bytes.length)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64) s
      (A.pool ∗ stackAt s.sp allocHookStack ∗
        vecGhostAt A locIk (coroPtr + 0xf8#64) ∗
        ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
        ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗
        ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        ∃ newLocIdPtr : BitVec 64,
          (P_f ⊢
            A.pool ∗ stackAt s.sp allocHookStack ∗
            vecGhostAt A locIk (coroPtr + 0xf8#64) ∗
            vecU8Buf A (BitVec.ofNat 64 locIk.bytes.length) newLocIdPtr locIk.bytes ∗
            ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
            ((s.sp + 0x7c#64) ↦₃₂ sessionVer) ∗
            ((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIk.bytes.length)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x23 = newLocIdPtr ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have h100 : coroPtr + 0xf8#64 + 8#64 = coroPtr + 0x100#64 := by bv_arith
  have h108 : coroPtr + 0xf8#64 + 16#64 = coroPtr + 0x108#64 := by bv_arith
  rw [vecGhostAt_eq_of_pos A locIk (coroPtr + 0xf8#64) hpos, h100, h108]
  simp only [sepConj_assoc]
  refine sepWPp_pure_3rd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  have hlen_lt63 : locIk.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hlen_le hcap_lt
  have hlen_lt64 : locIk.bytes.length < 2 ^ 64 := by omega
  have hlen_nz : BitVec.ofNat 64 locIk.bytes.length ≠ 0#64 :=
    ofNat_ne_zero_of_pos hpos hlen_lt64
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym
    (seg1a_4k_wp img.base ext hA s coroPtr locIk.ptr (BitVec.ofNat 64 locIk.bytes.length) u_d0
      sessionVer u_7c hlen_nz hpc hrun hsp_align hx19)
    (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1
      ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx21_1, hx27_1, hx29_1, hvregs1⟩ => ?_
  have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine P3P4.SepWPp.bind_sepWPp_frame_dep
    (alloc_179c_4k_ok img img.base ext hA s0 s1 (BitVec.ofNat 64 locIk.bytes.length)
      locIk.bytes.length emp hpos hlen_lt63
      hF1 hsym1 hpc1 hrun1 hsp1_al (htr1.trans htr) hx0_1 hx1_1)
    (by rw [hsp1]; sep_focus)
    fun s2 hpc2 hrun2 ⟨hnew_nz, hsp2, htr2, hcs2, hF2, hsym2⟩ => ?_
  set newLocIdPtr := s2.readReg64 .x0
  have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
  have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = locIk.ptr := hcs2.2.2.1.trans hx21_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
  have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
    hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
  refine P3P4.SepWPp.ret_sepWP_frame hF2 hsym2
    (seg1b_4k_wp img.base ext hA s2 coroPtr locIk.ptr newLocIdPtr locIk.bytes
      hnew_nz hlen_lt64 hpc2 hrun2 hsp2_al rfl hx19_2 hx21_2)
    (by simp only [hsp1, hsp2']; sep_focus)
    fun s3 _ _ hF3 hsym3 ⟨hsp3, htr3, hx19_3, hx23_3, hx27_3, hx29_3, hvregs3⟩ => ?_
  refine ⟨newLocIdPtr, ?_, hsp3.trans hsp2', by rw [htr3, htr2, htr1, htr], hF3, hsym3,
    hx19_3, hx23_3, hx27_3.trans hx27_2, hx29_3.trans hx29_2, hvregs3.trans hvregs2⟩
  rw [vecU8Buf_pos_eq A newLocIdPtr locIk.bytes hpos hlen_lt63 hnew_nz]
  simp only [sepConj_assoc, hsp1, hsp2']
  exact entails_pure_3rd ⟨hlen_le, hcap_lt, hptr⟩ (Entails.of_eq (by ac_rfl))

theorem seg_locId_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) (hA : AllocContracts img.base A ext) :
    ∀ (s0 s : State) (coroPtr u_d0 : BitVec 64) (sessionVer u_7c : BitVec 32)
      (locIk : VecGhost), 0 < locIk.bytes.length →
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64 →
      s.status = .Running → (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace → s.readReg64 .x19 = coroPtr →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64) s
        (A.pool ∗ stackAt s.sp allocHookStack ∗
          vecGhostAt A locIk (coroPtr + 0xf8#64) ∗
          ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
          ((s.sp + 0x7c#64) ↦₃₂ u_7c) ∗
          ((s.sp + 0xd0#64) ↦₆₄ u_d0))
        (fun s1 P_f =>
          ∃ newLocIdPtr : BitVec 64,
            (P_f ⊢
              A.pool ∗ stackAt s.sp allocHookStack ∗
              vecGhostAt A locIk (coroPtr + 0xf8#64) ∗
              vecU8Buf A (BitVec.ofNat 64 locIk.bytes.length) newLocIdPtr locIk.bytes ∗
              ((coroPtr + 0x240#64) ↦₃₂ sessionVer) ∗
              ((s.sp + 0x7c#64) ↦₃₂ sessionVer) ∗
              ((s.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 locIk.bytes.length)) ∧
            s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
            s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x23 = newLocIdPtr ∧
            s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s)
        (P3P4.PanicOomProp s0) :=
  seg_locId_4k_ok img ext (AllocContractsMem4K.of_AllocContracts hA)

/- Clone `remote_identity_public` (`+0x18e0 → +0x191c`, `[]` or non-empty, OOM `+0x3768`). -/
set_option maxHeartbeats 400000 in
theorem seg_remId_4k_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K img.base A ext)
    (s0 s : State) (coroPtr : BitVec 64) (remIk : VecGhost)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64) s
      (A.pool ∗ stackAt s.sp allocHookStack ∗
        vecGhostAt A remIk (coroPtr + 0x110#64))
      (fun s1 P_f =>
        ∃ newRemIdPtr : BitVec 64,
          (P_f ⊢
            A.pool ∗ stackAt s.sp allocHookStack ∗
            vecGhostAt A remIk (coroPtr + 0x110#64) ∗
            vecU8Buf A (BitVec.ofNat 64 remIk.bytes.length) newRemIdPtr remIk.bytes) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.sp + 0x930#64 ∧
          s1.readReg64 .x23 = s.readReg64 .x23 ∧
          s1.readReg64 .x24 = BitVec.ofNat 64 remIk.bytes.length ∧
          s1.readReg64 .x25 = newRemIdPtr ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have h118 : coroPtr + 0x110#64 + 8#64 = coroPtr + 0x118#64 := by bv_arith
  have h120 : coroPtr + 0x110#64 + 16#64 = coroPtr + 0x120#64 := by bv_arith
  rcases eq_nil_or_length_pos remIk.bytes with hnil | hpos
  · rw [vecGhostAt_eq_of_nil A remIk (coroPtr + 0x110#64) hnil, h118, h120]
    simp only [sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hcap_lt, hptr⟩ => ?_
    refine P3P4.SepWPp.ret_sepWP_frame hF hsym
      (seg2_nil_wp img.base ext s coroPtr hpc hrun hsp_align hx19)
      (by sep_focus)
      fun s1 _ _ hF1 hsym1
        ⟨hsp1, htr1, hx19_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1, hvregs1⟩ => ?_
    refine ⟨1#64, ?_, hsp1, htr1.trans htr, hF1, hsym1,
      hx19_1, hx22_1, hx23_1, by simpa [hnil] using hx24_1, hx25_1, hx27_1, hx29_1, hvregs1⟩
    simp only [hnil, List.length_nil, BitVec.ofNat_eq_ofNat, vecU8Buf_nil_eq A,
      sepConj_emp, emp_sepConj, sepConj_assoc]
    exact entails_pure_3rd ⟨hcap_lt, hptr⟩ (Entails.of_eq (by ac_rfl))
  · rw [vecGhostAt_eq_of_pos A remIk (coroPtr + 0x110#64) hpos, h118, h120]
    simp only [sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hlen_lt63 : remIk.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hlen_le hcap_lt
    have hlen_lt64 : remIk.bytes.length < 2 ^ 64 := by omega
    have hlen_nz : BitVec.ofNat 64 remIk.bytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpos hlen_lt64
    refine P3P4.SepWPp.bind_sepWP_frame hF hsym
      (seg2a_4k_wp img.base ext hA s coroPtr remIk.ptr (BitVec.ofNat 64 remIk.bytes.length)
        hlen_nz hpc hrun hsp_align hx19)
      (by sep_focus)
      fun s1 hpc1 hrun1 hF1 hsym1
        ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1, hx29_1,
          hvregs1⟩ => ?_
    have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    refine P3P4.SepWPp.bind_sepWPp_frame_dep
      (alloc_18fc_4k_ok img img.base ext hA s0 s1 remIk.bytes.length emp hpos hlen_lt63
        hF1 hsym1 hpc1 hrun1 hsp1_al (htr1.trans htr) hx0_1 hx1_1)
      (by rw [hsp1]; sep_focus)
      fun s2 hpc2 hrun2 ⟨hnew_nz, hsp2, htr2, hcs2, hF2, hsym2⟩ => ?_
    set newRemIdPtr := s2.readReg64 .x0
    have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
    have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
    have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
    have hx21_2 : s2.readReg64 .x21 = remIk.ptr := hcs2.2.2.1.trans hx21_1
    have hx22_2 : s2.readReg64 .x22 = s.sp + 0x930#64 := hcs2.2.2.2.1.trans hx22_1
    have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hcs2.2.2.2.2.1.trans hx23_1
    have hx24_2 : s2.readReg64 .x24 = BitVec.ofNat 64 remIk.bytes.length :=
      hcs2.2.2.2.2.2.1.trans hx24_1
    have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
    have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
    refine P3P4.SepWPp.ret_sepWP_frame hF2 hsym2
      (seg2b_4k_wp img.base ext hA s2 coroPtr remIk.ptr newRemIdPtr remIk.bytes
        hnew_nz hlen_lt64 hpc2 hrun2 hsp2_al rfl hx19_2 hx21_2 hx24_2)
      (by simp only [hsp1, hsp2']; sep_focus)
      fun s3 _ _ hF3 hsym3
        ⟨hsp3, htr3, hx19_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx29_3, hvregs3⟩ => ?_
    refine ⟨newRemIdPtr, ?_, hsp3.trans hsp2', by rw [htr3, htr2, htr1, htr], hF3, hsym3,
      hx19_3, hx22_3.trans hx22_2, hx23_3.trans hx23_2, hx24_3, hx25_3,
      hx27_3.trans hx27_2, hx29_3.trans hx29_2, hvregs3.trans hvregs2⟩
    rw [vecU8Buf_pos_eq A newRemIdPtr remIk.bytes hpos hlen_lt63 hnew_nz]
    simp only [sepConj_assoc, hsp1, hsp2']
    exact entails_pure_3rd ⟨hlen_le, hcap_lt, hptr⟩ (Entails.of_eq (by ac_rfl))

theorem seg_remId_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) (hA : AllocContracts img.base A ext) :
    ∀ (s0 s : State) (coroPtr : BitVec 64) (remIk : VecGhost),
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18e0#64 →
      s.status = .Running → (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace → s.readReg64 .x19 = coroPtr →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64) s
        (A.pool ∗ stackAt s.sp allocHookStack ∗
          vecGhostAt A remIk (coroPtr + 0x110#64))
        (fun s1 P_f =>
          ∃ newRemIdPtr : BitVec 64,
            (P_f ⊢
              A.pool ∗ stackAt s.sp allocHookStack ∗
              vecGhostAt A remIk (coroPtr + 0x110#64) ∗
              vecU8Buf A (BitVec.ofNat 64 remIk.bytes.length) newRemIdPtr remIk.bytes) ∧
            s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
            s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.sp + 0x930#64 ∧
            s1.readReg64 .x23 = s.readReg64 .x23 ∧
            s1.readReg64 .x24 = BitVec.ofNat 64 remIk.bytes.length ∧
            s1.readReg64 .x25 = newRemIdPtr ∧
            s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s)
        (P3P4.PanicOomProp s0) :=
  seg_remId_4k_ok img ext (AllocContractsMem4K.of_AllocContracts hA)

/- Clone `root_key` (`+0x191c → +0x195c`, `32` bytes, OOM `+0x375c`). -/
set_option maxHeartbeats 400000 in
theorem seg_rootKey_4k_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K img.base A ext)
    (s0 s : State) (coroPtr rootCap rootPtr u_50 u_98 : BitVec 64)
    (rootKey : RootKey)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64) s
      (A.pool ∗ stackAt s.sp allocHookStack ∗
        vecU8At A (coroPtr + 0x128#64) rootCap rootPtr (keyToBytes32 rootKey) ∗
        ((s.sp + 0x50#64) ↦₆₄ u_50) ∗
        ((s.sp + 0x98#64) ↦₆₄ u_98))
      (fun s1 P_f =>
        ∃ newRootKeyPtr : BitVec 64,
          (P_f ⊢
            A.pool ∗ stackAt s.sp allocHookStack ∗
            vecU8At A (coroPtr + 0x128#64) rootCap rootPtr (keyToBytes32 rootKey) ∗
            vecU8Buf A 32#64 newRootKeyPtr (keyToBytes32 rootKey) ∗
            ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
            ((s.sp + 0x98#64) ↦₆₄ 32#64)) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
          s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have h130 : coroPtr + 0x128#64 + 8#64 = coroPtr + 0x130#64 := by bv_arith
  have h138 : coroPtr + 0x128#64 + 16#64 = coroPtr + 0x138#64 := by bv_arith
  have hlen : (keyToBytes32 rootKey).length = 32 := by simp [keyToBytes32]
  have hpos : 0 < (keyToBytes32 rootKey).length := by omega
  have hlt63 : (keyToBytes32 rootKey).length < 2 ^ 63 := by omega
  have hlt64 : (keyToBytes32 rootKey).length < 2 ^ 64 := by omega
  have hbv32 : BitVec.ofNat 64 (keyToBytes32 rootKey).length = 32#64 := by rw [hlen]
  rw [vecU8At_eq_of_pos A (coroPtr + 0x128#64) rootCap rootPtr (keyToBytes32 rootKey) hpos,
      h130, h138, hbv32]
  simp only [sepConj_assoc]
  refine sepWPp_pure_3rd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym
    (seg3a_4k_wp img.base ext hA s coroPtr rootPtr 32#64 u_98 (by decide) hpc hrun hsp_align hx19)
    (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1
      ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
        hx27_1, hx29_1, hvregs1⟩ => ?_
  have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine P3P4.SepWPp.bind_sepWPp_frame_dep
    (alloc_1938_4k_ok img img.base ext hA s0 s1 32 emp (by decide) (by decide)
      hF1 hsym1 hpc1 hrun1 hsp1_al (htr1.trans htr) hx0_1 hx1_1)
    (by rw [hsp1]; sep_focus)
    fun s2 hpc2 hrun2 ⟨hnew_nz, hsp2, htr2, hcs2, hF2, hsym2⟩ => ?_
  set newRootKeyPtr := s2.readReg64 .x0
  have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
  have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = rootPtr := hcs2.2.2.1.trans hx21_1
  have hx22_2 : s2.readReg64 .x22 = s.readReg64 .x22 := hcs2.2.2.2.1.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hcs2.2.2.2.2.1.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = s.readReg64 .x24 := hcs2.2.2.2.2.2.1.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hcs2.2.2.2.2.2.2.1.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = BitVec.ofNat 64 (keyToBytes32 rootKey).length := by
    rw [hbv32]; exact hcs2.2.2.2.2.2.2.2.1.trans hx26_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2.2.2.2.2.2.2.2.2.1.trans hx27_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
  have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
    hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
  refine P3P4.SepWPp.ret_sepWP_frame hF2 hsym2
    (seg3b_4k_wp img.base ext hA s2 coroPtr rootPtr newRootKeyPtr u_50 (keyToBytes32 rootKey)
      hnew_nz hlt64 hpc2 hrun2 hsp2_al rfl hx19_2 hx21_2 hx26_2)
    (by simp only [hsp1, hsp2', hlen]; sep_focus)
    fun s3 _ _ hF3 hsym3
      ⟨hsp3, htr3, hx19_3, hx22_3, hx23_3, hx24_3, hx25_3, hx27_3, hx29_3, hvregs3⟩ => ?_
  have hbuf32 :
      vecU8Buf A 32#64 newRootKeyPtr (keyToBytes32 rootKey) =
        A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ keyToBytes32 rootKey) := by
    have h := vecU8Buf_pos_eq A newRootKeyPtr (keyToBytes32 rootKey) hpos hlt63 hnew_nz
    rwa [hlen] at h
  refine ⟨newRootKeyPtr, ?_, hsp3.trans hsp2', by rw [htr3, htr2, htr1, htr], hF3, hsym3,
    hx19_3, hx22_3.trans hx22_2, hx23_3.trans hx23_2, hx24_3.trans hx24_2,
    hx25_3.trans hx25_2, hx27_3.trans hx27_2, hx29_3.trans hx29_2, hvregs3.trans hvregs2⟩
  rw [hbuf32]
  simp only [sepConj_assoc, hsp1, hsp2']
  exact entails_pure_3rd ⟨hlen_le, hcap_lt, hptr⟩ (Entails.of_eq (by ac_rfl))

theorem seg_rootKey_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) (hA : AllocContracts img.base A ext) :
    ∀ (s0 s : State) (coroPtr rootCap rootPtr u_50 u_98 : BitVec 64)
      (rootKey : RootKey),
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x191c#64 →
      s.status = .Running → (s.sp &&& 15#64 == 0#64) = true →
      s.trace = s0.trace → s.readReg64 .x19 = coroPtr →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64) s
        (A.pool ∗ stackAt s.sp allocHookStack ∗
          vecU8At A (coroPtr + 0x128#64) rootCap rootPtr (keyToBytes32 rootKey) ∗
          ((s.sp + 0x50#64) ↦₆₄ u_50) ∗
          ((s.sp + 0x98#64) ↦₆₄ u_98))
        (fun s1 P_f =>
          ∃ newRootKeyPtr : BitVec 64,
            (P_f ⊢
              A.pool ∗ stackAt s.sp allocHookStack ∗
              vecU8At A (coroPtr + 0x128#64) rootCap rootPtr (keyToBytes32 rootKey) ∗
              vecU8Buf A 32#64 newRootKeyPtr (keyToBytes32 rootKey) ∗
              ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
              ((s.sp + 0x98#64) ↦₆₄ 32#64)) ∧
            s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
            s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
            s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
            s1.readReg64 .x25 = s.readReg64 .x25 ∧
            s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s)
        (P3P4.PanicOomProp s0) :=
  seg_rootKey_4k_ok img ext (AllocContractsMem4K.of_AllocContracts hA)

/- Clone `sender_chain` (`+0x195c → +0x19b0`, `None` inline at `+0x19ac` or `Some` via `hscc`). -/
set_option maxHeartbeats 400000 in
theorem seg_senderChain_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (hscc : SenderChainClone3OkExt img.base A ext)
    (s0 s : State) (coroPtr u_48
      u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (prevCounter u_5c : BitVec 32)
    (scG : Option SenderChainGhost) (scM : Option SenderChain)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x195c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = s.sp + 0x930#64)
    (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x19b0#64) s
      (A.pool ∗ stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
        optSenderChainAt A (coroPtr + 0x188#64) scG scM ∗
        ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
        ((s.sp + 0x48#64) ↦₆₄ u_48) ∗
        ((s.sp + 0x5c#64) ↦₃₂ u_5c) ∗
        ((s.sp + 0x930#64) ↦₆₄ u930) ∗ ((s.sp + 0x938#64) ↦₆₄ u938) ∗
        ((s.sp + 0x940#64) ↦₆₄ u940) ∗ ((s.sp + 0x948#64) ↦₆₄ u948) ∗
        ((s.sp + 0x950#64) ↦₆₄ u950) ∗ ((s.sp + 0x958#64) ↦₆₄ u958) ∗
        ((s.sp + 0x960#64) ↦₆₄ u960) ∗ ((s.sp + 0x968#64) ↦₆₄ u968) ∗
        ((s.sp + 0x970#64) ↦₆₄ u970) ∗ ((s.sp + 0x978#64) ↦₆₄ u978) ∗
        ((s.sp + 0x980#64) ↦₆₄ u980) ∗ ((s.sp + 0x988#64) ↦₆₄ u988))
      (fun s1 P_f =>
        ∃ (sender' : Option SenderChainGhost) (c0 : BitVec 64)
          (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
          OptSenderChainCloneRel scG scM sender' ∧
          OptSenderChainInline sender' scM (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) ∧
          (P_f ⊢
            A.pool ∗ stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
            optSenderChainAt A (coroPtr + 0x188#64) scG scM ∗
            optSenderChainHeap A sender' scM ∗
            ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
            ((s.sp + 0x48#64) ↦₆₄ c0) ∗
            ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗
            genP3SenderInlineWords s.sp sq0 sq1 sq2 sq3 sq4 sq5) ∧
          s1.sp = s.sp ∧ s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
          s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x23 = s.readReg64 .x23 ∧
          s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x27 = s.sp + 0x370#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  cases scG with
  | none =>
    cases scM with
    | none =>
      dsimp only [optSenderChainAt]
      refine P3P4.SepWPp.ret_sepWP_frame hF hsym
        (seg4_none_wp img.base ext s coroPtr u_48 prevCounter u_5c hpc hrun hsp_align hx19)
        (by sep_focus)
        fun s1 _ _ hF1 hsym1
          ⟨hsp1, htr1, hx19_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1, hvregs1⟩ => ?_
      let sq0 : BitVec 128 := u938 ++ u930
      let sq1 : BitVec 128 := u948 ++ u940
      let sq2 : BitVec 128 := u958 ++ u950
      let sq3 : BitVec 128 := u968 ++ u960
      let sq4 : BitVec 128 := u978 ++ u970
      let sq5 : BitVec 128 := u988 ++ u980
      refine ⟨none, noneCap, sq0, sq1, sq2, sq3, sq4, sq5, trivial,
        OptSenderChainInline.none_of_chunks96 sq0 sq1 sq2 sq3 sq4 sq5, ?_,
        hsp1, htr1.trans htr, hF1, hsym1,
        hx19_1, hx23_1, hx24_1, hx25_1, hx27_1.trans hx27, hx29_1, hvregs1⟩
      dsimp only [optSenderChainAt, optSenderChainHeap, genP3SenderInlineWords,
        sq0, sq1, sq2, sq3, sq4, sq5]
      simp only [cat128_lo, cat128_hi, emp_sepConj, sepConj_emp, sepConj_assoc]
      exact Entails.of_eq (by ac_rfl)
    | some _ =>
      dsimp only [optSenderChainAt]
      exact sepWPp_pure_4th False.elim
  | some sg =>
    cases scM with
    | none =>
      dsimp only [optSenderChainAt]
      exact sepWPp_pure_4th False.elim
    | some sc =>
      refine SepWPp.weaken_pre
        (Entails.of_eq (by rw [optSenderChainAt_some_eq_cap A (coroPtr + 0x188#64) sg sc])) ?_
      simp only [sepConj_assoc]
      refine sepWPp_pure_4th fun ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ => ?_
      have hsc_ne : sg.srk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hsrk_cap_lt
      refine P3P4.SepWPp.bind_sepWP_frame hF hsym
        (seg4a1_wp img.base ext s coroPtr sg.srk.cap prevCounter u_5c hsc_ne hpc hrun hsp_align hx19)
        (by sep_focus)
        fun s1 hpc1 hrun1 hF1 hsym1
          ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1,
            hx30_1, hvregs1⟩ => ?_
      have hsp1_al : s1.spAligned = true := by
        change (s1.sp &&& 15#64 == 0#64) = true
        rw [hsp1]; exact hsp_align
      have hopt_reasm :
          (((coroPtr + 0x188#64) ↦₆₄ sg.srk.cap) ∗
            optSenderChainSomeRest A (coroPtr + 0x188#64) sg sc) ⊢
          optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) := by
        rw [optSenderChainAt_some_eq_cap A (coroPtr + 0x188#64) sg sc]
        exact Entails.pure_right ⟨hsrk_le, hsrk_cap_lt, hsrk_ptr⟩ (Entails.refl _)
      refine P3P4.SepWPp.weaken_frame hopt_reasm (by sep_focus) ?_
      refine P3P4.SepWPp.call_frame_frozen_oom
        (spec := senderChainCloneSpec A)
        (x := ⟨s.sp + 0x3e0#64, coroPtr + 0x188#64, sg, sc⟩)
        (φ := s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x1 = coroPtr + 0x188#64)
        (T := memRegion (s.sp + 0x3e0#64) 104 ∗
          optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
          A.pool ∗ stackAt s1.sp chainCloneStack)
        hF1 hsym1 (htr1.trans htr) hscc hpc1 hrun1 hsp1_al hx30_1
        rfl ⟨hx0_1, hx1_1⟩ (by rw [hsp1]; sep_focus)
        (hnext := fun s2 hpc2 hrun2 hsp2 _ hcs2 hF2 hsym2 => ?_)
      dsimp only [senderChainCloneSpec]
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun htr2 => ?_
      rw [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun sg' => ?_
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hsrk', hpriv'⟩ => ?_
      have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
      have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
      have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2.1.trans hx19_1
      have hx22_2 : s2.readReg64 .x22 = s2.sp + 0x930#64 := by
        rw [hcs2.2.2.2.1, hx22_1, hx22, hsp2']
      have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hcs2.2.2.2.2.1.trans hx23_1
      have hx24_2 : s2.readReg64 .x24 = s.readReg64 .x24 := hcs2.2.2.2.2.2.1.trans hx24_1
      have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hcs2.2.2.2.2.2.2.1.trans hx25_1
      have hx27_2 : s2.readReg64 .x27 = s2.sp + 0x370#64 := by
        rw [hcs2.2.2.2.2.2.2.2.2.1, hx27_1, hx27, hsp2']
      have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 :=
        hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
      have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
        hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      refine SepWPp.weaken_pre
        (sepConj_mono_left
          (optSenderChainAt_entails_chunks104W6Q A (s.sp + 0x3e0#64) (some sg') (some sc))) ?_
      simp only [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun c0 =>
        SepWPp.exists_elim fun sq0 => SepWPp.exists_elim fun sq1 =>
        SepWPp.exists_elim fun sq2 => SepWPp.exists_elim fun sq3 =>
        SepWPp.exists_elim fun sq4 => SepWPp.exists_elim fun sq5 => ?_
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun hsc_inl => ?_
      rw [chunks104W6QAt_sp_0x3e0 s.sp c0 sq0 sq1 sq2 sq3 sq4 sq5]
      refine P3P4.SepWPp.ret_sepWP_frame hF2 hsym2
        (seg4a2_wp img.base ext s2 coroPtr u_48
          c0 (sq0.extractLsb' 0 64) (sq0.extractLsb' 64 64)
          (sq1.extractLsb' 0 64) (sq1.extractLsb' 64 64)
          (sq2.extractLsb' 0 64) (sq2.extractLsb' 64 64)
          (sq3.extractLsb' 0 64) (sq3.extractLsb' 64 64)
          (sq4.extractLsb' 0 64) (sq4.extractLsb' 64 64)
          (sq5.extractLsb' 0 64) (sq5.extractLsb' 64 64)
          u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
          hpc2 hrun2 hsp2_al hx19_2 hx22_2 hx27_2)
        (by simp only [hsp1, hsp2']; sep_focus)
        fun s3 _ _ hF3 hsym3 ⟨hsp3, htr3, hx19_3, hx23_3, hx24_3, hx25_3, hx27_3, hx29_3, hvregs3⟩ => ?_
      refine ⟨some sg', c0, sq0, sq1, sq2, sq3, sq4, sq5,
        ⟨hsrk', hpriv'⟩, hsc_inl, ?_,
        hsp3.trans hsp2', by rw [htr3, htr2, htr1, htr], hF3, hsym3,
        hx19_3, hx23_3.trans hx23_2, hx24_3.trans hx24_2, hx25_3.trans hx25_2,
        by rw [hx27_3, hsp2'], hx29_3.trans hx29_2, hvregs3.trans hvregs2⟩
      have h104 : ∀ R_tail : SepProp,
          ((s.sp + 0x3e0#64) ↦₆₄ c0) ∗
            ((s.sp + 0x3e8#64) ↦₆₄ sq0.extractLsb' 0 64) ∗
            ((s.sp + 0x3f0#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
            ((s.sp + 0x3f8#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
            ((s.sp + 0x400#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
            ((s.sp + 0x408#64) ↦₆₄ sq2.extractLsb' 0 64) ∗
            ((s.sp + 0x410#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
            ((s.sp + 0x418#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
            ((s.sp + 0x420#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
            ((s.sp + 0x428#64) ↦₆₄ sq4.extractLsb' 0 64) ∗
            ((s.sp + 0x430#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
            ((s.sp + 0x438#64) ↦₆₄ sq5.extractLsb' 0 64) ∗
            ((s.sp + 0x440#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ R_tail ⊢
          memRegion (s.sp + 0x3e0#64) 104 ∗ R_tail := by
        intro R_tail
        have h104_eq := congrArg (· ∗ R_tail)
          (chunks104W6QAt_sp_0x3e0 s.sp c0 sq0 sq1 sq2 sq3 sq4 sq5)
        simp only [sepConj_assoc] at h104_eq
        rw [← h104_eq]
        exact sepConj_mono_left (chunks104W6QAt_entails_memRegion _ _ _ _ _ _ _ _)
      let R_tail : SepProp :=
        A.pool ∗ stackAt s.sp chainCloneStack ∗
          optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
          optSenderChainHeap A (some sg') (some sc) ∗
          ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
          ((s.sp + 0x48#64) ↦₆₄ c0) ∗
          ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗
          genP3SenderInlineWords s.sp sq0 sq1 sq2 sq3 sq4 sq5
      dsimp only [genP3SenderInlineWords] at *
      simp only [hsp1, hsp2', sepConj_assoc]
      exact Entails.trans
        (Entails.of_eq (by dsimp only [R_tail, genP3SenderInlineWords]; ac_rfl))
        (Entails.trans (h104 R_tail)
          (Entails.of_eq (by dsimp only [R_tail, genP3SenderInlineWords]; ac_rfl)))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1

/-! ## 2. Public Top-Level Segment 1 Theorem (`CloneKeysFrontStmt`) -/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

set_option maxRecDepth 200000

private theorem sepWPp_done {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hQ : Q s P) :
    SepWPp prog ret s P Q Qp :=
  fun _ hm _ => ⟨s, Steps.refl s, Or.inl ⟨hpc, hrun, P, hm, hQ⟩⟩

private theorem sepWPp_weaken_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (himp : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hQ⟩ | hpan | hexit⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, himp sf Pf hQ⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hexit)⟩

/-- `calleeSavedVRegs`-strengthened `CloneKeysFrontStmt4K`. -/
def CloneKeysFrontVRegsStmt4K : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContractsMem4K img.base A ext) →
    (hscc : SenderChainClone3OkExt img.base A ext) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      st.receiverChains.length < 2 ^ 32 →
      (sp &&& 15#64 == 0#64) = true →
      rootStack ≤ sp.toNat →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (closureEntry img ext + 0x19b0#64) s
        (genP3Pre A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3J1 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
        (P3P4.PanicOomProp s0)

/-- `calleeSavedVRegs`-strengthened `CloneKeysFrontStmt`. -/
def CloneKeysFrontVRegsStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContracts img.base A ext) →
    (hscc : SenderChainClone3OkExt img.base A ext) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      st.receiverChains.length < 2 ^ 32 →
      (sp &&& 15#64 == 0#64) = true →
      rootStack ≤ sp.toNat →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (closureEntry img ext + 0x19b0#64) s
        (genP3Pre A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3J1 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
        (P3P4.PanicOomProp s0)

set_option maxHeartbeats 800000 in
theorem cloneKeysFront_vregs_4k_ok : CloneKeysFrontVRegsStmt4K := by
  intro A img ext hA hscc _ s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
    msgVer rest recG st rem loc msgG msg _ hsp_align _ hF hsym hpc hrun htr
  dsimp only [genP3Pre, genP3SpillAll]
  refine SepWPp.pure_elim fun ⟨hsp, hx19, hx27, hx29⟩ => ?_
  subst hsp
  rw [M3a1.sessionStateAt_front_eq A coroPtr recG st]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hss_pure => ?_
  have hloc_pos : 0 < recG.localIk.bytes.length := by
    have hloc33 : recG.localIk.bytes.length = 33 := hss_pure.2.2.2.2.2.1
    omega
  let F_rest : SepProp :=
    M3a1.frontSessionRestAt A coroPtr recG st ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFrame A img s.sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc
        msgG msg ∗
      genP3PendSpillScratch s.sp ∗
      genP3TailSpillScratch s.sp ∗
      genP3ChainsSpillScratch s.sp
  refine SepWPp.weaken_pre
    (P' := (∃∗ wf : GenP3FrontSpill,
      ((s.sp + 0x48#64) ↦₆₄ wf.u_48) ∗ ((s.sp + 0x50#64) ↦₆₄ wf.u_50) ∗
      ((s.sp + 0x5c#64) ↦₃₂ wf.u_5c) ∗ ((s.sp + 0x7c#64) ↦₃₂ wf.u_7c) ∗
      ((s.sp + 0x98#64) ↦₆₄ wf.u_98) ∗ ((s.sp + 0xd0#64) ↦₆₄ wf.u_d0) ∗
      ((s.sp + 0x930#64) ↦₆₄ wf.u930) ∗ ((s.sp + 0x938#64) ↦₆₄ wf.u938) ∗
      ((s.sp + 0x940#64) ↦₆₄ wf.u940) ∗ ((s.sp + 0x948#64) ↦₆₄ wf.u948) ∗
      ((s.sp + 0x950#64) ↦₆₄ wf.u950) ∗ ((s.sp + 0x958#64) ↦₆₄ wf.u958) ∗
      ((s.sp + 0x960#64) ↦₆₄ wf.u960) ∗ ((s.sp + 0x968#64) ↦₆₄ wf.u968) ∗
      ((s.sp + 0x970#64) ↦₆₄ wf.u970) ∗ ((s.sp + 0x978#64) ↦₆₄ wf.u978) ∗
      ((s.sp + 0x980#64) ↦₆₄ wf.u980) ∗ ((s.sp + 0x988#64) ↦₆₄ wf.u988)) ∗
      (vecGhostAt A recG.localIk (coroPtr + 0xf8#64) ∗
        vecGhostAt A recG.remoteIk (coroPtr + 0x110#64) ∗
        vecU8At A (coroPtr + 0x128#64) recG.root.cap recG.root.ptr (keyToBytes32 st.rootKey) ∗
        optSenderChainAt A (coroPtr + 0x188#64) recG.sender st.senderChain ∗
        ((coroPtr + 0x240#64) ↦₃₂ st.sessionVersion) ∗
        ((coroPtr + 0x244#64) ↦₃₂ st.previousCounter) ∗
        A.pool ∗ stackAt s.sp chainCloneStack ∗ memRegion (s.sp + 0x3e0#64) 104 ∗ F_rest))
    (by dsimp only [F_rest]; exact Entails.of_eq (by ac_rfl)) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun wf => ?_
  rw [stackAt_chainClone_eq_alloc s.sp]
  simp only [sepConj_assoc]
  refine SepWPp.bind_oom_frame
    (M3a1.seg_locId_4k_ok img ext hA s0 s coroPtr wf.u_d0 st.sessionVersion wf.u_7c recG.localIk
      hloc_pos hF hsym hpc hrun hsp_align htr hx19)
    (by sep_focus)
    fun s1 _ hpc1 hrun1
      ⟨newLocIdPtr, hent1, hsp1, htr1, hF1, hsym1, hx19_1, hx23_1, hx27_1, hx29_1, hvregs1⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent1) ?_
  simp only [sepConj_assoc]
  have hsp1_al : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  refine SepWPp.bind_oom_frame
    (M3a1.seg_remId_4k_ok img ext hA s0 s1 coroPtr recG.remoteIk
      hF1 hsym1 hpc1 hrun1 hsp1_al htr1 hx19_1)
    (by simp only [hsp1]; sep_focus)
    fun s2 _ hpc2 hrun2
      ⟨newRemIdPtr, hent2, hsp2, htr2, hF2, hsym2, hx19_2, hx22_2, hx23_2, hx24_2, hx25_2,
        hx27_2, hx29_2, hvregs2⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent2) ?_
  simp only [sepConj_assoc]
  have hsp2' : s2.sp = s.sp := hsp2.trans hsp1
  have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2']; exact hsp_align
  refine SepWPp.bind_oom_frame
    (M3a1.seg_rootKey_4k_ok img ext hA s0 s2 coroPtr recG.root.cap recG.root.ptr wf.u_50 wf.u_98
      st.rootKey hF2 hsym2 hpc2 hrun2 hsp2_al htr2 hx19_2)
    (by simp only [hsp1, hsp2']; sep_focus)
    fun s3 _ hpc3 hrun3
      ⟨newRootKeyPtr, hent3, hsp3, htr3, hF3, hsym3, hx19_3, hx22_3, hx23_3, hx24_3, hx25_3,
        hx27_3, hx29_3, hvregs3⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent3) ?_
  simp only [sepConj_assoc]
  have hsp3' : s3.sp = s.sp := hsp3.trans hsp2'
  have hsp3_al : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3']; exact hsp_align
  have hx22_3' : s3.readReg64 .x22 = s3.sp + 0x930#64 := by
    rw [hx22_3, hx22_2, hsp1, hsp3']
  have hx27_3' : s3.readReg64 .x27 = s3.sp + 0x370#64 := by
    rw [hx27_3, hx27_2, hx27_1, hx27, hsp3']
  have hstack_fold :
      (memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ stackAt s2.sp allocHookStack) ⊢
        stackAt s.sp chainCloneStack := by
    rw [hsp2', ← stackAt_chainClone_eq_alloc s.sp]
    exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_fold (by sep_focus) ?_
  refine SepWPp.bind_oom_frame
    (M3a1.seg_senderChain_ok img ext hscc s0 s3 coroPtr wf.u_48
      wf.u930 wf.u938 wf.u940 wf.u948 wf.u950 wf.u958
      wf.u960 wf.u968 wf.u970 wf.u978 wf.u980 wf.u988
      st.previousCounter wf.u_5c recG.sender st.senderChain
      hF3 hsym3 hpc3 hrun3 hsp3_al htr3 hx19_3 hx22_3' hx27_3')
    (by simp only [hsp3']; sep_focus)
    fun s4 _ hpc4 hrun4
      ⟨sender', c0, sq0, sq1, sq2, sq3, sq4, sq5, hsc_rel, hsc_inl, hent4,
        hsp4, htr4, hF4, hsym4, hx19_4, hx23_4, hx24_4, hx25_4, hx27_4, hx29_4, hvregs4⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent4) ?_
  refine sepWPp_done hpc4 hrun4
    ⟨?_, htr4, hF4, hsym4, hvregs4.trans (hvregs3.trans (hvregs2.trans hvregs1))⟩
  dsimp only [genP3J1, F_rest]
  refine Entails.sepExists_right
    { newLocIdPtr := newLocIdPtr
      newRemIdPtr := newRemIdPtr
      newRootKeyPtr := newRootKeyPtr
      c0 := c0
      sender' := sender'
      sq0 := sq0, sq1 := sq1, sq2 := sq2, sq3 := sq3, sq4 := sq4, sq5 := sq5 } ?_
  refine Entails.pure_right
    ⟨hsp4.trans hsp3', hx19_4,
     hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_1)),
     hx24_4.trans (hx24_3.trans hx24_2),
     hx25_4.trans (hx25_3.trans hx25_2),
     by rw [hx27_4, hsp3'],
     hx29_4.trans (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29))),
     hsc_rel, hsc_inl⟩ ?_
  rw [M3a1.sessionStateAt_front_eq A coroPtr recG st]
  simp only [hsp3', sepConj_assoc]
  exact Entails.pure_right hss_pure (Entails.of_eq (by ac_rfl))

/-- Segment 1 (`+0x1778 → +0x19b0`, `genP3Pre → genP3J1`, 4K stack). -/
theorem cloneKeysFront_4k_ok : CloneKeysFrontStmt4K := by
  intro A img ext hA hscc himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
    msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF hsym hpc hrun htr
  exact sepWPp_weaken_post
    (cloneKeysFront_vregs_4k_ok img ext hA hscc himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF hsym hpc
      hrun htr)
    fun _ _ ⟨h1, h2, h3, h4, _⟩ => ⟨h1, h2, h3, h4⟩

theorem cloneKeysFront_vregs_ok : CloneKeysFrontVRegsStmt :=
  fun img ext hA => cloneKeysFront_vregs_4k_ok img ext (AllocContractsMem4K.of_AllocContracts hA)

/-- Segment 1 (`+0x1778 → +0x19b0`, `genP3Pre → genP3J1`). -/
theorem cloneKeysFront_ok : CloneKeysFrontStmt :=
  fun img ext hA => cloneKeysFront_4k_ok img ext (AllocContractsMem4K.of_AllocContracts hA)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

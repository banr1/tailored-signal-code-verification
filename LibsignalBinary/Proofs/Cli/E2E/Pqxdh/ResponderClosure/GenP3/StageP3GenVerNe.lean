/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNeBlocks
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Stage P3 Version-Mismatch Path

Proves `stageP3_ver_ne_ext_ok` (`+0x1e04 → s0.readReg64 .x30` when `st.version ≠ msgVer`) on
`tripleRatchetProgAtExt b ext`, logging the version mismatch, recording the decryption-failed
`SignalProtocolError`, dropping both `SessionStructure` slots, and returning to
`s0.readReg64 .x30`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

/-! ## 1. Spatial Fold Helpers for `stageP3_ver_ne_ext_ok` -/

theorem sp3e0_48_ver_fold (sp w0 w2 w3 w4 w5 : BitVec 64) (lo1 hi1 : BitVec 32) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗
    ((sp + 0x3e8#64) ↦₃₂ lo1) ∗
    ((sp + 0x3ec#64) ↦₃₂ hi1) ∗
    ((sp + 0x3f0#64) ↦₆₄ w2) ∗
    ((sp + 0x3f8#64) ↦₆₄ w3) ∗
    ((sp + 0x400#64) ↦₆₄ w4) ∗
    ((sp + 0x408#64) ↦₆₄ w5) ⊢
    memRegion (sp + 0x3e0#64) 48 := by
  have hp : ((sp + 0x3e8#64) ↦₃₂ lo1) ∗ ((sp + 0x3ec#64) ↦₃₂ hi1) =
      ((sp + 0x3e8#64) ↦₆₄ (hi1 ++ lo1)) := pointsTo32_pair_sp3e8 sp lo1 hi1
  refine Entails.trans (entails_replace_sub (Entails.of_eq hp) (by sep_focus) rfl) ?_
  have hw := words6_entails_memRegion48 (sp + 0x3e0#64) w0 (hi1 ++ lo1) w2 w3 w4 w5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hw
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hw

theorem memRegion344_3e0_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 344 =
      memRegion (sp + 0x3e0#64) 48 ∗ memRegion (sp + 0x410#64) 296 :=
  ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 48) (k := 296)
    (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)
theorem pointsTo64_split_sp3e8 (sp w : BitVec 64) :
    ((sp + 0x3e8#64) ↦₆₄ w) =
      ((sp + 0x3e8#64) ↦₃₂ w.extractLsb' 0 32) ∗
      ((sp + 0x3ec#64) ↦₃₂ w.extractLsb' 32 32) := by
  have h : sp + 0x3ec#64 = (sp + 0x3e8#64) + 4#64 := by bv_omega
  rw [h, pointsTo64_split32]

/-! ## 2. Version-Mismatch Tail (`stageP3_err_ver_tail_ext_ok`, `+0x33b0 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
theorem stageP3_err_ver_tail_ext_4k_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsMem4K img.base A ext)
    (s0 s s7 : State) (coroPtr outPtr errsPtr prevStatesPtr : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hF7 : img.FrozenLoaded s7) (hsym7 : s7.symtab = img.symtab)
    (hpc7 : s7.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x33b0#64)
    (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr7 : s7.trace = s0.trace)
    (hx0_7 : s7.readReg64 .x0 = 17#64)
    (hx1_7 : s7.readReg64 .x1 = 1#64)
    (hx19_7 : s7.readReg64 .x19 = coroPtr)
    (hx24_7 : s7.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_7 : s7.readReg64 .x25 = s.sp + 0x210#64)
    (hx26_7 : s7.readReg64 .x26 = outPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 12#64) 36 ∗
       memRegion (errsPtr + 48#64) 144 ∗
       A.live errsPtr 192 8 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          memRegion (coroPtr + 0xf8#64) 344 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧
        ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s7)
      (PanicOomProp s0) := by
  have hb_align : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hs7_sp]; exact hsp_align
  have hstack_alloc :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have halloc17 := p3_alloc_33b0_ext_4k_ok (A := A) img img.base ext hA s0 s7
    emp hF7 hsym7 hpc7 hrun7 hsp7_align htr7 hx0_7 hx1_7
  rw [sepConj_emp, hs7_sp] at halloc17
  refine SepWPp.bind_sepWPp_frame_raw
    halloc17 (by sep_focus)
    fun s8 P_m8 hpc8 hrun8 ⟨hP8, hdf_ne, hsp8_7, htr8_7, hcs8, hF8, hsym8⟩ => ?_
  rw [sepConj_emp] at hP8
  refine P3P4.SepWPp.weaken_frame hP8 (by sep_focus) ?_
  have hstack_restore8 :
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore8 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion_17_split_eq (s8.readReg64 .x0)))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_df10 => SepWPp.exists_elim fun u_df8 =>
    SepWPp.exists_elim fun u_df0 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x270#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_270 => SepWPp.exists_elim fun u_278 =>
    SepWPp.exists_elim fun u_280 => SepWPp.exists_elim fun u_288 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3))
    (by sep_focus) ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, _, _, hvregs_cs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx24_8 : s8.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs8.trans hx24_7
  have hx25_8 : s8.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs8.trans hx25_7
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans hx26_7
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.intro_rodata_decryptionFailed
    himg hF8 ?_
  have hstep9 := p3_err_ver_e_ext_wp img.base ext s8 coroPtr (s8.readReg64 .x0) errsPtr
    0x6974707972636564#64 0x656c696166206e6f#64
    u_df0 u_df8 u_270 u_278 u_280 u_288 u_df10 (w3.extractLsb' 0 8)
    hb_align hdf_ne hpc8 hrun8 hsp8_align rfl hx19_8
  rw [hsp8_s] at hstep9
  refine P3P4.SepWPp.bind_sepWP_frame hF8 hsym8 hstep9 (by sep_focus)
    fun s9 hpc9 hrun9 hF9 hsym9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx19_9, hx21_9, hx22_9, hx23_9,
    hx24_9, hx25_9, hx26_9, _, hx28_9, _, hx30_9, hvregs_9⟩
  refine SepWPp.drop_frame
    (P_drop := ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s8.readReg64 .x0))) (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hsp9_s : s9.sp = s.sp := hsp9_8
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9_s] using hsp_align
  have hstack_spe :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 480 ∗ stackAt s.sp dropSpeStack :=
    stackAt_split_bottom s.sp dropSpeStack 480 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_spe) (by sep_focus) ?_
  refine call_frame_inImage_nopanic
    (spec := dropSpeVerSpec A)
    (x := (errsPtr, msgVer))
    (φ := s9.readReg64 .x0 = errsPtr)
    (T := (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 12#64) 36 ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hF9 hsym9 (drop_spe2_ver_ok_ext (A := A) (img := img) (ext := ext) himg)
    hpc9 hrun9 hsp9_al hx30_9
    (by dsimp only [dropSpeVerSpec]; rw [hsp9_s])
    hx0_9
    (by sep_focus)
    (hnext := fun s10 hpc10 hrun10 hsp10_9 hsp10_al hcs10 hF10 hsym10 => ?_)
  dsimp only [dropSpeVerSpec]
  rw [hsp9_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr10_9 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs48_144_join errsPtr)) (by sep_focus) ?_
  have hstack_restore10 :
      memRegion (s.sp - 4608#64) 480 ∗ stackAt s.sp dropSpeStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_spe]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore10 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) 17#64 (s8.readReg64 .x0) 17#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp10_s : s10.sp = s.sp := hsp10_9.trans hsp9_s
  have hsp10_align : (s10.sp &&& 15#64 == 0#64) = true := by rw [hsp10_s]; exact hsp_align
  rcases hcs10 with ⟨hx19_cs10, _, hx21_cs10, hx22_cs10, hx23_cs10, hx24_cs10, hx25_cs10,
    hx26_cs10, _, hx28_cs10, _, hvregs_cs10⟩
  have hx19_10 : s10.readReg64 .x19 = coroPtr := hx19_cs10.trans hx19_9
  have hx21_10 : s10.readReg64 .x21 = errsPtr := hx21_cs10.trans hx21_9
  have hx22_10 : s10.readReg64 .x22 = errsPtr := hx22_cs10.trans hx22_9
  have hx23_10 : s10.readReg64 .x23 = 1#64 := hx23_cs10.trans hx23_9
  have hx24_10 : s10.readReg64 .x24 = s10.sp + 0x370#64 := by
    rw [hx24_cs10, hx24_9, hx24_8, hsp10_s]
  have hx25_10 : s10.readReg64 .x25 = s10.sp + 0x210#64 := by
    rw [hx25_cs10, hx25_9, hx25_8, hsp10_s]
  have hx26_10 : s10.readReg64 .x26 = outPtr := hx26_cs10.trans (hx26_9.trans hx26_8)
  have hx28_10 : s10.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs10.trans hx28_9
  have hstep11 := p3_err_ver_f_ext_4k_wp img.base ext hA s10 coroPtr errsPtr recG.localIk.cap
    ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)
    w3' w4 u_250 u_258 u_370 u_378 u_384 u_38c
    ((17#64 : BitVec 64).extractLsb' 0 32) ((17#64 : BitVec 64).extractLsb' 32 32)
    u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc10 hrun10 hsp10_align
    hx19_10 hx21_10 hx22_10 hx23_10 hx24_10 hx25_10 hx28_10
  rw [hsp10_s] at hstep11
  refine P3P4.SepWPp.bind_sepWP_frame hF10 hsym10 hstep11 (by sep_focus)
    fun s11 hpc11 hrun11 hF11 hsym11 hregs11 => ?_
  rcases hregs11 with ⟨hsp11_10, htr11_10, hx0_11, hx19_11, hx22_11, _, hx25_11,
    hx26_11, _, hx28_11, _, hx30_11, hvregs_11⟩
  refine P3P4.SepWPp.weaken_frame hstack_restore8 (by sep_focus) ?_
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢
      sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (words6_entails_memRegion48 (s.sp + 0x270#64)
      0x8000000000000018#64 17#64 (s8.readReg64 .x0) 17#64 w3' w4)
    (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄
        ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄
        ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ (17#64 : BitVec 64).extractLsb' 32 32) ⊢
      memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64)
        ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
        ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)
        ((17#64 : BitVec 64).extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  have hsp11_s : s11.sp = s.sp := hsp11_10
  have hsp11_align : (s11.sp &&& 15#64 == 0#64) = true := by rw [hsp11_s]; exact hsp_align
  have hx25_11' : s11.readReg64 .x25 = s11.sp + 0x210#64 := by rw [hx25_11, hsp11_s]
  have htr11_0 : s11.trace = s0.trace :=
    htr11_10.trans (htr10_9.trans (htr9_8.trans (htr8_7.trans htr7)))
  have hcommon := stageP3_err_tail_common_ext_4k_ok img img.base ext hA
    s0 s11 coroPtr outPtr 0x8000000000000018#64 prevStatesPtr
    17#64 (s8.readReg64 .x0) 17#64 w3' w4 b_2c0 recG st
    hF11 hsym11 hpc11 hrun11 hsp11_align htr11_0
    hx0_11 hx19_11 hx22_11 hx25_11' (hx26_11.trans hx26_10) hx28_11 hx30_11
  rw [hsp11_s] at hcommon
  refine P3P4.SepWPp.ret_sepWPp_frame hcommon (by sep_focus)
    fun sf hpcf hrunf ⟨hspf, htrf, hcc, hFf, hsymf, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A
    outPtr (s8.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  have hstack_restore12 :
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_drop2]; exact Entails.refl _
  refine ⟨?_, hspf, htrf, hcc, hFf, hsymf,
    by rw [hvregs_f, hvregs_11, hvregs_cs10, hvregs_9, hvregs_cs8]⟩
  refine Entails.trans (entails_replace_sub hrec (by sep_focus) rfl) ?_
  exact entails_replace_sub hstack_restore12 (by sep_focus) (eq_of_sep_emp (by sep_focus))

theorem stageP3_err_ver_tail_ext_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (s0 s s7 : State) (coroPtr outPtr errsPtr prevStatesPtr : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hF7 : img.FrozenLoaded s7) (hsym7 : s7.symtab = img.symtab)
    (hpc7 : s7.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x33b0#64)
    (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr7 : s7.trace = s0.trace)
    (hx0_7 : s7.readReg64 .x0 = 17#64)
    (hx1_7 : s7.readReg64 .x1 = 1#64)
    (hx19_7 : s7.readReg64 .x19 = coroPtr)
    (hx24_7 : s7.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_7 : s7.readReg64 .x25 = s.sp + 0x210#64)
    (hx26_7 : s7.readReg64 .x26 = outPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 12#64) 36 ∗
       memRegion (errsPtr + 48#64) 144 ∗
       A.live errsPtr 192 8 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          memRegion (coroPtr + 0xf8#64) 344 ∗
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧
        ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s7)
      (PanicOomProp s0) :=
  stageP3_err_ver_tail_ext_4k_ok img ext himg (AllocContractsMem4K.of_AllocContracts hA)
    s0 s s7 coroPtr outPtr errsPtr prevStatesPtr msgVer b_2c0 recG st
    hF7 hsym7 hpc7 hrun7 hs7_sp hsp_align htr7
    hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7

/-! ## 3. Version-Mismatch Full Path (`stageP3_ver_ne_ext_ok`, `+0x1e04 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Stage P3 Version-Mismatch Path (`+0x1e04 → s0.readReg64 .x30`) on `tripleRatchetProgAtExt img.base ext`:
Composes Steps 1–7 (`+0x1e04 → +0x33b0`) with `stageP3_err_ver_tail_ext_ok`. -/
theorem stageP3_ver_ne_ext_4k_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsMem4K img.base A ext)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hF1 : img.FrozenLoaded s1) (hsym1 : s1.symtab = img.symtab)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
       ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       logOff img ∗
       memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr
            (.invalidMessage .preKey .decryptionFailed)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧
        ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s1)
      (PanicOomProp s0) := by
  unfold stageP3ErrPost
  dsimp only [SessionState.recordError]
  have hb_align : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hs1_sp]; exact hsp_align
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x3e0#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u3e0 => SepWPp.exists_elim fun u3e8_w =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo64_split_sp3e8 s.sp u3e8_w))
    (by sep_focus) ?_
  have hstep1 := p3_ver_ne_1e04_ext_wp img.base ext s1 coroPtr u3e0 msgVer
    (u3e8_w.extractLsb' 0 32) hb_align hpc1 hrun1 hsp1_align hx9_1 hx19_1
  rw [hs1_sp] at hstep1
  refine P3P4.SepWPp.bind_sepWP_frame hF1 hsym1 hstep1 (by sep_focus)
    fun s2 hpc2 hrun2 hF2 hsym2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, _, _, _, _, _, hx19_2, hx24_2, hx27_2, _, hx30_2, hvregs_2⟩
  have hsp2_s : s2.sp = s.sp := hsp2_1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_s] using hsp_align
  have hx24_2' : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_2.trans hx24_1
  have hx27_2' : s2.readReg64 .x27 = ctxPtr := hx27_2.trans hx27_1
  have hlog := pqxdh_log_closure_ok_ext (ext := ext) himg
  have hpc2_log : s2.pc =
    (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName := by
    rw [hpc2, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      show libsignalSessionCode.fnOff
          CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName =
        (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") from
        (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_frame_inImage_nopanic
    (spec := pqxdhLogClosureSpec img)
    (x := ())
    (φ := True)
    (T := logOff img ∗ stackAt s.sp pqxdhClosureStack)
    hF2 hsym2 hlog hpc2_log hrun2 hsp2_al hx30_2
    (by dsimp only [pqxdhLogClosureSpec]; rw [hsp2_s, pure_true, emp_sepConj])
    trivial
    (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 hsp3_al hcs3 hF3 hsym3 => ?_)
  dsimp only [pqxdhLogClosureSpec]
  rw [hsp2_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr3_2 => ?_
  have hstack_restore3 :
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_log]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore3 (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_s
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, _, _, hx27_cs3, _, _, hvregs_cs3⟩
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx24_3 : s3.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs3.trans hx24_2'
  have hx27_3 : s3.readReg64 .x27 = ctxPtr := hx27_cs3.trans hx27_2'
  have hstep3 := p3_err_ver_b_ext_wp img.base ext s3 coroPtr hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hstep3
  refine P3P4.SepWPp.bind_sepWP_frame hF3 hsym3 hstep3 (by sep_focus)
    fun s4 hpc4 hrun4 hF4 hsym4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, hx0_4, hx19_4, hx21_4, hx24_4, hx27_4, _, hx30_4, hvregs_4⟩
  have hsp4_s : s4.sp = s.sp := hsp4_3
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
  have hgrow := grow_one_spe_ok_ext (b := img.base) (ext := ext) (finish_grow_ok_ext_4k hA)
  have hpc4_grow : s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr growOneSpeName := by
    rw [hpc4, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")]
  have htr4_0 : s4.trace = s0.trace := htr4_3.trans (htr3_2.trans (htr2_1.trans htr1))
  refine P3P4.SepWPp.call_frame_frozen_oom
    (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool ∗ stackAt s.sp growOneSpeStack)
    hF4 hsym4 htr4_0 hgrow hpc4_grow hrun4 hsp4_al hx30_4
    (by
      rw [growOneSpe_pre_zero_eq A s4 (s.sp + 0x3c8#64) initErrsPtr hx0_4 hinit_ne, hsp4_s,
        pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial
    (by sep_focus)
    (hnext := fun s5 hpc5 hrun5 hsp5_4 hsp5_al hcs5 hF5 hsym5 => ?_)
  rw [growOneSpe_post_zero_eq A s4 s5 (s.sp + 0x3c8#64) initErrsPtr, hsp4_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine SepWPp.pure_elim fun htr5_4 => ?_
  refine SepWPp.pure_elim fun _ => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (pointsTo32_pair_sp3e8 s.sp msgVer (u3e8_w.extractLsb' 32 32)))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs192_split_eq errsPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_s
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, _, hx24_cs5, _, _, hx27_cs5, _, _, hvregs_cs5⟩
  have hx19_5 : s5.readReg64 .x19 = coroPtr := hx19_cs5.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = 0#64 := hx21_cs5.trans hx21_4
  have hx24_5 : s5.readReg64 .x24 = s5.sp + 0x370#64 := by
    rw [hx24_cs5, hx24_4, hx24_3, hsp5_s]
  have hx27_5 : s5.readReg64 .x27 = ctxPtr := hx27_cs5.trans (hx27_4.trans hx27_3)
  have hstep5 := p3_err_ver_c_ext_wp img.base ext s5 coroPtr errsPtr
    0x8000000000000006#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5 ctxPtr
    u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc5 hrun5 hsp5_align hx19_5 hx21_5 hx24_5
  rw [hsp5_s, hx27_5] at hstep5
  refine P3P4.SepWPp.bind_sepWP_frame hF5 hsym5 hstep5 (by sep_focus)
    fun s6 hpc6 hrun6 hF6 hsym6 hregs6 => ?_
  rcases hregs6 with ⟨hsp6_5, htr6_5, hx0_6, hx19_6, _, _, _, hx30_6, hvregs_6⟩
  refine P3P4.SepWPp.weaken_frame
    (errs48_fold_ver errsPtr e2 e3 e4 e5 msgVer (u3e8_w.extractLsb' 32 32))
    (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_al : s6.spAligned = true := by simpa only [State.spAligned, hsp6_s] using hsp_align
  have hdropSs3 := drop_session_structure3_ok_ext_4k (b := img.base) (ext := ext) hA
  have hpc6_drop : s6.pc =
    (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc6, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine P3P4.SepWPp.call_frame_frozen_nopanic
    (x := (⟨s.sp + 0xa90#64, G₁, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack)
    hF6 hsym6 hdropSs3 hpc6_drop hrun6 hsp6_al hx30_6
    (by dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]; rw [hsp6_s])
    hx0_6 (by sep_focus)
    (hnext := fun s6b hpc6b hrun6b hsp6b_6 hsp6b_al hcs6b hF6b hsym6b => ?_)
  dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]
  rw [hsp6_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr6b_6 => ?_
  have hstack_restore6b :
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_drop2]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore6b (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hlogOff_eq :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hlogOff_eq) (by sep_focus) ?_
  have hsp6b_s : s6b.sp = s.sp := hsp6b_6.trans hsp6_s
  have hsp6b_align : (s6b.sp &&& 15#64 == 0#64) = true := by rw [hsp6b_s]; exact hsp_align
  rcases hcs6b with ⟨hx19_cs6b, _, _, _, _, _, _, _, _, _, _, hvregs_cs6b⟩
  have hx19_6b : s6b.readReg64 .x19 = coroPtr := hx19_cs6b.trans hx19_6
  have hstep7 := p3_err_ver_d_ext_4k_wp img.base ext hA s6b coroPtr outPtr ctxPtr
    recG.localIk.cap 0x8000000000000006#64
    hb_align (cap_ne_noneCap_of_lt hcap_lt) hpc6b hrun6b hsp6b_align hx19_6b
  rw [hsp6b_s] at hstep7
  refine P3P4.SepWPp.bind_sepWP_frame hF6b hsym6b hstep7 (by sep_focus)
    fun s7 hpc7 hrun7 hF7 hsym7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6b, htr7_6b, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7, _, _,
    hvregs_7⟩
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢
      sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  have hfold3e0_48 :
      ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      ((s.sp + 0x3e8#64) ↦₆₄ (u3e8_w.extractLsb' 32 32 ++ msgVer)) ∗
      ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗
      ((s.sp + 0x400#64) ↦₆₄ e4) ∗ ((s.sp + 0x408#64) ↦₆₄ e5) ⊢
      memRegion (s.sp + 0x3e0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      words6_entails_memRegion48 (s.sp + 0x3e0#64)
        0xffffffffffffffff#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5
  refine P3P4.SepWPp.weaken_frame hfold3e0_48 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp).symm)
    (by sep_focus) ?_
  have htr7_0 : s7.trace = s0.trace :=
    htr7_6b.trans (htr6b_6.trans (htr6_5.trans (htr5_4.trans htr4_0)))
  have htail := stageP3_err_ver_tail_ext_4k_ok img ext himg hA
    s0 s s7 coroPtr outPtr errsPtr prevStatesPtr msgVer b_2c0 recG st
    hF7 hsym7 hpc7 hrun7 hsp7_6b hsp_align htr7_0
    hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus)
    fun sf hpcf hrunf ⟨hspf, htrf, hcc, hFf, hsymf, hvregs_f⟩ => ?_
  refine ⟨?_, hspf, htrf, hcc, hFf, hsymf,
    by rw [hvregs_f, hvregs_7, hvregs_cs6b, hvregs_6, hvregs_cs5, hvregs_4, hvregs_cs3,
      hvregs_2]⟩
  refine Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr
    (Entails.sepExists_right 1#64 ?_))
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem stageP3_ver_ne_ext_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hF1 : img.FrozenLoaded s1) (hsym1 : s1.symtab = img.symtab)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
       ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       logOff img ∗
       memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr
            (.invalidMessage .preKey .decryptionFailed)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧
        ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s1)
      (PanicOomProp s0) :=
  stageP3_ver_ne_ext_4k_ok img ext himg (AllocContractsMem4K.of_AllocContracts hA)
    s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr hinit_ne
    msgVer b_2c0 G₁ recG st hF1 hsym1 hpc1 hrun1 hs1_sp hsp_align htr1
    hx9_1 hx19_1 hx24_1 hx27_1

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

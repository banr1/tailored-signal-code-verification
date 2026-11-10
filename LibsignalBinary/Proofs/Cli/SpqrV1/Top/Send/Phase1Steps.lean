/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Phase 1a Steps for `spqr::send::<signal_session_ratchet::Coins>`: Post-`decode_state` Paths

Proves the `decode_state` `Err(e)` early-return path (`+80 -> s0.lr`) and `Ok(pq)` header
relocation step (`+80 -> +156`) for the CLI image.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession (ShaCompress)

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchet



open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Auth hiding Entails.sepExists_elim

open CryptoVerification.SpqrV1.Poly

open CryptoVerification.SpqrV1.Poly.EncoderFromPb

open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.ProtoRepr


open CryptoVerification.SpqrV1.States.FromPb

open CryptoVerification.SpqrV1.States.IntoPb

open CryptoVerification.SpqrV1.States.Leaves

open CryptoVerification.SpqrV1.Top.DecodeState

open CryptoVerification.SpqrV1.Top.ChainFrom

open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open CryptoVerification.SpqrV1.Top.EncodeVarint


open CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero
  CryptoVerification.SpqrV1.Top.DecodeState.none3Cap_add_three_beq_zero

/-- `Err(e)` return path after `spqr::decode_state` (`+80 -> s0.lr`, `+80 -> +4632`):
    writes `spqrSendResultAt A ret none`, rejoins the stack frame, and executes `CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_epilogue_4632`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_decode_state_err_step {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (ret : BitVec 64) (e : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (.error e) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        memRegion ret 72 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ spqrSendResultAt A ret none ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine EncoderFromPb.seq_clean
    (mid := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b + 4632#64)
    (P_mid :=
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (spqrSendResultAt A ret none ∗ Rest))
    (Q := fun sm => sm.sp = s0.sp - 0x1f80#64 ∧ sm.trace = s.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · rw [← CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_spqrSend_eq b ext] at hpc ⊢
    spqr_send_fetches_range_cli b (Rust.withPanics ext) 80 56
    dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
    examples_hide_fetches
    generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx26 ⊢
    refine SepWP.weaken_pre
      (sepConj_mono_right
        (sepConj_mono (memRegion_1260_split_190 fsp)
          (sepConj_mono (decodeStateResultAt_err_entails_head32_320 H_inner A (fsp + 4704#64) e)
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (memRegion_ret_72_split_err ret))))))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro r0
    apply ProofLib.SepWP.exists_left; intro rw8
    apply ProofLib.SepWP.exists_left; intro rw16
    apply ProofLib.SepWP.exists_left; intro rw24
    apply ProofLib.SepWP.exists_left; intro w1
    apply ProofLib.SepWP.exists_left; intro w2
    apply ProofLib.SepWP.exists_left; intro w3
    apply ProofLib.SepWP.exists_left; intro w190
    apply ProofLib.SepWP.exists_left; intro w198
    apply ProofLib.SepWP.exists_left; intro w1a0
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hframe := decode_state_err_frame_rejoin fsp w1 w2 w3
      have hret := err_ret_entails_sendResultAt_none A ret w1 w2 w3
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion fsp 400 ∗
           ((fsp + 400#64) ↦₆₄ w1) ∗
           ((fsp + 408#64) ↦₆₄ w2) ∗
           ((fsp + 416#64) ↦₆₄ w3) ∗
           memRegion (fsp + 424#64) (0x1260 - 0x1a8) ∗
           ((fsp + 4704#64) ↦₆₄ DecodeState.none2Cap) ∗
           ((fsp + 4712#64) ↦₆₄ w1) ∗
           ((fsp + 4720#64) ↦₆₄ w2) ∗
           ((fsp + 4728#64) ↦₆₄ w3) ∗
           memRegion (fsp + 4736#64) 320 ∗
           memRegion (fsp + 5056#64) (0x1f20 - 0x13c0)) ∗
          ((ret ↦₆₄ 18446744073709551615#64) ∗
           ((ret + 8#64) ↦₆₄ w1) ∗
           ((ret + 16#64) ↦₆₄ w2) ∗
           ((ret + 24#64) ↦₆₄ w3) ∗
           memRegion (ret + 32#64) 40) ∗
          (stackAt fsp spqrSendCalleeStack ∗
           spqrSendSavedRegs fsp s0 ∗
           Rest) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hframe (sepConj_mono_left hret)) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2⟩
    have hep := CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_epilogue_4632 (ext := ext) s0 s2 (spqrSendResultAt A ret none ∗ Rest) hsp0_align hpc2 hrun2 hsp2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩

/-! ## 1. `Ok(pq)` Relocation (`+80 -> +152`) -/

/-- `Ok(pq)` relocation step from `+80` to `+156`:
    loads the 32-byte header of `pq` into `x23 = w0` and `[sp + 0x190..0x1a8]`,
    checks `w0 ≠ none2Cap`, calls `memcpy(sp + 0x50, sp + 0x1280, 320)`, and reassembles
    `optChainPBAt A (sp + 0x60) pq.chain` and `optProtoPqRatchetInnerAt H_inner A (sp + 0xb0) pq.inner`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_decode_state_ok_to_156 {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (ret : BitVec 64) (pq : PqRatchetState) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64) :
    SepWP (tripleRatchetProgAtExt b ext) (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b + 156#64) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1260 ∗
        decodeStateResultAt H_inner A ((s0.sp - 0x1f80#64) + 0x1260#64) (.ok pq) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x13c0#64) (0x1f20 - 0x13c0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sm Pm =>
        ∃ w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64,
        ∃ bs16 : List (BitVec 8),
          w0 ≠ DecodeState.none2Cap ∧
          bs16.length = 16 ∧
          (Pm ⊢
            stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
            memRegion (s0.sp - 0x1f80#64) 0x30 ∗
            (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
            (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
            (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
            (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
            (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
            ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) pq.chain ∗
            optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) pq.inner ∗
            (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
            (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
            (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
            memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
            (relocOptVersionNegotiationPBTailAt A w0 w1 pq.versionNegotiation).1
              ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
            spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
            Rest) ∧
          sm.sp = s0.sp - 0x1f80#64 ∧
          sm.readReg64 .x19 = ret ∧
          sm.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64 ∧
          sm.readReg64 .x23 = w0 ∧
          sm.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
          sm.trace = s.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hmemcpy_raw : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy"))
      sessionMemcpyRegionSpec := Drop.sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_stub% "memcpy") (by decide))
    hA.session_memcpy_region
  rw [← CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_spqrSend_eq b ext] at hpc ⊢
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 80 76
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, decodeStateResultAt, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
  examples_hide_fetches
  generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx21 hx26 ⊢
  refine SepWP.weaken_pre
    (sepConj_mono_right
      (sepConj_mono
        (Entails.trans (memRegion_1260_split_190 fsp)
          (Entails.sepExists_elim fun w190 => Entails.sepExists_elim fun w198 => Entails.sepExists_elim fun w1a0 =>
            Entails.sepExists_right w190 (Entails.sepExists_right w198 (Entails.sepExists_right w1a0
              (sepConj_mono_left (memRegion_190_split_30_50 fsp))))))
        (sepConj_mono_left (protoPqRatchetStateAt_entails_split32_16_304 H_inner A (fsp + 4704#64) pq)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w0
  apply ProofLib.SepWP.exists_left; intro w1
  apply ProofLib.SepWP.exists_left; intro w2
  apply ProofLib.SepWP.exists_left; intro w3
  apply ProofLib.SepWP.exists_left; intro bs16
  apply ProofLib.SepWP.exists_left; intro bs304
  apply ProofLib.SepWP.exists_left; intro w190
  apply ProofLib.SepWP.exists_left; intro w198
  apply ProofLib.SepWP.exists_left; intro w1a0
  apply ProofLib.SepWP.exists_left; intro w30
  apply ProofLib.SepWP.exists_left; intro w38
  apply ProofLib.SepWP.exists_left; intro w40
  apply ProofLib.SepWP.exists_left; intro w48
  wp_focus_pure; rintro ⟨hw0, hl16, hl304⟩
  have hne2 := ne_none2Cap_add_two_beq_zero_false hw0
  have hlen_src : (bs16 ++ bs304).length = 320 := by rw [List.length_append, hl16, hl304]
  have hlen_lt64 : (bs16 ++ bs304).length < 2 ^ 64 := by rw [hlen_src]; decide
  wp_steps
  wp_apply
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
  refine ⟨w0, w1, w2, w3, w30, w38, w40, w48, bs16, hw0, hl16, ?_,
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *]⟩
  have hci := reassemble_chain_and_inner_after_memcpy H_inner A (fsp + 48#64) bs16 bs304 pq hl16 hl304
  have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := by bv_omega
  have ha96 : (fsp + 48#64) + 48#64 = fsp + 96#64 := by bv_omega
  have ha176 : (fsp + 48#64) + 128#64 = fsp + 176#64 := by bv_omega
  rw [ha80, ha96, ha176] at hci
  have hsrc := src352_rejoin_1a8_to_1f20 fsp w0 w1 w2 w3 (bs16 ++ bs304) hlen_src
  refine Entails.trans
    (Entails.of_eq (show _ =
      (((fsp + 80#64) ↦ₛ (bs16 ++ bs304)) ∗ (relocChainAndInnerAt H_inner A pq).1 bs304) ∗
      (memRegion (fsp + 424#64) (0x1260 - 0x1a8) ∗
       ((fsp + 4704#64) ↦₆₄ w0) ∗
       ((fsp + 4712#64) ↦₆₄ w1) ∗
       ((fsp + 4720#64) ↦₆₄ w2) ∗
       ((fsp + 4728#64) ↦₆₄ w3) ∗
       ((fsp + 4736#64) ↦ₛ (bs16 ++ bs304)) ∗
       memRegion (fsp + 5056#64) (0x1f20 - 0x13c0)) ∗
      (stackAt fsp spqrSendCalleeStack ∗
       memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ w30) ∗
       ((fsp + 56#64) ↦₆₄ w38) ∗
       ((fsp + 64#64) ↦₆₄ w40) ∗
       ((fsp + 72#64) ↦₆₄ w48) ∗
       ((fsp + 400#64) ↦₆₄ w1) ∗
       ((fsp + 408#64) ↦₆₄ w2) ∗
       ((fsp + 416#64) ↦₆₄ w3) ∗
       (relocOptVersionNegotiationPBTailAt A w0 w1 pq.versionNegotiation).1
         ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
       spqrSendSavedRegs fsp s0 ∗
       Rest) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hci (sepConj_mono_left hsrc)) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Send

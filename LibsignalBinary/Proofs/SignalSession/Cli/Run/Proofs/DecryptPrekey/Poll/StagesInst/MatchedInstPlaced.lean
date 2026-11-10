/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFoldPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext

/-!
# Relocatable `[LibsignalPlacement]` Poll Path B Stage P2 Instantiation

Proves `stageP2Matched_framed_cli_placed_ok : StageP2MatchedFramedCliPlacedStmt` under
`[LibsignalPlacement]` via `Matched.stageP2_matched_ok_framed_placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option linter.unusedSimpArgs false

private theorem withPanics_cliGhostExterns_eq (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      cliGhostExterns gh (cliExternsPlaced mmpl W) := by
  funext name
  by_cases hp : Rust.isPanicSymbol name = true
  · have hother :
        cliGhostExterns gh (cliExternsPlaced mmpl W) name = cliExternsPlaced mmpl W name :=
      cliGhostExterns_other gh (cliExternsPlaced mmpl W)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli, lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli, lsStringCloneSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadFileSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsReadStdinSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemsetSym] at hp)
        (fun h => by subst h; simp [Rust.isPanicSymbol, CryptoVerification.SignalSession.lsMemcpySym] at hp)
    unfold Rust.withPanics
    rw [hother]
    unfold cliExternsPlaced isCliPanicSymbolPlaced
    simp [hp]
  · simp [Rust.withPanics, hp]

private theorem dpPollProgPlaced_eq_withPanics [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
  dsimp only [dpPollProgPlaced, stageP1ProgPlaced]
  rw [withPanics_cliGhostExterns_eq mmpl gh W]

private theorem hookSat_withPanics_placed (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) {sym : String}
    {α : Type} {spec : Spec α}
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym spec) :
    HookSat (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) sym spec := by
  rw [withPanics_cliGhostExterns_eq mmpl gh W]
  exact hsat

private theorem cliExternsPlaced_blackBox_withPanics (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook := by
  rw [withPanics_cliGhostExterns_eq mmpl gh W]
  exact (cliGhostExterns_other gh (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (CryptoVerification.SignalSession.Cli.RunGlue.cliExternsPlaced_row mmpl W
      (List.mem_append_right _ (List.mem_of_getElem? (i := 11) rfl)))

private theorem cliExternsPlaced_panic_alloc_withPanics [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))
      "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked := by
  rw [withPanics_cliGhostExterns_eq mmpl gh W]
  exact hh.codecHooks.panic_raw

private theorem cliPublicKeySerialize_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec E2E.HooksE.A0)) :=
  ls_subroutine_ok_of_block (i := 518) (j := 205)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (public_key_serialize_placed_ok
        (hookSat_withPanics_placed mmpl gh W hh.codecHooks.shim)
        (hookSat_withPanics_placed mmpl gh W hh.codecHooks.alloc)
        (cliExternsPlaced_panic_alloc_withPanics mmpl gh W hh)))

private theorem cliStrToOwnedLocal2_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec E2E.HooksE.A0)) :=
  str_to_owned_local2_placed_ok_at (i := 518)
    (ls_hook_ok_ultra_of_mem (i := 530)
      (hookSat_withPanics_placed mmpl gh W
        ((show CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec =
            CryptoVerification.LibsignalTripleRatchet.sessionShimSpec from rfl) ▸
          hh.codecHooks.shim))
      (by decide))
    (ls_hook_ok_ultra_of_mem (i := 530)
      (hookSat_withPanics_placed mmpl gh W hh.codecHooks.alloc) (by decide))
    (ls_hook_ok_ultra_of_mem (i := 530)
      (hookSat_withPanics_placed mmpl gh W hh.memcpyRO) (by decide))
    (cliExternsPlaced_panic_alloc_withPanics mmpl gh W hh)

private theorem cliDealloc_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec E2E.HooksE.A0) :=
  ls_hook_ok_ultra_of_mem (i := 518)
    (hookSat_withPanics_placed mmpl gh W hh.codecHooks.dealloc)
    (by decide)

private theorem cliDropSessionStructureLocal2_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec E2E.HooksE.A0)) :=
  drop_session_structure4_placed_ok_at (i := 518)
    (hookSat_withPanics_placed mmpl gh W hh.codecHooks.dealloc)
    (by decide)

set_option maxHeartbeats 800000 in
/-- Instantiation of `StageP2MatchedFramedCliPlacedStmt` on `cliGhostExterns gh (cliExternsPlaced mmpl W)`
via `Matched.stageP2_matched_ok_framed_placed`. -/
theorem stageP2Matched_framed_cli_placed_ok [LibsignalPlacement] :
    StageP2MatchedFramedCliPlacedStmt := by
  intro mmpl gh W B S Scope y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_frame Q Qpan
    hh _hread _hdeser hcoins hMatch hcro htr hsp1 hsp0 hsp_root hpc1 hrun1 halign1 hregs
    hpan hmismatch hmatch
  rw [dpPollProgPlaced_eq_withPanics mmpl gh W] at hmismatch hmatch ⊢
  rcases hregs with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, hx28, hx29, hvregs1⟩
  have hunpack := matched_entry_unpack_placed (Scope := Scope) y sess s0 sp rngPtr v_a8 v_b8 v_d0
  refine sepWPp_conseq_pre (sepConj_mono_left hunpack) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun g => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun w => ?_
  let F_in := matchedInnerFramePlaced y rngPtr sp
  have hpre_assoc :
      (Poll.stageP2MatchedPrePlaced E2E.HooksE.A0 s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
        y.g.peerA (y.g.msgA + 0xc8#64)
        w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
        w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
        w.u_2a8 (v_b8.extractLsb' 0 32)
        y.g.msg.messageVersion y.g.msg.message.messageVersion
        w.b_4f1 0#8 0#8 0#8 w.b_3ac
        y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩ F_in) ∗ F_frame =
      Matched.stageP2MatchedPrePlaced E2E.HooksE.A0 s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
        y.g.peerA (y.g.msgA + 0xc8#64)
        w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
        w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
        w.u_2a8 (v_b8.extractLsb' 0 32)
        y.g.msg.messageVersion y.g.msg.message.messageVersion
        w.b_4f1 0#8 0#8 0#8 w.b_3ac
        y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩ (F_in ∗ F_frame) := by
    dsimp only [Poll.stageP2MatchedPrePlaced, Matched.stageP2MatchedPrePlaced, FromRecordCallees.lsLogOff]
    ac_rfl
  rw [hpre_assoc]
  refine sepWPp_entails_post ?_
  exact stageP2_matched_ok_framed_placed
    (cliPublicKeySerialize_placed_ok mmpl gh W hh)
    (cliStrToOwnedLocal2_placed_ok mmpl gh W hh)
    (cliDealloc_placed_ok mmpl gh W hh)
    (cliExternsPlaced_blackBox_withPanics mmpl gh W)
    (cliDropSessionStructureLocal2_placed_ok mmpl gh W hh)
    s0 s1
    sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
    y.g.peerA (y.g.msgA + 0xc8#64)
    w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
    w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
    w.u_2a8 (v_b8.extractLsb' 0 32)
    y.g.msg.messageVersion y.g.msg.message.messageVersion
    w.b_4f1 0#8 0#8 0#8 w.b_3ac
    y.g.msg.baseKey y.g.msg.identityKey
    g ⟨some sess⟩ sess (F_in ∗ F_frame)
    rfl hMatch.1 hMatch.2
    hcro htr hsp1 hsp_root hpc1 hrun1 halign1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28
    (x29_eq_sp_add_c70 hsp0 hx29)
    (fun sf Pf hp => by
      rw [← sepConj_assoc Pf F_in F_frame]
      exact hpan sf (Pf ∗ F_in) (poll_panicOomProp_of_matched F_in hp))
    (fun hne sf Pf hpcf hrunf hsteps hspf htrf hcsf hvregsf hcrof hent => by
      have hfold := matched_mismatch_fold_placed y s0 sp rngPtr (v_b8.extractLsb' 0 32) w
      have hpost_assoc :
          Matched.stageP2MatchedMismatchPostPlaced E2E.HooksE.A0 s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
            y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
            y.g.peerA (y.g.msgA + 0xc8#64)
            w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
            w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
            w.u_2a8 (v_b8.extractLsb' 0 32)
            y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
            y.g.msg.baseKey y.g.msg.identityKey (F_in ∗ F_frame) =
          Poll.stageP2MatchedMismatchPostPlaced E2E.HooksE.A0 s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
            y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
            y.g.peerA (y.g.msgA + 0xc8#64)
            w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
            w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
            w.u_2a8 (v_b8.extractLsb' 0 32)
            y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
            y.g.msg.baseKey y.g.msg.identityKey F_in ∗ F_frame := by
        dsimp only [Matched.stageP2MatchedMismatchPostPlaced, Poll.stageP2MatchedMismatchPostPlaced,
          FromRecordCallees.lsLogOff]
        ac_rfl
      rw [hpost_assoc] at hent
      exact ⟨_, Entails.trans hent (sepConj_mono_left hfold),
        hmismatch hne sf _ hpcf hrunf hsteps (hspf.trans hsp0) htrf hcsf
          (hvregsf.trans hvregs1) hcrof (Entails.refl _)⟩)
    (fun heq s2 recG opkHi kyberPreKeyId signedPreKeyId _hgcur hextra hsteps
        hpc2 hrun2 hsp2 halign2 htr2 hx19_2 hx27_2 hx29_2 hvregs2 hcro2 => by
      have hx29_2' := x29_eq_sp0_sub_60 hsp0 hx29_2
      refine sepWPp_lift_entails_post ?_
      refine sepWPp_conseq_pre
        (matched_match_fold_placed y sess s0 s2 sp rngPtr v_d0 g recG
          opkHi kyberPreKeyId signedPreKeyId F_frame hcoins
          hsp2 hx19_2 hx27_2) ?_
      exact hmatch heq s2 g recG y.g.msgA y.g.msgG.msg
        (((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
        opkHi kyberPreKeyId signedPreKeyId
        hextra
        (Entails.of_eq (by rw [preKeyMsgAt_eq_base_idKey_sep]; ac_rfl))
        hsteps hpc2 hrun2 hsp2 halign2 htr2 hx19_2 hx27_2 hx29_2'
        (hvregs2.trans hvregs1) hcro2)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
end

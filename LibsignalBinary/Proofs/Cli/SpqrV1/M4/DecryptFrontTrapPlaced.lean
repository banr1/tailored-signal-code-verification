/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS0Placed
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS1ErrPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvTrapV1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridgePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Drops.ChainPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Apply
public import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessage
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplay
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPb
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
public import LibsignalBinary.Proofs.ConsumeMessageKey.Assembly
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Verify
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblySat
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSliceSat
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Ext
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSat

/-!
# Relocatable Segment 3 (`DhStep`) and Block `433` Callee Seams

Proves `dhStep_433_placed_okT` (`S3TightSeamPlaced`) and instantiates all Block `433` segment seams
at `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.SpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt hiding
  ErrTailStatePlaced ErrTailStateXPlaced LoadRatchetStatePlaced FindChainStatePlaced
  DhStepStatePlaced ConsumeMsgKeyStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  VerifyMacStatePlaced AesDecryptStatePlaced ApplyRatchetStatePlaced
  ErrTailSeamPlaced S0SeamPlaced S1SeamPlaced S2SeamPlaced S3SeamPlaced S4SeamPlaced
  S5SeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

theorem blk433_s3_entry_eq [LibsignalPlacement] : (blkPl_434).base = lsmpl.base 434 := rfl

private theorem cliGhostExterns_row_placed (mmpl : Obj.MultiPlacement)
    (gh : RunGlue.CliGhostHooks) (W : CliHooks) {sym : String} {f : State → State}
    (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ CryptoVerification.SignalSession.lsReadFileSym := by decide)
    (h8 : sym ≠ CryptoVerification.SignalSession.lsReadStdinSym := by decide)
    (h9 : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (h10 : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some f :=
  (RunGlue.cliGhostExterns_other gh _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans
    (RunGlue.cliExternsPlaced_row mmpl W hrow)

/-- `ErrTailTightSeamPlaced` on Block `433` at
`RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem errTail_433_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) (ctl : BitVec 64) (S : SpqrModel) :
    ErrTailTightSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C E2E.HooksE.A0 ctl uuidTryParse S :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_433_placed_okT
    (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)

/-- `S5WTSeamPlaced` on Block `433` at `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)` from
`SpqrV1PlacedSeams mmpl gh W`. -/
theorem pqRecv_433_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (ctl : BitVec 64) :
    S5WTSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base SpqrV1.GF.Mul2U16.tokenInitPlacedAt W.C E2E.HooksE.A0 ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  exact pqRecv_433_placed_ok_WT W.C E2E.HooksE.A0 ctl (spqrV1 W.C.F W.Q.K)
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
    (spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecT _ _ _ W.C.F W.Q.K
      (hSpqr.spqrRecv_at_block (i := 434)))
    (ls_hook_ok_ultra_of_mem
      (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_formatInner_sat mmpl W)))
    (ls_hook_ok_ultra_of_mem (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG))

/-- `S8SeamPlaced` on Block `433` at `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem aesDecrypt_433_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hAesDec : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D E2E.HooksE.A0))
    (ctl : BitVec 64) (S : SpqrModel) :
    S8SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C E2E.HooksE.A0 ctl uuidTryParse S :=
  aesDecrypt_433_placed_ok W.C E2E.HooksE.A0 ctl S
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
    (ls_hook_ok_ultra_of_mem (Slots.cliExternsPlaced_aesDec_sat mmpl gh W hAesDec))
    (ls_hook_ok_ultra_of_mem
      (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_formatInner_sat mmpl W)))
    (ls_hook_ok_ultra_of_mem (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG))

/-- `S0PSeamPlaced` on Block `433` at `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem s0_433_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (ctl : BitVec 64) (S : SpqrModel) :
    S0PSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C E2E.HooksE.A0 ctl uuidTryParse S := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  have huuid : subroutine_ok
      ((CryptoVerification.blkPC_252).rebase (CryptoVerification.blkPl_252).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (CryptoVerification.blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)) := by
    refine subroutine_ok_mono
      (CryptoVerification.SignalSession.Cli.MainHops.UuidFs.uuidTryParse_placed_okFs_F
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (fun _ _ _ hp => hp) (fun x R s0 sf hq => ?_)
    dsimp only [withLsCodeLoaded, Spec.keepsFs] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.s0_433_placed_ok_P
    (CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_placed_ok_at
      E2E.HooksE.A0
      (callerProg := (blkPC_434).rebase (blkPl_434).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (cliGhostExterns_row_placed mmpl gh W (Slots.blackBox_row_placed mmpl W))
      huuid (by decide))

private theorem sub_ok_same_blk [LibsignalPlacement] {α : Type}
    {P Q : Program} {i : Nat} {H : LibsignalHooks}
    [hP : IsLsBlockProg P i H] [hQ : IsLsBlockProg Q i H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry spec) :
    subroutine_ok Q entry spec :=
  (hP.eq_blockProgram.trans hQ.eq_blockProgram.symm) ▸ h

/-- `S1TightSeamPlaced` on Block `433` at `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem s1_433_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) (ctl : BitVec 64) (S : SpqrModel) :
    S1TightSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C E2E.HooksE.A0 ctl uuidTryParse S :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_433_placed_okT
    (trFrom_placed_ok
      (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)
      (sub_ok_same_blk
        (Getters.remote_identity_key_placed_ok E2E.HooksE.A0
          (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (sub_ok_same_blk
        (Getters.drop_spe_placed_ok (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)))
      (sub_ok_same_blk
        (Getters.drop_vec_chain_placed_ok (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG))))

/-- `S2SeamPlaced` on Block `433` at `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem s2_433_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (ctl : BitVec 64) :
    S2SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base E2E.HooksE.A0 ctl :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_433_placed_ok
    (find_receiver_chain_key_placed_ok
      (cliGhostExterns_row_placed mmpl gh W (Slots.blackBox_row_placed mmpl W)))

private theorem new_from_slice_cro_of_cl_ro [LibsignalPlacement] {prog : Program}
    {F : ShaState → List (BitVec 8) → ShaState}
    (hblk : subroutine_ok prog (lsmpl.base 114)
      (withLsCodeLoaded lsmpl
        { newFromSliceSpec F with
          pre := fun x s0 =>
            (newFromSliceSpec F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ })) :
    subroutine_ok prog (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (newFromSliceSpec F)) := by
  refine subroutine_ok_mono hblk ?_ (fun _ _ _ _ hq => hq)
  intro x R s0 hp
  dsimp only [withLsCodeRoLoaded, withLsCodeLoaded] at hp ⊢
  have hcomm1 :
      ((newFromSliceSpec F).pre x s0 ∗
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        ((newFromSliceSpec F).pre x s0 ∗ R) := by ac_rfl
  have hcomm2 :
      (((newFromSliceSpec F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗
        ⌜LibsignalCodeLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
        (⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((newFromSliceSpec F).pre x s0 ∗ R)) := by ac_rfl
  rw [hcomm1, satisfies_pure_sepConj] at hp
  rw [hcomm2, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

private theorem new_from_slice_54_cro_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok
      ((blkPC_54).rebase (blkPl_54).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (newFromSliceSpec W.C.F)) := by
  have hEx : LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat
      W.C.F (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks hG
  exact new_from_slice_cro_of_cl_ro
    (ls_subroutine_ok_of_block
      (LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSliceSat.new_from_slice_placed_ok_withLsCodeLoaded_ro_sat
        W.C.F hEx.memcpy hEx.compress256))

private theorem new_from_slice_60_cro_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok
      ((blkPC_60).rebase (blkPl_60).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (newFromSliceSpec W.C.F)) := by
  have hEx : LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat
      W.C.F (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks hG
  exact new_from_slice_cro_of_cl_ro
    (ls_subroutine_ok_of_block
      (LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSliceSat.new_from_slice_placed_ok_withLsCodeLoaded_ro_sat
        W.C.F hEx.memcpy hEx.compress256))

private theorem extract_54_cro_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok
      ((blkPC_54).rebase (blkPl_54).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractSpec W.C.F)) := by
  have _ : LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat
      W.C.F (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks hG
  have hext54 :=
    LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSat.extract_placed_ok_of_inv_sat W.C
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      (Inv := LibsignalCodeRoLoaded lsmpl)
      LibsignalCodeRoLoaded.of_keepsFrozen (fun h => h.1)
      (new_from_slice_54_cro_ok mmpl gh W hG)
  refine subroutine_ok_mono hext54 (fun x R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withLsCodeRoLoaded] at hp ⊢
  exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp

private theorem addrDisplay_433_cro_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 215)
      (withLsCodeRoLoaded lsmpl (addrDisplaySpec E2E.HooksE.A0)) := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  have h215 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (addrDisplay_placed_ok
      (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_fmtWrite_sat mmpl W)))
  exact subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_434).rebase (blkPl_434).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) h215)

private theorem parseSid_61_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks) :
    subroutine_ok
      ((blkPC_61).rebase (blkPl_61).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec uuidTryParse)) := by
  have huuid252 : subroutine_ok
      ((blkPC_252).rebase (blkPl_252).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)) := by
    refine sub_ok_same_blk (subroutine_ok_mono
      (CryptoVerification.SignalSession.Cli.MainHops.UuidFs.uuidTryParse_placed_okFs_F
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (fun _ _ _ hp => hp) (fun x R s0 sf hq => ?_))
    dsimp only [withLsCodeLoaded, Spec.keepsFs] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2
  exact ls_subroutine_ok_of_block
    (callerProg := (blkPC_61).rebase (blkPl_61).base
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (parseSid_placed_ok_of_code
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) huuid252)

private theorem pkSer_205_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok
      ((blkPC_205).rebase (blkPl_205).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_205).base
      (publicKeySerializeSpec E2E.HooksE.A0) :=
  public_key_serialize_placed_ok
    (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
    (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)

private theorem createChain_433_cro_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpec W.C E2E.HooksE.A0)) := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  have _ : LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat
      W.C.F (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks hG
  have hct207 := ls_subroutine_ok_of_block
    (callerProg := (blkPC_207).rebase (blkPl_207).base
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ConsumeMessageKeyTransfer.ct_eq_ro_mem_placed_ok_withLsCodeLoaded
      (cliGhostExterns_row_placed mmpl gh W (Slots.blackBox_row_placed mmpl W)))
  have hag40 := keys_ls_subroutine_ok_of_block_cro
    (callerProg := (blkPC_40).rebase (blkPl_40).base
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (CryptoVerification.LibsignalTripleRatchet.Keys.calculateAgreement_placed_ok'
      (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_diffieHellman_sat mmpl W))
      (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_sharedSecretDrop_sat mmpl W))
      hct207
      (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
      (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
      (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_staticSecretDrop_sat mmpl W))
      (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W))
  have hext40 := keys_ls_subroutine_ok_of_block_cro
    (callerProg := (blkPC_40).rebase (blkPl_40).base
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (extract_54_cro_ok mmpl gh W hG)
  have hexp40 := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_40).rebase (blkPl_40).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat.expand_multi_info_placed_ok_sat W.C
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
  have hcc40 := CryptoVerification.LibsignalTripleRatchet.Keys.createChain_placed_ok_of_contracts
    hag40 hext40 hexp40
    (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG))
  exact keys_ls_subroutine_ok_of_block_cro
    (callerProg := (blkPC_434).rebase (blkPl_434).base
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    hcc40

/-- `S6SeamPlaced` on Block `433` at `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem s6_433_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) (ctl : BitVec 64) :
    S6SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C E2E.HooksE.A0 ctl := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  have _ : LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat
      W.C.F (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks hG
  have hext69 := keys_ls_subroutine_ok_of_block_cro
    (callerProg := (blkPC_69).rebase (blkPl_69).base
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (extract_54_cro_ok mmpl gh W hG)
  have hexp69 := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_69).rebase (blkPl_69).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat.expand_multi_info_placed_ok_sat W.C
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
  have hgk69 := CryptoVerification.LibsignalTripleRatchet.Keys.generateKeys_placed_ok_of_contracts
    hext69 hexp69
    (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG))
  exact deriveKeys_433_placed_ok W.C E2E.HooksE.A0 ctl
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
    (keys_ls_subroutine_ok_of_block_cro
      (callerProg := (blkPC_434).rebase (blkPl_434).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) hgk69)

/-- `S9SeamPlaced` on Block `433` at `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem s9_433_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) (ctl : BitVec 64) (S : SpqrModel) :
    S9SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C E2E.HooksE.A0 ctl uuidTryParse S := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hApply58 := ReceiveRatchetApply.trApply_placed_ok
    (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
    (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_framelessMemcpy_sat mmpl gh W hG)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
    (sub_ok_same_blk
      (Getters.drop_vec_message_key_placed_ok (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)))
    (sub_ok_same_blk
      (Getters.drop_vec_chain_placed_ok (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)))
  have hClear35 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (Getters.clear_unacknowledged_pre_key_message_placed_ok
      (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG))
  exact applyRatchet_433_placed_ok W.C E2E.HooksE.A0 ctl S
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block
        (callerProg := (blkPC_434).rebase (blkPl_434).base
          (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) hApply58))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block
        (callerProg := (blkPC_434).rebase (blkPl_434).base
          (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) hClear35))
    (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG))
    (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG))

section DhStepCro

open CryptoVerification.LibsignalTripleRatchet.Getters hiding drop_chain_placed_ok
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet hiding chainKeyBytes_pointsTo pack64
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep
open CryptoVerification.SignalSession.Coins

attribute [local irreducible] Program.fetch Program.externAt?

private def dhStepRecvFrame1 [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (s0 : State) : SepProp :=
  let sp := s0.sp - 1504#64
  sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
  trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
  memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
  memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
  memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x1d8#64) 0x1b8 ∗ memRegion (sp + 0x3d0#64) 0x1b0 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageRestAt A x.msgG x.msgA x.msg ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗
  stackAt (sp - BitVec.ofNat 64 createChainStack) (tryDecryptSubStack - createChainStack) ∗ tryDecryptSavedRegs s0.sp s0

private theorem withLsCodeRoLoaded_pre_of_plain [LibsignalPlacement] {α : Type}
    {spec : Spec α} {x : α} {R : SepProp} {s : State}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpre : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ R := by
  dsimp only [withLsCodeRoLoaded]
  have h1 : s.mem ⊨ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗ (spec.pre x s ∗ R) := by
    rw [satisfies_pure_sepConj]
    exact ⟨hcl, hpre⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) h1

private theorem dhStep_recv_pre_cc1_cro [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    (hwp : DhStepBlockWp prog entry rngFillEntry)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain) (R : SepProp) (s0 s : State)
    (hsc : tr.ratchet.senderChain = some sc) (hrk1_ne : s0.sp - 1504#64 + 0x3b0#64 ≠ 0#64)
    (hs3 : DhStepStatePlaced entry A ctl x trG tr st1 R s0 s) (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    let ccG1 : CreateChainGhost :=
      { rkA := sp + 0x3b0#64, rk := tr.ratchet.rootKey, theirA := x.msgA + 56#64,
        their := x.msg.senderRatchetKey, ourA := sp + 0x390#64, our := sc.ratchetKey.privateKey, ret := sp + 0x190#64 }
    ∃ sc1, Steps prog s sc1 ∧ sc1.pc = lsmpl.base 40 ∧ sc1.status = .Running ∧
      sc1.sp = sp ∧ s0.spAligned = true ∧ sc1.spAligned = true ∧
      LibsignalCodeRoLoaded lsmpl sc1.mem ∧ sc1.trace = s0.trace ∧
      calleeSavedVRegs sc1 = calleeSavedVRegs s0 ∧
      sc1.readReg64 .x19 = x.ret ∧ sc1.readReg64 .x20 = sp + 0x140#64 ∧
      sc1.readReg64 .x21 = x.ss ∧ sc1.readReg64 .x22 = x.msgA ∧
      sc1.readReg64 .x23 = sp + 0x500#64 ∧ (sc1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
      sc1.readReg64 .x25 = sp + 0x190#64 ∧ sc1.readReg64 .x26 = sp + 0x2c0#64 ∧
      sc1.readReg64 .x27 = sp + 0x38#64 ∧ sc1.readReg64 .x28 = sp + 0x2c0#64 ∧
      sc1.readReg64 .x29 = s0.sp - 96#64 ∧ sc1.readReg64 .x30 = entry + 1352#64 ∧
      (sc1.mem ⊨ (withLsCodeRoLoaded lsmpl (createChainSpec C A)).pre ccG1 sc1 ∗
        (dhStepRecvFrame1 A ctl x trG tr st1 s0 ∗ R)) := by
  obtain ⟨hpc, hmeta, hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩ := hs3
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hpriv_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 := sc.ratchetKey.privateKey.bytes.2
  have hrk_len : (keyToBytes32 tr.ratchet.rootKey).length = 32 := length_keyToBytes32 _
  obtain ⟨p0, hp0⟩ : ∃ v, pack64 (sc.ratchetKey.privateKey.bytes.toList.take 8) = v := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ v, pack64 ((sc.ratchetKey.privateKey.bytes.toList.drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ v, pack64 ((sc.ratchetKey.privateKey.bytes.toList.drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ v, pack64 (sc.ratchetKey.privateKey.bytes.toList.drop 24) = v := ⟨_, rfl⟩
  obtain ⟨k0, hk0⟩ : ∃ v, pack64 ((keyToBytes32 tr.ratchet.rootKey).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ v, pack64 (((keyToBytes32 tr.ratchet.rootKey).drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ v, pack64 (((keyToBytes32 tr.ratchet.rootKey).drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k3, hk3⟩ : ∃ v, pack64 ((keyToBytes32 tr.ratchet.rootKey).drop 24) = v := ⟨_, rfl⟩
  have hsc_split : ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) =
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗ ((sp + 0x84#64) ↦₆₄ p2) ∗
       ((sp + 0x8c#64) ↦₆₄ p3) ∗ ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) := by
    rw [hsc, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith, optSenderChainBytes_some_split sp sc trG.ratchet.senderPad,
        pointsTo_32_as_four_64 (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len, hp0, hp1, hp2, hp3,
        show sp + 0x74#64 + 8#64 = sp + 0x7c#64 by bv_arith, show sp + 0x74#64 + 16#64 = sp + 0x84#64 by bv_arith,
        show sp + 0x74#64 + 24#64 = sp + 0x8c#64 by bv_arith]; ac_rfl
  have hrk_split : ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) =
      (((sp + 0xb8#64) ↦₆₄ k0) ∗ ((sp + 0xc0#64) ↦₆₄ k1) ∗ ((sp + 0xc8#64) ↦₆₄ k2) ∗ ((sp + 0xd0#64) ↦₆₄ k3)) := by
    rw [show sp + 0x38#64 + 128#64 = sp + 0xb8#64 by bv_arith,
        pointsTo_32_as_four_64 (sp + 0xb8#64) (keyToBytes32 tr.ratchet.rootKey) hrk_len, hk0, hk1, hk2, hk3,
        show sp + 0xb8#64 + 8#64 = sp + 0xc0#64 by bv_arith, show sp + 0xb8#64 + 16#64 = sp + 0xc8#64 by bv_arith,
        show sp + 0xb8#64 + 24#64 = sp + 0xd0#64 by bv_arith]
  unfold trAt ratchetAt at hmem
  rw [hsc_split, hrk_split, split_140_for_cc1 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3c8, u3c0, u3b8, u3b0, u3a8, u3a0, u398, u390, hmem⟩
  have hwp1 := hwp.wpp_pre_cc1 s0 s x p0 p1 p2 p3 k0 k1 k2 k3 u390 u398 u3a0 u3a8 u3b0 u3b8 u3c0 u3c8
    hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 htrace hvregs
  have hmem_framed : s.mem ⊨
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3) ∗ ((sp + 0xb8#64) ↦₆₄ k0) ∗
       ((sp + 0xc0#64) ↦₆₄ k1) ∗ ((sp + 0xc8#64) ↦₆₄ k2) ∗ ((sp + 0xd0#64) ↦₆₄ k3) ∗
       ((sp + 0x390#64) ↦₆₄ u390) ∗ ((sp + 0x398#64) ↦₆₄ u398) ∗ ((sp + 0x3a0#64) ↦₆₄ u3a0) ∗
       ((sp + 0x3a8#64) ↦₆₄ u3a8) ∗ ((sp + 0x3b0#64) ↦₆₄ u3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u3c8)) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       (⌜∀ sc', tr.ratchet.senderChain = some sc' →
          Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
        (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
          trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
         vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
           (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
         ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗ ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
         ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
         ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗ memRegion (sp + 0x38#64 + 172#64) 4) ∗
        vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
        ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
        ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 72 ∗ memRegion (sp + 0x1d8#64) 0x1b8 ∗ memRegion (sp + 0x3d0#64) 0x1b0 ∗
       cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hmem
  obtain ⟨sc1, hsteps1, hout1⟩ := hwp1.elim hmem_framed hcode
  obtain ⟨hpcc1, hrunc1, P_c1, hmem_c1, hsp_c1, hx0_c1, hx1_c1, hx2_c1, hx8_c1,
    hx19_c1, hx20_c1, hx21_c1, hx22_c1, hx23_c1, hx24_c1, hx25_c1, hx26_c1, hx27_c1, hx28_c1,
    hx29_c1, hx30_c1, htrace_c1, hvregs_c1, hent_c1⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c1 : sc1.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_c1, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hcl_c1 := hcl.of_keepsFrozen hsteps1.keepsFrozen
  have hmem_c1_0 := hent_c1 sc1.mem _ hmem_c1
  have h74_fold : ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
      (((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗ ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len, hp0, hp1, hp2, hp3,
        show sp + 0x74#64 + 8#64 = sp + 0x7c#64 by bv_arith, show sp + 0x74#64 + 16#64 = sp + 0x84#64 by bv_arith,
        show sp + 0x74#64 + 24#64 = sp + 0x8c#64 by bv_arith]
  have h390_fold : ((sp + 0x390#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
      (((sp + 0x390#64) ↦₆₄ p0) ∗ ((sp + 0x398#64) ↦₆₄ p1) ∗ ((sp + 0x3a0#64) ↦₆₄ p2) ∗ ((sp + 0x3a8#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x390#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len, hp0, hp1, hp2, hp3,
        show sp + 0x390#64 + 8#64 = sp + 0x398#64 by bv_arith, show sp + 0x390#64 + 16#64 = sp + 0x3a0#64 by bv_arith,
        show sp + 0x390#64 + 24#64 = sp + 0x3a8#64 by bv_arith]
  have h3b0_fold : ((sp + 0x3b0#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) =
      (((sp + 0x3b0#64) ↦₆₄ k0) ∗ ((sp + 0x3b8#64) ↦₆₄ k1) ∗ ((sp + 0x3c0#64) ↦₆₄ k2) ∗ ((sp + 0x3c8#64) ↦₆₄ k3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x3b0#64) (keyToBytes32 tr.ratchet.rootKey) hrk_len, hk0, hk1, hk2, hk3,
        show sp + 0x3b0#64 + 8#64 = sp + 0x3b8#64 by bv_arith, show sp + 0x3b0#64 + 16#64 = sp + 0x3c0#64 by bv_arith,
        show sp + 0x3b0#64 + 24#64 = sp + 0x3c8#64 by bv_arith]
  have hb8_zero : ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 (0 : RootKey)) =
      (((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗ ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64)) := by
    rw [show sp + 0x38#64 + 128#64 = sp + 0xb8#64 by bv_arith, ← pointsTo64_zero_32 (sp + 0xb8#64),
        show sp + 0xb8#64 + 8#64 = sp + 0xc0#64 by bv_arith, show sp + 0xb8#64 + 16#64 = sp + 0xc8#64 by bv_arith,
        show sp + 0xb8#64 + 24#64 = sp + 0xd0#64 by bv_arith]
  have htr0_fold : trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } =
      (⌜∀ sc', tr.ratchet.senderChain = some sc' →
          Ratchet.clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
       (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
         trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
        vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
          (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
        (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
         (((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗ ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3)) ∗
         ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) ∗
        (((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗ ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64)) ∗
        ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
        ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗ memRegion (sp + 0x38#64 + 172#64) 4) ∗
       vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
       ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) := by
    unfold trAt ratchetAt; dsimp only
    rw [hsc, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith,
        optSenderChainBytes_some_split sp sc trG.ratchet.senderPad, h74_fold, hb8_zero]
  refine ⟨sc1, hsteps1, hpcc1, hrunc1, hsp_c1, hsp0_al, hsp_al_c1, hcl_c1, htrace_c1, hvregs_c1,
    hx19_c1, hx20_c1, hx21_c1, hx22_c1, hx23_c1, hx24_c1, hx25_c1, hx26_c1, hx27_c1, hx28_c1,
    hx29_c1, hx30_c1, withLsCodeRoLoaded_pre_of_plain hcl_c1 ?_⟩
  dsimp only [createChainSpec, dhStepRecvFrame1]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hx0_c1, hx1_c1, hx2_c1, hx8_c1, hrk1_ne⟩, ?_⟩
  rw [htr0_fold, h390_fold, h3b0_fold, show sc1.sp = sp from hsp_c1]
  unfold cliTryDecryptCommonHeapPlaced at hmem_c1_0
  rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
      show s0.sp - 1504#64 = sp from rfl, stackAt_subStack_createChain sp] at hmem_c1_0
  exact Eq.mp (congrArg (sc1.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hmem_c1_0

private theorem dhStep_recv_create_chain_cro_cli [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    (hwp : DhStepBlockWp prog entry rngFillEntry)
    (hcc : subroutine_ok prog (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec C A)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain) (R : SepProp) (s0 s : State)
    (hsc : tr.ratchet.senderChain = some sc) (hrk1_ne : s0.sp - 1504#64 + 0x3b0#64 ≠ 0#64)
    (hs3 : DhStepStatePlaced entry A ctl x trG tr st1 R s0 s) (hcode : prog.CodeLoaded s.mem) :
    match rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | .ok (rk1, rck) =>
      ∃ s', Steps prog s s' ∧
        (CliDhStepAfterRecvChainStatePlaced entry A ctl x trG tr st1 rk1 rck R s0 s' ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)))
    | .error e =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG' r1, ErrTailStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 e 0 R s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  set sp := s0.sp - 1504#64
  have hpriv_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 := sc.ratchetKey.privateKey.bytes.2
  have hrk_len : (keyToBytes32 tr.ratchet.rootKey).length = 32 := length_keyToBytes32 _
  let ccG1 : CreateChainGhost :=
    { rkA := sp + 0x3b0#64, rk := tr.ratchet.rootKey, theirA := x.msgA + 56#64,
      their := x.msg.senderRatchetKey, ourA := sp + 0x390#64, our := sc.ratchetKey.privateKey, ret := sp + 0x190#64 }
  let Frame1 := dhStepRecvFrame1 A ctl x trG tr st1 s0
  obtain ⟨sc1, hsteps1, hpcc1, hrunc1, hsp_c1, hsp0_al, hsp_al_c1, hcl_c1, htrace_c1, hvregs_c1,
    hx19_c1, hx20_c1, hx21_c1, hx22_c1, hx23_c1, hx24_c1, hx25_c1, hx26_c1, hx27_c1, hx28_c1,
    hx29_c1, hx30_c1, hpre_cc1⟩ :=
    dhStep_recv_pre_cc1_cro hwp x trG tr st1 sc R s0 s hsc hrk1_ne hs3 hcode
  obtain ⟨sm, hsteps_cc1, hout_cc1⟩ :=
    subroutine_ok_apply_outcome hcc ccG1 (Frame1 ∗ R) hpcc1 hrunc1 hpre_cc1 hsp_al_c1 (hsteps1.codeLoaded hcode)
  have hsteps12 : Steps prog s sm := Steps.trans hsteps1 hsteps_cc1
  rcases hout_cc1 with ⟨hret_m, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, -, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · have hpcm : sm.pc = entry + 1352#64 := hret_m.1.trans hx30_c1
    have hrunm : sm.status = .Running := hret_m.2.2
    dsimp only [withLsCodeRoLoaded, createChainSpec, ccG1] at hpost; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hcl_m := hcl_c1.of_keepsFrozen hsteps_cc1.keepsFrozen
    have htrace_m0 := hpost.1; have hpost := hpost.2
    have htrace_m : sm.trace = s0.trace := htrace_m0.trans htrace_c1
    have hsp_m : sm.sp = s0.sp - 1504#64 := hspm.trans hsp_c1
    have hsp_al_m : sm.spAligned = true := by unfold State.spAligned at hsp_al_c1 ⊢; rw [hspm]; exact hsp_al_c1
    have hx19_m : sm.readReg64 .x19 = x.ret := hcsm.1.trans hx19_c1
    have hx20_m : sm.readReg64 .x20 = sp + 0x140#64 := hcsm.2.1.trans hx20_c1
    have hx21_m : sm.readReg64 .x21 = x.ss := hcsm.2.2.1.trans hx21_c1
    have hx22_m : sm.readReg64 .x22 = x.msgA := hcsm.2.2.2.1.trans hx22_c1
    have hx23_m : sm.readReg64 .x23 = sp + 0x500#64 := hcsm.2.2.2.2.1.trans hx23_c1
    have hx24_m : (sm.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by rw [hcsm.2.2.2.2.2.1]; exact hx24_c1
    have hx25_m : sm.readReg64 .x25 = sp + 0x190#64 := hcsm.2.2.2.2.2.2.1.trans hx25_c1
    have hx26_m : sm.readReg64 .x26 = sp + 0x2c0#64 := hcsm.2.2.2.2.2.2.2.1.trans hx26_c1
    have hx27_m : sm.readReg64 .x27 = sp + 0x38#64 := hcsm.2.2.2.2.2.2.2.2.1.trans hx27_c1
    have hx28_m : sm.readReg64 .x28 = sp + 0x2c0#64 := hcsm.2.2.2.2.2.2.2.2.2.1.trans hx28_c1
    have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c1
    have hmeta_m : tryDecryptMidMetaPlaced s0 sm := ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl_m, by reg_chain⟩
    have hpost_grouped : sm.mem ⊨
        (memRegion (sp + 0x1d8#64) 0x1b8 ∗ ((sp + 0x390#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
         ((sp + 0x3b0#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗ memRegion (sp + 0x3d0#64) 0x1b0) ∗
        (memRegion (sp + 0x140#64) 0x50 ∗
         createChainResultAt (sp + 0x190#64) (rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
         memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
         memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
         cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
      dsimp only [Frame1, dhStepRecvFrame1] at hpost; rw [show sc1.sp = sp from hsp_c1] at hpost; unfold cliTryDecryptCommonHeapPlaced
      rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
          show s0.sp - 1504#64 = sp from rfl, stackAt_subStack_createChain sp]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hpost
    have hpost_folded := Satisfies.mono (sepConj_mono_left (fold_390_3b0_to_memRegion sp _ _ hpriv_len hrk_len)) hpost_grouped
    unfold rootCreateChain at hpost_folded ⊢
    cases hcc1 : Ratchet.createChain C.F C.X tr.ratchet.rootKey x.msg.senderRatchetKey.bytes sc.ratchetKey.privateKey.bytes with
    | none =>
      rw [hcc1] at hpost_folded; dsimp only [hcc1] at hpost_folded ⊢
      let Rest_err : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R
      have hmem_err : sm.mem ⊨ memRegion (sp + 0x140#64) 0x50 ∗
          createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗ memRegion (sp + 0x1d8#64) 0x3a8 ∗ Rest_err :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_err, sp]; ac_rfl)) hpost_folded
      obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
        dhStep_cc1_err_branch_placed (A := A) hwp Rest_err s0 sm hpcm hmeta_m
          hx20_m hx23_m hx25_m hx26_m hmem_err (hsteps12.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps12 hsteps2, Or.inl ⟨trG, { tr.ratchet with rootKey := (0 : RootKey) }, ?_⟩⟩
      refine ⟨hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s', ?_⟩
      dsimp only [Rest_err] at hmems'
      have hsp38_ent :
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ⊢ memRegion sp 0x38 := by
        rw [memRegion_split' (b := sp) (b' := sp + 0x20#64) (n := 0x20) (k := 0x18) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 0x8) (k := 0x10) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 0x4) (k := 0xc) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 0x4) (k := 0x8) rfl (by bv_arith) (by decide)]
        exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono_right (pointsTo64_entails_memRegion _ _))))
      have hmems1 : s'.mem ⊨
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ∗
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗ memRegion (sp + 0x140#64) 0x28 ∗
           speBodyAt A (LibsignalTripleRatchetRepr.utf8 "decrypt") (sp + 0x168#64) .invalidKeyAgreement ∗
           memRegion (sp + 0x190#64) 0x3f0 ∗ cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) :=
        Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp] at hmems' ⊢; ac_rfl)) hmems'
      have hmems2 := Satisfies.mono (sepConj_mono_left hsp38_ent) hmems1
      dsimp only [sp] at hmems2 ⊢; exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems2
    | some p1 =>
      rcases p1 with ⟨rk1, rckKey⟩; rw [hcc1] at hpost_folded; dsimp only [hcc1] at hpost_folded ⊢
      let Rest_ok : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x1d8#64) 0x3a8 ∗
        cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R
      have hmem_ok : sm.mem ⊨ createChainResultAt (sp + 0x190#64) (.ok (rk1, ⟨rckKey, 0⟩)) ∗ Rest_ok :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_ok, sp]; ac_rfl)) hpost_folded
      obtain ⟨s', hsteps2, hpcs', hmetas', hcss', hmems'⟩ :=
        dhStep_cc1_ok_branch_placed hwp rk1 ⟨rckKey, 0⟩ Rest_ok s0 sm hpcm hmeta_m hx25_m hmem_ok (hsteps12.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps12 hsteps2, Or.inl ?_⟩
      refine ⟨hpcs', hmetas',
        hcss'.1.trans hx19_m, hcss'.2.1.trans hx20_m, hcss'.2.2.1.trans hx21_m,
        hcss'.2.2.2.1.trans hx22_m, hcss'.2.2.2.2.1.trans hx23_m,
        by rw [hcss'.2.2.2.2.2.1]; exact hx24_m,
        hcss'.2.2.2.2.2.2.1.trans hx25_m, hcss'.2.2.2.2.2.2.2.1.trans hx26_m,
        hcss'.2.2.2.2.2.2.2.2.1.trans hx27_m, hcss'.2.2.2.2.2.2.2.2.2.1.trans hx28_m, ?_⟩
      dsimp only [Rest_ok, sp] at hmems' ⊢; exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems'
  · have hpan_td := onPanic_of_createChain_placed (C := C) (A := A) (ctl := ctl) (S := S) (x := x) (ccG := ccG1) htrace_c1 hpost
    cases rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | ok p1 => rcases p1 with ⟨rk1, rck⟩; exact ⟨sm, hsteps12, Or.inr ⟨hpan, hpan_td⟩⟩
    | error e => exact ⟨sm, hsteps12, Or.inr ⟨hpan, hpan_td⟩⟩
  · dsimp only [withLsCodeRoLoaded, createChainSpec] at hpost; rw [satisfies_pure_sepConj] at hpost; exact False.elim hpost.1

private def dhStepSendFrame2 [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (rck : ChainKey) (newSenderKey : LibsignalSession.KeyPair)
    (msgW : BitVec 32) (draws : Nat) (s0 : State) : SepProp :=
  let sp := s0.sp - 1504#64
  sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
  trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
  memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
  ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
  ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
  memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
  memRegion (sp + 0x1d8#64) 0x1f8 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
  memRegion (sp + 0x3f4#64) 12 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
  memRegion (sp + 0x440#64) 0x60 ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
  ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageRestAt A x.msgG x.msgA x.msg ∗ cliTapeAfter ctl x.cur x.rest draws ∗ FromRecordCallees.lsLogOff ∗
  stackAt (sp - BitVec.ofNat 64 createChainStack) (tryDecryptSubStack - createChainStack) ∗
  tryDecryptSavedRegs s0.sp s0

private theorem dhStep_cc2_err_cro [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    (hwp : DhStepBlockWp prog entry rngFillEntry)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (rk1 : RootKey) (rck : ChainKey)
    (msgW : BitVec 32) (R : SepProp) (s0 sm : State)
    (hpcm : sm.pc = entry + 2008#64) (hmeta_m : tryDecryptMidMetaPlaced s0 sm)
    (hx19_m : sm.readReg64 .x19 = x.ret)
    (hx20_m : sm.readReg64 .x20 = s0.sp - 1504#64 + 0x140#64)
    (hx23_m : sm.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25_m : sm.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hx26_m : sm.readReg64 .x26 = s0.sp - 1504#64 + 0x2c0#64)
    (hcode_m : prog.CodeLoaded sm.mem)
    (hpost_err : sm.mem ⊨
        createChainResultAt (s0.sp - 1504#64 + 0x190#64) (.error .invalidKeyAgreement) ∗
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (s0.sp - 1504#64 + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x10 ∗
        ((s0.sp - 1504#64 + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (s0.sp - 1504#64 + 0x14#64) 8 ∗
        ((s0.sp - 1504#64 + 0x1c#64) ↦₃₂ msgW) ∗ ((s0.sp - 1504#64 + 0x20#64) ↦₆₄ x.locA) ∗
        ((s0.sp - 1504#64 + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (s0.sp - 1504#64 + 0x2c#64) 4 ∗ ((s0.sp - 1504#64 + 0x30#64) ↦₆₄ x.remA) ∗
        memRegion (s0.sp - 1504#64 + 0x140#64) 0x50 ∗
        memRegion (s0.sp - 1504#64 + 0x1d8#64) 0x1f8 ∗ ((s0.sp - 1504#64 + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
        memRegion (s0.sp - 1504#64 + 0x3f4#64) 12 ∗
        ((s0.sp - 1504#64 + 0x400#64) ↦ₛ (KeyPair.generate C (coinsOf x.rest)).publicKey.bytes.toList) ∗
        ((s0.sp - 1504#64 + 0x420#64) ↦ₛ (KeyPair.generate C (coinsOf x.rest)).privateKey.bytes.toList) ∗
        memRegion (s0.sp - 1504#64 + 0x440#64) 0x60 ∗
        ((s0.sp - 1504#64 + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
        ((s0.sp - 1504#64 + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
        ((s0.sp - 1504#64 + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
        memRegion (s0.sp - 1504#64 + 0x4e0#64) 0xa0 ∗
        cliTryDecryptCommonHeapPlaced A ctl x (min 32 x.rest.length) s0 ∗ R) :
    ∃ s', Steps prog sm s' ∧
      ∃ trG' r1, ErrTailStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 .invalidKeyAgreement (min 32 x.rest.length) R s0 s' := by
  set sp := s0.sp - 1504#64
  set draws := min 32 x.rest.length
  set newSenderKey := KeyPair.generate C (coinsOf x.rest)
  have hpost_err0 : sm.mem ⊨
      (memRegion (sp + 0x1d8#64) 0x1f8 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
       memRegion (sp + 0x3f4#64) 12 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x440#64) 0x60 ∗
       ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0) ∗
      (((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
       memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [sp, draws, newSenderKey]; ac_rfl)) hpost_err
  have hpost_err1 := Satisfies.mono (sepConj_mono_left
    (fold_1d8_after_cc2_err sp rck newSenderKey.publicKey.bytes.toList newSenderKey.privateKey.bytes.toList rk1
      newSenderKey.publicKey.bytes.2 newSenderKey.privateKey.bytes.2)) hpost_err0
  let Rest_err : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R
  have hmem_err : sm.mem ⊨ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x140#64) 0x50 ∗
      createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗ memRegion (sp + 0x1d8#64) 0x3a8 ∗ Rest_err :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_err]; ac_rfl)) hpost_err1
  obtain ⟨s', hsteps2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_cc2_err_branch_placed (A := A) hwp msgW Rest_err s0 sm hpcm hmeta_m
      hx20_m hx23_m hx25_m hx26_m hmem_err hcode_m
  refine ⟨s', hsteps2, trG, { tr.ratchet with rootKey := (0 : RootKey) }, hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s', ?_⟩
  dsimp only [Rest_err] at hmems'
  have hmems0 : s'.mem ⊨
      (memRegion sp 0x10 ∗ ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW)) ∗
      (((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
       memRegion x.ret 48 ∗ memRegion (sp + 0x140#64) 0x28 ∗
       speBodyAt A (LibsignalTripleRatchetRepr.utf8 "decrypt") (sp + 0x168#64) .invalidKeyAgreement ∗
       memRegion (sp + 0x190#64) 0x3f0 ∗ cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) :=
    Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp] at hmems' ⊢; ac_rfl)) hmems'
  have hmems0' := Satisfies.mono (sepConj_mono_left (fold_sp_20_after_cc2_err sp rck msgW)) hmems0
  have hsp38_ent :
      (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ⊢ memRegion sp 0x38 := by
    rw [memRegion_split' (b := sp) (b' := sp + 0x20#64) (n := 0x20) (k := 0x18) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 0x8) (k := 0x10) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 0x4) (k := 0xc) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 0x4) (k := 0x8) rfl (by bv_arith) (by decide)]
    exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono_right (pointsTo64_entails_memRegion _ _))))
  have hmems1 : s'.mem ⊨
      (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
       memRegion x.ret 48 ∗ memRegion (sp + 0x140#64) 0x28 ∗
       speBodyAt A (LibsignalTripleRatchetRepr.utf8 "decrypt") (sp + 0x168#64) .invalidKeyAgreement ∗
       memRegion (sp + 0x190#64) 0x3f0 ∗ cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) :=
    Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems0'
  have hmems2 := Satisfies.mono (sepConj_mono_left hsp38_ent) hmems1
  dsimp only [sp, draws] at hmems2 ⊢; exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems2

private theorem dhStep_keygen_and_send_create_chain_cro_cli [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    (hwp : DhStepBlockWp prog entry rngFillEntry)
    (hcc : subroutine_ok prog (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec C A)))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (withLsCodeLoaded lsmpl (derivePublicKeyBytesSpec C.pubKey)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (rk1 : RootKey) (rck : ChainKey) (R : SepProp) (s0 s : State)
    (hrng : subroutine_ok prog rngFillEntry
      (withLsCodeLoaded lsmpl (coinsFillAtSpecPlaced tryDecryptSubStack x.cur x.rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop") zeroizeSecretSpec)
    (hrk2_ne : s0.sp - 1504#64 + 0x4a0#64 ≠ 0#64)
    (hafter : CliDhStepAfterRecvChainStatePlaced entry A ctl x trG tr st1 rk1 rck R s0 s)
    (hcode : prog.CodeLoaded s.mem) :
    let newSenderKey := KeyPair.generate C (coinsOf x.rest)
    match rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey with
    | .ok (finalRootKey, senderChainKey) =>
      ∃ s', Steps prog s s' ∧
        (CliDhCommitStatePlaced entry A ctl x trG tr st1 rck newSenderKey finalRootKey senderChainKey R s0 s' ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)))
    | .error e =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG' r1, ErrTailStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 e (min 32 x.rest.length) R s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  set sp := s0.sp - 1504#64
  set draws := min 32 x.rest.length
  set newSenderKey := KeyPair.generate C (coinsOf x.rest)
  obtain ⟨s5, hsteps5, hpc5, hmeta5, hx0_5, hx1_5, hx2_5, hx8_5, hx19_5, hx20_5, hx21_5,
    hx22_5, hx23_5, hx25_5, hx26_5, hx27_5, hx28_5, hx30_5, msgW, hmsgW, hmem5⟩ :=
    dhStep_after_cc1_to_cc2_call_placed_cli hwp hdpk x trG tr st1 rk1 rck R s0 s hrng hsd hafter hcode
  obtain ⟨hrun5, hsp5, hsp0_al, hsp_al5, hx29_5, htrace5, hcl5, hvregs5⟩ := hmeta5
  let ccG2 : CreateChainGhost :=
    { rkA := sp + 0x4a0#64, rk := rk1, theirA := x.msgA + 56#64, their := x.msg.senderRatchetKey,
      ourA := sp + 0x420#64, our := newSenderKey.privateKey, ret := sp + 0x190#64 }
  let Frame2 := dhStepSendFrame2 A ctl x trG tr st1 rck newSenderKey msgW draws s0
  have hpre_cc2 : s5.mem ⊨ (withLsCodeRoLoaded lsmpl (createChainSpec C A)).pre ccG2 s5 ∗ (Frame2 ∗ R) := by
    refine withLsCodeRoLoaded_pre_of_plain hcl5 ?_
    dsimp only [createChainSpec, ccG2, Frame2, dhStepSendFrame2]; simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_5, hx1_5, hx2_5, hx8_5, hrk2_ne⟩, ?_⟩
    rw [show s5.sp = sp from hsp5]; unfold cliTryDecryptCommonHeapPlaced at hmem5
    rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
        show s0.sp - 1504#64 = sp from rfl, stackAt_subStack_createChain sp] at hmem5
    exact Eq.mp (congrArg (s5.mem ⊨ ·) (by dsimp only [sp, draws, newSenderKey]; ac_rfl)) hmem5
  obtain ⟨sm, hsteps_cc2, hout_cc2⟩ :=
    subroutine_ok_apply_outcome hcc ccG2 (Frame2 ∗ R) hpc5 hrun5 hpre_cc2 hsp_al5 (hsteps5.codeLoaded hcode)
  have hsteps5m : Steps prog s sm := Steps.trans hsteps5 hsteps_cc2
  rcases hout_cc2 with ⟨hret_m, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, -, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · have hpcm : sm.pc = entry + 2008#64 := hret_m.1.trans hx30_5
    have hrunm : sm.status = .Running := hret_m.2.2
    dsimp only [withLsCodeRoLoaded, createChainSpec, ccG2] at hpost; simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hcl_m := hcl5.of_keepsFrozen hsteps_cc2.keepsFrozen
    have htrace_m0 := hpost.1; have hpost := hpost.2
    have hsp_al_m : sm.spAligned = true := by unfold State.spAligned at hsp_al5 ⊢; rw [hspm]; exact hsp_al5
    have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
      ⟨hrunm, by reg_chain, hsp0_al, hsp_al_m, by reg_chain, by reg_chain, hcl_m, by reg_chain⟩
    have hpost_grouped : sm.mem ⊨
        createChainResultAt (sp + 0x190#64) (rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey) ∗
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x1d8#64) 0x1f8 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
        memRegion (sp + 0x3f4#64) 12 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
        ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x440#64) 0x60 ∗
        ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
        ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
        cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R := by
      dsimp only [Frame2, dhStepSendFrame2] at hpost; rw [show s5.sp = sp from hsp5] at hpost; unfold cliTryDecryptCommonHeapPlaced
      rw [signalMessageAt_senderRatchetKey A x.msgG x.msgA x.msg,
          show s0.sp - 1504#64 = sp from rfl, stackAt_subStack_createChain sp]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [sp]; ac_rfl)) hpost
    dsimp only; unfold rootCreateChain at hpost_grouped ⊢
    cases hcc2 : Ratchet.createChain C.F C.X rk1 x.msg.senderRatchetKey.bytes newSenderKey.privateKey.bytes with
    | none =>
      rw [hcc2] at hpost_grouped; dsimp only at hpost_grouped ⊢
      obtain ⟨s', hsteps2, herr⟩ := dhStep_cc2_err_cro hwp x trG tr st1 rk1 rck msgW R s0 sm
        hpcm hmeta_m (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
        (hsteps5m.codeLoaded hcode) hpost_grouped
      exact ⟨s', Steps.trans hsteps5m hsteps2, Or.inl herr⟩
    | some p2 =>
      rcases p2 with ⟨finalRootKey, sckKey⟩; rw [hcc2] at hpost_grouped; dsimp only at hpost_grouped ⊢
      have hpost_ok0 : sm.mem ⊨
          (memRegion (sp + 0x1d8#64) 0x1f8 ∗ memRegion (sp + 0x440#64) 0x60 ∗ ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1)) ∗
          (createChainResultAt (sp + 0x190#64) (.ok (finalRootKey, ⟨sckKey, 0⟩)) ∗
           sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
           ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
           ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
           ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗ memRegion (sp + 0x3f4#64) 12 ∗
           ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
           ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
           ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
           ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
           cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hpost_grouped
      have hpost_ok1 := Satisfies.mono (sepConj_mono_left (fold_after_cc2_ok sp rk1)) hpost_ok0
      let Rest_ok : SepProp :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x1d8#64) 0xd8 ∗ memRegion (sp + 0x2b0#64) 0x10 ∗ memRegion (sp + 0x2c0#64) 0x110 ∗
        ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗ memRegion (sp + 0x3f4#64) 12 ∗
        ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
        ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x440#64) 0x80 ∗
        ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
        ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
        cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R
      have hmem_ok : sm.mem ⊨ createChainResultAt (sp + 0x190#64) (.ok (finalRootKey, ⟨sckKey, 0⟩)) ∗ Rest_ok :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_ok]; ac_rfl)) hpost_ok1
      obtain ⟨s', hsteps2, hpcs', hmetas', hcss', hmems'⟩ :=
        dhStep_cc2_ok_branch_placed hwp finalRootKey ⟨sckKey, 0⟩ Rest_ok s0 sm hpcm hmeta_m
          (by reg_chain) hmem_ok (hsteps5m.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps5m hsteps2, Or.inl ?_⟩
      refine ⟨hpcs', hmetas', by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
        by reg_chain, by reg_chain, by reg_chain, msgW, hmsgW, ?_⟩
      dsimp only [Rest_ok, sp, draws, newSenderKey] at hmems' ⊢
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by ac_rfl)) hmems'
  · have hpan_td := onPanic_of_createChain_placed (C := C) (A := A) (ctl := ctl) (S := S) (x := x) (ccG := ccG2) htrace5 hpost; dsimp only
    cases rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey with
    | ok p2 => rcases p2 with ⟨finalRootKey, senderChainKey⟩; exact ⟨sm, hsteps5m, Or.inr ⟨hpan, hpan_td⟩⟩
    | error e => exact ⟨sm, hsteps5m, Or.inr ⟨hpan, hpan_td⟩⟩
  · dsimp only [withLsCodeRoLoaded, createChainSpec] at hpost; rw [satisfies_pure_sepConj] at hpost; exact False.elim hpost.1

private theorem s3_cro_okT_cli [LibsignalPlacement] {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockWp prog entry rngFillEntry) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok prog (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec C A)))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (withLsCodeLoaded lsmpl (derivePublicKeyBytesSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry
        (withLsCodeLoaded lsmpl (coinsFillAtSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop") zeroizeSecretSpec)
    (hcommit : CliS3CommitSeamPlaced prog entry C A ctl uuidTryParse P3kR1bd.spqrNoPanic) :
    S3TightSeamPlaced prog entry C A ctl uuidTryParse S := by
  intro x trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hs3 hcode; dsimp only
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_none C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet hsc,
        decryptDraws_of_senderChain_none C x.st st1 tr x.msg.senderRatchetKey x.rest hfrom hfind hsc]
    obtain ⟨s', hsteps, ⟨_, _, herr⟩ | ⟨_, hoom⟩⟩ := dhStep_missing_sender_chain_placed_cli hwp x trG tr st1 R s0 s hsc hs3 hcode
    · exact ⟨s', hsteps, Or.inl ⟨trG, tr.ratchet, herr⟩⟩
    · exact hoom.elim
  | some sc =>
    have ⟨hrk1_ne, hrk2_ne⟩ := rk_ne_zero s0.sp (s0.sp - 1504#64) rfl hsp0
    have hstep1 := dhStep_recv_create_chain_cro_cli (S := P3kR1bd.spqrNoPanic) hwp hcc x trG tr st1 sc R s0 s hsc hrk1_ne hs3 hcode
    cases hcc1 : rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | error e =>
      rw [hcc1] at hstep1
      rw [dhRatchetStep_some_err1 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc e hsc hcc1,
          decryptDraws_of_cc1_err C x.st st1 tr x.msg.senderRatchetKey x.rest sc e hfrom hfind hsc hcc1]
      obtain ⟨s1, hsteps1, herr1 | ⟨hpan1, hq1⟩⟩ := hstep1
      · exact ⟨s1, hsteps1, Or.inl herr1⟩
      · exact ⟨s1, hsteps1, Or.inr ⟨hpan1, P3kR1bd.onPanicTightPlaced_of_spqrNoPanic hq1⟩⟩
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩; rw [hcc1] at hstep1
      rw [decryptDraws_of_cc1_ok C x.st st1 tr x.msg.senderRatchetKey x.rest sc rk1 rck hfrom hfind hsc hcc1]
      obtain ⟨s1, hsteps1, hafter | ⟨hpan1, hq1⟩⟩ := hstep1
      · have hstep2 := dhStep_keygen_and_send_create_chain_cro_cli (S := P3kR1bd.spqrNoPanic)
          hwp hcc hdpk x trG tr st1 rk1 rck R s0 s1 (hrng x.cur x.rest hx_rest) hsd hrk2_ne hafter (hsteps1.codeLoaded hcode)
        dsimp only at hstep2
        cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error e =>
          rw [hcc2] at hstep2
          rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc rk1 rck e hsc hcc1 hcc2]
          obtain ⟨s2, hsteps2, herr2 | ⟨hpan2, hq2⟩⟩ := hstep2
          · exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inl herr2⟩
          · exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inr ⟨hpan2, P3kR1bd.onPanicTightPlaced_of_spqrNoPanic hq2⟩⟩
        | ok p2 =>
          rcases p2 with ⟨finalRootKey, senderChainKey⟩; rw [hcc2] at hstep2
          rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
          obtain ⟨s2, hsteps2, hcm | ⟨hpan2, hq2⟩⟩ := hstep2
          · have hsteps12 := Steps.trans hsteps1 hsteps2
            have hclamp := clampScalar_keyPair_generate C (coinsOf x.rest)
            obtain ⟨s3, hsteps3, hout3 | ⟨hpan3, hq3⟩⟩ :=
              hcommit x trG tr st1 sc rck (KeyPair.generate C (coinsOf x.rest))
                finalRootKey senderChainKey R s0 s2 hsc hrc_len hclamp hcm (hsteps12.codeLoaded hcode)
            · exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inl hout3⟩
            · exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inr ⟨hpan3, P3kR1bd.onPanicTightPlaced_of_spqrNoPanic hq3⟩⟩
          · exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inr ⟨hpan2, P3kR1bd.onPanicTightPlaced_of_spqrNoPanic hq2⟩⟩
      · cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error e =>
          rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc rk1 rck e hsc hcc1 hcc2]
          exact ⟨s1, hsteps1, Or.inr ⟨hpan1, P3kR1bd.onPanicTightPlaced_of_spqrNoPanic hq1⟩⟩
        | ok p2 =>
          rcases p2 with ⟨finalRootKey, senderChainKey⟩
          rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
          exact ⟨s1, hsteps1, Or.inr ⟨hpan1, P3kR1bd.onPanicTightPlaced_of_spqrNoPanic hq1⟩⟩

set_option maxRecDepth 200000

private theorem derivePk_433_cl_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 200)
      (withLsCodeLoaded lsmpl (derivePublicKeyBytesSpec W.C.pubKey)) := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  exact ConsumeMessageKeyTransfer.ls_subroutine_ok_transfer_of_plain
    (callerProg := (blkPC_434).rebase (blkPl_434).base
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (derive_public_key_bytes_placed_ok
      (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_derivePublicKeyBytes_sat mmpl W)))

private theorem chainKeyToPb_433_cl_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 22)
      (withLsCodeLoaded lsmpl (chainKeyToPbSpec E2E.HooksE.A0)) := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  exact ConsumeMessageKeyTransfer.ls_subroutine_ok_transfer_of_plain
    (callerProg := (blkPC_434).rebase (blkPl_434).base
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (chain_key_to_pb_placed_ok
      (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
      (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
      (Slots.cliGhostExterns_panic_handle_error mmpl gh W))

private theorem dropChain_433_cl_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 445)
      (withLsCodeLoaded lsmpl (dropChainSpec E2E.HooksE.A0)) := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  exact ConsumeMessageKeyTransfer.ls_subroutine_ok_transfer_of_plain
    (callerProg := (blkPC_434).rebase (blkPl_434).base
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_placed_ok
      (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG))

private theorem growOne_433_cl_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 43)
      (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec E2E.HooksE.A0)) := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  exact ConsumeMessageKeyTransfer.growOneChain_placed_ok_at_block
    (callerProg := (blkPC_434).rebase (blkPl_434).base
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    ((RunGlue.cliGhostExterns_shim gh _).trans (congrArg some hG.shim_eq))
    (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_realloc_sat mmpl gh W hG)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)

/-- `S3TightSeamPlaced` on Block `433` at `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem dhStep_433_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) (ctl : BitVec 64) (S : SpqrModel) :
    S3TightSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 434) W.C E2E.HooksE.A0 ctl uuidTryParse S := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  exact s3_cro_okT_cli
    (dhStepBlockWp_549 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    W.C E2E.HooksE.A0 ctl S
    (createChain_433_cro_ok mmpl gh W hG) (derivePk_433_cl_ok mmpl gh W)
    (fun cur rest _ =>
      ls_subroutine_ok_of_block
        (callerProg := (blkPC_434).rebase (blkPl_434).base
          (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (Slots.cliCoinsFillAtPlaced_ok_cl mmpl gh W hG cur rest tryDecryptSubStack
          (by decide) (by decide)))
    (keys_ls_hook_ok_of_mem
      (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_staticSecretDrop_sat mmpl W)))
    (s3_commit_433_placed_ok (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      W.C E2E.HooksE.A0 ctl P3kR1bd.spqrNoPanic
      (ConsumeMessageKeyTransfer.ls_subroutine_ok_transfer_of_plain
        (callerProg := (blkPC_434).rebase (blkPl_434).base
          (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (pkSer_205_ok mmpl gh W hG))
      (chainKeyToPb_433_cl_ok mmpl gh W hG)
      (growOne_433_cl_ok mmpl gh W hG)
      (dropChain_433_cl_ok mmpl gh W hG)
      (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq))
      (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG))
      (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG))
      (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_framelessMemcpy_sat mmpl gh W hG))
      (keys_ls_hook_ok_of_mem
        (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
          (Slots.cliExternsPlaced_sessionMemmove_sat mmpl W dropChainStack)))
      ((cmk_externAt?_of_mem
        (prog := (blkPC_434).rebase (blkPl_434).base
          (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (sym := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")).trans
        (Slots.cliGhostExterns_panic_handle_error mmpl gh W)))

/-- `S4SeamPlaced` on Block `433` at `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem s4_433_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) (ctl : BitVec 64) (S : SpqrModel) :
    S4SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C E2E.HooksE.A0 ctl uuidTryParse S := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hEx : LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat
      W.C.F (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks hG
  have hshim_cmk : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      CryptoVerification.LibsignalSession.cmkRustNoAllocShimSym
      CryptoVerification.LibsignalSession.cmkShimSpec :=
    Slots.cliExternsPlaced_shim_sat mmpl gh W hG.shim_eq
  have hA_cmk : CryptoVerification.LibsignalSession.CmkAllocHooks
      E2E.HooksE.A0 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    ⟨Slots.cliExternsPlaced_alloc_sat mmpl gh W hG,
     Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG,
     hshim_cmk,
     Slots.cliGhostExterns_panic_handle_error mmpl gh W,
     Slots.cliGhostExterns_panic_option_expect_failed mmpl gh W,
     RunGlue.cliGhostExterns_panic_of_mem mmpl gh W (by decide)⟩
  have hcmk24 := LibsignalBinary.Proofs.ConsumeMessageKey.AssemblySat.consume_message_key_placed_ro_run_sat
    W.C.F E2E.HooksE.A0 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
    (cliGhostExterns_row_placed mmpl gh W (Slots.blackBox_row_placed mmpl W))
    ((RunGlue.cliGhostExterns_shim gh _).trans (congrArg some hG.shim_eq))
    (Slots.cliExternsPlaced_realloc_sat mmpl gh W hG)
    hEx.memcpy
    (Slots.cliExternsPlaced_sessionMemsetRegion_sat mmpl gh W hG)
    hEx.compress256
    hA_cmk
    (cliGhostExterns_row_placed mmpl gh W (Slots.memmove_row_placed mmpl W))
  have hcmk24_cro : subroutine_ok
      ((blkPC_24).rebase (blkPl_24).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_24).base
      (withLsCodeRoLoaded lsmpl (KeyDerive.cmkRawSpecPlaced W.C.F E2E.HooksE.A0)) := by
    refine subroutine_ok_mono hcmk24 (fun x R s0 hp => ?_) (fun x R s0 sf hq => ?_)
    · dsimp only [withLsCodeRoLoaded, KeyDerive.cmkRawSpecPlaced, cmkPlacedRoSpec, cmkPlacedSpec,
        withLsCodeLoaded] at hp ⊢
      rw [← lsLogOff_eq_logOff_placed] at hp
      dsimp only [FromRecordCallees.lsLogOff] at hp
      have h1 : s0.mem ⊨ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (((⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.theirA ∧ s0.readReg64 .x2 = x.ckA ∧
              (s0.readReg64 .x3).setWidth 32 = x.counter ∧
              (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s0.readReg64 .x8 = x.ret⌝ ∗
            ratchetAt E2E.HooksE.A0 x.self x.G x.st ∗
            (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
            memRegion x.ret 88 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp cmkStack ∗ E2E.HooksE.A0.pool)) ∗ R) :=
        Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp
      rw [satisfies_pure_sepConj] at h1
      rcases h1 with ⟨⟨hcl, hro⟩, hrest⟩
      have h2 : s0.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
          ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗
          (((⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.theirA ∧ s0.readReg64 .x2 = x.ckA ∧
              (s0.readReg64 .x3).setWidth 32 = x.counter ∧
              (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s0.readReg64 .x8 = x.ret⌝ ∗
            ratchetAt E2E.HooksE.A0 x.self x.G x.st ∗
            (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
            memRegion x.ret 88 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp cmkStack ∗ E2E.HooksE.A0.pool)) ∗ R) := by
        rw [satisfies_pure_sepConj]
        refine ⟨hcl, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hro, hrest⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h2
    · dsimp only [withLsCodeRoLoaded, KeyDerive.cmkRawSpecPlaced, cmkPlacedRoSpec, cmkPlacedSpec,
        withLsCodeLoaded] at hq ⊢
      rw [← lsLogOff_eq_logOff_placed]
      exact hq
  have hcmk433 := keys_ls_subroutine_ok_of_block_cro
    (callerProg := (blkPC_434).rebase (blkPl_434).base
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) hcmk24_cro
  exact consumeMsgKey_433_placed_ok W.C E2E.HooksE.A0 ctl S
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
    (addrDisplay_433_cro_ok mmpl gh W) hcmk433
    (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG))

/-- `S7SeamPlaced` on Block `433` at `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem s7_433_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) (ctl : BitVec 64) (S : SpqrModel) :
    S7SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C E2E.HooksE.A0 ctl uuidTryParse S := by
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hpk60 := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_60).rebase (blkPl_60).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl) (pkSer_205_ok mmpl gh W hG)))
  have hvmac62 := verifyMacWithAddresses_placed_cro_ok W.C E2E.HooksE.A0 uuidTryParse
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
    (parseSid_61_ok mmpl gh W) (new_from_slice_60_cro_ok mmpl gh W hG) hpk60
    (keys_ls_hook_ok_of_mem
      (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_blackBox_sat mmpl W)))
    (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
    (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
    (Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG)
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_compress256Multi_sat mmpl W))
    (Slots.cliExternsPlaced_sessionMemsetRegion_sat mmpl gh W hG)
  have hvmac433 : subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 62)
      (withLsCodeRoLoaded lsmpl
        (verifyMacWithAddressesPlacedSpec W.C.F E2E.HooksE.A0 uuidTryParse)) :=
    keys_ls_subroutine_ok_of_block_cro
      (callerProg := (blkPC_434).rebase (blkPl_434).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) hvmac62
  exact verifyMac_433_placed_ok' W.C E2E.HooksE.A0 ctl S
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
    hvmac433
    (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_shim_sat mmpl gh W hG.shim_eq))
    (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG))
    (keys_ls_hook_ok_of_mem (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG))
    ((cmk_externAt?_of_mem
      (prog := (blkPC_434).rebase (blkPl_434).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (sym := lsHandleErrorSym)).trans
      (Slots.cliGhostExterns_panic_handle_error mmpl gh W))

end DhStepCro

end CryptoVerification.Cli.SpqrV1.M4
